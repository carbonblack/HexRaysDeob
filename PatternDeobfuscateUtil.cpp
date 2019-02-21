#include <hexrays.hpp>
#include "HexRaysUtil.hpp"
#include "PatternDeobfuscateUtil.hpp"
#include "Config.hpp"
#include "DefUtil.hpp"

// For microinstructions with two or more operands (in l and r), check to see
// if one of them is numeric and the other one isn't. If this is the case,
// return pointers to the operands in the appropriately-named argument 
// variables and return true. Otherwise, return false.
// This is a utility function that helps implement many other pattern-matching
// deobfuscations.
bool ExtractNumAndNonNum(minsn_t *insn, mop_t *&numOp, mop_t *&otherOp)
{
	mop_t *num = NULL, *other = NULL;

	if (insn->l.t == mop_n)
	{
		num = &insn->l;
		other = &insn->r;
	}

	if (insn->r.t == mop_n)
	{
		if (num != NULL)
		{
			// Technically we have an option to perform constant folding 
			// here... but Hex-Rays should have done / should do that for us
			return false;
		}
		num = &insn->r;
		other = &insn->l;
	}
	if (num == NULL)
		return false;

	numOp = num;
	otherOp = other;

	return true;
}

// For microinstructions with two or more operands (in l and r), check to see
// if one of them is a mop_d (result of another microinstruction), where the
// provider microinstruction is has opcode type mc. If successful, return the
// provider microinstruction and the non-matching micro-operand in the 
// appropriately-named arguments. Otherwise, return false.
// This helper function is useful for performing pattern-matching upon 
// commutative operations. Without it, we'd have to write each of our patterns
// twice: once for when the operation we were looking for was on the left-hand
// side, and once for when the operation was on the right-hand side.
bool ExtractByOpcodeType(minsn_t *ins, mcode_t mc, minsn_t *&match, mop_t*& noMatch)
{
	mop_t *possNoMatch = NULL;
	minsn_t *possMatch = NULL;
	
	// Does the left-hand side contain the operation we're looking for?
	// Update possNoMatch or possMatch, depending.
	if (!ins->l.is_insn() || ins->l.d->opcode != mc)
		possNoMatch = &ins->l;
	else
		possMatch = ins->l.d;

	// Perform the same check on the right-hand side.
	if (!ins->r.is_insn() || ins->r.d->opcode != mc)
		possNoMatch = &ins->r;
	else
		possMatch = ins->r.d;
	
	// If both sides matched, or neither side matched, fail.
	if (possNoMatch == NULL || possMatch == NULL)
		return false;

	match = possMatch;
	noMatch = possNoMatch;
	return true;
}

// The obfuscation techniques upon conditional operations have "&1" 
// miscellaneously present or not present within them. Writing pattern-matching
// rules for all of the many possibilities would be extremely tedious. This
// helper function reduces the tedium by checking to see whether the provided
// microinstruction is "x & 1" (or "1 & x"), and it extracts x (as both an
// operand, and, if the operand is a mop_d (result of another 
// microinstruction), return the provider instruction also.
bool TunnelThroughAnd1(minsn_t *ins, minsn_t *&inner, bool bRequireSize1, mop_t **opInner)
{
	// Microinstruction must be AND
	if (ins->opcode != m_and)
		return false;

	// One side must be numeric, the other one non-numeric
	mop_t *andNum, *andNonNum;
	if (!ExtractNumAndNonNum(ins, andNum, andNonNum))
		return false;

	// The number must be the value 1
	if (andNum->nnn->value != 1)
		return false;

	if(bRequireSize1 && andNum->size != 1)
		return false;

	// If requested, pass the operand back to the caller this point
	if(opInner != NULL)
		*opInner = andNonNum;

	// If the non-numeric operand is an instruction, extract the 
	// microinstruction and pass that back to the caller.
	if (andNonNum->is_insn())
	{
		inner = andNonNum->d;
		return true;
	}

	// Otherwise, if the non-numeric part wasn't a mop_d, check to see whether
	// the caller specifically wanted a mop_d. If they did, fail. If the caller
	// was willing to accept another operand type, return true.
	return opInner != NULL;
}

// It checks to see whether the provided microinstruction is "x | -2" (or "-2 | x"),
// and extracts x as both an operand,
// and, if the operand is a mop_d (result of another microinstruction),
// return the provider instruction also.
bool TunnelThroughOrMinus2(minsn_t *ins, minsn_t *&inner, bool bRequireSize1, mop_t **opInner)
{
	// Microinstruction must be OR
	if (ins->opcode != m_or)
		return false;

	// One side must be numeric, the other one non-numeric
	mop_t *orNum, *orNonNum;
	if (!ExtractNumAndNonNum(ins, orNum, orNonNum))
		return false;

	// The number must be the value -2
	if (orNum->nnn->value != 0xFFFFFFFE)
		return false;

	if (bRequireSize1 && orNum->size != 1)
		return false;

	// If requested, pass the operand back to the caller this point
	if (opInner != NULL)
		*opInner = orNonNum;

	// If the non-numeric operand is an instruction, extract the
	// microinstruction and pass that back to the caller.
	if (orNonNum->is_insn())
	{
		inner = orNonNum->d;
		return true;
	}

	// Otherwise, if the non-numeric part wasn't a mop_d, check to see whether
	// the caller specifically wanted a mop_d. If they did, fail. If the caller
	// was willing to accept another operand type, return true.
	return opInner != NULL;
}

// The obfuscator implements boolean inversion via "x ^ 1". Hex-Rays, or one of
// our other deobfuscation rules, could also convert these to m_lnot 
// instructions. This function checks to see if the microinstruction passed as
// argument matches one of those patterns, and if so, extracts the negated 
// term as both a micro-operand and a microinstruction (if the negated operand
// was of mop_d type).
bool ExtractLogicallyNegatedTerm(minsn_t *ins, minsn_t *&insNegated, mop_t **opNegated)
{
	mop_t *nonNegated;
	
	// Check the m_lnot case.
	if (ins->opcode == m_lnot)
	{
		// Extract the operand, if requested by the caller.
		if(opNegated != NULL)
			*opNegated = &ins->l;

		// If the operand was mop_d (i.e., result of another microinstruction),
		// retrieve the provider microinstruction. Get rid of the pesky "&1" 
		// terms while we're at it.
		if (ins->l.is_insn())
		{
			insNegated = ins->l.d;
			while(TunnelThroughAnd1(insNegated, insNegated));
			return true;
		}
		
		// Otherwise, if the operand was not of type mop_d, "success" depends
		// on whether the caller was willing to accept a non-mop_d operand.
		else
		{
			insNegated = NULL;
			return opNegated != NULL;
		}
	}
	
	// If the operand wasn't m_lnot, check the m_xor case.
	if (ins->opcode != m_xor)
		return false;

	// We're looking for XORs with one constant and one non-constant operand
	mop_t *xorNum, *xorNonNum;
	if (!ExtractNumAndNonNum(ins, xorNum, xorNonNum))
		return false;

	// The constant must be the 1-byte value 1
	if (xorNum->nnn->value != 1 || xorNum->size != 1)
		return false;

	// The non-numeric part must also be 1. This check is probably unnecessary.
	if (xorNonNum->size != 1)
		return false;

	// If the caller wanted an operand, give it to them.
	if (opNegated != NULL)
		*opNegated = xorNonNum;

	// If the operand was mop_d (result of another microinstruction), extract
	// it and remove the &1 terms.
	if (xorNonNum->is_insn())
	{
		insNegated = xorNonNum->d;
		while (TunnelThroughAnd1(insNegated, insNegated));
		return true;
	}
	
	// Otherwise, if the operand was not of type mop_d, "success" depends on
	// whether the caller was willing to accept a non-mop_d operand.
	insNegated = NULL;
	return opNegated != NULL;
}

// This function checks whether two conditional terms are logically opposite. 
// For example, "eax <s 1" and "eax >=s 1" would be considered logically 
// opposite. The check is purely syntactic; semantically-equivalent conditions
// that were not implemented as syntactic logical opposites will not be 
// considered the same by this function.
bool AreConditionsOpposite(minsn_t *lhsCond, minsn_t *rhsCond)
{
	// Get rid of pesky &1 terms
	while (TunnelThroughAnd1(lhsCond, lhsCond));
	while (TunnelThroughAnd1(rhsCond, rhsCond));
	
	// If the conditions were negated via m_lnot or m_xor by 1, get the 
	// un-negated part as a microinstruction.
	bool bLhsWasNegated = ExtractLogicallyNegatedTerm(lhsCond, lhsCond);
	bool bRhsWasNegated = ExtractLogicallyNegatedTerm(rhsCond, rhsCond);

	// lhsCond and rhsCond will be set to NULL if their original terms were
	// negated, but the thing that was negated wasn't the result of another 
	// microinstruction.
	if (lhsCond == NULL || rhsCond == NULL)
		return false;
	
	// If one was negated and the other wasn't, compare them for equality.
	// If the non-negated part of the negated comparison was identical to
	// the non-negated comparison, then the conditions are clearly opposite.
	// I guess this could also be extended by incorporating the logic from
	// below, but I didn't need to do that in practice.
	if (bLhsWasNegated != bRhsWasNegated)
		return lhsCond->equal_insns(*rhsCond, EQ_IGNSIZE | EQ_IGNCODE);

	// Otherwise, if both were negated or both were non-negated, compare the
	// conditionals term-wise. First, ensure that both microoperands are
	// setXX instructions.
	else if (is_mcode_set(lhsCond->opcode) && is_mcode_set(rhsCond->opcode))
	{
		// Now we have two possibilities.
		// #1: Condition codes are opposite, LHS and RHS are both equal
		if (negate_mcode_relation(lhsCond->opcode) == rhsCond->opcode)
			return
				equal_mops_ignore_size(lhsCond->l, rhsCond->l) &&
				equal_mops_ignore_size(lhsCond->r, rhsCond->r);

		// #2: Condition codes are the same, LHS and RHS are swapped
		if (lhsCond->opcode == rhsCond->opcode)
			return 
				equal_mops_ignore_size(lhsCond->l, rhsCond->r) &&
				equal_mops_ignore_size(lhsCond->r, rhsCond->l);
	}
	
	// No dice.
	return false;
}

// This function checks whether the operand is a global variable unchanged since the initialization
bool IsReadOnlyInitedVar(mop_t *op)
{
	if (op->t != mop_v) // global variable?
		return false;

	// check the global variable
	// The variable is in a writable section? (e.g., .data section)
	segment_t *s = getseg(op->g);
	if (s == NULL)
		return false;
	if (s->perm != (SEGPERM_READ | SEGPERM_WRITE))
		return false;
	// TODO: section with IMAGE_SCN_CNT_INITIALIZED_DATA?

	// The variable doesn't have a byte value?
	if (is_loaded(op->g))
		return false;
	// The variable doesn't have xrefsTo with write access?
	xrefblk_t xb;
	for (bool ok = xb.first_to(op->g, XREF_DATA); ok; ok = xb.next_to())
		if (xb.type == dr_W)
			return false;

	return true;
}

// This function traces the operand until getting the instruction with it
// based on FindNumericDefBackwards in DefUtil.cpp
bool FindInsWithTheOp(mblock_t *blk, mop_t *op, minsn_t *start, minsn_t *&ins, mcode_t opcode, mopt_t opt)
{
	//return false;
	char buf[1000];
	mlist_t ml;
	// consider multiple register ids

	if (!InsertOp(blk, ml, op))
		return false;
	minsn_t *mStart = start;
	do
	{
		minsn_t *mDef = my_find_def_backwards(blk, ml, mStart);
		if (mDef != NULL)
		{
			if (mDef->opcode == opcode && (opt == 0 || opt == mDef->l.t))
			{
				ins = mDef;
				return true;
			}

			if (mDef->opcode == m_mov)
			{
				ml.clear();
				if (!InsertOp(blk, ml, &mDef->l))
					return false;
			}
			else
			{
				mcode_t_to_string(mDef, buf, sizeof(buf));
#if OPTVERBOSE
				msg("[E] FindInsWithTheOp: found %s\n", buf);
#endif
				return false;
			}
			mStart = mDef;
		}
		else // move to previous block
		{
			blk = blk->prevb;
			mStart = NULL;
		}
	} while (blk->prevb != NULL);
	return false;
}

// This function traces 2 operands separately for x and y in y * (x - 1)
bool TraceAndExtractOpsMovAndSubBy1(mblock_t *blk, mop_t *&opMov, mop_t *&opSub, minsn_t *start)
{
	minsn_t *insMov, *insSub;
	//if (FindInsWithTheOp(blk, &start->l, start, insMov, m_mov, mop_v) && FindInsWithTheOp(blk, &start->r, start, insSub, m_sub, mop_v))
	if (FindInsWithTheOp(blk, &start->l, start, insMov, m_mov) && FindInsWithTheOp(blk, &start->r, start, insSub, m_sub))
	{
		opMov = &insMov->l;
		mop_t *num;
		if (ExtractNumAndNonNum(insSub, num, opSub) && num->nnn->value == 1)
			return true;
	}
	// swap the search operands
	//if (FindInsWithTheOp(blk, &start->r, start, insMov, m_mov, mop_v) && FindInsWithTheOp(blk, &start->l, start, insSub, m_sub, mop_v))
	if (FindInsWithTheOp(blk, &start->r, start, insMov, m_mov) && FindInsWithTheOp(blk, &start->l, start, insSub, m_sub))
	{
		opMov = &insMov->l;
		mop_t *num;
		if (ExtractNumAndNonNum(insSub, num, opSub) && num->nnn->value == 1)
			return true;
	}
	return false;
}

// Insert a micro-operand into one of the two sets above. Remove 
// duplicates -- meaning, if the operand we're trying to insert is already
// in the set, remove the existing one instead. This is the "cancellation"
// in practice.
bool XorSimplifier::Insert(std::set<mop_t *> &whichSet, mop_t *op)
{
	mop_t &rop = *op;
		
	// Because mop_t types currently cannot be compared or hashed in the
	// current microcode API, I had to use a slow linear search procedure
	// to compare the micro-operand we're trying to insert against all
	// previously-inserted values in the relevant set.
	for (auto otherOp : whichSet)
	{
		// If the micro-operand was already in the set, get rid of it.
		if (equal_mops_ignore_size(rop, *otherOp))
		{
			whichSet.erase(otherOp);
			
			// Mark these operands as being able to be deleted.
			m_ZeroOut.push_back(op);
			m_ZeroOut.push_back(otherOp);
			
			// Couldn't insert.
			return false;
		}
	}
	
	// Otherwise, if it didn't match an operand already in the set, insert
	// it into the set and return true on successful insertion.
	whichSet.insert(op);
	return true;
}

// Wrapper to insert constant and non-constant terms
bool XorSimplifier::InsertNonConst(mop_t *op) 
{ 
	++m_InsertedNonConst; 
	return Insert(m_NonConst, op); 
}

bool XorSimplifier::InsertConst(mop_t *op) 
{ 
	++m_InsertedConst; 
	return Insert(m_Const, op); 
}

// Insert one micro-operand. If the operand is the result of another XOR
// microinstruction, recursively insert the operands being XORed. 
// Otherwise, insert the micro-operand into the proper set (constant or
// non-constant) depending upon its operand type.
void XorSimplifier::Insert(mop_t *op)
{
	// If operand is m_xor microinstruction, recursively insert children 
	if (op->t == mop_d && op->d->opcode == m_xor)
	{
		Insert(&op->d->l);
		Insert(&op->d->r);
		return;
	}
		// Otherwise, insert it into the constant or non-constant set
	if (op->t == mop_n)
		InsertConst(op);
	else
		InsertNonConst(op);
}

// This function takes an XOR microinstruction and inserts its operands
// by calling the function above
void XorSimplifier::Insert(minsn_t *insn)
{
	if (insn->opcode != m_xor)
	{
#if OPTVERBOSE
		char buf[1000];
		mcode_t_to_string(insn, buf, sizeof(buf));
		msg("[I] Tried to insert from non-XOR instruction of type %s at %a\n", buf, insn->ea);
#endif
		return;
	}

	// Insert children
	Insert(&insn->l);
	Insert(&insn->r);
}

// Were any cancellations performed?
bool XorSimplifier::DidSimplify()
{
	return !m_ZeroOut.empty();
	//return m_Const.size() != m_InsertedConst || m_NonConst.size() != m_InsertedNonConst;
}

// Top-level functionality to simplify an XOR microinstruction. Insert the
// instruction, then see if any simplifications could be performed. If so,
// remove the simplified terms.
bool XorSimplifier::Simplify(minsn_t *insn, mblock_t *blk)
{
	// Only insert XOR instructions
	if (insn->opcode != m_xor)
		return false;

	Insert(insn);
	
	// Were there common terms that could be cancelled?
	if (!DidSimplify())
		return false;

	// Perform the cancellations by zeroing out the common micro-operands
	for (auto zo : m_ZeroOut)
		zo->make_number(0, zo->size);

	// Trigger Hex-Rays' ordinary optimizations, which will remove the 
	// XOR 0 terms. Return true.
#if IDA_SDK_VERSION == 710
	insn->optimize_flat();
#elif IDA_SDK_VERSION >= 720
	if (blk)
		blk->optimize_insn(insn);
	else
		insn->optimize_solo();
#endif
	return true;
}
