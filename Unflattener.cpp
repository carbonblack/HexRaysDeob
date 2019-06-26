// ROLF TODO: Change control flow in func so that PruneUnreachable gets called even if CFI info fails?
// Probably doesn't matter at that point.

#define USE_DANGEROUS_FUNCTIONS
#include <hexrays.hpp>
#include "HexRaysUtil.hpp"
#include "Unflattener.hpp"
#include "CFFlattenInfo.hpp"
#include "TargetUtil.hpp"
#include "DefUtil.hpp"
#include "Config.hpp"

std::set<ea_t> g_BlackList;
std::set<ea_t> g_WhiteList;

mba_maturity_t g_LastMaturity = MMAT_ZERO;
ea_t g_LastFuncEa = BADADDR;
int g_NumGotosRemoved = 0;
int atThisMaturity = 0;

// Find the block that dominates iDispPred, and which is one of the targets of
// the control flow flattening switch.
mblock_t *CFUnflattener::GetDominatedClusterHead(mbl_array_t *mba, int iDispPred, int &iClusterHead)
{
	mblock_t *mbClusterHead = NULL;
	// Find the block that is targeted by the dispatcher, and that
	// dominates the block we're currently looking at. This logic won't
	// work for the first block (since it wasn't targeted by the control
	// flow dispatch switch, so it doesn't have an entry in the dominated
	// cluster information), so we special-case it.
	if (iDispPred == cfi.iFirst)
	{
		//iClusterHead = cfi.iFirst;
		//mbClusterHead = mba->get_mblock(cfi.iFirst);
		iClusterHead = 1; // to trace back until the start
		mbClusterHead = mba->get_mblock(1);
	}
	else
	{
		// If it wasn't the first block, look up its cluster head block
		iClusterHead = cfi.m_DominatedClusters[iDispPred];
		if (iClusterHead < 0)
		{
			debugmsg("[I] Block %d was not part of a dominated cluster\n", iDispPred);
			return NULL;
		}
		mbClusterHead = mba->get_mblock(iClusterHead);
		debugmsg("[I] Block %d was part of dominated cluster %d\n", iDispPred, iClusterHead);
	}
	return mbClusterHead;

}

// This function attempts to locate the numeric assignment to a given variable
// "what" starting from the end of the block "mb". It follows definitions
// backwards, even across blocks, until it either reaches the block
// "mbClusterHead", or, if the boolean "bAllowMultiSuccs" is false, it will
// stop the first time it reaches a block with more than one successor.
// If it finds an assignment whose source is a stack variable, then it will not
// be able to continue in the backwards direction, because intervening memory
// writes will make the definition information useless. In that case, it
// switches to a strategy of searching in the forward direction from
// mbClusterHead, looking for assignments to that stack variable.
// Information about the chain of assignment instructions along the way are
// stored in the vector called m_DeferredErasuresLocal, a member variable of
// the CFUnflattener class.
int CFUnflattener::FindBlockTargetOrLastCopy(
        mblock_t *mb,
        mblock_t *mbClusterHead,
        mop_t *what,
        bool bAllowMultiSuccs,
        bool bRecursive)
{
	int iClusterHead = mbClusterHead->serial;

	MovChain local;

	mop_t *opNum = NULL, *opCopy;
	// Search backwards looking for a numeric assignment to "what". We may or
	// may not find a numeric assignment, but we might find intervening
	// assignments where "what" is copied from other variables.
	bool bFound = FindNumericDefBackwards(mb, what, opNum, local, bRecursive, bAllowMultiSuccs, iClusterHead);

	// If we found no intervening assignments to "what", that's bad.
	if (local.empty())
		return -1;

	// opCopy now contains the last non-numeric assignment that we saw before
	// FindNumericDefBackwards terminated (either due to not being able to
	// follow definitions, or, if bAllowMultiSuccs is true, because it recursed
	// into a block with more than one successor.
	opCopy = local.back().opCopy;

	// Copy the assignment chain into the erasures vector, so we can later
	// remove them if our analysis succeeds.
	m_DeferredErasuresLocal.insert(m_DeferredErasuresLocal.end(), local.begin(), local.end());

	// If we didn't find a numeric definition, but we did find an assignment
	// from a stack variable, switch to a forward analysis from the beginning
	// of the cluster. If we don't find it, this is not necessarily an
	// indication that the analysis failed; for blocks with two successors,
	// we do further analysis.
	if (!bFound && opCopy != NULL && opCopy->t == mop_S)
	{
		mop_t *num = FindForwardStackVarDef(mbClusterHead, opCopy, local);
		if (num)
		{
			opNum = num;
			bFound = true;
		}
		else
		{
			debugmsg("[EEE] Forward method also failed\n");
		}

	}

	// If we found a numeric assignment...
	if (bFound)
	{
		// Look up the integer number of the block corresponding to that value.
		int64 theImm = opNum->nnn->value;
		if (cfi.bOpAndAssign) // m_and assignment with immediate value
			theImm &= cfi.OpAndImm;
		int iDestNo = cfi.FindBlockByKey(theImm);
		if (iDestNo == -1)
			iDestNo = cfi.FindBlockByKeyFromEA(theImm, mb->mba);

		// If we couldn't find the block, that's bad news.
		if (iDestNo < 0)
			debugmsg("[E] Block %d assigned unknown key %llx to assigned var\n", mb->serial, opNum->nnn->value);

		// Otherwise, we win! Return the block number.
		else
		{
			if (cfi.bOpAndAssign)
				debugmsg("[I] Next target resolved: %d (cluster head %d) -> %d (%x & %x = %x)\n", mb->serial, iClusterHead, iDestNo, opNum->nnn->value, cfi.OpAndImm, theImm);
			else
				debugmsg("[I] Next target resolved: %d (cluster head %d) -> %d (%x)\n", mb->serial, iClusterHead, iDestNo, theImm);
			return iDestNo;
		}
	}

	// Negative return code indicates failure.
	return -1;
}

// This function is used for unflattening constructs that have two successors,
// such as if statements. Given a block that assigns to the assignment variable
// that has two predecessors, analyze each of the predecessors looking for
// numeric assignments by calling the previous function.
bool CFUnflattener::HandleTwoPreds(mblock_t *mb, mblock_t *mbClusterHead, mop_t *opCopy, mblock_t *&endsWithJcc, mblock_t *&nonJcc, int &actualGotoTarget, int &actualJccTarget)
{
	mbl_array_t *mba = mb->mba;
	int iDispPred = mb->serial;

	// No really, don't call this function on a block that doesn't have two
	// predecessors. I was kind enough to warn you in the documentation; now
	// you get an assertion failure.

	mblock_t *pred1, *pred2;
	if (mb->npred() == 2)
	{
		pred1 = mba->get_mblock(mb->pred(0));
		pred2 = mba->get_mblock(mb->pred(1));
	}
	else {
		return false;
	}

	nonJcc = NULL;
	int jccDest = -1, jccFallthrough = -1;

	// Given the two predecessors, find the block with the conditional jump at
	// the end of it (store the block in "endsWithJcc") and the one without
	// (store it in nonJcc). Also find the block number of the jcc target, and
	// the block number of the jcc fallthrough (i.e., the block number of
	// nonJcc).
	if (!SplitMblocksByJccEnding(pred1, pred2, endsWithJcc, nonJcc, jccDest, jccFallthrough))
	{
		debugmsg("[I] Block %d w/preds %d, %d did not have one predecessor ending in jcc, one without\n", iDispPred, pred1->serial, pred2->serial);
		return false;
	}

	// Sanity checking the structure of the graph. The nonJcc block should only
	// have one incoming edge...
	if (nonJcc->npred() != 1)
	{
		debugmsg("[I] Block %d w/preds %d, %d, non-jcc pred %d had %d predecessors (not 1)\n", iDispPred, pred1->serial, pred2->serial, nonJcc->serial, nonJcc->npred());
		return false;
	}

	// ... namely, from the block ending with the jcc.
	if (nonJcc->pred(0) != endsWithJcc->serial)
	{
		debugmsg("[I] Block %d w/preds %d, %d, non-jcc pred %d did not have the other as its predecessor\n", iDispPred, pred1->serial, pred2->serial, nonJcc->serial);
		return false;
	}

	// Call the previous function to locate the numeric definition of the
	// variable that is used to update the assignment variable if the jcc is
	// not taken.
	actualGotoTarget = FindBlockTargetOrLastCopy(endsWithJcc, mbClusterHead, opCopy, false, true);

	// If that succeeded...
	if (actualGotoTarget >= 0)
	{
		// ... then do the same thing when the jcc is not taken.
		actualJccTarget = FindBlockTargetOrLastCopy(nonJcc, mbClusterHead, opCopy, true, true);

		// If that succeeded, great! We can unflatten this two-way block.
		if (actualJccTarget >= 0)
			return true;
	}
	return false;
}

void CFUnflattener::CopyOrAppendMinsns(mblock_t *src, mblock_t *&dst)
{
	minsn_t *mbHead = src->head;
	minsn_t *mbCurr = mbHead;

	// allow copying to an empty block or appending to a block without a conditional jump
    QASSERT(99000, dst->tail == NULL || !is_mcode_jcond(dst->tail->opcode));

	if (dst->tail != NULL && dst->tail->opcode == m_goto)
        {
                minsn_t *delme = dst->tail;
		dst->remove_from_block(delme);
                delete delme;
        }

	do
	{
		minsn_t *mCopy = new minsn_t(*mbCurr);
		dst->insert_into_block(mCopy, dst->tail);
		mbCurr = mbCurr->next;

		char buf[1000];
		mcode_t_to_string(dst->tail, buf, sizeof(buf));
		debugmsg("[I] CopyMinsnsToTailNoCond: src block %d -> dst block %d, copied instruction is %s\n", src->serial, dst->serial, buf);
	} while (mbCurr != NULL);
}

void CFUnflattener::CopyMblock(
        DeferredGraphModifier & /*dgm*/,
        mblock_t *src,
        mblock_t *&dst)
{
        mbl_array_t *mba = src->mba;
	dst = mba->insert_block(mba->qty - 1);

	// copy microcode instructions
	CopyOrAppendMinsns(src, dst);

	// copy struct members
	dst->flags = src->flags;
	dst->start = src->start;
	dst->end = src->end;
	dst->type = src->type;

	// copy mlist_t
	dst->dead_at_start = src->dead_at_start;
	dst->mustbuse = src->mustbuse;
	dst->maybuse = src->maybuse;
	dst->mustbdef = src->mustbdef;
	dst->maybdef = src->maybdef;
	dst->dnu = src->dnu;

	// copy sval_t
	dst->maxbsp = src->maxbsp;
	dst->minbstkref = src->minbstkref;
	dst->minbargref = src->minbargref;

	// predset/succset wiil be modified later
}

void CFUnflattener::UpdateDestBlockNumber(DeferredGraphModifier &dgm, mblock_t *mb, int oldDest, int newDest)
{
	if (mb->tail != NULL && is_mcode_jcond(mb->tail->opcode))
	{
		mb->tail->d.b = newDest;
		if (oldDest != -1)
			dgm.Replace(mb->serial, oldDest, newDest);
		else
			dgm.Add(mb->serial, newDest);
	}
	else
	{
		if (mb->tail != NULL && mb->tail->opcode != m_goto)
			AppendGotoOntoNonEmptyBlock(mb, newDest);
		else
			mb->tail->l.b = newDest;

		if (oldDest != -1)
			dgm.Replace(mb->serial, oldDest, newDest);
		else
			dgm.Add(mb->serial, newDest);
		mb->mark_lists_dirty();
	}
}

int CFUnflattener::CopyAndConnectBlocksToPred(DeferredGraphModifier &dgm, mblock_t *mb, mblock_t *&pred, int iDest)
{
	mbl_array_t *mba = mb->mba;

	mblock_t *mbCopy, *mbSuccFalseCopy, *mbSuccFalse;
	CopyMblock(dgm, mb, mbCopy);
	bool bJcond = mb->tail != NULL && is_mcode_jcond(mb->tail->opcode);
	if (bJcond)
	{
		mbSuccFalse = mba->get_mblock(mb->serial + 1);
		CopyMblock(dgm, mbSuccFalse, mbSuccFalseCopy);
		if (mbCopy->serial + 1 != mbSuccFalseCopy->serial)
		{
			debugmsg("[E] CopyAndConnectBlocksToPred: copied conditional blocks are not successive for a conditional jump. Abort. \n", mb->serial);
			return -1;
		}
	}

	// update instructions/CFGs
	// pred
	UpdateDestBlockNumber(dgm, pred, mb->serial, mbCopy->serial);
	// mbCopy
	if (bJcond)
		dgm.Add(mbCopy->serial, mbCopy->serial + 1); // the order is important (add false case then true case, or INTERR 50860)
	UpdateDestBlockNumber(dgm, mbCopy, -1, iDest);
	// mbSuccFalseCopy
	if (bJcond)
	{
		if (mbSuccFalseCopy->tail != NULL && is_mcode_jcond(mbSuccFalseCopy->tail->opcode))
		{
			msg("[!] CopyAndConnectConditionalBlocksToPred: mbSuccFalseCopy tail is Jcc at func %a (no such function in the tested samples)\n", mba->entry_ea);
			return -1;
		}
		else
			UpdateDestBlockNumber(dgm, mbSuccFalseCopy, -1, mbSuccFalse->succ(0));
	}

	return mbCopy->serial;
}

void CFUnflattener::CorrectStopBlockPreds(DeferredGraphModifier & dgm, mbl_array_t *mba, intvec_t stopPreds)
{
	int stopBlkNum = mba->qty - 1;
	mblock_t * mbCurrentStop = mba->get_mblock(stopBlkNum);
	for (auto bNum : stopPreds)
	{
		mblock_t *stopPred = mba->get_mblock(bNum);
		if (stopPred->tail != NULL)
		{
			if (is_mcode_jcond(stopPred->tail->opcode))
			{
				debugmsg("[I] CorrectStopBlockPreds: The pred of BLT_STOP block (%d) with Jcc will be updated in func %a\n", stopPred->serial, mba->entry_ea);
				if (stopPred->serial + 1 != stopBlkNum && stopPred->tail->d.b != stopBlkNum)
					UpdateDestBlockNumber(dgm, stopPred, stopPred->tail->d.b, stopBlkNum);
				else if (stopPred->serial + 1 == stopBlkNum && stopPred->succ(0) != stopBlkNum)
					UpdateDestBlockNumber(dgm, stopPred, stopPred->succ(0), stopBlkNum);
				else if (stopPred->tail->d.b == stopBlkNum && stopPred->succ(1) != stopBlkNum)
					UpdateDestBlockNumber(dgm, stopPred, stopPred->succ(1), stopBlkNum);
			}
			else
			{
				debugmsg("[I] CorrectStopBlockPreds: The pred of BLT_STOP block (%d) will be updated in func %a\n", stopPred->serial, mba->entry_ea);
				if ((stopPred->tail->opcode != m_goto && stopPred->serial + 1 != stopBlkNum) || stopPred->succ(0) != stopBlkNum)
					UpdateDestBlockNumber(dgm, stopPred, stopPred->succ(0), stopBlkNum);
				else if (stopPred->tail->opcode == m_goto && stopPred->tail->l.b != stopBlkNum)
					UpdateDestBlockNumber(dgm, stopPred, stopPred->tail->l.b, stopBlkNum);
			}
		}
	}
}

void CFUnflattener::DisconnectBlockFromPred(DeferredGraphModifier &dgm, mblock_t *mb, mblock_t *&pred, int iDest) {
	// append mb code to the pred tail
	CopyOrAppendMinsns(mb, pred);

	// update pred instruction/CFG
	dgm.ChangeGoto(pred, mb->serial, iDest);
	pred->mark_lists_dirty();
}

int CFUnflattener::PostHandleTwoPreds(DeferredGraphModifier &dgm, mblock_t *&mb, int actualGotoTargetOld, int actualGotoTargetNew, mblock_t *&nonJcc, int actualJccTarget)
{
	// handle endWithJcc's destination (actualGotoTarget)
	if (mb->tail != NULL && is_mcode_jcond(mb->tail->opcode))
	{
		// we can not change the jump target to be the next block
		if (actualGotoTargetNew == mb->serial + 1)
		{
			debugmsg("[E] PostHandleTwoPreds: actualGotoTarget is matched with the false case of the dispatcher predecessor = %d. Abort.\n", mb->serial);
			return -1;
		}
		dgm.Replace(mb->serial, actualGotoTargetOld, actualGotoTargetNew);
		mb->tail->d.b = actualGotoTargetNew;
	}
	else
	{
		dgm.ChangeGoto(mb, actualGotoTargetOld, actualGotoTargetNew);
		mb->mark_lists_dirty();
	}

	// this is not flattened if-statement blocks. Abort.
	if (actualGotoTargetNew == actualJccTarget)
	{
		debugmsg("[I] PostHandleTwoPreds: actualGotoTarget is matched with actualJccTarget in the dispatcher predecessor = %d. Abort.\n", mb->serial);
		return -1;
	}

	// handle nonJcc
	if (is_mcode_jcond(mb->tail->opcode))
	{
		// copy the conditional blocks for nonJcc
		return CopyAndConnectBlocksToPred(dgm, mb, nonJcc, actualJccTarget);
	}
	else
	{
		// change the destination from mb->serial to actualJccTarget
		DisconnectBlockFromPred(dgm, mb, nonJcc, actualJccTarget);
		return -1;
	}
}

bool CFUnflattener::FindJccInFirstBlocks(mbl_array_t *mba, mop_t *&opCopy, mblock_t *&endsWithJcc, mblock_t *&nonJcc, int &actualGotoTarget, int &actualJccTarget)
{
	actualGotoTarget = actualJccTarget = -1;

	// search assignment for endsWithJcc (the assignment can be done in every endsWithJcc blocks)
	for (int iCurrent = cfi.iFirst; iCurrent > 0; iCurrent -= 2)
	{
		endsWithJcc = mba->get_mblock(iCurrent);
		if (iCurrent == cfi.iFirst || is_mcode_jcond(endsWithJcc->tail->opcode))
		{
			actualGotoTarget = FindBlockTargetOrLastCopy(endsWithJcc, endsWithJcc, opCopy, false, false);
			if (actualGotoTarget >= 0)
				break;
			else
			{
				mop_t *opCopy2nd = m_DeferredErasuresLocal.back().opCopy;
				if (!equal_mops_ignore_size(*opCopy, *opCopy2nd)) {
					debugmsg("[I] FindJccInFirstBlocks: %s assigned to %s at %08lx\n", mopt_t_to_string(opCopy2nd->t), mopt_t_to_string(opCopy->t), m_DeferredErasuresLocal.back().insMov->ea);
					opCopy = opCopy2nd;
				}
			}
		}
	}

	// search assignment for nonJcc
	for (int iCurrent = cfi.iFirst - 1; iCurrent > 0; iCurrent -= 2)
	{
		nonJcc = mba->get_mblock(iCurrent);
		if (!is_mcode_jcond(nonJcc->tail->opcode))
		{
			actualJccTarget = FindBlockTargetOrLastCopy(nonJcc, nonJcc, opCopy, false, false);
			if (actualJccTarget >= 0 && actualGotoTarget >= 0)
			{
				// actual endsWithJcc is the pred of nonJcc
				endsWithJcc = mba->get_mblock(nonJcc->pred(0));
				return true;
			}
		}
	}

	return false;
}

// Erase the now-superfluous chain of instructions that were used to copy a
// numeric value into the assignment variable.
void CFUnflattener::ProcessErasures(mbl_array_t *mba)
{
	m_PerformedErasuresGlobal.insert(m_PerformedErasuresGlobal.end(), m_DeferredErasuresLocal.begin(), m_DeferredErasuresLocal.end());
	for (auto erase : m_DeferredErasuresLocal)
	{
		qstring qs;
		erase.insMov->print(&qs);
		tag_remove(&qs);
		debugmsg("[I] Erasing %a: %s\n", erase.insMov->ea, qs.c_str());

		// Be gone, sucker
		mba->get_mblock(erase.iBlock)->make_nop(erase.insMov);
	}

	m_DeferredErasuresLocal.clear();
}

// copied from verify.cpp
void CFUnflattener::CheckInterr50860(mblock_t *mb)
{
	// check that the successor list is correct
	intvec_t outs;
	switch (mb->tail == NULL ? m_nop : mb->tail->opcode)
	{
	case m_jtbl:
		//if (tail->r.t != mop_c)
			//INTERR(50859);
		outs = mb->tail->r.c->targets;
		break;
	case m_goto:
		if (mb->tail->l.t == mop_b)
			outs.add(mb->tail->l.b);
		break;
	case m_jcnd:
	case m_jnz:
	case m_jz:
	case m_jae:
	case m_jb:
	case m_ja:
	case m_jbe:
	case m_jg:
	case m_jge:
	case m_jl:
	case m_jle:
		// conditional jumps must pass control to the next block
		// if the condition is not satisfied
		outs.add(mb->serial + 1);
		outs.add_unique(mb->tail->d.b); // if true, control is passed to the jump target
		break;
	default:
		if (mb->nsucc() != 0)
			outs.add(mb->serial + 1);
		break;
	case m_ijmp:
	case m_ret:
		break;
	case m_ext:
		// we cannot verify m_ext insns because of ignored insns
		outs = mb->succset;
		break;
	}
	if (outs != mb->succset)
		debugmsg("INTERR 50860 found in block %d\n", mb->serial);
}

// This is the top-level un-flattening function for an entire graph. Hex-Rays
// calls this function since we register our CFUnflattener class as a block
// optimizer.
int idaapi CFUnflattener::func(mblock_t *blk)
{
	char buf[1000];

	// Was this function blacklisted? Skip it if so
	mbl_array_t *mba = blk->mba;
	if (g_BlackList.find(mba->entry_ea) != g_BlackList.end())
		return 0;

	const char *matStr = MicroMaturityToString(mba->maturity);
	//debugmsg("[I] Block optimization called at maturity level %s\n", matStr);

	// Only operate once per maturity level in the function except hxe_prealloc events
	if (g_LastMaturity == mba->maturity && g_LastFuncEa == mba->entry_ea && !this->bLastChance)
		return 0;

	// Update the last maturity level and function address
	g_LastMaturity = mba->maturity;
	g_LastFuncEa = mba->entry_ea;

#if UNFLATTENDEBUG
	// If we're debugging, save a copy of the graph on disk
	snprintf(buf, sizeof(buf), "c:\\temp\\dumpBefore-%s-%d.txt", matStr, atThisMaturity);
	DumpMBAToFile(mba, buf);
#endif

	// operation condition
	bool opCond;
#if USE_HEXRAYS_CALLBACK
	opCond = mba->maturity != MMAT_DEOB_MAP && !this->bLastChance;
#else
	opCond = mba->maturity != MMAT_DEOB_MAP && mba->maturity < MMAT_DEOB_UNFLATTEN;
#endif
	if (opCond)
		return 0;

	int iChanged = 0;

	// If local optimization has just been completed, remove transfer-to-gotos
	iChanged = RemoveSingleGotos(mba);
	//return iChanged;

	debugmsg("\tRemoved %d vacuous GOTOs\n", iChanged);

#if UNFLATTENDEBUG
	snprintf(buf, sizeof(buf), "c:\\temp\\dumpAfter-%s-%d.txt", matStr, atThisMaturity);
	DumpMBAToFile(mba, buf);
#endif

	// Might as well verify we haven't broken anything
	if (iChanged)
		mba->verify(true);


	// Get the preliminary information needed for control flow flattening, such
	// as the assignment/comparison variables.
	if (!cfi.GetAssignedAndComparisonVariables(blk))
	{
		bool errCond;
#if USE_HEXRAYS_CALLBACK
		errCond = this->bLastChance;
#else
		errCond = mba->maturity >= MMAT_DEOB_UNFLATTEN;
#endif
		if (errCond)
			debugmsg("[E] %s: Couldn't get control-flow flattening information\n", matStr);
		return iChanged;
	}

	// enable mblock_t copy for later maturity levels
	mba->clr_mba_flags2(MBA2_NO_DUP_CALLS);

	// Create an object that allows us to modify the graph at a future point.
	DeferredGraphModifier dgm;
	bool bDirtyChains = false;

	// collect pred block numbers of BLT_STOP
	int iStop = mba->qty - 1;
	mblock_t * mbStop = mba->get_mblock(mba->qty - 1);
	intvec_t stopPreds;
	for (int i = 0; i < mbStop->npred(); ++i)
	{
		debugmsg("[I] BLT_STOP pred = %d\n", mbStop->pred(i));
		stopPreds.add(mbStop->pred(i));
	}

	// Iterate through the predecessors of the top-level control flow switch
	for (auto iDispPred : mba->get_mblock(cfi.iDispatch)->predset)
	{
		mblock_t *mb = mba->get_mblock(iDispPred);

		if (mb->nsucc() != 1 && mb->nsucc() != 2)
		{
			debugmsg("[E] nsucc check: The dispatcher predecessor %d had %d successors, not 1&2 (continue)\n", iDispPred, mb->nsucc());
			continue;
		}
		bool bJcond = false;
		if (mb->nsucc() == 2)
		{
			bJcond = mb->tail != NULL && is_mcode_jcond(mb->tail->opcode) && mb->tail->d.b == cfi.iDispatch;
			if (!bJcond)
			{
				debugmsg("[E] nsucc 2 but !bJcond: The dispatcher predecessor %d (continue)\n", iDispPred, mb->nsucc());
				continue;
			}
		}

		// Find the block that dominates this cluster, or skip this block if
		// we can't. This ensures that we only try to unflatten parts of the
		// control flow graph that were actually flattened. Also, we need the
		// cluster head so we know where to bound our searches for numeric
		// definitions.
		int iClusterHead;
		mblock_t *mbClusterHead = GetDominatedClusterHead(mba, iDispPred, iClusterHead);
		if (mbClusterHead == NULL)
		{
			debugmsg("[I] Dominator tree algorithm didn't work for predecessor %d\n", iDispPred);
			mbClusterHead = mb;
		}

		// It's best to process erasures for every block we unflatten
		// immediately, so we don't end up duplicating instructions that we
		// want to eliminate
		m_DeferredErasuresLocal.clear();

		// Try to find a numeric assignment to the assignment variable, but
		// pass false for the last parameter so that the search stops if it
		// reaches a block with more than one successor. This ought to succeed
		// if the flattened control flow region only has one destination,
		// rather than two destinations for flattening of if-statements.
		int iDestNo = FindBlockTargetOrLastCopy(mb, mbClusterHead, cfi.opAssigned, true, true);

		// Stash off a copy of the last variable in the chain of assignments
		// to the assignment variable, as well as the assignment instruction
		// (the latter only for debug-printing purposes).
		mop_t *opCopy;
		if (m_DeferredErasuresLocal.empty())
			opCopy = cfi.opAssigned;
		else
			opCopy = m_DeferredErasuresLocal.back().opCopy;
		// set the block number of the pred true case if the last assignment is block sub-comparison variable (TODO: the validation with more sample cases needed)
		if (iDestNo < 0 && cfi.opSubCompared != NULL && equal_mops_ignore_size(*opCopy, *cfi.opSubCompared))
		{
			debugmsg("[I] The dispatcher predecessor = %d: the last assignment is block sub-comparison variable (useless loop condition)\n", iDispPred);
			mblock_t *pred = mba->get_mblock(mb->pred(0));
			if (is_mcode_jcond(pred->tail->opcode))
			{
				iDestNo = pred->tail->d.b;
				debugmsg("[I] The dispatcher predecessor = %d: the destination is set to the block number of the pred true case %d\n", iDispPred, iDestNo);
			}
		}

		// Did we find a block target? Great; just update the CFG to point the
		// destination directly to its target, rather than back to the
		// dispatcher.
		if (iDestNo >= 0)
		{
			// Erase the intermediary assignments to the assignment variable
			ProcessErasures(mba);

			if (bJcond)
			{
				dgm.Replace(mb->serial, cfi.iDispatch, iDestNo);
				mb->tail->d.b = iDestNo;
				debugmsg("[*] The dispatcher predecessor = %d (conditional jump true case), cluster head = %d, destination = %d\n", iDispPred, iClusterHead, iDestNo);
			}
			else
			{
				// Make a note to ourselves to modify the graph structure later
				dgm.ChangeGoto(mb, cfi.iDispatch, iDestNo);
				debugmsg("[*] The dispatcher predecessor = %d (goto), cluster head = %d, destination = %d\n", iDispPred, iClusterHead, iDestNo);
			}
			mb->mark_lists_dirty();

			// add the block if the dest is BLT_STOP
			if (iDestNo == iStop)
				stopPreds.add(mb->serial);

			++iChanged;
			continue;
		}

/*#if UNFLATTENVERBOSE
		debugmsg("[I] Block %d did not define assign a number to assigned var; assigned %s instead\n", iDispPred, mopt_t_to_string(m->l.t));
#endif*/

		// I rarely observed mblock_t::npred() returns 0 or 1 though they have 2 preds in MMAT_GLBOPT2. What should I do?
		//uint64 nPred = mb->npred() >= mb->predset.alloc ? mb->npred() : mb->predset.alloc;
		if (mb->npred() < 2 && !cfi.bTrackingFirstBlocks)
			{
			debugmsg("[*] The dispatcher predecessor %d at %#x that assigned non-numeric value had %d predecessors (<2). And the function has no jcc in the first blocks (continue)\n", iDispPred, mb->start, mb->npred());
			continue;
		}

		mblock_t *endsWithJcc = NULL;
		mblock_t *nonJcc = NULL;
		int actualGotoTarget, actualJccTarget;

		// Call the function that handles the case of a conditional assignment
		// to the assignment variable (i.e., the flattened version of an
		// if-statement).
		if (HandleTwoPreds(mb, mbClusterHead, opCopy, endsWithJcc, nonJcc, actualGotoTarget, actualJccTarget))
		{
			if (bJcond)
				debugmsg("[*] HandleTwoPreds: The dispatcher predecessor = %d (conditional jump true case), actualGotoTarget from endsWithJcc = %d, actualJccTarget from nonJcc = %d\n", mb->serial, actualGotoTarget, actualJccTarget);
			else
				debugmsg("[*] HandleTwoPreds: The dispatcher predecessor = %d (goto), actualGotoTarget from endsWithJcc = %d, actualJccTarget from nonJcc = %d\n", mb->serial, actualGotoTarget, actualJccTarget);

			int iCopied = PostHandleTwoPreds(dgm, mb, cfi.iDispatch, actualGotoTarget, nonJcc, actualJccTarget);

			// add the block if the dest is BLT_STOP
			if (bJcond)
			{
				if (actualGotoTarget == iStop)
					stopPreds.add(mb->serial);
				if (actualJccTarget == iStop && iCopied != -1)
					stopPreds.add(iCopied); // copied mb's serial
			}
			else
			{
				if (actualGotoTarget == iStop)
					stopPreds.add(mb->serial);
				if (actualJccTarget == iStop)
					stopPreds.add(nonJcc->serial);
			}

			// If it succeeded...
			// Get rid of the superfluous assignments
			ProcessErasures(mba);

			// Mark that the def-use information will need re-analyzing
			bDirtyChains = true;
		}
		// goto n preds
		else if (endsWithJcc == NULL && nonJcc == NULL && mb->npred() >= 2)
		{
			for (int i = 0; i < mb->npred(); i++)
			{
				mblock_t *pred = mba->get_mblock(mb->pred(i));
				bool bJcondPred = pred->tail != NULL && is_mcode_jcond(pred->tail->opcode);

				// reset the cluster head for the pred
				int iClusterHeadForPred;
				mblock_t *mbClusterHeadForPred = GetDominatedClusterHead(mba, pred->serial, iClusterHeadForPred);
				if (mbClusterHeadForPred == NULL)
					mbClusterHeadForPred = pred;

				int iDestPred = FindBlockTargetOrLastCopy(pred, mbClusterHeadForPred, opCopy, true, true);
				if (iDestPred >= 0)
				{
					if (bJcond || bJcondPred)
					{
						debugmsg("[*] goto n preds: The dispatcher predecessor = %d (conditional jump true case bJcond=%d, bJcondPred=%d), pred index %d (%d -> %d)\n", mb->serial, bJcond, bJcondPred, i, pred->serial, iDestPred);

						if (i == 0)
						{
							// just update mb
							UpdateDestBlockNumber(dgm, mb, cfi.iDispatch, iDestPred);
							// add the block if the dest is BLT_STOP
							if (iDestPred == iStop)
								stopPreds.add(mb->serial);
						}
						else
						{
							// copy the block (or conditional blocks) for each pred
							int iCopied = CopyAndConnectBlocksToPred(dgm, mb, pred, iDestPred);
							// add the block if the dest is BLT_STOP
							if (iDestPred == iStop && iCopied != -1)
								stopPreds.add(iCopied);
						}
					}
					else
					{
						debugmsg("[*] goto n preds: The dispatcher predecessor = %d (goto), pred index %d (%d -> %d)\n", mb->serial, i, pred->serial, iDestPred);

						// change the destination from mb->serial to iDestPred
						DisconnectBlockFromPred(dgm, mb, pred, iDestPred);
						// add the block if the dest is BLT_STOP
						if (iDestPred == iStop)
							stopPreds.add(pred->serial);
					}
				}
				// for flattened conditional predecessors
				else if (pred->npred() == 2 && HandleTwoPreds(pred, mbClusterHeadForPred, opCopy, endsWithJcc, nonJcc, actualGotoTarget, actualJccTarget))
				{
					if (bJcond || bJcondPred)
					{
						debugmsg("[*] HandleTwoPreds + goto n preds combo: The dispatcher predecessor = %d (conditional jump true case), pred index %d block number %d, actualGotoTarget from endsWithJcc = %d, actualJccTarget from nonJcc = %d\n", mb->serial, i, pred->serial, actualGotoTarget, actualJccTarget);

						mblock_t *mbCopy, *predCopy;

						// copy and connect #1: copied mb to each pred
						int iCopied = CopyAndConnectBlocksToPred(dgm, mb, pred, cfi.iDispatch);
						if (iCopied != -1)
						{
							mbCopy = mba->get_mblock(iCopied);

							// copy and connect #2: copied pred to nonJcc
							int iCopied = CopyAndConnectBlocksToPred(dgm, pred, nonJcc, mbCopy->serial);
							if (iCopied != -1)
							{
								predCopy = mba->get_mblock(iCopied);

								// the same operations as ones in HandleTwoPreds case
								iCopied = PostHandleTwoPreds(dgm, mbCopy, cfi.iDispatch, actualGotoTarget, predCopy, actualJccTarget);

								// add the block if the dest is BLT_STOP
								if (actualGotoTarget == iStop)
									stopPreds.add(mbCopy->serial);
								if (actualJccTarget == iStop && iCopied != -1)
									stopPreds.add(iCopied); // copied mbCopy's serial
							}
						}
					}
					else
					{
						debugmsg("[*] HandleTwoPreds + goto n preds combo: The dispatcher predecessor = %d (goto), pred index %d block number %d, actualGotoTarget from endsWithJcc = %d, actualJccTarget from nonJcc = %d\n", mb->serial, i, pred->serial, actualGotoTarget, actualJccTarget);

						// 1st copy: mb code to the pred tail
						CopyOrAppendMinsns(mb, pred);

						// the same operations as ones in HandleTwoPreds case
						PostHandleTwoPreds(dgm, pred, mb->serial, actualGotoTarget, nonJcc, actualJccTarget);

						// add the block if the dest is BLT_STOP
						if (actualGotoTarget == iStop)
							stopPreds.add(pred->serial);
						if (actualJccTarget == iStop)
							stopPreds.add(nonJcc->serial);
					}
				}
				else
					debugmsg("[E] goto n preds: The dispatcher predecessor = %d, pred index %d block number %d, destination not found\n", mb->serial, i, pred->serial);
			}

			// ProcessErasures should be called after taking care of all preds
			ProcessErasures(mba);
			bDirtyChains = true;
		}
		// For the case when the update variables for if-statement are assigned in the first blocks
		else if (cfi.bTrackingFirstBlocks && !equal_mops_ignore_size(*opCopy, *cfi.opAssigned)) // assignment in advance is necessary
		{
			if (!FindJccInFirstBlocks(mba, opCopy, endsWithJcc, nonJcc, actualGotoTarget, actualJccTarget))
			{
				debugmsg("[E] first blocks: The dispatcher predecessor = %d, FindJccInFirstBlocks failed (continue)\n", mb->serial);
				continue;
			}

			if (bJcond)
				debugmsg("[*] first blocks: The dispatcher predecessor = %d (conditional jump true case), endsWithJcc = %d & actualGotoTarget = %d, nonJcc = %d & actualJccTarget = %d\n", mb->serial, endsWithJcc->serial, actualGotoTarget, nonJcc->serial, actualJccTarget);
			else
				debugmsg("[*] first blocks: The dispatcher predecessor = %d (goto), endsWithJcc = %d & actualGotoTarget = %d, nonJcc = %d & actualJccTarget = %d\n", mb->serial, endsWithJcc->serial, actualGotoTarget, nonJcc->serial, actualJccTarget);

			ProcessErasures(mba);
			bDirtyChains = true;

			// dispatcher predecessor -> endsWithJcc
			if (bJcond)
			{
				dgm.Replace(mb->serial, cfi.iDispatch, endsWithJcc->serial);
				mb->tail->d.b = endsWithJcc->serial;
			}
			else
				dgm.ChangeGoto(mb, cfi.iDispatch, endsWithJcc->serial);
			// endsWithJcc true case -> actualGotoTarget
			int JccTrueSerial = endsWithJcc->succ(0) == nonJcc->serial ? endsWithJcc->succ(1) : endsWithJcc->succ(0);
			dgm.Replace(endsWithJcc->serial, JccTrueSerial, actualGotoTarget);
			endsWithJcc->tail->d.b = actualGotoTarget;
			// nonJcc -> actualJccTarget
			dgm.ChangeGoto(nonJcc, nonJcc->succ(0), actualJccTarget);

			// add the block if the dest is BLT_STOP
			if (actualGotoTarget == iStop)
				stopPreds.add(endsWithJcc->serial);
			if (actualJccTarget == iStop)
				stopPreds.add(nonJcc->serial);

			// Probably all blocks have the instruction modification
			mb->mark_lists_dirty();
			//endsWithJcc->mark_lists_dirty();
			nonJcc->mark_lists_dirty();
		}
		else
			debugmsg("[*] end of loop: The dispatcher predecessor = %d at %#x\n", mb->serial, mb->start);
	} // end for loop that unflattens all blocks

	// fix/append jump in the pred of the last block to pass control correctly
	CorrectStopBlockPreds(dgm, mba, stopPreds);

	// After we've processed every block, apply the deferred modifications to
	// the graph structure.
	iChanged += dgm.Apply(mba);

#if UNFLATTENDEBUG
	for (mblock_t *mb = mba->get_mblock(0); mb->nextb != NULL; mb = mb->nextb)
		CheckInterr50860(mb);
#endif

	// If there were any two-way conditionals, that means we copied
	// instructions onto the jcc taken blocks, which means the def-use info is
	// stale. Mark them dirty, and perform local optimization for the lulz too.
	if (bDirtyChains)
	{
#if IDA_SDK_VERSION == 710
		mba->make_chains_dirty();
#elif IDA_SDK_VERSION >= 720
		mba->mark_chains_dirty();
#endif
		mba->optimize_local(0);
	}

	// If we changed the graph, verify that we did so legally.
	if (iChanged != 0)
		mba->verify(true);

	return iChanged;
}
