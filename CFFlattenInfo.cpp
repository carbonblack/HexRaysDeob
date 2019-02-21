#include <hexrays.hpp>
#include "HexRaysUtil.hpp"
#include "CFFlattenInfo.hpp"
#include "Config.hpp"

#define MIN_NUM_COMPARISONS 2

extern std::set<ea_t> g_BlackList;
extern std::set<ea_t> g_WhiteList;


static int debugmsg(const char *fmt, ...)
{
#if UNFLATTENVERBOSE
	va_list va;
	va_start(va, fmt);
	return vmsg(fmt, va);
#endif
	return 0;
}

// This method determines whether a given function is likely obfuscated. It 
// does this by ensuring that:
// 1) Some minimum number of comparisons are made against the "comparison 
//    variable"
// 2) The constant values used in the comparisons are sufficiently entropic.
bool JZInfo::ShouldBlacklist()
{
	// This check is pretty weak. I thought I could set the minimum number to 
	// 6, but the pattern deobfuscators might eliminate some of them before 
	// this function gets called.
	if (nSeen < MIN_NUM_COMPARISONS)
	{
#if UNFLATTENVERBOSE
		debugmsg("[I] Blacklisting due to lack of JZ/JG comparisons (%d < minimum of %d)\n", nSeen, MIN_NUM_COMPARISONS);
#endif
		return true;
	};

	// Count the number of 1-bits in the constant values used for comparison
	int iNumBits = 0;
	int iNumOnes = 0;
	for (auto num : nums)
	{
		iNumBits += num->size * 8;
		uint64 v = num->nnn->value;
		for (int i = 0; i < num->size * 8; ++i)
		{
			if (v & (1 << i))
				++iNumOnes;
		}
	}
	
	// Compute the percentage of 1-bits. Given that these constants seem to be
	// created pseudorandomly, the percentage should be roughly 1/2.
	float fEntropy = iNumBits == 0 ? 0.0 : (float)iNumOnes / (float(iNumBits));
#if UNFLATTENVERBOSE
	debugmsg("[I] %d comparisons, %d numbers, %d bits, %d ones, %f entropy\n",
		nSeen,
		nums.size(),
		iNumBits,
		iNumOnes,
		fEntropy);
#endif

	// We'll give 10% leeway on the 50% expectation.
	//if (fEntropy < 0.4 || fEntropy > 0.6)
	if (fEntropy < 0.32 || fEntropy > 0.65) // adjust for checking in high maturity level
	{
		debugmsg("[I] Entropy %f indicates this function is not obfuscated\n", fEntropy);
		return true;
	}
	return false;
}


// This class looks for jz/jg comparisons against constant values. For each
// thing being compared, we use a JZInfo structure to collect the number of 
// times it's been used in a comparison, and a list of the values it was
// compared against.
struct JZCollector : public minsn_visitor_t
{
	std::vector<JZInfo> m_SeenComparisons;
	int m_nMaxJz;

	JZCollector() : m_nMaxJz(-1) {};

	int visit_minsn(void)
	{
		// We're looking for jz/jg instructions...
		//if (curins->opcode != m_jz && curins->opcode != m_jg)
		if (curins->opcode != m_jz && curins->opcode != m_jg && curins->opcode != m_jnz && curins->opcode != m_jle)
			return 0;

		// ... which compare something against a number ...
		if (curins->r.t != mop_n)
			return 0;

		int iFound = 0;
		mop_t *thisMop = &curins->l;

		int idxFound = 0;
		// Search for the comparison operand in the saved information
		for (auto &sc : m_SeenComparisons)
		{
			if (equal_mops_ignore_size(*sc.op, *thisMop))
			{
				// If found, update the counter and save the number
				sc.nSeen += 1;
				sc.nums.push_back(&curins->r);
				iFound = sc.nSeen;
				break;
			}
			++idxFound;
		}
		
		// If we didn't find it in the vector, create a new JZInfo structure
		if (!iFound)
		{
			m_SeenComparisons.emplace_back();
			JZInfo &jz = m_SeenComparisons.back();
			jz.op = thisMop;
			jz.nSeen = 1;
			jz.nums.push_back(&curins->r);
			iFound = 1;
		}

		// If the variable we just saw has been used more often than the previous
		// candidate, mark this variable as the new candidate
		if (m_nMaxJz < 0 || iFound > m_SeenComparisons[m_nMaxJz].nSeen)
			m_nMaxJz = idxFound;

		return 0;
	}
};

// This function finds the "first" block immediately before the control flow
// flattening dispatcher begins. The logic is simple; start at the beginning
// of the function, keep moving forward until the next block has more than one
// predecessor. As it happens, this is where the assignment to the switch 
// dispatch variable takes place, and that's mostly why we want it.
// The information is recorded in the arguments iFirst and iDispatch.
mblock_t *GetFirstBlock(mbl_array_t *mba, int &iFirst, int &iDispatch)
{
	// Initialise iFirst and iDispatch to erroneous values
	iFirst = -1, iDispatch = -1;
	
	int iCurr = 0, iPred = 0;
	int npred_max = MIN_NUM_COMPARISONS;
	bool bFound = false;

	// search for the block with maximum preds
	for (mblock_t *mb = mba->get_mblock(0); mb->nextb != NULL; mb = mb->nextb)
	{
		//if (npred_max < mb->npred())
		if (npred_max < mb->npred() && mb->tail != NULL && is_mcode_jcond(mb->tail->opcode))
		{
			if (mb->tail->r.t != mop_n)
				continue;
			if (mb->tail->l.t == mop_r || (mb->tail->l.t == mop_d && mb->tail->l.d->opcode == m_and))
			{
				npred_max = mb->npred();
				iDispatch = mb->serial;
			}
		}
	}
	// extract the minimum block id (probably it's the "first" block)
	if (iDispatch != -1)
	{
		iFirst = mba->get_mblock(iDispatch)->pred(0); // it's rough but works mostly
		if (iFirst >= iDispatch) // or check the minimum number gently
		{
			int iMinNum = iDispatch;
			for (int i = 0; i < mba->get_mblock(iDispatch)->npred(); i++)
			{
				iCurr = mba->get_mblock(iDispatch)->pred(i);
				//iPred = mba->get_mblock(iCurr)->pred(0);
				//if (iCurr < iMinNum && mba->get_mblock(iPred)->tail != NULL && !is_mcode_jcond(mba->get_mblock(iPred)->tail->opcode))
				if (iCurr < iMinNum)
					iMinNum = iCurr;
			}
			iFirst = iMinNum;
		}
		// The following code is not available for multiple control dispatchers
		/*for (int i = 0; i < mba->get_mblock(iDispatch)->npred(); i++)
		{
			iCurr = mba->get_mblock(iDispatch)->pred(i);
			while (1) // tracking the pred to detect a loop
			{
				iPred = mba->get_mblock(iCurr)->pred(0);
				int prevNpred = mba->get_mblock(iPred)->npred();

				if (prevNpred == 0 || prevNpred == mba->get_mblock(iDispatch)->npred()) // tracking is done
				{
					if (prevNpred == 0) // not back to dispatch (that means it's the first block)
						bFound = true;
					break;
				}
				iCurr = iPred;
			}
			if (bFound)
			{
				iFirst = mba->get_mblock(iDispatch)->pred(i);
				break;
			}
		}*/
	}

	if (iFirst != -1)
		return mba->get_mblock(iFirst);
	else
	{
#if UNFLATTENVERBOSE
		debugmsg("[E] Dispatcher block could not be found \n");
#endif
		return NULL;
	}
}

// This class is used to find all variables that have 32-bit numeric values 
// assigned to them in the first block (as well as the values that are 
// assigned to them).
struct BlockInsnAssignNumberExtractor : public minsn_visitor_t
{
	std::vector<std::pair<mop_t *, uint64> > m_SeenAssignments;
	int visit_minsn()
	{
		// We're looking for MOV(const.4,x)
		if (curins->opcode != m_mov || curins->l.t != mop_n || curins->l.size != 4)
			return 0;

		// Record all such information in the vector
		m_SeenAssignments.push_back(std::pair<mop_t *, uint64>(&curins->d, curins->l.nnn->value));
		return 0;
	}
};

// Protected functions might use either one, or two, variables for the switch
// dispatch number. If it uses two, one of them is the "update" variable, whose
// contents will be copied into the "comparison" variable in the first dispatch
// block. This class is used to locate the "update" variable, by simply looking
// for a variable whose contents are copied into the "comparison" variable, 
// which must have had a number assigned to it in the first block.
struct HandoffVarFinder : public minsn_visitor_t
{
	// We're looking for assignments to this variable
	mop_t *m_ComparisonVar;
	
	// These are the numeric assignments from the first block
	std::vector<std::pair<mop_t *, uint64> > &m_SeenAssignments;
	
	// This information is generated by this class. Namely, it's a list of 
	// variables that are seen copied into the comparison variable, as well
	// as a count of the number of times it is copied.
	std::vector<std::pair<mop_t *, int> > m_SeenCopies;
	/*std::vector<std::tuple<mop_t *&, int&, uint64&>> m_SeenCopies;
	int cnt = 1;*/
	uint64 andImm = 0;

	HandoffVarFinder(mop_t *opMax, std::vector<std::pair<mop_t *, uint64> > &assignments) :
		m_ComparisonVar(opMax),
		m_SeenAssignments(assignments)
	{};

	int visit_minsn(void)
	{
		// We want copies into our comparison variable
		//if (curins->opcode != m_mov || !equal_mops_ignore_size(curins->d, *m_ComparisonVar))
		if ((curins->opcode != m_mov && curins->opcode != m_and) || !equal_mops_ignore_size(curins->d, *m_ComparisonVar))
			return 0;

		// Iterate through the numeric assignments from the first block. These
		// are our candidates.
		for (auto &as : m_SeenAssignments)
		{
			if (equal_mops_ignore_size(curins->l, *as.first))
			{
				// If we found a copy into our comparison variable from a 
				// variable that was assigned to a constant in the first block,
				// add it to the vector (or increment its counter if it was
				// already there).
				bool bFound = false;
				for (auto sc : m_SeenCopies)
				{
					if (equal_mops_ignore_size(*as.first, *sc.first))
					//if (equal_mops_ignore_size(*as.first, *std::get<0>(sc)))
						{
						sc.second += 1;
						//std::get<1>(sc) += 1;
						if (curins->opcode == m_and && curins->r.nnn->value != 0)
							//std::get<2>(sc) = curins->r.nnn->value;
							andImm = curins->r.nnn->value;
						bFound = true;
					}
				}
				if (!bFound)
				{
					m_SeenCopies.push_back(std::pair<mop_t *, int>(as.first, 1));
					if (curins->opcode == m_and && curins->r.nnn->value != 0)
						andImm = curins->r.nnn->value;
					//m_SeenCopies.push_back(std::tuple<mop_t *, int, uint64>(as.first, 1, 0));
					/*std::tuple<mop_t *&, int&, uint64&> t = std::tie(as.first, cnt, andImm);
					m_SeenCopies.push_back(t);*/
				}
			}
		}
		return 0;
	}
};

// Once we know which variable is the one used for comparisons, look for all
// jz instructions that compare a number against this variable. This then tells
// us which number corresponds to which basic block.
struct JZMapper : public minsn_visitor_t
{
	std::map<uint64, int> &m_KeyToBlock;
	std::map<int, uint64> &m_BlockToKey;
	std::map<uint64, ea_t> &m_KeyToEA;
	std::map<ea_t, uint64> &m_EAToKey;
	mop_t *m_CompareVar;
	mop_t *m_SubCompareVar;
	mop_t *m_AssignVar;
	int m_DispatchBlockNo;
	//JZMapper(mop_t *mc, mop_t *ma, int iFirst, std::map<uint64, int> &map, std::map<int, uint64> &map2) :
	JZMapper(mop_t *mc, mop_t *mc_sub, mop_t *ma, int iFirst, std::map<uint64, int> &map, std::map<int, uint64> &map2, std::map<uint64, ea_t> &map3, std::map<ea_t, uint64> &map4) :
		m_CompareVar(mc),
		m_SubCompareVar(mc_sub),
		m_AssignVar(ma),
		m_DispatchBlockNo(iFirst),
		m_KeyToBlock(map),
		//m_BlockToKey(map2) {};
		m_BlockToKey(map2),
		m_KeyToEA(map3),
		m_EAToKey(map4) {};

	int visit_minsn(void)
	{
		// We're looking for jz instructions that compare a number ...
		//if (curins->opcode != m_jz || curins->r.t != mop_n)
		if ((curins->opcode != m_jz && curins->opcode != m_jnz) || curins->r.t != mop_n)
			return 0;

		// ... against our comparison variable ...
		//if (!equal_mops_ignore_size(*m_CompareVar, curins->l))
		// get all maps for multiple dispatchers in MMAT_DEOB_MAP
		if (!equal_mops_ignore_size(*m_CompareVar, curins->l) && mba->maturity != MMAT_DEOB_MAP)
		{
			// ... or, if it's the dispatch block, possibly the assignment variable ...
			if (blk->serial != m_DispatchBlockNo || !equal_mops_ignore_size(*m_AssignVar, curins->l))
			{
				// or if it's sub-comparison var, include the map
				if (m_SubCompareVar == NULL)
					return 0;
				else if (!equal_mops_ignore_size(*m_SubCompareVar, curins->l))
					return 0;
			}
		}

		// ... and the destination of the jz must be a block
		if(curins->d.t != mop_b)
			return 0;

		// Record the information in two maps
		uint64 keyVal = curins->r.nnn->value;
		int blockNo;
		if (curins->opcode == m_jz)
			blockNo = curins->d.b;
		else
			blockNo = blk->serial + 1;

		// If the block number is dispatcher, the actual number actually points to the block itself
		if (blockNo == m_DispatchBlockNo)
		{
#if UNFLATTENVERBOSE
			debugmsg("[I] JZMapper: changed blockNo (dispatcher to the current %d)\n", blk->serial);
#endif
			blockNo = blk->serial;
		}

		if (mba->maturity == MMAT_DEOB_MAP)
		{
			//ea_t ea = mba->get_mblock(blockNo)->start;
			//ea_t ea = mba->get_mblock(blockNo)->head->ea;
			ea_t ea = (mba->get_mblock(blockNo)->start + mba->get_mblock(blockNo)->end - 1) / 2;
#if UNFLATTENVERBOSE
			const char *matStr = MicroMaturityToString(mba->maturity);
			debugmsg("[I] %s: Inserting %08lx -> ea %08lx into map\n", matStr, (uint32)keyVal, ea);
#endif
			m_KeyToEA[keyVal] = ea;
			m_EAToKey[ea] = keyVal;
		}
		else // later maturity level
		{
#if UNFLATTENVERBOSE
			const char *matStr = MicroMaturityToString(mba->maturity);
			debugmsg("[I] %s: Inserting %08lx -> block ID %d into map\n", matStr, (uint32)keyVal, blockNo);
#endif
			m_KeyToBlock[keyVal] = blockNo;
			m_BlockToKey[blockNo] = keyVal;
		}

		return 0;
	}
};

// Compute dominator information for the function.
array_of_bitsets *ComputeDominators(mbl_array_t *mba)
{
	int iNumBlocks = mba->qty;
	assert(iNumBlocks >= 1);

	// Use Hex-Rays' handy array_of_bitsets to represent dominators
	array_of_bitsets *domInfo = new array_of_bitsets;
	domInfo->resize(iNumBlocks);
	
	// Per the algorithm, initialize each block to be dominated by every block
	for (auto &bs : *domInfo)
		bs.fill_with_ones(iNumBlocks - 1);

	// ... except the first block, which only dominates itself
	domInfo->front().clear();
	domInfo->front().add(0);

	// Now we've got a standard, not-especially-optimized dataflow analysis 
	// fixedpoint computation...
	bool bChanged;
	do
	{
		bChanged = false;
		// For every block...
		for (int i = 1; i < iNumBlocks; ++i)
		{
			// Grab its current dataflow value and copy it
			bitset_t &bsCurr = domInfo->at(i);
			bitset_t bsBefore(bsCurr);
			
			// Get that block from the graph
			mblock_t *blockI = mba->get_mblock(i);
			
			// Iterate over its predecessors, intersecting their dataflow 
			// values against this one's values
			for (int j = 0; j < blockI->npred(); ++j)
				bsCurr.intersect(domInfo->at(blockI->pred(j)));

			// Then, re-indicate that the block dominates itself
			bsCurr.add(i);

			// If this process changed the dataflow information, we're going to
			// need another iteration
			bChanged |= bsBefore != bsCurr;
		}
	} 
	// Keep going until the dataflow information stops changing
	while (bChanged);

	// The dominator information has been computed. Now we're going to derive 
	// some information from it. Namely, the current representation tells us,
	// for each block, which blocks dominate it. We want to know, instead, for
	// each block, which blocks are dominated by it. This is a simple 
	// transformation; for each block b and dominator d, update the information
	// for d to indicate that it dominates b.
	
	// Create a new array_of_bitsets
	array_of_bitsets *domInfoOutput = new array_of_bitsets;
	domInfoOutput->resize(iNumBlocks);
	
	// Iterate over each block
	for (int i = 0; i < iNumBlocks; ++i)
	{
		// Get the dominator information for this block (b)
		bitset_t &bsCurr = domInfo->at(i);
		
		// For each block d that dominates this one, mark that d dominates b
		for (auto it = bsCurr.begin(); it != bsCurr.end(); bsCurr.inc(it))
			domInfoOutput->at(*it).add(i);
	}
	
	// Don't need the original dominator information anymore; get rid of it
	delete domInfo;
	
	// Just return the inverted dominator information
	return domInfoOutput;
}

// Convenience function to look up a block number by its key. This way, we can
// write the iterator-end check once, so clients don't have to do it.
int CFFlattenInfo::FindBlockByKey(uint64 key)
{
	if (m_KeyToBlock.find(key) == m_KeyToBlock.end())
		return -1;
	return m_KeyToBlock[key];
}

int CFFlattenInfo::TranslateEA2Block(ea_t ea, mbl_array_t *mba)
{
	// 1st try for mblock_t start/end
	for (mblock_t *mb = mba->get_mblock(1); mb != NULL; mb = mb->nextb)
		{
		if (mb->start == -1 || mb->end == -1)
			continue;
		int64 min = mb->start;
		int64 max = mb->end - 1;
		if (min <= ea && ea <= max)
			return mb->serial;
	}
	// 2nd try for mblock_t start/end or minsn_t ea (aggresive and less reliable)
	for (mblock_t *mb = mba->get_mblock(1); mb != NULL; mb = mb->nextb)
	{
		if (mb->start == -1 || mb->end == -1 || mb->head == NULL || mb->tail == NULL)
			continue;
		ea_t ea_min = BADADDR, ea_max = 0;
		for (minsn_t *p = mb->head; p != NULL; p = p->next)
		{
			if (p->ea < ea_min)
				ea_min = p->ea;
			if (p->ea > ea_max)
				ea_max = p->ea;
		}
		ea_t min = mb->start < ea_min ? mb->start : ea_min;
		ea_t max = mb->end - 1 > ea_max ? mb->end - 1 : ea_max;
		if (min <= ea && ea <= max)
			return mb->serial;
	}
/*#if UNFLATTENVERBOSE
	msg("[E] ea %08lx in MMAT_LOCOPT cannot be translated to block ID in MMAT_GLBOPT2\n", ea);
#endif*/
	return -1;
}

int CFFlattenInfo::FindBlockByKeyFromEA(uint64 key, mbl_array_t *mba)
{
	if (m_KeyToEA.find(key) == m_KeyToEA.end())
		return -1;
	ea_t ea = m_KeyToEA[key];
	int serial = TranslateEA2Block(ea, mba);
#if UNFLATTENVERBOSE
	const char *matStrOld = MicroMaturityToString(MMAT_DEOB_MAP);
	const char *matStr = MicroMaturityToString(mba->maturity);
	if (serial == -1)
		msg("[E] FindBlockByKeyFromEA: block key %08lx (ea=%08lx) cannot be translated\n", key, ea);
	else
		msg("[I] FindBlockByKeyFromEA: block key %08lx (ea=%08lx) in %s is translated to block ID %d in %s\n", key, ea, matStrOld, serial, matStr);
#endif
	return serial;
}

// This function computes all of the preliminary information needed for 
// unflattening.
bool CFFlattenInfo::GetAssignedAndComparisonVariables(mblock_t *blk)
{
	// Ensure that this function hasn't been blacklisted (e.g. because entropy
	// calculation indicates that it isn't obfuscated).
	mbl_array_t *mba = blk->mba;
	Clear(true, mba->maturity); // // Erase any existing information in this structure.
	if (g_BlackList.find(mba->entry_ea) != g_BlackList.end())
		return false;

	// There's also a separate whitelist for functions that were previously 
	// seen to be obfuscated.
	bool bWasWhitelisted = g_WhiteList.find(mba->entry_ea) != g_WhiteList.end();

	// Look for the variable that was used in the largest number of jz/jg 
	// comparisons against a constant. This is our "comparison" variable.
	JZCollector jzc;
	mba->for_all_topinsns(jzc);
	if (jzc.m_nMaxJz < 0)
	{
		// If there were no comparisons and we haven't seen this function 
		// before, blacklist it.
#if UNFLATTENVERBOSE
		debugmsg("[I] No comparisons seen; failed\n");
#endif
		if (!bWasWhitelisted)
			g_BlackList.insert(mba->entry_ea);
		return false;
	}

	// Otherwise, we were able to find jz comparison information. Use that to
	// determine if the constants look entropic enough. If not, blacklist this
	// function. If so, whitelist it.
	//if (!bWasWhitelisted)
	if (!bWasWhitelisted && mba->maturity != MMAT_DEOB_MAP)
	{
		if (jzc.m_SeenComparisons[jzc.m_nMaxJz].ShouldBlacklist())
		{
			g_BlackList.insert(mba->entry_ea);
			return false;
		}
		g_WhiteList.insert(mba->entry_ea);
	}

	// Find the "first" block in the function, the one immediately before the
	// control flow switch.
	mblock_t *first = GetFirstBlock(mba, this->iFirst, this->iDispatch);
	if (first == NULL)
	{
#if UNFLATTENVERBOSE
		debugmsg("[E] Can't find top-level block in function\n");
#endif
		return false;
	}
#if UNFLATTENVERBOSE
	const char *matStr = MicroMaturityToString(mba->maturity);
	msg("[I] %s: found first block id %d (ea=%#x), dispatcher id %d (ea=%#x) \n", matStr, this->iFirst, mba->get_mblock(this->iFirst)->start, this->iDispatch, mba->get_mblock(this->iDispatch)->start);
#endif

	// opMax is our "comparison" variable used in the control flow switch.
	mop_t *opMax = jzc.m_SeenComparisons[jzc.m_nMaxJz].op;
#if UNFLATTENVERBOSE
	qstring tmpo;
	get_mreg_name(&tmpo, opMax->r, opMax->size);
	msg("[I] %s: Comparison variable = %s\n", matStr, tmpo.c_str());
#endif
	// if there are nested control flow switches, we have to identify the opMax of the dispatcher
	mblock_t *mb_dispatch = mba->get_mblock(this->iDispatch);
	mop_t *opMaxMoreLikely, *opMaxSub;
	for (auto sc : jzc.m_SeenComparisons)
	{
		mlist_t ml;
		mop_t *op = sc.op;
		mb_dispatch->append_use_list(&ml, *op, MUST_ACCESS);

		opMaxMoreLikely = opMaxSub = NULL;
		for (minsn_t *p = mb_dispatch->tail; p != NULL; p = p->prev)
		//for (minsn_t *p = mb_dispatch->head; p != NULL; p = p->next)
		{
			mlist_t def = mb_dispatch->build_def_list(*p, MAY_ACCESS | FULL_XDSU);
			//if ((def.includes(ml) || (p->l.t == mop_r && p->l.r == op->r)) && sc.nSeen > MIN_NUM_COMPARISONS &&
				//(p->opcode == m_jz || p->opcode == m_jg || p->opcode == m_jnz || p->opcode == m_jle || p->opcode == m_and))
			if ((def.includes(ml) || (p->l.t == mop_r && p->l.r == op->r)) && sc.nSeen > MIN_NUM_COMPARISONS)
			{
				if (p->opcode == m_jz || p->opcode == m_jg || p->opcode == m_jnz || p->opcode == m_jle || p->opcode == m_and)
				{
					opMaxMoreLikely = op;
					//break;
				}
				else if (opMaxMoreLikely != NULL && p->opcode == m_mov && p->d.t == mop_r)
				{
					opMaxSub = &p->d;
				}
			}
		}
		if (opMaxMoreLikely != NULL)
			break;
	}
	if (opMaxMoreLikely != NULL && !equal_mops_ignore_size(*opMax, *opMaxMoreLikely))
	{
#if UNFLATTENVERBOSE
		qstring tmpo, tmpn;
		get_mreg_name(&tmpo, opMax->r, opMax->size);
		get_mreg_name(&tmpn, opMaxMoreLikely->r, opMaxMoreLikely->size);
		msg("[I] %s: Comparison variable renewed from %s to %s (probably nested control flow dispatchers)\n", matStr, tmpo.c_str(), tmpn.c_str());
#endif
		opMax = opMaxMoreLikely;
	}

	// Get all variables assigned to numbers in the first block. If we find the
	// comparison variable in there, then the assignment and comparison 
	// variables are the same. If we don't, then there are two separate 
	// variables.
	BlockInsnAssignNumberExtractor fbe;

	// The "first" block sometimes doesn't contain the assignment to the comparison variable
	// So I modified to trace back from the block to the beginning (called first blocks)
	bool bFound = false;
	for (mblock_t *mb = first; mb->prevb != NULL; mb = mb->prevb)
	{
		mb->for_all_insns(fbe);
		// Was the comparison variable assigned a number in the first blocks?
		for (auto as : fbe.m_SeenAssignments)
		{
			if (equal_mops_ignore_size(*as.first, *opMax))
			{
				bFound = true;
				break;
			}
		}
		if (bFound)
			break;
	}

	// This is the "assignment" variable, whose value is updated by the switch
	// case code
	mop_t *localOpAssigned;

	// If the "comparison" variable was assigned a number in the first block, 
	// then the function is only using one variable, not two, for dispatch.
	if (bFound)
		localOpAssigned = opMax;

	// Otherwise, look for assignments of one of the variables assigned a
	// number in the first block to the comparison variable
	else
	{
		// For all variables assigned a number in the first block, find all
		// assignments throughout the function to the comparison variable
		HandoffVarFinder hvf(opMax, fbe.m_SeenAssignments);
		mba->for_all_topinsns(hvf);

		// There should have only been one of them; is that true?
		if (hvf.m_SeenCopies.size() != 1)
		{
#if UNFLATTENVERBOSE
			debugmsg("[E] Comparison var was copied from %d assigned-to-constant variables, not 1 as expected\n", hvf.m_SeenCopies.size());
			for (auto sc : hvf.m_SeenCopies)
				debugmsg("\t%s (%d copies)\n", mopt_t_to_string(sc.first->t), sc.second);
#endif
			return false;
		}

		// If only one variable (X) assigned a number in the first block was 
		// ever copied into the comparison variable, then X is our "assignment"
		// variable.
		localOpAssigned = hvf.m_SeenCopies[0].first;
		if (hvf.andImm)
		{
			this->bOpAndAssign = true;
			this->OpAndImm = hvf.andImm;
#if UNFLATTENVERBOSE
			qstring tmpa;
			get_mreg_name(&tmpa, localOpAssigned->r, localOpAssigned->size);
			msg("[I] %s: Update variable=%d (%s) is assigned by AND instruction with %x\n", matStr, localOpAssigned->r, tmpa.c_str(), this->OpAndImm);
#endif
		}

		// Find the number that was assigned to the assignment variable in the
		// first block.
		bool bFound = false;
		for (auto as : fbe.m_SeenAssignments)
		{
			if (equal_mops_ignore_size(*as.first, *localOpAssigned))
			{
				uFirst = as.second;
				bFound = true;
				break;
			}
		}
		if (!bFound)
		{
			debugmsg("[E] ??? couldn't find assignment to assignment variable?\n");
			return false;
		}
	}
	// Make copies of the comparison and assignment variables so we don't run
	// into liveness issues
	this->opCompared = new mop_t(*opMax);
	this->opAssigned = new mop_t(*localOpAssigned);
	if (opMaxSub != NULL)
		this->opSubCompared = new mop_t(*opMaxSub);
#if UNFLATTENVERBOSE
	qstring tmpc, tmpa, tmpc_sub;
	get_mreg_name(&tmpc, this->opCompared->r, this->opCompared->size);
	get_mreg_name(&tmpa, this->opAssigned->r, this->opAssigned->size);
	if (opMaxSub == NULL)
		msg("[I] %s: register numbers: comparison variable=%d (%s), update variable=%d (%s) \n", matStr, this->opCompared->r, tmpc.c_str(), this->opAssigned->r, tmpa.c_str());
	else
	{
		get_mreg_name(&tmpc_sub, this->opSubCompared->r, this->opSubCompared->size);
		msg("[I] %s: register numbers: comparison variable=%d (%s), update variable=%d (%s), sub comparison variable=%d (%s) \n",
			matStr, this->opCompared->r, tmpc.c_str(), this->opAssigned->r, tmpa.c_str(), this->opSubCompared->r, tmpc_sub.c_str());
	}
#endif

	// Extract the key-to-block mapping for each JZ against the comparison
	// variable
	JZMapper jzm(opCompared, opSubCompared, localOpAssigned, iDispatch, m_KeyToBlock, m_BlockToKey, m_KeyToEA, m_EAToKey);
	mba->for_all_topinsns(jzm);
	if (mba->maturity == MMAT_DEOB_MAP)
		// abort
		return false;

	// Save off the current function's starting EA
	m_WhichFunc = mba->entry_ea;

	// Compute the dominator information for this function and stash it
	array_of_bitsets *ab = ComputeDominators(mba);
	m_DomInfo = ab;
	
	// Compute some more information from the dominators. Basically, once the
	// control flow dispatch switch has transferred control to the function's 
	// code, there might be multiple basic blocks that can execute before 
	// control goes back to the switch statement. For all of those blocks, we
	// want to know the "first" block as part of that region of the graph, 
	// i.e., the one targeted by a jump out of the control flow dispatch 
	// switch.
	
	// Allocate an array mapping each basic block to the block that dominates
	// it and was targeted by the control flow switch.
	int *DominatedClusters = new int[mba->qty];
	memset(DominatedClusters, 0xFF, sizeof(int)*mba->qty);
	
	// For each block/key pair (the targets of the control flow switch)
	for (auto bk : m_EAToKey)
	{
		int i = TranslateEA2Block(bk.first, mba);
		if (i == -1)
			continue;
		// For each block dominated by this control flow switch target, mark
		// that this block its the beginning of its cluster.
		for (auto it = ab->at(i).begin(); it != ab->at(i).end(); ab->at(i).inc(it))
			DominatedClusters[*it] = i;
	}
	for (auto bk : m_BlockToKey)
	{
		int i = bk.first;
		// For each block dominated by this control flow switch target, mark 
		// that this block its the beginning of its cluster.
		for (auto it = ab->at(i).begin(); it != ab->at(i).end(); ab->at(i).inc(it))
			DominatedClusters[*it] = i;
	}
	
	// Save that information off.
	m_DominatedClusters = DominatedClusters;

	// Check if the first blocks may contain block update variables for flattened if-else statement blocks
	//if (this->iFirst % 2 == 1 && this->iFirst > 2 && is_mcode_jcond(mba->get_mblock(1)->tail->opcode))
	if (this->iFirst > 2 && is_mcode_jcond(mba->get_mblock(1)->tail->opcode))
			this->bTrackingFirstBlocks = true;
	else
		this->bTrackingFirstBlocks = false;
	
	// Ready to go!
	return true;
}
