#include <hexrays.hpp>
#include "HexRaysUtil.hpp"
#include "TargetUtil.hpp"

// Append a goto onto a non-empty block, which is assumed not to already have
// a goto at the end of it.
void AppendGotoOntoNonEmptyBlock(mblock_t *blk, int iBlockDest)
{
	assert(blk->tail != NULL);

	// Allocate a new instruction, using the tail address
	minsn_t *newGoto = new minsn_t(blk->tail->ea);

	// Create a goto instruction to the specified block
	newGoto->opcode = m_goto;
	newGoto->l.t = mop_b;
	newGoto->l.b = iBlockDest;

	// Add it onto the block
	blk->insert_into_block(newGoto, blk->tail);
}

// For a block with a single successor, change its target from some old block
// to a new block. This is only on the graph level, not in terms of gotos.
void ChangeSingleTarget(mblock_t *blk, int iOldTarget, int iNewTarget)
{
	assert(blk->nsucc() == 1);
	mbl_array_t *mba = blk->mba;

	// Overwrite the successor with the new target
	blk->succset[0] = iNewTarget;

	// Add this block to the predecessor set of the target
	mba->get_mblock(iNewTarget)->predset.add(blk->serial);

	// Remove this block from the predecessor set of the old target
	mba->get_mblock(iOldTarget)->predset.del(blk->serial);
}

// Reverse engineered from hexrays.dll (though it's obvious). Basically: does
// this block end in a call instruction?
bool is_call_block(mblock_t *blk)
{
	if (blk->tail == NULL)
		return false;

	return blk->tail->opcode == m_call || blk->tail->opcode == m_icall;
}

#define GOTO_NOT_SINGLE -1

// This function eliminates transfers to blocks with a single goto on them.
// Either if a given block has a goto at the end of it, where the destination
// is a block with a single goto on it, or if the block doesn't end in a goto,
// but simply falls through to a block with a single goto on it. Also, this
// process happens recursively; i.e., if A goes to B, and B goes to C, and C
// goes to D, then after we've done our tranformations, A will go to D.
int RemoveSingleGotos(mbl_array_t *mba)
{
	// This information determines, ultimately, to which block a goto will go.
	// As mentioned in the function comment, this accounts for gotos-to-gotos.
	int *forwarderInfo = new int[mba->qty];

	// For each block
	for (int i = 0; i < mba->qty; ++i)
	{
		// Begin by initializing its information to say that it does not
		// consist of a single goto. Update later if it does.
		forwarderInfo[i] = GOTO_NOT_SINGLE;

		// Get the block and skip any "assert" instructions.
		mblock_t *b = mba->get_mblock(i);
		minsn_t *m2 = getf_reginsn(b->head);

		// Is the first non-assert instruction a goto?
		if (m2 == NULL || m2->opcode != m_goto || m2->l.t != mop_b)
			continue;

		// If it was a goto, record the destination block number
		forwarderInfo[i] = m2->l.b;
	}

	int iRetVal = 0;
	// Now, actually replace transfer-to-goto blocks with their destinations.
	for (int i = 0; i < mba->qty; ++i)
	{
		mblock_t *blk = mba->get_mblock(i);

		// FYI, don't screw with blocks that have calls at the end of them.
		// You'll get an INTERR. Also, if this block has more than one
		// successor, then it couldn't possibly be a transfer to a goto.
		if (is_call_block(blk) || blk->nsucc() != 1)
			continue;

		// Get the last instruction on the block
		minsn_t *mgoto = blk->tail;
		if (mgoto == NULL)
			continue;

		int iOriginalGotoTarget;
		// Now, look up the block number of the destination.
		bool bWasGoto = true;

		// If the last instruction was a goto, get the information from there.
		if (mgoto->opcode == m_goto)
			iOriginalGotoTarget = mgoto->l.b;

		// Otherwise, take the number of the only successor block.
		else
		{
			iOriginalGotoTarget = blk->succ(0);
			bWasGoto = false;
		}

		// Now, we determine if the target was a single-goto block.
		int iGotoTarget = iOriginalGotoTarget;
		bool bShouldReplace = false;
		intvec_t visited;

		// Keep looping while we still find goto-to-gotos.
		while (true)
		{
			// Keep track of the blocks we've seen so far, so we don't end up
			// in an infinite loop if the goto blocks form a cycle in the
			// graph.
			if (!visited.add_unique(iGotoTarget))
			{
				bShouldReplace = false;
				break;
			}
			// Once we find the first non-single-goto block, stop.
			if (forwarderInfo[iGotoTarget] == GOTO_NOT_SINGLE)
				break;

			// If we find at least one single goto at the destination, then
			// indicate that we should replace. Keep looping, though, to find
			// the ultimate destination.
			bShouldReplace = true;

			// Now check: did the single-goto block also target a single-goto
			// block?
			iGotoTarget = forwarderInfo[iGotoTarget];
		}

		// If the target wasn't a single-goto block, or there was an infinite
		// loop in the graph, don't touch this block.
		if (!bShouldReplace)
			continue;

		// Otherwise, update the destination with the final target.

		// If the block had a goto, overwrite its block destination.
		if (bWasGoto)
			mgoto->l.b = iGotoTarget;

		// Otherwise, add a goto onto the block. You might think you could skip
		// this step and just change the successor information, but you'll get
		// an INTERR if you do.
		else
			AppendGotoOntoNonEmptyBlock(blk, iGotoTarget);

		// Change the successor/predecessor information for this block and its
		// old and new target.
		ChangeSingleTarget(blk, iOriginalGotoTarget, iGotoTarget);

		// Counter of the number of blocks changed.
		++iRetVal;
	}

	// Don't need the forwarder information anymore.
	delete[] forwarderInfo;

	// Return the number of blocks whose destinations were changed
	return iRetVal;
}

// For a block that ends in a conditional jump, extract the integer block
// numbers for the "taken" and "not taken" cases.
bool ExtractJccParts(mblock_t *pred1, mblock_t *&endsWithJcc, int &jccDest, int &jccFallthrough)
{
	if (is_mcode_jcond(pred1->tail->opcode))
	{
		if (pred1->tail->d.t != mop_b)
		{
			debugmsg("[I] SplitMblocksByJccEnding: block %d was jcc, but destination was %s, not mop_b\n", mopt_t_to_string(pred1->tail->d.t));
			return false;
		}
		endsWithJcc = pred1;
		jccDest = pred1->tail->d.b;

		// The fallthrough location is the block that's not directly targeted
		// by the jcc instruction. Determine that by looking at the successors.
		// I guess technically Hex-Rays enforces that it must be the
		// sequentially-next-numbered block, but oh well.
		jccFallthrough = pred1->succ(0) == jccDest ? pred1->succ(1) : pred1->succ(0);
		return true;
	}
	return false;
}

// For a block with two predecessors, figure out if one of them ends in a jcc
// instruction. Return pointers to the block that ends in a jcc and the one
// that doesn't. Also return the integer numbers of those blocks.
bool SplitMblocksByJccEnding(mblock_t *pred1, mblock_t *pred2, mblock_t *&endsWithJcc, mblock_t *&nonJcc, int &jccDest, int &jccFallthrough)
{
	endsWithJcc = NULL;
	nonJcc = NULL;
	if (pred1->tail == NULL || pred2->tail == NULL)
		return false;

	// Check if the first block ends with jcc. Make sure the second one
	// doesn't also.
	if (ExtractJccParts(pred1, endsWithJcc, jccDest, jccFallthrough))
	{
		if (is_mcode_jcond(pred2->tail->opcode))
			return false;

		nonJcc = pred2;
	}
	// Otherwise, check if the second block ends with jcc. Make sure the first
	// one doesn't also.
	else
	{
		if (!ExtractJccParts(pred2, endsWithJcc, jccDest, jccFallthrough))
			return false;
		nonJcc = pred1;
	}
	return true;
}

// Plan to add an edge
void DeferredGraphModifier::Add(int src, int dest)
{
        edgeinfo_t &ei = edges.push_back();
        ei.src = src;
        ei.dst1 = -1;
        ei.dst2 = dest;
}

// Plan to replace an edge from src->oldDest to src->newDest
void DeferredGraphModifier::Replace(int src, int oldDest, int newDest)
{
        for ( const auto &ei: edges )
          if ( ei.src == src && ei.dst1 == oldDest )
            oldDest = ei.dst2; // update block to be deleted
        edgeinfo_t &ei = edges.push_back();
        ei.src = src;
        ei.dst1 = oldDest;
        ei.dst2 = newDest;
}

// Apply the planned changes to the graph
int DeferredGraphModifier::Apply(mbl_array_t *mba)
{
	// Iterate through the edges slated for removal or addition
	for (const auto &re: edges)
	{
		mblock_t *mSrc = mba->get_mblock(re.src);
                if ( re.dst1 != -1 )
                {
		  mblock_t *mDst1 = mba->get_mblock(re.dst1);
		  mSrc->succset.del(mDst1->serial);
		  mDst1->predset.del(mSrc->serial);
                }
		mblock_t *mDst2 = mba->get_mblock(re.dst2);
		mSrc->succset.add(mDst2->serial);
		mDst2->predset.add(mSrc->serial);
		debugmsg("[I] Replaced edge (%d->%d) by (%d->%d)\n", re.src, re.dst1, re.src, re.dst2);
	}

	return edges.size();
}

// Either change the destination of an existing goto, or add a new goto onto
// the end of the block to the destination. Also, plan to modify the graph
// structure later to reflect these changes.
bool DeferredGraphModifier::ChangeGoto(mblock_t *blk, int iOld, int iNew)
{
	// can not change a block that ends with a conditional jump
	QASSERT(99000, blk->tail == NULL || !is_mcode_jcond(blk->tail->opcode));

	bool bChanged = true;

	// If the last instruction isn't a goto, add a new one
	if (blk->tail->opcode != m_goto)
		AppendGotoOntoNonEmptyBlock(blk, iNew);

	// Otherwise, if it is a goto...
	else
	{
		// Be sure we're actually *changing* the destination to a different
		// location
		int prev = blk->tail->l.b;
		if (prev == iNew)
			bChanged = false;

		// And if so, do it
		else
			blk->tail->l.b = iNew;
	}

	// If we did change the destination, plan to update the graph later
	if (bChanged)
		Replace(blk->serial, iOld, iNew);

	return bChanged;
}

// Delete all instructions on a block, and remove its outgoing edges. Blocks
// will be deleted if we have removed edges in the graph such that the block
// is no longer reachable from block #0.
void DeleteBlock(mblock_t *mb)
{
	mbl_array_t *mba = mb->mba;

	// Delete this block from the predecessor set of the successors
	for (int j = 0; j < mb->nsucc(); ++j)
		mba->get_mblock(mb->succ(j))->predset.del(mb->serial);

	// Delete all successor edges
	while (mb->nsucc() != 0)
		mb->succset.del(mb->succ(0));

	// Delete the instructions on the block
	minsn_t *pCurr = mb->head, *pNext = NULL;
	while (pCurr != NULL)
	{
		pNext = pCurr->next;
		delete pCurr;
		pCurr = pNext;
	}

	// Mark that the block now has no instructions.
	mb->head = NULL;
	mb->tail = NULL;
}

