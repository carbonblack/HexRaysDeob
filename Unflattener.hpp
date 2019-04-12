#pragma once
#include <map>
#include <hexrays.hpp>
#include "CFFlattenInfo.hpp"
#include "DefUtil.hpp"
#include "TargetUtil.hpp"

struct CFUnflattener : public optblock_t
{
	CFFlattenInfo cfi;
	MovChain m_DeferredErasuresLocal;
	MovChain m_PerformedErasuresGlobal;
	bool bLastChance;
	bool bStop;

	void Clear(bool bFree)
	{
		cfi.Clear(bFree);
		m_DeferredErasuresLocal.clear();
		m_PerformedErasuresGlobal.clear();
		bLastChance = false;
		bStop = false;
	}

	CFUnflattener() { Clear(false); };
	~CFUnflattener() { Clear(true); }
	int idaapi func(mblock_t *blk);
	mblock_t *GetDominatedClusterHead(mbl_array_t *mba, int iDispPred, int &iClusterHead);
	int FindBlockTargetOrLastCopy(mblock_t *mb, mblock_t *mbClusterHead, mop_t *what, bool bAllowMultiSuccs, bool bRecursive);
	bool HandleTwoPreds(mblock_t *mb, mblock_t *mbClusterHead, mop_t *opCopy, mblock_t *&endsWithJcc, mblock_t *&nonJcc, int &actualGotoTarget, int &actualJccTarget);
	void CopyMinsnsToTailNoCond(mblock_t * src, mblock_t *& dst);
	void CopyMblock(mbl_array_t *mba, DeferredGraphModifier &dgm, mblock_t * src, mblock_t *& dst);
	void PostHandleTwoPredsNoCond(DeferredGraphModifier &dgm, mblock_t *&mb, mblock_t *&endsWithJcc, mblock_t *&nonJcc, int actualGotoTarget, int actualJccTarget);
	bool FindJccInFirstBlocks(mbl_array_t *mba, mop_t *opCopy, mblock_t *&endsWithJcc, mblock_t *&nonJcc, int &actualGotoTarget, int &actualJccTarget);
	void ProcessErasures(mbl_array_t *mba);
};