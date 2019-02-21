#pragma once
#include <hexrays.hpp>
#include "Config.hpp"

struct JZInfo
{
	JZInfo() : op(NULL) {};

	mop_t *op;
	int nSeen;
	std::vector<mop_t *> nums;

	bool ShouldBlacklist();
};

struct CFFlattenInfo
{
	mop_t *opAssigned, *opCompared, *opSubCompared;
	uint64 uFirst;
	int iFirst, iDispatch;
	std::map<uint64, int> m_KeyToBlock;
	std::map<int, uint64> m_BlockToKey;
	std::map<uint64, ea_t> m_KeyToEA;
	std::map<ea_t, uint64> m_EAToKey;
	ea_t m_WhichFunc;
	array_of_bitsets *m_DomInfo;
	int *m_DominatedClusters;
	bool bTrackingFirstBlocks;
	bool bOpAndAssign;
	int64 OpAndImm;

	int FindBlockByKey(uint64 key);
	int FindBlockByKeyFromEA(uint64 key, mbl_array_t *mba);
	int TranslateEA2Block(ea_t ea, mbl_array_t *mba);
	void Clear(bool bFree, mba_maturity_t maturity = MMAT_ZERO)
	{
		if (bFree && opAssigned != NULL)
			delete opAssigned;
		opAssigned = NULL;

		if (bFree && opCompared != NULL)
			delete opCompared;
		opCompared = NULL;

		if (bFree && opSubCompared != NULL)
			delete opSubCompared;
		opSubCompared = NULL;

		iFirst = -1;
		iDispatch = -1;
		uFirst = 0LL;
		m_WhichFunc = BADADDR;
		if (bFree && m_DomInfo != NULL)
			delete m_DomInfo;
		m_DomInfo = NULL;

		if (bFree && m_DominatedClusters != NULL)
			delete m_DominatedClusters;
		m_DominatedClusters = NULL;

		bTrackingFirstBlocks = bOpAndAssign = false;
		OpAndImm = 0;

		m_KeyToBlock.clear();
		m_BlockToKey.clear();
		if (maturity <= MMAT_DEOB_MAP)
		{
			m_KeyToEA.clear();
			m_EAToKey.clear();
		}
	};
	CFFlattenInfo() { Clear(false); }
	~CFFlattenInfo() { Clear(true); }
	bool GetAssignedAndComparisonVariables(mblock_t *blk);
	//mblock_t * TranslateBlock(mbl_array_t * omba, mblock_t * mb);
};
