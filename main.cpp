/*
*      Hex-Rays Decompiler project
*      Copyright (c) 2007-2018 by Hex-Rays, support@hex-rays.com
*      ALL RIGHTS RESERVED.
*
*      Sample plugin for Hex-Rays Decompiler.
*      It generates microcode for selection and dumps it to the output window.
*/

#include <set>
#define USE_DANGEROUS_FUNCTIONS
#include <hexrays.hpp>
#include "HexRaysUtil.hpp"
#include "MicrocodeExplorer.hpp"
#include "PatternDeobfuscate.hpp"
#include "AllocaFixer.hpp"
#include "Unflattener.hpp"
#include "Config.hpp"

// Hex-Rays API pointer
hexdsp_t *hexdsp = NULL;

ObfCompilerOptimizer hook;
CFUnflattener cfu;

extern std::set<ea_t> g_BlackList;

//--------------------------------------------------------------------------
static ssize_t idaapi unflatten_callback(void *, hexrays_event_t event, va_list va)
{
	if (event == hxe_prealloc)
	//if (event == hxe_prealloc && !cfu.bStop)
	{
		mbl_array_t *mba = va_arg(va, mbl_array_t *);
		// call optblock_t callback
		cfu.bLastChance = true;
		int iChanged = cfu.func(mba->blocks);
		cfu.bLastChance = false;
		if (iChanged > 0)
			return 1; // if modified microcode
		//else
			//cfu.bStop = true;
	}
	return 0;
}

//--------------------------------------------------------------------------
int idaapi init(void)
{
	if (!init_hexrays_plugin())
	{
		msg("no decompiler");
		return PLUGIN_SKIP; // no decompiler
	}
	const char *hxver = get_hexrays_version();
	msg("Hex-rays version %s has been detected, %s ready to use\n", hxver, PLUGIN.wanted_name);

	// Install our block and instruction optimization classes.
#if DO_OPTIMIZATION
	install_optinsn_handler(&hook);
	install_optblock_handler(&cfu);
	#if USE_HEXRAYS_CALLBACK
		install_hexrays_callback(unflatten_callback, NULL);
	#endif
#endif
	return PLUGIN_KEEP;
}

//--------------------------------------------------------------------------
void idaapi term(void)
{
	if (hexdsp != NULL)
	{

		// Uninstall our block and instruction optimization classes.
#if DO_OPTIMIZATION
		remove_optinsn_handler(&hook);
		remove_optblock_handler(&cfu);
		#if USE_HEXRAYS_CALLBACK
			remove_hexrays_callback(unflatten_callback, NULL);
		#endif

		// I couldn't figure out why, but my plugin would segfault if it tried
		// to free mop_t pointers that it had allocated. Maybe hexdsp had been
		// set to NULL at that point, so the calls to delete crashed? Anyway,
		// cleaning up before we unload solved the issues.
		cfu.Clear(true);
#endif
		term_hexrays_plugin();
	}
}

//--------------------------------------------------------------------------
bool idaapi run(size_t arg)
{
	if (arg == 0xbeef)
	{
		PLUGIN.flags |= PLUGIN_UNL;
		return true;
	}
	if (arg == 0xdead)
	{
		func_t *fn = get_func(get_screen_ea());
		g_BlackList.insert(fn->start_ea);
		return true;
	}
	if (arg == 0xf001)
	{
		func_t *fn = get_func(get_screen_ea());
		g_BlackList.erase(fn->start_ea);
		return true;
	}
	if (arg == 2)
	{
		FixCallsToAllocaProbe();
		return true;
	}
	if (arg == 3)
	{
		ShowMicrocodeExplorer();
		return true;
	}

	return true;
}

//--------------------------------------------------------------------------
static const char comment[] = "Show microcode";


//--------------------------------------------------------------------------
//
//      PLUGIN DESCRIPTION BLOCK
//
//--------------------------------------------------------------------------
plugin_t PLUGIN =
{
	IDP_INTERFACE_VERSION,
	0,                    // plugin flags
	init,                 // initialize
	term,                 // terminate. this pointer may be NULL.
	run,                  // invoke plugin
	comment,              // long comment about the plugin
						  // it could appear in the status line
						  // or as a hint
	"",                   // multiline help about the plugin
	"Microcode explorer (HexRaysDeob)", // the preferred short name of the plugin
	""                    // the preferred hotkey to run the plugin
};
