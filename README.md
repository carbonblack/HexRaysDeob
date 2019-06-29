# HexRaysDeob for APT10 ANEL

This is a forked repository of HexRaysDeob for defeating APT10 ANEL code obfuscations.

This plugin supports IDA 7.3 only.

The tested hashes are:
- 3d2b3c9f50ed36bef90139e6dd250f140c373664984b97a97a5a70333387d18d (5.4.1 dropped payload)
- f333358850d641653ea2d6b58b921870125af1fe77268a6fdfeda3e7e0fb636d (5.5.0 rev1 loader DLL)

# Building

This project ships with:
- A Visual Studio solution file (you might want to edit it so it works in your environment).
- Makefiles from IDASDKs. Build with 'make' as you would build any IDA plugin from its SDK.
- A CMakefile compatible with [ida-cmake](https://github.com/0xeb/ida-cmake).