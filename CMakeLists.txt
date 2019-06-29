cmake_minimum_required(VERSION 3.2 FATAL_ERROR)

# Included file

set(PLUGIN_NAME              HexRaysDeob)
file(GLOB PLUGIN_SOURCES *.hpp *.cpp)

include($ENV{IDASDK}/ida-cmake/plugins.cmake)

set_source_files_properties(${DISABLED_SOURCES} PROPERTIES LANGUAGE "")