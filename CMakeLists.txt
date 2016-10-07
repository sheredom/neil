# This is free and unencumbered software released into the public domain.
#
# Anyone is free to copy, modify, publish, use, compile, sell, or
# distribute this software, either in source code form or as a compiled
# binary, for any purpose, commercial or non-commercial, and by any
# means.
#
# In jurisdictions that recognize copyright laws, the author or authors
# of this software dedicate any and all copyright interest in the
# software to the public domain. We make this dedication for the benefit
# of the public at large and to the detriment of our heirs and
# successors. We intend this dedication to be an overt act of
# relinquishment in perpetuity of all present and future rights to this
# software under copyright law.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
# IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
# OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
# ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.
#
# For more information, please refer to <http://unlicense.org/>

project(neil)
cmake_minimum_required(VERSION 3.4.3)

add_subdirectory(external/llvm)

add_executable(neilc
  ${CMAKE_CURRENT_SOURCE_DIR}/external/mpc/mpc.h
  ${CMAKE_CURRENT_SOURCE_DIR}/external/mpc/mpc.c
  ${CMAKE_CURRENT_SOURCE_DIR}/neilc.cpp
)

target_include_directories(neilc PRIVATE
  ${CMAKE_CURRENT_BINARY_DIR}/external/llvm/include
  ${CMAKE_CURRENT_SOURCE_DIR}/external/llvm/include
  ${CMAKE_CURRENT_SOURCE_DIR}/external/mpc/
)

target_link_libraries(neilc PRIVATE LLVMCore)

target_compile_features(neilc PRIVATE cxx_range_for)
