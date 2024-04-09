# Install script for directory: /Users/garychen/csmith/runtime

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/Users/garychen/csmith")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/objdump")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/lib/libcsmith.a")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/lib" TYPE STATIC_LIBRARY FILES "/Users/garychen/csmith/runtime/libcsmith.a")
  if(EXISTS "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.a" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.a")
    execute_process(COMMAND "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/ranlib" "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.a")
  endif()
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/lib/libcsmith.0.0.0.dylib;/Users/garychen/csmith/lib/libcsmith.0.dylib")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/lib" TYPE SHARED_LIBRARY FILES
    "/Users/garychen/csmith/runtime/libcsmith.0.0.0.dylib"
    "/Users/garychen/csmith/runtime/libcsmith.0.dylib"
    )
  foreach(file
      "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.0.0.0.dylib"
      "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.0.dylib"
      )
    if(EXISTS "${file}" AND
       NOT IS_SYMLINK "${file}")
      if(CMAKE_INSTALL_DO_STRIP)
        execute_process(COMMAND "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/strip" -x "${file}")
      endif()
    endif()
  endforeach()
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/lib/libcsmith.dylib")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/lib" TYPE SHARED_LIBRARY FILES "/Users/garychen/csmith/runtime/libcsmith.dylib")
  if(EXISTS "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.dylib" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.dylib")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/strip" -x "$ENV{DESTDIR}/Users/garychen/csmith/lib/libcsmith.dylib")
    endif()
  endif()
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/include/csmith.h;/Users/garychen/csmith/include/csmith_minimal.h;/Users/garychen/csmith/include/custom_limits.h;/Users/garychen/csmith/include/custom_stdint_x86.h;/Users/garychen/csmith/include/platform_avr.h;/Users/garychen/csmith/include/platform_generic.h;/Users/garychen/csmith/include/platform_msp430.h;/Users/garychen/csmith/include/random_inc.h;/Users/garychen/csmith/include/safe_abbrev.h;/Users/garychen/csmith/include/stdint_avr.h;/Users/garychen/csmith/include/stdint_ia32.h;/Users/garychen/csmith/include/stdint_ia64.h;/Users/garychen/csmith/include/stdint_msp430.h;/Users/garychen/csmith/include/volatile_runtime.c;/Users/garychen/csmith/include/volatile_runtime.h")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/include" TYPE FILE FILES
    "/Users/garychen/csmith/runtime/csmith.h"
    "/Users/garychen/csmith/runtime/csmith_minimal.h"
    "/Users/garychen/csmith/runtime/custom_limits.h"
    "/Users/garychen/csmith/runtime/custom_stdint_x86.h"
    "/Users/garychen/csmith/runtime/platform_avr.h"
    "/Users/garychen/csmith/runtime/platform_generic.h"
    "/Users/garychen/csmith/runtime/platform_msp430.h"
    "/Users/garychen/csmith/runtime/random_inc.h"
    "/Users/garychen/csmith/runtime/safe_abbrev.h"
    "/Users/garychen/csmith/runtime/stdint_avr.h"
    "/Users/garychen/csmith/runtime/stdint_ia32.h"
    "/Users/garychen/csmith/runtime/stdint_ia64.h"
    "/Users/garychen/csmith/runtime/stdint_msp430.h"
    "/Users/garychen/csmith/runtime/volatile_runtime.c"
    "/Users/garychen/csmith/runtime/volatile_runtime.h"
    )
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/include/safe_math.h")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/include" TYPE FILE FILES "/Users/garychen/csmith/runtime/safe_math.h")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/include/safe_math_macros.h")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/include" TYPE FILE FILES "/Users/garychen/csmith/runtime/safe_math_macros.h")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/include/safe_math_macros_notmp.h")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/include" TYPE FILE FILES "/Users/garychen/csmith/runtime/safe_math_macros_notmp.h")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  list(APPEND CMAKE_ABSOLUTE_DESTINATION_FILES
   "/Users/garychen/csmith/include/windows/stdint.h")
  if(CMAKE_WARN_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(WARNING "ABSOLUTE path INSTALL DESTINATION : ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  if(CMAKE_ERROR_ON_ABSOLUTE_INSTALL_DESTINATION)
    message(FATAL_ERROR "ABSOLUTE path INSTALL DESTINATION forbidden (by caller): ${CMAKE_ABSOLUTE_DESTINATION_FILES}")
  endif()
  file(INSTALL DESTINATION "/Users/garychen/csmith/include/windows" TYPE FILE FILES "/Users/garychen/csmith/runtime/windows/stdint.h")
endif()

