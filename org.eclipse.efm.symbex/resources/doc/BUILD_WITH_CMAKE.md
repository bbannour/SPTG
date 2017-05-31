# Symbex Build with CMake

## Environment installation
Symbex can be build with CMake on Linux Ubuntu or Windows MSYS2 systems
Follow steps described in `INSTALL_MSYS2.md ` or  `INSTALL_LINUX.md ` to install the required environment.

## CMake Fundamentals
CMake is an open-source, cross-platform family of tools designed to build, test and package software. CMake is used to control the software compilation process using simple platform and compiler independent configuration files, and generate native makefiles and workspaces that can be used in the compiler environment of your choice. 

CMake holds the build rules in configuration files (``src/CMakeLists.txt``, ``src/*/CMakeLists.txt`` and ``src/cmake/*.cmake``) written in a dedicated [platform independent language](https://cmake.org/cmake/help/v3.6/manual/cmake-language.7.html).

Basically, [building with CMake](https://cmake.org/cmake/help/v3.6/manual/cmake-buildsystem.7.html) follows this procedure : 
1. The user chooses a [Toolchain](https://cmake.org/cmake/help/v3.6/manual/cmake-toolchains.7.html) (a set of compiler, linker and associated libraries) and a [Generator](https://cmake.org/cmake/help/v3.6/manual/cmake-generators.7.html) (a platform dependent build system such as Make, Visual Studio, etc.). Of course, these must be available on the current platform.
2. Configuration. CMake analyses the current platform, toolchain and generator and put the relevant information in a cache file (CMakeCache.txt).
3. Generation. CMake creates all the files needed by the chosen generator.
4. Build. The generator executes the build without knowing anything about CMake.

If one or several sources file are modified, it is only required to redo the build step. If compile options or prerequisites are modified, the whole procedure must be done again from the beginning.

CMake can launched through a [GUI](https://cmake.org/cmake/help/v3.6/manual/cmake-gui.1.html) or a [command line](https://cmake.org/cmake/help/v3.6/manual/cmake.1.html).

## Standard Build Procedure

### Build on Windows MSYS2

#### Bypass of a CVC4 configure anomaly 
After boost is installed, copy the boost default installation to a directory where CVC4 configure will be able to find it :  
``cp -R /mingw64 /mingw642``

#### Build Procedure

1. Open a MSYS2-MINGW64 shell console. Make sure MINGW64 appears in the prompt.
2. Clone the Symbex sources repository using Eclipse Git or the command line ``git clone ssh://gitolite@132.166.135.212/diversity/org.eclipse.efm-symbex.git``. Make sure your SSH keys exists and are properly declared to Git.
3. Launch ``cmake-gui &`` and fill the two top fields with the path to the workspace sources directory (it should be ``src``) and the directory where you want to build (it is better to choose one outside the workspace). 
4. Press _Configure_. In the opening dialog choose the _MSYS Makefile_ generator. Don't change the default checked option _Use Default Native Compiler_ unless you know what you do. Press _Finish_ to launch the configure step. CMake logs what it is doing in the bottom message console. Pay attention to messages in red if any. During the very first build, some prerequisites are not found and CMake says it will build them later. At the end of the configure step, the cache console shows the resulting CMake variables and theirs values. (this is nothing more than a pretty display of the cache file). 
5. Press _Generate_ and wait for the message _Generating done_ to appear. Makefiles have been created in the build directory.
6. In the shell console, go to the build directory and launch the build with ``make``. On multicore platform you can launch parallel build with ``make -jX`` where X is slightly inferior to the number of cores. The current platform core number is displayed in the CMake message console. Build verbosity can be increased with ``make VERBOSE=1``. If it is the very first build, CMake will try to download, build and install the missing prerequisites (longer build).
7. A the end of the process, the ``symbex.exe`` executable is built and can be checked using ``./symbex -test``.

### Build on Linux Ubuntu

#### Build Procedure
1. Open a shell console. 

Follow steps 2 to 7 of Build on Windows MSYS2 procedure.
During step 4, choose the _Unix Makefiles_ generator
During step 6, if it is the very first build, Cmake will install the missing prerequisites, but will not have access to the default folders. Either try ``sudo make`` or install in other folders. It is possible to configure installation in other folders in SpecificOptions-LinuxNAtive.cmake

## Known Problems

* **Problem : Configure step failed at the basic compilation check made by CMake**  
Usually this problem arises when cache is deleted. Solution : Just kill cmake-gui and relaunch.


## Changing Build Options

* **Options that affect the whole project on every platform**
Edit ``GenericOptions.cmake`` and modify ``add_definitions()`` and ``add_options()`` commands according to your wish. Pay attention to only put platform independent options here.  Exemple : ``-g``, ``-O3``, ``-D_AVM_BUILTIN_NUMERIC_GMP_  ``

* **Options that affect the whole project on a specific platform**
Edit ``SpecificOptions-<platform>.cmake`` and modify ``add_definitions()`` and ``add_options()`` commands according to your wish.  
Exemple : ``-D__AVM_MINGW__``

* **Options that affect a specific internal library on every platform**
Edit the ``CMakeLists.txt`` file of this library and modify (or add) the ``add_definitions()`` and ``add_options()`` commands according to your wish.  

**Note : No mechanism is provided to set an option that is specific to only one internal library and only one platform.**  


## Advanced CMake (for Developers)
* **How to add a new source file ?**    
CMake will automatically detect the file as long as it is located in the directory hierarchy of an existing internal library and have a known suffix (``.h, .cpp, .c``). 

* **How to add a new sources directory without defining a new internal library**  
CMake will automatically detect the directory and files it contains as long as it is located in the directory hierarchy of an existing internal library.  

* **How to add a new internal library ?**  
1.  In ``src/``, create the top directory for mylib and any other required subdirectories. 
2. Edit ``DefineProject.cmake`` 
2.1 Add the required ``add_subdirectory (mylib)`` command.
2.2 Add mylib in the ``target_link_libraries (symbex ... mylib ...)`` command, at the right place for the link to succeed.
3. Copy the ``CMakeLists.txt`` file of an existing internal library into the top directory of mylib. Change all occurences of the existent library name with mylib. If needed, add or remove ``target_include_directories()`` commands to give access to any needed prerequisiste headers. Never write an explicit path here, instead use CMake variable (you can look at the CMakeLists.txt of other library to know about the right variable).  

* **How to add a new prerequisite X ?**
If the prerequisite is a binary package available on every Symbex supported platform, follow the following process :  
1. Create a new ``FindX.cmake module``, taking inspiration from an existing one. This module should return CMake variables containing path to the library(ies) and the include directory(ies).
2. Add the relevant code in ``LookForMandatoryPrereq.cmake`` for CMake to call the new ``FindX`` module.
3. Link to the new library(ies)  in the ``target_link_libraries(symbex ...)`` command in ``DefineProject.cmake``
4. For every internal library needing access to the new prerequisites headers, add a new ``target_include_directories`` command in the ``CMalkeLists.txt`` of this library. Always use CMake variables created by the FindX module (cf. step 1).



