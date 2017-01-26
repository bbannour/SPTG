# EFM-SYMBEX : Build and Installation Instructions

## Overview
In order to build EFM-SYMBEX, you'll need :  
* [CMake](https://cmake.org/download/), 2.8 or higher
* [Boost](http://www.boost.org/users/download/), 1.53 or higher
* [GMP](https://gmplib.org/), 2.5.1.3
* [ANTLR2](http://www.antlr2.org), C bindings library, 2.7.7
* [ANTLR3](http://www.antlr3.org), C bindings library, 3.4
* [CVC4](http://cvc4.cs.nyu.edu), 1.3.1 or higher
* [Omega](https://github.com/davewathaverford/the-omega-project)
 
EFM-SYMBEX build is driven by CMake and tested with the following generators : 

* Unix Makefiles (native compilers)

## Prerequisites installation

### Binaries (almost) installation on Linux

Following instructions are given for debian-like distributions. You should adapt them to the package manager used by your distribution.   

#### CMake 
`sudo apt-get install cmake`  
`sudo apt-get install cmake-gui`  

#### Boost
`sudo apt-get install boost-1.53`  

#### GMP
`sudo apt-get install libgmp-dev`   

#### ANTLR2  
`sudo apt-get install libantlr-dev`   

#### ANTLR3
As no ANTLR 3.4 package seems available, it is necessary to compile a source distribution : 
Download [libantlr3c-3.4.tar.gz](http://www.antlr3.org/download/C/libantlr3c-3.4.tar.gz) then :  
 
`tar zxvf libantlr3c-3.4.tar.gz`  
`./configure --enable-static=true --enable-shared=false`, add `--enable-64bit` according to your system.  
`make`  
`make check`  
`sudo make install`  
    
Headers and library should be automatically installed in /usr/local. Use `.\configure --prefix=<yourpath>` to install in another location. In this case, you'll need to set `ANTLR3_ROOT` variable to this location for CMake to know about it.  

#### CVC4
Add the following lines in `/etc/apt/sources.list` :  

`deb http://cvc4.cs.nyu.edu/debian/ stable/`
`deb http://cvc4.cs.nyu.edu/debian unstable/`
`deb_src http://cvc4.cs.nyu.edu/debian unstable/`  

Then do :  

`sudo apt-get update`  
`sudo apt-get install cvc4 libcvc4-dev`  

#### Omega
No package being available for Omega, it is necessary to compile a source distribution. Clone the source repository :  

`git clone https://github.com/davewathaverford/the-omega-project.git`  

Then do : 

`make depends`  
`make libomega.a`  
`sudo make install`
  
Headers and library should be automatically installed in /usr/local. Use .\configure --prefix=/usr/local to install in another location. In this case, you'll need to set `OMEGA_ROOT` variable to this location for CMake to know about it. 

### Sources installation on Linux
**TO BE DONE**

### Sources installation on Windows/MinGW/MSYS2 
**WARNING : Currently under test**

#### CMake
Use the Windows installer found [here](https://cmake.org/download/)

#### MSYS2
Follow instructions of INSTALL_MSYS.md.

#### CVC4
Download the sources archive [cvc4-1.4.tar.gz](http://cvc4.cs.nyu.edu/builds/src/cvc4-1.4.tar.gz)

**TO BE CONTINUED**

## Standard Build 
Launch cmake (or cMake-gui), set the source directory and the desired build directory.
Choose a valid generator, select your compilers (native compilers are recommended), configure and generate.
If your prerequisites are installed in non-standard locations, you'll have to set `<PREREQUISITE>_ROOT` variable(s) in the CMake cache editor.  

Then build the project using the built-in commands of the generator :  
* With "Unix Makefiles", simply do `make` in the build directory.

A the end of the process, the symbex executable is built and can be checked using  `symbex -test `.

## Customize the Build (for developers)
To customize the build, you'll have to modify CMake Files. All CMake files are `CMakeLists.txt` or `*.cmake`.
Each project target (main executable and internal libraries) is associated with a `CMakeLists.txt` in which every thing specific to this target are defined. All things relative to the project as a whole (prerequisites, cmake detection module, ...) are stored stored in the cmake directory.

### Set compilation options
Options which hold for all target and whatever the platform are set in `DefineGeneric.cmake`
Options which hold for all target and are platform-specific are set in `<Platform>Specific.cmake`.
Options which hold for one target and whatever the platform are set in the `CMakeLists.txt` of this target.

### Modify link command line
Main target link is defined in `LinkMainTarget.cmake`

### Change prerequisites look-up / Add a nex prerequisite
Prerequisites are defined and searched for in `LookForMandatoryPrerequisites.cmake`.  
Here you can add a new prerequisite or change the way an existing prerequisite is search for.

### Change project structure without adding a new target
Simply add a new subdirectory(ies) into existing target(s) source hierarchy.

### Add a new target
To add a new `newtarget` to the project, you have to :  
1. Create the `newtarget` source hierarchy in `src/newtarget/`
1. Add a `CMakeLists.txt` into target root directory `newtarget/` (it is easy to adapt a `CMakeLists.txt` from other targets)
2. Add a new `add_subdirectory (newtarget)` in `DefineProjectStructure.cmake` to make CMake aware to the new sources
3. Complete `LinkMainTarget.cmake` by adding `newtarget` to the link line.











