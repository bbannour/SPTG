# Linux Ubuntu Environment Installation

## Core System installation
This procedure has been tested under Ubuntu 14.04 LTS.

## APT, the package manager
APT is a set of core tools found inside Debian based operating systems. It provides utilities for the installation and removal of software packages and dependencies on a system.

### APT-GET, package management

#### Update repositories
Repositories are updated from the locations specified in /etc/apt/sources.list and /etc/apt/sources.list.d/. 
``sudo apt-get update``

#### Upgrade the whole OS distribution
``sudo apt-get upgrade``

#### Installing a package
``sudo apt-get install <package>``

#### Removing a package without removing its configurations files
``sudo apt-get remove <package>``

#### Removing a package including its configurations files
``sudo apt-get purge <package>``
or
``sudo apt-get remove --purge <package>``

### APT-CACHE, high level package query
APT cache files are located in /var/cache/apt/archives

#### List all available packages for the OS
``apt-cache pkgnames``

#### Look for packages matching a string pattern
``apt-cache search <string>``

#### Show comprehensive information about a package
``apt-cache show <package>``

### DPKG, low level package management

#### Show all files installed by a package
``dpkg -L <package>``

#### Show all packages containing a filename or filepath
``dpkg -S <filenameorpath>``

## Main Components Installation

#### CMake, a tool to build across several platforms
`sudo apt-get install cmake`  
`sudo apt-get install cmake-gui`  

#### Boost, the Free peer-reviewed portable C++ source libraries (compulsory)  
`sudo apt-get install libboost-all-dev` : Debian's default boost version (currently 1.54)

#### ANTLR2, a parser
`sudo apt-get install libantlr-dev`   

#### GMP, a free library for arbitrary precision arithmetic (optional)
`sudo apt-get install libgmp-dev`

#### Git, The distributed version control system
`sudo apt-get install git`




