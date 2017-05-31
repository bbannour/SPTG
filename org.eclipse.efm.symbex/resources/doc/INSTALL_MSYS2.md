# MSYS2 Compiler Environment : installation

## Core System installation
* Go to [http://msys2.github.io](http://msys2.github.io/)
* Download and run the installer **msys2-x86_64-20160921.exe**
* When prompted to enter **Installation Folder**, use default choice **C:\msys64**
* Tick **Run MSYS2 now**, this will open a shell
* Update the package database and pacman with ``pacman -Sy pacman``
* If needed, close MSYS2, run it again from Start menu. Update the rest with: Update the package database and core system packages with:  ``pacman -Syu``
* Again, if needed, close MSYS2, run it again from Start menu. Update the rest with: ``pacman -Su``

Pinning to Taskbar: shortcut command list 
1. C:\msys64\msys2_shell.cmd -mingw64
2. C:\msys64\usr\bin\mintty.exe -i /msys2.ico /usr/bin/bash --login



## Pacman, the package manager
The documentation [wiki page](https://wiki.archlinux.org/index.php/pacman)

### Querying package databases
* Help on queries on the sync database **-S**
* Help on queries on installed packages **-Q**

```
pacman -S --help
pacman -Q --help
```

* Search for packages in the database / in already installed packages

```

pacman -Ss string1 string2

pacman -Qs string1 string2

```


* To display installed file list a given package

```
pacman -Slq package_name

pacman -Qlq package_name
```

* To display extensive information about a given package

```
pacman -Si package_name

pacman -Qi package_name
```

### Installing packages
* Installing specific packages

```
pacman -S package_name1 package_name2
```

### Removing packages
* Removing packages, leaving all of its dependencies installed

```
pacman -R package_name
```

* Removing packages and its dependencies which are not required by any other installed package

```
pacman -Rs package_name
```

### Updating packages
* Comparing versions before updating, to see old and new versions of available packages

```
pacman -Syu
```


## Main Components installation
### Utilities used to store, backup, and transport files

```
pacman -S tar
```

### Git : The distributed version control system

```
pacman -S git
```

### Binutils : A set of programs to assemble and manipulate binary and object files

```
pacman -S binutils
``` 

# Utils for compilation

### GNU autotools : tools to automate parts of the compilation process
```
pacman -S autoconf

pacman -S automake

pacman -S libtool

pacman -S make
```

### CMake : a tool to build across several platforms
*  **CMake**  (compulsory)

```
pacman -S mingw-w64-x86_64-cmake
```
*  **Qt5 Framework**  (optional big package only needed for cmake-gui)
```
pacman -S mingw-w64-x86_64-qt5
```

### Gcc : The GNU Compiler Collection - C and C++ frontends
*  **Gcc** for **MinGW w64-x86_64** environment (compulsory)

```
pacman -S mingw-w64-x86_64-gcc
```

*  **GNU Debugger** (optional)

```
pacman -S mingw-w64-x86_64-gdb
```

### Additional developer libraries
* **Boost**, the Free peer-reviewed portable C++ source libraries (compulsory)

```
pacman -S mingw-w64-x86_64-boost
```

* **GMP**,  A free library for arbitrary precision arithmetic (optional)

```
pacman -S mingw-w64-x86_64-gmp
```

*  **GNU readline** library (optional)

```
pacman -S libreadline-devel
```

### Python : the version 3 of the high-level scripting language 
Required by
* Z3 prover compilation
Optional otherwise
```
pacman -S mingw-w64-x86_64-python3
```
