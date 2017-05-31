msys64/symbex# MinGW Distro - nuwen.net

* **Web** [mingw-nuwen](https://nuwen.net/mingw.html)
* **Download & install**

```
Download: 'mingw-14.x.exe'
Unarchive it in the root directory: 'C:\'
```


# SEP: Open Source Solvers compilation & installation

* For Microsoft Windows platform, assume that the system **MSYS2 / MinGW64** is installed, see [INSTALL_MSYS2](INSTALL_MSYS2.md)

* Assume that you have these file system configuration

```
 git-repository-local-directory
 	|__ solvers
 	|__ install
```

* Go to ```git-repository-local-directory```

```sh
cd git-repository-local-directory
```


## ANTLR Tools, for C++ lexer or parser, version 2.7.7

* **Repository** [download](http://www.antlr2.org/download.html)
* **Web** [antlr2.org](http://www.antlr2.org/)
* **Get source code**

```sh
Just download it: http://www.antlr2.org/download/antlr-2.7.7.tar.gz
```
* **Go to** the local unarchive directory

```sh
cd antlr-2.7.7-directory
```

* **Patch** ```lib\cpp\antlr\CharScanner.hpp```

```cpp
+#include <string.h>
or
+#include <cstring>
```

* **Configuration**

```sh
./configure --host=x86_64-w64-mingw32 --build=x86_64-w64-mingw32 --prefix=/c/msys64/symbex --enable-cxx --disable-java --disable-python --disable-csharp  --enable-static=true --enable-shared=false --enable-64bit

--host=x86_64-w64-mingw32 --build=x86_64-w64-mingw32

#--host=i686-w64-mingw32 --build=i686-w64-mingw32
#--host=mingw-w64-x86_64 --build=mingw-w64-x86_64


./configure --host=x86_64-w64-mingw32 --build=x86_64-w64-mingw32 --prefix=/c/mingw/symbex --enable-cxx --disable-java --disable-python --disable-csharp  --enable-static=true --enable-shared=false --enable-64bit
```

## ANTLR Tools, for C++ lexer or parser, version 3.4

* **Repository** [download](http://www.antlr3.org/download/C/)
* **Web** [antlr3.org](http://www.antlr3.org/)
* **Get source code**

```sh
Just download it: http://www.antlr3.org/download/C/libantlr3c-3.4.tar.gz
```
* **Go to** the local unarchive directory

```sh
cd libantlr3c-3.4-directory
```

* **Configuration**

```sh
./configure --prefix=/c/msys64/symbex --enable-static=true --enable-shared=false --enable-64bit

./configure --prefix=/c/mingw/symbex --enable-static=true --enable-shared=false --enable-64bit
```

## ANTLR Tools, for C++ lexer or parser, version 4.6

* **Repository** [GitHub](https://github.com/antlr/antlr4)
* **Doc** [cpp-target](https://github.com/antlr/antlr4/blob/master/doc/cpp-target.md)
* **Get source code**

```sh
 git clone https://github.com/antlr/antlr4.git
```
* **Go to** the local clone directory

```sh
cd antlr4-directory
```

* **Configuration**

```sh
cd /runtime/Cpp
mkdir build && mkdir run && cd build
cmake .. -DANTLR_JAR_LOCATION=/c/msys64/symbex/source/antlr-4.6-complet.jar  -DCMAKE_BUILD_TYPE=Release -DCMAKE_MAKE_PROGRAM=make -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++ -DWITH_DEMO=True
```



## GMP, The GNU Multiple Precision Arithmetic Library, version 6.1.2

* **Repository** [download](https://gmplib.org/#DOWNLOAD)
* **Web** [gmplib.org](https://gmplib.org/)
* **Get source code**

```sh
Just download it: https://gmplib.org/download/gmp/gmp-6.1.2.tar.bz2
```
* **Go to** the local unarchive directory

```sh
cd gmp-6.1-directory
```

* **Configuration**

```sh
./configure --prefix=/c/msys64/symbex --enable-cxx  --disable-shared

./configure --prefix=/c/mingw/symbex --enable-cxx  --disable-shared
```


## CLN, Class Library for Numbers, version 1.3.4

* **Repository** [CLN](http://www.ginac.de/CLN/cln.git/)
* **Web** [CLN](http://www.ginac.de/CLN/)
* **Get source code**

```sh
 git clone git://www.ginac.de/cln.git
 autoreconf -iv
```
* **Go to** the local clone directory

```sh
cd cln-1.3-directory
```

* **Configuration**

```sh

./configure --host=x86_64-w64-mingw32 --build=x86_64-w64-mingw32 --prefix=/c/msys64/symbex --with-gmp=/c/msys64/symbex --enable-static  --disable-shared

./configure --host=x86_64-w64-mingw32 --build=x86_64-w64-mingw32 --prefix=/c/mingw/symbex --with-gmp=/c/mingw/symbex --enable-static  --disable-shared

```

## GiNaC is Not a CAS ()Computer Algebra System), version 1.7.1

* **Repository** [GiNaC](http://www.ginac.de/ginac.git/)
* **Web** [GiNaC](http://www.ginac.de/)
* **Get source code**

```sh
 git clone git://www.ginac.de/ginac.git
 autoreconf -i
```
* **Go to** the local clone directory

```sh
cd ginac-1.7-directory
```

* **Configuration**

```sh

export CLN_CFLAGS=-I/c/msys64/symbex/include

export CLN_LIBS=-L/c/msys64/symbex/lib


export LIBS="/c/msys64/symbex/lib/libcln.a /c/msys64/symbex/lib/libgmp.a -lreadline -lncurses"

./configure --prefix=/c/msys64/symbex --enable-static  --disable-shared


export LIBS="/c/mingw/symbex/lib/libcln.a /c/mingw/symbex/lib/libgmp.a -lreadline -lncurses"

./configure --prefix=/c/mingw/symbex --enable-static  --disable-shared

```




## Omega Library, for constraint manipulation
Omega Project Source Release, version 2.1

* **Repository** [GitHub](https://github.com/davewathaverford/the-omega-project)

* **Get source code**

```sh
 git clone https://github.com/davewathaverford/the-omega-project.git
```
* **Go to** the local clone directory

```sh
cd omega-directory
```

* **Configuration**
	+ Edit ```omega-directory/Makefile.config```
	+ Modify compiler flags ```COMPILER_CFLAGS``` and install location ```DESTDIR```

```makefile

# line 15: uncomment it i.e.
X11_LIBS = -lXm -lXt -lX11  -lICE -lSM

# line 18: comment it i.e.
#X11_LIBS = #-lICE -lSM

# near line 28
COMPILER_CFLAGS=-Wall -Wno-format -Wparentheses -DSIG_HANDLER_HAS_ONE_ARG=1 -DSHUT_UP_ABOUT_STATEMENT_WITH_NO_EFFECT_IN_DYNAMIC_ARRAY_CREATION -DDAVEW_THESIS_REDUCTIONS -DSTUDY_KILL_USE

# near line 83
DESTDIR=git-repository-local-directory/install
```

* **Patch** ```basic\include\basic\assert.h```

```cpp

15,17c15,17
< #ifdef WIN32
< # define _assert(ex)	((!(ex)) ? ((void)fprintf(stderr,"\n\nAssertion \"%s\" failed: file \"%s\", line %d\n", ex, __FILE__, __LINE__), Exit(-2), 0) : 1)
< #else
---
> //#ifdef WIN32
> //# define _assert(ex)	((!(ex)) ? ((void)fprintf(stderr,"\n\nAssertion \"%s\" failed: file \"%s\", line %d\n", ex, __FILE__, __LINE__), //Exit(-2), 0) : 1)
> //#else
20c20
< #endif
---
> //#endif

```

* **Patch** ```basic\include\basic\util.h```

```cpp

4,8c4,10
< #ifdef WIN32
< #define LONGLONG _int64
< #else
< #define LONGLONG long long
< #endif
---
> #include <stdint.h>
>
> //#ifdef WIN32
> #define LONGLONG int64_t
> //#else
> //#define LONGLONG long long
> //#endif
22,24c24,26
< #ifdef WIN32
< #    define MAXLONGLONG (0x7ffffffffffffff)
< #else
---
> //#ifdef WIN32
> //#    define MAXLONGLONG (0x7ffffffffffffff)
> //#else
26c28
< #endif
---
> //#endif

```

* **Patch** ```omega_lib/src/omega_core/oc_simple.c```

```cpp

1189
<		if (GEQs[e2].coef[0] > GEQs[e].coef[0] ||
<		    (GEQs[e2].coef[0] == GEQs[e].coef[0] && GEQs[e2].color))
---
>		if (GEQs[e2].coef[0] >= GEQs[e].coef[0] && GEQs[e2].color)

```

* **Patch** ```omega_lib/src/closure.c```

```cpp


```

* **Patch** ```omega_lib/src/pres_dnf.c```

```cpp

332
<     int recursive=0;
---
> //    int recursive=0;

982
<     bool empty_or=true;
---
> //    bool empty_or=true;

```


* **Compilation**
	+ Do

```sh
make depend

make libomega.a
```

* **installation**

	+ Do

```sh
make install
```

## CVC4, SMT Solver from New York University
This is CVC4 release version 1.4

* **Repository** [GitHub](https://github.com/CVC4/CVC4)

* **Get source code**

```sh
git clone https://github.com/CVC4/CVC4.git
```

* **Go to** the local clone directory

```sh
cd cvc4-directory

./autogen.sh
```

* **Patch** ```src\util\sexpr.h:line71```

```cpp

#ifdef CVC4_NEED_INT64_T_OVERLOADS
  SExpr(int64_t  value);
  SExpr(uint64_t value);
#endif /* CVC4_NEED_INT64_T_OVERLOADS */

```

* **Patch** ```src\util\sexpr.cpp:line127```

```cpp

#ifdef CVC4_NEED_INT64_T_OVERLOADS
SExpr::SExpr(int64_t value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(uint64_t value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}
#endif /* CVC4_NEED_INT64_T_OVERLOADS */

```


* **Configuration**
	+ Get & Compile the tool **antlr-3.4**

```sh

cd contrib/
./get-antlr-3.4
cd ..

cd contrib/ && ./get-antlr-3.4 && cd ..

```

   + Configure UNIX

```sh
export LIBS="-lgmp"

./configure --prefix=/home/lapitre_is148245/efm/symbex/contrib --with-antlr-dir=`pwd`/antlr-3.4 ANTLR=`pwd`/antlr-3.4/bin/antlr3  --enable-static=true --enable-shared=false --enable-static-binary --enable-proof --enable-optimized --bsd

--without-cln  --with-gmp 

--best need  --with-cln
```


   + Configure MSYS2

```sh
export LIBS="-lgmp"

export CFLAGS=-I/c/msys64/symbex/include
export CPPFLAGS=-I/c/msys64/symbex/include
export CXXFLAGS=-I/c/msys64/symbex/include
export LDFLAGS=-L/c/msys64/symbex/lib

./configure --prefix=/c/msys64/symbex --with-antlr-dir=`pwd`/antlr-3.4 ANTLR=`pwd`/antlr-3.4/bin/antlr3  --enable-static=true --enable-shared=false --enable-static-binary --enable-proof --enable-optimized --bsd

./configure --prefix=/c/msys64/symbex --with-antlr-dir=`pwd`/antlr-3.4 ANTLR=`pwd`/antlr-3.4/bin/antlr3  --enable-static=true --enable-shared=false --enable-static-binary --enable-proof --enable-optimized --without-cln --with-gmp --bsd

--with-boost=/c/msys64/mingw64/include/boost --with-boost-libdir=/c/msys64/mingw64/lib


export LIBS="-lgmp"

export CFLAGS=-I/c/mingw/symbex/include
export CPPFLAGS=-I/c/mingw/symbex/include
export CXXFLAGS=-I/c/mingw/symbex/include

./configure --prefix=/c/mingw/symbex --with-antlr-dir=`pwd`/antlr-3.4 ANTLR=`pwd`/antlr-3.4/bin/antlr3  --enable-static=true --enable-shared=false --enable-static-binary --enable-proof --enable-optimized --bsd

./configure --prefix=/c/mingw/symbex --with-antlr-dir=`pwd`/antlr-3.4 ANTLR=`pwd`/antlr-3.4/bin/antlr3  --enable-static=true --enable-shared=false --enable-static-binary --enable-proof --enable-optimized --without-cln  --with-gmp  --with-boost=/c/mingw/include/boost --with-boost-libdir=/c/mingw/lib --bsd


--best need  --with-cln
```

* **Compilation**

Check if the `Makefile` is correct i.e. if `buildirs = <builds/$arch/$buildid>` !

```sh
make -j4
```

* **installation**
```sh
make install
```


## Z3, Theorem Prover from Microsoft Research
This is Z3 release version 4.4.1

* **Repository** [GitHub](https://github.com/Z3Prover/z3)

* **Get source code**
```sh
 git clone https://github.com/Z3Prover/z3.git
```

* **Go to** the local clone directory
```sh
cd z3-directory
```

* **Configuration**
  + Using configure

```sh

export LDFLAGS="-L/c/msys64/symbex/lib"

export LIBS="/c/msys64/symbex/lib/libgmp.a"

export Z3_INSTALL_BIN_DIR=/c/msys64/symbex/bin
export Z3_INSTALL_LIB_DIR=/c/msys64/symbex/lib
export Z3_INSTALL_INCLUDE_DIR=/c/msys64/symbex/include

export LDFLAGS="-L/c/mingw/symbex/lib"

export LIBS="/c/mingw/symbex/lib/libgmp.a"

export Z3_INSTALL_BIN_DIR=/c/mingw/symbex/bin
export Z3_INSTALL_LIB_DIR=/c/mingw/symbex/lib
export Z3_INSTALL_INCLUDE_DIR=/c/mingw/symbex/include


./configure CXX=g++ CC=gcc AR=ar --staticlib --staticbin --optimize --noomp
CXX=g++ CC=gcc AR=ar ./configure --staticlib --staticbin --optimize --noomp --makefiles

CXX=g++ CC=gcc AR=ar python scripts/mk_make.py --staticlib --staticbin --optimize --noomp
python scripts/mk_make.py --staticlib --staticbin --optimize --noomp

```

  + Using cmake

```sh

cd z3-directory

git clean -nx src
git clean -fx src

python contrib/cmake/bootstrap.py create

./configure --staticlib --staticbin --optimize --noomp

#rm -rfd build
mkdir build && cd build

cmake -G "Unix Makefiles" ../

make -j4 # Replace 4 with an appropriate number

```


* **Compilation**
```sh
cd build
make -j4
```

* **installation**
```sh
make install
```
