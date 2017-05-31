echo cmake -G \"Unix Makefiles\" ./build

# Setting build directory step

rm -d -r -f build

mkdir build ; cd build

# Cmake Configuration step

cmake -G "Unix Makefiles" ../org.eclipse.efm.symbex/

# Compilation step

make -j28

