echo cmake -G \"Unix Makefiles\" ./build

rm -rfd build

mkdir build ; cd build

cmake -G "Unix Makefiles" ../

make

#ctest -W -s 

