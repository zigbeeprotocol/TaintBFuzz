make -k clean
find src \( -name "*.cm*" -or -name "*.o" \) -delete -print
rm -fr config.status autom4te.cache/
autoconf -f
./configure
make clean
make depend
make -kj
