FROM ysli/quickchick
RUN . ~/.profile \
 && opam install -y menhir \
 && git clone -b dsss https://github.com/vellvm/vellvm.git \
 && curl http://plv.mpi-sws.org/paco/paco-1.2.8.zip -o paco.zip \
 && unzip paco -d vellvm/lib \
 && rm paco.zip \
 && make -C vellvm/lib/paco/src \
 && make -C vellvm/src -j
