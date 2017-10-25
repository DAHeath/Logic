FROM ocaml/opam:ubuntu-16.04_ocaml-4.03.0

# must update repos before installing
RUN sudo apt-get update

# install ocam and other deps
# z3 Deps: python2
# javalib/sawja Deps: zlib1g-dev
# ocamlfind Deps: m4
# project Deps: openjdk-7-jdk
# scheme-format Deps: chicken-bin libchicken-dev
RUN sudo apt-get install -y \
    m4 \
    zlib1g-dev \
    python \
    default-jdk \
    chicken-bin \
    libchicken-dev

# set up scheme-format helper binary
RUN git clone 'https://github.com/russellw/scheme-format.git' && \
    cd scheme-format && \
    git checkout f03ebe75fd4e7a5f22f40744d37d0f67c20d3bd8 && \
    csc main.scm -o scheme-format && \
    sudo mv scheme-format /usr/bin/ && \
    cd .. && \
    rm -rf scheme-format

# init opam
RUN opam init -y

# build z3 with ml bindings
# stay on version 4.5.0 for now
COPY z3-patches /z3-patches
RUN git clone 'https://github.com/Z3Prover/z3.git' && \
    cd z3 && \
    git checkout tags/z3-4.5.0 && \
    eval $(opam config env) && \
    ls /z3-patches/*.patch && git apply --whitespace=nowarn /z3-patches/*.patch && \
    python scripts/mk_make.py --ml && \
    cd build && \
    make && \
    sudo make install && \
    cd ../.. && \
    rm -rf z3

# setup opam and install ocam libraries
RUN opam install -y \
    ocamlgraph \
    ocamlbuild \
    oasis \
    core \
    sawja

ADD . /home/opam/src

RUN sudo chown -R $(id -u):$(id -g) /home/opam && \
    cd /home/opam/src && \
    eval $(opam config env) && \
    make clean && \
    make
