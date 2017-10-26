FROM ocaml/opam:ubuntu-16.04_ocaml-4.03.0

# must update repos before installing
RUN sudo add-apt-repository ppa:openjdk-r/ppa && \
    sudo apt-get update

# install ocam and other deps
# javalib/sawja Deps: zlib1g-dev
# ocamlfind Deps: m4
# project Deps: openjdk-7-jdk
RUN sudo apt-get install -y \
    m4 \
    zlib1g-dev \
    openjdk-7-jdk

# init && setup opam and install ocam libraries
RUN opam init -y && opam install -y \
    ocamlgraph \
    ocamlbuild \
    oasis \
    core \
    ppx_hash \
    ppx_compare \
    ppx_sexp_conv \
    ppx_deriving \
    sawja

ADD . /home/opam/build

RUN sudo chown -R $(id -u):$(id -g) /home/opam && \
    cd /home/opam/build && \
    eval $(opam config env) && \
    make
