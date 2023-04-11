FROM ubuntu:22.04

# Install system packages.

RUN apt update && apt upgrade -y
RUN apt install -y build-essential ocaml ocaml-dune libzarith-ocaml-dev \
                   liblwt-ocaml-dev curl git bc nano cmake libreadline-dev \
                   gdb python3 sudo coq libcoq-mathcomp-ssreflect \
                   libcoq-mathcomp-algebra libgmp-dev binutils \
                   libboost-timer-dev

# Clone CoqCryptoLine.

RUN git clone --recursive https://github.com/fmlab-iis/coq-cryptoline.git \
	/home/coq-cryptoline

# Install external tools.

WORKDIR /home/coq-cryptoline
RUN ./scripts/install-mlton.sh \
	&& ./scripts/install-grat.sh \
	&& ./scripts/install-kissat.sh \
	&& ./scripts/install-singular.sh

# Compile CoqCryptoLine OCaml code.

WORKDIR /home/coq-cryptoline/src/ocaml
RUN dune build && dune install
