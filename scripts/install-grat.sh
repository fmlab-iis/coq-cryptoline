#!/bin/bash

TOOLS_DIR=tools
GRATGEN_DIR=gratgen
GRATGEN_TGZ=gratgen.tgz
GRATGEN_URL=https://www21.in.tum.de/~lammich/grat/gratgen.tgz
GRATCHK_DIR=gratchk/code
GRATCHK_TGZ=gratchk.tgz
GRATCHK_URL=https://www21.in.tum.de/~lammich/grat/gratchk.tgz

sudo apt install -y curl build-essential cmake libboost-timer-dev
mkdir -p ${TOOLS_DIR}
pushd ${TOOLS_DIR}
curl -L ${GRATGEN_URL} -o ${GRATGEN_TGZ}
curl -L ${GRATCHK_URL} -o ${GRATCHK_TGZ}
tar zxf ${GRATGEN_TGZ}
tar zxf ${GRATCHK_TGZ}
pushd ${GRATGEN_DIR}
cmake .
make
sudo install -m 755 gratgen /usr/local/bin
popd
pushd ${GRATCHK_DIR}
make
sudo install -m 755 gratchk /usr/local/bin
popd
popd
