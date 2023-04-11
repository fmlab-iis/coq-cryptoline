#!/bin/bash

TOOLS_DIR=tools
KISSAT_VERSION=3.0.0
KISSAT_DIR=kissat-rel-${KISSAT_VERSION}
KISSAT_TAR_GZ=kissat-${KISSAT_VERSION}.tar.gz
KISSAT_URL=https://github.com/arminbiere/kissat/archive/refs/tags/rel-${KISSAT_VERSION}.tar.gz

sudo apt install -y curl build-essential binutils autoconf autogen libtool
mkdir -p ${TOOLS_DIR}
pushd ${TOOLS_DIR}
curl -L ${KISSAT_URL} -o ${KISSAT_TAR_GZ}
tar zxf ${KISSAT_TAR_GZ}
pushd ${KISSAT_DIR}
./configure
make
sudo install -m 755 build/kissat /usr/local/bin
popd
popd
