#!/bin/bash

TOOLS_DIR=tools
DIR=mlton-20210117-1.amd64-linux-glibc2.31
TGZ=mlton-20210117-1.amd64-linux-glibc2.31.tgz
URL=https://github.com/MLton/mlton/releases/download/on-20210117-release/mlton-20210117-1.amd64-linux-glibc2.31.tgz

sudo apt install -y curl make libgmp-dev
mkdir -p ${TOOLS_DIR}
pushd ${TOOLS_DIR}
curl -L ${URL} -o ${TGZ}
tar zxf ${TGZ}
pushd ${DIR}
sudo make install
popd
popd
