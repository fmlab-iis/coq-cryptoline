#!/bin/bash

SWITCHES=${SWITCHES:- \
	ocaml4.12.1-coq8.13.2-ssr1.12.0 \
	ocaml4.13.1-coq8.14.1-ssr1.13.0 \
	ocaml4.13.1-coq8.15.0-ssr1.14.0 \
	ocaml4.14.0-coq8.15.2-ssr1.14.0 \
}

BUILD_DIR=${BUILD_DIR:-_build}

if [[ "$1" == "clean" ]]; then
  read -n 1 -p "Delete ${BUILD_DIR} (y/N)? " answer
  echo
  case ${answer:-N} in
    y|Y )
      rm -rf ${BUILD_DIR}
      ;;
    * )
      ;;
  esac
  exit
fi

CURRENT=`opam switch show`

for s in ${SWITCHES}; do
  echo "Building with ${s}"

  echo -n -e "  * Running 'opam switch'\t\t"
  opam switch ${s} &> /dev/null
  status=$?
  if [[ ${status} == 0 ]]; then
    echo "[DONE]"
  else
    echo "[FAIL]"
    continue
  fi
  eval $(opam env)

  echo -n -e "  * Copying files\t\t\t"
  mkdir -p ${BUILD_DIR}/${s}
  tar -c --exclude ${BUILD_DIR} --exclude "*.vo" --exclude "*.vok" --exclude "*.vos" --exclude "*.glob" * | tar -x --keep-newer-files -C ${BUILD_DIR}/${s} &> /dev/null
  echo "[DONE]"

  echo -n -e "  * Compiling Coq code\t\t\t"
  make -C ${BUILD_DIR}/${s} all >${BUILD_DIR}/${s}.log 2>&1
  status=$?
  if [[ $status == 0 ]]; then
    echo "[DONE]"
    echo -n -e "  * Compiling OCaml code\t\t"
    pushd ${BUILD_DIR}/${s}/src/ocaml &> /dev/null
    dune build &> /dev/null
    status=$?
    if [[ $status == 0 ]]; then
      echo "[DONE]"
    else
      echo "[FAIL]"
    fi
    popd &> /dev/null
  else
    echo "[FAIL]"
  fi
done

echo
echo "See the following log files for compilation details."
for s in ${SWITCHES}; do
  echo "  * ${BUILD_DIR}/${s}.log"
done

opam switch ${CURRENT} &> /dev/null
eval $(opam env)
