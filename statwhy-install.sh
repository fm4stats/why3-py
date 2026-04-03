#!/bin/sh

# This file installs the modified why3 and statwhy.

# Usage: ./statwhy-install.sh INSTALL_DIRECTORY OPAM_SWITCH
# The current directory must be the modified why3 source directory
#
# This installation modifies following files/directories:
#
# - INSTALL_DIRECTORY
# - $HOME/.opam/OPAM_SWITCH
# - $HOME/.profile                      # add opam configuration
# - $HOME/.why3.conf                    # why3 configuration
# - $HOME/.statwhy.conf                 # statwhy configuration
#
# Example:
#   This uses $HOME/statwhy and $HOME/.opam/statwhy.
#
#   % git clone --depth 1 --branch python-real http://host/path/why3-py.git
#   % cd why3-py
#   % ./statwhy-install.sh $HOME/statwhy statwhy
#   % eval $(opam env)

D="${1:?INSTALL_DIRECTORY not specified.  Specify it as the first argument}"
opam_switch="${2:?OPAM_SWITCH not specified.  Specify it as the second argument}"

case "$D" in
/*) ;;
*) echo "install-directory must start with /" >&2
  exit 1
   ;;
esac

# sudo apt install opam
# sudo apt install git
# sudo apt install python3-dev
# sudo apt install python3-venv                 # We need mypy without Cython
# sudo apt install rsync                        # opam
# sudo apt install pkgconf                      # why3, scipy
# sudo apt install autoconf                     # why3, scipy
# sudo apt install automake                     # scipy
# sudo apt install cvc5                         # why3
# sudo apt install libgmp-dev                   # why3
# sudo apt install libcairo2-dev                # why3-ide
# sudo apt install libgtk-3-dev                 # why3-ide
# sudo apt install libgtksourceview-3.0-dev     # why3-ide
# sudo apt install gfortran                     # scipy
# sudo apt install libssl-dev                   # scipy
# sudo apt install libopenblas-dev              # scipy

if [ -e "$D" ]; then
  echo "[skip] statwhy install directory already exists \"$D\"."
else
  echo "[do] mkdir $D"
  mkdir "$D" || exit 1
fi

if [ -e "$HOME/.opam" ]; then
  echo "[skip] opam already initialized."
else
  echo "[do] opam init"
  # modify ~/.profile.
  opam init --shell-setup || exit 1
fi

if [ -e "$HOME/.opam/$opam_switch" ]; then
  echo "[skip] opam switch already exists \"$HOME/.opam/$opam_switch\"."
else
  echo "[do] create opam switch"
  opam switch create "$opam_switch" --packages=ocaml-option-flambda.1,ocaml-variants.5.0.0+options || exit 1
fi

eval $(opam env --switch="$opam_switch")

if [ -e "$D/bin/python" ]; then
  echo "[skip] python venv already setup."
else
  echo "[do] create python venv"
  python3 -m venv "$D" || exit 1
fi

install_python_package() {
  pkg="$1"

  if "$D/bin/pip" list | grep -q "^${pkg} "; then
    echo "[skip] ${pkg} already installed."
  else
    echo "[do] install ${pkg}."
    "$D/bin/pip" install "${pkg}" || exit 1
  fi
}

install_python_package no-manylinux     # disable binary package (disable Cython)
install_python_package mypy
install_python_package scipy
install_python_package scipy-stubs
install_python_package scikit-posthocs

# The version constraint of these packages are different for why3 and cameleer.
# So, installing them with right versions at beginning avoids recompiling why3 when installing cameleer.
opam install -y ppx_deriving.6.0.3 ppx_sexp_conv.v0.16.0 sexplib.v0.16.0 sexplib0.v0.16.0

if opam list --short | grep -q '^why3$'; then
  echo "[skip] why3 already installed."
else
  echo "[do] install modified why3."
  opam pin add -y --working-dir --with-version=1.8.0 why3 . || exit 1
  opam pin add -y --working-dir --with-version=1.8.0 why3-ide . || exit 1
fi

git_clone_or_pull() {
  dir="$1"
  repo="$2"

  if [ -d "$D/$dir" ]; then
    echo "[pull] pull latest $dir."
    (cd "$D/$dir" && git pull)
  else
    echo "[do] clone $dir."
    git clone --depth 1 "$repo" "$D/$dir" || exit 1
  fi
}

git_clone_or_pull statwhy https://github.com/fm4stats/statwhy.git

if opam list --short | grep -q '^cameleer$'; then
  echo "[skip] cameleer(statwhy) already installed."
else
  echo "[do] install statwhy(cameleer)."
  (cd "$D/statwhy/cameleer" && opam pin add . -y --working-dir --with-version=0.1) || exit 1
fi

export PATH="$D/bin:$PATH"

why3 config detect || exit 1    # creates ~/.why3.conf

statwhy --genconf || exit 1     # creates ~/.statwhy.conf


# uninstall:
# opam switch remove OPAM_SWITCH
# rm -rf INSTALL_DIRECTORY
