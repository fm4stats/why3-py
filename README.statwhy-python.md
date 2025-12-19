# README for extended why3 python plugin for statwhy

## Installation

```
% D=/some/directory/to/to/use/statwhy/with/python/plugin
% sudo apt install autoconf libcairo2-dev libgtk-3-dev libgtksourceview-3.0-dev
% sudo apt install cvc5
% sudo apt install python3-venv
% python3 -m venv $D/py
% $D/py/bin/pip install no-manylinux
% $D/py/bin/pip install mypy
% cd $D
% git clone git@github.com:ykwmt/why3-py.git
% git clone https://github.com/fm4stats/statwhy.git
% (cd why3; opam pin add . -y)
% (cd statwhy/cameleer; opam pin add . -y)
% why3 config detect
```

## Run

```
% cd why3
% MYPYPATH=$D/why3/examples/statwhy-python \
  WHY3_PYTHON_EXE=$D/py/bin/python \
  WHY3_PYTHON_TYPE_INFERENCE=$D/why3/plugins/python/inf_script.py \
  why3 ide examples/statwhy-python/multiple_hypotheses.py \
      --extra-config /home/your-user-name/.statwhy.conf
```

