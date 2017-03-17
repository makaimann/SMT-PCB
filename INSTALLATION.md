# Ubuntu Installation Instructions
## Dependencies
1. KiCAD
2. Z3
3. Requires python2 and python3

### Install KiCAD
1. sudo add-apt-repository --yes ppa:js-reynaud/ppa-kicad
2. sudo apt update
3. sudo apt install kicad

### Install Z3 with Python3 bindings
Z3 can be found [here](https://github.com/Z3Prover/z3)
You can build it from source by using:
python_scripts/mk_make.py --python

## Environment Variables
Set environment variables:
1. export KISYSMOD="/usr/share/kicad/modules”
2. export SMT_PCB="\<your path\>/SMT-PCB/“
3. export PYTHONPATH="$SMT_PCB/new:$SMT_PCB/kicad-python:$SMT_PCB/Python-PCB”
