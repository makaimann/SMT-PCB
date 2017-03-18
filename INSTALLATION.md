# Ubuntu Installation Instructions
## Dependencies
1. KiCAD
2. Z3
3. Requires python2 and python3

### Install KiCAD
```
sudo add-apt-repository --yes ppa:js-reynaud/ppa-kicad
sudo apt update
sudo apt install kicad
```

### Install Z3 with Python3 bindings
Z3 can be found [here](https://github.com/Z3Prover/z3)

You can build it from source by using:
```
python <your local path to z3-master>/scripts/mk_make.py --python
cd build
make
sudo make install
```

If python2 is the default on your system, you can do the following:

```
alias python=python3
python <your local path to z3-master>/scripts/mk_make.py --python
cd build
make
sudo make install
alias python=python2
```

## Environment Variables
Set environment variables:
```
export KISYSMOD="/usr/share/kicad/modules”
export SMT_PCB="<your path>/SMT-PCB/“
export PYTHONPATH="$SMT_PCB/new:$SMT_PCB/kicad-python:$SMT_PCB/smt-pcb”
```
