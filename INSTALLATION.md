# Ubuntu Installation Instructions
## Dependencies
1. KiCAD
2. Z3
3. Requires python2 and python3
4. FreeRouting (if you would like to route the design)

### Install KiCAD
```
sudo add-apt-repository --yes ppa:js-reynaud/ppa-kicad
sudo apt update
sudo apt install kicad
```

### Install Z3 with Python3 bindings

If python2 is the default on your system, do the following:

```
git clone https://github.com/Z3Prover/z3.git
cd z3
alias python=python3
python scripts/mk_make.py --python
cd build
make
sudo make install
alias python=python2
```

If python3 is the default on your system, do the following:
```
git clone https://github.com/Z3Prover/z3.git
cd z3
python scripts/mk_make.py --python
cd build
make
sudo make install
```

### FreeRouting Installation

Install FreeRouting dependencies

```
sudo apt-get install netbeans javahelp2 icedtea-netx-common
```

Get the modified FreeRouting source code:

```
git clone https://github.com/sgherbst/FreeRouting.git
```

Now follow instructions [here](http://brianhoskins.uk/install-freerouting-ubuntu-14-04-15-04/), starting from the section titled "Loading FreeRouting into NetBeans, Compiling and Running".

Once you've installed FreeRouting, follow these steps to integrate it into the design flow:
1. Make sure FreeRouting is running within NetBeans.
2. Type `cd ~/NetBeansProjects/FreeRouter`
3. Type `ant jar`
    * This will build an executable JAR of the FreeRouting project.

## Environment Variables
Set environment variables:
```
export KISYSMOD="/usr/share/kicad/modules”
export SMT_PCB="<your path>/SMT-PCB/“
export PYTHONPATH="$SMT_PCB/smt-core:$SMT_PCB/kicad-python:$SMT_PCB/smt-pcb”
```

