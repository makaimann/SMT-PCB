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

Now follow these instructions (credit: [Brian Hoskins](http://brianhoskins.uk/install-freerouting-ubuntu-14-04-15-04/)):

1. Open NetBeans.
2. Select File -> New Project.
3. In the **Categories** window, select *Java*.  In the **Projects** window, select *Java Project with Existing Sources*.  Select **Next**.
4. Name the project **FreeRouter** and accept the default path.  Select **Next**.
5. In the **Source Package Folders** area, select *Add Folder*.  Browse to the place where you cloned the FreeRouting source.  Select **Finish**.
6. Select File -> Project Properties.
7. In the **Categories** area, select *Libraries*.  With the compile tab displayed in the area on the right, select *Add JAR/Folder*.  Choose **/usr/share/java/jh.jar**
8. Select **Add JAR/Folder** again.  Choose **/usr/share/icedtea-web/netx.jar**
9. In the **Appication** area, choose *Web Start*.  Make sure the **Enable Web Start** box is NOT checked.
10.  In the **Categories** area, select *Run* and make sure the Configuration pull down is set to **\<default config\>**.
11. Select **OK** to exit Project Properties.
12.  From the NetBeans main menu, choose **Run** and select *Clean and Build Project*.  If all has gone well, it will conclude with **BUILD SUCCESSFUL**.

Once you've installed FreeRouting, follow these steps to integrate it into the design flow:
1. Make sure FreeRouting is running within NetBeans.
2. Type `cd ~/NetBeansProjects/FreeRouter`
3. Type `ant jar`
    * This will build an executable JAR of the FreeRouting project.

## Environment Variables
Set environment variables:
```
export PYTHONPATH="$SMT_PCB/smt-core:$SMT_PCB/kicad-python:$SMT_PCB/smt-pcb”
```

