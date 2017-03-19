PROJECT = freeduino
# PROJECT = simple

SMT_PCB_DIR = ../smt-pcb
FREE_ROUTE_DIR = $(HOME)/NetBeansProjects/FreeRouter/dist

all: first second third

first:
	time ./$(PROJECT).py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb

second:
	time ./$(SMT_PCB_DIR)/smt_place.py --json $(PROJECT).json

third:
	time ./$(SMT_PCB_DIR)/kicad_placer.py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb

bom:
	time ./$(SMT_PCB_DIR)/digikey_bom.py --json $(PROJECT).json --bom $(PROJECT).csv

view:
	pcbnew $(PROJECT).kicad_pcb &

route:
	cd $(FREE_ROUTE_DIR); \
	java -jar "FreeRouter.jar"

lint_code:
	-flake8 --max-complexity 6 --ignore=F405,F403,N801,N802
	-pep8 *.py

tidy_code:
	autoflake --in-place --remove-unused-variables --remove-all-unused-imports *.py
	autopep8 --in-place --max-line-length=79 --aggressive --aggressive *.py

clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak 
	rm -f *.log *.json *.rules *.csv

.PHONY: all explain install clean tidy_code lint_code
