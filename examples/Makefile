PROJECT = freeduino
#PROJECT = simple

SMT_PCB_DIR = ../smt-pcb
FREE_ROUTE_DIR = $(HOME)/NetBeansProjects/FreeRouter/dist
PLOT_NAME = plot

all: clean place route fab

place: first second third

first:
	./$(PROJECT).py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb 

second:
	./$(SMT_PCB_DIR)/smt_place.py --json $(PROJECT).json 

third:
	./$(SMT_PCB_DIR)/kicad_placer.py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb

view:
	pcbnew $(PROJECT).kicad_pcb &

route:
	./$(SMT_PCB_DIR)/export_specctra.py --pcb $(PROJECT).kicad_pcb
	./$(SMT_PCB_DIR)/run_freerouting.py --pcb $(PROJECT).kicad_pcb --route_dir $(FREE_ROUTE_DIR)
	./$(SMT_PCB_DIR)/import_specctra.py --pcb $(PROJECT).kicad_pcb

fab: edge gerbers bom

edge:
	./$(SMT_PCB_DIR)/edge.py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb

gerbers: 
	rm -rf ./$(PLOT_NAME)/
	rm -f $(PLOT_NAME).zip
	./$(SMT_PCB_DIR)/gen_gerbers.py --pcb $(PROJECT).kicad_pcb --plot $(PLOT_NAME)
	zip $(PLOT_NAME).zip $(PLOT_NAME)/*

bom: 
	./$(SMT_PCB_DIR)/digikey_bom.py --json $(PROJECT).json --bom $(PROJECT).csv

lint_code:
	-flake8 --max-complexity 6 --ignore=F405,F403,N801,N802,N806
	-pep8 *.py

tidy_code:
	autoflake --in-place --remove-unused-variables --remove-all-unused-imports *.py
	autopep8 --in-place --max-line-length=79 --aggressive --aggressive *.py

clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak 
	rm -f *.log *.json *.rules *.csv *.zip
	rm -rf ./$(PLOT_NAME)/

.PHONY: all explain install clean tidy_code lint_code
