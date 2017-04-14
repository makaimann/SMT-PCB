PROJECT = freeduino
#PROJECT = simple

SMT_PCB_DIR = ../smt-pcb
FREE_ROUTE_DIR = $(HOME)/NetBeansProjects/FreeRouter/dist
PLOT_NAME = plot
QUANTITY = 2

PLACE_DATA_FILE = "place_times.txt" #can be used with --dout to record placement times

all: clean place route fab summary

place: describe_design run_smt_solver kicad_place_parts

describe_design:
	./$(PROJECT).py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb --dx 0.1 --dy 0.1

run_smt_solver:
	./$(SMT_PCB_DIR)/smt_place.py --json $(PROJECT).json --solver Z3 --logic Int

kicad_place_parts:
	./$(SMT_PCB_DIR)/kicad_placer.py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb

view:
	pcbnew $(PROJECT).kicad_pcb &

route: export_specctra run_freerouting import_specctra

export_specctra:
	./$(SMT_PCB_DIR)/export_specctra.py --pcb $(PROJECT).kicad_pcb --dsn $(PROJECT).dsn --json $(PROJECT).json

run_freerouting:
	./$(SMT_PCB_DIR)/run_freerouting.py --dsn $(PROJECT).dsn --route_dir $(FREE_ROUTE_DIR)

import_specctra:
	./$(SMT_PCB_DIR)/import_specctra.py --pcb $(PROJECT).kicad_pcb --ses $(PROJECT).ses

fab: edge gerbers bom

edge:
	./$(SMT_PCB_DIR)/edge.py --json $(PROJECT).json --pcb $(PROJECT).kicad_pcb

gerbers: 
	rm -rf ./$(PLOT_NAME)/
	rm -f $(PLOT_NAME).zip
	./$(SMT_PCB_DIR)/gen_gerbers.py --pcb $(PROJECT).kicad_pcb --plot $(PLOT_NAME)
	zip $(PLOT_NAME).zip $(PLOT_NAME)/*

bom: 
	./$(SMT_PCB_DIR)/octopart_bom.py --json $(PROJECT).json --bom $(PROJECT).csv

summary: 
	./$(SMT_PCB_DIR)/summary.py --json $(PROJECT).json --units inches

lint_code:
	-flake8 --max-complexity 6 --ignore=F405,F403,N801,N802,N806
	-pep8 *.py

tidy_code:
	autoflake --in-place --remove-unused-variables --remove-all-unused-imports *.py
	autopep8 --in-place --max-line-length=79 --aggressive --aggressive *.py

clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak 
	rm -f *.log *.json *.rules *.csv *.zip *.smt
	rm -rf ./$(PLOT_NAME)/

.PHONY: all explain install clean tidy_code lint_code
