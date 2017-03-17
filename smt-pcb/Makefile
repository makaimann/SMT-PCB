PROJECT = freeduino
#PROJECT = xtal
#PROJECT = arduino
#PROJECT = simple

all: first second third

first:
	time python $(PROJECT).py $(PROJECT).json $(PROJECT).kicad_pcb

second:
	time ./run_smt.sh $(PROJECT).json

third:
	time python kicad_placer.py $(PROJECT).json $(PROJECT).kicad_pcb

view:
	pcbnew $(PROJECT).kicad_pcb &

tidy_code:
	autoflake --in-place --remove-unused-variables *.py
	autopep8 --in-place --aggressive --aggressive *.py

clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak *.log *.json *.rules

.PHONY: all explain install clean tidy_code
