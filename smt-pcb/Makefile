PROJECT = arduino
# PROJECT = simple

all:
	time python $(PROJECT).py $(PROJECT).json $(PROJECT).kicad_pcb
	@echo
	time ./run_smt.sh $(PROJECT).json
	@echo
	time python kicad_placer.py $(PROJECT).json $(PROJECT).kicad_pcb
view:
	pcbnew $(PROJECT).kicad_pcb &
clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak *.log *.json

.PHONY: all explain install clean
