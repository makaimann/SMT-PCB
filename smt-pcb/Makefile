PROJECT = test

all:
	time python arduino.py $(PROJECT).dict $(PROJECT).kicad_pcb
	@echo
	time ./run_smt.sh $(PROJECT).dict
	@echo
	time python kicad_placer.py $(PROJECT).dict $(PROJECT).kicad_pcb
view:
	pcbnew $(PROJECT).kicad_pcb &
clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak *.log

.PHONY: all explain install clean
