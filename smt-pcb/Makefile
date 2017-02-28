all:
	python test.py
	./run_smt.sh
	python kicad_placer.py
view:
	pcbnew test.kicad_pcb &
clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak *.log

.PHONY: all explain install clean
