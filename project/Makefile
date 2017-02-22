all:
	python schem_test.py
	./run_smt.sh
	python pcb_test.py
	cp netlist.pcb ../Python-PCB/.
	cd ../Python-PCB/ && pypy pcb.py --v 1 netlist.pcb > out.pcb
	cp ../Python-PCB/out.pcb .
	python route_test.py
view:
	pcbnew test.kicad_pcb &
clean:
	rm -f *.kicad_pcb *.net *.dict *.pro *.pyc *.pcb *.ses *.dsn *.kicad_pcb-bak

.PHONY: all explain install clean
