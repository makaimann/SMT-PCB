# PCB Compiler

## Team
* Makai Mann (makaim@stanford.edu)
* Steven Herbst (sherbst@stanford.edu)

## Project Goal
Our goal is to create a fully-automated system for compiling a Magma-like circuit description into a manufacturable printed circuit board (PCB) design.  

## Motivation
This work is motivated by the fact that designing PCBs is time-consuming.  The process is largely manual, requiring the user to draw a schematic, position each component, and draw the copper routes between component pads.  Simple designs could take hours, and complicated designs can take days or even weeks.

In this project, we hope to significantly reduce design time by allowing users to describe circuits and their physical constraints in Python.  By doing so, users may take advantage of the language flexibility to make circuit generators, build abstraction levels, and embed debugging circuits in their designs.  Since the design will be automatically placed and routed, users can focus on the system architecture, rather than having to worry about how long it will take to physically integrate a new feature.

## Previous Work
At the schematic level, [SKiDL](https://github.com/xesscorp/skidl) allows users to instantiate components in Python and wire them together.  The result is a netlist that can be read by a PCB design tool.  In this way, the schematic drawing step is bypassed, allowing the user to start immediately with PCB placement and routing. 

Automated placement of components on a PCB is supported by some PCB design tools.  However, autoplacers are rarely used in practice because they tend to be slow and result in low-quality placements.  It may also be inconvenient to specify the positions of certain components, such as connectors, that have to be placed in a specific location.  

Automated routing of PCBs is supported by many PCB design tools.  In a typical PCB design flow, however, the autorouter is not used exclusively.  The designer might autoroute some traces while manually routing others, because it may be hard or time-consuming to specify the routing constraints needed to get the desired routing outcome.

As we work on this project we plan to take advantage of several open source projects related to PCB design.  First, the PCB designs themselves will be stored in the *.kicad_pcb format, which is readable by the open-source program [KiCAD](http://kicad-pcb.org).  KiCAD has a large user base and extensive component library, which make it a great development platform.

KiCAD has a low-level Python interface that exposes many functions to manipulate PCBs.  An effort to better document this library is currently underway by [Kevin McCoo](https://kicad.mmccoo.com).  We also plan to make use of the higher-level PCB functions available in a [fork of kicad-python](https://github.com/hyOzd/kicad-python).  

For automatic placement, we will build from the [SMT-PNR project](https://github.com/cdonovick/SMT-PNR) current underway at Stanford.  We initially tested the automatic placer built into KiCAD, but found that it was slow and did not produce a useable placement.  The SMT-PNR placer is intended primarily for FPGAs, but early experiments have suggested that it could perform well for PCB placement, given several extensions.

For autorouting, we plan to leverage existing work in the [FreeRouting project](https://github.com/nikropht/FreeRouting), a popular Java program often used in conjunction with KiCAD.  We considered using [Python-PCB](https://github.com/vygr/Python-PCB), but found that it does not support routing of surface-mount parts and does not consistently produce routes that pass all design rule checks (DRCs).

## Deliverables
* What do you hope to show when you are done? What are your deliverables?

## Timeline
* What are the major tasks and results you intend to pursue?
* How will you break them down?
* How are you planning to divide responsibility within your team?

1. Feb 20 - Feb 26
2. Feb 27 - Mar 5
3. Mar 6 - Mar 12
  1. Mar 7: Preliminary presentation
4. Mar 13 - Mar 19
  1. Mar 21: Final presentation 
