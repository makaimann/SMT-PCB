# Compiling Circuit Descriptions to Manufacturable PCBs

## Team
* Makai Mann (makaim@stanford.edu)
* Steven Herbst (sherbst@stanford.edu)

## Project Goal
Our goal is to create a fully-automated system for compiling a Magma-like circuit description into a manufacturable printed circuit board (PCB) design.  

## Motivation
This work is motivated by the fact that designing PCBs is time-consuming.  The process is largely manual, requiring the user to draw a schematic, position each component, and draw the copper routes between component pads.  Simple designs could take hours, and complicated designs can take days or even weeks [1,2].

In this project, we hope to significantly reduce design time by allowing users to describe circuits and their physical constraints in Python.  By doing so, users may take advantage of the language flexibility to make circuit generators, build abstraction levels, and embed debugging circuits in their designs.  Since the design will be automatically placed and routed, users can focus on the system architecture, rather than having to worry about how long it will take to physically integrate a new feature.

## Previous Work
At the schematic level, [SKiDL](https://github.com/xesscorp/skidl) allows users to instantiate components in Python and wire them together.  The result is a netlist that can be read by a PCB design tool.  In this way, the schematic drawing step is bypassed, allowing the user to start immediately with PCB placement and routing. 

Automated placement of components on a PCB is supported by some PCB design tools.  However, autoplacers are rarely used in practice because they tend to be slow and result in low-quality placements [3,4].  It may also be inconvenient to specify the positions of certain components, such as connectors, that have to be placed in a specific location [4,5].  

Automated routing of PCBs is supported by many PCB design tools.  In a typical PCB design flow, however, the autorouter is not used exclusively.  The designer might autoroute some traces while manually routing others, because it may be hard or time-consuming to specify the routing constraints needed to get the desired routing outcome [6].

As we work on this project we plan to take advantage of several open source projects related to PCB design.  First, the PCB designs themselves will be stored in the *.kicad_pcb format, which is readable by the open-source program [KiCAD](http://kicad-pcb.org).  KiCAD has a large user base and extensive component library, which make it a great development platform.

KiCAD has a low-level Python interface that exposes many functions to manipulate PCBs.  An effort to better document this library is currently underway by [Kevin McCoo](https://kicad.mmccoo.com).  We also plan to make use of the higher-level PCB functions available in a [fork of kicad-python](https://github.com/hyOzd/kicad-python).  

For automatic placement, we will build from the [SMT-PNR project](https://github.com/cdonovick/SMT-PNR) current underway at Stanford.  We initially tested the automatic placer built into KiCAD, but found that it was slow and did not produce a useable placement.  The SMT-PNR placer is intended primarily for FPGAs, but early experiments have suggested that it could perform well for PCB placement, given several extensions.

For autorouting, we plan to leverage existing work in the [FreeRouting project](https://github.com/nikropht/FreeRouting), a popular Java program often used in conjunction with KiCAD.  We considered using [Python-PCB](https://github.com/vygr/Python-PCB), but found that it does not support routing of surface-mount parts and does not consistently produce routes that pass all design rule checks (DRCs).

## Deliverables
1. Python Circuit Description
 1. Ability to instantiate any component from the KiCAD library.
 2. Ability to declare wires connecting pads of instantiated components.  Each wire connects two or more pads, and a given pad may only be connected to one net.
 3. Ability to declare routing constraints on any wire: clearance, trace width, via drill, and via diameter.
 4. Ability to specify a fixed position and orientation for any component.
2. Automatic Placement
 1. Ability to automatically place components on the top side of the PCB such that: all lie within the board edge, none overlap, and the maximum distance between any two connected components is reasonable.  
 2. Ability to automatically rotate components in 90 degree increments as an additional degree of freedom in the autoplace routine.
 3. Take into account the fixed placements when running the autoplacer.
 4. Implement fixed placements with at least 10um resolution, to minimize impact on system-level mechnical tolerances.
 5. Allow fixed placements to lie partially outside the board edge, as is commonly required for connectors.
 6. Use pad-level connectivity information in placement
3. Other
 1. Ability to draw the board edge.
 2. Ability to center the PCB design within the title block.
 3. The PCB design must pass all KiCAD DRCs after automatic placement and routing.
 4. Demonstrate system operation by automatically generating the PCB design for [Arduino Uno](https://www.arduino.cc/en/uploads/Main/Arduino_Uno_Rev3-schematic.pdf)

## Timeline

Note: We have started work on the project already, and have completed 2(i) and 2(iii).

1. Feb 20 - Feb 26
 * SH: Implement 1(i) - 1(iv)
 * MM: Work on 2(ii)
2. Feb 27 - Mar 5
 * SH: Implement 2(iv) and 2(v) for preliminary presentation
 * MM: Finish 2(ii), work on preliminary presentation
3. Mar 6 - Mar 12
 * SH: Implement 3(iv) for presentation
 * MM: Implement 2(vi)
4. Mar 13 - Mar 19
 * SH: Implement 3(i) - 3(iii), work on final presentation
 * MM: Work on final presentation
 
## References

[1] C. Bazeghi, F. Mesa-Martinez, and J. Renau. µComplexity: Estimating Processor Design Effort. In International Symposium on Microarchitecture, Nov 2005. https://users.soe.ucsc.edu/~renau/docs/wced06.pdf

[2] Polycom and Cadence. Shaving Weeks of PCB Design Cycle Via Auto-Routing. https://www.cadence.com/content/dam/cadence-www/global/en_US/documents/tools/ic-package-design-analysis/polycom-cs.pdf

[3] Jones, David L. PCB Layout Tutorial. pg. 22 Alternate Zone, 2004. https://server.ibfriedrich.com/wiki/ibfwikien/images/d/da/PCB_Layout_Tutorial_e.pdf

[4] Stack Exchange Question. Apr 25, 2015. http://electronics.stackexchange.com/questions/166653/new-to-pcb-design-why-doesnt-auto-placing-components-exist

[5] Forum Question. May 22, 2013. https://forum.allaboutcircuits.com/threads/pcb-designing-auto-place-auto-route.86714/

[6] Hernandez, Sal. Sunstone Circuits Forum. http://forum.sunstone.com/autorouting-what-is-an-autorouter-and-why-do-i-care-t15711.html

