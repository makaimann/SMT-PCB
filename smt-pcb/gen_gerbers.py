#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to generate gerbers from the kicad_pcb file
# Based on kicad-source-mirror/demos/python_scripts_examples/

# general imports
import json
import argparse
import pcbnew
import os
import os.path

# project imports
from kicad.pcbnew.board import Board
from kicad.point import Point
from board_tools import BoardTools


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--plot')
    args = parser.parse_args()

    # load board
    board = pcbnew.LoadBoard(args.pcb)

    # get plot options
    pctl = pcbnew.PLOT_CONTROLLER(board)
    popt = pctl.GetPlotOptions()
    
    # set up output directory
    plotDir = args.plot + '/'
    popt.SetOutputDirectory(plotDir)

    # Set plot options according to:
    # http://docs.oshpark.com/design-tools/kicad/generating-kicad-gerbers/

    # Options
    popt.SetPlotFrameRef(False) 
    popt.SetPlotPadsOnSilkLayer(False)
    popt.SetPlotValue(True)
    popt.SetPlotReference(True)
    popt.SetPlotInvisibleText(False)
    popt.SetPlotViaOnMaskLayer(True)
    popt.SetExcludeEdgeLayer(True)
    popt.SetMirror(False)
    popt.SetNegative(False)
    popt.SetUseAuxOrigin(False)

    popt.SetDrillMarksType(pcbnew.PCB_PLOT_PARAMS.NO_DRILL_SHAPE)
    popt.SetAutoScale(False)
    popt.SetScale(1)
    # TODO: Plot mode = filled
    popt.SetLineWidth(pcbnew.FromMM(0.1))
    
    # Gerber options
    popt.SetUseGerberProtelExtensions(True)
    popt.SetUseGerberAttributes(False)
    popt.SetSubtractMaskFromSilk(False)
    popt.SetGerberPrecision(6)

    # Layers to be plotted
    plot_plan = [
        ("CuTop", pcbnew.F_Cu, "Top layer"),
        ("CuBottom", pcbnew.B_Cu, "Bottom layer"),
        ("EdgeCuts", pcbnew.Edge_Cuts, "Edges")]
    
    # Plot the layers
    for layer_info in plot_plan:
        pctl.SetLayer(layer_info[1])
        pctl.OpenPlotfile(layer_info[0], 
                          pcbnew.PLOT_FORMAT_GERBER, 
                          layer_info[2])
        fullname = pctl.GetPlotFileName()
        basename = os.path.basename(fullname)
        print 'Plotting %s' % basename
        if pctl.PlotLayer() == False:
            raise Exception('Plotting error.')
    
    # Done with plotting gerbers
    pctl.ClosePlot()

    drlwriter = pcbnew.EXCELLON_WRITER(board)
    
    # Set Excellon format according to:
    # http://docs.oshpark.com/design-tools/kicad/generating-kicad-gerbers/

    # Drill units, zeros format
    metricFmt = False
    zerosFmt = pcbnew.EXCELLON_WRITER.DECIMAL_FORMAT
    drlwriter.SetFormat(metricFmt, zerosFmt)
    
    # Drill map format
    drlwriter.SetMapFileFormat(pcbnew.PLOT_FORMAT_POST)

    # Drill file options
    mirror = False
    minimalHeader = False
    mergeNPTH = True
    offset = pcbnew.wxPoint(0,0)
    drlwriter.SetOptions(mirror, minimalHeader, offset, mergeNPTH)

    genDrl = True
    genMap = False
    plotdir = pctl.GetPlotDirName()
    print 'Creating drill file.'
    drlwriter.CreateDrillandMapFilesSet(plotDir, genDrl, genMap)

if __name__ == '__main__':
    main()
