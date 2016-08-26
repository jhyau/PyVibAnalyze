# -*- coding: utf-8 -*-
"""
Created on Thu Jul 14 14:31:59 2016

This program analyzes the data sets added in by the user. All data sets of MScan are imported from the folder chosen by the user, and it
graphs the current chosen data set's magnitude, phase, and gain, as well as the average of all data sets' magnitude, phase, and gain. The
average graph also calculates and graphs the standard error of mean. The data sets can be filtered through the category comboboxes, and the 
data sets calculated in the averages can also be filtered depending on the category chosen in the average category comboboxes. The project is
saved as a pickle (*.p) file. The Characteristic Frequency and Q10dB are calculated and displayed just above the Magnitude graph. If the data set
does not mention whether a mouse is dead or alive, a message box will pop up to ask the user the mouse's status, then calculate CF. The Q10dB is 
also displayed as a dashed red line on the Magnitude graph. The noise floor/threshold can also be set, and it will show up on the Magnitude
graph as a dashed black line. All data points below the noise floor are NaNs. The phase shift is also calculated for each data set, and done so
before the average phase is calculated. The phase shift can be unchecked anytime to see the phase before it has been shifted. All data sets can
also be exported to Excel, which includes each individual data set's magnitude, shifted phase, and gain, as well as the averages and standard
error for each average. The averages are split into all possible different combinations based on the categories listed in the combo boxes. A
dialog box will pop up to ask what the user would like to name the Excel files containing the averages. The individual data sets will be named
simply based on the data set name. All graphs are labelled, for both x and y axis, and title. Also, each graph can be exported as an image by 
right-clicking the desired graph, choosing export, then choosing image, and hitting the export button.

@author: OHNS, Jacqueline Yau, John Oghalai, Patrick Raphael
"""

from PyQt4 import QtCore, QtGui, uic

from PyQt4.QtGui import *
from PyQt4.QtCore import *
from collections import defaultdict
from scipy import interpolate, stats
import os
import sys
import traceback
import numpy as np
import pickle
import math
import pyqtgraph as pg
import xlsxwriter

# for Windows uncomment this line
#sys.path.append("C:\\PyVib\\src")
# for MacOS X uncomment this line
sys.path.append('/Volumes/NO NAME/OCT Mscan analysis program/PyVib src')
import MScan

#Set to a white background
pg.setConfigOption('background', 'w')

#form_class = uic.loadUiType(os.path.join("..", "ui", "PyOCT.ui"))[0]                 # Load the UI
form_class = uic.loadUiType("pyvibanalyze.ui")[0]     # Load the UI

class PyVibAnalyzeWindowClass(QtGui.QMainWindow, form_class):
    def __init__(self, parent=None):
        QtGui.QMainWindow.__init__(self, parent)
        try:
            self.setupUi(self)
        except Exception as ex:
            print(format(ex))
            
        self.addDataSets_pushBiutton.clicked.connect(self.addDataSets)
        self.excludeDataSet_checkBox.setChecked(False)
        self.phaseShift_checkBox.setChecked(True)
        self.logX_checkBox.setChecked(False)
        self.lineEdit.setText("0.0")
        self.CF_lineEdit.setText("0.0")
        self.CF_lineEdit.setReadOnly(True)
        self.Q10db_lineEdit.setText("0.0")
        self.Q10db_lineEdit.setReadOnly(True)
        self.N_lineEdit.setText("0")
        self.N_lineEdit.setReadOnly(True)
        self.apply_pushButton.clicked.connect(self.newCategories)
        self.excludeDataSet_checkBox.stateChanged.connect(self.excludeData)
        self.remove_pushButton.clicked.connect(self.removeCategories)
        self.dataSet_comboBox.currentIndexChanged.connect(self.dataSetChanged)
        self.dataSet_category_comboBox.currentIndexChanged.connect(self.filterData)
        self.dataSet_category_comboBox_2.currentIndexChanged.connect(self.filterData)
        self.dataSet_category_comboBox_3.currentIndexChanged.connect(self.filterData)
        self.avg_category_comboBox.currentIndexChanged.connect(self.filterAverage)
        self.avg_category_comboBox_2.currentIndexChanged.connect(self.filterAverage)
        self.newProject_pushBiutton.clicked.connect(self.createNewProject)
        self.saveProject_pushBiutton.clicked.connect(self.saveProject)
        self.openProject_pushBiutton.clicked.connect(self.openProject)
        self.lineEdit.returnPressed.connect(self.setThreshold)
        self.phaseShift_checkBox.stateChanged.connect(self.phaseShiftPrep)
        self.logX_checkBox.stateChanged.connect(self.phaseShiftPrep)
        self.excel_pushButton.clicked.connect(self.exportToExcel)
#        self.magPlot.mouseReleaseEvent = self.mouseCFCalculation
        self.newProject()
        self.setComboBoxDefaults()
    
    #Each new project's data is contained in these data structures    
    def newProject(self):
        self.dataSets = []
        self.categories = []
        self.dataSetNameDict = {}
        #Keeps track of the data sets that are included in the average calculation
        self.avgData = {}
        #Keeps track of the chosen threshold for each data set
        self.threshold = {}
        #Keeps track of mouse status if there are data sets that did not label whether a mouse is dead or live
        self.mouseStatus = {}
        
    #Sets the default comboBox categories for data set comboBox and average comboBox
    def setComboBoxDefaults(self):    
        self.categories.append("")
        self.categories.append("dead")
        self.categories.append("live")
        self.categories.append("BM")
        self.categories.append("TM")
        self.categories.append("RL")
        
        for name in self.categories:
            self.dataSet_category_comboBox.addItem(name)
            self.dataSet_category_comboBox_2.addItem(name)
            self.dataSet_category_comboBox_3.addItem(name)
            self.avg_category_comboBox.addItem(name)
            self.avg_category_comboBox_2.addItem(name)
    
    #Creates a new project and clears all plots and previous project data        
    def createNewProject(self):
        self.newProject()
        self.magPlot.clear()
        self.phasePlot.clear()
        self.gainPlot.clear()
        self.avgMag_Plot.clear()
        self.avgPhase_Plot.clear()
        self.avgGain_Plot.clear()
        self.dataSet_comboBox.clear()
        self.dataSet_category_comboBox.clear()
        self.dataSet_category_comboBox_2.clear()
        self.dataSet_category_comboBox_3.clear()
        self.avg_category_comboBox.clear()
        self.avg_category_comboBox_2.clear()
        self.setComboBoxDefaults()
        self.categories_textEdit.clear()
        self.excludeDataSet_checkBox.setChecked(False)
        self.phaseShift_checkBox.setChecked(False)
        self.lineEdit.setText("0.0")
        self.CF_lineEdit.setText("0.0")
        self.CF_lineEdit.setReadOnly(True)
        self.Q10db_lineEdit.setText("0.0")
        self.Q10db_lineEdit.setReadOnly(True)
        self.N_lineEdit.setText("0")
        self.N_lineEdit.setReadOnly(True)
    
    #Saves the current project in a pickle file, allows user to choose directory to save in    
    #Files end with .p as pickle file    
    def saveProject(self):
        #Keep track of all data in a large list
        save = [self.dataSets, self.categories, self.dataSetNameDict, self.avgData, self.threshold, self.mouseStatus]
        caption = "Save file"
        fil = "Pickles (*.p)"
        path = '.'
        dataDir = QtGui.QFileDialog.getSaveFileName(self, caption, path, fil)        
        try:        
            pickle.dump(save, open(dataDir, "wb"))
        except:
            traceback.print_exc()
            print('Could not save project at %s' % dataDir)
    
    #Opens a previous project from a pickle file, user chooses from a file dialog box
    #Can only open projects that are .p pickle files
    def openProject(self):
        caption = "Open file"
        fil = "Pickles (*.p)"
        path = '.'
        dataDir = QtGui.QFileDialog.getOpenFileName(self, caption, path, fil)
        try:
            #Load in the data from the pickle file of the saved project
            prev = pickle.load(open(dataDir, "rb"))
            self.dataSets = prev[0]
            self.categories = prev[1]
            self.dataSetNameDict = prev[2]
            self.avgData = prev[3]
            self.threshold = prev[4]
            self.mouseStatus = prev[5]
            
            #Set N for number of data sets in average calculation
            self.N_lineEdit.setText(str(len(self.avgData)))
            
            self.dataSet_comboBox.clear()
            
            for n in self.dataSetNameDict:
                self.dataSet_comboBox.addItem(n)
            
            self.dataSet_category_comboBox.clear()
            self.dataSet_category_comboBox_2.clear()
            self.dataSet_category_comboBox_3.clear()
            
            #Sets the category comboBoxes to have the right categories
            for s in self.categories:
                if self.dataSet_category_comboBox.findText(s) == -1:
                    self.dataSet_category_comboBox.addItem(s)
                    self.dataSet_category_comboBox_2.addItem(s)
                    self.dataSet_category_comboBox_3.addItem(s)
                    
            self.categories_textEdit.clear()
            self.averagePlot()
        except:
            traceback.print_exc()
            print('Could not open project at %s' % dataDir)
    
    #Sets the noise floor/threshold whenever user inputs a new number into the Line Edit        
    def setThreshold(self):
        current = self.dataSet_comboBox.currentText()
        floor = self.lineEdit.text()
        num = float(floor)
        self.threshold[current] = num
        self.plotDataSet(self.dataSetNameDict[current], current)
        self.averagePlot()  
    
    #Filters out the data sets to be averaged together
    def filterAverage(self):
        self.avgData.clear()
        curText1 = self.avg_category_comboBox.currentText()
        curText2 = self.avg_category_comboBox_2.currentText()
        if curText1 != "" or curText2 != "":
            for name in self.dataSetNameDict:
                check = True
                #Case insensitive by turning the strings to lower-case first
                temp = name.lower()
                text1 = curText1.lower()
                text2 = curText2.lower()
                if (temp.find(text1) == -1) or (temp.find(text2) == -1):
                    check = False
                if check == True:
                    self.avgData[name] = self.dataSetNameDict[name]
        #If there are no filters chosen
        else:
            for name in self.dataSetNameDict:
                self.avgData[name] = self.dataSetNameDict[name]
        
        self.N_lineEdit.setText(str(len(self.avgData)))
        self.averagePlot()
    
    #Exclude data from average by removing it from the avgData dictionary, includes again if checkbox is unchecked
    def excludeData(self):
        if bool(self.dataSetNameDict) == True:
            if self.excludeDataSet_checkBox.isChecked() == True:
                curData = self.dataSet_comboBox.currentText()
                if curData in self.avgData:
                    del self.avgData[curData]
            else:
                curData = self.dataSet_comboBox.currentText()
                if curData not in self.avgData:
                    self.avgData[curData] = self.dataSetNameDict[curData]
            
            self.N_lineEdit.setText(str(len(self.avgData)))
            self.averagePlot()
            
    #Adds new categories to the combo boxes for data set and average
    def newCategories(self):
        string = self.categories_textEdit.toPlainText()
        cat = str(string)
        for words in cat.split():
            if (words not in self.categories):
                self.categories.append(words)
                
        for s in self.categories:
            if self.dataSet_category_comboBox.findText(s) == -1:
                self.dataSet_category_comboBox.addItem(s)
                self.dataSet_category_comboBox_2.addItem(s)
                self.dataSet_category_comboBox_3.addItem(s)
                self.avg_category_comboBox.addItem(s)
                self.avg_category_comboBox_2.addItem(s)
        
    #Allows for filtering for multiple categories exactly, and search is case-insensitive
    def filterData(self):
        self.dataSet_comboBox.clear()
        curText1 = self.dataSet_category_comboBox.currentText()
        curText2 = self.dataSet_category_comboBox_2.currentText()
        curText3 = self.dataSet_category_comboBox_3.currentText()
        if curText1 != "" or curText2 != "" or curText3 != "":
            #Need to iterate from the map, not combobox because combobox is being modified
            for name in self.dataSetNameDict:
                check = True
                #Case insensitive by turning the strings to lower-case first
                temp = name.lower()
                text1 = curText1.lower()
                text2 = curText2.lower()
                text3 = curText3.lower()
                if (temp.find(text1) == -1) or (temp.find(text2) == -1) or (temp.find(text3) == -1):
                    check = False
                if check == True:
                    self.dataSet_comboBox.addItem(name)
        #If there are no filters chosen
        else:
            for name in self.dataSetNameDict:
                self.dataSet_comboBox.addItem(name)
    
    #Removes categories from the category combo boxes for data set and average
    def removeCategories(self):
        string = self.categories_textEdit.toPlainText()
        rem = str(string)
        for words in rem.split():
            if (words in self.categories):
                self.categories.remove(words)
                index = self.dataSet_category_comboBox.findText(words)
                self.dataSet_category_comboBox.removeItem(index)
                self.dataSet_category_comboBox_2.removeItem(index)
                self.dataSet_category_comboBox_3.removeItem(index)
                self.avg_category_comboBox.removeItem(index)
                self.avg_category_comboBox_2.removeItem(index)
            else:
                print("This category does not exist")
    
    #Prepares the correct data set that needs phase shifting
    def phaseShiftPrep(self):
        cur = self.dataSet_comboBox.currentText()
        self.plotDataSet(self.dataSetNameDict[cur], cur)
    
    #Rounds down to the nearest multiple of mul
    def round_down(self, dif, mul):
        return math.floor(dif / mul) * mul
    
    #Shifts the phase so all phase is within 2*PI of the 80dB curve
    def phaseShift(self, magResp, phase, freq, amp):
        resultPhase = np.zeros((len(freq), len(amp)))
        resultPhase[:, :] = np.NaN
        
        check = False
        
        for i in range(len(freq)):
            for j in range(len(amp)):
                
                #Curve of the 80dB phase
                if j != len(amp) - 1:
                    index = len(amp) - 1                    
                    
                    #If current phase curve has NaN
                    if np.isnan(phase[i][j]) == True:
                        resultPhase[i][j] = phase[i][j]
                    
                    #Case when the 80dB curve has NaN at a point
                    elif np.isnan(phase[i][len(amp) - 1]) == True:
                        #Iterate through all curves to find one that is not NaN
                        for k in range(len(amp) - 1):
                            if (np.isnan(phase[i][len(amp) - (k + 2)]) == False):
                                index = len(amp) - (k + 2)
                                check = True
                                break
                        
                        #All curves have NaN at this point, so this point is NaN
                        if check == False:
                            index = np.NaN
                            resultPhase[i][j] = np.NaN
                    
                    #Phase shifting/adjusting
                    if np.isnan(index) == False:
                        dif = phase[i][j] - phase[i][index]
                        if dif > (2 * np.pi):
                            adjust = self.round_down(dif, 2 * np.pi)
                            result = phase[i][j] - adjust
                            resultPhase[i][j] = result
                        elif dif < -(2 * np.pi):
                            adjust = self.round_down(math.fabs(dif), 2 * np.pi)
                            result = phase[i][j] + adjust
                            resultPhase[i][j] = result
                        else:
                            resultPhase[i][j] = phase[i][j]
                
                #Keep the original data points of the 80db curve
                else:
                    resultPhase[i][j] = phase[i][j]
        
        return resultPhase
        
    
    #Takes in the a data set's magResp, phase, freq, and amp, finds the NaNs, and returns 
    #the corrected magResp and phase
    def findNaNs(self, magResp, phase, freq, amp, setName):
        resultMag = np.zeros((len(freq), len(amp)))
        resultMag[:, :] = np.NaN
        resultPhase = np.zeros((len(freq), len(amp)))
        resultPhase[:, :] = np.NaN
        
        thres = self.threshold[setName]
        
        for i in range(len(freq)):
            for j in range(len(amp)):
                if magResp[i][j] >= thres:
                    resultMag[i][j] = magResp[i][j]
                    resultPhase[i][j] = phase[i][j]
                else :
                    resultMag[i][j] = np.NaN
                    resultPhase[i][j] = np.NaN
        
        return resultMag, resultPhase
    
    #Plots the selected data set in the combo box    
    def plotDataSet(self, dataSet, setName):
        audioParams = dataSet.audioParams
        magResp = dataSet.magResp
        freq = audioParams.freq[0, :]
        amp = audioParams.amp
        
        #Unwrapping the phase data along the frequency axis
        phase = dataSet.phaseResp
        self.phasePlot.clear()     
        unWrapThreshold = np.pi
        phase = np.unwrap(phase, discont=unWrapThreshold, axis=0)
        
        self.magPlot.clear()
        
        #If threshold/noise floor is set, finds the NaNs in the magResp and applies to phase as well
        magRespNew, phase = self.findNaNs(magResp, phase, freq, amp, setName)
        
        #Shifts the phase if check box is checked
        if self.phaseShift_checkBox.isChecked() == True:
            phase = self.phaseShift(magRespNew, phase, freq, amp)            
        
        for a_i in range(len(amp)):
            factor = 200 / len(amp)
            red = 200 - a_i * factor
            green = 200 - a_i * factor
            #Creates a different shade of blue for each curve
            coloredPen = pg.mkPen(color=(red, green, 255), width=2)
            self.magPlot.plot(freq, magResp[:, a_i], pen=coloredPen)
            self.phasePlot.plot(freq, phase[:, a_i], pen=coloredPen)
            
        self.magPlot.setLogMode(x=False, y=True)
        self.phasePlot.setLogMode(x=False)
        self.gainPlot.setLogMode(x=False)
        #Checks if the user wants x-axis to be plotted in log as well
        if self.logX_checkBox.isChecked() == True:
            self.magPlot.setLogMode(x=True)
            self.phasePlot.setLogMode(x=True)
            self.gainPlot.setLogMode(x=True)
        
        #Calculates the CF
        self.calculateCF(magRespNew, freq, amp, setName)
        #Plots the gain graph
        self.plotGain(magRespNew, freq, amp)
        
        #If a threshold is set, graph the threshold line, in a dashed black line
        if self.threshold[setName] != 0:
            #Create the threshold line
            line = []
            for i in range(len(freq)):
                line.append(self.threshold[setName]) 
                
            #Plot the threshold line
            pen = pg.mkPen('k', style=QtCore.Qt.DashLine)
            self.magPlot.plot(freq, line, pen=pen)
            
        #Setting the labels on axes
        self.magPlot.setTitle('Magnitude Response at Stim Frequency')
        self.magPlot.setLabel('left', 'Response', units='nm')
        self.magPlot.setLabel('bottom', 'Stim Frequency', units='kHz')
        self.phasePlot.setTitle('Phase at Stim Frequency')
        self.phasePlot.setLabel('bottom', 'Stim Frequency', units='kHz')
        self.phasePlot.setLabel('left', 'Phase', units='rad')
        
    #Plots the gain graph of the current data set
    def plotGain(self, magResp, freq, amp):
        self.gainPlot.clear()
        gain = np.zeros((len(freq), len(amp)))
        gain[:, :] = np.NaN
        #Calculate the gain for each data point
        for j in range(len(amp)):
            pascal = (2 * math.pow(10,-5)) * math.pow(10, (amp[j] / 20))
            for i in range(len(freq)):
                gain[i][j] = magResp[i][j] / pascal
    
        for k in range(len(amp)):
            factor = 200 / len(amp)
            red = 200 - k * factor
            green = 200 - k * factor
            #Creates a different shade of blue for each curve
            coloredPen = pg.mkPen(color=(red, green, 255), width=2)
            self.gainPlot.plot(freq, gain[:, k], pen=coloredPen)
            
        self.gainPlot.setLogMode(y=True)
        #Setting the labels on gain graph
        self.gainPlot.setTitle('Gain at Stim Frequency')
        self.gainPlot.setLabel('left', 'Gain', units='nm/Pa')
        self.gainPlot.setLabel('bottom', 'Stim Frequency', units='kHz')
    
    #Calculates the gain from the magnitude
    def calculateGain(self, magResp, freq, amp):
        gain = np.zeros((len(freq), len(amp)))
        gain[:, :] = np.NaN
        #Calculate the gain for each data point
        for j in range(len(amp)):
            pascal = (2 * math.pow(10,-5)) * math.pow(10, (amp[j] / 20))
            for i in range(len(freq)):
                gain[i][j] = magResp[i][j] / pascal
        
        return gain
    
    #Plots the average graphs of all the data 
    def averagePlot(self):    
        freqlen = 0
        amplen = 0
        frequency = []
        amplitude = []
        
        #A 2D array where each element holds a list for all the data points of that respective position
        allArraysMag = defaultdict(lambda : defaultdict(list))
        allArraysPhase = defaultdict(lambda : defaultdict(list))
        allArraysPhaseError = defaultdict(lambda : defaultdict(list))
        allArraysMagError = defaultdict(lambda : defaultdict(list))
        allArraysGain = defaultdict(lambda : defaultdict(list))
        allArraysGainError = defaultdict(lambda : defaultdict(list))
        
        if bool(self.avgData) == False:
            self.avgMag_Plot.clear()
            self.avgPhase_Plot.clear()
            self.avgGain_Plot.clear()
        else:
            #Iterate through the data sets in the avgData dictionary, also unwrapping phase
            for d in self.avgData:
                dataSet = self.avgData[d]
                audioParams = dataSet.audioParams
                magResp = dataSet.magResp
                phase = dataSet.phaseResp     
                unWrapThreshold = np.pi
                phase = np.unwrap(phase, discont=unWrapThreshold, axis=0)
                freq = audioParams.freq[0, :]
                amp = audioParams.amp
                freqlen = len(freq)
                amplen = len(amp)
                frequency = freq
                amplitude = amp
                
                #Calculate the gain
                gain = self.calculateGain(magResp, freq, amp)
                #Phase shift the phase first before averaging
                phase = self.phaseShift(magResp, phase, freq, amp)
                
                thres = self.threshold[d]
                
                #Adds each data point from each data set to its corresponding list
                #Need the error list because the stats.sem 0.16.1 version can't handle NaNs 
                for i in range(len(freq)):
                    for j in range(len(amp)):
                        if magResp[i][j] >= thres:
                            allArraysMag[i][j].append(magResp[i][j])
                            allArraysPhase[i][j].append(phase[i][j])
                            allArraysGain[i][j].append(gain[i][j])
                            if np.isnan(phase[i][j]) == False:
                                allArraysPhaseError[i][j].append(phase[i][j])
                            if np.isnan(magResp[i][j]) == False:
                                allArraysMagError[i][j].append(magResp[i][j])
                            if np.isnan(gain[i][j]) == False:
                                allArraysGainError[i][j].append(gain[i][j])
                        else:
                            allArraysMag[i][j].append(np.NaN)
                            allArraysPhase[i][j].append(np.NaN)
                            allArraysGain[i][j].append(np.NaN)
            
            #Hold the resulting averages of each point
            resultMag = np.zeros((freqlen, amplen))
            resultMag[:, :] = np.NaN
            resultPhase = np.zeros((freqlen, amplen))
            resultPhase[:, :] = np.NaN
            resultGain = np.zeros((freqlen, amplen))
            resultGain[:, :] = np.NaN
            
            #Hold the standard errors of mean for each data point
            stdErrorMag = np.zeros((freqlen, amplen))
            stdErrorMag[:, :] = np.NaN
            stdErrorGain = np.zeros((freqlen, amplen))
            stdErrorGain[:, :] = np.NaN
            stdErrorPhase = np.zeros((freqlen, amplen))
            stdErrorPhase[:, :] = np.NaN
            
            #Average each list in the 2D array, to find the average for that corresponding point
            for k in range(freqlen):
                for z in range(amplen):
                    resultMag[k][z] = np.nanmean(allArraysMag[k][z])
                    resultPhase[k][z] = np.nanmean(allArraysPhase[k][z])
                    resultGain[k][z] = np.nanmean(allArraysGain[k][z])
                    #Calculates the standard error of mean with degree of freedom = 0
                    stdErrorMag[k][z] = stats.sem(allArraysMagError[k][z], ddof=0)
                    stdErrorGain[k][z] = stats.sem(allArraysGainError[k][z], ddof=0)
                    stdErrorPhase[k][z] = stats.sem(allArraysPhaseError[k][z], ddof=0)
            
            #Plots the average magnitude and phase graphs
            self.avgMag_Plot.clear()
            self.avgPhase_Plot.clear()
            self.avgGain_Plot.clear()
            for i in range(amplen):
                factor = 200 / amplen
                red = 200 - i * factor
                green = 200 - i * factor
                coloredPen = pg.mkPen(color=(red, green, 255), width=2)
                self.avgMag_Plot.plot(frequency, resultMag[:, i], pen=coloredPen)
                self.avgPhase_Plot.plot(frequency, resultPhase[:, i], pen=coloredPen)
                self.avgGain_Plot.plot(frequency, resultGain[:, i], pen=coloredPen)
                    
            self.avgMag_Plot.setLogMode(y=True)
            self.avgGain_Plot.setLogMode(y=True)
            
            #Set the axes labels
            self.avgMag_Plot.setTitle('Avg. Magnitude Response at Stim Frequency')
            self.avgMag_Plot.setLabel('left', 'Average Response', units='nm')
            self.avgMag_Plot.setLabel('bottom', 'Stim Frequency', units='kHz')
            self.avgPhase_Plot.setTitle('Average Phase at Stim Frequency')
            self.avgPhase_Plot.setLabel('left', 'Average Phase (shifted)', units='rad')
            self.avgPhase_Plot.setLabel('bottom', 'Stim Frequency', units='kHz')
            self.avgGain_Plot.setTitle('Average Gain at Stim Frequency')
            self.avgGain_Plot.setLabel('left', 'Average Gain', units='nm/Pa')
            self.avgGain_Plot.setLabel('bottom', 'Stim Frequency', units='kHz')
            
            #Plot the standard error of each mean
            self.plotStandardError(resultMag, stdErrorMag, freqlen, amplen, frequency, "mag")
            self.plotStandardError(resultGain, stdErrorGain, freqlen, amplen, frequency, "gain")
            self.plotStandardError(resultPhase, stdErrorPhase, freqlen, amplen, frequency, "phase")
    
    #Plots the standard error for the averages
    def plotStandardError(self, result, stdError, freqlen, amplen, frequency, kind):
        for x in range(freqlen):
            for y in range(amplen):
                ind = []
                dep = []
                ind.append(frequency[x])
                ind.append(frequency[x])
                below = result[x][y] - stdError[x][y]
                above = result[x][y] + stdError[x][y]
                dep.append(below)
                dep.append(above)
                adjust = pg.mkPen(0.5)
                if kind == "mag":
                    self.avgMag_Plot.plot(ind, dep, pen=adjust)
                elif kind == "gain":
                    self.avgGain_Plot.plot(ind, dep, pen=adjust)
                elif kind == "phase":
                    self.avgPhase_Plot.plot(ind, dep, pen=adjust)
    
    #Incomplete, need to fix the mapping of points from graph to the scene to compare against the mouse position, or vice versa
    #Determines the position of the mouse when pressed in the widget to determine position, and find closest point to it from the graph
    def mouseCFCalculation(self, QMouseEvent):
        #Get mouse position
        x = QMouseEvent.x()
        y = QMouseEvent.y()
        
        #Get current data set
        setName = self.dataSet_comboBox.currentText()
        dataSet = self.dataSetNameDict[setName]
        audioParams = dataSet.audioParams
        magResp = dataSet.magResp
        freq = audioParams.freq[0, :]
        amp = audioParams.amp
        
        #Unwrapping the phase data along the frequency axis
        phase = dataSet.phaseResp
        self.phasePlot.clear()     
        unWrapThreshold = np.pi
        phase = np.unwrap(phase, discont=unWrapThreshold, axis=0)
        
        #If threshold/noise floor is set, finds the NaNs in the magResp and applies to phase as well
        magResp, phase = self.findNaNs(magResp, phase, freq, amp, setName)

        distance = 10000
        index = 0
        cf = 0.0        
        
        for i in range(len(freq)):
            if np.isnan(magResp[i][0]) == False:
                pt = QPoint(freq[i], magResp[i][0])
                updated_pt = self.magPlot.mapToScene(pt)
                check_x = updated_pt.x()
                check_y = updated_pt.y()
                dist1 = x - check_x
                dist2 = y - check_y
                dist = math.sqrt(math.pow(dist1, 2) + math.pow(dist2, 2))
                print("updatedx: ", check_x)
                print("updatedy: ", check_y)
                if dist < distance: 
                    cf = magResp[i][0]
                    index = freq[i]
                    distance = dist
        
        print("x: ", x)
        print("y: ", y)
        print("Mouse called")        
        print("cf: ", cf)
        self.CF_lineEdit.setText(str(cf))
        self.calculateQ10db(magResp, freq, amp, cf, index)
    
    #Calculates the Characteristic Frequency of the lowest stimulus, 10dB
    def calculateCF(self, magResp, freq, amp, setName):
        cf = 0.0
        #Finds the x-coordinate of the CF
        index = 0
        #Keeps track of whether the mouse is dead or alive
        result = ""
        
        #Determine from the data set name if the mouse is live or dead
        lowerCase = setName.lower()
        if lowerCase.find("live") != -1:
            result = "live"
        elif lowerCase.find("dead") != -1:
            result = "dead"
        else:
            if setName in self.mouseStatus:
                result = self.mouseStatus[setName]
            else:
                #QWidget is the base class of all user interfaces objects in PyQt4
                w = QWidget()
                #Creates a question message box to ask the state of the mouse
                msg = QMessageBox.question(w, "Mouse Status", "Is this a live mouse?", QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
                if msg == QMessageBox.Yes:
                    result = "live"
                else:
                    result = "dead"
                self.mouseStatus[setName] = result
        #Determine the CF
        if result == "live":
            for i in range(len(freq)):
                #Ensures that the CF found should not be noise for live mouse
                if np.isnan(magResp[i][0]) == False and magResp[i][0] > cf and i > ((len(freq) / 2) + 2) and i < len(freq) - 1:
                    cf = magResp[i][0]
                    index = freq[i]
        elif result == "dead":
            for i in range(len(freq)):
                #Filters out the noise for CF of dead mouse
                if np.isnan(magResp[i][0]) == False and magResp[i][0] > cf and i < ((len(freq) / 2) + 2) and i > 0:
                    cf = magResp[i][0]
                    index = freq[i]
                  
        self.CF_lineEdit.setText(str(cf))
        self.calculateQ10db(magResp, freq, amp, cf, index)

        
    #Calculates the Q10dB of the 10dB curve, set to 0.0 by default and N/A Q10dB can't be calculated
    def calculateQ10db(self, magResp, freq, amp, cf, index):
        #Determine the shift for 10dB
        shift = cf / math.pow(10, 0.5)      
        
        #CF subtracted by 10dB
        limit = cf - shift
        y = []
        
        #Get the data points for the 10dB curve
        for i in range(len(freq)):
            y.append(magResp[i][0])
        
        #Use interpolation to deal with NaNs first before calculating Q10dB
        modify = np.array(y)
        not_nan = np.logical_not(np.isnan(modify))
        indices = np.arange(len(modify))

        #Interpolate for the NaNs that occur, so Q10dB can be calculated        
        interp = np.interp(indices, indices[not_nan], modify[not_nan])        
        changed = interp[indices]

        f = interpolate.UnivariateSpline(freq, changed, s=0)
        
        yreduced = np.array(changed) - limit
        freduced = interpolate.UnivariateSpline(freq, yreduced, s=0)
        
        #Calculates the roots of intersection between the curve and the horizontal line y = limit
        Q = freduced.roots()
        
        #Finds the closest two roots to to CF calculate bandwidth, protect against when there are multiple roots that cross the y = limit line
        if len(Q) > 2:
            less = 0
            more = freq[len(freq) - 1]
            for num in Q:
                if num >= less and num < index:
                    less = num
                if num <= more and num > index:
                    more = num
            
            bandwidth = more - less
            #Calculates Q10dB
            result = cf / bandwidth
            rounded = round(result, 4)
            self.Q10db_lineEdit.setText(str(rounded))
            
            #Graphs the Q10Db, in a dotted red line
            x = []
            x.append(less)
            x.append(more)
            z = []
            z.append(limit)
            z.append(limit)
            pen = pg.mkPen('r', width=1, style=QtCore.Qt.DashLine)
            self.magPlot.plot(x, z, pen=pen)
        
        elif len(Q) == 2:
            #Case when there are exactly 2 roots
            bandwidth = Q[1] - Q[0]
            result = cf / bandwidth
            rounded = round(result, 4)
            self.Q10db_lineEdit.setText(str(rounded))
            
            #Graphs the Q10Db, in a dotted red line
            x = []
            x.append(Q[len(Q) - 1])
            x.append(Q[len(Q) - 2])
            z = []
            z.append(limit)
            z.append(limit)
            pen = pg.mkPen('r', width=1, style=QtCore.Qt.DashLine)
            self.magPlot.plot(x, z, pen=pen)
        else:
            self.Q10db_lineEdit.setText("N/A")
    
    #Exports the magnitude response, shifted phase, and gain of every data set to Excel. Also exports the averages and standard errors in a separate workbook in Excel
    def exportToExcel(self):
        #Iterate through to each data set
        for data in self.dataSetNameDict:
            filename = data + ".xlsx"
            #Create a new Excel file 
            workbook = xlsxwriter.Workbook(filename)
            #Write the magnitude response to Excel
            self.magRespToExcel(self.dataSetNameDict[data], workbook, data)
            #Close the workbook after done writing to it
            workbook.close()
        
        #Ask user for average Excel file name when exported
        text, ok = QInputDialog.getText(self, 'Project Average Excel File Name', 'Name of Average Excel File: ')
        if ok:
            filename = str(text)
            #Write the averages of the data sets to new workbook in Excel
            self.avgToExcelPrep(filename)
    
    #Writes the Magnitude Response of a data set to Excel
    def magRespToExcel(self, dataSet, workbook, setName):
        #Add a worksheet
        worksheet = workbook.add_worksheet('Mag')
        #Get the Magnitude Response from data set
        audioParams = dataSet.audioParams
        magResp = dataSet.magResp
        freq = audioParams.freq[0, :]
        amp = audioParams.amp
        
        #Get the phase of data set
        phase = dataSet.phaseResp    
        unWrapThreshold = np.pi
        phase = np.unwrap(phase, discont=unWrapThreshold, axis=0)
        
        magResp, phase = self.findNaNs(magResp, phase, freq, amp, setName)
        
        worksheet.write('A1', 'Stim Mag Resp')
        for i in range(len(freq)):
            worksheet.write(i+2, 0, freq[i])
        for j in range(len(amp)):
            worksheet.write(1, j+1, amp[j])
        for k in range(len(freq)):
            for z in range(len(amp)):
                if np.isnan(magResp[k][z]) == False:
                    worksheet.write(k+2, z+1, magResp[k][z])
        
       
        #Write the shifted phase to Excel
        self.phaseShiftToExcel(magResp, phase, workbook, freq, amp)
        #Write the gain to Excel
        self.gainToExcel(magResp, workbook, freq, amp)
    
    #Writes the Phase Unwrapped and shifted of data set to Excel
    def phaseShiftToExcel(self, magResp, phase, workbook, freq, amp):
        #Add a worksheet
        worksheet = workbook.add_worksheet('Phase')
        #Phase shifting
        phase = self.phaseShift(magResp, phase, freq, amp)
        
        worksheet.write('A1', 'Phase Resp Unwrapped and Shifted')
        for i in range(len(freq)):
            worksheet.write(i+2, 0, freq[i])
        for j in range(len(amp)):
            worksheet.write(1, j+1, amp[j])
        for k in range(len(freq)):
            for z in range(len(amp)):
                if np.isnan(phase[k][z]) == False:
                    worksheet.write(k+2, z+1, phase[k][z])
    
    #Writes the Gain of data set to Excel
    def gainToExcel(self, magResp, workbook, freq, amp):
        #Add a worksheet
        worksheet = workbook.add_worksheet('Gain')
        
        #Get the gain of data set
        gain = self.calculateGain(magResp, freq, amp)
        
        worksheet.write('A1', 'Gain')
        for i in range(len(freq)):
            worksheet.write(i+2, 0, freq[i])
        for j in range(len(amp)):
            worksheet.write(1, j+1, amp[j])
        for k in range(len(freq)):
            for z in range(len(amp)):
                if np.isnan(gain[k][z]) == False:
                    worksheet.write(k+2, z+1, gain[k][z])
                    
    #Prepare the data sets to be averaged together based on combos for exporting to Excel
    def avgToExcelPrep(self, filename):
        excelAvg = {}
        curText1 = self.categories
        curText2 = self.categories
        for i in range(len(curText1)):
            for j in range(i, len(curText2)):
                excelAvg.clear()
                cate1 = curText1[i]
                cate2 = curText2[j]
                for name in self.dataSetNameDict:
                    check = True
                    #Case insensitive by turning the strings to lower-case first
                    temp = name.lower()
                    text1 = cate1.lower()
                    text2 = cate2.lower()
                    if (temp.find(text1) == -1) or (temp.find(text2) == -1) or (text1 == text2):
                        #Filter out unwanted data sets for average combinations                        
                        check = False
                    if (text1 == "" and text2 == "" and text1 == text2):
                        #Keeps the case where both categories are "", so averages all data sets
                        check = True
                    if check == True:
                        excelAvg[name] = self.dataSetNameDict[name]
                
                #Create a new workbook for a new set of averages, if there are data sets in the category combination
                if bool(excelAvg) == True:
                    n = ""
                    n = filename + "_" + cate1 + "_" + cate2 + "_Average.xlsx"
                    avgWorkbook = xlsxwriter.Workbook(n)
                    self.avgToExcel(avgWorkbook, excelAvg)
                    #Close the workbook
                    avgWorkbook.close()
        
    #Calculates the average magnitude, shifted phase, gain, and standard errors
    def avgToExcel(self, workbook, excelAvg):    
        frequency = []
        amplitude = []
        freqlen = 0
        amplen = 0
        
        #A 2D array where each element holds a list for all the data points of that respective position
        allArraysMag = defaultdict(lambda : defaultdict(list))
        allArraysPhase = defaultdict(lambda : defaultdict(list))
        allArraysPhaseError = defaultdict(lambda : defaultdict(list))
        allArraysMagError = defaultdict(lambda : defaultdict(list))
        allArraysGain = defaultdict(lambda : defaultdict(list))
        allArraysGainError = defaultdict(lambda : defaultdict(list))
        
        #Iterate through the data sets in the avgData dictionary, also unwrapping phase
        for d in excelAvg:
            dataSet = excelAvg[d]
            audioParams = dataSet.audioParams
            magResp = dataSet.magResp
            phase = dataSet.phaseResp     
            unWrapThreshold = np.pi
            phase = np.unwrap(phase, discont=unWrapThreshold, axis=0)
            freq = audioParams.freq[0, :]
            amp = audioParams.amp
            frequency = freq
            amplitude = amp
            freqlen = len(freq)
            amplen = len(amp)
            
            #Calculate the gain
            gain = self.calculateGain(magResp, freq, amp)
            #Phase shift the phase first before averaging
            phase = self.phaseShift(magResp, phase, freq, amp)
            #Set the threshold/noise floor
            thres = self.threshold[d]
            
            #Adds each data point from each data set to its corresponding list
            #Need the error list because the stats.sem 0.16.1 version can't handle NaNs 
            for i in range(len(freq)):
                for j in range(len(amp)):
                    if magResp[i][j] >= thres:
                        allArraysMag[i][j].append(magResp[i][j])
                        allArraysPhase[i][j].append(phase[i][j])
                        allArraysGain[i][j].append(gain[i][j])
                        if np.isnan(phase[i][j]) == False:
                            allArraysPhaseError[i][j].append(phase[i][j])
                        if np.isnan(magResp[i][j]) == False:
                            allArraysMagError[i][j].append(magResp[i][j])
                        if np.isnan(gain[i][j]) == False:
                            allArraysGainError[i][j].append(gain[i][j])
                    else:
                        allArraysMag[i][j].append(np.NaN)
                        allArraysPhase[i][j].append(np.NaN)
                        allArraysGain[i][j].append(np.NaN)
        
        #Hold the resulting averages of each point
        resultMag = np.zeros((freqlen, amplen))
        resultMag[:, :] = np.NaN
        resultPhase = np.zeros((freqlen, amplen))
        resultPhase[:, :] = np.NaN
        resultGain = np.zeros((freqlen, amplen))
        resultGain[:, :] = np.NaN
        
        #Hold the standard errors of mean for each data point
        stdErrorMag = np.zeros((freqlen, amplen))
        stdErrorMag[:, :] = np.NaN
        stdErrorGain = np.zeros((freqlen, amplen))
        stdErrorGain[:, :] = np.NaN
        stdErrorPhase = np.zeros((freqlen, amplen))
        stdErrorPhase[:, :] = np.NaN
        
        #Average each list in the 2D array, to find the average for that corresponding point
        for k in range(freqlen):
            for z in range(amplen):
                resultMag[k][z] = np.nanmean(allArraysMag[k][z])
                resultPhase[k][z] = np.nanmean(allArraysPhase[k][z])
                resultGain[k][z] = np.nanmean(allArraysGain[k][z])
                stdErrorMag[k][z] = stats.sem(allArraysMagError[k][z], ddof=0)
                stdErrorGain[k][z] = stats.sem(allArraysGainError[k][z], ddof=0)
                stdErrorPhase[k][z] = stats.sem(allArraysPhaseError[k][z], ddof=0)
                
        #Iterate through all average calculations to be exported to Excel
        for i in range(6):
            title = ""
            first = ""
            result = np.zeros((freqlen, amplen))
            result[:, :] = np.NaN
            if i == 0:
                title = 'Avg Mag'
                first = 'Average Stim Mag Resp'
                result = resultMag
            elif i == 1:
                title = 'Avg Phase'
                first = 'Average Phase Resp Unwrapped and Shifted'
                result = resultPhase
            elif i == 2:
                title = 'Avg Gain'
                first = 'Average Gain'
                result = resultGain
            elif i == 3:
                title = 'Std Error Mag'
                first = 'Standard Error Average Stim Mag Resp'
                result = stdErrorMag
            elif i == 4:
                title = 'Std Error Phase'
                first = 'Standard Error Average Phase Resp Unwrapped and Shifted'
                result = stdErrorPhase
            elif i == 5:
                title = 'Std Error Gain'
                first = 'Standard Error Average Gain'
                result = stdErrorGain
            self.avgArrayToExcel(result, frequency, amplitude, workbook, title, first)
                
    
    #Writes the average calcultion to Excel
    def avgArrayToExcel(self, result, freq, amp, workbook, title, first):
        #Add a worksheet
        worksheet = workbook.add_worksheet(title)
        
        worksheet.write('A1', first)
        for i in range(len(freq)):
            worksheet.write(i+2, 0, freq[i])
        for j in range(len(amp)):
            worksheet.write(1, j+1, amp[j])
        for k in range(len(freq)):
            for z in range(len(amp)):
                if np.isnan(result[k][z]) == False:
                    worksheet.write(k+2, z+1, result[k][z])
            
    #Detects when the chosen data set in the combo box changes. Will set to correct state of the exclude data checkbox and call plotDataSet
    def dataSetChanged(self):
        cur = self.dataSet_comboBox.currentText()
        if cur == "":
            self.magPlot.clear()
            self.phasePlot.clear()
            self.lineEdit.setText("0.0")
            
        if bool(self.dataSetNameDict) == True and cur != "":
            dataSet = self.dataSetNameDict[cur]
            if cur in self.avgData:
                self.excludeDataSet_checkBox.setChecked(False)
            else:
                self.excludeDataSet_checkBox.setChecked(True)
            num = self.threshold[cur]
            self.lineEdit.setText(str(num))
            self.plotDataSet(dataSet, cur)
    
    #Imports all immediate MScan data files    
    def addDataSets(self):
        caption = "Choose save directory"
        #directory = self.saveDir_lineEdit.text()
        path = '.'
        dataDir = QtGui.QFileDialog.getExistingDirectory (self, caption, path)
        # (dirpath, dirnames, filenames) = os.walk(top, topdown=True, onerror=None, followlinks=False)
        # product listing of all directories by list comprehension
        pathList = [os.path.join(dataDir,o) for o in os.listdir(dataDir) if os.path.isdir(os.path.join(dataDir,o))]       
        for d in pathList:
            try:
                # read in data set (which is of type MScan.MScanTuningCurve and audio parameters (OCTProtocolParams.AudioOutputParamters)
                dataSet, audioParams = MScan.readMscanDataTuningCurve(d)
                dataSet.audioParams = audioParams
                self.dataSets.append(dataSet)
                (head, setName) = os.path.split(d)
                
                
                self.dataSetNameDict[setName] = dataSet
                self.avgData[setName] = dataSet
                self.threshold[setName] = 0.0
                self.dataSet_comboBox.addItem(setName)
                print('Added %s' % d)
            except:
                traceback.print_exc()
                print('Could not read in data at %s' % d)
        
        #Plots the averages of magnitude and phase of all imported data
        self.averagePlot()
        
        #Sets the N number of data sets that create the average
        self.N_lineEdit.setText(str(len(self.dataSetNameDict)))

        # TODO: check that after we added data sets taht audio parameters are the same add act appropriate
        self.plotDataSet(self.dataSetNameDict[self.dataSet_comboBox.currentText()], self.dataSet_comboBox.currentText())
        
            
        
            
if __name__ == "__main__":
    #To prevent kernel from unexpectedly closing
    app=0  
    app = QtGui.QApplication(sys.argv)
    myWindow = PyVibAnalyzeWindowClass(None)
    myWindow.show()
    app.exec_()
            
