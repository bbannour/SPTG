# ==============================================================================
#                      Workflow Configuration Pure Python GUI
# ==============================================================================

from ipywidgets import RadioButtons, Checkbox, IntSlider, ToggleButtons, Button, Dropdown, Button, Tab, Text, Textarea, Label, Box, VBox, HBox, Output
from ipywidgets import interact, interactive, jslink, Layout
from IPython.display import display

from ..systemdefinition.system import System
from ..engine import Engine
from .configuration_tui import Configuration, ConfigurationError


class ConfigurationGui(object):
  """ This class produce a GUI though which a configuration is defined. 
  An analysis can be started  (an Engine is created)
  """
  
  def __init__(self, system):
    if not isinstance(system, System):
      raise ConfigurationError("system parameter is not an instance of System")
    else:
      self.system = system
      self.engine = None
      self.result = None
      self.configuration = Configuration()
      self.createGui()   
  
  def createGui(self):
#   out = Output(layout={'border': '1px solid red'})

    observableWidgets = []    

    # ===========================================================================
    # Top level Tabs Widget
    # ===========================================================================
    overviewTabBox       = self.__createOverviewTab(observableWidgets)
    supervisionTabBox    = self.__createSupervisionTabBox(observableWidgets)
    testGenerationTabBox = self.__createTestGenerationTabBox(observableWidgets)
    verbosityTabBox      = self.__createVerbosityTabBox(observableWidgets)
    genConfigTabBox      = self.__createGenConfigTabBox(observableWidgets)
    
    generalTabs_titles = ['Overview', 'Supervision', 'Test Generation', 'Verbosity', 'Generated Conf.']
    generalTabs_widgets = [overviewTabBox, supervisionTabBox, testGenerationTabBox, verbosityTabBox, genConfigTabBox]
    generalTabs = Tab(children=generalTabs_widgets, layout={'height': '400px'})
    for i in range(len(generalTabs_titles)):
      generalTabs.set_title(i, generalTabs_titles[i])
    
    
    # Update mechanism for texttual configuration 
    def updateGenConfigTextArea(change):
      # First children of genConfigTabBox is assumed to be the Textarea widget
      genConfigTabBox.children[0].value = str(self.configuration)   
         
    # Connecting all individual widget
    for w in observableWidgets: 
      w.observe(updateGenConfigTextArea, 'value')
    
    # Connecting the analysis type tab widget (the text config shall be update because strategy can change) 
    # Second children of overviewTabBox is assumed to be the analysis Tab widget
    overviewTabBox.children[1].observe(updateGenConfigTextArea)
       
    display(generalTabs)

    
    
  def __createOverviewTab(self, observableWidgets):

    # ===========================================================================
    #                              Overview Tab
    # ===========================================================================     
     
    # Analysis type
    analysisTypeRadioButtons = RadioButtons(options=list(self.configuration._analysisTypes), 
                                        description='Analysis:')
    interactive(self.configuration.setAnalysisType, analysis=analysisTypeRadioButtons)
    observableWidgets.append(analysisTypeRadioButtons)
    
    # Constraint Solver
    constraintSolverDropdown = Dropdown(options=self.configuration._solvers, 
                            value=self.configuration._solvers[0], 
                            description='Solver:', 
                            layout={"width":"200px"}
                            )
        
    interactive(self.configuration.setSolver, solver=constraintSolverDropdown)
    observableWidgets.append(constraintSolverDropdown)
   
    # Reset Button
    resetConfButton = Button(description='Restore Defaults',
                             button_style='', 
                             tooltip='Restore default Configuration', 
                             icon='fa-refresh', 
                             layout={"margin":"50px 0 0 50px"}
                             )
    
    resetConfButton.on_click(self.restoreDefaults)

    # startAnalysis
    startAnalysisButton = Button(description='Start',
                                 button_style='',
                                 tooltip='Start the selected analysis',
                                 icon='play-circle',
                                 layout={"margin":"20px 0 0 50px"}
                                 )
    
    startAnalysisButton.on_click(self.startAnalysis)

    
    
    # ======================= Subtab 1 : Exploration =======================

    # Strategy
    strategyRadioButtons = RadioButtons(options=list(self.configuration._strategies), 
                                        description='Strategy:', 
                                        layout={"width":"40%"})
    interactive(self.configuration.setStrategy, strategy=strategyRadioButtons)
    observableWidgets.append(strategyRadioButtons)
    
    # Redundancy detection
    redundancyRadioButtons = RadioButtons(options=list(self.configuration._redundancyDetectionMethods.values()), description='Redundancy detection:')
    interactive(self.configuration.setRedundancyDetectionMethod, method=redundancyRadioButtons)
    observableWidgets.append(redundancyRadioButtons)
    
    # Redundancy detection / General Loop Detection / Path Scope
    pathScopeDropdown = Dropdown(options=list(self.configuration._pathScopes), 
                            value=list(self.configuration._pathScopes)[0], 
                            description='Path Scope:', 
                            layout={"width":"90%"}
                            )
    interactive(self.configuration.setRedundancyDetectionPathScope, scope=pathScopeDropdown)
    observableWidgets.append(pathScopeDropdown)
    
    # Redundancy detection / General Loop Detection / Comparison Operator    
    comparisonOperatorDropdown = Dropdown(options=list(self.configuration._comparisonOperators), 
                            value=list(self.configuration._comparisonOperators)[0], 
                            description='Comparison operator:',
                            layout={"width":"90%"}
                            )
    interactive(self.configuration.setRedundancyDetectionComparisonOperator, operator=comparisonOperatorDropdown)
    observableWidgets.append(comparisonOperatorDropdown)
       
    # Gathering all widgets for simple layout    
    explorationTabBox = VBox([strategyRadioButtons, HBox([redundancyRadioButtons, VBox([pathScopeDropdown, comparisonOperatorDropdown])])]) 
    observableWidgets.append(explorationTabBox)
    
    # =================== Subtab 2 : Transition Coverage  ====================
    
    # WBFS Strategy
    wbfsStrategyRadioButtons = RadioButtons(options=["WBFS"], 
                                        description='Strategy:', 
                                        layout={"width":"40%"})
    interactive(self.configuration.setStrategy, strategy=wbfsStrategyRadioButtons)
    observableWidgets.append(wbfsStrategyRadioButtons)
    
    # Transition coverage scope
    transitionCoverageScopeRadioButtons = RadioButtons(options=list(self.configuration._transitionCoverageScopes), description='Scope:')
    interactive(self.configuration.setTransitionCoverageScope, scope=transitionCoverageScopeRadioButtons)
    observableWidgets.append(transitionCoverageScopeRadioButtons)
    
    transitionCoverageTabBox = VBox([wbfsStrategyRadioButtons, transitionCoverageScopeRadioButtons])
        
        
    # =================== Subtab 3 : Behavior Selection  =====================
    
    

    behaviorSelectionTabBox = Box()
    # =================== Subtab 4 : Trace Compliance  =======================    
    
    traceComplianceTabBox = Box()
    
    #  ======================= Overview Tabs Widget  =========================  
    overviewTabs_titles = ['Exploration', 'Transition Coverage', 'Behavior Selection', 'Trace Compliance']
    
    overviewTabs_widgets = [explorationTabBox, transitionCoverageTabBox, behaviorSelectionTabBox, traceComplianceTabBox]
    overviewTabs = Tab(children=overviewTabs_widgets, layout={'height': '300px', 'width':'60%'})
    for i in range(len(overviewTabs_titles)):
      overviewTabs.set_title(i, overviewTabs_titles[i])
    
    overviewTabBox = HBox([VBox([analysisTypeRadioButtons, constraintSolverDropdown, resetConfButton, startAnalysisButton]), overviewTabs])
    
    jslink((analysisTypeRadioButtons, "index"), (overviewTabs, "selected_index"))
        
          
    # Update mechanism for strategy (which is implicitly changed from a tab to another)
    def updateStrategy(change):
      if change["new"] == 0: # tab 0 is explorationTabBox
        self.configuration.setStrategy(strategyRadioButtons.value)

    
    overviewTabs.observe(updateStrategy, 'selected_index')
    
    return overviewTabBox
  
  
  def __createSupervisionTabBox(self, observableWidgets):
    # ===========================================================================
    #                              Supervision Tab
    # ===========================================================================    
    
    # Evaluation limits 
    evaluationLimitsLabel = Label(value='Evaluation limits')
    symbexStepSlider = IntSlider(min=-1, max=self.configuration._max_limits["symbexStep"], step=1, value=-1)
    symbexTimerSlider = IntSlider(min=-1, max=self.configuration._max_limits["symbexTimer"], step=1, value=-1)
    observableWidgets.append(symbexStepSlider)
    observableWidgets.append(symbexTimerSlider)
    
    interactive(self.configuration.setSymbexLimits, step = symbexStepSlider, timeout = symbexTimerSlider) 
   
    # Graph Size limits 
    graphSizeLimitsLabel = Label(value='Graph size limits')
    nodesSlider = IntSlider(min=-1, max=self.configuration._max_limits["graphNodes"], step=1, value=-1)
    widthSlider = IntSlider(min=-1, max=self.configuration._max_limits["graphWidth"], step=1, value=-1)
    heightSlider = IntSlider(min=-1, max=self.configuration._max_limits["graphHeight"], step=1, value=-1)
    observableWidgets.append(nodesSlider)
    observableWidgets.append(widthSlider)    
    observableWidgets.append(heightSlider)
    
    interactive(self.configuration.setGraphSizeLimits, node = nodesSlider, height = heightSlider, width = widthSlider) 

    
    supervisionTabBox = Box([VBox([evaluationLimitsLabel, symbexStepSlider, symbexTimerSlider]),
                             VBox([graphSizeLimitsLabel, nodesSlider, widthSlider, heightSlider])])
    
    return supervisionTabBox
 
  def __createTestGenerationTabBox(self, observableWidgets):
    # ===========================================================================
    #                              TestGeneration Tab
    # ===========================================================================
    testGenerationTabBox = Box()
    return testGenerationTabBox
    
    
  def __createVerbosityTabBox(self, observableWidgets):  
    # ===========================================================================
    #                              Verbosity Tab
    # ===========================================================================
    
    # Verbosity
    verbosityRadioButtons = RadioButtons(options=self.configuration._verbosity, 
                                        description='Verbosity:')
    interactive(self.configuration.setVerbosity, verb=verbosityRadioButtons)
    observableWidgets.append(verbosityRadioButtons)

    # Debug level
    debugLevelRadioButtons = RadioButtons(options=self.configuration._debugLevels, 
                                        description='Debug level:')
    interactive(self.configuration.setDebugLevel, level=debugLevelRadioButtons)
    observableWidgets.append(debugLevelRadioButtons)
    
    
    # Debug flags
    debugFlagsWidgets = []
    for f in self.configuration._debugFlags:
      debugFlagCheckBox = Checkbox(value=False, description=f)
      debugFlagsWidgets.append(debugFlagCheckBox)
      interactive(self.configuration.setDebugFlag, flag=f, active=debugFlagCheckBox)
    
    observableWidgets.extend(debugFlagsWidgets)
    
    verbosityTabBox = VBox([HBox([verbosityRadioButtons, debugLevelRadioButtons]), VBox(debugFlagsWidgets)])
    return verbosityTabBox

    
  def __createGenConfigTabBox(self, observableWidgets):
    # ===========================================================================
    #                              Generated Config. Tab
    # ===========================================================================  
    genConfigTextArea = Textarea(value=str(self.configuration), description='Config Code:', 
                                 layout={'height': '300px', 'width':'100%'})
    genConfigTabBox = Box([genConfigTextArea])
    return genConfigTabBox
  
  
  def startAnalysis(self, b):
    if self.engine : 
      print("Analysis already started")
    else:
      self.engine = Engine (self.configuration)
      self.engine.setSystem(self.system)    
      print("Analysis starting...")
      self.result = self.engine.start()
      print("Result: ", self.result)
      #self.engine = None # FIXME : => Kernel crash : we must have a proper way to destroy an engine
      # del(self.engine)
    
  def restoreDefaults(self, b):
    # TODO
    print("Not implemented yet")
    self.configuration.setDefaults()

    


