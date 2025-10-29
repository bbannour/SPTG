# ==============================================================================
#                      Workflow Configuration Pure Python API
# ==============================================================================


import os

from ..maatcore import *

class ConfigurationError(Exception):
  def __init__(self, msg):
    self.msg = str(msg)

  def __str__(self):
    return self.msg

 
  
class Configuration(Py_WorkflowParameter):

  _analysisTypes = {"exploration":"", "transition_coverage":"coverage#transition", 
                    "behavior_selection":"behavior#selection", "trace_compliance":"test#offline"}
  _strategies = {"BFS":"BREADTH_FIRST_SEARCH", 
                 "DFS":"DEPTH_FIRST_SEARCH",
                 "RFS":"RANDOM_FIRST_SEARCH", 
                 "ALL":"ALL"
                 }
  
  _redundancyDetectionMethods = {"None":None, "GLD":"General loop detection", "TLD":"loop#detection#trivial"}
  _pathScopes = ['CURRENT', 'ALL', 'PARENT']
  _comparisonOperators = ['Inclusion', 'Equality', 'Syntactic Equality']
  
  _transitionCoverageScopes = ["Model Transitions", "Instance Transitions"]
  
  _verbosity = ["SILENT", "MINIMUM", "MEDIUM", "MAXIMUM"]
  _debugFlags = ["PARSING", "CONFIGURING", "COMPILING", "LOADING", "COMPUTING", "PROCESSOR", "TRACE", "GOD_MODE"]
  _debugLevels = ["ZERO", "LOW", "MEDIUM", "HIGH", "ULTRA", "GOD_MODE"]
  _solvers = ["Z3", "CVC4"]
  _max_limits = {"symbexStep":500, "symbexTimer":1000, "graphNodes":500, "graphWidth":500, "graphHeight":500}

  
  def __init__(self):
    Py_WorkflowParameter.__init__(self)
    self.setDefaults()

  def setDefaults(self):
    # *** Workspace *** 
    self.analysisType = list(self._analysisTypes)[0]
    self.rootdir = "./"
    self.outdir = None
    self.launchdir = None
    self.logdir = None # FIXME Also in Developer section
    self.debugdir = None # FIXME Also in Developer section

    # *** Director exploration ***
    # ** Manifest **
    self.autoconf = True
    self.autostart = True
    # ** Project **
    self.source = "."
    self.model = None
    # ** Supervisor **
    # * Limit *
    self.symbexStep = 42
    self.symbexTimeout = -1
    self.symbexeval = None #1000
    self.node = None #-1
    self.height = None #-1
    self.width = None #-1
  # * Queue * 
    self.strategy = "BREADTH_FIRST_SEARCH"
    self.weight = 8
    # * Redundancy *
    self.redundancyDetectionMethod = None
    self.redundancyDetection = None
    self.pathScope = None
    self.comparisonOperator = None
    # TransitionCoverage
    self.transitionCoverageScope = None
    
    # * Console * 
    self.format = None
    self.report = None
    self.spiderInit = None
    self.spiderStep = None
    self.spiderStop = None
    # ** Worker **
    self.slice = None
    self.minimize = None
    self.heuristic = None
    self.scope = None
    self.scheduler = None
    self.traceFormat = None
    self.stepScheduler = None
    self.traceFolding = None
    self.traceFile = None
    # ** Output **
    self.outputFileName = None 
    self.specification = None
    self.executable = None
    self.initialization = None
    self.scenarii = None
    # ** Debug **
    self.parsing = None
    self.compilation = None
    self.execution = None
    
    # *** Symbex ***
    self.nameIdSeparator = None # "#"
    self.newfreshParamNamePid = None #False
    self.prettyPrinterVarName = True #False
    self.timeNameId = None #"$time"
    self.deltaNameId = None #"$delta"
    self.nodeConditionEnabled = None #False
    self.separationOfPcDisjunction = None #False
    self.checkPathconditionSatisfiability = True #True
    self.constraintSolver = "Z3"
   
    # *** Console ***
    self.verbosity = "SILENT"
    
    # *** Shell ***
    self.stop = None #"symbex.stop"

    # *** Developer ***
    self.logFilename = None # FIXME : Also in workspace section
    self.debugFilename = None # FIXME : Also in workspace section
    self.debugLevel = None
    self.activeDebugFlags = []
    # ** Developer flags **
    self.activedFlags = set()
   
     
  def __str__(self):
    """
    Return a formatted string with all the options and their selected values
    """
    return self.__workflowStr()

  def __workflowStr(self):
    depth = 0
    return "workflow {{\n{workspace}{directorexpl}{symbex}{console}{shell}{developer}}}\n".format(
                                                   workspace=self.__workspaceStr(depth),
                                                   directorexpl=self.__directorStr(depth),
                                                   symbex=self.__symbexStr(depth),
                                                   console=self.__consoleStr(depth), 
                                                   shell=self.__shellStr(depth),
                                                   developer=self.__developerStr(depth)
                                                   )                     
  # *** Workspace ***                                                 
  def __workspaceStr(self, depth):
    depth += 1
    return "{shift1}workspace [\n{rootdir}{launchdir}{outdir}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      rootdir=self.__keyValStr("root", self.rootdir, depth=depth, doublequoted=True),
      launchdir=self.__keyValStr("launch", self.launchdir, depth=depth, doublequoted=True),
      outdir=self.__keyValStr("output", self.outdir, depth=depth, doublequoted=True),
      shift2 = self.__shiftStr(depth)
      )
                                                   
  # *** Director  ***
  def __directorStr(self, depth):
    depth += 1
    return "{shift1}director {analysis} {{\n{manifest}{project}{supervisor}{worker}{shift2}}}\n".format(
      shift1 = self.__shiftStr(depth),
      analysis = str(self.__analysisTypeStr()),
      manifest = self.__manifestStr(depth), 
      project = self.__projectStr(depth),
      supervisor = self.__supervisorStr(depth),
      worker = self.__workerStr(depth), 
      shift2 = self.__shiftStr(depth)
      )
      
    
  def __analysisTypeStr(self):
    return self._analysisTypes[self.analysisType]

  def __manifestStr(self,depth):
    depth += 1
    return "{shift1}manifest [\n{aconf}{astart}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      aconf = self.__keyValStr("autoconf", self.autoconf, depth=depth, lower=True),
      astart = self.__keyValStr("autostart", self.autostart, depth=depth, lower=True),
      shift2 = self.__shiftStr(depth))
      
    
  def __projectStr(self, depth):
    depth += 1
    return "{shift1}project [\n{source}{model}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      source = self.__keyValStr("source", self.source,  depth=depth, doublequoted=True),
      model = self.__keyValStr("model", self.model,  depth=depth, doublequoted=True),
      shift2 = self.__shiftStr(depth) 
      )

#   def __supervisorStr(self):
#     return "supervisor {{\n{limit}{queue}{redund}{console}}}\n".format(limit=self.__explorationLimitStr(), 
#                               queue=self.__queueStr(), 
#                               redund=self.__redundancyStr(),
#                               console=self.__supervisorConsoleStr()
#                               )
  def __supervisorStr(self, depth):
    depth += 1
    return "{shift1}supervisor {{\n{limit}{queue}{redundancy}{shift2}}}\n".format(
      shift1 = self.__shiftStr(depth),
      limit = self.__explorationLimitStr(depth), 
      queue = self.__queueStr(depth), 
      redundancy = self.__redundancyStr(depth), 
      console = self.__supervisorConsoleStr(depth),
      shift2 = self.__shiftStr(depth),
      )
  
  def __explorationLimitStr(self, depth):
    depth += 1
    return "{shift1}limit [\n{step}{eval}{node}{height}{width}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      step=self.__keyValStr("step", self.symbexStep, depth=depth),
      eval=self.__keyValStr("eval", self.symbexeval, depth=depth), 
      node=self.__keyValStr("node", self.node, depth=depth), 
      height=self.__keyValStr("height", self.height, depth=depth),
      width=self.__keyValStr("width", self.width, depth=depth),
      shift2 = self.__shiftStr(depth),
      )
    
  def __queueStr(self, depth):
    # TODO : do the choice properly, at the leaf debugLevel
    depth += 1
    if self.strategy == "WEIGHT_BREADTH_FIRST_SEARCH":
        return "{shift1}queue [\n{strat}{weight}{shift2}]\n".format(
          shift1 = self.__shiftStr(depth),
          strat = self.__keyValStr("strategy", self.strategy, depth=depth, quoted=True),
          weight = self.__weightStr(depth),
          shift2 = self.__shiftStr(depth),
          )
    else:
        return "{shift1}queue [\n{strat}{shift2}]\n".format(
          shift1 = self.__shiftStr(depth),
          strat = self.__keyValStr("strategy", self.strategy, depth=depth, quoted=True), 
          shift2 = self.__shiftStr(depth),
          )
   
   
  def __weightStr(self, depth):

     return "{weight}".format(weight=self.__keyValStr("weight", self.weight, depth=depth))
   
#   def __heuristicFlagStr(self, depth):
# 
#      return "{heurflag}".format(heurflag=self.__keyValStr("heuristic", self.__heuristicFlag, depth=depth))   
# #   def __redundancyStr(self):
# #     return "redundancy [\n{ldt}]\n".format(ldt=self.__keyValStr("loop#detection#trivial", self.loopDetectionTrivial, lower=True))
# #

 
  def __redundancyStr(self, depth):
    # TODO : do the choice properly, at the leaf debugLevel
    depth += 1
    if self.redundancyDetectionMethod == self._redundancyDetectionMethods["TLD"]:
        return "{shift1}redundancy [\n{TLD}{shift2}]\n".format(
          shift1 = self.__shiftStr(depth),
          TLD = self.__keyValStr("loop#detection#trivial", True, depth=depth, lower=True), 
          shift2 = self.__shiftStr(depth),
          )
    else:
        return "{shift1}redundancy [\n{TLD}{shift2}]\n".format(
          shift1 = self.__shiftStr(depth),
          TLD = self.__keyValStr("loop#detection#trivial", False, depth=depth, lower=True), 
          shift2 = self.__shiftStr(depth),
          )
      

  def __supervisorConsoleStr(self, depth):
    return "{shift1}console [\n{format}{report}{spinit}{spstep}{spstop}{shift2}]\n".format(  format=self.__keyValStr("format", self.format, doublequoted=True),
                                          shift1 = self.__shiftStr(depth),
                                          report=self.__keyValStr("report", self.report, depth=depth, doublequoted=True),
                                          spinit=self.__keyValStr("spider#init", self.spiderInit, depth=depth, doublequoted=True),
                                          spstep=self.__keyValStr("spider#step", self.spiderStep, depth=depth, doublequoted=True),
                                          spstop=self.__keyValStr("spider#stop", self.spiderStop, depth=depth, doublequoted=True), 
                                          shift2 = self.__shiftStr(depth),
                                          )
  
  def __workerStr(self, depth):
    depth += 1
    return "{shift1}worker [\n{analysisbloc}{shift2}]\n".format(
          shift1 = self.__shiftStr(depth),
          analysisbloc = self.__analysisBlocStr(depth),
          shift2 = self.__shiftStr(depth)
          )

    
  def __analysisBlocStr(self, depth):
    if self._analysisTypes[self.analysisType] == "":
      return ""
    else:
      depth += 1
      return "{shift1}{analysis} {{\n{property}{tracebloc}{heuristicbloc}{console}{shift2}}}\n".format(
            shift1 = self.__shiftStr(depth),
            analysis=str(self._analysisTypes[self.analysisType]),
            property=self.__propertyStr(depth),
            tracebloc = self.__traceBlocStr(depth),
            heuristicbloc=self.__heuristicBlocStr(depth),
            console= self.__analysisBlocConsoleStr(depth),
            shift2 = self.__shiftStr(depth) 
        )
    
  def __propertyStr(self, depth):
    depth += 1
    return "{shift1}property [\n{stop}{slice}{minimize}{heuristic}{scope}{scheduler}{traceformat}{stepscheduler}{tracefolding}{shift2}]\n".format(
          shift1 = self.__shiftStr(depth),
          stop=self.__stopStr(depth),
          slice=self.__sliceStr(depth),
          minimize=self.__minimizeStr(depth),
          heuristic=self.__heuristicStr(depth),
          scope=self.__scopeStr(depth),
          scheduler=self.__schedulerStr(depth),
          traceformat=self.__traceFormatStr(depth),
          stepscheduler=self.__stepSchedulerStr(depth),
          tracefolding=self.__traceFoldingStr(depth),
          shift2 = self.__shiftStr(depth)
          )
    
    
  def __traceBlocStr(self, depth):
    depth += 1
    return "{shift1}merged_trace [\n{tracefile}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      tracefile = "{}".format(self.__keyValStr("mergedTraceFile", self.traceFile, depth=depth, doublequoted=True)),
      shift2 = self.__shiftStr(depth)
      )
    
  def __analysisBlocConsoleStr(self, depth):
    # TODO : complete
    depth += 1
    return "{shift1}console [\n{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      shift2 = self.__shiftStr(depth)
      )
    
  def __stopStr(self, depth):
    depth += 1
    if self.analysisType == "transition_coverage" or self.analysisType == "behavior_selection":
      return "{shift}stop = true\n".format(shift=self.__shiftStr(depth))
    else:
      return ""
    
  def __sliceStr(self, depth):
    if self.analysisType == "transition_coverage" or self.analysisType == "behavior_selection":
      return "{}".format(self.__keyValStr("slice", self.slice, depth=depth, lower=True))
    else:
      return ""
    
  def __minimizeStr(self, depth):
    if self.analysisType == "transition_coverage":
      return "{}".format(self.__keyValStr("minimize", self.minimize, depth=depth, lower=True))
    else:
      return ""
    
  def __heuristicStr(self, depth):
    if self.analysisType == "transition_coverage":
      return "{}".format(self.__keyValStr("heuristic", self.heuristic, depth=depth, lower=True))
    else:
      return ""
    
  def __scopeStr(self, depth):
    if self.analysisType == "transition_coverage" or self.analysisType == "behavior_selection":
      return "{}".format(self.__keyValStr("scope", self.scope, depth=depth, quoted=True))
    else:
      return ""
    
  def __schedulerStr(self, depth):
    if self.analysisType == "behavior_selection":
      return "{}".format(self.__keyValStr("scheduler", self.scheduler, depth=depth, quoted=True))
    else:
      return ""
    
  def __traceFormatStr(self, depth):
    if self.analysisType == "trace_compliance":
      return "{}".format(self.__keyValStr("format", self.traceFormat, depth=depth, quoted=True))
    else:
      return ""
    
  def __stepSchedulerStr(self, depth):
    if self.analysisType == "trace_compliance":
      return "{}".format(self.__keyValStr("step#scheduler", self.stepScheduler, depth=depth, quoted=True))
    else:
      return ""
    
  def __traceFoldingStr(self, depth):
    if self.analysisType == "trace_compliance":
      return "{}".format(self.__keyValStr("trace#folding", self.traceFolding, depth=depth, lower=True))
    else:
      return ""    
    
    
  def __heuristicBlocStr(self, depth):
    return ""
     
    """worker [\n coverage#transition transition_coverage {{\n property [
    stop  = true
    {slice}
    minimize  = true
    heuristic = true
    scope = 'MODEL'
    ]
    heuristic [ /* vide pour l'instant */]
    console [/* vide pour l'instant */] 
    }}]
    """
    
    """worker [\n coverage#behavior {{ 
    property [
    stop = true
    {slice} (=True*/False)
    {scope} (=GLOBALLY*/ LOCALLY)
    {scheduler} (= "ordered"* / "unordered")  
    ]
    heuristic [/* vide pour l'instant */]
    console [/* vide pour l'instant */]
    
    }}]
    """

    
    """worker [\n test#offline {{ 
    property [
    {format} = 'BASIC#XLIA'*
    {step#scheduler}  (= "ordered"* / "unordered")
    {trace#folding} (= true*/false)
    ]
    merged_trace [ traceFile = "clientfilepath" ]
    observable [ port1 port2 ... ] ou [*]
    controllable [*] (FIXE)
    }}]
    """
    
  def __outputStr(self, depth):
    depth += 1
    return "{shift1}console [\n{filename}{spec}{execut}{init}{scenarii}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      filename = self.__keyValStr("filename", self.outputFileName, depth=depth),
      spec = self.__keyValStr("specification", self.specification, depth=depth),
      execut = self.__keyValStr("executable", self.executable, depth=depth),
      init = self.__keyValStr("initialization", self.initialization, depth=depth),
      scenarii = self.__keyValStr("scenarii", self.scenarii, depth=depth),
      shift2 = self.__shiftStr(depth),
      )
 
  def __debugFilenameStr(self, depth):
    depth += 1
    return "{shift1}debug [\n{filename}{parsing}{compilation}{execution}]\n".format( filename=self.__keyValStr("filename", self.debugFileName),
      shift1 = self.__shiftStr(depth),
      spec = self.__keyValStr("parsing", self.parsing, depth=depth),
      execut = self.__keyValStr("compilation", self.compilation, depth=depth),
      init = self.__keyValStr("execution", self.execution, depth=depth),
      shift2 = self.__shiftStr(depth),
      )
    
  def __symbexStr(self, depth):
    depth += 1
    return "{shift1}symbex [\n{sep}{parampid}{prettyprint}{timeid}{deltaid}{nodecond}{sepofdisj}{checksatis}{solver}{shift2}]\n".format(
        shift1 = self.__shiftStr(depth),
        sep = self.__keyValStr("name_id_separator", self.nameIdSeparator, depth=depth, doublequoted=True),
        parampid = self.__keyValStr("newfresh_param_name_pid", self.newfreshParamNamePid, depth=depth, lower=True),
        prettyprint = self.__keyValStr("pretty_printer_var_name", self.prettyPrinterVarName, depth=depth, lower=True),
        timeid = self.__keyValStr("time_name_id", self.timeNameId, depth=depth, quoted=True),
        deltaid = self.__keyValStr("delta_name_id", self.deltaNameId, depth=depth, quoted=True),
        nodecond = self.__keyValStr("node_condition_enabled", self.nodeConditionEnabled, depth=depth, lower=True),
        sepofdisj = self.__keyValStr("separation_of_pc_disjunction", self.separationOfPcDisjunction, depth=depth, lower=True),
        checksatis = self.__keyValStr("check_pathcondition_satisfiability", self.checkPathconditionSatisfiability, depth=depth, lower=True),
        solver = self.__keyValStr("constraint_solver", self.constraintSolver, depth=depth, quoted=True),
        shift2 = self.__shiftStr(depth),
        )
    
  def __consoleStr(self, depth):
    depth += 1
    return "{shift1}console [\n{verb}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      verb = self.__keyValStr("verbose", self.verbosity, depth=depth, quoted=True),
      shift2 = self.__shiftStr(depth)
      )
   
  def __shellStr(self, depth):
    depth += 1
    return ""

  def __developerStr(self, depth):
    depth += 1
    return "{shift1}developer [\n{log}{debugfilename}{debuglevel}{flags}{shift2}]\n".format(
      shift1 = self.__shiftStr(depth),
      log = self.__logFilenameStr(depth),
      debugfilename = self.__debugFilenameStr(depth),
      debuglevel = self.__debugLevelStr(depth), 
      flags = self.__flagsStr(depth),
      shift2 = self.__shiftStr(depth),
      )
  
  def __logFilenameStr(self, depth):
    return  self.__keyValStr("log", self.logFilename, depth=depth, doublequoted=True)
  
  def __debugFilenameStr(self, depth):
    return  self.__keyValStr("debug", self.debugFilename, depth=depth, doublequoted=True)
  
  def __debugLevelStr(self, depth):
    return  self.__keyValStr("level", self.debugLevel, depth=depth, quoted=True)
  
  def __flagsStr(self, depth):
    txt = ""
    for f in self.activeDebugFlags: 
      txt +=  self.__keyValStr("flag", f, depth=depth, quoted=True)
    txt += "\n"
    return txt[:-1]
    
  def __keyValStr(self, keyword, value, depth=0, quoted=False, doublequoted=False, lower=False):
    if value is None:
      return ""
    try:
      value = str(value)
    except:
      raise ConfigurationError("String conversion failed")
    else:
      if lower:
        value = value.lower()
    if quoted and doublequoted:
      raise ConfigurationError("Internal inconsistency: double quote and single quote options simultaneously true")
    if quoted:
       return "{shift}{key} = '{val}'\n".format(shift=self.__shiftStr(depth+1), key=keyword, val=str(value))
    elif doublequoted:
       return '{shift}{key} = "{val}"\n'.format(shift=self.__shiftStr(depth+1), key=keyword, val=str(value))  
    else:
      return "{shift}{key} = {val}\n".format(shift=self.__shiftStr(depth+1), key=keyword, val=str(value))
    
  def __shiftStr(self, depth):
    return " " * 8 * depth
    
  def setWorkspace(self, rootdir="./", launchdir="./", outdir="./", logdir="./", debugdir="./"):
    self.rootdir = rootdir
    self.launchdir = launchdir
    self.outdir = outdir
    self.logdir = logdir
    self.debugdir = debugdir
        
  def setAnalysisType(self, analysis, slice=True):
    """Options whose value depends on the analysis type should bet set here"""
    if not analysis in list(self._analysisTypes):
       raise ConfigurationError("Unknown analysis type {}".format(analysis))
    else:
      self.analysisType = analysis
      self.slice = slice;
      if self.analysisType == "exploration":
        if self.strategy is None: 
          self.strategy = "BREADTH_FIRST_SEARCH"
      elif self.analysisType == "transition_coverage":
        self.strategy = "WEIGHT_BREADTH_FIRST_SEARCH"
        self.minimize = True
        self.heuristic = True
        self.scope = "MODEL"
      elif self.analysisType == "behavior_selection":
        if self.strategy is None: 
          self.strategy = "WEIGHT_BREADTH_FIRST_SEARCH"
        self.slice = True
        self.scope = "GLOBALLY"
        self.scheduler = "ordered"
      elif self.analysisType == "trace_compliance":
        if self.strategy is None: 
          self.strategy = "WEIGHT_BREADTH_FIRST_SEARCH"
        self.traceFormat = "BASIC#XLIA"
        self.stepScheduler = "ordered"
        self.traceFolding = True
        self.slice = True;
      else:
        pass
        
  def setManifest(self, autoconf=True, autostart=True):
    self.autoconf = autoconf
    self.autostart = autostart
    
  def setModel(self, model, source="."):
    self.source = source
    self.model = model
    
#   def setLimits(self, step=42, eval=-1, node=-1, height=-1, width=-1):
#     try:
#       self.symbexStep = int(step)
#     except (TypeError, ValueError):
#       raise ConfigurationError("Symbolic analysis 'step' must be an integer")
#     try:
#       self.symbexeval = int(eval) # 1000
#     except (TypeError, ValueError):
#       raise ConfigurationError("Symbolic execution 'eval' must be an integer")
#     self.node = node #-1
#     try:
#       self.height = int(height) #-1
#     except (TypeError, ValueError):
#       raise ConfigurationError("Symbolic execution 'height' must be an integer")
#     try:
#       self.width = int(width) #-1
#     except (TypeError, ValueError):
#       raise ConfigurationError("Symbolic execution 'width' must be an integer")
    
    
    
  def setSymbexLimits(self, step=42, timeout=-1):
    try:
      self.symbexStep = int(step)
    except (TypeError, ValueError):
      raise ConfigurationError("Symbolic execution 'step' must be an integer")
    try:
      self.symbexTimeout = int(timeout)
    except (TypeError, ValueError):
      raise ConfigurationError("Symbolic execution 'timeout' must be an integer")   
    
  def setGraphSizeLimits(self, node=42, height=-1, width=-1):
    try:
      self.symbexNode = int(node) # 1000
    except (TypeError, ValueError):
      raise ConfigurationError("SGraphSizeLimit 'node' must be an integer")
    try:
      self.height = int(height) #-1
    except (TypeError, ValueError):
      raise ConfigurationError("GraphSizeLimit 'height' must be an integer")
    try:
      self.width = int(width) #-1
    except (TypeError, ValueError):
      raise ConfigurationError("GraphSizeLimit 'width' must be an integer")
       
  def setStrategy(self, strategy="DFS"):
    if strategy == "WBFS": 
      self.strategy = "WEIGHT_BREADTH_FIRST_SEARCH"
    else:
      try:
        self.strategy = self._strategies[strategy]
      except KeyError:
        raise ConfigurationError("Unknown strategy {}".format(strategy))
    
  def setRedundancyDetectionMethod(self, method=None):
    try:
      self.redundancyDetectionMethod = self._redundancyDetectionMethods[method]
    except KeyError:
      raise ConfigurationError("Unknown redundancy detection method {}".format(method))
    
  def setRedundancyDetectionPathScope(self, scope=None):
    if not scope in self._pathScopes:
       raise ConfigurationError("Unknown path scope {}".format(scope))
    else:
      self.pathScope = scope
      
  def setRedundancyDetectionComparisonOperator(self, operator=None):
    if not operator in self.comparisonOperators:
       raise ConfigurationError("Unknown comparison operator {}".format(operator))
    else:
      self.comparisonOperator = operator
      
  def setTransitionCoverageScope(self, scope=None):
    if not scope in self._transitionCoverageScopes:
       raise ConfigurationError("Unknown transition coverage scope {}".format(scope))
    else:
      self.transitionCoverageScope = scope
      
  def setTraceFile(self, file):
    self.traceFile = file
      
  def setVerbosity(self, verb="SILENT"):
    if not verb in self._verbosity:
      raise ConfigurationError("unknown verbosity value {} ".format(verb))
    else:
      self.verbosity = verb
      
  def setSpider(self, init=None, step=None, stop=None):
    self.spiderInit = init
    self.spiderStep = step
    self.spiderStop = stop
  
  def setSolver(self, solver="Z3"):
    if not solver in self._solvers:
      raise ConfigurationError("Unknown solver {}".format(solver))     
    else:
      self.constraintSolver = solver
      
  def setDebugFilename(self, name):
    self.debugFilename = name
    
  def setLogFilename(self, name):
    self.logFilename = name
    
  def setDebugLevel(self, level):
    if not level in self._debugLevels:
      raise ConfigurationError("Unknown debug level: {}".format(level))
    else: 
      self.debugLevel = level
  
  
  def unsetDebugFlag(self, flag):
    self.setDebugFlag(flag, False)
  
  def setDebugFlag(self, flag, active=True):
    if not flag in self._debugFlags:
      raise ConfigurationError("Unknown debug flag: {}".format(flag))
    if active and flag in self.activeDebugFlags:
      raise ConfigurationError("Flag {} already active".format(flag))
    elif not active and not flag in self.activeDebugFlags:
      raise ConfigurationError("Flag {} already inactive".format(flag))
    else:
      if active:
        self.activeDebugFlags.append(flag)
      else:
        self.activeDebugFlags.remove(flag)
      
  def setDevFlags(self, *newflags):
    diffset = set(newflags).difference(self._debugFlags)
    if len(diffset) > 0:
      raise ConfigurationError("Unknown flags: %s" % str(diffset))
    else:
      self.activedFlags = self.activedFlags.union(newflags)
      
      
  def toggleDevFlag(self, flag, value):
    if flag in self.activedFlags:
      self.activedFlags.remove(flag)
    else:
      if flag in self._debugFlags:
        self.activedFlags.add(flag)
      else:
        raise ConfigurationError("Unknown flag: {}".format(flag))
      
  def check(self):
    print("Configuration check: ", end='') 
    try:
      self.__checkMandatoryOptions()
    except Exception as e:
      print("*** Error: {} ***".format(e))
    else:
      print(" all ok.")
      
  def __checkMandatoryOptions(self):
    """Check if any compulsory parameter is missing"""
    if not self.constraintSolver:
      raise ConfigurationError("No constraints solver defined")
    
    if not self.strategy:
      raise ConfigurationError("No exploration strategy defined")
      
  def load(self):
    self.__checkMandatoryOptions()
    ok = False
    try:
      ok = Py_WorkflowParameter.load(self, str(self))
    except RuntimeError:
      raise ConfigurationError("Kernel configuration returned an exception")
    else:
      if not ok:
        raise ConfigurationError("Configuration refused by kernel")
      
    print ("Configuration successfully loaded")
    
    
