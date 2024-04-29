# ==============================================================================
#                      System Definition Pure Python API
# ==============================================================================

from ..maatcore import *
from ..serialization import SystemDisplayStrategy
from ..serialization import show, showCG, showSD, showText


class IdentifierError(Exception):

  def __init__(self, msg):
    self.msg = msg

  def __str__(self):
    return self.msg


class SemanticError(Exception):

  def __init__(self, msg):
    self.msg = msg

  def __str__(self):
    return self.msg
    
    
def checkName(name):
  if (name != str(name)):
    raise IdentifierError("Name shall be a string")  

  if (name == ""):
    raise IdentifierError("Name cannot be an empty string")
  
  if (' ' in name or '#' in name or ':' in name):
    raise IdentifierError("Name cannot include any '#', ':' or ' '")
  
# class TimedSystemType:
#   NotTimed = 0
#   DiscreteTime = 1
#   ContinousTime = 2


class System(Py_System):
  
  def __init__(self, name, timed="not_timed"):
    checkName(name)
    Py_System.__init__(self, name, timed)
    self.display_strategy = SystemDisplayStrategy()

    
  def addStateMachine(self, name):
    checkName(name)
    if name in Py_System.getMachineNames(self):
      raise IdentifierError("State machine {} already exists".format(name))
    else:
      return StateMachine(Py_System.addStateMachine(self, name))

  def checkSameSignatures(self, ports):
    if len(ports) == 0:
      return True    
    ok = True
    ports = list(ports)
    first = ports.pop()
    while len(ports) > 0:
      current = ports.pop()
      if not first.isConnectablebleWith(current):
        raise SemanticError("{} and {} have different signatures".format(first, current))
    return True
    
  def connectRdv(self, *ports):
    if len(ports) != 2 : 
      raise SemanticError("Connect refused: exactly 2 ports are needed for a 'rdv' connection")
    self.checkSameSignatures(ports)
    self.connect(list(ports), "rdv")
        
  def connectMultiRdv(self, *ports):
    if not self.hasSameSignature(ports):
      raise SemanticError("Connect refused: ports have different signatures")
    else: 
        self.connect(list(ports), "multirdv")

  def connectEnv(self, *ports):
        self.connect(list(ports), "env")
        

# Final and Terminal states must be refuse transition 
def addTransitionRefused(self, name, state):
  raise SemanticError("{}:{} cannot have transition".format(self.__class__, repr(self)))


setattr(Py_FinalState, "addTransition", addTransitionRefused)
setattr(Py_TerminalState, "addTransition", addTransitionRefused)


class StateMachine(object):
#   def __init__(self, name):
#     checkName(name)
#     Py_StateMachine.__init__(self, name)

  def __init__(self, input):
    if isinstance(input, Py_StateMachine):
      self.instance = input
    elif str(input) == input:
      checkName(input)
      self.instance = Py_StateMachine(input)
    else:
      raise ValueError("StateMachine constructor is waiting either for a Py_StateMachine instance or for a string")

  def __str__(self):
     return str(self.instance) 
     
  def addInitialState(self, name):
    checkName(name)
    return self.instance.addInitialState(name)
  
  def addFinalState(self, name):
    checkName(name)
    return self.instance.addFinalState(name)
  
  def addStartState(self, name):
    checkName(name)
    return self.instance.addStartState(name)

  def addTerminalState(self, name):
    checkName(name)
    return self.instance.addTerminalState(name)

  def addJunctionState(self, name):
    checkName(name)
    return self.instance.addJunctionState(name)
  
  def addChoiceState(self, name):
    checkName(name)
    return self.instance.addChoiceState(name)

  def addAndState(self, name):
    checkName(name)
    return self.instance.addAndState(name)
  
  def addOrState(self, name):
    checkName(name)
    return self.instance.addOrState(name)

  def addState(self, name):
    checkName(name)
    if name in self.instance.getStateNames():
      raise IdentifierError("State {} already exists".format(name))
    else:
      return self.instance.addState(name)
    
  def addInPort(self, name, params=None):
    if params  is None: 
      params = []
    checkName(name)
    if name in self.instance.getPortNames():
      raise IdentifierError("Port {} already exists".format(name))
    else:
      return self.instance.addInPort(name, params)
    
  def addOutPort(self, name, params=None):
    if params  is None: 
      params = []
    checkName(name)
    if name in self.instance.getPortNames():
      raise IdentifierError("Port {} already exists".format(name))
    else:
      return self.instance.addOutPort(name, params)

  def addIntVar(self, name, init=None):
    checkName(name)
    v = self.instance.addVar(name, "int")
    if init is not None:
      try:
        InitInt = int(init)
      except ValueError:
        raise SemanticError("Integer variable {}: default value not an integer {}".format(name, str(init)))
      else:
        v.setIntInitVal(InitInt)
    return v
    
  def addBoolVar(self, name, init=None):
    checkName(name)
    v = self.instance.addVar(name, "bool")
    if init is not None:
      if init != True and init != False:  # we purposely not use the bool() function which never fail to convert any type to boolean
        raise SemanticError("Integer variable {}: default value not a boolean {}".format(name, str(init)))
      else:
        v.setBoolInitVal(init)
    return v

  def addStringVar(self, name, init=None):
    checkName(name)
    v = self.instance.addVar(name, "string")
    if init is not None:
      try:
        InitStr = str(init)
      except ValueError:
        raise SemanticError("Integer variable {}: default value not a string {}".format(name, str(init)))
      else:
        v.setStringInitVal(InitStr)
    return v
    
  def addIntConst(self, name, val):
    checkName(name)
    try:
      intVal = int(val)
    except ValueError:
      raise SemanticError("Integer constant {}: value not an integer {}".format(name, str(val)))
    else:
      c = self.instance.addConst(name, "int")
      c.setIntVal(intVal)
      return c
    
  def addBoolConst(self, name, val):
    checkName(name)
    if val != True and val != False:  # we purposely not use the bool() function which never fail to convert any type to boolean
      raise SemanticError("Integer constant {}: value not a boolean {}".format(name, str(val)))
    else:
      c = self.instance.addConst(name, "bool")
      c.setBoolVal(val)
      return c

  def addStringConst(self, name, val):
    checkName(name)
    try:
      strVal = str(val)
    except ValueError:
      raise SemanticError("Integer constant {}: value not a string {}".format(name, str(val)))
    else:
      c = self.instance.addConst(name, "string")
      c.setStringVal(strVal)
      return c

  def addClock(self, name):
    checkName(name)
    return self.instance.addClock(name)

# 
# class Transition(Py_Transition):
#   def __init__(self, name, source, target):
#     Py_Transition.__init__(self, name, source, target)
# 
# 
# class State(Py_State):
#   def __init__(self, name):
#     checkName(name)
#     Py_State.__init__(self, name)
# 
# 
# # class InitialState(Py_InitialState):
# #   def __init__(self, name):
# #     checkName(name)
# #     Py_InitialState.__init__(self, name)
# 
# 
# class FinalState(Py_FinalState):
#   def __init__(self, name):
#     checkName(name)
#     Py_FinalState.__init__(self, name)
# 
# 
# class StartState(Py_StartState):
#   def __init__(self, name):
#     checkName(name)
#     Py_StartState.__init__(self, name)
# 
# 
# class TerminalState(Py_TerminalState):
#   def __init__(self, name):
#     checkName(name)
#     Py_TerminalState.__init__(self, name)
# 
# 
# class JunctionState(Py_JunctionState):
#   def __init__(self, name):
#     checkName(name)
#     Py_JunctionState.__init__(self, name)
# 
# 
# class ChoiceState(Py_ChoiceState): 
#   def __init__(self, name):
#     checkName(name)
#     Py_ChoiceState.__init__(self, name)
    
