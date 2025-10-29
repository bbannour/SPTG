# ==============================================================================
#                       Serialization Pure Python code
# ==============================================================================



from ..maatcore import *


from plantuml import PlantUML
from IPython.display import Image
from .system import System
from .engine import Result


local_plantuml_url = "http://localhost:8080/plantuml/img/"
xavier_plantuml_url = "http://10.8.33.64:8080/plantuml/img/"

PLANTUML_SERVER = PlantUML(local_plantuml_url) # Remove argument to use distant plant Uml Server.




class Displayer(Py_Display):
  
  def __init__(self):
    Py_Display.__init__(self)
    
    
    
class DisplayStrategy():
  """Display Base Strategy """
  def display(self, element, **kwargs):
    """Default display"""
    raise NotImplementedError 
  
  def displayCG(self, element, **kwargs):
    """Display Communication Graph"""
    raise NotImplementedError
  
  def displaySD(self, element, **kwargs):
    """Display Sequence diagram"""
    raise NotImplementedError
    
    
class SystemDisplayStrategy(DisplayStrategy):
  
  def __init__(self):
    IDisplay.__init__(self)
    
    
  def display(self, **kwargs):
    try:
      showTransition = kwargs["showTransition"]
    except KeyError: 
      showTransition = True  
    try:
      showCommunication = kwargs["showCommunication"]
    except KeyError:
       showCommunication = True
    try:
      showAssign = kwargs["showAssign"]
    except KeyError:
      showAssign = False

    return Image(PLANTUML_SERVER.processes(Py_Display().display(element, showTransition, showCommunication , showAssign)))
  
  def displayComGraph(self, element, **kwargs):
    return Image(PLANTUML_SERVER.processes(Py_Display().displayCommunicationGraph(element)));
  
  
class ResultDisplayStrategy(IDisplay):
  
  def display(self, **kwargs):
    try:
      showAssign = kwargs["showAssign"]
    except KeyError:
      showAssign = False
    try:
      showTransition = kwargs["showTransition"]
    except KeyError:
      showTransition = False  
    try:
      enabledNumerization = kwargs["enabledNumerization"]
    except KeyError:
      enabledNumerization = False
        
    return element.displayText(showAssign, showTransition, enabledNumerization)


def display(element, showTransition=True, showCommunication=True, showAssign=False):
  if isinstance(element, System):
    return Image(PLANTUML_SERVER.processes(Displayer().display(element, showTransition, showCommunication , showAssign)))
  elif isinstance(element, Py_Result):
    return Image(PLANTUML_SERVER.processes(element.display(showTransition, showCommunication, showAssign)))
  else:
    return "Display not available for {}".format(repr(element)) 


def displaySD(element, showAssign=False, showTransition=False, enabledNumerization=False): 
  if isinstance(element, Py_Result):
    return Image(PLANTUML_SERVER.processes(element.displaySD(showAssign, showTransition, enabledNumerization)))
  else:
    return "Display not available for {}".format(repr(element)) 
  
  
  
def displayCommGraph(element):
  if isinstance(element, System):
    return Image(PLANTUML_SERVER.processes(Displayer().displayCommunicationGraph(element)));
  else:
    return "Display not available for {}".format(repr(element)) 
 


def displayText(element, showAssign=False, showTransition=False, enabledNumerization=False): 
  if isinstance(element, Py_Result):
    return element.displayText(showAssign, showTransition, enabledNumerization)
  else:
    return "Display not available for {}".format(repr(element))

