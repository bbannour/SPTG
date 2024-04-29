# ==============================================================================
#                           Engine Pure Python API
# ==============================================================================


from .maatcore import *
from .serialization import ResultDisplayStrategy
from .serialization import show, showCG, showSD, showText

  
# 
# def ClassFactory(name, argnames, BaseClass=BaseClass):
#     def __init__(self, **kwargs):
#         for key, value in kwargs.items():
#             # here, the argnames variable is the one passed to the
#             # ClassFactory call
#             if key not in argnames:
#                 raise TypeError("Argument %s not valid for %s" 
#                     % (key, self.__class__.__name__))
#             setattr(self, key, value)
#         BaseClass.__init__(self, name[:-len("Class")])
#     newclass = type(name, (BaseClass,),{"__init__": __init__})
#     return newclass
#   
#  SpecialClass = ClassFactory("Result", "a b c".split())

# class Result(Py_Result):
#   
#   def __init__(self):
#     P_Result.__init__(self)
#     DisplayableElement.__init__(self, ResultDisplayStrategy())
    


class Engine(Py_Engine):
  
  def __init__(self, w):
    w.load()
    Py_Engine.__init__(self, w)
        
  def setSystem(self, system):
    ok = Py_Engine.setSystem(self, system)
    if ok:
      print("System successfully loaded.")
    else: 
      print("System loading returned an error")
      
  def start(self):
    result = Py_Engine.start(self)
    setattr(result, "display_strategy", ResultDisplayStrategy())
    return result
    