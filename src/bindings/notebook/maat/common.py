# ==============================================================================
#            Common functions for the Pure Python layer 
# ==============================================================================


from .maatcore import *

# Printinf a C++ vector of strings as a Python string
def stringVectorToStr(self):
	outStr = "["
	for s in self: 
		outStr += s + ", "
	outStr = outStr[:-2] + "]"
	return outStr

setattr(string_vector, "__str__", stringVectorToStr)



