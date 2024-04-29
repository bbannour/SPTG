import unittest

from . import tests_system 
 
runner = unittest.TextTestRunner(verbosity=2)
loader = unittest.TestLoader()
loader.testMethodPrefix = "t_"

testsuite_system = loader.loadTestsFromModule(tests_system)

