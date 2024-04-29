import unittest

from ..systemdefinition import System, StateMachine, IdentifierError, SemanticError


class TestSystem(unittest.TestCase):

  def setUp(self):
     unittest.TestCase.setUp(self)
  
  def tearDown(self):
    unittest.TestCase.tearDown(self)
    
  def t_system_creation(self):
    s = System("SolarSystem")
    s_str = str(s)
    self.assertIn("system", s_str, "keyword 'system' not printed")
    self.assertIn("SolarSystem", s_str, "system name not printed")
    
  def t_system_creation_noname(self):
    with self.assertRaises(TypeError):
      System()
    with self.assertRaises(IdentifierError):
      System("")
    
  def t_system_creation_badname(self):
    with self.assertRaises(IdentifierError):
      System("Bad Name")
    with self.assertRaises(IdentifierError):
      System("Bad:Name")
    with self.assertRaises(IdentifierError):
      System("Bad#Name")
      
  def t_system_creation_of_2_refused(self):
    """TODO : expected behavior ? : one unique system only"""
    System("SolarSystem1")
    with self.assertRaises(SemanticError):
      System("SolarSystem2")
       
  def t_system_add_1_statemachine(self):
    s = System("SolarSystem")
    sm = s.addStateMachine("Earth")
    s_str = str(s)
    self.assertIn("statemachine", s_str, "keyword 'statemachine' not printed")
    self.assertIn("Earth", s_str, "state machine name not printed")
        
  def t_system_add_2_statemachines_samename(self):
    s = System("SolarSystem")
    sm1 = s.addStateMachine("Earth")
    with self.assertRaises(IdentifierError):
      sm2 = s.addStateMachine("Earth")
#    s_str = str(s)
#     self.assertIn("statemachine", s_str, "keyword 'statemachine' not printed")
#     self.assertIn("Earth", s_str, "state machine name not printed")        
    
  def t_system_connect_rdv(self):
    s = System("SolarSystem")
    sm1 = s.addStateMachine("Earth")
    sm2 = s.addStateMachine("Moon")
    p1 = sm1.addOutPort("laser_transmitter", ["bool"])
    p2 = sm2.addInPort("optical_cell", ["bool"])
    s.connectRdv(p1, p2)
    s_str = str(s)
    self.assertIn("@com", s_str, "keyword '@com' not printed")
    self.assertIn("connector< rdv , unicast >", s_str, "statement 'connector< rdv , unicast >' not printed")
    self.assertIn("output Earth->laser_transmitter", s_str, "statement 'input Earth->laser_transmitter' not printed")
    self.assertIn("input Moon->optical_cell", s_str, "statement 'output Moon->optical_cell' not printed")

  def t_system_connect_rdv_differentsignatures(self):
    s = System("SolarSystem")
    sm1 = s.addStateMachine("Earth")
    sm2 = s.addStateMachine("Moon")
    p1 = sm1.addOutPort("laser_transmitter", ["int"])
    p2 = sm2.addInPort("optical_cell", ["bool"])
    with self.assertRaises(SemanticError):
      s.connectRdv(p1, p2)
      
  def t_system_connect_rdv_1port(self):
    s = System("SolarSystem")
    sm1 = s.addStateMachine("Earth")
    p1 = sm1.addOutPort("laser_transmitter", ["bool"])
    with self.assertRaises(SemanticError):
      s.connectRdv(p1)
    
  def t_system_connect_rdv_3ports(self):
    s = System("SolarSystem")
    sm1 = s.addStateMachine("Earth")
    sm2 = s.addStateMachine("Moon")
    p1 = sm1.addOutPort("laser_transmitter", ["bool"])
    p21 = sm2.addInPort("optical_cell_1", ["bool"])
    p22 = sm2.addInPort("optical_cell_2", ["bool"])
    with self.assertRaises(SemanticError):
      s.connectRdv(p1, p21, p22)
      
      
class TestStateMachineGeneral(unittest.TestCase):
  
  def setUp(self):
     unittest.TestCase.setUp(self)
  
  def tearDown(self):
    unittest.TestCase.tearDown(self)
    
  def t_sm_general_creation(self):
    sm = StateMachine("Earth")
    sm_str = str(sm)
    self.assertIn("statemachine", sm_str, "keyword 'statemachine' not printed")
    self.assertIn("Earth", sm_str, "state machine name not printed")
    
  def t_sm_general_creation_noname(self):
    with self.assertRaises(IdentifierError):
      StateMachine("")
      
  def t_sm_general_creation_badname(self):
    with self.assertRaises(IdentifierError):
      StateMachine("Bad Name")     
    with self.assertRaises(IdentifierError):
      StateMachine("Bad:Name")
    with self.assertRaises(IdentifierError):
      StateMachine("Bad#Name")
          
          
class TestStateMachineStates(unittest.TestCase):
  """All these tests to be updated with a check condition when str() is available for state machine """

  def setUp(self):
     unittest.TestCase.setUp(self)
  
  def tearDown(self):
    unittest.TestCase.tearDown(self)  
    
  def t_sm_states_regularstate(self):
    sm = StateMachine("Earth")
    s = sm.addState("Europa")
    self.assertIn("state", str(s), "'state' keyword is absent")
    self.assertIn("Europa", str(s), "state name is absent")
    self.assertIn("Europa", str(sm), "state name is absent from the state machine")
  
    
  def t_sm_states_regularstate_noname(self):
    sm = StateMachine("Earth")
    with self.assertRaises(TypeError):
      sm.addState()
    with self.assertRaises(IdentifierError):
      sm.addState("")
    
  def  t_sm_states_regularstate_2_samename(self):
    sm = StateMachine("Earth")
    s1 = sm.addState("Europa")
    with self.assertRaises(IdentifierError):
      s2 = sm.addState("Europa")        
      
  def t_sm_states_initialstate_creation(self):
    sm = StateMachine("Earth")
    s = sm.addInitialState("Africa")
    self.assertIn("initial", str(s), "'initial' keyword is absent")
    self.assertIn("Africa", str(sm), "state name is absent from the state machine")
    self.assertIn("initial", str(sm), "'initial' keyword is absent from the state machine")
    
  def t_sm_states_finalstate_creation(self):
    # TBC : assertIn(...) 
    sm = StateMachine("Earth")
    s = sm.addFinalState("America")        
    
  def t_sm_states_startstate_creation(self):
    # TBC : assertIn(...)
    sm = StateMachine("Earth")
    s = sm.addStartState("Africa")
    
  def t_sm_states_terminalstate_creation(self):
    # TBC : assertIn(...)
    sm = StateMachine("Earth")
    s = sm.addTerminalState("America")
        
  def t_sm_states_choicestate_creation(self):
    # TBC : assertIn(...)
    sm = StateMachine("Earth")
    s = sm.addChoiceState("MiddleEast")
    
  def t_sm_states_junctionstate_creation(self):
    # TBC : assertIn(...)
    sm = StateMachine("Earth")
    s = sm.addJunctionState("ExtremeOrient")
    
  def t_sm_states_andstate_creation(self):
    # TBC : assertIn(...)
    sm = StateMachine("Evolution")
    s = sm.addAndState("HomoGenus")
    
  def  t_sm_states_orstate_creation(self):
    # TBC : assertIn(...)
    sm = StateMachine("Evolution")
    s = sm.addAndState("Hominoid")
  
    
class TestStateMachineTransitions(unittest.TestCase):
  """All these tests to be updated with a check condition when str() is available for state machine """

  def setUp(self):
    unittest.TestCase.setUp(self)
  
  def tearDown(self):
    unittest.TestCase.tearDown(self)
    
  def t_sm_transitions_creation(self):
    earth = StateMachine("Earth")
    warming = earth.addState("Warming")
    freezing = earth.addState("Freezing")
    t = freezing.addTransition("global_warming", warming)
    self.assertIn("transition", str(t), "'transition' statement is absent")
    self.assertIn("-->", str(t), "'-->' is absent")
    self.assertIn("global_warming", str(t), "transition name is absent")  
    self.assertIn("Warming", str(t), "target state name is absent")
    self.assertIn("global_warming", str(earth), "transition name is absent from state machine")
    
# TODO : check expected about transition name limitation 
#   def t_sm_transitions_badname(self):
#     sm = StateMachine("Earth")
#     africa = sm.addState("Africa")
#     europa = sm.addState("Europa")
#     with self.assertRaises(IdentifierError):
#       africa.addTransition("out of africa", europa)  
#     with self.assertRaises(IdentifierError):
#       StateMachine("outof:africa")
#     with self.assertRaises(IdentifierError):
#       StateMachine("outof#africa")
  
  def t_sm_transitions_autotransition(self):
    earth = StateMachine("Earth")
    standardClimate = earth.addState("StandardClimate")
    t = standardClimate.addTransition("balanced_changes", standardClimate)
    self.assertIn("transition", str(t), "'transition' statement is absent")
    self.assertIn("-->", str(t), "'-->' is absent")
    self.assertIn("balanced_changes", str(t), "transition name is absent")
    self.assertIn("StandardClimate", str(t), "target state name is absent")
    self.assertIn("balanced_changes", str(earth), "transition name is absent from state machine")

    
  def t_sm_transitions_goingintoinitialstate(self):
    earth = StateMachine("Earth")
    sulfurSaturated = earth.addInitialState("SulfurSaturated")
    standardClimate = earth.addState("StandardClimate")
    with self.assertRaises(Exception) as cm:
      standardClimate.addTransition("volcanic_activity", sulfurSaturated)
    self.assertIn("DiversityError", str(cm.exception))
    
#   def t_sm_transition_to_outerstate(self):
#     earth = StateMachine("Earth")
#     standardClimate = earth.addState("StandardClimate")
#     moon = StateMachine("Moon")
#     noClimate = moon.addState("NoClimate")
#       with self.assertRaises(Exception) as cm:
#       standardClimate.addTransition("anormal transition", noClimate)
#     # sm1.s1 -> sm2.s2
#     raise NotImplementedError
      
  def t_sm_transitions_goingintostartstate(self):
    earth = StateMachine("Earth")
    sulfurSaturated = earth.addStartState("SulfurSaturated")
    standardClimate = earth.addState("StandardClimate")
    with self.assertRaises(Exception) as cm:
      standardClimate.addTransition("volcanic_activity", sulfurSaturated)
    self.assertIn("DiversityError", str(cm.exception))

  def t_sm_transitions_startingfromterminalstate(self):
    earth = StateMachine("Earth")
    standardClimate = earth.addState("StandardClimate")
    nuclearWinter = earth.addTerminalState("NuclearWinter")
    with self.assertRaises(SemanticError):
      nuclearWinter.addTransition("terraforming", standardClimate)
      
  def t_sm_transitions_startingfromfinalstate(self):
    earth = StateMachine("Earth")
    standardClimate = earth.addState("StandardClimate")
    nuclearWinter = earth.addFinalState("NuclearWinter")
    with self.assertRaises(SemanticError):
      nuclearWinter.addTransition("terraforming", standardClimate)  
  
  def t_sm_transition_addSend(self):
    earth = StateMachine("Earth")
    idle = earth.addState("Idle")
    emitting = earth.addState("Emitting")
    start_emit = idle.addTransition("start_emission", emitting)
    laser_transmitter = earth.addOutPort("laser_transmitter", ["int"])
    start_emit.addSend(laser_transmitter, ["42"])
    self.assertIn("output", str(start_emit), "'output' statement is absent")
    self.assertIn("laser_transmitter", str(start_emit), "port name is absent")
    self.assertIn("42", str(start_emit), "output value is absent")

  def t_sm_transition_addSend_inconsistentdata(self):
    earth = StateMachine("Earth")
    idle = earth.addState("Idle")
    emitting = earth.addState("Emitting")
    start_emit = idle.addTransition("start_emission", emitting)
    laser_transmitter = earth.addOutPort("laser_transmitter", ["int"])
    with self.assertRaises(Exception) as cm:
      start_emit.addSend(laser_transmitter, ["badtyped_data"])
    self.assertIn("DiversityError", str(cm.exception))
    self.assertIn("Unfound symbol for literal expression", str(cm.exception))
    
  def t_sm_transition_addReceive(self):
    earth = StateMachine("Earth")
    idle = earth.addState("Idle")
    receiving = earth.addState("Receiving")
    start_receive = idle.addTransition("start_reception", receiving)
    optic_cell = earth.addOutPort("optic_cell", ["int"])
    od = earth.addIntVar("od")
    start_receive.addReceive(optic_cell, ["od"])
    self.assertIn("input", str(start_receive), "'input' statement is absent")
    self.assertIn("optic_cell", str(start_receive), "port name is absent")
    self.assertIn("od", str(start_receive), "input variable name is absent")
    #self.assertIn("DiversityError", str(cm.exception))
    #self.assertIn("Unfound symbol for literal expression", str(cm.exception))
    #raise NotImplementedError

  def t_sm_transition_addReceive_inconsistentdata(self):
    raise NotImplementedError
  
  
        
class TestStateMachinePorts(unittest.TestCase):
  
  def setUp(self):
     unittest.TestCase.setUp(self)
  
  def tearDown(self):
    unittest.TestCase.tearDown(self)     
  
  def t_sm_port_creation(self):
    sm = StateMachine("Earth")
    p1 = sm.addInPort("p1", ["bool"])
    p2 = sm.addOutPort("p2", ["uint"])
    self.assertIn("input port p1", str(p1), "'input port p1' statement is absent")
    self.assertIn("p1", str(p1), "'p1' port name is absent")    
    self.assertIn("bool", str(p1), "'bool' is absent in port signature")  
    self.assertIn("output port p2", str(p2), "'output port p2' statement is absent")
    self.assertIn("p2", str(p2), "'p2' port name is absent")    
    self.assertIn("uint", str(p2), "'uint' is absent in port signature")  
    self.assertIn("p1", str(sm), "faulty state machine string: no p1")
    self.assertIn("p2", str(sm), "faulty state machine string: no p2")
        
  def t_sm_port_nosignature(self):
    sm = StateMachine("Earth")
    p1 = sm.addInPort("p1")
    p2 = sm.addInPort("p2", [])          
    p3 = sm.addOutPort("p3")
    p4 = sm.addOutPort("p4", [])
    self.assertIn("input port p1", str(p1), "'input port p1' statement is absent")
    self.assertIn("input port p2", str(p2), "'input port p2' statement is absent")
    self.assertIn("output port p3", str(p3), "'input port p3' statement is absent")
    self.assertIn("output port p4", str(p4), "'input port p4' statement is absent")
    self.assertIn("p1", str(sm), "faulty state machine string: no p1")
    self.assertIn("p2", str(sm), "faulty state machine string: no p2")
    self.assertIn("p3", str(sm), "faulty state machine string: no p3")
    self.assertIn("p4", str(sm), "faulty state machine string: no p4")  
      
  def t_sm_port_badsignature(self):
    # TODO : update with the right diversity exception, when it is implemented in diversity
    sm = StateMachine("Earth")
    with self.assertRaises(RuntimeError):
      sm.addInPort("p", ["badtype"])
    with self.assertRaises(RuntimeError):
      sm.addOutPort("p", ["type_bad"])      
             
  def t_sm_port_2_samename(self):
    s = System("SolarSystem")
    sm1 = StateMachine("Earth")
    p11 = sm1.addInPort("laser_transmitter", ["bool"])
    with self.assertRaises(IdentifierError):
      p12 = sm1.addInPort("laser_transmitter", ["bool"])
    sm2 = StateMachine("Moon")
    p21 = sm2.addOutPort("optical_cell", ["bool"])
    with self.assertRaises(IdentifierError):
      p22 = sm2.addOutPort("optical_cell", ["bool"])          
      

class TestStateMachineVariables(unittest.TestCase):
  
  def setUp(self):
     unittest.TestCase.setUp(self)
  
  def tearDown(self):
    unittest.TestCase.tearDown(self)
    
  def t_sm_var_creation_int(self):
    sm = StateMachine("Earth")
    i1 = sm.addIntVar("i1")
    i2 = sm.addIntVar("i2", 42)
    self.assertIn("var int", str(i1), "'var int' statement is absent")
    self.assertIn("var int", str(i2), "'var int' statement is absent")
    self.assertIn("42", str(i2), "'42' initial value is absent")
    self.assertIn("i1", str(sm), "faulty state machine string: no i1")
    self.assertIn("i2", str(sm), "faulty state machine string: no i2")
    
  def t_sm_var_creation_int_badinit(self):
    sm = StateMachine("Earth")
    with self.assertRaises(SemanticError):
      sm.addIntVar("i1", "tralala")    

  def t_sm_var_creation_bool(self):
    sm = StateMachine("Earth")
    b1 = sm.addBoolVar("b1")
    b2 = sm.addBoolVar("b2", True)
    self.assertIn("var bool", str(b1), "'var bool' statement is absent")
    self.assertIn("var bool", str(b2), "'var bool' statement is absent")
    self.assertIn("true", str(b2), "'true' initial value is absent")
    self.assertIn("b1", str(sm), "faulty state machine string: no b1")
    self.assertIn("b2", str(sm), "faulty state machine string: no b2")
    
  def t_sm_var_creation_bool_badinit(self):
    sm = StateMachine("Earth")
    with self.assertRaises(SemanticError):
      sm.addBoolVar("b1", "quarante-deux")
      
  def t_sm_var_creation_string(self):
    sm = StateMachine("Earth")
    str1 = sm.addStringVar("str1")
    str2 = sm.addStringVar("str2", "quarante-deux")
    self.assertIn("var string", str(str1), "'var string' statement is absent")
    self.assertIn("var string", str(str2), "'var string' statement is absent")
    self.assertIn("quarante-deux", str(str2), "'quarante-deux' initial value is absent")
    self.assertIn("str1", str(sm), "faulty state machine string: no str1")
    self.assertIn("str2", str(sm), "faulty state machine string: no str2")


