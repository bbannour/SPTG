


from maat.systemdefinition import *


def createSystem_Faulty() : 
  system = System("WaterSystem_Ok")
  dispenser = system.addStateMachine("Dispenser")

  full      = dispenser.addState("Full")
  checking  = dispenser.addState("Checking")
  refilling = dispenser.addState("Refilling")

  LVLMIN  = dispenser.addIntConst("LVLMIN", 4)
  LVLRECO = dispenser.addIntConst("LVLRECO", 10)
  level    = dispenser.addIntVar("level")
  isclosed = dispenser.addBoolVar("isclosed")
  
  disp_sensor = dispenser.addInPort("sensor", ["int"])
  disp_closed = dispenser.addInPort("closed", ["bool"])
  disp_request = dispenser.addOutPort("request", ["int"])
  
  init = dispenser.addInitialState("init")
  
  startup = init.addTransition("startup", checking)
  
  level_ok  = checking.addTransition("level_ok", full)
  level_low = checking.addTransition("level_low", refilling)
  
  filling = refilling.addTransition("filling", refilling)
  filled  = refilling.addTransition("filled", full)
  
  detection = full.addTransition("dectection", checking)
  
  detection.addReceive(disp_sensor, ["level"])
  
  level_ok.addGuard("level > LVLMIN")
  
  level_low.addGuard("level <= LVLMIN")
  level_low.addSend(disp_request, ["LVLRECO - level"])
  
  filling.addReceive(disp_closed, ["isclosed"])
  #filling.addGuard("isclosed == false")
  filling.addGuard("isclosed == true")
  
  filled.addReceive(disp_closed, ["isclosed"])
  filled.addGuard("isclosed == true")
  
  pump = system.addStateMachine("Pump")
  
  init = pump.addInitialState("init")
  active = pump.addState("active")
  inactive = pump.addState("inactive")
  
  FLOW = pump.addIntConst("FLOW", 10)
  quantity = pump.addIntVar("quantity")
  
  pump_request = pump.addInPort("request", ["int"])
  pump_closed = pump.addOutPort("closed", ["bool"])
  
  startup = init.addTransition("startup", inactive)
  activation = inactive.addTransition("activation", active)
  flowing = active.addTransition("flowing", active)
  deactivation = active.addTransition("deactivation", inactive)
  
  activation.addReceive(pump_request, ["quantity"])
  
  flowing.addGuard("quantity > 0")
  flowing.addSend(pump_closed, ["false"])
  flowing.addStatement("quantity := quantity - FLOW")
  
  deactivation.addGuard("quantity <= 0")
  deactivation.addStatement("quantity := 0")
  deactivation.addSend(pump_closed, ["true"])
  
  system.connectRdv(pump_closed, disp_closed)
  system.connectRdv(pump_request, disp_request)
  
  system.connectEnv(disp_sensor)
  
  return system