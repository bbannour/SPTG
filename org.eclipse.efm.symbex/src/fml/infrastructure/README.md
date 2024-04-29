# EFM-SYMBEX : Infrastructure

## Object lyfe cycle / stage

### Modeling

### Compiled

### Runtime


## Elements

Modeling           |  Compiled         |  Runtime
-------------------|-------------------|-------------------
System             | ExecutableSystem  | Execution Context/Data
System             | ExecutableForm    | RuntimeForm
                   |                   |                   
Machine            | ExecutableForm    | RuntimeForm
Machine            | InstanceOfMachine | Optimized Runtime Process Access
                   |                   |                   
Statemachine       | ExecutableForm    | RuntimeForm
Statemachine       | InstanceOfMachine | Optimized Runtime Process Access
                   |                   |                   
State              | ExecutableForm    | ?? RuntimeForm
State              | InstanceOfMachine | ?? Optimized Runtime Process Access
                   |                   |                   
Procedure          | ExecutableForm    | RuntimeForm
Procedure          | InstanceOfMachine | Optimized Runtime Process Access
                   |                   |                   
Instance           | InstanceOfMachine | Optimized Runtime Process Access 
Instance           | InstanceOfMachine | Specific Primitive Routine Code 
                   |                   |                   
Primitive Routine  | Program           | Optimized 
Routine            | Program           | Optimized 
Transition         | Program           | Optimized
Transition         | Program           | Optimized
                   |                   |                   
Variable           | InstanceOfData    | Optimized Runtime [L/R] Value Access 
Buffer             | InstanceOfBuffer  | Optimized Runtime Concrete Buffer Access  
Port               | InstanceOfPort    | Optimized Runtime Routing Data Access
Signal/Message     |                   | Message Data                  
Connector          | InstanceOfConnector |                  
                   |                   |                   
Expression         | Bytecode          | Optimized Bytecode
Instruction        | Bytecode          | Optimized Bytecode
                   |                   |                   

## Source code structure

### Interfaces

### Classes
* **System**
* **Machine**
* **Behavior**
* **Routine**
* **Procedure**
* **Instance**
* **Connector**
* **Router**
* **Message**

#### Behavior
* **Statemachine**
* **Region**
* **State**
* **Pseudstate**
* **Transition**

#### Statemachine Behavior
* **Statemachine**
* **Region**
* **State**
* **Pseudstate**
* **Transition**

### Factories


