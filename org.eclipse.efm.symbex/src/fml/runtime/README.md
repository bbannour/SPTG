# EFM-SYMBEX : Runtime

## Source code structure

### Interfaces

### Classes

#### Processes
* **PID** as *Process Identifier* of Instance of Machine
* **Process** as *Instance* at runtime stage in an *Execution Context* snapshot
* **ProcessTable** as *Process Table* 

#### Table 
* **ValueTable** as Value Table of *Process* w.r.t *Variable* Table of Instance Model, aka Machine
* **BufferInstanceTable** as Buffer Instance Table of *Process* w.r.t Buffer Model Table of Instance Model, aka Machine

#### Message Table
##### Interfaces
* **IMessageTable** as *Runtime Buffer* Interface for message storage

##### Classes
* **FifoMessageTable** as Message Table with FIFO storage handler
* **LifoMessageTable** as Message Table with LIFO storage handler
* **BagMessageTable**  as Message Table with BAG storage handler
* **SetMessageTable** as Message Table with SET storage handler
* **RamMessageTable** as Message Table with RAM storage handler

##### Factories
* **MessageTable** as Smart Pointer


### Factories

