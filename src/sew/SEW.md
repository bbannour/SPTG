# SEW, Symbolic Execution Workflow Specification

##  Class Workflow
* **workspace** as Virtual File System for the Workflow
* **projet** as the specification
* **job** as analysis jobs

```sew

Workflow <sew-id> "<description> of the Symbolic Execution Workflow" {
	workspace: [
		//...
	]

	project: [
		//...
	]

	sep <id> "<description> of Global Symbolic Execution Platform Configuration" {
		//...
	}

	// Default Job / Director / Driver
	job = Job <id> "<description>" {
		// ...
	}

	// Additional Job
	job += Job <id> "<description>" {
		// ...
	}

	/*
	sop : Sequence
	    | Parallel
	*/
	scheduler = <sop> {
		start <jod-id-1>
		start <jod-id-1>
	}
}

```


### Sequence Workspace
* **root** as workspace native file system path // Chemin absolu ou relatif (au dossier de lancement!) du projet SEW
* **source** as workspace relative source folder
* **output** as workspace relative output folder
* **log** as workspace output relative log folder

```sew

workspace: [
	root   = "<path>"
	source = "<path>"
	output = "<path>"
	log    = "<path>"
]

```


### Sequence Project

```sew

project: [
	// ...
]

```


### Class SEP

```sew

sep <id> "<description> of Symbolic Execution Platform Configuration" {
	core: [
		//...
	]

	log: [
		//...
	]

	debug: [
		//...
	]

	// ...
}

```


### Class SAJ, Symbolic Analysis Job (or Director / Driver)
* **stream** as default interaction streams
* **project** as analyzed specification
* **serializer** as default serializers
* **fam** as Formal Analysis Module


```sew

job = Job <id> "<description>" {
	sep <id> "<description> of Local Symbolic Execution Platform Configuration" {
		//...
	}

	stream: [
		// ...
	]

	project: [
		//...
	]

	main = MainAnalysisModule <id> "<description> of the Main Analysis Module" {
		// ...
	}

	serializer = GraphVizStatemachineSerializer <id> "<description>" {
		// ...
	}

	serializer = GraphVizExecutionGraphSerializer <id> "<description>" {
		// ...
	}


	fam += StateTransitionCoverageModule "State/Transition Coverage Analysis Module" {
		// ...
	}

	fam += HitOrJumpModule "Hit or Jump Analysis Module" {
		// ...
	}


	fam "Formal Analysis Module" = hitorjump {
		// "Processor" de gestion des critères d'arrêt absolus (paramètres utilisateur)
		main { // or director / driver
			property: [
			
			]

			log: [
			
			]

			debug: [

			]

			queue: [

			]
		}
	}
}

```

#### Sequence Stream
* **stdin** as Standard Input Stream
* **stdout** as Standard Output Stream
* **stderr** as Standard Error Stream

* **project** as model specification


```sew

stream: [
	/*
	uri : std      "::" ( 'cout' | 'cerr' | 'cin'  )
	    | sew      "::" ( 'log'  | 'trace' )
	    | folder   "::" "<path>"
	    | file     "::" "<path>"
	    | filename "::" "<path>"
	    | socket   "::" <host-id> ":" <port-number>
	*/
	stdin  = <uri>
	stdout = <uri>
	stderr = <uri>

	// ...
]

```


#### Sequence Project
* **model** as FormalML Concrete Syntax model

```sew

project: [
	// Chemin relatif à workspace::source (ou absolu!)
	model = "<FormalML-Concrete-Syntax.fml>"

	// ...
]

```

#### Class (/ Sequence ?) FAM, Formal Analysis Module/Plugin
* **priority** as *scheduler priority* in the workflow

```sew

fam += FAM "Transition Coverage Analysis Module" {
	priority: [
		// ...
	]

	scheduling: [
		// ...
	]

	log: [
		// ...
	]

	debug: [
		// ...
	]

}

```


##### Sequence Priority
* **preprocess** as preprocessing stage priority
* **prefilter** as prefiltering stage priority
* **postfilter** as postfiltering stage priority
* **postprocess** as postprocessing stage priority

```sew

priority: [
	preprocess  = <integer>
	prefilter   = <integer>
	postfilter  = <integer>
	postprocess = <integer>

	// ...
]

```


##### Sequence Scheduling
* **preprocess** as preprocessing stage enabled flag
* **prefilter** as prefiltering stage enabled flag
* **postfilter** as postfiltering stage enabled flag
* **postprocess** as postprocessing stage enabled flag

```sew

scheduling: [
	preprocess  = <boolean>
	prefilter   = <boolean>
	postfilter  = <boolean>
	postprocess = <boolean>

	// ...
]

```


##### Sequence Log

```sew

log: [
	// ...
]

```


##### Sequence Debug

```sew

debug: [
	// ...
]

```


#### Class MainAnalysisModule as Director or Driver
* **queue** as Symbolic Execution Queue
* **limit** as Symbolic Execution Processing Limit
* **irq** as *interrupt request* listener configuration
* **detector** as list of *passive detector* enabled flag

```sew

main = MainAnalysisModule <id> "<description> of the MAM"  {
	queue "<description> of Symbolic Execution Queue" : [
		// ...
	]

	limit "Symbolic Execution Processing Limit" : [
		// ...
	]

	irq "IRQ, Interrupt ReQuest for the Workflow" : [
		// ...
	]

	detector <id> "Enable some passive detectors" : [
		// ...
	]

	// ...
}

```

##### Class / Sequence Queue
* **policy** as *enqueue/dequeue policy* of the queue

```sew
// Default Queue Sequence
queue "<description> of the Symbolic Execution Queue" : [
	/*
	'BFS' | 'BREADTH_FIRST_SEARCH'
	'DFS' | 'DEPTH_FIRST_SEARCH'
	'RFS' | 'RANDOM_FIRST_SEARCH'
	'WEIGHT::{ DFS | BFS | RFS | XFS }'
	*/
	policy = <policy>

	// ...
]

// Specific Class Queue
queue = <queue_type_id> "<description> of the Symbolic Execution Queue" {
	/*
	'BFS' | 'BREADTH_FIRST_SEARCH'
	'DFS' | 'DEPTH_FIRST_SEARCH'
	'RFS' | 'RANDOM_FIRST_SEARCH'
	'WEIGHT::{ DFS | BFS | RFS | XFS }'
	*/
	policy = <policy>

	// ...
}



```

##### Sequence Limit
* **node** as the maximum number of *nodes* built for the symbolic execution graph
* **height** as the maximum *height* of the symbolic execution graph
* **width** as the maximum *width* of the symbolic execution graph
* **eval** as the maximum number of symbolic *evaluation* steps
* **step** as the maximum number of symbolic evaluation *steps*
* **save** as a *point of serialization* based on the number of evaluation steps

```sew
limit "Symbolic Execution Processing Limit" : [
	node   = <integer>
	height = <integer>
	width  = <integer>

	eval = <integer>
	step = <integer>

	save = <integer>
	// ...
]

```


##### Sequence IRQ, Interrupt ReQuest
* **frequency** as a *frequency of listening* based on the number of evaluation steps

```sew
irq "IRQ, Interrupt ReQuest for the Workflow" : [
	frequency = <integer>

	file = "<stop-if-this-file-path-exist>"
	// ...
]

```


##### Sequence Detector
* **deadlock** as the maximum *height* of the symbolic execution graph
* **loop#trivial** as the maximum number of *nodes* built for the symbolic execution graph

```sew
detector "Enable some passive detectors" : [
	deadlock      = <boolean>
	loop#trivial = <boolean>
	// ...
]

```


#### Class Serializer

##### Class GraphVizStatemachineSerializer

```sew

serializer += GraphVizStatemachineSerializer <id> "<description>" {
	// ...

property: [

]
	
trace: [

]
	
format: [

]

vfs: [
    file = "<save-file-path>"
]

```

##### Class GraphVizExecutionGraphSerializer

```sew

serializer += GraphVizExecutionGraphSerializer <id> "<description>" {	
	// ...

property: [

]
	
trace: [

]
	
format: [

]

vfs: [
    file = "<save-file-path>"
]

```


#### Class StateTransitionCoverageModule

```sew

fam += StateTransitionCoverageModule "State/Transition Coverage Analysis Module" {
	// ...
}

```s

#### Class HitOrJumpModule

```sew

fam += HitOrJumpModule <id> "<description>" {
	// ...
}

```


## Simple Workflow: BFS exploration :

```sew

Workflow explorationBFS "Simple model BFS exploration Workflow" {
	workspace: [
		root = "<workspace-root-folder-from-filse-system-path>"
		output = "out"
	]

	job {
		project: [
			model = "<FormalML-Concrete-Syntax.fml>"
		]

		main {
			queue "Symbolic Execution Queue" : [
				policy = 'BFS'
			]

			limit "Symbolic Execution Processing Limit" : [
				step = 10
			]
		}

		serializer = GraphVizStatemachineSerializer { }

		serializer = GraphVizExecutionGraphSerializer { }
	}
}

```





