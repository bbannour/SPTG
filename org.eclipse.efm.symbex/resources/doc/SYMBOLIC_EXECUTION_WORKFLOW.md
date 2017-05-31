# SEW, Symbolic Execution Workflow Specification

##  Class Workflow
* **workspace** as Virtual File System for the Workflow
* **projet** as the specification
* **job** as analysis jobs

```sew

Workflow <sew-id> "<description> of the Symbolic Execution Workflow" {
	workspace {
		//...
	}

	project {
		//...
	}

	// Default Job
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


### Class Workspace
* **root** as workspace native file system path
* **source** as workspace source folder
* **output** as workspace output folder
* **log** as workspace output log folder

```sew

workspace {
	// Chemin absolu ou relatif (au dossier de lancement!) du projet SEW
	root = <path>
	// Chemin relatif à @project (ou absolu!) du dossier contenant les fichiers XFSP
	source = <path>
	// Chemin relatif à @project (ou absolu!) du dossier principal des fichiers générés par DIVERSITY
	output = <path>
	// Chemin relatif à @output (ou absolu!) du dossier des fichiers log et debug
	log = <path>
}

```


### Class Project

```sew

project {
	// ...
}

```




### Class SAJ, Symbolic Analysis Job
* **stream** as default interaction streams
* **project** as analyzed specification
* **serializer** as default serializers
* **fam** as Formal Analysis Module


```sew

	stream {
		// ...
	}

	project {
		//...
	}

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
		main {
			@property:

			log:

			debug {

			}

			queue {

			}
		}
	}

}

```

#### Class Stream
* **stdin** as Standard Input Stream
* **stdout** as Standard Output Stream
* **stderr** as Standard Error Stream

* **project** as model specification


```sew

stream {
	/*
	uri : std      "::" ( 'cout' | 'cerr' | 'cin'  )
	    | sew      "::" ( 'log'  | 'trace' )
	    | folder   "::" <path>
	    | file     "::" <path>
	    | filename "::" <path>
	    | socket   "::" <host-id> ":" <port-number>
	*/
	stdin  = <uri>
	stdout = <uri>
	stderr = <uri>

	// ...
}

```


#### Class Project
* **model** as FormalML Concrete Syntax model

```sew

project {
	// Chemin relatif à @workspace::source (ou absolu!)
	model = <FormalML-Concrete-Syntax.fml>

	// ...
}

```

#### Class FAM, Formal Analysis Module/Plugin
* **priority** as *scheduler priority* in the workflow

```sew

fam += CoverageFAM "Transition Coverage Analysis Module" {
	priority  {
		// ...
	}
}

```


##### Class Priority
* **preprocess** as preprocessing thread priority
* **prefilter** as prefiltering thread priority
* **postfilter** as postfiltering thread priority
* **postprocess** as postprocessing thread priority

```sew

priority {
	preprocess  = <integer>
	prefilter   = <integer>
	postfilter  = <integer>
	postprocess = <integer>

	// ...
}

```


#### Class MainAnalysisModule
* **queue** as Symbolic Execution Queue
* **limit** as Symbolic Execution Processing Limit

```sew

main += MainAnalysisModule <id> "<description> of the MAM"  {
	queue <id> "Symbolic Execution Queue" {
		// ...
	}

	limit <id> "Symbolic Execution Processing Limit" {
		// ...
	}

	// Nombre de noeud MAXIMAL (-1 <=> no-limit) de l'arbre d'évaluation symbolique
	node = <integer>

	// Nombre de pas de calcul MAXIMAL (-1 <=> no-limit) du moteur d'évaluation symbolique
	@eval = <integer>;

	// Hauteur MAXIMALE
	@height = <integer>;

	// Largeur MAXIMALE
	@width  = <integer>;

	// ...
}

```

##### Class Queue
* **policy** as *enqueue/dequeue policy* of the queue

```sew

queue <id> "<description> of the Symbolic Execution Queue" {
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


#### Class Serializer

##### Class GraphVizStatemachineSerializer

```sew

serializer += GraphVizStatemachineSerializer <id> "<description>" {
	// ...
}

```

##### Class GraphVizExecutionGraphSerializer

```sew

serializer += GraphVizExecutionGraphSerializer <id> "<description>" {
	// ...
}

```


#### Class StateTransitionCoverageModule

```sew

fam += StateTransitionCoverageModule "State/Transition Coverage Analysis Module" {
	// ...
}

```


#### Class HitOrJumpModule

```sew

fam += HitOrJumpModule <id> "<description>" {
	// ...
}

```





