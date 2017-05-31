# SEP, Symbolic Execution Platform: Documentation
La palteforme est constituée des projets suivants:

Projet                        | Descritption
------------------------------|----------------------------------
 org.eclipse.efm.sep.doc      |  Documentation, architecture générale
 org.eclipse.efm.sep.common   |  Eléments communs
 org.eclipse.efm.sep.core     |  Eléments de base
 org.eclipse.efm.sep.infra    |  Infrastructure de données
 org.eclipse.efm.sep.fam      |  Modules d'analyse formalle
 org.eclipse.efm.sep.solver   |  Services de solver
 org.eclipse.efm.sep.engine   |  Le moteur
 org.eclipse.efm.sep.workflow |  Le workflow

Chaque projet est constitué des sections suivante:
* **require** :> ses dépendances externes
* **import** :> ses dépendances au sein de la SEP
* **export** :> ses services proposées
* **internal** :> ses éléments internes


## org.eclipse.efm.sep.common
Utilitaires communs à tous les autres composants

### Require


### Import


### Export
services de sérialisation
services de gestion de trace de mise au point

### Internal
Les détails d'implémentation interne !


## org.eclipse.efm.sep.core

### Require


### Import
* **org.eclipse.efm.sep.common**

### Export
* Smart-Pointer


### Internal
Les détails d'implémentation interne !


## org.eclipse.efm.sep.infra
Infrastructure pour l'exécution symbolique

### Require

### Import
* **org.eclipse.efm.sep.common**
* **org.eclipse.efm.sep.core**


### Export
* Expression
* Instruction
* EC: Execution Context
* ED: Execution Data
* EVAL: Evaluation Environnement
* EXEC: Execution Environnement

### Internal
Les détails d'implémentation interne !


## org.eclipse.efm.sep.fam
Module d'Analyse Formelle

### Require

### Import
* **org.eclipse.efm.sep.common**
* **org.eclipse.efm.sep.core**
  + Smart-Pointer

### Export

#### IFAM: Interface of Formal Analysis Module
C'est l'interface que doit implémenter tout Module d'Analyse Formelle.
Il fournit des services pour intervenir dans les différentes phases du SEW, Symbolic Execution Workflow, à savoir:

* **configure**, MANDATORY
	+ Définit (et vérifie?) dans quelle phase du *SE-Workflow* il va intervenir
	+ Prise en compte la configuration fournit par l'utilisateur, défini dans son **fichier.sew** (ancienmment *fichier.favm*)

* **preprocess**, OPTIONAL, s'il a un traitement à effectuer, en *preprocessing*, i.e. avant la phase dynamique du processus Diversity
* **postprocess**, OPTIONAL, s'il a un traitement à effectuer, en *postprocessing*, i.e. après la phase dynamique du processus Diversity

* **prefilter**, OPTIONAL, s'il a un traitement à effectuer, en *prefiltering*, i.e. pendant la phase dynamique du processus Diversity , mais avant l'exécution symbolique proprement dite

* **postfilter**, OPTIONAL, s'il a un traitement à effectuer, en *postfiltering*, i.e. pendant la phase dynamique du processus Diversity , mais après l'exécution symbolique proprement dite


* **report**, OPTIONAL, pour proposer un bilan de l'analyse formelle effectuée

Soit par exemple:

```cpp
class MyFAM : public AutoRegisteredFAM< MyFAM >,
{
	// MANDATORY for Smart Pointer services
	AVM_DECLARE_CLONABLE_CLASS( MyFAM )

	/**
	 * MyFAM
	 * for automatic registration in the FAM repository
	 * the UFID key
	 * need for instanciation from the SEW specification file
	 */
	AVM_INJECT_AUTO_REGISTER_UFID_KEY( "MyFAM" )
	// end registration

protected:
	/**
	 * ATTRIBUTE
	 */

public:
	/**
	 * CONSTRUCTOR
	 */
	MyFAM(CentralProcessorUnit & aManager, Form * aParameterForm)
	: AutoRegisteredFAM(aManager, aParameterForm,
		AVM_PRE_FILTERING_STAGE | AVM_POST_FILTERING_STAGE, ...),

	/**
	 * CONFIGURE
	 */
	bool configureImpl();

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(AvmOstream & os) const;

	////////////////////////////////////////////////////////////////////////////
	// PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preProcessing
	 */
	virtual bool preprocess();

	/**
	 * postprocessing
	 */
	virtual bool postprocess();

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preFiltering
	 */
	virtual bool prefilter(ExecutionContext * anEC);

	/**
	 * postFiltering
	 * Every post filter has to implement this method
	 */
	virtual bool postfilter(ExecutionContext * anEC);
};

```


#### CPU: Central Processor Unit
C'est le scheduler qui gère l'activation les FAMs dans les différentes phases de l'exécution (voir *section MOE* dans le *fichier SEW/FAVM* de spécification du workflow)

#### MPU: Main Processor Unit
C'est le FAM principal, toujours actif, ayant la charge de

* gérer les "critèrse d'arrêts" (voir *fichier SEW/FAVM* dans le fichier
* détecter les *deadlocks* d'exécution (noeud sans fils en *postprefiltering*)
* diverses traitementents internes, tel l'attribution d'un identifiant (numéro) de largeur dans le graphe d'exécution
* ...


#### Some FAMs
* FAM Coverage (state / transition -- input / output, ...) :pour les analyses dédiées couvertures structurelles des modèles
* FAM Hit or Jump : pour la sélection de comportement à partir de trace fournie par l'utilisateur
* FAM Testing (Online / Offline) : pour calculer un verdict associé à un *objectif de test* en mode *online/offline*

### Internal
Les détails d'implémentation interne !


## org.eclipse.efm.sep.solver

### Require
* CVC4, le solver de l'université de New York hébergé [ici](http://cvc4.cs.nyu.edu/web/) et sur Github [ici](https://github.com/CVC4/CVC4)
* Z3, le solver open-source de Microsoft hébergé [ici](https://github.com/Z3Prover/z3/wiki) et sur Github [ici](https://github.com/Z3Prover/z3)

### Import
* **org.eclipse.efm.sep.common**
  + Outils de mise au point

* **org.eclipse.efm.sep.core**
  + Smart-Pointer

* **org.eclipse.efm.sep.infra**
  + Expression

### Export
**org.eclipse.efm.sep.solver.ISolver** défini l'interface des services attendus d'un solver, pour un prédicat booléen donné, tel:
* **checkSatisfiability()** pour vérifier (ou *checker*) sa satisfiabilité i.e.
  + SAT, satisfiable
  + UNSAT, non-satisfiable
  + ABORT, échec (par abandon) de la vérification
  + UNKNOWN, satisfiabilité inconnu !
* **checkModel()** pour obtenir, si posssible, un modèle concrèt la validant

**org.eclipse.efm.sep.solver.SolverFactory** est une factory permettant:
* l'instanciation d'un solver pariculier,
* l'accès au solver instancié par défaut.

### Internal
Les détails d'implémentation interne !


## org.eclipse.efm.sep.engine
Instancie et exécute la plateforme d'analyse symbolique définie dans le *workflow*

### Require
* Rien

### Import
**org.eclipse.efm.sep.**
* tous les autres composants de la plateforme SEP.

### Export
L'exécutable résultant

### Internal
Les détails d'implémentation interne !
* CPU: Central Processor Unit
* MPU: Main Processor Unit


## org.eclipse.efm.sep.

### Require


### Import


### Export


### Internal
Les détails d'implémentation interne !
