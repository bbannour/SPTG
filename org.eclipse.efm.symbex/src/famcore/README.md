# EFM-SYMBEX::FAM - Formal Analysis Module

## Source code structure

### Interfaces

### Classes

### Factories

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

* **preprocess**, OPTIONAL, s'il a un traitement à effectuer, en *preprocessing*, i.e. avant la phase dynamique du processus Diversity.
Cela pourra être, par exemple un traitemenent sur le modèle à exécuter.
Concrètement on pourrait compléter certains états par l'ajout de transtions pour expliciter les cas de sous-spécification c'est-à-dire ajout de transitions pour 
  + la réception de signaux sans effet (problématique de quiescence?),
  + le remplissage des trous dans les gardes i.e. si on a prévu respectivement les cas [x > 42] , [x < 7], il resterait à spécifier le cas [7 <= x <= 42], et on l'ajouterait sur une nouvelle transition)
  + 
* **postprocess**, OPTIONAL, s'il a un traitement à effectuer, en *postprocessing*, i.e. après la phase dynamique du processus Diversity
On pourrait par exemple 
  + élaguer le graphe pour ne garder que les chemins d'intérêts qui couvre par exemple un comportement critique
  + générer une représention dans un format web ou pour un outils permettant de le visualiser/parcourir graphiquement

* **prefilter**, OPTIONAL, s'il a un traitement à effectuer, en *prefiltering*, i.e. pendant la phase dynamique du processus Diversity , mais avant l'exécution symbolique proprement dite et cela pour chaque noeud/contexte du graphe d'exécution en cours de construction.
Durant cette phase on aura la possibilité de
  + littérallemnt filtrer les noeuds qu'on souhaite réellement voir exécuter avec un critère pertinent pour faciliter l'atteignabilité de notre objectif.
  + modifier des données porter par le noeud (valeur des variables, path condition, ...) et ainsi orienter son exécution

* **postfilter**, OPTIONAL, s'il a un traitement à effectuer, en *postfiltering*, i.e. pendant la phase dynamique du processus Diversity , mais après l'exécution symbolique proprement dite
Durant cette phase on aura la possibilité de
  + littérallemnt filtrer les noeuds qu'on souhaite réellement voir apparaître dans le graphe en ayant connaissance de leurs fils
  + faire des statistiques en vu d'une couverture structurelle (relever les transitions couvertes, les communications, ...)
  
* **report**, OPTIONAL, pour proposer un bilan de l'analyse formelle effectuée, par exemple 
  + affichage d'un verdict (PASS, FAIL, ...)
  + affichage de statistiques d'une couverture structurelle

Soit par exemple:

```cpp
#include  <famcore/api/AbstractProcessorUnit.h>

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
	MyFAM(SymbexControllerUnitManager & aManager, const WObject * wfParameterObject)
	: AutoRegisteredFAM(aManager, wfParameterObject,
		AVM_PRE_FILTERING_STAGE | AVM_POST_FILTERING_STAGE, ...),

	/**
	 * CONFIGURE
	 */
	bool configureImpl();

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const;

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
	virtual bool prefilter(ExecutionContext & anEC);

	/**
	 * postFiltering
	 * Every post filter has to implement this method
	 */
	virtual bool postfilter(ExecutionContext & anEC);
};

```

##### Que peut faire un FAM ?
Seule l'imagination du développeur peut en fixer les limites !

##### A quoi a-t-il accès ?

###### A la Configuration via ``getConfiguration()``
Et par la même 
* au modèle parsé de la spécification xlia, son AST, via ``getConfiguration().getSpecification()``
* au modèle compilé de la spécification, son exécutable, via ``getConfiguration().getExecutableSystem()``
* au graphe d'exécution de la spécification, sa trace, via ``getConfiguration().getExecutionTrace()``

* the queue contains the next symbolic states which are not evaluated yet via``getExecutionQueue()``

* the access to all instanciated FAM via ``getControllerUnitManager()``

* the module supervisor via ``getControllerUnitManager().getMainProcessor()`` // 

* the workflow contains user's configurations of symbolic execution via ``getConfiguration().getWorkflow()``

* the request stop: stop symbolic execution ``getSymbexRequestManager().postRequestStop(this)``

* the event destroy: a signal before the destruction of a given execution context via ``getSymbexEventManager().postEventDestroyCtx(anEC)``



#### SymbexControllerUnitManager (old --> CPU: Central Processor Unit)
C'est le controller/scheduler qui gère l'activation les FAMs dans les différentes phases de l'exécution **(DEPRECATED: voir *section MOE* dans le *fichier SEW/FAVM* de spécification du workflow)**

#### MPU: Main Processor Unit
C'est le FAM principal, toujours actif, ayant la charge de

* gérer les *critèrse d'arrêts absolu* en vue de limité la taille du graphe d'exécution calculé (voir l'objet ``supervisor {  ... }`` *fichier SEW/FAVM* dans le fichier
* détecter les *deadlocks* d'exécution (noeud sans fils en *postprefiltering*)
* diverses traitementents internes, tel l'attribution d'un identifiant (numéro) de largeur dans le graphe d'exécution
* ...


#### Some FAMs
* FAM Coverage (state / transition -- input / output, ...) :pour les analyses dédiées couvertures structurelles des modèles
* FAM Hit or Jump : pour la sélection de comportement à partir de trace fournie par l'utilisateur
* FAM Testing (Online / Offline) : pour calculer un verdict associé à un *objectif de test* en mode *online/offline*

### Internal
Les détails d'implémentation interne !

