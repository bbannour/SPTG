/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCoverageTransitionView.h"

#include "AvmCoverageProcessor.h"

#include <computer/primitive/AvmCommunicationFactory.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/ExpressionConstructor.h>

#include <fml/common/SpecifierElement.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <fam/coverage/BaseCoverageFilter.h>

#include <fam/queue/WaitingStrategy.h>
#include <fam/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>


namespace sep
{


/**
 ***************************************************************************
prototype filter::transition_coverage as &avm::core.filter.PROGRAM_COVERAGE is
	section PROPERTY
		// Nombre de pas de calcul "cumulés" avant de débuter
		// la vérification de la couverture
		@begin_step = 0;

		// Arrète l'exécution dès que la couverture est complète
		@stop = true;

		// Arrète l'exécution au plutôt
		@minimize = true;

		// Arrète l'exécution du chemin courant dès qu'un objectif est atteint
		@break = true;

		// Elagage du graphe des scénarios à la fin de la vérification
		@slice = true;

		// Active l'utilisation d'heuristique
		@heuristic = true;

		// choix de l'heuristique de départ
		// basic | naive | smart | agressive
		@heuristic#start = 'basic';

		// Nombre d'essais d'heuristiques
		@heuristic#trials = 7;

		// Critère de satisfaction du succès des heuristiques
		// taux de couverte / nombre d'élément restant...
		@objective#rate = 95;
		@objective#rest = 5;


		// Choix des contextes avec des transitions
		// [ fortement | faiblement | autre ] tirables

		// Limitations temporaire de la profondeur d'exploration
		@coverage#height = 7;

		// nombre de fois que la limite doit être atteint avant de l'augmenter
		@coverage#height#reached#limit = 42;

		@hit#strongly#random = false;
		@hit#strongly#count = 1;

		@hit#weakly#random = false;
		@hit#weakly#count = 1;

		@hit#other#random = false;
		@hit#other#count = 1;

		@scope = 'DETAILS'; 	// 'INSTANCE' | 'FORM' | 'DETAILS'
	endsection PROPERTY

	// Utilisé pour préciser les machines ou les transitions particulières à couvrir!
	section DETAILS
		@form = spec::ascenseur.ascenseur.controler;
		@instance = spec::ascenseur.ascenseur.enregistrer;

		@transition = spec::ascenseur.ascenseur.aller_a_l_etage.attente.transition#6;
	endsection DETAILS
endprototype
 ***************************************************************************
 */


/**
 * DESTRUCTOR
 */
AvmCoverageTransitionView::~AvmCoverageTransitionView()
{
	if( mExecutableCoverageTable != NULL )
	{
		const ExecutionData & anED =
				mCoverageProcessor.getConfiguration().getMainExecutionData();

		if( mTransitionCoverageTable != NULL )
		{
			avm_size_t endOffset = mTransitionCoverageTable->size();
			for( avm_size_t i = 0 ; i < endOffset ; ++i )
			{
				if( mTransitionCoverageTable->at(i)
					!= mExecutableCoverageTable->at(
						anED.getRuntime(i).getExecutable()->getOffset()) )
				{
					delete( mTransitionCoverageTable->at(i) );
				}
			}

			delete( mTransitionCoverageTable );
		}

		endOffset = mExecutableCoverageTable->size();
		for( avm_size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mExecutableCoverageTable->at(i) != NULL )
			{
				delete( mExecutableCoverageTable->at(i) );
			}
		}

		delete( mExecutableCoverageTable );
	}

	else if( mTransitionCoverageTable != NULL )
	{
		avm_size_t endOffset = mTransitionCoverageTable->size();
		for( avm_size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mTransitionCoverageTable->at(i) != NULL )
			{
				delete( mTransitionCoverageTable->at(i) );
			}
		}

		delete( mTransitionCoverageTable );
	}
}


/**
 * CONFIGURE
 */
bool AvmCoverageTransitionView::configureImpl()
{
	WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		const ExecutionData & anED =
				mCoverageProcessor.getConfiguration().getMainExecutionData();

		mTransitionCoverageTable =
				new ArrayOfBitset(anED.getTableOfRuntime().size(), NULL);

		ExecutableQuery XQuery( mCoverageProcessor.getConfiguration() );

		XQuery.getRuntimeExecutable( mTableofRuntimeExecutable );

		mScope = Specifier::toDesignKind(
				Query::getWPropertyString(thePROPERTY, "scope", "MODEL") );

		switch( mScope )
		{
			case Specifier::DESIGN_INSTANCE_KIND:
			{
				// INITIALISATION de la table de tous les PROGRAM
				// associés à chacune des INSTANCE...
				configureInstanceCoverageTableFlag(false);

				break;
			}

			case Specifier::DESIGN_MODEL_KIND:
			{
				// INITIALISATION de la table de tous les PROGRAM
				// associés à chacune des EXECUTABLE...
				configureExecutableCoverageTableFlag(false);

				break;
			}

			default: // for  << @scope = 'DETAILS'; >>
			{
				WObject * theDETAILS = Query::getRegexWSequence(
						getParameterWObject(), OR_WID2("details", "DETAILS"));

				if( theDETAILS != WObject::_NULL_ )
				{
					ExecutableForm * anExecutable = NULL;
					AvmTransition * aTransition = NULL;

					ListOfExecutableForm listOfExecutable;
					ListOfInstanceOfMachine listOfInstance;
					ListOfAvmTransition listOfTransition;

					WObject::const_iterator itWfO = theDETAILS->owned_begin();
					WObject::const_iterator endWfO = theDETAILS->owned_end();
					for( ; itWfO != endWfO ; ++itWfO )
					{
						if( (*itWfO)->isWProperty() )
						{
							const std::string & kind = (*itWfO)->getNameID();
							const std::string & qnid = (*itWfO)->toStringValue();

							if( (kind == "model") || (kind == "form")  ||
									(kind == "executable") )
							{
								anExecutable =
									XQuery.getExecutableByQualifiedNameID(
											qnid ).to_ptr< ExecutableForm >();
								if( anExecutable != NULL )
								{
									listOfExecutable.append(anExecutable);
								}
								else
								{
									AVM_OS_WARN << "Unfound the machine "
										<< kind << " << " << qnid
										<< " >> as coverage processor parameter:> "
										<< getParameterWObject()
												->getFullyQualifiedNameID()
										<< std::endl;
								}
							}
							else if( kind == "instance" )
							{
								const BF & anInstance = XQuery.searchMachine(
										Specifier::DESIGN_INSTANCE_KIND, qnid);
								if( anInstance.valid() )
								{
									listOfInstance.append(
											anInstance.to_ptr< InstanceOfMachine >());
								}
								else
								{
									AVM_OS_WARN << "Unfound the machine "
										<< kind << " << " << qnid
										<< " >> as coverage processor parameter:> "
										<< getParameterWObject()
												->getFullyQualifiedNameID()
										<< std::endl;
								}
							}
							else if( kind == "transition" )
							{
								aTransition =
									XQuery.getTransitionByQualifiedNameID(
											qnid ).to_ptr< AvmTransition >();
								if( aTransition != NULL )
								{
									listOfTransition.append(aTransition);
								}
								else
								{
									AVM_OS_WARN  << "Unfound the "
										<< kind << " << " << qnid
										<< " >> as coverage processor parameter:> "
										<< getParameterWObject()
												->getFullyQualifiedNameID()
										<< std::endl;
								}
							}
							else if( kind == "program" )
							{
								aTransition =
									XQuery.getTransitionByQualifiedNameID(
											qnid ).to_ptr< AvmTransition >();
								if( aTransition != NULL )
								{
									listOfTransition.append(aTransition);
								}
								else
								{
									AVM_OS_WARN  << "Unfound the "
										<< kind << " << " << qnid
										<< " >> as coverage processor parameter:> "
										<< getParameterWObject()
												->getFullyQualifiedNameID()
										<< std::endl;
								}
							}
							else
							{
								AVM_OS_WARN << "Unexpected attribute << "
									<< (*itWfO)->str()
									<< " >> as coverage processor parameter:> "
									<< getParameterWObject()
											->getFullyQualifiedNameID()
									<< std::endl;
							}
						}
					}


					// INITIALISATION de la table de tous les PROGRAM
					// associés à chacun des EXECUTABLE...
					configureExecutableCoverageTableFlag(true);

					ListOfExecutableForm::iterator itExec = listOfExecutable.begin();
					ListOfExecutableForm::iterator endExec = listOfExecutable.end();
					for( ; itExec != endExec ; ++itExec )
					{
						configureExecutableCoverageTableFlag((*itExec), false);
					}


					// Cas des programmes
					configureTransitionCoverageTableFlag(listOfTransition, false);


					// INITIALISATION de la table de tous les PROGRAM
					// associés à chacune des INSTANCE...
					ListOfInstanceOfMachine::iterator itInst = listOfInstance.begin();
					ListOfInstanceOfMachine::iterator endInst = listOfInstance.end();
					for( ; itInst != endInst ; ++itInst )
					{
						if( (*itInst)->getExecutable()->hasTransition() )
						{
							configureInstanceCoverageTableFlag(anED,
									anED.getRuntimeID(*itInst), false);
						}
					}


					if( mExecutableCoverageTable != NULL)
					{
						if( mTransitionCoverageTable != NULL)
						{
							// INITIALISATION de la table de tous les PROGRAM
							// associés à chacune des INSTANCE...
							configureInstanceCoverageTableFlag();
						}
						else
						{
							mScope = Specifier::DESIGN_MODEL_KIND;
						}
					}
				}
				else
				{
					AVM_OS_WARN << "Unfound section << DETAILS >> "
							"as coverage processor parameter:> "
							<< getParameterWObject()->getFullyQualifiedNameID()
							<< std::endl;
				}

				break;
			}
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "Uncovered Transition Count at the beginning :> "
			<< mCoverageStatistics.mNumberOfElements << std::endl << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	}


	if( (mHeuristicProperty.mCoverageHeightPeriod == 0) ||
		(mHeuristicProperty.mCoverageHeightPeriod == AVM_NUMERIC_MAX_SIZE_T) )
	{
		mHeuristicProperty.mCoverageHeight =
				mHeuristicProperty.mCoverageHeightPeriod = 7;
//						mCoverageStatistics.mNumberOfElements;
	}
	mHeuristicProperty.mCoverageHeightReachedCount = 0;
	mHeuristicProperty.mCoverageHeightReachedFlag = false;

	if( mHeuristicProperty.mCoverageHeightReachedLimit == 0 )
	{
		mHeuristicProperty.mCoverageHeightReachedLimit =
				mCoverageStatistics.mNumberOfElements;
	}


	return mConfigFlag;
}


void AvmCoverageTransitionView::configureExecutableCoverageTableFlag(bool value)
{
	if( mExecutableCoverageTable == NULL )
	{
		mExecutableCoverageTable = new ArrayOfBitset(mCoverageProcessor.
				getConfiguration().getExecutableSystem().size(), NULL);
	}

	Bitset * tableOfFlag = NULL;
	avm_size_t itTransition = 0;
	avm_size_t endTransition = 0;

	VectorOfExecutableForm::iterator itExec = mTableofRuntimeExecutable.begin();
	VectorOfExecutableForm::iterator endExec = mTableofRuntimeExecutable.end();
	for( ; itExec != endExec ; ++itExec )
	{
		if( (*itExec)->hasTransition() )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << "executable :> " << (*itExec)->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			tableOfFlag = mExecutableCoverageTable->at( (*itExec)->getOffset() );
			if( tableOfFlag == NULL )
			{
				tableOfFlag = new Bitset((*itExec)->getTransition().size(), true);

				mExecutableCoverageTable->set((*itExec)->getOffset(), tableOfFlag);
			}

			endTransition = (*itExec)->getTransition().size();
			for( itTransition = 0 ; itTransition < endTransition ; ++itTransition )
			{
				if( (! value) && tableOfFlag->test(itTransition) )
				{
					tableOfFlag->set(itTransition, value);

					if( not value )
					{
						mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
			<< (*itExec)->rawTransition(itTransition)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
					}
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}
		else
		{
			mExecutableCoverageTable->set((*itExec)->getOffset(), NULL);
		}
	}
}


void AvmCoverageTransitionView::configureExecutableCoverageTableFlag(
		ExecutableForm * anExecutable, bool value)
{
	if( mExecutableCoverageTable == NULL )
	{
		mExecutableCoverageTable = new ArrayOfBitset(mCoverageProcessor.
				getConfiguration().getExecutableSystem().size(), NULL);
	}

	if( anExecutable->hasTransition() )
	{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << "executable :> " << anExecutable->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

		Bitset * tableOfFlag =
				mExecutableCoverageTable->at( anExecutable->getOffset() );
		if( tableOfFlag == NULL )
		{
			tableOfFlag = new Bitset(anExecutable->getTransition().size(), true);

			mExecutableCoverageTable->set(anExecutable->getOffset(), tableOfFlag);
		}

		avm_size_t endTransition = anExecutable->getTransition().size();
		avm_size_t itTransition = 0;
		for( ; itTransition < endTransition ; ++itTransition )
		{
			if( (! value) && tableOfFlag->test(itTransition) )
			{
				tableOfFlag->set(itTransition, value);

				mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
			<< anExecutable->rawTransition(itTransition)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
			}
		}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
		AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
	}

	// Cas des sous machine executable
	if( anExecutable->hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator it = anExecutable->instance_static_begin();
		TableOfSymbol::const_iterator endIt = anExecutable->instance_static_end();
		for( ; it != endIt ; ++it )
		{
			configureExecutableCoverageTableFlag((*it).getExecutable(), value);
		}
	}
}


void AvmCoverageTransitionView::configureInstanceCoverageTableFlag()
{
	if( mExecutableCoverageTable != NULL)
	{
		const ExecutionData & anED =
				mCoverageProcessor.getConfiguration().getMainExecutionData();

		RuntimeID aRID;

		if( mTransitionCoverageTable == NULL )
		{
			mTransitionCoverageTable =
					new ArrayOfBitset(anED.getTableOfRuntime().size(), NULL);
		}

		avm_size_t endMachine = mTransitionCoverageTable->size();
		for( avm_size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
		{
			aRID = anED.getRuntimeID(itMachine);
			if( aRID.getExecutable()->hasTransition() &&
					(mTransitionCoverageTable->at(itMachine) == NULL) )
			{
				mTransitionCoverageTable->set(itMachine,
						mExecutableCoverageTable->at(
								aRID.getExecutable()->getOffset()));
			}
		}
	}
}



void AvmCoverageTransitionView::configureInstanceCoverageTableFlag(bool value)
{
	const ExecutionData & anED =
			mCoverageProcessor.getConfiguration().getMainExecutionData();
	RuntimeID aRID;
	Bitset * tableOfFlag = NULL;

	avm_size_t itTransition = 0;
	avm_size_t endTransition = 0;

	if( mTransitionCoverageTable == NULL )
	{
		mTransitionCoverageTable =
				new ArrayOfBitset(anED.getTableOfRuntime().size(), NULL);
	}

	avm_size_t endMachine = mTransitionCoverageTable->size();
	for( avm_size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
	{
		aRID = anED.getRuntimeID(itMachine);
		if( aRID.getExecutable()->hasTransition() )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			tableOfFlag = mTransitionCoverageTable->at( itMachine );
			if( tableOfFlag == NULL )
			{
				tableOfFlag = new Bitset(
						aRID.getExecutable()->getTransition().size(), true);

				mTransitionCoverageTable->set(itMachine, tableOfFlag);
			}

			endTransition = aRID.getExecutable()->getTransition().size();
			for( itTransition = 0 ; itTransition < endTransition ; ++itTransition )
			{
				if( (not value) && tableOfFlag->test(itTransition) )
				{
					tableOfFlag->set(itTransition, value);

					if( not value )
					{
						mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
			<< aRID.getExecutable()->rawTransition(itTransition)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
					}
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}
		else
		{
			mTransitionCoverageTable->set(itMachine, NULL);
		}
	}
}


void AvmCoverageTransitionView::configureInstanceCoverageTableFlag(
		const ExecutionData & anED, const RuntimeID & aRID, bool value)
{
	if( mExecutableCoverageTable == NULL )
	{
		configureExecutableCoverageTableFlag( true );
	}

	if( mTransitionCoverageTable == NULL )
	{
		mTransitionCoverageTable =
				new ArrayOfBitset(anED.getTableOfRuntime().size(), NULL);
	}

	ExecutableForm * anExecutable = aRID.getExecutable();

	if( (anExecutable != NULL) &&
			(mTransitionCoverageTable->at(aRID.getOffset()) == NULL) )
	{
		if( anExecutable->hasTransition() &&
			mExecutableCoverageTable->at(anExecutable->getOffset()) == NULL )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			Bitset * tableOfFlag =
					mTransitionCoverageTable->at( aRID.getOffset() );
			if( tableOfFlag == NULL )
			{
				tableOfFlag = new Bitset(
						anExecutable->getTransition().size(), true);

				mTransitionCoverageTable->set(aRID.getOffset(), tableOfFlag);
			}

			avm_size_t endTransition = anExecutable->getTransition().size();
			avm_size_t itTransition = 0;
			for( ; itTransition < endTransition ; ++itTransition )
			{
				if( (! value) && tableOfFlag->test(itTransition) )
				{
					tableOfFlag->set(itTransition, value);

					mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
			<< anExecutable->rawTransition(itTransition)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}
		else if( anExecutable->hasTransition() )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			Bitset * tableOfFlag =
					mTransitionCoverageTable->at( aRID.getOffset() );
			if( tableOfFlag == NULL )
			{
				tableOfFlag = new Bitset(
						anExecutable->getTransition().size(), true);

				mTransitionCoverageTable->set(aRID.getOffset(), tableOfFlag);
			}

			avm_size_t endTransition = anExecutable->getTransition().size();
			avm_size_t itTransition = 0;
			for( ; itTransition < endTransition ; ++itTransition )
			{
				tableOfFlag->set(itTransition,
						value && mExecutableCoverageTable->at(
								anExecutable->getOffset())->test(itTransition) );

				if( (! value) && mExecutableCoverageTable->at(
						anExecutable->getOffset())->test(itTransition) )
				{
					mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
			<< anExecutable->rawTransition(itTransition)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (! value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}

		// Cas des sous machine instance
		if( anED.getRuntime(aRID).hasChild() )
		{
			TableOfRuntimeID::const_iterator itSubMachine =
					anED.getRuntime(aRID).beginChild();
			TableOfRuntimeID::const_iterator endSubMachine =
					anED.getRuntime(aRID).endChild();
			for( ; itSubMachine != endSubMachine ; ++itSubMachine )
			{
				configureInstanceCoverageTableFlag(anED, (*itSubMachine), value);
			}
		}
	}
}


void AvmCoverageTransitionView::configureTransitionCoverageTableFlag(
		ListOfAvmTransition & listOfTransition, bool value)
{
	if( mExecutableCoverageTable == NULL )
	{
		mExecutableCoverageTable = new ArrayOfBitset(mCoverageProcessor.
				getConfiguration().getExecutableSystem().size(), NULL);
	}

	Bitset * tableOfFlag = NULL;
	avm_offset_t containerExecOffset = 0;

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING ,
		(! value) && listOfTransition.nonempty() )
	AVM_OS_TRACE << "program :> user details" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

	ListOfAvmTransition::iterator itProg = listOfTransition.begin();
	ListOfAvmTransition::iterator endProg = listOfTransition.end();
	for( ; itProg != endProg ; ++itProg )
	{
		containerExecOffset = (*itProg)->getExecutableContainer()->getOffset();

		tableOfFlag = mExecutableCoverageTable->at(containerExecOffset);
		if( tableOfFlag == NULL )
		{
			tableOfFlag = new Bitset(
					(*itProg)->getExecutableContainer()->getTransition().size(), true);

			mExecutableCoverageTable->set(containerExecOffset, tableOfFlag);
		}
		if( (! value) && tableOfFlag->test( (*itProg)->getOffset() ) )
		{
			mExecutableCoverageTable->at( containerExecOffset )->set(
					(*itProg)->getOffset(), value);

			mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> " << (*itProg)->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING ,
		(! value) && listOfTransition.nonempty() )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
}


Bitset * AvmCoverageTransitionView::getCoverageTableBitset(
		const RuntimeID & aRID)
{
	switch( mScope )
	{
		case Specifier::DESIGN_MODEL_KIND:
		{
			return( mExecutableCoverageTable->at(
					aRID.getExecutable()->getOffset() ) );
		}
		case Specifier::DESIGN_INSTANCE_KIND:
		default:
		{
			return( mTransitionCoverageTable->at( aRID.getOffset() ) );
		}
	}
}


/*
 * REPORT
 */
void AvmCoverageTransitionView::reportMinimum(OutStream & os) const
{
	if( mCoverageStatistics.goalAchieved() )
	{
		os << TAB2 << "All the << " << mCoverageStatistics.mNumberOfElements
				<< " >> transitions are covered !" << EOL;
	}
	else
	{
		os << TAB2 << "Warning: all the transitions are not covered !" << EOL;
		mCoverageStatistics.toStreamCoverageRate( os << TAB2,
				"Results: << ", " on "," >> are covered !\n" );

		if( isReportDetails() )
		{
			os << TAB2 << "List of the << "
					<< mCoverageStatistics.getNumberOfUncovered()
					<< " >> transitions non covered:" << EOL2;

			const ExecutionData & anED =
				mCoverageProcessor.getConfiguration().getMainExecutionData();

			RuntimeID aRID;

			StringOutStream oss( os.INDENT );
			bool hasOneUncoverdTransition = false;

			avm_size_t offset;
			avm_size_t endOffset;
			AvmTransition * itTransition;

			switch( mScope )
			{
				case Specifier::DESIGN_INSTANCE_KIND:
				{
					if( mTransitionCoverageTable == NULL )
					{
						break;
					}

					avm_size_t endMachine = mTransitionCoverageTable->size();
					avm_size_t itMachine = 0;
					for( ; itMachine < endMachine ; ++itMachine )
					{
						aRID = anED.getRuntimeID(itMachine);
						if( aRID.getExecutable()->hasTransition() )
						{
							oss.str("");

//							oss << TAB2 << "instance :> " << aRID.getFullyQualifiedNameID() << EOL;
							if( not aRID.getExecutable()->isReachableState() )
							{
								oss << TAB2 << "instance[ NO INCOMING TRANSITION ] :> "
										<< aRID.getFullyQualifiedNameID() << EOL;
							}

							hasOneUncoverdTransition = false;

							endOffset = aRID.getExecutable()->getTransition().size();
							for( offset = 0 ; offset < endOffset ; ++offset )
							{
								itTransition = aRID.getExecutable()->
										getTransition().rawAt(offset);

								if( not mTransitionCoverageTable->
										at( aRID.getOffset() )->test( offset ) )
								{
									hasOneUncoverdTransition = true;
									oss << TAB3 << itTransition->
											strTransitionHeader() << EOL;
								}
							}
							if( hasOneUncoverdTransition )
							{
								os << oss.str() << EOL;
							}
						}
					}

					break;
				}

				case Specifier::DESIGN_MODEL_KIND:
				{
					if( mExecutableCoverageTable == NULL )
					{
						break;
					}

					VectorOfExecutableForm::const_iterator itExec =
							mTableofRuntimeExecutable.begin();
					VectorOfExecutableForm::const_iterator endExec =
							mTableofRuntimeExecutable.end();
					for( avm_size_t indexExec = 0 ; itExec != endExec ;
							++itExec , ++indexExec )
					{
						if( (*itExec)->hasTransition() )
						{
							oss.str("");

//							oss << TAB2 << "model :> " << (*itExec)->getFullyQualifiedNameID() << EOL;
							if( not (*itExec)->isReachableState() )
							{
								oss << TAB2 << "model[ NO INCOMING TRANSITION ] :> "
										<< (*itExec)->getFullyQualifiedNameID() << EOL;
							}

							hasOneUncoverdTransition = false;

							endOffset = (*itExec)->getTransition().size();
							for( offset = 0 ; offset < endOffset ; ++offset )
							{
								itTransition = (*itExec)->getTransition().rawAt(offset);

								if( not mExecutableCoverageTable->
										at((*itExec)->getOffset())->test( offset ) )
								{
									hasOneUncoverdTransition = true;
									oss << TAB3 << itTransition->
											strTransitionHeader() << EOL;
								}
							}
							if( hasOneUncoverdTransition )
							{
								os << oss.str() << EOL;
							}
						}
					}

					break;
				}

				default:
				{
					if( mExecutableCoverageTable != NULL )
					{
						VectorOfExecutableForm::const_iterator itExec =
								mTableofRuntimeExecutable.begin();
						VectorOfExecutableForm::const_iterator endExec =
								mTableofRuntimeExecutable.end();
						for( avm_size_t indexExec = 0 ; itExec != endExec ;
								++itExec , ++indexExec )
						{
							if( (*itExec)->hasTransition() )
							{
								oss.str("");

//								oss << TAB2 << "model :> " << (*itExec)->getFullyQualifiedNameID() << EOL;
								if( not (*itExec)->isReachableState() )
								{
									oss << TAB2 << "model[ NO INCOMING TRANSITION ] :> "
											<< (*itExec)->getFullyQualifiedNameID() << EOL;
								}

								hasOneUncoverdTransition = false;

								endOffset = (*itExec)->getTransition().size();
								for( offset = 0 ; offset < endOffset ; ++offset )
								{
									itTransition = (*itExec)->getTransition().rawAt(offset);

									if( not mExecutableCoverageTable->
											at((*itExec)->getOffset())->test( offset ) )
									{
										hasOneUncoverdTransition = true;
										oss << TAB3 << itTransition->
												strTransitionHeader() << EOL;
									}
								}
								if( hasOneUncoverdTransition )
								{
									os << oss.str() << EOL;
								}
							}
						}
					}

					if( mTransitionCoverageTable != NULL )
					{
						avm_size_t endMachine = mTransitionCoverageTable->size();
						avm_size_t itMachine = 0;
						for( ; itMachine < endMachine ; ++itMachine )
						{
							aRID = anED.getRuntimeID(itMachine);
							if( aRID.getExecutable()->hasTransition() )
							{
								oss.str("");

//								oss << TAB2 << "instance :> " << aRID.getFullyQualifiedNameID() << EOL;
								if( not aRID.getExecutable()->isReachableState() )
								{
									oss << TAB2 << "instance[ NO INCOMING TRANSITION ] :> "
											<< aRID.getFullyQualifiedNameID() << EOL;
								}

								hasOneUncoverdTransition = false;

								endOffset = aRID.getExecutable()->getTransition().size();
								for( offset = 0 ; offset < endOffset ; ++offset )
								{
									itTransition = aRID.getExecutable()->
											getTransition().rawAt(offset);

									if( (not mTransitionCoverageTable->
											at(aRID.getOffset())->test(offset))
										&& mExecutableCoverageTable->
											at(aRID.getExecutable()->getOffset())->
												test(offset) )
									{
										hasOneUncoverdTransition = true;
										oss << TAB3 << itTransition->
												strTransitionHeader() << EOL;
									}
								}
								if( hasOneUncoverdTransition )
								{
									os << oss.str() << EOL;
								}
							}
						}
					}

					break;
				}
			}
		}

		if ( isReportDetails() && mCoverageStatistics.hasUncovered() )
		{
			mCoverageStatistics.toStreamCoverageRate( os << TAB2,
					"Results: << ", " on "," >> are covered !\n" );
		}
	}

//$	if( mSliceFlag )
//	{
//		os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
//$	}

	os << std::flush;
}


void AvmCoverageTransitionView::reportDefault(OutStream & os) const
{
//$	if( mHeuristicFlag )
	{
		os << std::boolalpha
				<< " < ch:"   << mHeuristicProperty.mCoverageHeight
				<< " , chp:"  << mHeuristicProperty.mCoverageHeightPeriod
				<< " , chrl:" << mHeuristicProperty.mCoverageHeightReachedLimit

				<< " ; hcr:"  << mHeuristicProperty.mHitCertainlyRandomFlag
				<< " , hcc:"  << mHeuristicProperty.mHitCertainlyCount

				<< " ; hsr:"  << mHeuristicProperty.mHitStronglyRandomFlag
				<< " , hsc:"  << mHeuristicProperty.mHitStronglyCount

				<< " ; hwr:"  << mHeuristicProperty.mHitWeaklyRandomFlag
				<< " , hwc:"  << mHeuristicProperty.mHitWeaklyCount

				<< " ; hor:"  << mHeuristicProperty.mHitOtherRandomFlag
				<< " , hoc:"  << mHeuristicProperty.mHitOtherCount
				<< " > "
				<< std::noboolalpha;
	}

	os << EOL_FLUSH;

	if( mCoverageStatistics.goalAchieved() )
	{
		os << TAB2 << "All the << " << mCoverageStatistics.mNumberOfElements
				<< " >> transitions are covered !" << EOL;
	}
	else
	{
		os << TAB2 << "Warning: all the transitions are not covered !" << EOL;
		mCoverageStatistics.toStreamCoverageRate( os << TAB2,
				"Results: << ", " on "," >> are covered !\n" );

		if( isReportDetails() )
		{
			os << TAB2 << "List of the << "
					<< mCoverageStatistics.getNumberOfUncovered()
					<<  " >> transitions non covered:" << EOL << EOL;

			const ExecutionData & anED =
				mCoverageProcessor.getConfiguration().getMainExecutionData();

			RuntimeID aRID;

			StringOutStream oss( os.INDENT );
			bool hasOneUncoverdTransition = false;

			avm_size_t offset;
			avm_size_t endOffset;
			AvmTransition * itTransition;

			switch( mScope )
			{
				case Specifier::DESIGN_INSTANCE_KIND:
				{
					if( mTransitionCoverageTable == NULL )
					{
						break;
					}

					avm_size_t endMachine = mTransitionCoverageTable->size();
					avm_size_t itMachine = 0;
					for( ; itMachine < endMachine ; ++itMachine )
					{
						aRID = anED.getRuntimeID(itMachine);
						if( aRID.getExecutable()->hasTransition() )
						{
							oss.str("");

							oss << TAB2 << "instance";
							if( not aRID.getExecutable()->isReachableState() )
							{
								oss << "[ NO INCOMING TRANSITION ]";
							}
							oss << " :> " << aRID.getFullyQualifiedNameID() << EOL;

							hasOneUncoverdTransition = false;

							endOffset = aRID.getExecutable()->getTransition().size();
							for( offset = 0 ; offset < endOffset ; ++offset )
							{
								itTransition = aRID.getExecutable()->
										getTransition().rawAt(offset);

								if( not mTransitionCoverageTable->
										at( aRID.getOffset() )->test( offset ) )
								{
									hasOneUncoverdTransition = true;
									oss << TAB3 << itTransition->
											strTransitionHeader() << EOL;
								}
							}
							if( hasOneUncoverdTransition )
							{
								os << oss.str() << EOL;
							}
						}
					}

					break;
				}

				case Specifier::DESIGN_MODEL_KIND:
				{
					if( mExecutableCoverageTable == NULL )
					{
						break;
					}

					VectorOfExecutableForm::const_iterator itExec =
							mTableofRuntimeExecutable.begin();
					VectorOfExecutableForm::const_iterator endExec =
							mTableofRuntimeExecutable.end();
					for( avm_size_t indexExec = 0 ; itExec != endExec ;
							++itExec , ++indexExec )
					{
						if( (*itExec)->hasTransition() )
						{
							oss.str("");

							oss << TAB2 << "model";
							if( not (*itExec)->isReachableState() )
							{
								oss << "[ NO INCOMING TRANSITION ]";
							}
							oss << " :> " << (*itExec)->getFullyQualifiedNameID() << EOL;

							hasOneUncoverdTransition = false;

							endOffset = (*itExec)->getTransition().size();
							for( offset = 0 ; offset < endOffset ; ++offset )
							{
								itTransition = (*itExec)->getTransition().rawAt(offset);

								if( not mExecutableCoverageTable->
										at((*itExec)->getOffset())->test( offset ) )
								{
									hasOneUncoverdTransition = true;
									oss << TAB3 << itTransition->
											strTransitionHeader() << EOL;
								}
							}
							if( hasOneUncoverdTransition )
							{
								os << oss.str() << EOL;
							}
						}
					}

					break;
				}

				default:
				{
					if( mExecutableCoverageTable != NULL )
					{
						VectorOfExecutableForm::const_iterator itExec =
								mTableofRuntimeExecutable.begin();
						VectorOfExecutableForm::const_iterator endExec =
								mTableofRuntimeExecutable.end();
						avm_size_t indexExec = 0;
						for( ; itExec != endExec ; ++itExec , ++indexExec )
						{
							if( (*itExec)->hasTransition() )
							{
								oss.str("");

								oss << TAB2 << "model";
								if( not (*itExec)->isReachableState() )
								{
									oss << "[ NO INCOMING TRANSITION ]";
								}
								oss << " :> " << (*itExec)->getFullyQualifiedNameID() << EOL;


								hasOneUncoverdTransition = false;

								endOffset = (*itExec)->getTransition().size();
								for( offset = 0 ; offset < endOffset ; ++offset )
								{
									itTransition = (*itExec)->getTransition().rawAt(offset);

									if( not mExecutableCoverageTable->
											at((*itExec)->getOffset())->test( offset ) )
									{
										hasOneUncoverdTransition = true;
										oss << TAB3 << itTransition->
												strTransitionHeader() << EOL;
									}
								}
								if( hasOneUncoverdTransition )
								{
									os << oss.str() << EOL;
								}
							}
						}
					}

					if( mTransitionCoverageTable != NULL )
					{
						avm_size_t endMachine = mTransitionCoverageTable->size();
						avm_size_t itMachine = 0;
						for( ; itMachine < endMachine ; ++itMachine )
						{
							aRID = anED.getRuntimeID(itMachine);
							if( aRID.getExecutable()->hasTransition() )
							{
								oss.str("");

								oss << TAB2 << "instance";
								if( not aRID.getExecutable()->isReachableState() )
								{
									oss << "[ NO INCOMING TRANSITION ]";
								}
								oss << " :> " << aRID.getFullyQualifiedNameID() << EOL;

								hasOneUncoverdTransition = false;

								endOffset = aRID.getExecutable()->getTransition().size();
								for( offset = 0 ; offset < endOffset ; ++offset )
								{
									itTransition = aRID.getExecutable()->
											getTransition().rawAt(offset);

									if( (not mTransitionCoverageTable->
											at(aRID.getOffset())->test(offset))
										&& mExecutableCoverageTable->
											at(aRID.getExecutable()->getOffset())->
												test(offset) )
									{
										hasOneUncoverdTransition = true;
										oss << TAB3 << itTransition->
												strTransitionHeader() << EOL;
									}
								}
								if( hasOneUncoverdTransition )
								{
									os << oss.str() << EOL;
								}
							}
						}
					}

					break;
				}
			}
		}

		if ( isReportDetails() && mCoverageStatistics.hasUncovered() )
		{
			mCoverageStatistics.toStreamCoverageRate( os << TAB2,
					"Results: << ", " on "," >> are covered !\n" );
		}
	}

//$	if( mSliceFlag )
//	{
//		os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
//$	}

	os << std::flush;
}




////////////////////////////////////////////////////////////////////////////////
// PROCESSOR FILTERING API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageTransitionView::prefiltering(ListOfExecutionContext & ecQueue)
{
	mDirectiveFailedFlag = false;
	mDirectiveHitEC = NULL;

	endQueue = ecQueue.end();
	for( itQueue = ecQueue.begin() ; itQueue != endQueue ; ++itQueue )
	{
		if( (*itQueue)->isWeight(WEIGHT_SELECTED_ACHIEVABLE) )
		{
			mDirectiveHitEC = (*itQueue);
		}
		else if( (mDirectiveHitEC == NULL) && (*itQueue)->
				isWeight(WEIGHT_CERTAINLY_ACHIEVABLE) )
		{
			mDirectiveHitEC = (*itQueue);
		}
		else if( (mDirectiveHitEC == NULL) && (*itQueue)->
				isWeight(WEIGHT_STRONGLY_ACHIEVABLE) )
		{
			mDirectiveHitEC = (*itQueue);
		}
	}

	return( true );
}


bool AvmCoverageTransitionView::postfiltering(ListOfExecutionContext & ecQueue)
{
	endQueue = ecQueue.end();
	for( itQueue = ecQueue.begin() ; itQueue != endQueue ; ++itQueue )
	{
		endEC = (*itQueue)->end();
		for( itEC = (*itQueue)->begin() ; (itEC != endEC) ; ++itEC )
		{
//			updateTransitionCoverageTable((*itEC),
//					(*itEC)->getRunnableElementTrace());
			updateCoverageTable( *itEC );

			if( mCoverageStatistics.goalAchieved() )
			{
				return( true );
			}
		}

		if( mDirectiveHitEC == (*itQueue) )
		{
			mDirectiveFailedFlag = mCoverageStatistics.isNewlyFailedStep();
		}
	}

	return( false );
}


void AvmCoverageTransitionView::updateCoverageTable(ExecutionContext * anEC)
{
	updateTransitionCoverageTable(anEC, anEC->getRunnableElementTrace());
}



/**
 * Heuristic << High Priority Context >> implementation
 * REQUEUE_WAITING part
 */
bool AvmCoverageTransitionView::computeHighPriorityContext(
		ListOfExecutionContext & ecQueue,
		WaitingStrategy & aWaitingStrategy)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	mCoverageStatistics.toStreamCoverageRate(AVM_OS_COUT ,
			"Number of covered transitions = ", " / ", "\n");

	mCoverageStatistics.toStreamCoverageRate(AVM_OS_TRACE,
			"Number of covered transitions = ", " / ", "\n");
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	computeWeightOfResult(ecQueue);

	if( mDirectiveFailedFlag && mCoverageStatistics.hasFailedStep() &&
		(mHeuristicProperty.mHitStronglyCount == 1) )
	{
		if( aWaitingStrategy.hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
		{
			//!! NOTHING if Waiting Queue has BFS Strategy
			return( true );
		}
		else
		{
			// goto failedCase:
		}
	}

	// case of found certainly hit EC
	else if( mCertainlyFireableTransitionCount > 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Next [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> Next [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		setHitWeight(mCertainlyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
				mHeuristicProperty.mHitCertainlyRandomFlag,
				mHeuristicProperty.mHitCertainlyCount);

		return( true );
	}

	// case of found strongly hit EC
	else if( mStronglyFireableTransitionCount > 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Next [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> Next [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		setHitWeight(mStronglyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
				mHeuristicProperty.mHitStronglyRandomFlag,
				mHeuristicProperty.mHitStronglyCount);

		return( true );
	}


	// failedCase:
	if( aWaitingStrategy.hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
	{
		mCoverageProcessor.setRequestRequeueWaiting();
	}
//	else if( aWaitingStrategy.hasWaiting(WEIGHT_NON_PRIORITY) )
//	{
//		mCoverageProcessor.setRequest(
//				SymbexControllerRequestManager::AVM_REQUEUE_WAITING_REQUEST);
//	}
	else
	{
		mCoverageProcessor.setRequestHeuristic();
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	if( (mCertainlyFireableTransitionCount == 0) &&
		(mStronglyFireableTransitionCount == 0) &&
		(mWeaklyFireableTransitionCount > 0) )
	{
		AVM_OS_COUT  << "==> Next [ Weakly ] Fireable Count :> "
				<< mWeaklyFireableTransitionCount
				<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
		AVM_OS_TRACE << "==> Next [ Weakly ] Fireable Count :> "
				<< mWeaklyFireableTransitionCount
				<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	return( false );
}


bool AvmCoverageTransitionView::highRequeueWaitingTable(
		WaitingStrategy & aWaitingStrategy,
		avm_uint8_t aWeightMin, avm_uint8_t aWeightMax)
{
	mCoverageStatistics.setFailedHeuristic();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_COUT  << ">>>>>>> REQUEST REQUEUE <<<<<<<" << std::endl;
	AVM_OS_TRACE << ">>>>>>> REQUEST REQUEUE <<<<<<<" << std::endl;

	AVM_IF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
		report(AVM_OS_COUT);
		report(AVM_OS_TRACE);
	AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	do
	{
		mWaitingQueue.clear();

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )
	AVM_OS_TRACE << "AvmCoverageTransitionView::highRequeueWaitingTable :>" << std::endl;
	aWaitingStrategy.toStream(AVM_OS_COUT);
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )

//		aWaitingStrategy.spliceQueueTable(mWaitingQueue, aWeightMax);

		aWeightMin = aWaitingStrategy.splicePriorQueueTable(
				mWaitingQueue, aWeightMin, aWeightMax);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "REQUEUE QUEUE << "
			<< IHeuristicContextWeight::strHeuristicWeight(aWeightMin)
			<< " >> " << std::endl;
	AVM_OS_TRACE << "REQUEUE QUEUE << "
			<< IHeuristicContextWeight::strHeuristicWeight(aWeightMin)
			<< " >> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		mCertainlyHitEC.clear();
		mCertainlyFireableTransitionCount = 0;

		mStronglyHitEC.clear();
		mStronglyFireableTransitionCount = 0;

		mWeaklyHitEC.clear();
		mWeaklyFireableTransitionCount = 0;

		ListOfExecutionContext::iterator ecQueueIt = mWaitingQueue.begin();
		ListOfExecutionContext::iterator ecQueueItEnd = mWaitingQueue.end();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			computeWeight( *ecQueueIt );

			aWaitingStrategy.push( *ecQueueIt );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	if( (*ecQueueIt)->getWeight() <= WEIGHT_CERTAINLY_ACHIEVABLE )
	{
		AVM_OS_COUT  << DEFAULT_WRAP_DATA << "REQUEUE candidate [ <= Certainly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_COUT); AVM_OS_COUT << END_WRAP;
		fireableTransitionTrace(AVM_OS_COUT, (*ecQueueIt)->refExecutionData());

		AVM_OS_TRACE << DEFAULT_WRAP_DATA << "REQUEUE candidate [ <= Certainly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_TRACE); AVM_OS_TRACE << END_WRAP;
		fireableTransitionTrace(AVM_OS_TRACE, (*ecQueueIt)->refExecutionData());
	}

	else if( (*ecQueueIt)->getWeight() <= WEIGHT_STRONGLY_ACHIEVABLE )
	{
		AVM_OS_COUT  << DEFAULT_WRAP_DATA << "REQUEUE candidate [ <= Strongly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_COUT); AVM_OS_COUT << END_WRAP;
		fireableTransitionTrace(AVM_OS_COUT, (*ecQueueIt)->refExecutionData());

		AVM_OS_TRACE << DEFAULT_WRAP_DATA << "REQUEUE candidate [ <= Strongly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_TRACE); AVM_OS_TRACE << END_WRAP;
		fireableTransitionTrace(AVM_OS_TRACE, (*ecQueueIt)->refExecutionData());
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )
	AVM_OS_TRACE << "AvmCoverageTransitionView::highRequeueWaitingTable :>" << std::endl;
	aWaitingStrategy.toStream(AVM_OS_COUT);
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )

		// case of found certainly hit EC
		if( mCertainlyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> REQUEUE candidate [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> REQUEUE candidate [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

		// case of found strongly hit EC
		if( mStronglyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> REQUEUE candidate [ Strongly ] Fireable Count :> "
		<< mStronglyFireableTransitionCount
		<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> REQUEUE candidate [ Strongly ] Fireable Count :> "
		<< mStronglyFireableTransitionCount
		<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

		// case of found weakly hit EC
		if( mWeaklyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> REQUEUE candidate [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> REQUEUE candidate [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
	}
//	while( ((++aWeightMin) <= WEIGHT_NON_PRIORITY) &&
	while( ((++aWeightMin) <= WEIGHT_STRONGLY_ACHIEVABLE) &&
//	while( ((++aWeightMin) <= aWeightMax) &&
			(mCertainlyFireableTransitionCount == 0) &&
			(mStronglyFireableTransitionCount == 0) );

	return( true );
}


/**
 * Heuristic << Any Priority Context >> implementation
 * REQUEUE_WAITING part
 */
bool AvmCoverageTransitionView::computePriorityContext(
		ListOfExecutionContext & ecQueue,
		WaitingStrategy & aWaitingStrategy)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	mCoverageStatistics.toStreamCoverageRate(AVM_OS_COUT ,
			"Number of covered transitions = ", " / ", "\n");

	mCoverageStatistics.toStreamCoverageRate(AVM_OS_TRACE,
			"Number of covered transitions = ", " / ", "\n");
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	computeWeightOfResult(ecQueue);

	// case of found certainly hit EC
	if( mCertainlyFireableTransitionCount > 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Next [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> Next [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		setHitWeight(mCertainlyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
				mHeuristicProperty.mHitCertainlyRandomFlag,
				mHeuristicProperty.mHitCertainlyCount);

		mCoverageProcessor.setRequestHeuristic();

		return( true );
	}

	// case of found strongly hit EC
	if( mStronglyFireableTransitionCount > 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Next [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> Next [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		setHitWeight(mStronglyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
				mHeuristicProperty.mHitStronglyRandomFlag,
				mHeuristicProperty.mHitStronglyCount);

		mCoverageProcessor.setRequestHeuristic();

		return( true );
	}

	// case of found weakly hit EC
	else if( mWeaklyFireableTransitionCount > 0 )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Next [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> Next [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		setHitWeight(mWeaklyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
				mHeuristicProperty.mHitWeaklyRandomFlag,
				mHeuristicProperty.mHitWeaklyCount);

		return( true );
	}

	else if( aWaitingStrategy.hasWaiting( WEIGHT_WEAKLY_ACHIEVABLE) )
	{
		mCoverageProcessor.setRequestRequeueWaiting();
	}
	else
	{
		mCoverageProcessor.setRequestHeuristic();
	}

	return( false );
}


bool AvmCoverageTransitionView::elseRequeueWaitingTable(
		WaitingStrategy & aWaitingStrategy,
		avm_uint8_t aWeightMin, avm_uint8_t aWeightMax)
{
	mCoverageStatistics.setFailedHeuristic();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_COUT  << ">>>>>>> REQUEST REQUEUE <<<<<<<" << std::endl;
	AVM_OS_TRACE << ">>>>>>> REQUEST REQUEUE <<<<<<<" << std::endl;

	AVM_IF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
		report(AVM_OS_COUT);
		report(AVM_OS_TRACE);
	AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	do
	{
		mWaitingQueue.clear();

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )
	AVM_OS_TRACE << "AvmCoverageTransitionView::elseRequeueWaitingTable :>" << std::endl;
	aWaitingStrategy.toStream(AVM_OS_COUT);
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )

//		aWaitingStrategy.spliceQueueTable(mWaitingQueue, aWeightMax);

		aWeightMin = aWaitingStrategy.splicePriorQueueTable(
				mWaitingQueue, aWeightMin, aWeightMax);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "REQUEUE QUEUE << "
			<< IHeuristicContextWeight::strHeuristicWeight(aWeightMin)
			<< " >> " << std::endl;
	AVM_OS_TRACE << "REQUEUE QUEUE << "
			<< IHeuristicContextWeight::strHeuristicWeight(aWeightMin)
			<< " >> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


		mCertainlyHitEC.clear();
		mCertainlyFireableTransitionCount = 0;

		mStronglyHitEC.clear();
		mStronglyFireableTransitionCount = 0;

		mWeaklyHitEC.clear();
		mWeaklyFireableTransitionCount = 0;

		ListOfExecutionContext::iterator ecQueueIt = mWaitingQueue.begin();
		ListOfExecutionContext::iterator ecQueueItEnd = mWaitingQueue.end();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			computeWeight( *ecQueueIt );

			aWaitingStrategy.push( *ecQueueIt );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	if( (*ecQueueIt)->getWeight() <= WEIGHT_CERTAINLY_ACHIEVABLE )
	{
		AVM_OS_COUT  << "REQUEUE candidate [ <= Certainly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_COUT);
		fireableTransitionTrace(AVM_OS_COUT, (*ecQueueIt)->refExecutionData());

		AVM_OS_TRACE << "REQUEUE candidate [ <= Certainly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_TRACE);
		fireableTransitionTrace(AVM_OS_TRACE, (*ecQueueIt)->refExecutionData());
	}

	else if( (*ecQueueIt)->getWeight() <= WEIGHT_STRONGLY_ACHIEVABLE )
	{
		AVM_OS_COUT  << "REQUEUE candidate [ <= Strongly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_COUT);
		fireableTransitionTrace(AVM_OS_COUT, (*ecQueueIt)->refExecutionData());

		AVM_OS_TRACE << "REQUEUE candidate [ <= Strongly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_TRACE);
		fireableTransitionTrace(AVM_OS_TRACE, (*ecQueueIt)->refExecutionData());
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )
	AVM_OS_TRACE << "AvmCoverageTransitionView::elseRequeueWaitingTable :>" << std::endl;
	aWaitingStrategy.toStream(AVM_OS_COUT);
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )

		// case of found certainly hit EC
		if( mCertainlyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> REQUEUE candidate [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> REQUEUE candidate [ Certainly ] Fireable Count :> "
			<< mCertainlyFireableTransitionCount
			<< "  Hit Count : " << mCertainlyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

		// case of found strongly hit EC
		if( mStronglyFireableTransitionCount > 0 )
		{
		AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		AVM_OS_COUT  << "==> REQUEUE candidate [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
		AVM_OS_TRACE << "==> REQUEUE candidate [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
		AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

		// case of found weakly hit EC
		if( mWeaklyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> REQUEUE candidate [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
	AVM_OS_TRACE << "==> REQUEUE candidate [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
	}
	while( ((++aWeightMin) <= WEIGHT_NON_PRIORITY) &&
//	while( ((++aWeightMin) <= aWeightMax) &&
			(mCertainlyFireableTransitionCount == 0) &&
			(mStronglyFireableTransitionCount == 0) );

	if( (mHeuristicProperty.mCoverageHeightReachedCount >
				mHeuristicProperty.mCoverageHeightReachedLimit) &&
		(mCertainlyFireableTransitionCount == 0) &&
		(mStronglyFireableTransitionCount == 0) )
	{
		mHeuristicProperty.mCoverageHeightReachedCount = 0;
		mHeuristicProperty.mCoverageHeightReachedFlag = false;

		mHeuristicProperty.mCoverageHeight +=
				mHeuristicProperty.mCoverageHeightPeriod;

		mHeuristicProperty.mCoverageHeightReachedCount +=
				mHeuristicProperty.mCoverageHeightReachedCount;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << "REQUEUE [ chp: " << mHeuristicProperty.mCoverageHeightPeriod
			<< " ] ==> New Coverage Height :> "
			<< mHeuristicProperty.mCoverageHeight << std::endl;

	AVM_OS_TRACE << "REQUEUE [ chp: " << mHeuristicProperty.mCoverageHeightPeriod
			<< " ] ==> New Coverage Height :> "
			<< mHeuristicProperty.mCoverageHeight << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	}

	return( true );
}


/**
 * Compute Hit Weigth for Execution Context
 */
void AvmCoverageTransitionView::setHitWeight(VectorOfExecutionContext & hitEC,
		avm_uint8_t hitWeight, bool randomFlag, avm_size_t hitCount)
{
	if( randomFlag && (hitCount < hitEC.size()) )
	{
		maxRandomOffset = hitEC.size() - 1;
		randomOffsetBitset.reset();
		randomOffsetBitset.resize(maxRandomOffset + 1, false);

		for( ; 0 < hitCount ; --hitCount )
		{
			do
			{
				offset = RANDOM::gen_uint(0, maxRandomOffset);
			}
			while( randomOffsetBitset[offset] );

			randomOffsetBitset[offset] = true;

			hitEC[ offset ]->setWeight( hitWeight );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl << DEFAULT_WRAP_DATA << "HIT :> ";
	hitEC[ offset ]->traceMinimum(AVM_OS_COUT); AVM_OS_COUT << END_WRAP;
	fireableTransitionTrace(AVM_OS_COUT , hitEC[ offset ]->refExecutionData());

	AVM_OS_TRACE << std::endl << DEFAULT_WRAP_DATA << "HIT :> ";
	hitEC[ offset ]->traceMinimum(AVM_OS_TRACE); AVM_OS_TRACE << END_WRAP;
	fireableTransitionTrace(AVM_OS_TRACE, hitEC[ offset ]->refExecutionData());
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << std::endl;
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	}

	else
	{
		if( hitCount > hitEC.size() )
		{
			hitCount = hitEC.size();
		}
		for( offset = 0 ; offset < hitCount ; ++offset )
		{
			hitEC[ offset ]->setWeight( hitWeight );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl << DEFAULT_WRAP_DATA << "HIT :> ";
	hitEC[ offset ]->traceMinimum(AVM_OS_COUT); AVM_OS_COUT << END_WRAP;
	fireableTransitionTrace(AVM_OS_COUT , hitEC[ offset ]->refExecutionData());

	AVM_OS_TRACE << std::endl << DEFAULT_WRAP_DATA << "HIT :> ";
	hitEC[ offset ]->traceMinimum(AVM_OS_TRACE); AVM_OS_TRACE << END_WRAP;
	fireableTransitionTrace(AVM_OS_TRACE, hitEC[ offset ]->refExecutionData());
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << std::endl;
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	}
}

/*
 * weight: 1  if some transition of leaf EC will  be fired
 * weight: 2  if some transition of leaf EC could be fired
 * weight: 3  else
 */
void AvmCoverageTransitionView::computeWeight(ExecutionContext * anEC)
{
	switch( mHeuristicProperty.mHeuristicClass )
	{
		case IHeuristicClass::HEURISTIC_BASIC_CLASS:
		{
//			computeWeightNaive( anEC );
			computeWeightSmart( anEC );
			break;
		}
		case IHeuristicClass::HEURISTIC_NAIVE_CLASS:
		{
			computeWeightNaive( anEC );
			break;
		}
		case IHeuristicClass::HEURISTIC_SMART_CLASS:
		{
			computeWeightSmart( anEC );
			break;
		}

		case IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS:
		{
			computeWeightAgressive( anEC );
			break;
		}

		case IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS:
		default:
		{
			computeWeightSmart( anEC );
			break;
		}
	}
}


void AvmCoverageTransitionView::computeWeightNaive(ExecutionContext * anEC)
{
	computePriorityWeight(anEC);

	if( checkCertainlyPriorityWeight(anEC) )
	{
		return;
	}

	else if( checkNonPriorityWeight(anEC) )
	{
		return;
	}

	else if( checkStronglyPriorityWeight(anEC) )
	{
		return;
	}
	else if( checkWeaklyPriorityWeight(anEC) )
	{
		return;
	}
	else
	{
		anEC->setWeight( WEIGHT_UNKNOWN_ACHIEVABLE );
	}
}


void AvmCoverageTransitionView::computeWeightSmart(ExecutionContext * anEC)
{
	computePriorityWeight(anEC);

	if( checkCertainlyPriorityWeight(anEC) )
	{
		return;
	}

	if( checkStronglyPriorityWeight(anEC) )
	{
		return;
	}

	else if( checkNonPriorityWeight(anEC) )
	{
		return;
	}

	else if( checkWeaklyPriorityWeight(anEC) )
	{
		return;
	}
	else
	{
		anEC->setWeight( WEIGHT_UNKNOWN_ACHIEVABLE );
	}
}


void AvmCoverageTransitionView::computeWeightAgressive(ExecutionContext * anEC)
{
	computePriorityWeight(anEC);

	if( checkCertainlyPriorityWeight(anEC) )
	{
		return;
	}

	if( checkStronglyPriorityWeight(anEC) )
	{
		return;
	}
	else if( checkWeaklyPriorityWeight(anEC) )
	{
		return;
	}
	else
	{
		anEC->setWeight( WEIGHT_UNKNOWN_ACHIEVABLE );
	}
}


bool AvmCoverageTransitionView::checkNonPriorityWeight(ExecutionContext * anEC)
{
	if( anEC->getHeight() > mHeuristicProperty.mCoverageHeight )
	{
		mHeuristicProperty.mCoverageHeightReachedFlag = true;

		anEC->setWeight( WEIGHT_NON_PRIORITY );

		return( true );
	}
	else if( anEC->getWeight() != WEIGHT_NON_PRIORITY )
	{
		if( isTrivialLoop(anEC) )
		{
			anEC->setWeight( WEIGHT_NON_ACHIEVABLE );

			return( true );
		}

//		if( isSyntaxicLoop(anEC) )
//		{
//			anEC->setWeight( WEIGHT_NON_ACHIEVABLE );
//
//			return( true );
//		}

		else if( isControlLoop(anEC) )
		{
			anEC->setWeight( WEIGHT_NON_PRIORITY );

			return( true );
		}
	}

	return( false );
}


void AvmCoverageTransitionView::computePriorityWeight(ExecutionContext * anEC)
{
	tmpCertainlyFireableTransitionCount = 0;
	tmpStronglyFireableTransitionCount = 0;
	tmpWeaklyFireableTransitionCount = 0;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << ":> from ";  anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_TRACE << ":> from ";  anEC->traceMinimum(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	// compute :>
//	fireableTransitionCount( anEC->getAPExecutionData() );
	fireableTransitionCount( anEC->refExecutionData() ,
			anEC->refExecutionData().getSystemRuntime() );
}



bool AvmCoverageTransitionView::checkCertainlyPriorityWeight(
		ExecutionContext * anEC)
{
	if( tmpCertainlyFireableTransitionCount > 0 )
	{
		anEC->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

		if( mCertainlyFireableTransitionCount <
				tmpCertainlyFireableTransitionCount )
		{
			mCertainlyFireableTransitionCount =
					tmpCertainlyFireableTransitionCount;

			mCertainlyHitEC.clear();
			mCertainlyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> HIT EC [ Certain : "
			<< mCertainlyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << std::flush;

	AVM_OS_TRACE << "==> HIT EC [ Certain : "
			<< mCertainlyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			return( true );
		}

		else if( mCertainlyFireableTransitionCount ==
				tmpCertainlyFireableTransitionCount )
		{
			mCertainlyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> HIT EC [ Certain : "
			<< mCertainlyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << std::flush;

	AVM_OS_TRACE << "==> HIT EC [ Certain : "
			<< mCertainlyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		}

		return( true );
	}

	return( false );
}


bool AvmCoverageTransitionView::checkStronglyPriorityWeight(
		ExecutionContext * anEC)
{
	if( tmpStronglyFireableTransitionCount > 0 )
	{
		anEC->setWeight( WEIGHT_STRONGLY_ACHIEVABLE );

		if( mStronglyFireableTransitionCount <
				tmpStronglyFireableTransitionCount )
		{
			mStronglyFireableTransitionCount =
					tmpStronglyFireableTransitionCount;

			mStronglyHitEC.clear();
			mStronglyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> HIT EC [ Strong : "
			<< mStronglyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << std::flush;

	AVM_OS_TRACE << "==> HIT EC [ Strong : "
			<< mStronglyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			return( true );
		}

		else if( mStronglyFireableTransitionCount ==
				tmpStronglyFireableTransitionCount )
		{
			mStronglyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> HIT EC [ Strong : "
			<< mStronglyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << std::flush;

	AVM_OS_TRACE << "==> HIT EC [ Strong : "
			<< mStronglyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		}

		return( true );
	}

	return( false );
}


bool AvmCoverageTransitionView::checkWeaklyPriorityWeight(
		ExecutionContext * anEC)
{
	if( tmpWeaklyFireableTransitionCount > 0 )
	{
		anEC->setWeight( WEIGHT_WEAKLY_ACHIEVABLE );

		if( mWeaklyFireableTransitionCount <
				tmpWeaklyFireableTransitionCount )
		{
			mWeaklyFireableTransitionCount =
					tmpWeaklyFireableTransitionCount;

			mWeaklyHitEC.clear();
			mWeaklyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> HIT EC [ Weak : "
			<< mWeaklyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << std::flush;

	AVM_OS_TRACE << "==> HIT EC [ Weak : "
			<< mWeaklyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			return( true );
		}

		else if( mWeaklyFireableTransitionCount ==
				tmpWeaklyFireableTransitionCount )
		{
			mWeaklyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> HIT EC [ Weak : "
			<< mWeaklyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << std::flush;

	AVM_OS_TRACE << "==> HIT EC [ Weak : "
			<< mWeaklyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		}

		return( true );
	}

	return( false );
}


void AvmCoverageTransitionView::computeWeightOfResult(
		const ListOfExecutionContext & ecQueue)
{
	mCertainlyHitEC.clear();
	mCertainlyFireableTransitionCount = 0;

	mStronglyHitEC.clear();
	mStronglyFireableTransitionCount = 0;

	mWeaklyHitEC.clear();
	mWeaklyFireableTransitionCount = 0;

	ListOfExecutionContext::const_iterator ecQueueIt = ecQueue.begin();
	ListOfExecutionContext::const_iterator ecQueueItEnd = ecQueue.end();
	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
	{
		endEC = (*ecQueueIt)->end();
		for( itEC = (*ecQueueIt)->begin() ; (itEC != endEC) ; ++itEC )
		{
			computeWeight( *itEC );

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//	if( (*itEC)->getWeight() == WEIGHT_CERTAINLY_ACHIEVABLE )
//	{
//		fireableTransitionTrace(AVM_OS_COUT , (*itEC)->getAPExecutionData());
//		fireableTransitionTrace(AVM_OS_TRACE, (*itEC)->getAPExecutionData());
//	}
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
	}

	// Count one time per step CoverageHeightReached
	if( mHeuristicProperty.mCoverageHeightReachedFlag )
	{
		++mHeuristicProperty.mCoverageHeightReachedCount;

		mHeuristicProperty.mCoverageHeightReachedFlag = false;
	}
}


avm_uint8_t AvmCoverageTransitionView::checkFireability(
		const ExecutionData & anED, const RuntimeID & aRID,
		AvmTransition * aTransition)
{
	if( aTransition->hasCode() && aTransition->getCode()->nonempty() &&
			aTransition->getCode()->first().is< AvmCode >() )
	{
		const AvmCode * firstStatement =
				aTransition->getCode()->first().to_ptr< AvmCode >();

		switch( firstStatement->getOptimizedOpCode() )
		{
			case AVM_OPCODE_INPUT_ENV:
			case AVM_OPCODE_OUTPUT_ENV:
			{
				if( aTransition->isStatementBasicFamily() )
				{
					return( WEIGHT_CERTAINLY_ACHIEVABLE );
				}
				else if( aTransition->hasConditionalComStatementFamily() )
				{
					return( WEIGHT_WEAKLY_ACHIEVABLE );
				}
				else
				{
					return( WEIGHT_STRONGLY_ACHIEVABLE );
				}
			}
			default:
			{
				if( firstStatement->isOpCode( AVM_OPCODE_INPUT ) &&
					firstStatement->first().is< InstanceOfPort >() )
				{
					if( AvmCommunicationFactory::computePresence(anED, aRID,
							firstStatement->first().to_ptr< InstanceOfPort >()) )
					{
						if( aTransition->hasStatementGuardFamily() )
						{
							return( WEIGHT_STRONGLY_ACHIEVABLE );
						}
						else
						{
							return( WEIGHT_CERTAINLY_ACHIEVABLE );
						}
					}
					else
					{
						return( WEIGHT_WEAKLY_ACHIEVABLE );
					}
				}

				else if( aTransition->isStatementBasicFamily() )
				{
					return( WEIGHT_CERTAINLY_ACHIEVABLE );
				}
				else if( aTransition->hasConditionalComStatementFamily() )
				{
					return( WEIGHT_STRONGLY_ACHIEVABLE );
				}
			}
		}
	}

	return( WEIGHT_SELECTED_ACHIEVABLE );
}


void AvmCoverageTransitionView::computeFireability(const ExecutionData & anED,
		const RuntimeID & aRID, AvmTransition * aTransition)
{
	switch( checkFireability(anED, aRID, aTransition) )
	{
		case WEIGHT_CERTAINLY_ACHIEVABLE:
		{
			tmpCertainlyFireableTransitionCount += 1;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Fireable [ Certainly ] :> "
			<< aTransition->strTransitionHeader() << std::endl;
	AVM_OS_TRACE << "==> Fireable [ Certainly ] :> "
			<< aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			break;
		}

		case WEIGHT_STRONGLY_ACHIEVABLE:
		{
			tmpStronglyFireableTransitionCount += 1;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "==> Fireable [ Strongly ] :> "
			<< aTransition->strTransitionHeader() << std::endl;
	AVM_OS_TRACE << "==> Fireable [ Strongly ] :> "
			<< aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			break;
		}

		case WEIGHT_WEAKLY_ACHIEVABLE:
		default:
		{
			tmpWeaklyFireableTransitionCount += 1;
		}
	}
}


void AvmCoverageTransitionView::traceFireability(
		OutStream & os, const ExecutionData & anED,
		const RuntimeID & aRID, AvmTransition * aTransition)
{
	switch( checkFireability(anED, aRID, aTransition) )
	{
		case WEIGHT_CERTAINLY_ACHIEVABLE:
		{
			os << "==> [ Certainly ] Fireable :> "
					<< aTransition->strTransitionHeader()
					<< std::endl;

			break;
		}

		case WEIGHT_STRONGLY_ACHIEVABLE:
		{
			os << "==> [ Strongly ] Fireable :> "
					<< aTransition->strTransitionHeader()
					<< std::endl;

			break;
		}

		case WEIGHT_WEAKLY_ACHIEVABLE:
		default:
		{
			os << "==> [ Weakly ] Fireable :> "
					<< aTransition->strTransitionHeader()
					<< std::endl;
		}
	}
}


bool AvmCoverageTransitionView::isControlLoop(ExecutionContext * anEC)
{
	for( tmpEC = anEC->getPrevious() ; tmpEC != NULL ; tmpEC = tmpEC->getPrevious() )
	{
		if( anEC->refExecutionData().getRuntimeFormStateTable()->equalsState(
				tmpEC->refExecutionData().getRuntimeFormStateTable() ) )
		{
			return( true );
		}
	}
	return( false );
}


bool AvmCoverageTransitionView::isSyntaxicLoop(ExecutionContext * anEC)
{
	tmpEC = anEC->getPrevious();
	for( ; tmpEC != NULL ; tmpEC = tmpEC->getPrevious() )
	{
		if( anEC->refExecutionData().getRuntimeFormStateTable()->equalsState(
				tmpEC->refExecutionData().getRuntimeFormStateTable() ) )
		{
			return( true );
		}
	}
	return( false );
}


bool AvmCoverageTransitionView::isTrivialLoop(ExecutionContext * anEC)
{
	tmpEC = anEC->getPrevious();
	for( ; tmpEC != NULL ; tmpEC = tmpEC->getPrevious() )
	{
		if( anEC->refExecutionData().isTEQ( tmpEC->getExecutionData() ) )
		{
			return( true );
		}
	}
	return( false );
}


void AvmCoverageTransitionView::fireableTransitionCount(
		const ExecutionData & anED, const RuntimeID & aRID)
{
	tmpEF = aRID.getExecutable();

	tmpRuntimeTransitionBitset = getCoverageTableBitset( aRID );

	if( tmpRuntimeTransitionBitset == NULL )
	{
		//!! NOTHING
	}
	//tmpEF->hasTransition()
	else if( tmpRuntimeTransitionBitset->anyFalse() )
	{
		AvmTransition * aTransition;

		avm_size_t endOffset = tmpEF->getTransition().size();
		for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
		{
			aTransition = tmpEF->getTransition().rawAt(offset);

			if( not tmpRuntimeTransitionBitset->test(aTransition->getOffset()) )
			{
				computeFireability(anED, aRID, aTransition);
			}
		}
	}

//	else if( tmpRuntimeTransitionBitset->allTrue() )
//	{
//		anED.setRuntimeFormState(itRID, PROCESS_SUSPENDED_STATE);
//	}
}


void AvmCoverageTransitionView::fireableTransitionCount(
		const ExecutionData & anED)
{
	avm_size_t offset;
	avm_size_t endOffset;
	AvmTransition * aTransition;

	itRF = anED.getTableOfRuntime().begin();
	endRF = anED.getTableOfRuntime().end();
	for( ; (itRF != endRF) ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( not anED.isIdleOrRunning( itRID ) )
		{
			continue;
		}

		tmpEF = itRID.getExecutable();

		tmpRuntimeTransitionBitset = getCoverageTableBitset( itRID );

		if( tmpRuntimeTransitionBitset == NULL )
		{
			//!! NOTHING
		}
		//tmpEF->hasTransition()
		else if( anED.isIdleOrRunning( itRID ) &&
				tmpRuntimeTransitionBitset->anyFalse() )
		{
			endOffset = tmpEF->getTransition().size();
			for( offset = 0 ; offset < endOffset ; ++offset )
			{
				aTransition = tmpEF->getTransition().rawAt(offset);

				if( not tmpRuntimeTransitionBitset->
						test(aTransition->getOffset()) )
				{
					computeFireability(anED, itRID, aTransition);
				}
			}
		}

//		else if( tmpRuntimeTransitionBitset->allTrue() )
//		{
//			anED.setRuntimeFormState(itRID, PROCESS_SUSPENDED_STATE);
//		}

	}
}


void AvmCoverageTransitionView::fireableTransitionCount(
		const ExecutionData & anED, const RuntimeForm & aRF)
{
	if( not anED.isIdleOrRunning( aRF.getRID() ) )
	{
		return;
	}

	tmpEF = aRF.getRID().getExecutable();

	if( tmpEF->hasTransition() )
	{
		tmpRuntimeTransitionBitset = getCoverageTableBitset( aRF.getRID() );

		if( tmpRuntimeTransitionBitset->anyFalse() )
		{
			AvmTransition * atransition = NULL;

			avm_size_t endOffset = tmpEF->getTransition().size();
			for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				atransition = tmpEF->getTransition().rawAt(offset);

				if( not tmpRuntimeTransitionBitset->test(atransition->getOffset()) )
				{
					computeFireability(anED,  aRF.getRID(), atransition);
				}
			}
		}
	}

	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		for( ; itRID != itRIDEnd ; ++itRID )
		{
			if( anED.isIdleOrRunning( *itRID ) )
			{
				fireableTransitionCount(anED, anED.getRuntime(*itRID));
			}
		}
	}
}



void AvmCoverageTransitionView::fireableTransitionTrace(
		OutStream & os, const ExecutionData & anED)
{
	avm_size_t offset;
	avm_size_t endOffset;
	AvmTransition * aTransition = NULL;

	itRF = anED.getTableOfRuntime().begin();
	endRF = anED.getTableOfRuntime().end();
	for( ; (itRF != endRF) ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		tmpEF = itRID.getExecutable();

		tmpRuntimeTransitionBitset = getCoverageTableBitset( itRID );

		if( tmpRuntimeTransitionBitset == NULL )
		{
			//!! NOTHINGclass APExecutionData;

		}
		//tmpEF->hasTransition()
		else if( anED.isIdleOrRunning( itRID ) )
		{
			if( tmpRuntimeTransitionBitset->anyFalse() )
			{
				endOffset = tmpEF->getTransition().size();
				for( offset = 0 ; offset < endOffset ; ++offset )
				{
					aTransition = tmpEF->getTransition().rawAt(offset);

					if( not tmpRuntimeTransitionBitset->
							test(aTransition->getOffset()) )
					{
						traceFireability(os,
								anED, itRID, aTransition);
					}
				}
			}
//			else if( tmpRuntimeTransitionBitset->allTrue() )
//			{
//				os << "==> [ suspended ! ] machine :> "
//						<< (*itRF)->getFullyQualifiedNameID() << std::endl;
//			}
		}
	}
}


void AvmCoverageTransitionView::fireableTransitionTrace(OutStream & os,
		const ExecutionData & anED, const RuntimeForm & aRF)
{
	tmpEF = aRF.getRID().getExecutable();

	if( tmpEF->hasTransition() )
	{
		tmpRuntimeTransitionBitset = getCoverageTableBitset( aRF.getRID() );

		if( tmpRuntimeTransitionBitset->anyFalse() )
		{
			AvmTransition * aTransition = NULL;

			avm_size_t endOffset = tmpEF->getTransition().size();
			for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				aTransition = tmpEF->getTransition().rawAt(offset);

				if( not tmpRuntimeTransitionBitset->test(
						aTransition->getOffset()) )
				{
					traceFireability(os, anED, aRF.getRID(), aTransition);
				}
			}
		}
	}

	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		for( ; itRID != itRIDEnd ; ++itRID )
		{
			if( anED.isIdleOrRunning( *itRID ) )
			{
				fireableTransitionTrace(os, anED, anED.getRuntime(*itRID));
			}
		}
	}
}


/**
 * updateTransitionCoverageTable using new fresh Execution Context
 */
void AvmCoverageTransitionView::updateTransitionCoverageTable(
		ExecutionContext * anEC, const BF & aFiredCode)
{
	if( aFiredCode.invalid() )
	{
		return;
	}

	// Vérification de la création de nouvelle instance dynamique
	// par la commande ${ NEW , EXEC }
	if( (mScope != Specifier::DESIGN_MODEL_KIND) &&
			(anEC->refExecutionData().getTableOfRuntime().size() >
					mTransitionCoverageTable->size()) )
	{
		//TODO
		return;
	}

	switch( aFiredCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const BFCode & anAvmCode = aFiredCode.bfCode();

			AvmCode::iterator itEnd = anAvmCode->end();
			for( AvmCode::iterator it = anAvmCode->begin() ; it != itEnd ; ++it )
			{
				updateTransitionCoverageTable(anEC, (*it));
			}

			break;
		}

		case FORM_EXECUTION_CONFIGURATION_KIND:
		{
			ExecutionConfiguration * anExecConf =
					aFiredCode.to_ptr< ExecutionConfiguration >();

			if( anExecConf->isTransition() )
			{
				updateTransitionCoverageTable(anEC,
						anExecConf->getRuntimeID(), anExecConf->getTransition());

//				AvmTransition * firedTransition = anExecConf->getTransition();
//
//				if( not mTransitionCoverageTable->
//						at( anExecConf->getRuntimeID().getOffset() )->
//						test( firedTransition->getOffset() ) )
//				{
//					mCoverageStatistics.addCoveredElement();
//
//					mTransitionCoverageTable->at(
//							anExecConf->getRuntimeID().getOffset() )->
//									set(firedTransition->getOffset(), true);
//
//					if( mExecutableCoverageTable != NULL )
//					{
//						mExecutableCoverageTable->at( firedTransition->
//								getExecutableContainer()->getOffset() )->
//										set(firedTransition->getOffset(), true);
//					}
//
//					anEC->addInfo(mCoverageProcessor,
//							ExpressionConstructor::newString(
//									firedTransition->getNameID()) );
//
//					mListOfPositiveEC.append( anEC );
			}

			break;
		}

		default:
		{
			break;
		}
	}
}


void AvmCoverageTransitionView::updateTransitionCoverageTable(
		ExecutionContext * anEC, const RuntimeID & aRID,
		AvmTransition * firedTransition)
{
	bool isNewlyCovered = false;

	switch( mScope )
	{
		case Specifier::DESIGN_MODEL_KIND:
		{
			if( not mExecutableCoverageTable->at( firedTransition->
					getExecutableContainer()->getOffset() )->
							test(firedTransition->getOffset()) )
			{
				isNewlyCovered = true;

				mExecutableCoverageTable->at( firedTransition->
						getExecutableContainer()->getOffset() )->
								set(firedTransition->getOffset(), true);
			}

			break;
		}

		case Specifier::DESIGN_INSTANCE_KIND:
		{
			if( not mTransitionCoverageTable->at( aRID.getOffset() )->
					test( firedTransition->getOffset() ) )
			{
				isNewlyCovered = true;

				mTransitionCoverageTable->at( aRID.getOffset() )->
						set(firedTransition->getOffset(), true);
			}

			break;
		}

		default:
		{
			if( not mTransitionCoverageTable->at( aRID.getOffset() )->
					test( firedTransition->getOffset() ) )
			{
				isNewlyCovered = true;

				mTransitionCoverageTable->at( aRID.getOffset() )->
						set(firedTransition->getOffset(), true);

				if( mExecutableCoverageTable != NULL )
				{
					mExecutableCoverageTable->at( firedTransition->
							getExecutableContainer()->getOffset() )->
									set(firedTransition->getOffset(), true);
				}
			}

			break;
		}
	}


	if( isNewlyCovered )
	{
		mCoverageStatistics.addCoveredElement();

		anEC->getwFlags().addCoverageElementTrace();

		anEC->addInfo(mCoverageProcessor,
				ExpressionConstructor::newString( firedTransition->getNameID() ));

//$		mListOfPositiveEC.append( anEC );
	}
}


bool AvmCoverageTransitionView::testTransitionCoverage(
		AvmTransition * firedTransition)
{
	switch( mScope )
	{
		case Specifier::DESIGN_MODEL_KIND:
		{
			return( mExecutableCoverageTable->at( firedTransition->
					getExecutableContainer()->getOffset() )->
							test(firedTransition->getOffset()) );
		}

		case Specifier::DESIGN_INSTANCE_KIND:
		{
//			return( mTransitionCoverageTable->at( aRID.getOffset() )->
//					test( firedTransition->getOffset() ) );

			return( true );
		}

		default:
		{
			return( (mExecutableCoverageTable != NULL) ||
					mExecutableCoverageTable->at( firedTransition->
					getExecutableContainer()->getOffset() )->
							test(firedTransition->getOffset()) );
		}
	}
}


/**
 * Update uncovered transition table
 */
void AvmCoverageTransitionView::updateUncoveredTransition(
		VectorOfAvmTransition & aTableofUncoveredTransition)
{
	avm_size_t endTransition = aTableofUncoveredTransition.size();
	avm_size_t uncoveredOffset = 0;

	avm_size_t offset = 0;
	for( ; offset < endTransition ; ++offset )
	{
		if( not testTransitionCoverage( aTableofUncoveredTransition[offset] ) )
		{
			uncoveredOffset = offset;
			break;
		}
	}

	for( ++offset ; offset < endTransition ; ++offset )
	{
		if( not testTransitionCoverage(aTableofUncoveredTransition[offset]) )
		{
			aTableofUncoveredTransition[ uncoveredOffset++ ] =
					aTableofUncoveredTransition[ offset ];
		}
	}

	aTableofUncoveredTransition.resize( uncoveredOffset );


AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "AvmCoverageTransitionView::updateUncoveredTransition:> count: "
			<< aTableofUncoveredTransition.size() << std::endl;
	AVM_OS_TRACE << "AvmCoverageTransitionView::updateUncoveredTransition:> count: "
			<< aTableofUncoveredTransition.size() << std::endl;

	VectorOfAvmTransition::const_iterator itTransition = aTableofUncoveredTransition.begin();
	VectorOfAvmTransition::const_iterator endTransition = aTableofUncoveredTransition.end();
	for( ; itTransition != endTransition ; ++itTransition )
	{
		AVM_OS_COUT << "\t"  << (*itTransition)->strTransitionHeader() << std::endl;

		AVM_OS_TRACE << "\t" << (*itTransition)->strTransitionHeader() << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
}


/**
 * Collect all uncovered transition
 */
//void AvmCoverageTransitionView::collectUncoveredTransition(
//		VectorOfAvmTransition & aTableofUncoveredTransition)
//{
//	const ExecutionData & anED =
//			mCoverageProcessor.getConfiguration().getMainExecutionData();
//
//	RuntimeID aRID;
//
//	avm_size_t offset;
//	avm_size_t endOffset;
//	AvmTransition * itTransition;
//
//	switch( mScope )
//	{
//		case Specifier::DESIGN_INSTANCE_KIND:
//		{
//			if( mTransitionCoverageTable == NULL )
//			{
//				break;
//			}
//
//			avm_size_t endMachine = mTransitionCoverageTable->size();
//			for( avm_size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
//			{
//				aRID = anED.getRuntimeID(itMachine);
//				if( aRID.getExecutable()->hasTransition() )
//				{
//					endOffset = aRID.getExecutable()->getTransition().size();
//					for( offset = 0 ; offset < endOffset ; ++offset )
//					{
//						itTransition = aRID.getExecutable()->getTransition().rawAt(offset);
//
//						if( not mTransitionCoverageTable->
//								at( aRID.getOffset() )->test( offset ) )
//						{
//							aTableofUncoveredTransition.append( itTransition );
//
//							if( aTableofUncoveredTransition.size() >=
//								mCoverageStatistics.getNumberOfUncovered() )
//							{
////								return( true );
//								goto endComputing;
//							}
//						}
//					}
//				}
//			}
//
//			break;
//		}
//
//		case Specifier::DESIGN_MODEL_KIND:
//		{
//			if( mExecutableCoverageTable == NULL )
//			{
//				break;
//			}
//
//			VectorOfExecutableForm::const_iterator itExec =
//					mTableofRuntimeExecutable.begin();
//			VectorOfExecutableForm::const_iterator endExec =
//					mTableofRuntimeExecutable.end();
//			for( avm_size_t indexExec = 0 ; itExec != endExec ;
//					++itExec , ++indexExec )
//			{
//				if( (*itExec)->hasTransition() )
//				{
//					endOffset = (*itExec)->getTransition().size();
//					for( offset = 0 ; offset < endOffset ; ++offset )
//					{
//						itTransition = (*itExec)->getTransition().rawAt(offset);
//
//						if( not mExecutableCoverageTable->
//								at((*itExec)->getOffset())->test( offset ) )
//						{
//							aTableofUncoveredTransition.append( itTransition );
//
//							if( aTableofUncoveredTransition.size() >=
//								mCoverageStatistics.getNumberOfUncovered() )
//							{
////								return( true );
//								goto endComputing;
//							}
//						}
//					}
//				}
//			}
//
//			break;
//		}
//
//		default:
//		{
//			if( mExecutableCoverageTable != NULL )
//			{
//				VectorOfExecutableForm::const_iterator itExec =
//						mTableofRuntimeExecutable.begin();
//				VectorOfExecutableForm::const_iterator endExec =
//						mTableofRuntimeExecutable.end();
//				for( avm_size_t indexExec = 0 ; itExec != endExec ;
//						++itExec , ++indexExec )
//				{
//					if( (*itExec)->hasTransition() )
//					{
//						endOffset = (*itExec)->getTransition().size();
//						for( offset = 0 ; offset < endOffset ; ++offset )
//						{
//							itTransition = (*itExec)->getTransition().rawAt(offset);
//
//							if( not mExecutableCoverageTable->
//									at((*itExec)->getOffset())->test( offset ) )
//							{
//								aTableofUncoveredTransition.append( itTransition );
//
//								if( aTableofUncoveredTransition.size() >=
//									mCoverageStatistics.getNumberOfUncovered() )
//								{
////									return( true );
//									goto endComputing;
//								}
//							}
//						}
//					}
//				}
//			}
//
//			if( mTransitionCoverageTable != NULL )
//			{
//				avm_size_t endMachine = mTransitionCoverageTable->size();
//				for( avm_size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
//				{
//					aRID = anED.getRuntimeID(itMachine);
//					if( aRID.getExecutable()->hasTransition() )
//					{
//						endOffset = aRID.getExecutable()->getTransition().size();
//						for( offset = 0 ; offset < endOffset ; ++offset )
//						{
//							itTransition = aRID.getExecutable()->getTransition().rawAt(offset);
//
//							if( (not mTransitionCoverageTable->
//									at(aRID.getOffset())->test(offset))
//								&& mExecutableCoverageTable->
//									at(aRID.getExecutable()->getOffset())->test(offset) )
//							{
//								aTableofUncoveredTransition.append( itTransition );
//
//								if( aTableofUncoveredTransition.size() >=
//									mCoverageStatistics.getNumberOfUncovered() )
//								{
////									return( true );
//									goto endComputing;
//								}
//							}
//						}
//					}
//				}
//			}
//
//			break;
//		}
//	}
//
//
//endComputing:
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//	AVM_OS_COUT  << "AvmCoverageTransitionView::collectUncoveredTransition:> count: "
//			<< aTableofUncoveredTransition.size() << std::endl;
//	AVM_OS_TRACE << "AvmCoverageTransitionView::collectUncoveredTransition:> count: "
//			<< aTableofUncoveredTransition.size() << std::endl;
//
//	VectorOfAvmTransition::const_iterator itTransition = aTableofUncoveredTransition.begin();
//	VectorOfAvmTransition::const_iterator endTransition = aTableofUncoveredTransition.end();
//	for( ; itTransition != endTransition ; ++itTransition )
//	{
//		AVM_OS_COUT << "\t"  << (*itTransition)->strTransitionHeader() << std::endl;
//
//		AVM_OS_TRACE << "\t" << (*itTransition)->strTransitionHeader() << std::endl;
//	}
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//}



inline static bool isPertinent(AvmTransition * aTransition)
{
	if( aTransition->hasTarget() )
	{
		return( not aTransition->isUnstableTarget() );
	}

	return( not aTransition->isUnstableSource() );
}


void AvmCoverageTransitionView::collectUncoveredTransition(
		VectorOfAvmTransition & aTableofUncoveredTransition)
{
	const ExecutionData & anED =
			mCoverageProcessor.getConfiguration().getMainExecutionData();

	RuntimeID aRID;

	avm_size_t offset;
	avm_size_t endOffset;
	AvmTransition * itTransition;

	avm_size_t uncoveredCount = 0;

	VectorOfAvmTransition nonPertinentTransition;

	switch( mScope )
	{
		case Specifier::DESIGN_INSTANCE_KIND:
		{
			if( mTransitionCoverageTable == NULL )
			{
				break;
			}

			avm_size_t endMachine = mTransitionCoverageTable->size();
			for( avm_size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
			{
				aRID = anED.getRuntimeID(itMachine);
				if( aRID.getExecutable()->hasTransition() )
				{
					endOffset = aRID.getExecutable()->getTransition().size();
					for( offset = 0 ; offset < endOffset ; ++offset )
					{
						itTransition = aRID.getExecutable()->
								getTransition().rawAt(offset);

						if( not mTransitionCoverageTable->
								at( aRID.getOffset() )->test( offset ) )
						{
							++uncoveredCount;

							if( isPertinent( itTransition ) )
							{
								aTableofUncoveredTransition.append( itTransition );
							}
							else
							{
								nonPertinentTransition.append( itTransition );
							}

							if( uncoveredCount >=
								mCoverageStatistics.getNumberOfUncovered() )
							{
//								return( true );
								goto endComputing;
							}
						}
					}
				}
			}

			break;
		}

		case Specifier::DESIGN_MODEL_KIND:
		{
			if( mExecutableCoverageTable == NULL )
			{
				break;
			}

			VectorOfExecutableForm::const_iterator itExec =
					mTableofRuntimeExecutable.begin();
			VectorOfExecutableForm::const_iterator endExec =
					mTableofRuntimeExecutable.end();
			for( avm_size_t indexExec = 0 ; itExec != endExec ;
					++itExec , ++indexExec )
			{
				if( (*itExec)->hasTransition() )
				{
					endOffset = (*itExec)->getTransition().size();
					for( offset = 0 ; offset < endOffset ; ++offset )
					{
						itTransition = (*itExec)->getTransition().rawAt(offset);

						if( not mExecutableCoverageTable->
								at((*itExec)->getOffset())->test( offset ) )
						{
							++uncoveredCount;

							if( isPertinent( itTransition ) )
							{
								aTableofUncoveredTransition.append( itTransition );
							}
							else
							{
								nonPertinentTransition.append( itTransition );
							}

							if( uncoveredCount >=
								mCoverageStatistics.getNumberOfUncovered() )
							{
//								return( true );
								goto endComputing;
							}
						}
					}
				}
			}

			break;
		}

		default:
		{
			if( mExecutableCoverageTable != NULL )
			{
				VectorOfExecutableForm::const_iterator itExec =
						mTableofRuntimeExecutable.begin();
				VectorOfExecutableForm::const_iterator endExec =
						mTableofRuntimeExecutable.end();
				for( avm_size_t indexExec = 0 ; itExec != endExec ;
						++itExec , ++indexExec )
				{
					if( (*itExec)->hasTransition() )
					{
						endOffset = (*itExec)->getTransition().size();
						for( offset = 0 ; offset < endOffset ; ++offset )
						{
							itTransition = (*itExec)->getTransition().rawAt(offset);

							if( not mExecutableCoverageTable->
									at((*itExec)->getOffset())->test( offset ) )
							{
								++uncoveredCount;

								if( isPertinent( itTransition ) )
								{
									aTableofUncoveredTransition.append( itTransition );
								}
								else
								{
									nonPertinentTransition.append( itTransition );
								}

								if( uncoveredCount >=
									mCoverageStatistics.getNumberOfUncovered() )
								{
//									return( true );
									goto endComputing;
								}
							}
						}
					}
				}
			}

			if( mTransitionCoverageTable != NULL )
			{
				avm_size_t endMachine = mTransitionCoverageTable->size();
				for( avm_size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
				{
					aRID = anED.getRuntimeID(itMachine);
					if( aRID.getExecutable()->hasTransition() )
					{
						endOffset = aRID.getExecutable()->getTransition().size();
						for( offset = 0 ; offset < endOffset ; ++offset )
						{
							itTransition = aRID.getExecutable()->
									getTransition().rawAt(offset);

							if( (not mTransitionCoverageTable->
									at(aRID.getOffset())->test(offset))
								&& mExecutableCoverageTable->
									at(aRID.getExecutable()->getOffset())->
									test(offset) )
							{
								++uncoveredCount;

								if( isPertinent( itTransition ) )
								{
									aTableofUncoveredTransition.append( itTransition );
								}
								else
								{
									nonPertinentTransition.append( itTransition );
								}

								if( uncoveredCount >=
									mCoverageStatistics.getNumberOfUncovered() )
								{
//									return( true );
									goto endComputing;
								}
							}
						}
					}
				}
			}

			break;
		}
	}


endComputing:

	aTableofUncoveredTransition.append( nonPertinentTransition );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT  << "AvmCoverageTransitionView::collectUncoveredTransition:> count: "
			<< aTableofUncoveredTransition.size() << std::endl;
	AVM_OS_TRACE << "AvmCoverageTransitionView::collectUncoveredTransition:> count: "
			<< aTableofUncoveredTransition.size() << std::endl;

	VectorOfAvmTransition::const_iterator itTransition = aTableofUncoveredTransition.begin();
	VectorOfAvmTransition::const_iterator endTransition = aTableofUncoveredTransition.end();
	for( ; itTransition != endTransition ; ++itTransition )
	{
		AVM_OS_COUT << "\t"  << (*itTransition)->strTransitionHeader() << std::endl;

		AVM_OS_TRACE << "\t" << (*itTransition)->strTransitionHeader() << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
}


/**
 * Collect uncovered transition in a given context
 */
void AvmCoverageTransitionView::collectUncoveredTransition(
		const ExecutionData & anED, VectorOfAvmTransition & tableofTransitions)
{
	ExecutableForm * tmpExecutable = NULL;

	ListOfAvmTransition listOfOutgoingTransition;
	ListOfAvmTransition::const_iterator itTrans;
	ListOfAvmTransition::const_iterator endTrans;

	itRF = anED.getTableOfRuntime().begin();
	endRF = anED.getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		tmpExecutable = itRID.getExecutable();

		if( anED.isIdleOrRunning( itRID ) && tmpExecutable->hasTransition() )
		{
			tmpExecutable->getOutgoingTransition( listOfOutgoingTransition );

			itTrans = listOfOutgoingTransition.begin();
			endTrans = listOfOutgoingTransition.end();
			for( ; itTrans != endTrans ; ++itTrans )
			{
				if( not testTransitionCoverage(*itTrans) )
				{
					tableofTransitions.append( *itTrans );
				}
			}
		}
	}
}


} /* namespace sep */
