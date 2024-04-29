/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *  Alain Faivre (CEA LIST) alain.faivre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TransitionCoverageFilter.h"
#include "AvmCoverageTransitionView.h"

#include <computer/primitive/AvmCommunicationFactory.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/ExpressionConstructor.h>

#include <fml/common/SpecifierElement.h>


#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include  <famcore/queue/WaitingStrategy.h>
#include  <famcore/queue/ExecutionQueue.h>

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
TransitionCoverageFilter::~TransitionCoverageFilter()
{
	if( mExecutableCoverageTable != nullptr )
	{
		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		std::size_t endOffset = mTransitionCoverageTable->size();
		for( std::size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mTransitionCoverageTable->at(i) != mExecutableCoverageTable->
					at(anED.getRuntime(i).refExecutable().getOffset()) )
			{
				delete( mTransitionCoverageTable->at(i) );
			}
		}

		delete( mTransitionCoverageTable );

		endOffset = mExecutableCoverageTable->size();
		for( std::size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mExecutableCoverageTable->at(i) != nullptr )
			{
				delete( mExecutableCoverageTable->at(i) );
			}
		}

		delete( mExecutableCoverageTable );
	}

	else if( mTransitionCoverageTable != nullptr )
	{
		std::size_t endOffset = mTransitionCoverageTable->size();
		for( std::size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mTransitionCoverageTable->at(i) != nullptr )
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

bool TransitionCoverageFilter::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();

	const WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		mNbCoverage = Query::getWPropertyPosSizeT(
				thePROPERTY, "nbCoverage", AVM_NUMERIC_MAX_SIZE_T);

		mCoverageHeight = mCoverageHeightPeriod =
				Query::getRegexWPropertySizeT(
						thePROPERTY, CONS_WID2("coverage", "height"), 0);

		mCoverageHeightReachedLimit = Query::getRegexWPropertySizeT(thePROPERTY,
			CONS_WID4("coverage", "height", "reached", "limit"), 0);

		// Options pour les transitions fortement tirables
		mHitStronglyRandomFlag = Query::getRegexWPropertyBoolean(
				thePROPERTY, CONS_WID3("hit", "strongly", "random"), false);

		mHitStronglyCount = Query::getRegexWPropertyPosSizeT(
				thePROPERTY, CONS_WID3("hit", "strongly", "count"), 1);

		// Options pour les transitions faiblement tirables
		mHitWeaklyRandomFlag = Query::getRegexWPropertyBoolean(
				thePROPERTY, CONS_WID3("hit", "weakly", "random"), false);

		mHitWeaklyCount = Query::getRegexWPropertyPosSizeT(
				thePROPERTY, CONS_WID3("hit", "weakly", "count"), 1);

		// Options pour les autres transitions tirables ?
		mHitOtherRandomFlag = Query::getRegexWPropertyBoolean(
				thePROPERTY, CONS_WID3("hit", "other", "random"), false);

		mHitOtherCount = Query::getRegexWPropertyPosSizeT(
				thePROPERTY, CONS_WID3("hit", "other", "count"), 1);


		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		mTransitionCoverageTable = new ArrayOfBitset(
				anED.getTableOfRuntime().size(), nullptr);

		ExecutableQuery XQuery( getConfiguration() );

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
				const WObject * theDETAILS = Query::getRegexWSequence(
						getParameterWObject(), OR_WID2("details", "DETAILS"));

				if( theDETAILS != WObject::_NULL_ )
				{
					ExecutableForm * anExecutable = nullptr;
					AvmTransition * aTransition = nullptr;

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
								if( anExecutable != nullptr )
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
								if( aTransition != nullptr )
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
								if( aTransition != nullptr )
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

					for( const auto & itExec : listOfExecutable )
					{
						configureExecutableCoverageTableFlag((* itExec), false);
					}


					// Cas des programmes
					configureTransitionCoverageTableFlag(listOfTransition, false);


					// INITIALISATION de la table de tous les PROGRAM
					// associés à chacune des INSTANCE...
					for( const auto & itInstance : listOfInstance )
					{
						if( itInstance->refExecutable().hasTransition() )
						{
							configureInstanceCoverageTableFlag(anED,
									anED.getRuntimeID(* itInstance), false);
						}
					}


					if( mExecutableCoverageTable != nullptr)
					{
						if( mTransitionCoverageTable != nullptr)
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


	if( (mCoverageHeightPeriod == 0) ||
			(mCoverageHeightPeriod == AVM_NUMERIC_MAX_SIZE_T) )
	{
		mCoverageHeight = mCoverageHeightPeriod = 7;
//				mCoverageStatistics.mNumberOfElements;
	}
	mCoverageHeightReachedCount = 0;
	mCoverageHeightReachedFlag = false;

	if( mCoverageHeightReachedLimit == 0 )
	{
		mCoverageHeightReachedLimit = mCoverageStatistics.mNumberOfElements;
	}


	enablePreprocess( this );

	return mConfigFlag;
}


void TransitionCoverageFilter::configureExecutableCoverageTableFlag(bool value)
{
	if( mExecutableCoverageTable == nullptr )
	{
		mExecutableCoverageTable = new ArrayOfBitset(
				getConfiguration().getExecutableSystem().size(), nullptr);
	}

	Bitset * tableOfFlag = nullptr;
	std::size_t itTransition = 0;
	std::size_t endTransition = 0;

	for( const auto & itExec : mTableofRuntimeExecutable )
	{
		if( itExec->hasTransition() )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << "executable :> " << itExec->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			tableOfFlag = mExecutableCoverageTable->at(itExec->getOffset());
			if( tableOfFlag == nullptr )
			{
				tableOfFlag = new Bitset(
						itExec->getTransition().size(), true);

				mExecutableCoverageTable->set(
						itExec->getOffset(), tableOfFlag);
			}

			endTransition = itExec->getTransition().size();
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
			<< itExec->rawTransition(itTransition)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
					}
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}
		else
		{
			mExecutableCoverageTable->set(itExec->getOffset(), nullptr);
		}
	}
}


void TransitionCoverageFilter::configureExecutableCoverageTableFlag(
		const ExecutableForm & anExecutable, bool value)
{
	if( mExecutableCoverageTable == nullptr )
	{
		mExecutableCoverageTable = new ArrayOfBitset(
				getConfiguration().getExecutableSystem().size(), nullptr);
	}

	if( anExecutable.hasTransition() )
	{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << "executable :> " << anExecutable.getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

		Bitset * tableOfFlag =
				mExecutableCoverageTable->at( anExecutable.getOffset() );
		if( tableOfFlag == nullptr )
		{
			tableOfFlag = new Bitset(anExecutable.getTransition().size(), true);

			mExecutableCoverageTable->set(anExecutable.getOffset(), tableOfFlag);
		}

		std::size_t endTransition = anExecutable.getTransition().size();
		std::size_t itTransition = 0;
		for( ; itTransition < endTransition ; ++itTransition )
		{
			if( (not value) && tableOfFlag->test(itTransition) )
			{
				tableOfFlag->set(itTransition, value);

				mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
		<< anExecutable.rawTransition(itTransition)->getFullyQualifiedNameID()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
			}
		}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
		AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
	}

	// Cas des sous machine executable
	if( anExecutable.hasInstanceStatic() )
	{
		TableOfSymbol::const_iterator it = anExecutable.instance_static_begin();
		TableOfSymbol::const_iterator endIt = anExecutable.instance_static_end();
		for( ; it != endIt ; ++it )
		{
			configureExecutableCoverageTableFlag((*it).getExecutable(), value);
		}
	}
}


void TransitionCoverageFilter::configureInstanceCoverageTableFlag()
{
	if( mExecutableCoverageTable != nullptr)
	{
		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		RuntimeID aRID;

		if( mTransitionCoverageTable == nullptr )
		{
			mTransitionCoverageTable = new ArrayOfBitset(
					anED.getTableOfRuntime().size(), nullptr);
		}

		std::size_t endMachine = mTransitionCoverageTable->size();
		for( std::size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
		{
			aRID = anED.getRuntimeID(itMachine);
			if( aRID.refExecutable().hasTransition() &&
					(mTransitionCoverageTable->at(itMachine) == nullptr) )
			{
				mTransitionCoverageTable->set(itMachine,
						mExecutableCoverageTable->at(
								aRID.refExecutable().getOffset()));
			}
		}
	}
}



void TransitionCoverageFilter::configureInstanceCoverageTableFlag(bool value)
{
	const ExecutionData & anED = getConfiguration().getMainExecutionData();
	RuntimeID aRID;
	Bitset * tableOfFlag = nullptr;

	std::size_t itTransition = 0;
	std::size_t endTransition = 0;

	if( mTransitionCoverageTable == nullptr )
	{
		mTransitionCoverageTable = new ArrayOfBitset(
				anED.getTableOfRuntime().size(), nullptr);
	}

	std::size_t endMachine = mTransitionCoverageTable->size();
	for( std::size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
	{
		aRID = anED.getRuntimeID(itMachine);
		if( aRID.refExecutable().hasTransition() )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			tableOfFlag = mTransitionCoverageTable->at( itMachine );
			if( tableOfFlag == nullptr )
			{
				tableOfFlag = new Bitset(
						aRID.refExecutable().getTransition().size(), true);

				mTransitionCoverageTable->set(itMachine, tableOfFlag);
			}

			itTransition = 0;
			endTransition = aRID.refExecutable().getTransition().size();
			for( ; itTransition < endTransition ; ++itTransition )
			{
				if( (not value) && tableOfFlag->test(itTransition) )
				{
					tableOfFlag->set(itTransition, value);

					if( not value )
					{
						mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
			<< aRID.refExecutable().rawTransition(
					itTransition )->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
					}
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}
		else
		{
			mTransitionCoverageTable->set(itMachine, nullptr);
		}
	}
}


void TransitionCoverageFilter::configureInstanceCoverageTableFlag(
		const ExecutionData & anED, const RuntimeID & aRID, bool value)
{
	if( mExecutableCoverageTable == nullptr )
	{
		configureExecutableCoverageTableFlag( true );
	}

	if( mTransitionCoverageTable == nullptr )
	{
		mTransitionCoverageTable = new ArrayOfBitset(
				anED.getTableOfRuntime().size(), nullptr);
	}

	const ExecutableForm & anExecutable = aRID.refExecutable();

	if( anExecutable.isnotNullref()
		&& (mTransitionCoverageTable->at(aRID.getOffset()) == nullptr) )
	{
		if( anExecutable.hasTransition() &&
				mExecutableCoverageTable->at(anExecutable.getOffset()) == nullptr )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			Bitset * tableOfFlag =
					mTransitionCoverageTable->at( aRID.getOffset() );
			if( tableOfFlag == nullptr )
			{
				tableOfFlag = new Bitset(
						anExecutable.getTransition().size(), true);

				mTransitionCoverageTable->set(aRID.getOffset(), tableOfFlag);
			}

			std::size_t endTransition = anExecutable.getTransition().size();
			std::size_t itTransition = 0;
			for( ; itTransition < endTransition ; ++itTransition )
			{
				if( (not value) && tableOfFlag->test(itTransition) )
				{
					tableOfFlag->set(itTransition, value);

					mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
		<< anExecutable.rawTransition(itTransition)->getFullyQualifiedNameID()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
		}
		else if( anExecutable.hasTransition() )
		{
AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

			Bitset * tableOfFlag =
					mTransitionCoverageTable->at( aRID.getOffset() );
			if( tableOfFlag == nullptr )
			{
				tableOfFlag = new Bitset(
						anExecutable.getTransition().size(), true);

				mTransitionCoverageTable->set(aRID.getOffset(), tableOfFlag);
			}

			std::size_t endTransition = anExecutable.getTransition().size();
			std::size_t itTransition = 0;
			for( ; itTransition < endTransition ; ++itTransition )
			{
				tableOfFlag->set(itTransition,
						value && mExecutableCoverageTable->at(
								anExecutable.getOffset())->test(itTransition) );

				if( (not value) && mExecutableCoverageTable->at(
						anExecutable.getOffset())->test(itTransition) )
				{
					mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
		<< anExecutable.rawTransition(itTransition)->getFullyQualifiedNameID()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
				}
			}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING , (not value) )
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


void TransitionCoverageFilter::configureTransitionCoverageTableFlag(
		ListOfAvmTransition & listOfTransition, bool value)
{
	if( mExecutableCoverageTable == nullptr )
	{
		mExecutableCoverageTable = new ArrayOfBitset(
				getConfiguration().getExecutableSystem().size(), nullptr);
	}

	Bitset * tableOfFlag = nullptr;
	avm_offset_t containerExecOffset = 0;

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING ,
		(not value) && listOfTransition.nonempty() )
	AVM_OS_TRACE << "program :> user details" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )

	for( const auto & itProg : listOfTransition )
	{
		containerExecOffset = itProg->getExecutableContainer()->getOffset();

		tableOfFlag = mExecutableCoverageTable->at(containerExecOffset);
		if( tableOfFlag == nullptr )
		{
			tableOfFlag = new Bitset(itProg->getExecutableContainer()
					->getTransition().size(), true);

			mExecutableCoverageTable->set(containerExecOffset, tableOfFlag);
		}
		if( (not value) && tableOfFlag->test( itProg->getOffset() ) )
		{
			mExecutableCoverageTable->at( containerExecOffset )->set(
					itProg->getOffset(), value);

			mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_TRACE << "\t" << "program :> "
		<< itProg->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING ,
		(not value) && listOfTransition.nonempty() )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , CONFIGURING )
}


Bitset * TransitionCoverageFilter::getCoverageTableBitset(
		const RuntimeID & aRID)
{
	switch( mScope )
	{
		case Specifier::DESIGN_MODEL_KIND:
		{
			return( mExecutableCoverageTable->at(
					aRID.refExecutable().getOffset() ) );
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
void TransitionCoverageFilter::reportMinimum(OutStream & os) const
{
	os << TAB << "TRANSITION COVERAGE PROCESSOR" << EOL_FLUSH;

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
					getConfiguration().getMainExecutionData();

			switch( mScope )
			{
				case Specifier::DESIGN_INSTANCE_KIND:
				{
					if( mTransitionCoverageTable == nullptr )
					{
						break;
					}

					std::size_t endMachine = mTransitionCoverageTable->size();
					std::size_t itMachine = 0;
					for( ; itMachine < endMachine ; ++itMachine )
					{
						const RuntimeID & aRID = anED.getRuntimeID(itMachine);

						AvmCoverageTransitionView::reportCoverageStateTransitions(os,
								mTransitionCoverageTable->at(aRID.getOffset()),
								aRID.refExecutable(),
								aRID.getFullyQualifiedNameID(), "instance");
					}

					break;
				}

				case Specifier::DESIGN_MODEL_KIND:
				{
					if( mExecutableCoverageTable == nullptr )
					{
						break;
					}

					VectorOfExecutableForm::const_iterator itExec =
							mTableofRuntimeExecutable.begin();
					VectorOfExecutableForm::const_iterator endExec =
							mTableofRuntimeExecutable.end();
					for( std::size_t indexExec = 0 ; itExec != endExec ;
							++itExec , ++indexExec )
					{
						const ExecutableForm & anExecutable = *(*itExec);

						AvmCoverageTransitionView::reportCoverageStateTransitions(os,
								mExecutableCoverageTable->at(anExecutable.getOffset()),
								anExecutable, anExecutable.getFullyQualifiedNameID(), "model");
					}

					break;
				}

				default:
				{
					if( mExecutableCoverageTable != nullptr )
					{
						VectorOfExecutableForm::const_iterator itExec =
								mTableofRuntimeExecutable.begin();
						VectorOfExecutableForm::const_iterator endExec =
								mTableofRuntimeExecutable.end();
						for( std::size_t indexExec = 0 ; itExec != endExec ;
								++itExec , ++indexExec )
						{
							const ExecutableForm & anExecutable = *(*itExec);

							AvmCoverageTransitionView::reportCoverageStateTransitions(os,
									mExecutableCoverageTable->at(anExecutable.getOffset()),
									anExecutable, anExecutable.getFullyQualifiedNameID(), "model");
						}
					}

					if( mTransitionCoverageTable != nullptr )
					{
						std::size_t endMachine = mTransitionCoverageTable->size();
						std::size_t itMachine = 0;
						for( ; itMachine < endMachine ; ++itMachine )
						{
							const RuntimeID & aRID = anED.getRuntimeID(itMachine);

							AvmCoverageTransitionView::reportCoverageStateTransitions(os,
									mTransitionCoverageTable->at(aRID.getOffset()),
									aRID.refExecutable(),
									aRID.getFullyQualifiedNameID(), "instance");
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

	if( mSliceFlag )
	{
		os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
	}

	os << std::flush;
}


void TransitionCoverageFilter::reportDefault(OutStream & os) const
{
	reportHeader(os, "TRANSITION COVERAGE ");

	if( mHeuristicProperty.mHeuristicEnabled )
	{
		os << std::boolalpha
				<< " < chp:" << mCoverageHeightPeriod
				<< " , ch:"  << mCoverageHeight
				<< " ; hsr:" << mHitStronglyRandomFlag
				<< " , hsc:" << mHitStronglyCount
				<< " ; hwr:" << mHitWeaklyRandomFlag
				<< " , hwc:" << mHitWeaklyCount
				<< " ; hor:" << mHitOtherRandomFlag
				<< " , hoc:" << mHitOtherCount
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

		if( true )//isReportDetails() )
		{
			os << TAB2 << "List of the << "
					<< mCoverageStatistics.getNumberOfUncovered()
					<<  " >> transitions non covered:" << EOL << EOL;

			const ExecutionData & anED = getConfiguration().getMainExecutionData();

			switch( mScope )
			{
				case Specifier::DESIGN_INSTANCE_KIND:
				{
					if( mTransitionCoverageTable == nullptr )
					{
						break;
					}

					std::size_t endMachine = mTransitionCoverageTable->size();
					std::size_t itMachine = 0;
					for( ; itMachine < endMachine ; ++itMachine )
					{
						const RuntimeID & aRID = anED.getRuntimeID(itMachine);

						AvmCoverageTransitionView::reportCoverageStateTransitions(os,
								mTransitionCoverageTable->at(aRID.getOffset()),
								aRID.refExecutable(),
								aRID.getFullyQualifiedNameID(), "instance");
					}

					break;
				}

				case Specifier::DESIGN_MODEL_KIND:
				{
					if( mExecutableCoverageTable == nullptr )
					{
						break;
					}

					VectorOfExecutableForm::const_iterator itExec =
							mTableofRuntimeExecutable.begin();
					VectorOfExecutableForm::const_iterator endExec =
							mTableofRuntimeExecutable.end();
					for( std::size_t indexExec = 0 ; itExec != endExec ;
							++itExec , ++indexExec )
					{
						const ExecutableForm & anExecutable = *(*itExec);

						AvmCoverageTransitionView::reportCoverageStateTransitions(os,
								mExecutableCoverageTable->at(anExecutable.getOffset()),
								anExecutable, anExecutable.getFullyQualifiedNameID(), "model");
					}

					break;
				}

				default:
				{
					if( mExecutableCoverageTable != nullptr )
					{
						VectorOfExecutableForm::const_iterator itExec =
								mTableofRuntimeExecutable.begin();
						VectorOfExecutableForm::const_iterator endExec =
								mTableofRuntimeExecutable.end();
						for( std::size_t indexExec = 0 ; itExec != endExec ;
								++itExec , ++indexExec )
						{
							const ExecutableForm & anExecutable = *(*itExec);

							AvmCoverageTransitionView::reportCoverageStateTransitions(os,
									mExecutableCoverageTable->at(anExecutable.getOffset()),
									anExecutable, anExecutable.getFullyQualifiedNameID(), "model");
						}
					}

					if( mTransitionCoverageTable != nullptr )
					{
						std::size_t endMachine = mTransitionCoverageTable->size();
						std::size_t itMachine = 0;
						for( ; itMachine < endMachine ; ++itMachine )
						{
							const RuntimeID & aRID = anED.getRuntimeID(itMachine);

							AvmCoverageTransitionView::reportCoverageStateTransitions(os,
									mTransitionCoverageTable->at(aRID.getOffset()),
									aRID.refExecutable(),
									aRID.getFullyQualifiedNameID(), "instance");
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

	if( mSliceFlag )
	{
		os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
	}

	os << std::flush;
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void TransitionCoverageFilter::tddRegressionReportImpl(OutStream & os) const
{
	os << TAB1 << "COVERED TRANSITIONS : ";
	if( mCoverageStatistics.goalAchieved() )
	{
		os << mCoverageStatistics.mNumberOfElements << " / "
				<< mCoverageStatistics.mNumberOfElements << EOL;
	}
	else
	{
		os << mCoverageStatistics.getNumberOfUncovered() << " / "
				<< mCoverageStatistics.mNumberOfElements << EOL;
	}

//$	if( mSliceFlag )
//	{
//		os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
//$	}

	os << std::flush;
}



/**
 * PRE-FILTER
 */
bool TransitionCoverageFilter::prefilter()
{
	bool mCondition =
			( mNbCoverage > mCoverageStatistics.mNumberOfElements ) ?
			mCoverageStatistics.goalAchieved() && mStopFlag :
			(mCoverageStatistics.mNumberOfCovered >= mNbCoverage);

	if( mCondition )
	{
		getSymbexRequestManager().postRequestStop( this );

		return false;
	}

	return( getExecutionQueue().hasReady() );
}


/**
 * postEval Filter
 */
bool TransitionCoverageFilter::postfilter()
{
	if( mCoverageStatistics.hasUncovered() )
	{
		mCoverageStatistics.backupCovered();

		ecQueue = &( getExecutionQueue().getResultQueue() );

		ecQueueIt = ecQueue->begin();
		ecQueueItEnd = ecQueue->end();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			itEndEC = (*ecQueueIt)->end();
			for( itEC = (*ecQueueIt)->begin() ; (itEC != itEndEC) ; ++itEC )
			{
				updateTransitionCoverageTable((*itEC) ,
						(*itEC)->getRunnableElementTrace());
			}
		}


		if( mHeuristicProperty.mHeuristicEnabled )
		{
			if( mTraceDirectiveRunningFlag )
			{
				if( runTraceDriver() )
				{
					//!! Continue driven
				}
				else
				{
					getSymbexRequestManager().postRequestRequeueWaiting( this );
				}

				if( mTraceDirectiveRunningFlag )
				{
					if( not mCoverageStatistics.updateFailedStep() )
					{
						mCoverageStatistics.resetFailedStep();
					}

					return( getExecutionQueue().hasResult() );
				}
			}


			if( mCoverageStatistics.updateFailedStep() )
			{
				//!!! TODO optimization
				if( mCoverageStatistics.isSeriouslyFailedStep() )
				{
					mHeuristicProperty.incrHeuristicClass();

					getSymbexRequestManager().postRequestRequeueWaiting( this );


AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_INFO << std::endl
			<< EMPHASIS(mHeuristicProperty.strHeuristicClass(), '*', 80);
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	mCoverageStatistics.toStreamFailedStep(AVM_OS_COUT,
			"No new transition covered since << ", " step", " >> !!!\n");
	mCoverageStatistics.toStreamFailedStep(AVM_OS_TRACE,
			"No new transition covered since << ", " step", " >> !!!\n");
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
			}
			else
			{
				mCoverageStatistics.resetFailedStep();
			}


			switch( mHeuristicProperty.mHeuristicClass )
			{
				case IHeuristicClass::HEURISTIC_BASIC_CLASS:
				{
					mHeuristicProperty.mHeuristicClass =
							IHeuristicClass::HEURISTIC_BASIC_CLASS;

					heuristicNaiveClassImpl();
					break;
				}
				case IHeuristicClass::HEURISTIC_NAIVE_CLASS:
				{
					heuristicNaiveClassImpl();
					break;
				}
				case IHeuristicClass::HEURISTIC_SMART_CLASS:
				{
					heuristicSmartClassImpl();
					break;
				}

				case IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS:
				{
					heuristicAgressiveClassImpl();
					break;
				}

				case IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS:
				default:
				{
					heuristicNothingElseClassImpl();
					break;
				}
			}
		}
	}

	return( getExecutionQueue().hasResult() );
}



/**
 * Heuristic NAIVE Class implementation
 */
void TransitionCoverageFilter::heuristicNaiveClassImpl()
{
	if( mCoverageStatistics.hasUncovered() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	mCoverageStatistics.toStreamCoverageRate(AVM_OS_COUT ,
			"Number of covered transitions = ", " / ", "\n");

	mCoverageStatistics.toStreamCoverageRate(AVM_OS_TRACE,
			"Number of covered transitions = ", " / ", "\n");
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		computeWeightOfResult();

		// case of found strong hit EC
		if( mStronglyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "==> Next [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

			setHitWeight(mStronglyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
					mHitStronglyRandomFlag, mHitStronglyCount);
		}

		// case of has waiting strong hit EC
		else if( getExecutionQueue().getWaitingStrategy()->
				hasWaiting(WEIGHT_STRONGLY_ACHIEVABLE) )
		{
			getSymbexRequestManager().postRequestRequeueWaiting( this );
		}

		// case of found weak hit EC
		else if( mWeaklyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "==> Next [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

			setHitWeight(mWeaklyHitEC, WEIGHT_SELECTED_ACHIEVABLE,
					mHitWeaklyRandomFlag, mHitWeaklyCount);
		}

		//!!! TODO optimization
		else// if( mCoverageStatistics.updateFailedHeuristic() )
		{
			getSymbexRequestManager().postRequestRequeueWaiting( this );
		}
	}
}

/**
 * Heuristic SMART Class implementation
 */
void TransitionCoverageFilter::heuristicSmartClassImpl()
{
	heuristicNaiveClassImpl();
}


/**
 * Heuristic AGRESSIVE Class implementation
 */
void TransitionCoverageFilter::heuristicAgressiveClassImpl()
{
	heuristicNaiveClassImpl();
}


/**
 * Heuristic NOTHING HELSE Class implementation
 */
void TransitionCoverageFilter::heuristicNothingElseClassImpl()
{
	collectUncoveredTransition();

	mHeuristicProperty.resetHeuristicClass(
			IHeuristicClass::HEURISTIC_NAIVE_CLASS);

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_INFO << std::endl
			<< EMPHASIS(mHeuristicProperty.strHeuristicClass(), '*', 80);
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

	heuristicNaiveClassImpl();


	if( mCoverageStatistics.goalAchievedRate() )
	{
		if( mStopFlag )
		{
			getSymbexRequestManager().postRequestStop( this );
		}

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_INFO << "******* HEURISTIC GOAL ACHIEVED RATE : "
			<< mCoverageStatistics.mCoverageRateGoal << " % *******" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
	}

	if( mCoverageStatistics.goalAchievedRest() )
	{
		if( mStopFlag )
		{
			getSymbexRequestManager().postRequestStop( this );
		}

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_INFO << "******* HEURISTIC GOAL ACHIEVED REST : "
			<< mCoverageStatistics.mCoverageRestGoal << " *******" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
	}


	if( ++mHeuristicProperty.mHeuristicTrialsCount
			> mHeuristicProperty.mHeuristicTrialsLimit )
	{
		if( mStopFlag )
		{
			getSymbexRequestManager().postRequestStop( this );
		}

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_INFO << "******* HEURISTIC TRIALS STOP : "
			<< mHeuristicProperty.mHeuristicTrialsLimit
			<< " *******" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
	}
}



/**
 * Compute Hit Weigth for Execution Context
 */
void TransitionCoverageFilter::setHitWeight(VectorOfExecutionContext & hitEC,
		std::uint8_t hitWeight, bool randomFlag, std::size_t hitCount)
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
	AVM_OS_INFO << std::endl << DEFAULT_WRAP_DATA << "HIT :> ";
	hitEC[ offset ]->traceMinimum(AVM_OS_COUT );
	hitEC[ offset ]->traceMinimum(AVM_OS_TRACE);
	AVM_OS_INFO << END_WRAP;

	fireableTransitionTrace(AVM_OS_COUT , hitEC[ offset ]->getExecutionData());
	fireableTransitionTrace(AVM_OS_TRACE, hitEC[ offset ]->getExecutionData());
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << std::endl;
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
	AVM_OS_INFO << std::endl << DEFAULT_WRAP_DATA << "HIT :> ";
	hitEC[ offset ]->traceMinimum(AVM_OS_COUT );
	hitEC[ offset ]->traceMinimum(AVM_OS_TRACE);
	AVM_OS_INFO << END_WRAP;

	fireableTransitionTrace(AVM_OS_COUT , hitEC[ offset ]->getExecutionData());
	fireableTransitionTrace(AVM_OS_TRACE, hitEC[ offset ]->getExecutionData());
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	}
}

/*
 * weight: 1  if some transition of leaf EC will  be fired
 * weight: 2  if some transition of leaf EC could be fired
 * weight: 3  else
 */
void TransitionCoverageFilter::computeWeight(ExecutionContext * anEC)
{
	switch( mHeuristicProperty.mHeuristicClass )
	{
		case IHeuristicClass::HEURISTIC_BASIC_CLASS:
		{
			mHeuristicProperty.mHeuristicClass =
					IHeuristicClass::HEURISTIC_BASIC_CLASS;

			computeWeightNaive( anEC );
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
			computeWeightNaive( anEC );
			break;
		}
	}
}


void TransitionCoverageFilter::computeWeightNaive(ExecutionContext * anEC)
{
	if( computeCheckNonPriorityWeight(anEC) )
	{
		return;
	}

	computePriorityWeight(anEC);

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


void TransitionCoverageFilter::computeWeightSmart(ExecutionContext * anEC)
{
	computePriorityWeight(anEC);

	if( checkStronglyPriorityWeight(anEC) )
	{
		return;
	}

	else if( computeCheckNonPriorityWeight(anEC) )
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


void TransitionCoverageFilter::computeWeightAgressive(ExecutionContext * anEC)
{
	computePriorityWeight(anEC);

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


bool TransitionCoverageFilter::computeCheckNonPriorityWeight(
		ExecutionContext * anEC)
{
	if( anEC->getHeight() > mCoverageHeight )
	{
		mCoverageHeightReachedFlag = true;

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


void TransitionCoverageFilter::computePriorityWeight(ExecutionContext * anEC)
{
	tmpStronglyFireableTransitionCount = 0;
	tmpWeaklyFireableTransitionCount = 0;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO << ":> from ";  anEC->traceMinimum(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	// compute :>
//	fireableTransitionCount( anEC->getExecutionData() );
	fireableTransitionCount( anEC->getExecutionData() ,
			anEC->getExecutionData().getSystemRuntime() );
}



bool TransitionCoverageFilter::checkStronglyPriorityWeight(
		ExecutionContext * anEC)
{
	if( tmpStronglyFireableTransitionCount > 0 )
	{
		anEC->setWeight( WEIGHT_STRONGLY_ACHIEVABLE );

		if( mStronglyFireableTransitionCount
			< tmpStronglyFireableTransitionCount )
		{
			mStronglyFireableTransitionCount =
					tmpStronglyFireableTransitionCount;

			mStronglyHitEC.clear();
			mStronglyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO  << "==> HIT EC [ Strong : "
			<< mStronglyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_INFO << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			return( true );
		}

		else if( mStronglyFireableTransitionCount ==
				tmpStronglyFireableTransitionCount )
		{
			mStronglyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO  << "==> HIT EC [ Strong : "
			<< mStronglyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_INFO << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		}

		return( true );
	}

	return( false );
}

bool TransitionCoverageFilter::checkWeaklyPriorityWeight(ExecutionContext * anEC)
{
	if( tmpWeaklyFireableTransitionCount > 0 )
	{
		anEC->setWeight( WEIGHT_WEAKLY_ACHIEVABLE );

		if( mWeaklyFireableTransitionCount < tmpWeaklyFireableTransitionCount )
		{
			mWeaklyFireableTransitionCount = tmpWeaklyFireableTransitionCount;

			mWeaklyHitEC.clear();
			mWeaklyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO  << "==> HIT EC [ Weak : "
			<< mWeaklyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_INFO << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

			return( true );
		}

		else if( mWeaklyFireableTransitionCount ==
				tmpWeaklyFireableTransitionCount )
		{
			mWeaklyHitEC.append( anEC );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO  << "==> HIT EC [ Weak : "
			<< mWeaklyFireableTransitionCount << " ]:> ";
	anEC->traceMinimum(AVM_OS_COUT);
	anEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_INFO << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		}

		return( true );
	}

	return( false );
}


void TransitionCoverageFilter::computeWeightOfResult()
{
	mStronglyHitEC.clear();
	mStronglyFireableTransitionCount = 0;

	mWeaklyHitEC.clear();
	mWeaklyFireableTransitionCount = 0;

	ecQueueIt = ecQueue->begin();
	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
	{
		itEndEC = (*ecQueueIt)->end();
		for( itEC = (*ecQueueIt)->begin() ; (itEC != itEndEC) ; ++itEC )
		{
			computeWeight( *itEC );

//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//	if( (*itEC)->getWeight() == WEIGHT_SELECTED_ACHIEVABLE )
//	{
//		fireableTransitionTrace(AVM_OS_COUT , (*itEC)->getExecutionData());
//		fireableTransitionTrace(AVM_OS_TRACE, (*itEC)->getExecutionData());
//	}
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
	}

	// Count one time per step CoverageHeightReached
	if( mCoverageHeightReachedFlag )
	{
		++mCoverageHeightReachedCount;

		mCoverageHeightReachedFlag = false;
	}
}


void TransitionCoverageFilter::handleRequestRequeueWaitingTable(
		WaitingStrategy & aWaitingStrategy,
		std::uint8_t aWeightMin, std::uint8_t aWeightMax)
{
	mCoverageStatistics.setFailedHeuristic();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_INFO << std::endl << ">>>>>>> REQUEST REQUEUE <<<<<<<" << std::endl;

	AVM_IF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
		report(AVM_OS_COUT);
		report(AVM_OS_TRACE);
	AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	do
	{
		mWaitingQueue.clear();

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )
	aWaitingStrategy.toStream(AVM_OS_COUT);
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )

//		aWaitingStrategy.spliceQueueTable(mWaitingQueue, aWeightMax);

		aWeightMin = aWaitingStrategy.flushPriorQueueTable(
				mWaitingQueue, aWeightMin, aWeightMax);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "REQUEUE QUEUE << " << strHeuristicWeight(aWeightMin)
			<< " >> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


		mStronglyHitEC.clear();
		mStronglyFireableTransitionCount = 0;

		mWeaklyHitEC.clear();
		mWeaklyFireableTransitionCount = 0;

		ecQueueIt = mWaitingQueue.begin();
		ecQueueItEnd = mWaitingQueue.end();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			computeWeight( *ecQueueIt );

			aWaitingStrategy.push( *ecQueueIt );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	if( (*ecQueueIt)->getWeight() <= WEIGHT_STRONGLY_ACHIEVABLE )
	{
		AVM_OS_INFO  << DEFAULT_WRAP_DATA
				<< "REQUEUE candidate [ <= Strongly ] :> ";
		(*ecQueueIt)->traceMinimum(AVM_OS_COUT );
		(*ecQueueIt)->traceMinimum(AVM_OS_TRACE);
		AVM_OS_INFO << END_WRAP;

		fireableTransitionTrace(AVM_OS_COUT, (*ecQueueIt)->getExecutionData());
		fireableTransitionTrace(AVM_OS_TRACE,(*ecQueueIt)->getExecutionData());
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )
	aWaitingStrategy.toStream(AVM_OS_COUT);
	aWaitingStrategy.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , QUEUE )

		// case of found strongly hit EC
		if( mStronglyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO  << "==> REQUEUE candidate [ Strongly ] Fireable Count :> "
			<< mStronglyFireableTransitionCount
			<< "  Hit Count : " << mStronglyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}

		// case of found weakly hit EC
		if( mWeaklyFireableTransitionCount > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "==> REQUEUE candidate [ Weakly ] Fireable Count :> "
			<< mWeaklyFireableTransitionCount
			<< "  Hit Count : " << mWeaklyHitEC.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		}
	}
	while( ((++aWeightMin) <= WEIGHT_NON_PRIORITY) &&
//	while( ((++aWeightMin) <= aWeightMax) &&
			(mStronglyFireableTransitionCount == 0) );


//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	// Passer en mode DIRECTIF vers une transition WEAKLY_ACHIEVABLE à couvrir
	// Calcul d'une trace vers cette transition
	if( mStronglyFireableTransitionCount == 0 )
	{
		if( initializeTraceDriver(aWaitingStrategy) )
		{
			//!! NOTHING
		}
	}
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	if( (mCoverageHeightReachedCount > mCoverageHeightReachedLimit) &&
			(mStronglyFireableTransitionCount == 0) )
	{
		mCoverageHeightReachedCount = 0;
		mCoverageHeightReachedFlag = false;

		mCoverageHeight += mCoverageHeightPeriod;
		mCoverageHeightReachedCount += mCoverageHeightReachedCount;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "REQUEUE [ chp: " << mCoverageHeightPeriod
			<< " ] ==> New Coverage Height :> "	<< mCoverageHeight << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	}
}


bool TransitionCoverageFilter::testFireability(const ExecutionData & anED,
		const RuntimeID & aReceiverRID, AvmTransition * aTransition)
{
	if( aTransition->hasCode() && aTransition->getAvmCode().hasOperand()
		&& aTransition->getAvmCode().first().is< AvmCode >() )
	{
		const AvmCode * firstStatement =
				aTransition->getAvmCode().first().to_ptr< AvmCode >();

		switch( firstStatement->getOptimizedOpCode() )
		{
			case AVM_OPCODE_INPUT_ENV:
			case AVM_OPCODE_OUTPUT_ENV:
			{
				return( true );
			}
			default:
			{
				if( firstStatement->isOpCode( AVM_OPCODE_INPUT ) &&
					firstStatement->first().is< InstanceOfPort >() )
				{
					return( AvmCommunicationFactory::computePresence(
							anED, aReceiverRID,
							firstStatement->first().to< InstanceOfPort >()) );
				}
				return( true );
			}
		}
	}

	return( true );
}


bool TransitionCoverageFilter::isControlLoop(ExecutionContext * anEC)
{
	tmpEC = anEC->getPrevious();
	for( ; tmpEC != nullptr ; tmpEC = tmpEC->getPrevious() )
	{
		if( anEC->getExecutionData().getRuntimeFormStateTable()->equalsState(
				tmpEC->getExecutionData().getRuntimeFormStateTable() ) )
		{
			return( true );
		}
	}
	return( false );
}


bool TransitionCoverageFilter::isSyntaxicLoop(ExecutionContext * anEC)
{
	tmpEC = anEC->getPrevious();
	for( ; tmpEC != nullptr ; tmpEC = tmpEC->getPrevious() )
	{
		if( anEC->getExecutionData().getRuntimeFormStateTable()->equalsState(
				tmpEC->getExecutionData().getRuntimeFormStateTable() ) )
		{
			return( true );
		}
	}
	return( false );
}


bool TransitionCoverageFilter::isTrivialLoop(ExecutionContext * anEC)
{
	tmpEC = anEC->getPrevious();
	for( ; tmpEC != nullptr ; tmpEC = tmpEC->getPrevious() )
	{
		if( anEC->edTEQ( *tmpEC ) )
		{
			return( true );
		}
	}
	return( false );
}


void TransitionCoverageFilter::fireableTransitionCount(
		const ExecutionData & anED, const RuntimeID & aRID)
{
	tmpEF = aRID.getExecutable();

	tmpRuntimeTransitionBitset = getCoverageTableBitset( aRID );

	if( tmpRuntimeTransitionBitset == nullptr )
	{
		//!! NOTHING
	}
	//tmpEF->hasTransition()
	else if( tmpRuntimeTransitionBitset->anyFalse() )
	{
		AvmTransition * aProg;

		std::size_t endOffset = tmpEF->getTransition().size();
		for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
		{
			aProg = tmpEF->getTransition().rawAt(offset);

			if( not tmpRuntimeTransitionBitset->test(aProg->getOffset()) )
			{
				tmpWeaklyFireableTransitionCount += 1;

				if( testFireability(anED, aRID, aProg) )
				{
					tmpStronglyFireableTransitionCount += 1;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "==> Fireable :> " << aProg->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
				}
			}
		}
	}

//	else if( tmpRuntimeTransitionBitset->allTrue() )
//	{
//		anED.setRuntimeFormState((*itRF)->getRID(), PROCESS_SUSPENDED_STATE);
//	}
}


void TransitionCoverageFilter::fireableTransitionCount(
		const ExecutionData & anED)
{
	std::size_t offset;
	std::size_t endOffset;
	AvmTransition * aProg;

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

		if( tmpRuntimeTransitionBitset == nullptr )
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
				aProg = tmpEF->getTransition().rawAt(offset);

				if( not tmpRuntimeTransitionBitset->test(aProg->getOffset()) )
				{
					tmpWeaklyFireableTransitionCount += 1;

					if( testFireability(anED, itRID, aProg) )
					{
						tmpStronglyFireableTransitionCount += 1;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "==> Fireable :> " << aProg->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
					}
				}
			}
		}

//		else if( tmpRuntimeTransitionBitset->allTrue() )
//		{
//			anED.setRuntimeFormState(itRID, PROCESS_SUSPENDED_STATE);
//		}

	}
}


void TransitionCoverageFilter::fireableTransitionCount(
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
			AvmTransition * aProg = nullptr;

			std::size_t endOffset = tmpEF->getTransition().size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				aProg = tmpEF->getTransition().rawAt(offset);

				if( not tmpRuntimeTransitionBitset->test(aProg->getOffset()) )
				{
					if( testFireability(anED,  aRF.getRID(), aProg) )
					{
						tmpStronglyFireableTransitionCount += 1;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "==> Fireable :> " << aProg->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
					}
					else
					{
						tmpWeaklyFireableTransitionCount += 1;
					}
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



void TransitionCoverageFilter::fireableTransitionTrace(
		OutStream & os, const ExecutionData & anED)
{
	std::size_t offset;
	std::size_t endOffset;
	AvmTransition * aProg = nullptr;

	itRF = anED.getTableOfRuntime().begin();
	endRF = anED.getTableOfRuntime().end();
	for( ; (itRF != endRF) ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		tmpEF = itRID.getExecutable();

		tmpRuntimeTransitionBitset = getCoverageTableBitset( itRID );

		if( tmpRuntimeTransitionBitset == nullptr )
		{
			//!! NOTHING
		}
		//tmpEF->hasTransition()
		else if( anED.isIdleOrRunning( itRID ) )
		{
			if( tmpRuntimeTransitionBitset->anyFalse() )
			{
				endOffset = tmpEF->getTransition().size();
				for( offset = 0 ; offset < endOffset ; ++offset )
				{
					aProg = tmpEF->getTransition().rawAt(offset);

					if( not tmpRuntimeTransitionBitset->
							test(aProg->getOffset()) )
					{
						if( testFireability(anED, itRID, aProg) )
						{
							os << "==> [ Strongly ] Fireable :> "
								<< aProg->strTransitionHeader() << std::endl;
						}
						else
						{
							os << "==> [ Weakly ] Fireable :> "
								<< aProg->strTransitionHeader() << std::endl;
						}
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


void TransitionCoverageFilter::fireableTransitionTrace(OutStream & os,
		const ExecutionData & anED, const RuntimeForm & aRF)
{
	tmpEF = aRF.getRID().getExecutable();

	if( tmpEF->hasTransition() )
	{
		tmpRuntimeTransitionBitset = getCoverageTableBitset( aRF.getRID() );

		if( tmpRuntimeTransitionBitset->anyFalse() )
		{
			AvmTransition * aProg = nullptr;

			std::size_t endOffset = tmpEF->getTransition().size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				aProg = tmpEF->getTransition().rawAt(offset);

				if( not tmpRuntimeTransitionBitset->test(aProg->getOffset()) )
				{
					if( testFireability(anED, aRF.getRID(), aProg) )
					{
						os << "==> [ Strongly ] Fireable :> "
								<< aProg->strTransitionHeader() << std::endl;
					}
					else
					{
						os << "==> [ Weakly ] Fireable :> "
								<< aProg->strTransitionHeader() << std::endl;
					}
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
void TransitionCoverageFilter::updateTransitionCoverageTable(
		ExecutionContext * anEC, const BF & aFiredCode)
{
	if( aFiredCode.invalid() )
	{
		return;
	}

	// Vérification de la création de nouvelle instance dynamique
	// par la commande ${ NEW , EXEC }
	if( (mScope != Specifier::DESIGN_MODEL_KIND) &&
			(anEC->getExecutionData().getTableOfRuntime().size() >
					mTransitionCoverageTable->size()) )
	{
		//TODO
		return;
	}

	switch( aFiredCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			for( const auto & itOperand :
				aFiredCode.to< AvmCode >().getOperands() )
			{
				updateTransitionCoverageTable(anEC, itOperand);
			}

			break;
		}

		case FORM_EXECUTION_CONFIGURATION_KIND:
		{
			const ExecutionConfiguration & anExecConf =
					aFiredCode.to< ExecutionConfiguration >();

			if( anExecConf.isTransition() )
			{
				updateTransitionCoverageTable(anEC,
						anExecConf.getRuntimeID(), anExecConf.getTransition());

//				AvmTransition * firedTransition = anExecConf.getTransition();
//
//				if( not mTransitionCoverageTable->
//						at( anExecConf.getRuntimeID().getOffset() )->
//						test( firedTransition->getOffset() ) )
//				{
//					mCoverageStatistics.addCoveredElement();
//
//					mTransitionCoverageTable->at(
//							anExecConf.getRuntimeID().getOffset() )->
//									set(firedTransition->getOffset(), true);
//
//					if( mExecutableCoverageTable != nullptr )
//					{
//						mExecutableCoverageTable->at( firedTransition->
//								getExecutableContainer()->getOffset() )->
//										set(firedTransition->getOffset(), true);
//					}
//
//					anEC->addInfo( *this, INCR_BF( firedTransition ) );
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


void TransitionCoverageFilter::updateTransitionCoverageTable(
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

				if( mExecutableCoverageTable != nullptr )
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

		anEC->addInfo( *this, INCR_BF( firedTransition ) );

		mListOfPositiveEC.append( anEC );
	}
}


bool TransitionCoverageFilter::testTransitionCoverage(
		const AvmTransition * firedTransition)
{
	switch( mScope )
	{
		case Specifier::DESIGN_MODEL_KIND:
		{
			return( mExecutableCoverageTable->at(
					firedTransition->getExecutableContainer()->getOffset() )
					->test(firedTransition->getOffset()) );
		}

		case Specifier::DESIGN_INSTANCE_KIND:
		{
//			return( mTransitionCoverageTable->at( aRID.getOffset() )->
//					test( firedTransition->getOffset() ) );

			return( true );
		}

		default:
		{
			return( (mExecutableCoverageTable != nullptr)
					|| mExecutableCoverageTable->at(
						firedTransition->getExecutableContainer()->getOffset() )
						->test(firedTransition->getOffset()) );
		}
	}
}


/**
 * mTableofUncoveredTransition
 */
void TransitionCoverageFilter::collectUncoveredTransition()
{
	if( mLastCollectedCoverCount < mCoverageStatistics.mNumberOfCovered )
	{
		mLastCollectedCoverCount = mCoverageStatistics.mNumberOfCovered;

		mTableofUncoveredTransition.clear();

//		std::size_t endTransition = mTableofUncoveredTransition.size();
//		for( std::size_t offset = 0 ; offset < endTransition ; ++offset )
//		{
//			if( testTransitionCoverage(mTableofUncoveredTransition[offset]) )
//			{
//				mTableofUncoveredTransition[offset] =
//						mTableofUncoveredTransition[offset];
//			}
//		}
	}
	else
	{
		return;
	}

	const ExecutionData & anED = getConfiguration().getMainExecutionData();

	RuntimeID aRID;

	std::size_t offset;
	std::size_t endOffset;
	AvmTransition * itTransition;

	switch( mScope )
	{
		case Specifier::DESIGN_INSTANCE_KIND:
		{
			if( mTransitionCoverageTable == nullptr )
			{
				break;
			}

			std::size_t endMachine = mTransitionCoverageTable->size();
			for( std::size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
			{
				aRID = anED.getRuntimeID(itMachine);
				if( aRID.refExecutable().hasTransition() )
				{
					endOffset = aRID.refExecutable().getTransition().size();
					for( offset = 0 ; offset < endOffset ; ++offset )
					{
						itTransition = aRID.refExecutable().
								getTransition().rawAt(offset);

						if( not mTransitionCoverageTable->
								at( aRID.getOffset() )->test( offset ) )
						{
							mTableofUncoveredTransition.append( itTransition );

							if( mTableofUncoveredTransition.size() >=
								mCoverageStatistics.getNumberOfUncovered() )
							{
								return;
							}
						}
					}
				}
			}

			break;
		}

		case Specifier::DESIGN_MODEL_KIND:
		{
			if( mExecutableCoverageTable == nullptr )
			{
				break;
			}

			VectorOfExecutableForm::const_iterator itExec =
					mTableofRuntimeExecutable.begin();
			VectorOfExecutableForm::const_iterator endExec =
					mTableofRuntimeExecutable.end();
			for( std::size_t indexExec = 0 ; itExec != endExec ;
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
							mTableofUncoveredTransition.append( itTransition );

							if( mTableofUncoveredTransition.size() >=
								mCoverageStatistics.getNumberOfUncovered() )
							{
								return;
							}
						}
					}
				}
			}

			break;
		}

		default:
		{
			if( mExecutableCoverageTable != nullptr )
			{
				VectorOfExecutableForm::const_iterator itExec =
						mTableofRuntimeExecutable.begin();
				VectorOfExecutableForm::const_iterator endExec =
						mTableofRuntimeExecutable.end();
				for( std::size_t indexExec = 0 ; itExec != endExec ;
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
								mTableofUncoveredTransition.append( itTransition );

								if( mTableofUncoveredTransition.size() >=
									mCoverageStatistics.getNumberOfUncovered() )
								{
									return;
								}
							}
						}
					}
				}
			}

			if( mTransitionCoverageTable != nullptr )
			{
				std::size_t endMachine = mTransitionCoverageTable->size();
				for( std::size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
				{
					aRID = anED.getRuntimeID(itMachine);
					if( aRID.refExecutable().hasTransition() )
					{
						endOffset = aRID.refExecutable().getTransition().size();
						for( offset = 0 ; offset < endOffset ; ++offset )
						{
							itTransition = aRID.refExecutable().
									getTransition().rawAt(offset);

							if( (not mTransitionCoverageTable->
									at(aRID.getOffset())->test(offset))
								&& mExecutableCoverageTable->
									at(aRID.refExecutable().getOffset())->test(offset) )
							{
								mTableofUncoveredTransition.append( itTransition );

								if( mTableofUncoveredTransition.size() >=
									mCoverageStatistics.getNumberOfUncovered() )
								{
									return;
								}
							}
						}
					}
				}
			}

			break;
		}
	}


AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_INFO << "TransitionCoverageFilter::collectUncoveredTransition:> count: "
			<< mTableofUncoveredTransition.size() << std::endl;

	for( const auto & itTransition : mTableofUncoveredTransition )
	{
		AVM_OS_INFO << "\t" << itTransition->strTransitionHeader() << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
}


void TransitionCoverageFilter::collectUncoveredTransition(
		const ExecutionData & anED, ListOfAvmTransition & listofTransition)
{
	ExecutableForm * tmpExecutable = nullptr;

	ListOfAvmTransition listOfOutgoingTransition;
	ListOfAvmTransition::const_iterator itTrans;
	ListOfAvmTransition::const_iterator endTrans;

	itRF = anED.getTableOfRuntime().begin();
	endRF = anED.getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		tmpExecutable = itRID.getExecutable();

		if( anED.isIdleOrRunning( itRID )
			&& tmpExecutable->hasTransition() )
		{
			tmpExecutable->getOutgoingTransition( listOfOutgoingTransition );

			itTrans = listOfOutgoingTransition.begin();
			endTrans = listOfOutgoingTransition.end();
			for( ; itTrans != endTrans ; ++itTrans )
			{
				if( not testTransitionCoverage(*itTrans) )
				{
					listofTransition.append( *itTrans );
				}
			}
		}
	}
}


/**
 * mTraceDriver
 */
bool TransitionCoverageFilter::initializeTraceDriver(
		WaitingStrategy & aWaitingStrategy)
{
	std::uint8_t aWeightMin = 0;

	mWaitingQueue.clear();

	aWeightMin = aWaitingStrategy.flushPriorQueueTable(
			mWaitingQueue, aWeightMin, WEIGHT_UNKNOWN_ACHIEVABLE);

	ecQueueItEnd = mWaitingQueue.end();

	if( mWeaklyFireableTransitionCount > 0 )
	{
		ecQueueIt = mWaitingQueue.begin();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			if( initializeTraceDriver(*ecQueueIt) )
			{
				mTraceDirectiveRunningFlag = true;

				(*ecQueueIt)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

				aWaitingStrategy.push(mWaitingQueue);

				return( true );
			}
		}
	}


	if( mLastCollectedCoverCount < mCoverageStatistics.mNumberOfCovered )
	{
		mLastDirectiveTransitionOffset = 0;
	}
	collectUncoveredTransition();

	std::size_t endTransition = mTableofUncoveredTransition.size();
	if( mLastDirectiveTransitionOffset >= endTransition )
	{
		mLastDirectiveTransitionOffset = 0;
	}

	do
	{
		std::size_t offset = mLastDirectiveTransitionOffset;
		for( ; offset < endTransition ; ++offset )
		{
			ecQueueIt = mWaitingQueue.begin();
			for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
			{
				if( mTraceDriver.initialize(*ecQueueIt,
						mTableofUncoveredTransition[offset]) )
				{
					++mLastDirectiveTransitionOffset;

					mTraceDirectiveRunningFlag = true;

					(*ecQueueIt)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

					aWaitingStrategy.push(mWaitingQueue);

					return( true );
				}
			}
		}

		aWaitingStrategy.push(mWaitingQueue);

		if( (++aWeightMin) <= WEIGHT_UNKNOWN_ACHIEVABLE )
		{
			mWaitingQueue.clear();

			aWeightMin = aWaitingStrategy.flushPriorQueueTable(
					mWaitingQueue, aWeightMin, WEIGHT_UNKNOWN_ACHIEVABLE);

			ecQueueItEnd = mWaitingQueue.end();
		}
		else
		{
			break;
		}
	}
	while( mWaitingQueue.nonempty() );

	mTraceDriver.resetFailedTransitionTargetHistory();

	return( false );
}


bool TransitionCoverageFilter::initializeTraceDriver(ExecutionContext * anEC)
{
	ListOfAvmTransition uncoveredTransition;
	collectUncoveredTransition(anEC->getExecutionData(), uncoveredTransition);

	while( uncoveredTransition.nonempty() )
	{
		if( mTraceDriver.initialize(anEC, uncoveredTransition.pop_first()) )
		{
			return( true );
		}
	}

	return( false );
}


bool TransitionCoverageFilter::runTraceDriver()
{
	if( mTraceDriver.process( getExecutionQueue().getResultQueue() ) )
	{
		if( mTraceDriver.goalAchieved() )
		{
			mTraceDirectiveRunningFlag = false;

			mLastDirectiveTransitionOffset = 0;
		}

		return( true );
	}
	else
	{
		mTraceDirectiveRunningFlag = false;

		return( false );
	}
}


}
