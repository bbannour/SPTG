/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "MachineCoverageFilter.h"

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/ExpressionConstructor.h>

#include <fml/common/SpecifierElement.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeDef.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfRuntimeFormState.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <famcore/queue/ExecutionQueue.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 ***************************************************************************
prototype filter::machine_coverage as &avm::core.filter.MACHINE_COVERAGE is
	section PROPERTY
		@begin_step = 0; 	     // Nombre de pas de calcul "cumulés" avant de débuter la vérification de la couverture

		@stop = true;			// Arrète l'exécution dès que la couverture est complète
		@slice = true;			// Elagage du graphe des scénarios à la fin de la vérification


		@strict = true;			// Une machine est couverse si et seulement si ses sous machines le sont aussi

		@scope = 'DETAILS'; 	// 'INSTANCE' | 'FORM' | 'DETAILS'
	endsection PROPERTY

	section DETAILS 			// Utilisé pour préciser les machines ou les transitions particulières à couvrir!
		@form = spec::ascenseur.ascenseur.enregistrer;

		@instance = spec::ascenseur.ascenseur.controler;

		@machine = spec::ascenseur.ascenseur.aller_a_l_etage.attente;
	endsection DETAILS
endprototype
 ***************************************************************************
 */


/**
 * DESTRUCTOR
 */
MachineCoverageFilter::~MachineCoverageFilter()
{
	if( mExecutableCoverageTable != nullptr )
	{
		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		std::size_t endOffset = mMachineCoverageTable->size();
		for( std::size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mMachineCoverageTable->at(i)
				!= mExecutableCoverageTable->at(
						anED.getRuntime(i).refExecutable().getOffset()) )
			{
				delete( mMachineCoverageTable->at(i) );
			}
		}

		delete( mMachineCoverageTable );

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

	else if( mMachineCoverageTable != nullptr )
	{
		std::size_t endOffset = mMachineCoverageTable->size();
		for( std::size_t i = 0 ; i < endOffset ; ++i )
		{
			if( mMachineCoverageTable->at(i) != nullptr )
			{
				delete( mMachineCoverageTable->at(i) );
			}
		}

		delete( mMachineCoverageTable );
	}
}


/**
 * CONFIGURE
 */

bool MachineCoverageFilter::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();

	const WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		mScope = Query::getWPropertyString(thePROPERTY, "scope", "INSTANCE");

		mStrictFlag = Query::getWPropertyBoolean(thePROPERTY, "strict", false);

		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		mMachineCoverageTable = new ArrayOfBitset(
				anED.getTableOfRuntime().size(), nullptr);

		if( mScope == "INSTANCE" )
		{
			// INITIALISATION de la table de toutes
			// les MACHINE associés à chacune des INSTANCE...
			configureInstanceCoverageTableFlag(false);
		}

		else if( (mScope == "MODEL") || (mScope == "FORM") )
		{
			// INITIALISATION de la table de toutes
			// les MACHINE associés à chacune des EXECUTABLE...
			configureExecutableCoverageTableFlag(false);

			// INITIALISATION de la table de toutes
			// les MACHINE associés à chacune des INSTANCE...
			configureInstanceCoverageTableFlag();
		}

		else if( mScope == "DETAILS" )
		{
			const WObject * theDETAILS = Query::getRegexWSequence(
					getParameterWObject(), OR_WID2("details", "DETAILS"));

			if( theDETAILS != WObject::_NULL_ )
			{
				ExecutableForm * anExecutable = nullptr;
				RuntimeID aRID;

				ListOfExecutableForm listOfExecutable;
				List< RuntimeID > listOfInstance;
				List< RuntimeID > listOfMachine;

				ExecutableQuery XQuery( getConfiguration() );

				WObject::const_iterator itWfO = theDETAILS->owned_begin();
				WObject::const_iterator endWfO = theDETAILS->owned_end();
				for( ; itWfO != endWfO ; ++itWfO )
				{
					if( (*itWfO)->isWProperty() )
					{
						const std::string & kind = (*itWfO)->getNameID();
						const std::string & qnid = (*itWfO)->toStringValue();

						if( (kind == "model") || (kind == "form") )
						{
							anExecutable = XQuery.getExecutableByQualifiedNameID(
									qnid ).to_ptr< ExecutableForm >();
							if( anExecutable != nullptr )
							{
								listOfExecutable.append(anExecutable);
							}
							else
							{
								AVM_OS_WARN << "Unfound the model machine "
										<< kind << " << " << qnid
										<< " >> as coverage processor parameter:> "
										<< getParameterWObject()
												->getFullyQualifiedNameID()
										<< std::endl;
							}
						}
						else if( kind == "instance" )
						{
							InstanceOfMachine * anInstance =
									XQuery.getMachineByQualifiedNameID(
											Specifier::DESIGN_INSTANCE_KIND,
											qnid ).rawMachine();
							if( anInstance != nullptr )
							{
								listOfInstance.append(
										anED.getRuntimeID(* anInstance) );
							}
							else
							{
								aRID = anED.getRuntimeID( qnid );
								if( aRID.valid() )
								{
									listOfInstance.append( aRID );
								}
								else
								{
									AVM_OS_WARN << "Unfound the instance machine "
										<< kind << " << " << qnid
										<< " >> as coverage processor parameter:> "
										<< getParameterWObject()
											->getFullyQualifiedNameID()
										<< std::endl;
								}
							}
						}
						else if( kind == "machine" )
						{
							const BF & anInstance =
									XQuery.getMachineByQualifiedNameID(
										Specifier::DESIGN_INSTANCE_KIND, qnid);
							if( anInstance != nullptr )
							{
								listOfMachine.append( anED.getRuntimeID(
										anInstance.to< InstanceOfMachine >()) );
							}
							else
							{
								aRID = anED.getRuntimeID( qnid );
								if( aRID.valid() )
								{
									listOfMachine.append( aRID );
								}
								else
								{
									AVM_OS_WARN << "Unfound the machine << "
										<< qnid
										<< " >> as machine coverage parameter"
										<< std::endl;
								}
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


				// INITIALISATION de la table de toutes
				// les MACHINE associés à chacune des EXECUTABLE...
				configureExecutableCoverageTableFlag(true);

				for( const auto & itExec : listOfExecutable )
				{
					configureExecutableCoverageTableFlag((* itExec), false);
				}


				// Cas des machines
				configureMachineCoverageTableFlag(listOfMachine, false);


				// INITIALISATION de la table de toutes
				// les MACHINE associés à chacune des INSTANCE...
				List< RuntimeID >::iterator itRID = listOfInstance.begin();
				List< RuntimeID >::iterator endRID = listOfInstance.end();
				for( ; itRID != endRID ; ++itRID )
				{
					if( (*itRID).hasExecutable() )
					{
						configureInstanceCoverageTableFlag(anED, (*itRID), false);
					}
				}

				// INITIALISATION de la table de toutes
				// les MACHINE associés à chacune des INSTANCE...
				configureInstanceCoverageTableFlag();
			}
			else
			{
				AVM_OS_WARN << "Unfound section << DETAILS >> as machine "
						"coverage parameter" << std::endl;
			}
		}
		else
		{
			AVM_OS_WARN << "Unexpected scope << " + mScope + " >> as machine "
					"coverage parameter" << std::endl;
		}


AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << "Uncovered Program Count at the beginning :> "
			<< mCoverageStatistics.mNumberOfElements << std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
	}

	return mConfigFlag;
}



void MachineCoverageFilter::configureExecutableCoverageTableFlag(bool value)
{
	if( mExecutableCoverageTable == nullptr )
	{
		mExecutableCoverageTable = new ArrayOfBitset(
				getConfiguration().getExecutableSystem().size(), nullptr);
	}

	TableOfExecutableForm::const_raw_iterator itExec =
			getConfiguration().getExecutableSystem().getExecutables().begin();
	TableOfExecutableForm::const_raw_iterator endExec =
			getConfiguration().getExecutableSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		if( mExecutableCoverageTable->at((itExec)->getOffset()) == nullptr )
		{
			mExecutableCoverageTable->set(
					(itExec)->getOffset(), new Bitset(1, true));
		}
		if( (not value)
			&& mExecutableCoverageTable->at((itExec)->getOffset())->test(0) )
		{
			mExecutableCoverageTable->at((itExec)->getOffset())->set(0, value);

			mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << "executable :> " << (itExec)->getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
		}
	}
}


void MachineCoverageFilter::configureExecutableCoverageTableFlag(
		const ExecutableForm & anExecutable, bool value)
{
	if( mExecutableCoverageTable == nullptr )
	{
		mExecutableCoverageTable = new ArrayOfBitset(
				getConfiguration().getExecutableSystem().size(), nullptr);
	}

	if( mExecutableCoverageTable->at(anExecutable.getOffset()) == nullptr )
	{
		mExecutableCoverageTable->set(
				anExecutable.getOffset(), new Bitset(1, true));
	}
	if( (not value)
		&& mExecutableCoverageTable->at(anExecutable.getOffset())->test(0) )
	{
		mExecutableCoverageTable->at(anExecutable.getOffset())->set(0, value);

		mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << "executable :> " << anExecutable.getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
	}

	// Cas des sous machine executable
	if( anExecutable.hasInstanceStatic() )
	{
		for( const auto & itInstanceStatic : anExecutable.getInstanceStatic() )
		{
			configureExecutableCoverageTableFlag(
					itInstanceStatic.getExecutable(), value);
		}
	}
}


void MachineCoverageFilter::configureInstanceCoverageTableFlag()
{
	if( mExecutableCoverageTable != nullptr)
	{
		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		if( mMachineCoverageTable == nullptr )
		{
			mMachineCoverageTable =
					new ArrayOfBitset(anED.getTableOfRuntime().size(), nullptr);
		}

		std::size_t endMachine = mMachineCoverageTable->size();
		for( std::size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
		{
			if(  mMachineCoverageTable->at(itMachine) == nullptr )
			{
				mMachineCoverageTable->set(itMachine,
						mExecutableCoverageTable->at(anED.getRuntime(
								itMachine ).refExecutable().getOffset()) );
			}
		}
	}
}



void MachineCoverageFilter::configureInstanceCoverageTableFlag(bool value)
{
	const ExecutionData & anED = getConfiguration().getMainExecutionData();

	if( mMachineCoverageTable == nullptr )
	{
		mMachineCoverageTable =
				new ArrayOfBitset(anED.getTableOfRuntime().size(), nullptr);
	}

	std::size_t endMachine = mMachineCoverageTable->size();
	for( std::size_t itMachine = 0 ; itMachine < endMachine ; ++itMachine )
	{
		if( mMachineCoverageTable->at(itMachine) == nullptr )
		{
			mMachineCoverageTable->set(itMachine, new Bitset(1, true));
		}
		if( (! value) && mMachineCoverageTable->at(itMachine)->test(0) )
		{
			mMachineCoverageTable->at(itMachine)->set(0, value);

			mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << "machine :> "
			<< anED.getRuntime(itMachine).getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
		}
	}
}


void MachineCoverageFilter::configureInstanceCoverageTableFlag(
		const ExecutionData & anED, const RuntimeID & aRID, bool value)
{
	if( mMachineCoverageTable == nullptr )
	{
		mMachineCoverageTable =
				new ArrayOfBitset(anED.getTableOfRuntime().size(), nullptr);
	}

	if( mMachineCoverageTable->at(aRID.getOffset()) == nullptr )
	{
		mMachineCoverageTable->set(aRID.getOffset(), new Bitset(1, true));
	}
	if( (! value) && mMachineCoverageTable->at(aRID.getOffset())->test(0) )
	{
		mMachineCoverageTable->at(aRID.getOffset())->set(0, value);

		mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << "machine :> " << aRID.getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
	}

	// Cas des sous machine instance
	if( anED.getRuntime(aRID).hasChild() )
	{
		TableOfRuntimeID::const_iterator itMachineID =
				anED.getRuntime(aRID).beginChild();
		TableOfRuntimeID::const_iterator endMachineID =
				anED.getRuntime(aRID).endChild();
		for( ; itMachineID != endMachineID ; ++itMachineID )
		{
			if( (*itMachineID).hasExecutable()  )
			{
				configureInstanceCoverageTableFlag(anED, (*itMachineID), value);
			}
		}
	}
}


void MachineCoverageFilter::configureMachineCoverageTableFlag(
		const List< RuntimeID > & listOfMachine, bool value)
{
	if( mMachineCoverageTable == nullptr )
	{
		const ExecutionData & anED = getConfiguration().getMainExecutionData();

		mMachineCoverageTable =
				new ArrayOfBitset(anED.getTableOfRuntime().size(), nullptr);
	}

AVM_IF_DEBUG_FLAG_AND( PROCESSOR , (! value) && listOfMachine.nonempty() )
	AVM_OS_TRACE << "machine :> user details" << std::endl;
AVM_ENDIF_DEBUG_FLAG_AND( PROCESSOR )

	List< RuntimeID >::const_iterator itRID = listOfMachine.begin();
	List< RuntimeID >::const_iterator endRID = listOfMachine.end();
	for( ; itRID != endRID ; ++itRID )
	{
		if( mMachineCoverageTable->at((*itRID).getOffset()) == nullptr )
		{
			mMachineCoverageTable->set(
					(*itRID).getOffset(), new Bitset(1, true));
		}
		if( (not value)
			&& mMachineCoverageTable->at( (*itRID).getOffset() )->test(0) )
		{
			mMachineCoverageTable->at((*itRID).getOffset())->set(0, value);

			mCoverageStatistics.addUncoveredElement();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << "\t" << "machine :> " << (*itRID).getFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
		}
	}

AVM_IF_DEBUG_FLAG_AND( PROCESSOR , (! value) && listOfMachine.nonempty() )
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG_AND( PROCESSOR )
}



/**
 * INIT
 */
bool MachineCoverageFilter::preprocess()
{
	if( mBeginningStepTimout == 0 )
	{
		ListOfExecutionContext::iterator it =
				getExecutionQueue().getInitQueue().begin();
		ListOfExecutionContext::iterator itEnd =
				getExecutionQueue().getInitQueue().end();

		if( mCoverageStatistics.hasUncovered() )
		{
			for ( ; it != itEnd ; ++it)
			{
				checkMachine( *it );
			}
		}
		else if( not mStopFlag )
		{
			for ( ; it != itEnd ; ++it)
			{
				checkMachineAfter( (*it) );
			}
		}
	}
	else
	{
		--mBeginningStepTimout;
	}

	return( true );
}





/**
 * FILTERING
 */

bool MachineCoverageFilter::postfilter(ExecutionContext & anEC)
{
	if( mCoverageStatistics.hasUncovered() )
	{
		itEndEC = anEC.end();
		for( itEC = anEC.begin() ; itEC != itEndEC ; ++itEC )
		{
			checkMachine( (*itEC) );
		}
	}
	else if( not mStopFlag )
	{
		itEndEC = anEC.end();
		for( itEC = anEC.begin() ; itEC != itEndEC ; ++itEC )
		{
			checkMachineAfter( (*itEC) );
		}
	}

	return true;
}

void MachineCoverageFilter::setCoverage(
		ExecutionContext * anEC, avm_offset_t rid)
{
	if( mStrictFlag )
	{
		bool isCoverage = true;

		const RuntimeForm & aRF = anEC->getExecutionData().getRuntime(rid);

		TableOfRuntimeID * childMachine = aRF.getChildTable();
		if( childMachine != nullptr )
		{
			AVM_OS_ASSERT_FATAL_ERROR_EXIT( childMachine->get(0) == aRF.getRID() )
					<< "Unexpected RuntimeForm without THIS as first child !!!"
					<< SEND_EXIT;

			// We have to ignore the runtime form THIS at the first position
			std::size_t endMachine = childMachine->size();
			for( std::size_t itMachine = 1 ; itMachine < endMachine ; ++itMachine )
			{
				if( not mMachineCoverageTable->at(
						childMachine->get(itMachine).getOffset())->test(0) )
				{
					isCoverage = false;
					break;
				}
			}
		}

		if( isCoverage )
		{
			mMachineCoverageTable->at(rid)->set(0, true);

			mCoverageStatistics.addCoveredElement();

			anEC->getwFlags().addCoverageElementTrace();

			anEC->addInfo(*this,
					ExpressionConstructor::newIdentifier( aRF.getNameID() ));

			mListOfPositiveEC.append( anEC );

			if( mCoverageStatistics.hasUncovered() && aRF.hasParentRID() )
			{
				setCoverage(anEC, aRF.getParentRID().getOffset());
			}
		}
	}
	else
	{
		mMachineCoverageTable->at(rid)->set(0, true);

		mCoverageStatistics.addCoveredElement();

		anEC->addInfo(*this, ExpressionConstructor::newIdentifier(
				anEC->getExecutionData().getRuntime(rid).getNameID() ) );

		mListOfPositiveEC.append( anEC );
	}
}

void MachineCoverageFilter::checkMachine(ExecutionContext * anEC)
{
	const TableOfRuntimeFormState * tableOfState =
			anEC->getExecutionData().getRuntimeFormStateTable();

	std::size_t endMachine = tableOfState->size();
	for( avm_offset_t offset = 0 ; offset < endMachine ; ++offset )
	{
		if( tableOfState->isIdleOrRunning(offset) &&
				(! mMachineCoverageTable->at(offset)->test(0)) )
		{
			setCoverage(anEC, offset);
		}
	}

	checkMachine(anEC, anEC->getRunnableElementTrace());
}


void MachineCoverageFilter::checkMachine(ExecutionContext * anEC,
		const BF & aFiredCode)
{
	if( aFiredCode.invalid() )
	{
		return;
	}

	// Vérification de la création de nouvelle instance dynamique
	// par la commande ${ EXEC }
	if( anEC->getExecutionData().getTableOfRuntime().size() >
			mMachineCoverageTable->size() )
	{
		// TODO
		return;
	}


	switch( aFiredCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{

			for( const auto & itOperand :
				aFiredCode.to< AvmCode >().getOperands() )
			{
				checkMachine(anEC, itOperand);
			}

			break;
		}

		case FORM_EXECUTION_CONFIGURATION_KIND:
		{
			const ExecutionConfiguration & anExecConf =
					aFiredCode.to< ExecutionConfiguration >();

			if( anExecConf.getOperator().isTEQ( OperatorManager::OPERATOR_RUN ) )
			{
				RuntimeID aRID = anExecConf.getRuntimeID();
				avm_offset_t rid = aRID.getOffset();

				if( not mMachineCoverageTable->at(rid)->test(0) )
				{
					setCoverage(anEC, rid);

					aRID = aRID.getPRID();
					while( aRID.valid() )
					{
						rid = aRID.getOffset();

						if( not mMachineCoverageTable->at(rid)->test(0) )
						{
							setCoverage(anEC, rid);
						}
						else
						{
							break;
						}

						aRID = aRID.getPRID();
					}

				}
			}
			break;
		}

		default:
		{
			break;
		}
	}
}


void MachineCoverageFilter::checkMachineAfter(ExecutionContext * anEC)
{
//	TableOfRuntimeFormState * tableOfState =
//			anEC->getExecutionData().getRuntimeFormStateTable();
//
//	std::size_t endState = tableOfState->size();
//	for( std::size_t i = 0 ; i != endState ; ++i )
//	{
//		if( tableOfState->isIdleOrRunning(i)
//			&& (not mMachineCoverageTable->at(i)) )
//		{
//		}
//	}
}





/*
 * REPORT
 */

void MachineCoverageFilter::reportDefault(OutStream & os) const
{
	reportHeader(os, QNID());

	if( mCoverageStatistics.goalAchieved() )
	{
		os << TAB2 << "All the << " << mCoverageStatistics.mNumberOfElements
				<< " >> machines are covered !" << EOL;
	}
	else
	{
		os << TAB2 << "Warning: all machines are not covered !" << EOL;
		mCoverageStatistics.toStreamCoverageRate( os << TAB2,
				"Results: << ", " on "," >> are covered !\n" );

		if ( isReportDetails() )
		{
			os << TAB2 << "List of the << "
					<< mCoverageStatistics.getNumberOfUncovered()
					<<  " >> machines non covered:" << EOL;

			const ExecutionData & anED =
					getConfiguration().getMainExecutionData();

			if( (mScope == "INSTANCE") & (mMachineCoverageTable != nullptr) )
			{
				std::size_t endMachine = mMachineCoverageTable->size();
				for( std::size_t itRF = 0 ; itRF < endMachine ; ++itRF )
				{
					if( not mMachineCoverageTable->at( itRF )->test(0) )
					{
						os << TAB3 << "machine :> "
							<< anED.getRuntime(itRF).getFullyQualifiedNameID()
							<< EOL;
					}
				}
			}

			else if( ((mScope == "MODEL") || (mScope == "FORM")) &&
					(mExecutableCoverageTable != nullptr) )
			{
				TableOfExecutableForm::const_raw_iterator itExec =
						getConfiguration().getExecutableSystem()
								.getExecutables().begin();
				TableOfExecutableForm::const_raw_iterator endExec =
						getConfiguration().getExecutableSystem()
								.getExecutables().end();
				for( ; itExec != endExec ; ++itExec )
				{
					if( not mExecutableCoverageTable->at(
							(itExec)->getOffset() )->test(0) )
					{
						os << TAB3 << "executable :> "
								<< (itExec)->getFullyQualifiedNameID() << EOL;
					}
				}
			}

			else if( mScope == "DETAILS" )
			{
				if( mExecutableCoverageTable != nullptr )
				{
					TableOfExecutableForm::const_raw_iterator itExec =
							getConfiguration().getExecutableSystem()
									.getExecutables().begin();
					TableOfExecutableForm::const_raw_iterator endExec =
							getConfiguration().getExecutableSystem()
									.getExecutables().end();
					for( ; itExec != endExec ; ++itExec )
					{
						if( not mExecutableCoverageTable->at(
								(itExec)->getOffset() )->test(0) )
						{
							os << TAB3 << "executable :> "
									<< (itExec)->getFullyQualifiedNameID() << EOL;
						}
					}
				}

				if( mMachineCoverageTable != nullptr )
				{
					std::size_t endMachine = mMachineCoverageTable->size();
					for( std::size_t itRF = 0 ; itRF < endMachine ; ++itRF )
					{
						if( (! mMachineCoverageTable->at( itRF )->test(0))
							&& mExecutableCoverageTable->at(anED.getRuntime(
								itRF ).refExecutable().getOffset())->test(0) )
						{
							os << TAB3 << "machine :> "
								<< anED.getRuntime(
										itRF ).getFullyQualifiedNameID()
								<< EOL;
						}
					}
				}
			}
		}
	}

	if ( isReportDetails() && mCoverageStatistics.hasUncovered() )
	{
		mCoverageStatistics.toStreamCoverageRate( os << TAB2,
				"Results: << ", " on "," >> are covered !\n" );
	}

	if( mSliceFlag )
	{
		os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
	}

	os << std::flush;
}




}
