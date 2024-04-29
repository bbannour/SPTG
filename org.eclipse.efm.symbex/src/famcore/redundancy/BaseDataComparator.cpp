/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "BaseDataComparator.h"

#include  <famcore/redundancy/RedundancyFilter.h>

#include <fml/buffer/BaseBufferForm.h>
#include <fml/buffer/BaseBufferQueue.h>
#include <fml/buffer/RamBuffer.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionFactory.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeForm.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * destroyMachineData
 */

void BaseDataComparator::destroyMachineData()
{
	mListOfSelectedIOMachine.clear();

	mListOfAllVariable.clear();

	mListOfSelectedPresburgerVariable.clear();

	mListOfSelectedNonPresburgerVariable.clear();
}


/**
 ***************************************************************************
prototype filter::redundancy as avm::core.filter.REDUNDANCY is
section PROPERTY
	@predicate = 'INCLUSION';  // ( <=  | INC | INCLUSION )
	                              ( ==  | EQ  | EQUALITY )
	                              ( =a= | AEQ | ALPHA_EQUIV)
	                              ( =s= | SEQ | SYNTAXIC_EQUALITY)
	                              ( =t= | TEQ | TRIVIALLY_EQUALITY)
	                              NONE

	@solver = 'OMEGA';         // OMEGA | CVC4

	@path_scope = 'ALL';       // ALL | CURRENT execution graph path

	@data_scope = 'ALL';       // ALL data ; or DETAILS section
	                           // DETAILS | DETAILS< exclude > some data,
endsection PROPERTY

section HEURISTIC
	@communication = false;

	@variable = true;
	@path_condition = false;
endsection HEURISTIC

section DETAILS
	@model = ufi;

	@instance = ufi;

	@variable = ufi;
endsection DETAILS
endprototype
 ***************************************************************************
 */

/**
 * CONFIGURE
 */
bool BaseDataComparator::configure(const WObject * wfParameterObject)
{
	const ExecutionData & theED = mConfiguration.getMainExecutionData();

	mMachineCount = theED.getTableOfRuntime().size();

	const WObject * thePROPERTY =
		RedundancyFilter::AUTO_REGISTER_TOOL.isTypeID( *wfParameterObject )
			? Query::getRegexWSequence(wfParameterObject,
					OR_WID2("property", "PROPERTY"), wfParameterObject)
			: Query::getRegexWSequence(wfParameterObject,
					OR_WID2("redundancy" , "REDUNDANCY"), wfParameterObject);

	std::string path_scope = Query::getRegexWPropertyString(
					thePROPERTY, CONS_WID2("path", "scope"), "ALL");
	mCurrentPathScopeFlag =
			( (path_scope == "CURRENT") || (path_scope == "PARENT") );

	std::string data_scope = Query::getRegexWPropertyString(
			thePROPERTY, CONS_WID2("data", "scope"), "ALL");


	const WObject * theHEURISTIC =
		RedundancyFilter::AUTO_REGISTER_TOOL.isTypeID( *wfParameterObject )
			? Query::getRegexWSequence(wfParameterObject,
					OR_WID2("heuristic", "HEURISTIC"), thePROPERTY)
			: Query::getRegexWSequence(wfParameterObject,
					OR_WID2("redundancy" , "REDUNDANCY"), thePROPERTY);

	if( theHEURISTIC != WObject::_NULL_ )
	{
		mUseCommunication = Query::getWPropertyBoolean(
				theHEURISTIC, "communication", true);

		mUseVariable = Query::getWPropertyBoolean(
				theHEURISTIC, "variable", true);

		mIgnorePathCondition = not Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID2("path", "condition"), true);
	}


	if( data_scope == "ALL" )
	{
		computeAllMachineData(theED);
	}
	// TODO configure for @data_scope = 'DETAILS';
	else if( StringTools::startsWith(data_scope, "DETAILS") )
	{
		const WObject * theDETAILS =
			RedundancyFilter::AUTO_REGISTER_TOOL.isTypeID( *wfParameterObject )
				? Query::getRegexWSequence(wfParameterObject,
						OR_WID2("details", "DETAILS"), thePROPERTY)
				: Query::getRegexWSequence(wfParameterObject,
						OR_WID2("redundancy" , "REDUNDANCY"), thePROPERTY);

		if( theDETAILS != WObject::_NULL_ )
		{
			ExecutableForm * anExecutable = nullptr;
			InstanceOfMachine * aMachine = nullptr;
			InstanceOfData * aVariable = nullptr;

			ListOfExecutableForm listOfExecutable;
			ListOfInstanceOfMachine listOfInstance;
			ListOfInstanceOfData listOfVariable;

			ExecutableQuery XQuery( mConfiguration );

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
						anExecutable = XQuery.getExecutable(
								qnid ).to_ptr< ExecutableForm >();
						if( anExecutable != nullptr )
						{
							listOfExecutable.append(anExecutable);
						}
						else
						{
							AVM_OS_WARN << "Unfound the machine "
								<< kind << " << " << qnid
								<< " >> as processor parameter:> "
								<< wfParameterObject->getFullyQualifiedNameID()
								<< std::endl;
						}
					}
					else if( kind == "instance" )
					{
						aMachine = XQuery.getMachine(
							Specifier::DESIGN_INSTANCE_KIND, qnid).rawMachine();
						if( aMachine != nullptr )
						{
							listOfInstance.append(aMachine);
						}
						else
						{
							AVM_OS_WARN << "Unfound the machine "
								<< kind << " << " << qnid
								<< " >> as processor parameter:> "
								<< wfParameterObject->getFullyQualifiedNameID()
								<< std::endl;
						}
					}
					// TODO: à faire pour les variables.
					else if( kind == "variable" )
					{
						aVariable = XQuery.getVariable(
								qnid ).to_ptr< InstanceOfData >();
						if( aVariable != nullptr )
						{
							listOfVariable.append(aVariable);
						}
						else
						{
							AVM_OS_WARN << "Unfound the " << kind << " << "
								<< qnid << " >> as processor parameter:> "
								<< wfParameterObject->getFullyQualifiedNameID()
								<< std::endl;
						}
					}
					else
					{
						AVM_OS_WARN << "Unexpected attribute << "
							<< (*itWfO)->str() << " >> as processor parameter:> "
							<< wfParameterObject->getFullyQualifiedNameID()
							<< std::endl;
					}
				}
			}


			if( data_scope.find("exclude") != std::string::npos )
			{
				computeDetailsExcludeMachineData(theED,
						listOfExecutable, listOfInstance, listOfVariable);
			}
			else
			{
				computeDetailsIncludeMachineData(theED,
						listOfExecutable, listOfInstance, listOfVariable);
			}

		}
		else
		{
			AVM_OS_WARN << "Unfound section << DETAILS >> as redundancy "
					"detector parameter" << std::endl;
		}
	}
	else
	{
		AVM_OS_ERROR_ALERT << "Unexpected REDUNDANCY filter << @data_scope = "
				<< data_scope << "; >> !!!" << std::endl
				<< "NB. << @data_scope = {[ 'ALL' | 'DETAILS' ]}; >> !!!"
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}


void BaseDataComparator::computeAllMachineData(const ExecutionData & anED)
{
	destroyMachineData();

	selectIOMachine(anED, mListOfSelectedIOMachine);

	selectAllVariable(anED, mListOfAllVariable);

	selectPresburgerVariable(anED, mListOfSelectedPresburgerVariable);

	selectNonPresburgerVariable(anED, mListOfSelectedNonPresburgerVariable);
}




void BaseDataComparator::computeDetailsIncludeMachineData(
		const ExecutionData & anED,
		ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance,
		ListOfInstanceOfData & listOfVariable)
{
	destroyMachineData();

	// TODO: réécrire les 4 méthodes suivantes pour prendre en compte les
	// DETAILS contenus dans les deux paramètres additionnels par rapport au cas ALL:

	selectDetailsIOMachine(anED, mListOfSelectedIOMachine,
			listOfExecutable, listOfInstance);

	selectDetailsVariable(anED, mListOfAllVariable,
			listOfExecutable, listOfInstance, listOfVariable);

	selectDetailsPresburgerVariable(anED, mListOfSelectedPresburgerVariable,
			listOfExecutable, listOfInstance, listOfVariable);

	selectDetailsNonPresburgerVariable(
			anED, mListOfSelectedNonPresburgerVariable,
			listOfExecutable, listOfInstance, listOfVariable);

	if( mListOfAllVariable.empty() )
	{
//		AVM_OS_WARNING_ALERT
//				<< "Attention la liste des variables utilisées pour le "
//					"calcul de la redondance est vide (cas DETAILS) !!!"
//				<< SEND_ALERT;
	}
}


static void excludeVariable(ListOfPairMachineData & includeListOfVariable,
		ListOfExecutableForm & excludeListOfExecutable,
		ListOfInstanceOfMachine & excludeListOfInstance,
		ListOfInstanceOfData & excludeListOfVariable)
{
	ListOfExecutableForm::iterator itExec;
	ListOfExecutableForm::iterator endExec;

	ListOfInstanceOfMachine::iterator itRF;
	ListOfInstanceOfMachine::iterator endRF;

	ListOfInstanceOfData::iterator itVar;
	ListOfInstanceOfData::iterator endVar;

	bool hasEraseNothing;

	ListOfPairMachineData::iterator itPairMachineData = includeListOfVariable.begin();
	for( ; itPairMachineData != includeListOfVariable.end() ; )
	{
		hasEraseNothing = true;

		itExec = excludeListOfExecutable.begin();
		endExec = excludeListOfExecutable.end();
		for( ; itExec != endExec ; ++itExec )
		{
			if( (*itPairMachineData).first().getExecutable() == (*itExec) )
			{
				itPairMachineData = includeListOfVariable.erase(itPairMachineData);
				hasEraseNothing = false;
				continue;
			}
		}

		itRF = excludeListOfInstance.begin();
		endRF = excludeListOfInstance.end();
		for( ; itRF != endRF ; ++itRF )
		{
			if( (*itPairMachineData).first().getInstance() == (*itRF) )
			{
				itPairMachineData = includeListOfVariable.erase(itPairMachineData);
				hasEraseNothing = false;
				continue;
			}
		}

		for( const auto & itVariable : excludeListOfVariable )
		{
			(*itPairMachineData).second().remove( itVariable );
			if( (*itPairMachineData).second().empty() )
			{
				itPairMachineData = includeListOfVariable.erase(itPairMachineData);
				hasEraseNothing = false;
				continue;
			}
		}

		if( hasEraseNothing )
		{
			++itPairMachineData;
		}
	}
}


void BaseDataComparator::computeDetailsExcludeMachineData(
		const ExecutionData & anED,
		ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance,
		ListOfInstanceOfData & listOfVariable)
{
	computeAllMachineData(anED);

	excludeVariable(mListOfAllVariable,
			listOfExecutable, listOfInstance, listOfVariable);

	excludeVariable(mListOfSelectedPresburgerVariable,
			listOfExecutable, listOfInstance, listOfVariable);

	excludeVariable(mListOfSelectedNonPresburgerVariable,
			listOfExecutable, listOfInstance, listOfVariable);

}





void BaseDataComparator::selectIOMachine(const ExecutionData & anED,
		List< RuntimeID > & aListOfSelectedIOMachine)
{
	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator itRFEnd = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != itRFEnd ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( itRID.refExecutable().hasBuffer() )
		{
			aListOfSelectedIOMachine.append( itRID );
		}
	}
}

void BaseDataComparator::selectDetailsIOMachine(
		const ExecutionData & anED,
		List< RuntimeID > & aListOfSelectedIOMachine,
		ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance)
{
	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator itRFEnd = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != itRFEnd ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( itRID.refExecutable().hasBuffer()
			&& ( listOfExecutable.contains(itRID.getExecutable())
				|| listOfInstance.contains(itRID.getInstance()) ) )
		{
			aListOfSelectedIOMachine.append( itRID );
		}
	}
}

void BaseDataComparator::selectAllVariable(const ExecutionData & anED,
		ListOfPairMachineData & aListOfSelectedVariable)
{
	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator itVarEnd;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator itRFEnd = anED.getTableOfRuntime().end();
	for( RuntimeForm * pRF = nullptr ; itRF != itRFEnd ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->refExecutable().hasVariable() )
		{
			aListOfSelectedVariable.append( PairMachineData(pRF->getRID()) );
			ListOfInstanceOfData & listOfData =
					aListOfSelectedVariable.last().second();

			itVar = pRF->getVariables().begin();
			itVarEnd = pRF->getVariables().end();
			for( ; itVar != itVarEnd ; ++itVar )
			{
				listOfData.append( (itVar) );
			}

			if( listOfData.empty() )
			{
				aListOfSelectedVariable.pop_last();
			}
		}
	}
}


// todo: collecter toutes les variables dans les sous-machines ...
//void  BaseDataComparator::collectDetailsVariables(const RuntimeID & aRID,
//		ListOfPairMachineData & aListOfSelectedVariable,
//		ListOfExecutableForm & listOfExecutable,
//		ListOfInstanceOfMachine & listOfInstance)
//{
//	PairMachineData * tmpPairMachineData = new PairMachineData(aRID);
//	TableOfInstanceOfData::const_raw_iterator itVar = aRID->getVariables().begin();
//	TableOfInstanceOfData::const_raw_iterator endVar = aRID->getVariables().end();
//	for( ; itVar != endVar ; ++itVar )
//	{
//		if( (itVar)->anyModifierOfStateData()
//			&& (itVar)->hasTypeSpecifier()
//			&& ((itVar)->isTypedNumeric()
//				|| (itVar)->isTypedEnumeration()) )
//		{
//			tmpPairMachineData->second().append( (itVar) );
//		}
//	}
//	if( tmpPairMachineData->second().nonempty() )
//	{
//		aListOfSelectedVariable.append(tmpPairMachineData);
//	}
//	else
//	{
//		delete( tmpPairMachineData );
//	}
//	TableOfRuntimeID::iterator itRecRID = (*itmachine)->beginChildTable() ;
//	TableOfRuntimeID::iterator itRecEnd = (*itmachine)->endChildTable() ;
//	for( ; itRecRID != itRecEnd ; ++itRecRID )
//	{
//		//itRecMachine
//	}
//}



std::size_t BaseDataComparator::selectVariable(
		ListOfInstanceOfData & listOfData, const InstanceOfData * pData)
{
	if( pData->getModifier().anyModifierOfStateData() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( pData->hasTypeSpecifier() )
				<< "Unexpected variable << " << pData->getFullyQualifiedNameID()
				<< " >> without type specififer !!!"
				<< SEND_EXIT;

		std::size_t varCount = 0;

		if( pData->isTypedNumeric()     ||
			pData->isTypedEnumeration() ||
			pData->isTypedMachine()     )
		{
			++varCount;

			listOfData.append( const_cast< InstanceOfData * >(pData) );
		}
		else if( pData->hasTypeArrayOrStructure() )
		{
			TableOfSymbol::iterator attrIt = pData->getAttribute()->begin();
			TableOfSymbol::iterator attrEnd = pData->getAttribute()->end();
			for( ; attrIt != attrEnd ; ++attrIt )
			{
				varCount += selectVariable(listOfData, (*attrIt).
						variable().getAliasTarget()->as_ptr< InstanceOfData >() );
			}
		}

		return( varCount );
	}

	return( 0 );
}


std::size_t BaseDataComparator::selectPresburgerVariable(
		ListOfInstanceOfData & listOfData, const InstanceOfData * pData)
{
	if( pData->getModifier().anyModifierOfStateData() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( pData->hasTypeSpecifier() )
				<< "Unexpected variable << " << pData->getFullyQualifiedNameID()
				<< " >> without type specififer !!!"
				<< SEND_EXIT;

		std::size_t varCount = 0;

		if( pData->weaklyTypedInteger() ||
			pData->isTypedEnumeration() ||
			pData->isTypedMachine()     )
		{
			++varCount;

			listOfData.append( const_cast< InstanceOfData * >(pData) );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "\tpresburger :> " << str_header( pData ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
		}
		else if( pData->hasTypeArrayOrStructure() )
		{
			TableOfSymbol::iterator attrIt = pData->getAttribute()->begin();
			TableOfSymbol::iterator attrEnd = pData->getAttribute()->end();
			for( ; attrIt != attrEnd ; ++attrIt )
			{
				varCount += selectPresburgerVariable(listOfData, (*attrIt).
						variable().getAliasTarget()->as_ptr< InstanceOfData >() );
			}
		}
		else
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "\tNON presburger :> " << str_header( pData ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
		}

		return( varCount );
	}

	return( 0 );
}


std::size_t BaseDataComparator::selectNonPresburgerVariable(
		ListOfInstanceOfData & listOfData, const InstanceOfData * pData)
{
	if( pData->getModifier().anyModifierOfStateData() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( pData->hasTypeSpecifier() )
				<< "Unexpected variable << " << pData->getFullyQualifiedNameID()
				<< " >> without type specififer !!!"
				<< SEND_EXIT;

		std::size_t varCount = 0;

		if( (not pData->weaklyTypedInteger()) &&
			(not pData->isTypedEnumeration()) &&
			(not pData->isTypedMachine())     )
		{
			++varCount;

			listOfData.append( const_cast< InstanceOfData * >(pData) );
		}
		else if( pData->hasTypeArrayOrStructure() )
		{
			TableOfSymbol::iterator attrIt = pData->getAttribute()->begin();
			TableOfSymbol::iterator attrEnd = pData->getAttribute()->end();
			for( ; attrIt != attrEnd ; ++attrIt )
			{
				selectNonPresburgerVariable(listOfData, (*attrIt).
						variable().getAliasTarget()->as_ptr< InstanceOfData >() );
			}
		}

		return( varCount );
	}

	return( 0 );
}


// TODO: attention on ne prend pas en compte les SOUS-machines !!!
void BaseDataComparator::selectDetailsVariable(const ExecutionData & anED,
		ListOfPairMachineData & aListOfSelectedVariable,
		ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance,
		ListOfInstanceOfData & listOfVariable)
{
	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator itVarEnd;

	ListOfInstanceOfData::iterator varIt;
	ListOfInstanceOfData::iterator varEnd;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator itRFEnd = anED.getTableOfRuntime().end();
	for( RuntimeForm * pRF = nullptr ; itRF != itRFEnd ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->refExecutable().hasVariable() )
		{
			if( listOfInstance.contains(pRF->getInstance()) ||
				listOfExecutable.contains(pRF->getExecutable()) )
			{
				aListOfSelectedVariable.append(
						PairMachineData(pRF->getRID()) );
				ListOfInstanceOfData & listOfData =
						aListOfSelectedVariable.last().second();

				itVar = pRF->getVariables().begin();
				itVarEnd = pRF->getVariables().end();
				for( ; itVar != itVarEnd ; ++itVar )
				{
					selectVariable(listOfData, (itVar));
				}

				// TODO: parcourir les children
//				TableOfRuntimeID::iterator itRecMachine = (*itmachine)->beginChildTable() ;
//				TableOfRuntimeID::iterator itRecEnd     = (*itmachine)->endChildTable() ;
//				for( ; itRecMachine != itRecEnd ; ++itRecMachine )
//				{
//				}
			}
			else
			{
				aListOfSelectedVariable.append(
						PairMachineData(pRF->getRID()) );
				ListOfInstanceOfData & listOfData =
						aListOfSelectedVariable.last().second();

				varIt = listOfVariable.begin();
				varEnd = listOfVariable.end();
				for( ; varIt != varEnd ; ++varIt )
				{
					if( pRF->refExecutable().containsAllVariable(*varIt) )
					{
						selectVariable(listOfData, (*varIt));
					}
				}

				if( listOfData.empty() )
				{
					aListOfSelectedVariable.pop_last();
				}
			}
		}
	}
}


void BaseDataComparator::selectPresburgerVariable(const ExecutionData & anED,
		ListOfPairMachineData & aListOfSelectedVariable)
{
	std::size_t varCount = 0;

	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator itVarEnd;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator itRFEnd = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != itRFEnd ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( itRID.refExecutable().hasVariable() )
		{
			aListOfSelectedVariable.append( PairMachineData(itRID) );
			ListOfInstanceOfData & listOfData = aListOfSelectedVariable.last().second();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "presburger machine :> " << itRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )

			itVar = itRID.refExecutable().getBasicVariables().begin();
			itVarEnd = itRID.refExecutable().getBasicVariables().end();
			for( ; itVar != itVarEnd ; ++itVar )
			{
				varCount += selectPresburgerVariable(listOfData, (itVar));
			}

			if( listOfData.empty() )
			{
				aListOfSelectedVariable.pop_last();
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "Total:> " << varCount << std::endl << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
}


void BaseDataComparator::selectDetailsPresburgerVariable(
		const ExecutionData & anED,
		ListOfPairMachineData & aListOfSelectedVariable,
		ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance,
		ListOfInstanceOfData & listOfVariable)
{
	std::size_t varCount = 0;

	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator itVarEnd;

	ListOfInstanceOfData::iterator varIt;
	ListOfInstanceOfData::iterator varEnd;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator itRFEnd = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != itRFEnd ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( itRID.refExecutable().hasVariable() )
		{
			if( listOfExecutable.contains(itRID.getExecutable()) ||
				listOfInstance.contains(itRID.getInstance()))
			{
				aListOfSelectedVariable.append( PairMachineData(itRID) );
				ListOfInstanceOfData & listOfData = aListOfSelectedVariable.last().second();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "presburger machine :> " << itRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )

				itVar = itRID.refExecutable().getBasicVariables().begin();
				itVarEnd = itRID.refExecutable().getBasicVariables().end();
				for( ; itVar != itVarEnd ; ++itVar )
				{
					varCount += selectPresburgerVariable(listOfData, (itVar));
				}

				if( listOfData.empty() )
				{
					aListOfSelectedVariable.pop_last();
				}
			}
			else
			{
				aListOfSelectedVariable.append(
						PairMachineData(itRID) );
				ListOfInstanceOfData & listOfData =
						aListOfSelectedVariable.last().second();

				varIt = listOfVariable.begin();
				varEnd = listOfVariable.end();
				for( ; varIt != varEnd ; ++varIt )
				{
					if( itRID.refExecutable().containsAllVariable(*varIt) )
					{
						varCount += selectPresburgerVariable(listOfData, (*varIt));
					}
				}

				if( listOfData.empty() )
				{
					aListOfSelectedVariable.pop_last();
				}
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "Total:> " << varCount << std::endl << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )

}

void BaseDataComparator::selectNonPresburgerVariable(
		const ExecutionData & anED,
		ListOfPairMachineData & aListOfSelectedVariable)
{
	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator itVarEnd;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( RuntimeForm * pRF = nullptr ; itRF != endRF ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->refExecutable().hasVariable() )
		{
			aListOfSelectedVariable.append(
					PairMachineData(pRF->getRID()) );
			ListOfInstanceOfData & listOfData =
					aListOfSelectedVariable.last().second();

//			AVM_OS_TRACE << "presburger machine :> "
//					<< itRID.str() << std::endl;

			itVar = pRF->getVariables().begin();
			itVarEnd = pRF->getVariables().end();
			for( ; itVar != itVarEnd ; ++itVar )
			{
				selectNonPresburgerVariable(listOfData, (itVar));
			}

			if( listOfData.empty() )
			{
				aListOfSelectedVariable.pop_last();
			}
		}
	}
}


void BaseDataComparator::selectDetailsNonPresburgerVariable(
		const ExecutionData & anED,
		ListOfPairMachineData & aListOfSelectedVariable,
		ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance,
		ListOfInstanceOfData & listOfVariable)
{
	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator itVarEnd;

	ListOfInstanceOfData::iterator varIt;
	ListOfInstanceOfData::iterator varEnd;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( RuntimeForm * pRF = nullptr ; itRF != endRF ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->refExecutable().hasVariable() )
		{
			if( listOfExecutable.contains(pRF->getExecutable()) ||
				listOfInstance.contains(pRF->getInstance()) )
			{
				aListOfSelectedVariable.append(
						PairMachineData(pRF->getRID()) );
				ListOfInstanceOfData & listOfData =
						aListOfSelectedVariable.last().second();

//				AVM_OS_TRACE << "Non presburger machine :> "
//						<< itRID.str() << std::endl;

				itVar = pRF->getVariables().begin();
				itVarEnd = pRF->getVariables().end();
				for( ; itVar != itVarEnd ; ++itVar )
				{
					selectNonPresburgerVariable(listOfData, (itVar));
				}

				if( listOfData.empty() )
				{
					aListOfSelectedVariable.pop_last();
				}
			}
			else
			{
				aListOfSelectedVariable.append(
						PairMachineData(pRF->getRID()) );
				ListOfInstanceOfData & listOfData =
						aListOfSelectedVariable.last().second();

				varIt = listOfVariable.begin();
				varEnd = listOfVariable.end();
				for( ; varIt != varEnd ; ++varIt )
				{
					selectNonPresburgerVariable(listOfData, (*varIt));
				}

				if( listOfData.empty() )
				{
					aListOfSelectedVariable.pop_last();
				}
			}
		}
	}
}


/*
 * REFRESH CURRENT PRESBURGER VARIABLE
 */

void BaseDataComparator::refreshCurrentVariables(
		ListOfPairMachineData & currentVariables,
		ListOfPairMachineData & referenceVariables,
		const ExecutionData & newED, const ExecutionData & oldED)
{
	currentVariables.clear();

	ListOfInstanceOfData::iterator itVar;
	ListOfInstanceOfData::iterator endVar;

	for( const auto & itPairMachineData : referenceVariables )
	{
		if( itPairMachineData.second().nonempty() )
		{
			const RuntimeForm & newRF =
					newED.getRuntime( itPairMachineData.first() );
			const RuntimeForm & oldRF =
					oldED.getRuntime( itPairMachineData.first() );

			currentVariables.append( PairMachineData(newRF.getRID()) );
			ListOfInstanceOfData & listOfData = currentVariables.last().second();

			for( const auto & itVar : itPairMachineData.second() )
			{
				if( not ExpressionComparer::isTEQ(
						newRF.getData( itVar->getOffset() ),
						oldRF.getData( itVar->getOffset() )) )
				{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )
	AVM_OS_TRACE << "current var :> " << newRF.getRID().str()
			<< ":" << itVar->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , REDUNDANCE )

					listOfData.append( itVar );
				}
			}

			if( listOfData.empty() )
			{
				currentVariables.pop_last();
			}
		}
	}
}


/*
 * COMPARE
 */
bool BaseDataComparator::compareIO(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	const ExecutionData & newED = newEC.getExecutionData();
	const ExecutionData & oldED = oldEC.getExecutionData();

	TableOfBufferT::const_iterator itNewBuf;
	TableOfBufferT::const_iterator itNewBufEnd;

	TableOfBufferT::const_iterator itOldBuf;

	// compare BUFFER
	List< RuntimeID >::const_iterator itRID = getSelectedIOMachine().begin();
	List< RuntimeID >::const_iterator endRID = getSelectedIOMachine().end();
	for( ; itRID != endRID ; ++itRID )
	{
		newRF = newED.ptrRuntime( *itRID );
		oldRF = oldED.ptrRuntime( *itRID );

		if( newRF->hasBuffer()
			&& (newRF->getBufferTable() != oldRF->getBufferTable()) )
		{
			itNewBuf = newRF->getBufferTable().begin();
			itNewBufEnd = newRF->getBufferTable().end();
			itOldBuf = oldRF->getBufferTable().begin();
			for( ; itNewBuf != itNewBufEnd ; ++itNewBuf, ++itOldBuf )
			{
				if( ((*itNewBuf) != (*itOldBuf))
					&& (not compareBUFFER(*itNewBuf, *itOldBuf)) )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_TRACE << "oldRF :ctx-" << oldEC.getIdNumber() << "> "
			<< oldRF->getRID().str() << std::endl;
	oldRF->getBufferTable().toStream(AVM_OS_TRACE);

	AVM_OS_TRACE << "newRF :ctx-" << newEC.getIdNumber() << "> "
			<< newRF->getRID().str() << std::endl;
	newRF->getBufferTable().toStream(AVM_OS_TRACE);

	AVM_OS_TRACE << ">>>>>>> false <<<<<<<" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )

					return( false );
				}
			}
		}
	}

	return( true );
}


bool BaseDataComparator::compareBUFFER(
		const BaseBufferForm * newBuf, const BaseBufferForm * oldBuf)
{
	switch( newBuf->classKind() )
	{
		case FORM_BUFFER_FIFO_KIND:
		case FORM_BUFFER_LIFO_KIND:
		{
			const BaseBufferQueue * newMsgList = newBuf->to_ptr< BaseBufferQueue >();
			const BaseBufferQueue * oldMsgList = oldBuf->to_ptr< BaseBufferQueue >();

			if( newMsgList->nonempty()
				&& (newMsgList->size() == oldMsgList->size()) )
			{
				ListOfMessage::
				const_iterator itNewMsg = newMsgList->beginMessages();
				ListOfMessage::
				const_iterator itNewMsgEnd = newMsgList->endMessages();
				ListOfMessage::
				const_iterator itOldMsg = oldMsgList->beginMessages();
				for( ; itNewMsg != itNewMsgEnd ; ++itNewMsg, ++itOldMsg )
				{
					if( ((*itNewMsg) != (*itOldMsg))
						&& (not compareMESSAGE((*itNewMsg), (*itOldMsg))) )
					{
						return( false );
					}
				}
				return( true );
			}
			return( newMsgList->empty() );
		}

		case FORM_BUFFER_MULTISET_KIND:
		case FORM_BUFFER_SET_KIND:
		{ // TODO correct comparaison
			const BaseBufferQueue * newMsgList = newBuf->to_ptr< BaseBufferQueue >();
			const BaseBufferQueue * oldMsgList = oldBuf->to_ptr< BaseBufferQueue >();

			if( newMsgList->size() == oldMsgList->size() )
			{
				ListOfMessage::
				const_iterator itNewMsg = newMsgList->beginMessages();
				ListOfMessage::
				const_iterator itNewMsgEnd = newMsgList->endMessages();
				ListOfMessage::
				const_iterator itOldMsg = oldMsgList->beginMessages();
				for( ; itNewMsg != itNewMsgEnd ; ++itNewMsg, ++itOldMsg )
				{
					if( ((*itNewMsg) != (*itOldMsg))
						&& (not compareMESSAGE((*itNewMsg), (*itOldMsg))) )
					{
						return( false );
					}
				}
				return( true );
			}
			return( newMsgList->empty() );
		}

		case FORM_BUFFER_BROADCAST_KIND:
		case FORM_BUFFER_RAM_KIND:
		{
			return( compareMESSAGE(
					newBuf->to_ptr< RamBuffer >()->top(),
					oldBuf->to_ptr< RamBuffer >()->top() ) );
		}

		default :
		{
			return( true );
		}
	}

	return( true );
}


bool BaseDataComparator::compareMESSAGE(
		const Message & newMsg, const Message & oldMsg)
{
	if( (newMsg.getMID() == oldMsg.getMID())
		&& (newMsg.size() == oldMsg.size()) )
	{
		Message::const_iterator itNew = newMsg.beginParameters();
		Message::const_iterator itOld = oldMsg.beginParameters();
		Message::const_iterator itNewEnd = newMsg.endParameters();
		for( ; itNew != itNewEnd ; ++itNew, ++itOld )
		{
			if( not ExpressionComparer::isEQ(*itNew, *itOld) )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}



bool BaseDataComparator::compare(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	if( mMachineCount != newEC.getExecutionData().getTableOfRuntime().size() )
	{
		mMachineCount = newEC.getExecutionData().getTableOfRuntime().size();

		computeAllMachineData( newEC.getExecutionData() );
	}

	++mComparisonCount;

	if( compareTEQ(newEC, oldEC) )
	{
		return( true );
	}
	else if( mUseCommunication || mUseVariable )
	{
		return( (mUseCommunication ? compareIO(newEC, oldEC) : true)
				&& (mUseVariable ? compareDATA(newEC, oldEC) : true) );
	}

	return( true );
}




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TRIVIALLY DATA COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool TriviallyDataComparison::compareDATA(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	const ExecutionData & newED = newEC.getExecutionData();
	const ExecutionData & oldED = oldEC.getExecutionData();

	// compare PC
	if( mIgnorePathCondition || ExpressionComparer::isTEQ(
			newED.getPathCondition(), oldED.getPathCondition() ) )
	{
		// compare DATAs
		for( const auto & itPairMachineData : getAllVariable() )
		{
			if( itPairMachineData.second().nonempty() )
			{
				newRF = newED.ptrRuntime( itPairMachineData.first() );
				oldRF = oldED.ptrRuntime( itPairMachineData.first() );

				if( newRF->getDataTable() != oldRF->getDataTable() )
				{
					for( const auto & itVariable : itPairMachineData.second() )
					{
						if( not ExpressionComparer::isTEQ(
								newRF->getData(itVariable->getOffset()),
								oldRF->getData(itVariable->getOffset())) )
						{
							return( false );
						}
					}
				}
			}
		}

		return( true );
	}

	return( false );
}


}
