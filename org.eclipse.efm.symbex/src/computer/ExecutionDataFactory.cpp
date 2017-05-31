/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 janv. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutionDataFactory.h"

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


/*
 * SETTER
 * Schedule
 * RunnableElementTrace
 * IOElementTrace
 */

void ExecutionDataFactory::appendRunnableElementTrace(
		APExecutionData & apED, const BF & aRunnableElementTrace)
{
	if( apED->hasRunnableElementTrace() )
	{
		apED.makeWritable();

		BF & theNewRunnableElementTrace = apED->getRunnableElementTrace();

//AVM_OS_DEBUG << "theNewRunnableElementTrace beg: "
//		<< apED->getRunnableElementTrace().str(" ") << std::endl;

		if( theNewRunnableElementTrace.is< AvmCode >() &&
			theNewRunnableElementTrace.to_ptr<
					AvmCode >()->isOpCode( AVM_OPCODE_SEQUENCE ) )
		{
			theNewRunnableElementTrace.makeWritable();
			theNewRunnableElementTrace.to_ptr<
					AvmCode >()->append(aRunnableElementTrace);
		}
		else
		{
			apED->setRunnableElementTrace( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					theNewRunnableElementTrace, aRunnableElementTrace) );
		}

//AVM_OS_DEBUG << "theNewRunnableElementTrace end: "
//		<< apED->getRunnableElementTrace().str(" ") << std::endl << std::endl;
	}
	else
	{
		apED.mwsetRunnableElementTrace( aRunnableElementTrace );

//AVM_OS_DEBUG << "aRunnableElementTrace: " << aRunnableElementTrace.str(" ")
//		<< std::endl << std::endl;
	}
}


void ExecutionDataFactory::appendIOElementTrace(
		APExecutionData & apED, const BF & theIOElementTrace)
{
	if( apED->hasIOElementTrace() )
	{
		apED.makeWritable();

		BF & theNewIOElementTrace = apED->getIOElementTrace();

		if( theNewIOElementTrace.is< AvmCode >() &&
			theNewIOElementTrace.to_ptr< AvmCode >()->isOpCode( AVM_OPCODE_SEQUENCE ) )
		{
			theNewIOElementTrace.makeWritable();
			theNewIOElementTrace.to_ptr< AvmCode >()->append(theIOElementTrace);
		}
		else
		{
			apED->setIOElementTrace( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					theNewIOElementTrace, theIOElementTrace) );
		}
	}
	else
	{
		apED.mwsetIOElementTrace( theIOElementTrace );
	}
}




/**
 * COMPARISON
 */
bool ExecutionDataFactory::equalsStatus(
		const ExecutionData & oneED, const ExecutionData & otherED)
{
	bool isEquals = false;

	if( oneED.getRuntimeFormStateTable() == otherED.getRuntimeFormStateTable() )
	{
		isEquals = oneED.getPathCondition().strEQ( otherED.getPathCondition() );

		if( isEquals && oneED.getRuntimeFormStateTable()->hasAssigned() )
		{
			isEquals = equalsData(oneED, otherED);
		}
	}
	else if( oneED.getRuntimeFormStateTable()->
			equalsState(otherED.getRuntimeFormStateTable()) )
	{
//		if( getRuntimeFormStateTable()->hasAssigned() &&
//				otherED.getRuntimeFormStateTable()->hasAssigned() )
//		{
//			isEquals = ExpressionComparer::isSEQ(getPathCondition(),
//					otherED.getPathCondition()) && equalsData(one, other);
//		}
//		else if( getRuntimeFormStateTable()->zeroAssigned() &&
//				otherED.getRuntimeFormStateTable()->zeroAssigned() )
//		{
//			isEquals = ExpressionComparer::isSEQ(
//					getPathCondition(), otherED.getPathCondition());
//		}

		if( (oneED.getSaveTableOfAssignedFlag() != NULL) &&
				otherED.getRuntimeFormStateTable()->hasAssigned() )
		{
			isEquals = oneED.getPathCondition().strEQ( otherED.getPathCondition() )
					&& equalsData(oneED, otherED);
		}
		else if( (oneED.getSaveTableOfAssignedFlag() == NULL) &&
				otherED.getRuntimeFormStateTable()->zeroAssigned() )
		{
			isEquals = oneED.getPathCondition().strEQ( otherED.getPathCondition() );
		}
	}

	return( isEquals );
}


bool ExecutionDataFactory::equalsData(
		const ExecutionData & oneED, const ExecutionData & otherED)
{
	TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag =
			oneED.getSaveTableOfAssignedFlag();
//	TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag =
//			theTableOfRuntimeFormFlags->getTableOfAssignedFlag();

	TableOfRuntimeFormState::TableOfAssignedFlag otherTableOfAssignedFlag =
			otherED.getRuntimeFormStateTable()->getTableOfAssignedFlag();

	if( (aTableOfAssignedFlag != NULL) && (otherTableOfAssignedFlag != NULL) )
	{
		avm_size_t varCount = 0;
		avm_size_t rfCount = oneED.getRuntimeFormStateTable()->size();

		for( avm_size_t rid = 0 ; rid != rfCount ; ++rid )
		{
			if( (aTableOfAssignedFlag[rid] != NULL) &&
					(otherTableOfAssignedFlag[rid] != NULL) )
			{
				const RuntimeForm & aRF = oneED.getRuntime(rid);
				varCount = aRF.getExecutable()->getBasicDataSize();
				for( avm_size_t offset = 0 ; offset < varCount ; ++offset )
				{
					if( (*(aTableOfAssignedFlag[rid]))[offset] !=
							(*(otherTableOfAssignedFlag[rid]))[offset] )
					{
						return( false );
					}
					else if( (*(aTableOfAssignedFlag[rid]))[offset] )
					{
						if( aRF.getData(offset).strNEQ(
								otherED.getRuntime(rid).getData(offset)) )
						{
							return( false );
						}
					}
				}
			}
			else if( aTableOfAssignedFlag[rid] != otherTableOfAssignedFlag[rid] )
			{
				return( false );
			}
		}

		return( true );
	}
	else
	{
		return( aTableOfAssignedFlag == otherTableOfAssignedFlag );
	}
}


} /* namespace sep */
