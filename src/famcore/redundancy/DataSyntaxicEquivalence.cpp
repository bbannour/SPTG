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
#include "DataSyntaxicEquivalence.h"

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>

#include <fml/expression/ExpressionComparer.h>

#include <fml/runtime/RuntimeForm.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DATA SYNTAXIC EQUIVALENCE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool DataSyntaxicEquivalence::compareMESSAGE(
		const Message & newMsg, const Message & oldMsg)
{
	if( newMsg.getMID() == oldMsg.getMID() )
	{
		if( newMsg.hasParameter() )
		{
			Message::const_iterator itNew = newMsg.beginParameters();
			Message::const_iterator itNewEnd = newMsg.endParameters();
			Message::const_iterator itOld = oldMsg.beginParameters();
			for( ; itNew != itNewEnd ; ++itNew, ++itOld )
			{
				if( not ExpressionComparer::isEQ(*itNew, *itOld) )
				{
					return( false );
				}
			}
		}
		return( true );
	}

	return( false );
}


/*
 * COMPARE
 */
bool DataSyntaxicEquivalence::compareDATA(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	const ExecutionData & newED = newEC.getExecutionData();
	const ExecutionData & oldED = oldEC.getExecutionData();

	// compare PC
	if( mIgnorePathCondition || ExpressionComparer::isEQ(
			newED.getPathCondition(), oldED.getPathCondition() ) )
	{
		// compare DATAs
		for( const auto & itPairMachineData : getAllVariable() )
		{
			if( itPairMachineData.second().nonempty() )
			{
				newRF = newED.ptrRuntime( itPairMachineData.first() );
				oldRF = oldED.ptrRuntime( itPairMachineData.first() );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )
	AVM_OS_TRACE << "machine :> " << oldRF->getRID().str() << std::endl;
	for( const auto & itVariable : itPairMachineData.second() )
	{
		AVM_OS_TRACE << "  " << str_header( itVariable ) << std::endl;	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )

				if( newRF->getDataTable() != oldRF->getDataTable() )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_TRACE << "oldRF :ctx-" << oldEC.getIdNumber() << "> "
			<< oldRF->getRID().str() << std::endl;
	oldRF->getDataTable()->toStream(AVM_OS_TRACE, oldRF->getVariables());

	AVM_OS_TRACE << "newRF :ctx-" << newEC.getIdNumber() << "> "
			<< newRF->getRID().str() << std::endl;
	newRF->getDataTable()->toStream(AVM_OS_TRACE, newRF->getVariables());
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )

					for( const auto & itVariable : itPairMachineData.second() )
					{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )
	AVM_OS_TRACE << str_header( itVariable ) << std::endl;
	AVM_OS_TRACE << "  oldVal :ctx-" << oldEC.getIdNumber() << "> "
			<< oldRF->getData(itVariable->getOffset()).str() << std::endl;
	AVM_OS_TRACE << "  newVal :ctx-" << newEC.getIdNumber() << "> "
			<< newRF->getData(itVariable->getOffset()).str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )

						if( itVariable->getModifier().anyModifierOfStateData()
							&& (not ExpressionComparer::isEQ(
								newRF->getData(itVariable->getOffset()),
								oldRF->getData(itVariable->getOffset()))) )
						{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_TRACE << str_header( itVariable ) << std::endl;
	AVM_OS_TRACE << "  oldVal :ctx-" << oldEC.getIdNumber() << "> "
			<< oldRF->getData(itVariable->getOffset()).str() << std::endl;
	AVM_OS_TRACE << "  newVal :ctx-" << newEC.getIdNumber() << "> "
			<< newRF->getData(itVariable->getOffset()).str() << std::endl;
	AVM_OS_TRACE << ">>>>>>> false <<<<<<<" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )

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


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DATA ALPHA EQUIVALENCE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool DataAlphaEquivalence::compareDATA(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	const ExecutionData & newED = newEC.getExecutionData();
	const ExecutionData & oldED = oldEC.getExecutionData();

	// compare PC
	if( mIgnorePathCondition || ExpressionComparer::isEQ(
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
						if( itVariable->getModifier().anyModifierOfStateData()
							&& (not ExpressionComparer::isEQ(
								newRF->getData(itVariable->getOffset()),
								oldRF->getData(itVariable->getOffset()))) )
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
