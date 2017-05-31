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
	newED = newEC.getExecutionData();
	oldED = oldEC.getExecutionData();

	// compare PC
	if( mIgnorePathCondition || ExpressionComparer::isEQ(
			newED->getPathCondition(), oldED->getPathCondition() ) )
	{
		// compare DATAs
		itPairMachineData = getAllVariable().begin();
		endPairMachineData = getAllVariable().end();
		for( ; itPairMachineData != endPairMachineData ; ++itPairMachineData )
		{
			if( (*itPairMachineData).second().nonempty() )
			{
				newRF = newED->ptrRuntime( (*itPairMachineData).first() );
				oldRF = oldED->ptrRuntime( (*itPairMachineData).first() );


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )
	AVM_OS_COUT << "machine :> " << oldRF->getRID().str() << std::endl;
	itVar = (*itPairMachineData).second().begin();
	endVar = (*itPairMachineData).second().end();
	for( ; itVar != endVar ; ++itVar )
	{
		AVM_OS_COUT << "  " << str_header( *itVar ) << std::endl;	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )


				if( newRF->getDataTable() != oldRF->getDataTable() )
				{

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_COUT << "oldRF :> " << oldRF->getRID().str() << std::endl;
	oldRF->getDataTable()->toStream(AVM_OS_COUT, oldRF->getVariables());

	AVM_OS_COUT << "newRF :> " << newRF->getRID().str() << std::endl;
	newRF->getDataTable()->toStream(AVM_OS_COUT, newRF->getVariables());
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )

					itVar = (*itPairMachineData).second().begin();
					endVar = (*itPairMachineData).second().end();
					for( ; itVar != endVar ; ++itVar )
					{

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )
	AVM_OS_COUT << str_header( *itVar ) << std::endl;
	AVM_OS_COUT << "  oldVal :> " << oldRF->getData((*itVar)->getOffset()).str()
			<< std::endl;
	AVM_OS_COUT << "  newVal :> " << newRF->getData((*itVar)->getOffset()).str()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REDUNDANCE )

						if( not ExpressionComparer::isEQ(
								newRF->getData((*itVar)->getOffset()),
								oldRF->getData((*itVar)->getOffset())) )
						{

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_COUT << str_header( *itVar ) << std::endl;
	AVM_OS_COUT << "  oldVal :> " << oldRF->getData((*itVar)->getOffset()).str()
			<< std::endl;
	AVM_OS_COUT << "  newVal :> " << newRF->getData((*itVar)->getOffset()).str()
			<< std::endl;
	AVM_OS_COUT << ">>>>>>> false <<<<<<<" << std::endl;
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
	newED = newEC.getExecutionData();
	oldED = oldEC.getExecutionData();

	// compare PC
	if( mIgnorePathCondition || ExpressionComparer::isEQ(
			newED->getPathCondition(), oldED->getPathCondition() ) )
	{
		// compare DATAs
		itPairMachineData = getAllVariable().begin();
		endPairMachineData = getAllVariable().end();
		for( ; itPairMachineData != endPairMachineData ; ++itPairMachineData )
		{
			if( (*itPairMachineData).second().nonempty() )
			{
				newRF = newED->ptrRuntime( (*itPairMachineData).first() );
				oldRF = oldED->ptrRuntime( (*itPairMachineData).first() );

				if( newRF->getDataTable() != oldRF->getDataTable() )
				{
					itVar = (*itPairMachineData).second().begin();
					endVar = (*itPairMachineData).second().end();
					for( ; itVar != endVar ; ++itVar )
					{
						if( not ExpressionComparer::isEQ(
								newRF->getData((*itVar)->getOffset()),
								oldRF->getData((*itVar)->getOffset())) )
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
