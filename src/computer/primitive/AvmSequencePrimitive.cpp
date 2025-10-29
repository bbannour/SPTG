/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmSequencePrimitive.h"

#include <computer/ExecutionEnvironment.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an ATOMIC SEQUENCE program
 ***************************************************************************
 */

bool AvmPrimitive_AtomicSequence::run(ExecutionEnvironment & ENV)
{
	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
	AvmCode::const_iterator endOperand = ENV.inCODE->end();

	ExecutionData tmpED;

	// Evaluation of FIRST SEQUENCIAL STATEMENT
	ExecutionEnvironment tmpENV(ENV, (*itOperand).bfCode());
	if( not tmpENV.run() )
	{
		return( false );
	}

	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
AVM_IF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )
		static std::uint32_t ecCount = 8;
		if( tmpENV.outEDS.size() > ecCount )
		{
			ecCount = (std::uint32_t)( ecCount * 1.5 );
			AVM_OS_TRACE << REPEAT("==========", 5) << std::endl
					<< ">>>> Execution from " << tmpENV.outEDS.size()
					<< " ECs" << std::endl;
		}
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )

		// for output ED
		if( tmpENV.outEDS.nonempty() )
		{
			if( not tmpENV.runFromOutputs((*itOperand).bfCode()) )
			{
				return( false );
			}
		}
		else
		{
			break;
		}
	}

	ENV.spliceOutput( tmpENV );

	return( true );
}




/**
 ***************************************************************************
 * execution of a SEQUENCE program
 ***************************************************************************
 */

bool AvmPrimitive_Sequence::run(ExecutionEnvironment & ENV,
		AvmCode::const_iterator itOperand, AvmCode::const_iterator endOperand)
{
	ExecutionData tmpED;
	RuntimeID tmpRID = ENV.inED.getRID();

	ListOfExecutionData listOfCurrentED;

	// Evaluation of FIRST SEQUENCIAL STATEMENT
	ExecutionEnvironment tmpENV(ENV, (*itOperand).bfCode());
	if( tmpENV.run() )
	{
		listOfCurrentED.splice( tmpENV.outEDS );

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
	}
	else
	{
		return( false );
	}

	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
AVM_IF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )
		static std::uint32_t ecCount = 8;
		if( listOfCurrentED.size() > ecCount )
		{
			ecCount = (std::uint32_t)( ecCount * 1.5 );
			AVM_OS_TRACE << REPEAT("==========", 5) << std::endl
					<< ">>>> Execution from " << listOfCurrentED.size()
					<< " ECs" << std::endl;
		}
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )

		while( listOfCurrentED.nonempty() )
		{
			listOfCurrentED.pop_last_to( tmpED );

			switch( tmpED.getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					[[fallthrough]]; //!! No BREAK for that CASE statement
				}

				// Evaluation of NEXT SEQUENCIAL STATEMENT
				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					if( tmpED.isPreserveRID() )
					{
						tmpED.setPreserveRID( false );
						tmpRID = tmpED.getRID();
					}
					else
					{
						tmpED.setRID( tmpRID );
					}

					if( tmpENV.run(tmpED, (*itOperand).bfCode()) )
					{
						// Sync EDS traitement
						ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
					}
					else
					{
						return( false );
					}

					break;
				}

				default:
				{
					ENV.destroyOutED();

					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS:> "
							<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		listOfCurrentED.splice(  tmpENV.outEDS  );
	}

	ENV.outEDS.splice( listOfCurrentED );

	ENV.spliceNotOutput(tmpENV);

	return( true );
}


bool AvmPrimitive_Sequence::run(ExecutionEnvironment & ENV)
{
	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
	AvmCode::const_iterator endOperand = ENV.inCODE->end();

	ExecutionData tmpED;
	RuntimeID tmpRID = ENV.inED.getRID();

	ListOfExecutionData listOfCurrentED;

	// Evaluation of FIRST SEQUENCIAL STATEMENT
	ExecutionEnvironment tmpENV(ENV, (*itOperand).bfCode());
	if( tmpENV.run() )
	{
		listOfCurrentED.splice( tmpENV.outEDS );

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
	}
	else
	{
		return( false );
	}

	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
AVM_IF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )
		static std::uint32_t ecCount = 8;
		if( listOfCurrentED.size() > ecCount )
		{
			ecCount = (std::uint32_t)( ecCount * 1.5 );
			AVM_OS_TRACE << REPEAT("==========", 5) << std::endl
					<< ">>>> Execution from " << listOfCurrentED.size()
					<< " ECs" << std::endl;
		}
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )

		while( listOfCurrentED.nonempty() )
		{
			listOfCurrentED.pop_last_to( tmpED );

			switch( tmpED.getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					[[fallthrough]]; //!! No BREAK for that CASE statement
				}

				// Evaluation of NEXT SEQUENCIAL STATEMENT
				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					if( tmpED.isPreserveRID() )
					{
						tmpED.setPreserveRID( false );
						tmpRID = tmpED.getRID();
					}
					else
					{
						tmpED.setRID( tmpRID );
					}

					if( tmpENV.run(tmpED, (*itOperand).bfCode()) )
					{
						// Sync EDS traitement
						ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
					}
					else
					{
						return( false );
					}

					break;
				}

				default:
				{
					ENV.destroyOutED();

					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS:> "
							<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		listOfCurrentED.splice(  tmpENV.outEDS  );
	}


	ENV.outEDS.splice( listOfCurrentED );

	ENV.spliceNotOutput(tmpENV);

	return( true );
}


bool AvmPrimitive_Sequence::resume(ExecutionEnvironment & ENV)
{
	if( ENV.inEXEC_LOCATION->itCode != ENV.inEXEC_LOCATION->endCode )
	{
		return( run(ENV, ENV.inEXEC_LOCATION->itCode,
				ENV.inEXEC_LOCATION->endCode) );
	}
	else
	{
		ENV.outEDS.append( ENV.inED );
		return( true );
	}
}



/**
 ***************************************************************************
 * execution of a SIDE_SEQUENCE program
 ***************************************************************************
 */
bool AvmPrimitive_SideSequence::run(ExecutionEnvironment & ENV,
		AvmCode::const_iterator itOperand, AvmCode::const_iterator endOperand)
{
	ExecutionData tmpED;
	RuntimeID tmpRID = ENV.inED.getRID();

	ListOfExecutionData listOfCurrentED;
	ListOfExecutionData listOfNextED;

	// Evaluation of FIRST SEQUENCIAL STATEMENT
	ExecutionEnvironment tmpENV(ENV, (*itOperand).bfCode());
	if( tmpENV.run() )
	{
		listOfCurrentED.splice( tmpENV.outEDS );

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
	}
	else
	{
		return( false );
	}

	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
AVM_IF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )
		static std::uint32_t ecCount = 8;
		if( listOfCurrentED.size() > ecCount )
		{
			ecCount = (std::uint32_t)( ecCount * 1.5 );
			AVM_OS_TRACE << REPEAT("==========", 5) << std::endl
					<< ">>>> Execution from " << listOfCurrentED.size()
					<< " ECs" << std::endl;
		}
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )

		while( listOfCurrentED.nonempty() )
		{
			listOfCurrentED.pop_last_to( tmpED );

			switch( tmpED.getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					[[fallthrough]]; //!! No BREAK for that CASE statement
				}

				// Evaluation of NEXT SEQUENCIAL STATEMENT
				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					if( tmpED.isPreserveRID() )
					{
						tmpED.setPreserveRID( false );
						tmpRID = tmpED.getRID();
					}
					else
					{
						tmpED.setRID( tmpRID );
					}

					if( tmpENV.run(tmpED, (*itOperand).bfCode()) )
					{
						// Sync EDS traitement
						ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
					}
					else
					{
						return( false );
					}

					if( tmpENV.outEDS.nonempty() )
					{
						listOfNextED.splice(tmpENV.outEDS);
					}
					else if( tmpENV.exitEDS.empty() && tmpENV.syncEDS.empty() )
					{
						ENV.outEDS.append( tmpED );
					}

					ENV.spliceNotOutput(tmpENV);

					break;
				}

				default:
				{
					ENV.destroyOutED();

					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS:> "
							<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		listOfCurrentED.splice( listOfNextED );
	}

	ENV.outEDS.splice( listOfCurrentED );

	return( true );
}


bool AvmPrimitive_SideSequence::run(ExecutionEnvironment & ENV)
{
	return( run(ENV, ENV.inCODE->begin(), ENV.inCODE->end()) );
}


bool AvmPrimitive_SideSequence::resume(ExecutionEnvironment & ENV)
{
	if( ENV.inEXEC_LOCATION->itCode != ENV.inEXEC_LOCATION->endCode )
	{
		return( run(ENV, ENV.inEXEC_LOCATION->itCode,
				ENV.inEXEC_LOCATION->endCode) );
	}
	else
	{
		ENV.outEDS.append( ENV.inED );
		return( true );
	}
}



/**
 ***************************************************************************
 * execution of a WEAK_SEQUENCE program
 ***************************************************************************
 */
bool AvmPrimitive_WeakSequence::run(ExecutionEnvironment & ENV,
		AvmCode::const_iterator itOperand, AvmCode::const_iterator endOperand)
{
	ExecutionData tmpED;
	RuntimeID tmpRID = ENV.inED.getRID();

	ListOfExecutionData listOfCurrentED;
	ListOfExecutionData listOfNextED;

	// Evaluation of FIRST SEQUENCIAL STATEMENT
	ExecutionEnvironment tmpENV(ENV, (*itOperand).bfCode());
	if( tmpENV.run() )
	{
		if( tmpENV.outEDS.nonempty() )
		{
			listOfCurrentED.splice( tmpENV.outEDS );
		}
		else if( tmpENV.exitEDS.empty() && tmpENV.syncEDS.empty() )
		{
			listOfCurrentED.append( ENV.inED );
		}
		else
		{
			ENV.spliceOutput(tmpENV);

			return( true );
		}

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);

		ENV.spliceNotOutput(tmpENV);
	}
	else
	{
		listOfCurrentED.append( ENV.inED );
	}

	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
AVM_IF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )
		static std::uint32_t ecCount = 8;
		if( listOfCurrentED.size() > ecCount )
		{
			ecCount = (std::uint32_t)( ecCount * 1.5 );
			AVM_OS_TRACE << REPEAT("==========", 5) << std::endl
					<< ">>>> Execution from " << listOfCurrentED.size()
					<< " ECs" << std::endl;
		}
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG2( HIGH , COMPUTING , STATEMENT )

		while( listOfCurrentED.nonempty() )
		{
			listOfCurrentED.pop_last_to( tmpED );

			switch( tmpED.getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					[[fallthrough]]; //!! No BREAK for that CASE statement
				}

				// Evaluation of NEXT SEQUENCIAL STATEMENT
				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					tmpED.setRID( tmpRID );

					if( tmpENV.run(tmpED, (*itOperand).bfCode()) )
					{
						if( tmpENV.outEDS.nonempty() )
						{
							listOfNextED.splice(tmpENV.outEDS);
						}
						else if( tmpENV.exitEDS.empty() && tmpENV.syncEDS.empty() )
						{
							listOfNextED.append(tmpED);
						}

						// Sync EDS traitement
						ENV.spliceSync_mwStorePos(tmpENV, (itOperand + 1), endOperand);
					}
					else
					{
						listOfNextED.append( tmpED );
					}


					ENV.spliceNotOutput(tmpENV);

					break;
				}

				default:
				{
					ENV.destroyOutED();

					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS:> "
							<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		listOfCurrentED.splice( listOfNextED );
	}


	if( listOfCurrentED.singleton() )
	{
		tmpED = listOfCurrentED.back();

		if( ENV.inED == tmpED )
		{
			return( false );
		}
	}

	ENV.outEDS.splice( listOfCurrentED );

	return( true );
}


bool AvmPrimitive_WeakSequence::run(ExecutionEnvironment & ENV)
{
	return( run(ENV, ENV.inCODE->begin(), ENV.inCODE->end()) );
}


bool AvmPrimitive_WeakSequence::resume(ExecutionEnvironment & ENV)
{
	if( ENV.inEXEC_LOCATION->itCode != ENV.inEXEC_LOCATION->endCode )
	{
		return( run(ENV, ENV.inEXEC_LOCATION->itCode,
				ENV.inEXEC_LOCATION->endCode) );
	}
	else
	{
		ENV.outEDS.append( ENV.inED );
		return( true );
	}
}



}
