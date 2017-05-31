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

#include "AvmIterationPrimitive.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of a FOR program
 ***************************************************************************
 */
bool AvmPrimitive_For::run(ExecutionEnvironment & ENV)
{
	return( run(ENV, ENV.inCODE->first()) );
}


bool AvmPrimitive_For::resume(ExecutionEnvironment & ENV)
{
	return( run(ENV, ENV.inCODE->third()) );
}


bool AvmPrimitive_For::run(ExecutionEnvironment & ENV, const BF & initStmnt)
{
	const BF &     forCond = ENV.inCODE->second();
	const BFCode & forIncr = ENV.inCODE->third().bfCode();
	const BFCode & forStmnt = ENV.inCODE->fourth().bfCode();

	ExecutionEnvironment stmntENV(ENV, BFCode::REF_NULL);

	ExecutionEnvironment iterENV(ENV, initStmnt);

	// INITIALISATION
	if( not iterENV.run() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Failed to RUN FOR< INIT > !!!"
				<< SEND_EXIT;

		return( false );
	}

	APExecutionData tmpED;

	while( iterENV.outEDS.nonempty() )
	{
		iterENV.outEDS.pop_first_to( tmpED );

		// Evaluation of FOR CONDITION
		EvaluationEnvironment condENV(ENV, tmpED);
		if( not condENV.evalBoolean(forCond) )
		{
			AVM_OS_EXIT( FAILED )
					<< "Failed to EVAL FOR< CONDITION > !!!"
					<< SEND_EXIT;

			return( false );
		}

		ENV.spliceFailure(condENV);


		if( condENV.outVAL.isEqualTrue() )
		{
			// Evaluation of FOR STATEMENT
			if( not stmntENV.run(condENV.outED, forStmnt) )
			{
				AVM_OS_EXIT( FAILED )
						<< "Failed to RUN FOR< STATEMENT > !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
		else if( condENV.outVAL.isEqualFalse() )
		{
			ENV.outEDS.append( tmpED );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Throw unexpected "
						"NON CONCRETE BOOLEAN VALUE FOR CONDITION : "
					<< tmpED->mRID.strUniqId()
					<< " ," << str_indent( condENV.outVAL )
					<< " |=>" << forCond.str() << " !!!"
					<< SEND_EXIT;
		}

		// OUTPUT EDS traitement
		while( stmntENV.outEDS.nonempty() )
		{
			stmntENV.outEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					// Evaluation of FOR INCREMENT statement
					if( not iterENV.run(tmpED, forIncr) )
					{
						AVM_OS_EXIT( FAILED )
								<< "Failed to RUN FOR< INCREMENT > !!!"
								<< SEND_EXIT;

						return( false );
					}

					break;
				}

				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					// Evaluation of FOR INCREMENT statement
					if( not iterENV.run(tmpED, forIncr) )
					{
						AVM_OS_EXIT( FAILED )
								<< "Failed to RUN FOR< INCREMENT > !!!"
								<< SEND_EXIT;

						return( false );
					}

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// IRQ EDS traitement
		while( stmntENV.irqEDS.nonempty() )
		{
			stmntENV.irqEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_BREAK:
				{
					tmpED.mwsetAEES( AEES_OK );

					ENV.outEDS.append( tmpED );

					break;
				}
				case AEES_STMNT_RETURN:
				{
					ENV.irqEDS.append( tmpED );

					break;
				}

				case AEES_STMNT_CONTINUE:
				{
					tmpED.mwsetAEES( AEES_OK );

					// Evaluation of FOR INCREMENT statement
					if( not iterENV.run(tmpED, forIncr) )
					{
						AVM_OS_EXIT( FAILED )
								<< "Failed to RUN FOR< INCREMENT > !!!"
								<< SEND_EXIT;

						return( false );
					}

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(stmntENV);
	}

	ENV.spliceNotOutput(stmntENV);

	return( true );
}


/**
 ***************************************************************************
 * execution of a FOR program
 ***************************************************************************
 */
bool AvmPrimitive_Foreach::run(ExecutionEnvironment & ENV)
{
	InstanceOfData * forIterator = ENV.mARG->at(0).to_ptr< InstanceOfData >();
	const BF     & forCollection = ENV.mARG->at(1);
	const BFCode & forStatement  = ENV.mARG->at(2).bfCode();

	ExecutionEnvironment stmntENV(ENV, BFCode::REF_NULL);

	ExecutionEnvironment iterENV(ENV, BFCode::REF_NULL);
	iterENV.appendOutput( ENV.mARG->outED );

	APExecutionData tmpED;

	avm_size_t endOffset = forCollection.size();
	for( avm_size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		while( iterENV.outEDS.nonempty() )
		{
			iterENV.outEDS.pop_first_to( tmpED );

			if( ENV.setRvalue(tmpED, forIterator, forCollection.at(offset)) )
			{
				stmntENV.appendOutput( tmpED );
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "Failed to INCREMENT FOREACH< ITERATOR > !!!"
						<< SEND_EXIT;

				return( false );
			}
		}

		if( not stmntENV.runFromOutputs(forStatement) )
		{
			AVM_OS_EXIT( FAILED )
					<< "Failed to RUN FOREACH< STATEMENT > !!!"
					<< SEND_EXIT;

			return( false );
		}

		ENV.spliceFailure( stmntENV );


		// OUTPUT EDS traitement
		while( stmntENV.outEDS.nonempty() )
		{
			stmntENV.outEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					iterENV.outEDS.append( tmpED );

					break;
				}

				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					iterENV.outEDS.append( tmpED );

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// IRQ EDS traitement
		while( stmntENV.irqEDS.nonempty() )
		{
			stmntENV.irqEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_BREAK:
				{
					tmpED.mwsetAEES( AEES_OK );

					ENV.outEDS.append( tmpED );

					break;
				}
				case AEES_STMNT_RETURN:
				{
					ENV.irqEDS.append( tmpED );

					break;
				}

				case AEES_STMNT_CONTINUE:
				{
					tmpED.mwsetAEES( AEES_OK );

					iterENV.outEDS.append( tmpED );

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(stmntENV);
	}

	ENV.spliceOutput(iterENV);

	return( true );
}



/**
 ***************************************************************************
 * execution of a WHILE program
 ***************************************************************************
 */

bool AvmPrimitive_WhileDo::run(ExecutionEnvironment & ENV)
{
	const BF &   whileCond = ENV.inCODE->first();
	const BFCode & doStmnt = ENV.inCODE->second().bfCode();

	ListOfAPExecutionData tmpListOfInputED( ENV.inED );

	ExecutionEnvironment stmntENV(ENV, BFCode::REF_NULL);

	APExecutionData tmpED;

	while( tmpListOfInputED.nonempty() )
	{
		tmpListOfInputED.pop_first_to( tmpED );

		// Evaluation of WHILE_DO CONDITION
		EvaluationEnvironment condENV(ENV, tmpED);
		if( not condENV.evalBoolean(whileCond) )
		{
			AVM_OS_EXIT( FAILED )
					<< "Failed to EVAL WHILE_DO< CONDITION > !!!"
					<< SEND_EXIT;

			return( false );
		}

		ENV.spliceFailure(condENV);


		if( condENV.outVAL.isEqualTrue() )
		{
			// Evaluation of WHILE_DO STATEMENT
			if( not stmntENV.run(condENV.outED, doStmnt) )
			{
				AVM_OS_EXIT( FAILED )
						<< "Failed to RUN WHILE_DO< STATEMENT > !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
		else if( condENV.outVAL.isEqualFalse() )
		{
			ENV.outEDS.append( tmpED );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Throw unexpected "
						"NON CONCRETE BOOLEAN VALUE FOR CONDITION : "
					<< tmpED->mRID.strUniqId()
					<< " ," << str_indent( condENV.outVAL )
					<< " |=>" << whileCond.str() << " !!!"
					<< SEND_EXIT;
		}

		// OUTPUT EDS traitement
		while( stmntENV.outEDS.nonempty() )
		{
			stmntENV.outEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					tmpListOfInputED.append( tmpED );

					break;
				}

				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					tmpListOfInputED.append( tmpED );

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// IRQ EDS traitement
		while( stmntENV.irqEDS.nonempty() )
		{
			stmntENV.irqEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_BREAK:
				{
					tmpED.mwsetAEES( AEES_OK );

					ENV.outEDS.append( tmpED );

					break;
				}
				case AEES_STMNT_RETURN:
				{
					ENV.irqEDS.append( tmpED );

					break;
				}

				case AEES_STMNT_CONTINUE:
				{
					tmpED.mwsetAEES( AEES_OK );

					// Evaluation of FOR INCREMENT statement
					tmpListOfInputED.append( tmpED );

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}


		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(stmntENV);
	}

	ENV.spliceNotOutput(stmntENV);

	return( true );
}


bool AvmPrimitive_WhileDo::resume(ExecutionEnvironment & ENV)
{
	return( run( ENV ) );
}



/**
 ***************************************************************************
 * execution of a WHILE program
 ***************************************************************************
 */
bool AvmPrimitive_DoWhile::run(ExecutionEnvironment & ENV)
{
	const BFCode & doStmnt = ENV.inCODE->first().bfCode();
	const BF &    whileCond = ENV.inCODE->second();

	ListOfAPExecutionData tmpListOfInputED( ENV.inED );

	ExecutionEnvironment stmntENV(ENV, BFCode::REF_NULL);

	APExecutionData tmpED;

	while( tmpListOfInputED.nonempty() )
	{
		// Evaluation of DO_WHILE STATEMENT
		if( not stmntENV.run(tmpListOfInputED, doStmnt) )
		{
			AVM_OS_EXIT( FAILED )
					<< "Failed to RUN DO_WHILE< STATEMENT > !!!"
					<< SEND_EXIT;

			return( false );
		}

		tmpListOfInputED.clear();

		// OUTPUT EDS traitement
		while( stmntENV.outEDS.nonempty() )
		{
			stmntENV.outEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					//!!! NO << break >> for these statement
				}
				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					// Evaluation of DO_WHILE CONDITION
					EvaluationEnvironment condENV(ENV, tmpED);
					if( not condENV.evalBoolean(whileCond) )
					{
						AVM_OS_EXIT( FAILED )
								<< "Failed to EVAL WHILE_DO< CONDITION > !!!"
								<< SEND_EXIT;

						return( false );
					}

					ENV.spliceFailure(condENV);



					if( condENV.outVAL.isEqualTrue() )
					{
						tmpListOfInputED.append( condENV.outED );
					}
					else if( condENV.outVAL.isEqualFalse() )
					{
						ENV.outEDS.append( tmpED );
					}
					else
					{
						tmpListOfInputED.clear();

						AVM_OS_FATAL_ERROR_EXIT
								<< "Throw unexpected "
								"NON CONCRETE BOOLEAN VALUE FOR CONDITION : "
								<< tmpED->mRID.strUniqId()
								<< " ," << str_indent( condENV.outVAL )
								<< " |=>" << whileCond.str() << " !!!"
								<< SEND_EXIT;
					}

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// IRQ EDS traitement
		while( stmntENV.irqEDS.nonempty() )
		{
			stmntENV.irqEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_BREAK:
				{
					tmpED.mwsetAEES( AEES_OK );

					ENV.outEDS.append( tmpED );

					break;
				}
				case AEES_STMNT_RETURN:
				{
					ENV.irqEDS.append( tmpED );

					break;
				}

				case AEES_STMNT_CONTINUE:
				{
					tmpED.mwsetAEES( AEES_OK );

					// Evaluation of DO_WHILE CONDITION
					EvaluationEnvironment condENV(ENV, tmpED);
					if( not condENV.evalBoolean(whileCond) )
					{
						AVM_OS_EXIT( FAILED )
								<< "Failed to EVAL WHILE_DO< CONDITION > !!!"
								<< SEND_EXIT;

						return( false );
					}

					ENV.spliceFailure(condENV);


					if( condENV.outVAL.isEqualTrue() )
					{
						tmpListOfInputED.append( condENV.outED );
					}
					else if( condENV.outVAL.isEqualFalse() )
					{
						ENV.outEDS.append( tmpED );
					}
					else
					{
						tmpListOfInputED.clear();

						AVM_OS_FATAL_ERROR_EXIT
								<< "Throw unexpected "
								"NON CONCRETE BOOLEAN VALUE FOR CONDITION : "
								<< tmpED->mRID.strUniqId()
								<< " ," << str_indent( condENV.outVAL )
								<< " |=>" << whileCond.str() << " !!!"
								<< SEND_EXIT;
					}

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as irqEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(stmntENV);
	}

	ENV.spliceNotOutput(stmntENV);

	return( true );
}


bool AvmPrimitive_DoWhile::resume(ExecutionEnvironment & ENV)
{
	const BFCode &  doStmnt = ENV.inCODE->first().bfCode();
	const BF &    whileCond = ENV.inCODE->second();

	ListOfAPExecutionData tmpListOfInputED( ENV.inED );

	ExecutionEnvironment stmntENV(ENV, BFCode::REF_NULL);

	APExecutionData tmpED;

	while( tmpListOfInputED.nonempty() )
	{
		tmpListOfInputED.pop_first_to( tmpED );

		// Evaluation of WHILE_DO CONDITION
		EvaluationEnvironment condENV(ENV, tmpED);
		if( not condENV.evalBoolean(whileCond) )
		{
			AVM_OS_EXIT( FAILED )
					<< "Failed to EVAL WHILE_DO< CONDITION > !!!"
					<< SEND_EXIT;

			return( false );
		}

		ENV.spliceFailure(condENV);


		if( condENV.outVAL.isEqualTrue() )
		{
			// Evaluation of WHILE_DO STATEMENT
			if( not stmntENV.run(condENV.outED, doStmnt) )
			{
				AVM_OS_EXIT( FAILED )
						<< "Failed to RUN WHILE_DO< STATEMENT > !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
		else if( condENV.outVAL.isEqualFalse() )
		{
			ENV.outEDS.append( tmpED );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Throw unexpected "
						"NON CONCRETE BOOLEAN VALUE FOR CONDITION : "
					<< tmpED->mRID.strUniqId()
					<< " ," << str_indent( condENV.outVAL )
					<< " |=>" << whileCond.str() << " !!!"
					<< SEND_EXIT;
		}

		// OUTPUT EDS traitement
		while( stmntENV.outEDS.nonempty() )
		{
			stmntENV.outEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					tmpListOfInputED.append( tmpED );

					break;
				}

				case AEES_OK:
				case AEES_STEP_RESUME:
				{
					tmpListOfInputED.append( tmpED );

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// IRQ EDS traitement
		while( stmntENV.irqEDS.nonempty() )
		{
			stmntENV.irqEDS.pop_last_to( tmpED );

			switch( tmpED->getAEES() )
			{
				case AEES_STMNT_BREAK:
				{
					tmpED.mwsetAEES( AEES_OK );

					ENV.outEDS.append( tmpED );

					break;
				}
				case AEES_STMNT_RETURN:
				{
					ENV.irqEDS.append( tmpED );

					break;
				}

				case AEES_STMNT_CONTINUE:
				{
					tmpED.mwsetAEES( AEES_OK );

					// Evaluation of FOR INCREMENT statement
					tmpListOfInputED.append( tmpED );

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS as irqEDS  :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		// Sync EDS traitement
		ENV.spliceSync_mwStorePos(stmntENV);
	}

	ENV.spliceNotOutput(stmntENV);

	return( true );
}



}
