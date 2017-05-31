/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "EvaluationEnvironment.h"

#include <builder/Builder.h>

#include <fml/executable/InstanceOfPort.h>


namespace sep
{


/**
 * TOOLS
 */
BF EvaluationEnvironment::ioSubst(
		const APExecutionData & apED, AvmProgram * aProgram,
		AvmCode * progIO, AvmCode * traceIO, const BF & aCode)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( traceIO->sameOperator( progIO )
		&& (traceIO->size() >= progIO->size()) )
			<< " The traceIO and progIO are incompatible !!!"
			<< SEND_EXIT;

AVM_IF_DEBUG_LEVEL_GT_LOW
	AVM_OS_TRACE << INCR_INDENT_TAB << "ioSubst:: << " << aCode.str() << " >>"
			<< std::endl
			<< TAB << " In the context Of << " << traceIO->str() << " >>"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_GT_LOW


	bool destroyLocalRuntimeStack = false;

	if( (aProgram != NULL) && aProgram->hasData() )
	{
		if( not apED->hasLocalRuntimeStack() )
		{
			destroyLocalRuntimeStack = true;
			apED->createLocalRuntimeStack();
		}

		LocalRuntime aLocalRuntime( *aProgram );
		apED->getLocalRuntimes()->push( aLocalRuntime );

		AvmCode::iterator traceArg = traceIO->begin();
		AvmCode::iterator itArg = progIO->begin();
		AvmCode::iterator itEndArg = progIO->end();
		for( ++itArg, ++traceArg ; itArg != itEndArg ; ++itArg, ++traceArg )
		{
			aLocalRuntime.setData(itArg->as_ptr<
					BaseInstanceForm >()->getOffset(), (*traceArg));
		}

		eval(apED, apED->getSystemRID(), aCode);

		apED->getLocalRuntimes()->pop();
		if( destroyLocalRuntimeStack )
		{
			apED->destroyLocalRuntimeStack();
		}
	}
	else
	{
		eval(apED, apED->getSystemRID(), aCode);
	}

	BF substCode = outVAL;


AVM_IF_DEBUG_LEVEL_GT_LOW
	AVM_OS_TRACE << TAB_DECR_INDENT << "result:: << " << substCode.str() << " >>"
		<< std::endl << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GT_LOW

	return( substCode );
}


////////////////////////////////////////////////////////////////////////////////
///// the EVAL statement for FILTER
////////////////////////////////////////////////////////////////////////////////

bool EvaluationEnvironment::eval(const APExecutionData & anED,
		const RuntimeID & aRID, const BF & bf)
{
	RuntimeID prevRID = anED->mRID;
	anED->mRID = aRID;

	inEC = anED->getExecutionContext();

	outED = inED = anED;

	bool rt = false;

	if( bf.is< AvmCode >() )
	{
		inFORM = inCODE = bf.bfCode();

		rt = PRIMITIVE_PROCESSOR.seval(*this);
	}
	else
	{
		inFORM = bf;

		rt = PRIMITIVE_PROCESSOR.decode_seval(*this);
	}

	anED->mRID = prevRID;

	return( rt );
}


bool EvaluationEnvironment::eval(const APExecutionData & anED,
		const RuntimeID & aRID, const BFCode & aCode)
{
	RuntimeID prevRID = anED->mRID;
	anED->mRID = aRID;

	inEC = anED->getExecutionContext();

	outED = inED = anED;

	inFORM = inCODE = aCode;

	bool rt = PRIMITIVE_PROCESSOR.seval(*this);

	anED->mRID = prevRID;

	return( rt );
}



/**
 * Serialization
 */
void EvaluationEnvironment::toStream(OutStream & os) const
{
	inEC->traceDefault(os);

	inEC->traceDefaultPostEval(AVM_OS_TRACE);

	outED->toStream(AVM_OS_TRACE);
}



/**
 * CHECK SATISFIABILITY
 */
bool EvaluationEnvironment::evalFormula(const APExecutionData & anED,
		const RuntimeID & aRID, AvmProgram * aProgram, const BF & anExpr)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode * aFormula = anExpr.to_ptr< AvmCode >();

			switch( aFormula->getAvmOpCode() )
			{
				case AVM_OPCODE_OBS :
				{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
//	AVM_OS_TRACE << " ==> evtFormula:> "
//			<< aFormula->second().str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

					const BFCode & evtFormula = aFormula->second().bfCode();

					BF constraintFormula = aFormula->third();

					switch( evtFormula->getAvmOpCode() )
					{
						case AVM_OPCODE_INPUT :
						case AVM_OPCODE_OUTPUT :
						{
							if( evtFormula->first().is< BaseInstanceForm >() )
							{
								BaseInstanceForm * ioInstance = evtFormula->
										first().to_ptr< BaseInstanceForm >();

								if( ioInstance->is< InstanceOfPort >() )
								{
									BFCode ioTrace = searchTraceIO(
											anED->getIOElementTrace(), evtFormula);

									if( ioTrace.valid() )
									{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> aFormula:> "
			<< constraintFormula.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

										if( constraintFormula.isEqualTrue() )
										{
											outVAL = constraintFormula;
										}
										else
										{
											outVAL = ioSubst( anED, aProgram,
													evtFormula, ioTrace,
													constraintFormula );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> EC<" << inEC->getIdNumber()
			<< "> |=?= anExecFormula:> " << outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
										}

										return( true );
									}
								}
								else if( ioInstance->is< InstanceOfData >() )
								{
									if( isAssigned(anED, aRID,
											ioInstance->to< InstanceOfData >()) )
									{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> aFormula:> "
			<< constraintFormula.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

										if( eval(anED, aRID, constraintFormula) )
										{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> EC<" << inEC->getIdNumber()
			<< "> |=?= anExecFormula:> " << outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

											return( true );
										}
									}
								}
							}

							break;
						}

						default:
						{
							if( eval(anED, aRID, evtFormula) )
							{
								if( outVAL.isEqualTrue() )
								{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> Constraint Formula:> "
			<< constraintFormula.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

									if( evalCondition(constraintFormula) )
									{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> EC<" << inEC->getIdNumber()
			<< "> |=?= anExecFormula:> " << outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

										return( true );
									}
								}
							}

							break;
						}
					}

					break;
				}

				default:
				{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
//	AVM_OS_TRACE << " ==> aFormula:> " << aFormula.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

					if( eval(anED, aRID, anExpr.bfCode()) )
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> EC<" << inEC->getIdNumber()
			<< "> |=?= anExecFormula:> " << outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

						return( true );
					}

					break;
				}
			}
			break;
		}

		default:
		{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
//	AVM_OS_TRACE << " ==> aFormula:> " << aFD->formula.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

			if( eval(anED, aRID, anExpr) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> EC<" << inEC->getIdNumber()
			<< "> |=?= anExecFormula:> " << outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

				return( true );
			}

			break;
		}
	}

	return( false );
}




}
