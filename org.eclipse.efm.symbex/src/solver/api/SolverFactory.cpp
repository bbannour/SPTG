/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SolverFactory.h"

#include <common/BF.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/executable/ExecutableLib.h>

#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeLib.h>

#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>

#include <fml/workflow/WObject.h>

#include <solver/api/SatSolver.h>
#include <solver/api/SolverDef.h>

#include <solver/CVC4Solver.h>
#include <solver/Z3Solver.h>

#if defined( _AVM_SOLVER_YICES_V2_ )
#include <solver/Yices2Solver.h>
#endif /* _AVM_SOLVER_YICES_V2_ */

// Mandatory after other Solver for compilation FIX
#include <solver/OmegaSolver.h>


namespace sep
{


SatSolver * SolverFactory::theDefaultSolver4CheckSatisfiability = nullptr;
SatSolver * SolverFactory::theDefaultSolver4ModelsProduction = nullptr;

InstanceOfData::Table SolverFactory::thePCParameters;
BFVector SolverFactory::thePCParameterValues;

ExecutionData SolverFactory::theSymbolicED;


/**
 * LOADER
 */
void SolverFactory::load()
{
	switch( SolverDef::DEFAULT_SOLVER_KIND )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		{
			CVC4Solver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new CVC4Solver();

			theDefaultSolver4ModelsProduction =
					new CVC4Solver(true /*to set option << produce-models >>*/);

			break;
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			Z3Solver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new Z3Solver();
			theDefaultSolver4ModelsProduction    = new Z3Solver();
			break;
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		{
			Yices2Solver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new Yices2Solver();
			theDefaultSolver4ModelsProduction    = new Yices2Solver();
			break;
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			OmegaSolver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new OmegaSolver();
			theDefaultSolver4ModelsProduction    = new OmegaSolver();
			break;
		}
#endif /* _AVM_SOLVER_OMEGA_ */


		case SolverDef::SOLVER_UNDEFINED_KIND:
		default:
		{
#if defined( _AVM_SOLVER_CVC4_ )

			CVC4Solver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new CVC4Solver();

			theDefaultSolver4ModelsProduction =
					new CVC4Solver(true /*to set option << produce-models >>*/);

			SolverDef::DEFAULT_SOLVER_KIND = SolverDef::SOLVER_CVC4_KIND;

#elif( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )

			Z3Solver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new Z3Solver();
			theDefaultSolver4ModelsProduction    = new Z3Solver();

			SolverDef::DEFAULT_SOLVER_KIND = SolverDef::SOLVER_Z3_KIND;

#elif defined( _AVM_SOLVER_YICES_V2_ )

			Yices2Solver::configure(WObject::_NULL_);

			theDefaultSolver4CheckSatisfiability = new Yices2Solver();
			theDefaultSolver4ModelsProduction    = new Yices2Solver();

			SolverDef::DEFAULT_SOLVER_KIND = SolverDef::SOLVER_YICES2_KIND;

#else

			theDefaultSolver4CheckSatisfiability = nullptr;
			theDefaultSolver4ModelsProduction    = nullptr;

#endif /* _AVM_SOLVER_XXX_ */

			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( theDefaultSolver4CheckSatisfiability )
					<< "SolverFactory::load:> Unfound default solver << "
					<< SolverDef::strSolver( SolverDef::DEFAULT_SOLVER_KIND )
					<< " >> in this executable and and there are no alternative solver !"
					<< SEND_EXIT;

			break;
		}
	}

////////////////////////////////////////////////////////////////////////////////
// CACHE FOR MEMORY ALLOCATION OPTIMIZATION FOR SOLVER CALCULUS
////////////////////////////////////////////////////////////////////////////////

#if defined( _AVM_SOLVER_CVC4_ )

	CVC4Solver::initCache();

#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )

	Z3Solver::initCache();

#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )

	Yices2Solver::initCache();

#endif /* _AVM_SOLVER_YICES_V2_ */
}


/**
 * DISPOSER
 */
void SolverFactory::dispose()
{
	delete( theDefaultSolver4CheckSatisfiability );
	delete( theDefaultSolver4ModelsProduction );

#if defined( _AVM_SOLVER_CVC4_ )

	CVC4Solver::finalizeCache();

#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )

	Z3Solver::finalizeCache();

#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )

	Yices2Solver::finalizeCache();

#endif /* _AVM_SOLVER_YICES_V2_ */
}


SolverDef::SATISFIABILITY_RING SolverFactory::isSatisfiable(
		SolverDef::SOLVER_KIND aSolverKind, const BF & aCondition)
{
	if( aCondition.isEqualTrue() )
	{
		return( SolverDef::SATISFIABLE );
	}
	else if( aCondition.isEqualFalse() )
	{
		return( SolverDef::UNSATISFIABLE );
	}

	switch( aSolverKind )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		case SolverDef::SOLVER_CVC4_BV32_KIND:
		case SolverDef::SOLVER_CVC_KIND:
		{
			CVC4Solver solver;

			return( solver.isSatisfiable( aCondition ) );
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			Z3Solver solver;

			return( solver.isSatisfiable( aCondition ) );
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		case SolverDef::SOLVER_YICES_KIND:
		{
			Yices2Solver solver;

			return( solver.isSatisfiable( aCondition ) );
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			OmegaSolver solver;

			return( solver.isSatisfiable( aCondition ) );
		}
#endif /* _AVM_SOLVER_OMEGA_ */

		default:
		{
			AVM_OS_WARNING_ALERT
					<< "SolverFactory::isSatisfiable:> Unknown solver << "
					<< SolverDef::strSolver( aSolverKind )
					<< " >> in this executable !!!"
					<< SEND_ALERT;

			return( SolverDef::UNKNOWN_SAT );
		}
	}

	return( SolverDef::UNKNOWN_SAT );
}


/**
 * DESTROY
 */
void SolverFactory::destroy(SatSolver * aSolver)
{
	if( (aSolver != nullptr)
		&& (aSolver != SolverFactory::theDefaultSolver4CheckSatisfiability)
		&& (aSolver != SolverFactory::theDefaultSolver4ModelsProduction) )
	{
		delete( aSolver );
	}
}

SolverDef::SATISFIABILITY_RING SolverFactory::isSatisfiable(
		const BF & aCondition, bool useDefaultSolver)
{
	if( aCondition.isEqualTrue() )
	{
		return( SolverDef::SATISFIABLE );
	}
	else if( aCondition.isEqualFalse() )
	{
		return( SolverDef::UNSATISFIABLE );
	}
	else if( useDefaultSolver )
	{
		return( SolverFactory::isSatisfiable(
				SolverDef::DEFAULT_SOLVER_KIND, aCondition) );
	}

	return( SolverDef::UNKNOWN_SAT );
}



/**
 * USED BY FAM LtlProverFilter
 */
bool SolverFactory::isEmptyIntersection(ListOfInstanceOfData aListOfVarParam,
		const ExecutionContext & aMainEC, const ExecutionContext & aComparEC)
{
#if defined( _AVM_SOLVER_OMEGA_ )

	OmegaSolver theSolver;

	theSolver.setSelectedVariable(aMainEC.getExecutionData(), aListOfVarParam);

	return( theSolver.isEmptyIntersection( aMainEC , aComparEC ) );

#else

	return( false );

#endif /* _AVM_SOLVER_OMEGA_ */
}

bool SolverFactory::isSubSet(
		const ExecutionContext & aMainEC, const ExecutionContext & aComparEC)
{
#if defined( _AVM_SOLVER_OMEGA_ )

	OmegaSolver theSolver;

	theSolver.setSelectedVariable( aMainEC.getExecutionData() );

	return( theSolver.isSubSet( aMainEC , aComparEC) );

#else

	return( false );

#endif /* _AVM_SOLVER_OMEGA_ */
}


/**
 * SOLVER
 */

SatSolver * SolverFactory::newSolver4CheckSatisfiability(
		SolverDef::SOLVER_KIND aSolverKind)
{
	switch( aSolverKind )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		case SolverDef::SOLVER_CVC_KIND:
		{
			return( new CVC4Solver() );
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			return( new Z3Solver() );
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		case SolverDef::SOLVER_YICES_KIND:
		{
			return( new Yices2Solver() );
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			return( new OmegaSolver() );
		}
#endif /* _AVM_SOLVER_OMEGA_ */

		default:
		{
			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( theDefaultSolver4CheckSatisfiability )
					<< "SolverFactory::newSolver4CheckSatisfiability:> Unknown solver << "
					<< SolverDef::strSolver( aSolverKind )
					<< " >> in this executable and  there are no default alternative solver!!!"
					<< SEND_EXIT;

			SolverDef::toStreamSolverList(AVM_OS_COUT, "Available solver");

			return( theDefaultSolver4CheckSatisfiability );
		}
	}
}


SatSolver * SolverFactory::newSolver4ModelsProduction(
		SolverDef::SOLVER_KIND aSolverKind)
{
	switch( aSolverKind )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		case SolverDef::SOLVER_CVC_KIND:
		{
			return( new CVC4Solver(true/*produce-models*/) );
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			return( new Z3Solver() );
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		case SolverDef::SOLVER_YICES_KIND:
		{
			return( new Yices2Solver() );
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			return( new OmegaSolver() );
		}
#endif /* _AVM_SOLVER_OMEGA_ */

		default:
		{
			AVM_OS_ASSERT_FATAL_ERROR_EXIT( theDefaultSolver4ModelsProduction )
					<< "SolverFactory::newSolver4ModelsProduction:> Unknown solver << "
					<< SolverDef::strSolver( aSolverKind )
					<< " >> in this executable and and there are no default alternative solver !"
					<< SEND_EXIT;

			return( theDefaultSolver4ModelsProduction );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// CONDITION PARAMETER SOLVING
////////////////////////////////////////////////////////////////////////////////

bool SolverFactory::solve(SolverDef::SOLVER_KIND aSolverKind, const BF & aCondition,
		InstanceOfData::Table & dataVector, BFVector & valuesVector)
{
	switch( aSolverKind )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		case SolverDef::SOLVER_CVC_KIND:
		{
			CVC4Solver solver(true /*to set option << produce-models >>*/);

			return( solver.solve( aCondition, dataVector, valuesVector ) );
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			Z3Solver solver;
			return( solver.solve( aCondition, dataVector, valuesVector ) );
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		case SolverDef::SOLVER_YICES_KIND:
		{
			Yices2Solver solver;

			return( solver.solve( aCondition, dataVector, valuesVector ) );
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			OmegaSolver solver;

			return( solver.solve( aCondition, dataVector, valuesVector ) );
		}
#endif /* _AVM_SOLVER_OMEGA_ */

		default:
		{
			AVM_OS_WARNING_ALERT
					<< "SolverFactory::solve:> Unknown solver << "
					<< SolverDef::strSolver( aSolverKind )
					<< " >> in this executable !!!"
					<< SEND_ALERT;

			return( false );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// EXECUTION CONTEXT SOLVING
////////////////////////////////////////////////////////////////////////////////

ExecutionData SolverFactory::solve(SolverDef::SOLVER_KIND aSolverKind,
		EvaluationEnvironment & ENV, const ExecutionContext & anEC,
		const BF & aCondition)
{
	switch( aSolverKind )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		case SolverDef::SOLVER_CVC_KIND:
		{
			CVC4Solver aSolver(true /*to set option << produce-models >>*/);

			return( SolverFactory::solve(aSolver, ENV, anEC, aCondition) );
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			Z3Solver aSolver;

			return( SolverFactory::solve(aSolver, ENV, anEC, aCondition) );
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		case SolverDef::SOLVER_YICES_KIND:
		{
			Yices2Solver aSolver;

			return( SolverFactory::solve(aSolver, ENV, anEC, aCondition) );
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			OmegaSolver aSolver;

			return( SolverFactory::solve(aSolver, ENV, anEC, aCondition) );
		}
#endif /* _AVM_SOLVER_OMEGA_ */


		default:
		{
			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( theDefaultSolver4ModelsProduction )
					<< "SolverFactory::solve:> Unknown solver << "
					<< SolverDef::strSolver( aSolverKind )
					<< " >> in this executable and and there are no default alternative solver !"
					<< SEND_EXIT;

			return( SolverFactory::solve(
				(*theDefaultSolver4ModelsProduction), ENV, anEC, aCondition) );
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
// EXECUTION DATA SOLVING
////////////////////////////////////////////////////////////////////////////////

bool SolverFactory::solve(SatSolver & aSolver, EvaluationEnvironment & ENV,
		ExecutionData & anED, const BF & aCondition)
{
	thePCParameters.clear();
	thePCParameterValues.clear();

	// On numérise le PC

	// On crée un ED avec des valeurs numériques
	if( aSolver.solve( aCondition, thePCParameters, thePCParameterValues ) )
	{
		if( thePCParameterValues.nonempty() )
		{
			setRuntimeParametersSolvingValues(anED);

			ExecutableForm * exec = nullptr;
			TableOfInstanceOfData::const_ref_iterator itVar;
			TableOfInstanceOfData::const_ref_iterator endVar;

			TableOfRuntimeT::
			const_iterator itRF = anED.getTableOfRuntime().begin();
			TableOfRuntimeT::
			const_iterator endRF = anED.getTableOfRuntime().end();
			for( RuntimeID itRID ; itRF != endRF ; ++itRF)
			{
				itRID = (*itRF)->getRID();

				exec = itRID.getExecutable();
				if( exec->hasBasicVariable() )
				{
					itVar = exec->getBasicVariables().begin();
					endVar = exec->getBasicVariables().end();
					for( ; itVar != endVar ; ++itVar)
					{
						if( (itVar)->getModifier().hasNatureMacro() )
						{
							//!! LET UNCHANGED
						}
						else
						{
							const BF & rvalue = ENV.getRvalue(anED, itRID, (itVar));

							updateRuntimeParametersValues(rvalue);

							if( ENV.eval(theSymbolicED,
									theSymbolicED.getParametersRID(), rvalue) )
							{
								ENV.setRvalue(anED, itRID, (itVar), ENV.outVAL);
							}
							else
							{
								finalizeRuntimeParameters();
								return( false );
							}
						}
					}
				}
			}

			finalizeRuntimeParameters();
		}
		thePCParameters.clear();
		thePCParameterValues.clear();

		return( true );
	}
	else
	{
		thePCParameters.clear();
		thePCParameterValues.clear();

		return( false );
	}
}


////////////////////////////////////////////////////////////////////////////////
// EXECUTION CONTEXT PARAMETERS NUMERIZATION
////////////////////////////////////////////////////////////////////////////////

bool SolverFactory::solveParameters(ExecutionData & anED, const BF & aCondition)
{
	if( aCondition.isEqualTrue() )
	{
		return( false );
	}

	thePCParameters.clear();
	thePCParameterValues.clear();

	if( theDefaultSolver4ModelsProduction->solve(
			aCondition, thePCParameters, thePCParameterValues) )
	{
		ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();
		APTableOfData & aDataTable = paramsRF.getWritableDataTable();

		InstanceOfData::Table::raw_iterator itParam = thePCParameters.begin();
		InstanceOfData::Table::raw_iterator endParam = thePCParameters.end();
		for( std::size_t offset = 0 ; itParam != endParam ; ++itParam , ++offset )
		{
			aDataTable->set( (itParam), thePCParameterValues[offset] );
		}

		return( true );
	}

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
// Pour pouvoir reutiliser tout l'outillage de Diverity
////////////////////////////////////////////////////////////////////////////////

void SolverFactory::setModel(EvaluationEnvironment & ENV, ExecutionData & anED)
{
	ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();

	BF value;
	TableOfInstanceOfData::ref_iterator itParam = paramsRF.getParameters().begin();
	TableOfInstanceOfData::ref_iterator endParam = paramsRF.getParameters().end();
	TableOfData::const_iterator itValue = paramsRF.getDataTable()->begin();
	for( ; itParam != endParam ; ++itParam, ++itValue )
	{
		value = (*itValue);

		(itParam)->getwModifier().setFeatureFinal( false );

		if( value.isBuiltinValue() )
		{
			/* OK:> value is numeric */
		}
		else if( value != (*itParam) )
		{
			if( ENV.eval(anED, anED.getSystemRID(), value) )
			{
				paramsRF.setData((itParam)->getOffset(), ENV.outVAL);
			}
		}
		else if( (itParam)->hasValue() )
		{
			paramsRF.setData((itParam)->getOffset(), (itParam)->getValue());
		}
		else if( (itParam)->hasTypeSpecifier() &&
				(itParam)->getTypeSpecifier().hasDefaultValue() )
		{
			paramsRF.setData((itParam)->getOffset(),
					(itParam)->getTypeSpecifier().getDefaultValue());
		}
		else
		{
			const BaseTypeSpecifier & paramType =
					(itParam)->referedTypeSpecifier();

			/* OK:> NO value */
			if( paramType.isTypedNumeric() )
			{
				if( paramType.isTypedInterval() )
				{
					const IntervalTypeSpecifier & intervalTS = (itParam)->
							getTypeSpecifier().as< IntervalTypeSpecifier >();

					if( intervalTS.getInfimum().isNumeric() &&
							intervalTS.getSupremum().isNumeric() )
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
							ExpressionConstructor::newInteger(
								RANDOM::gen_int(
									intervalTS.getInfimum().toInteger(),
									intervalTS.getSupremum().toInteger())) );
					}
					else if( intervalTS.isLClosed() )
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
								intervalTS.getInfimum() );
					}
					else if( intervalTS.isRClosed() )
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
								intervalTS.getSupremum() );
					}
					else
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
							ExpressionConstructor::divExpr(
									ExpressionConstructor::addExpr(
										intervalTS.getInfimum(),
										intervalTS.getSupremum()),
									ExpressionConstant::INTEGER_TWO) );
					}
				}
				else
				{
					// Calcul aléatoire d'un nombre entier
					paramsRF.setData((itParam)->getOffset(),
						ExpressionConstructor::newInteger(
							RANDOM::gen_uint(0, INT8_MAX)) );
				}
			}

			else if( paramType.isTypedBoolean() )
			{
				// Calcul aléatoire d'un nombre compris entre 0 et 1
				paramsRF.setData((itParam)->getOffset(),
						ExpressionConstructor::newBoolean(
								RANDOM::gen_uint(0, 1) != 0));
			}
			else if( paramType.isTypedEnum() )
			{
				// Choix aléatoire d'un symbol du type Enum
				paramsRF.setData((itParam)->getOffset(),
					paramType.as< EnumTypeSpecifier >().getRandomSymbolData());
			}

			else if( paramType.isTypedString() )
			{
				// Calcul aléatoire d'une chaine de charactère

				paramsRF.setData((itParam)->getOffset(),
					ExpressionConstructor::newString("<< random string >>"));

//				AVM_OS_FATAL_ERROR_EXIT
//						<< "SolverFactory::setModel:> "
//							"Unexpected symbolic value for << "
//						<< str_header( *itParam ) << " >> !!!"
//						<< SEND_EXIT;

			}
			else if( paramType.isTypedCharacter() )
			{
				// Choix aléatoire d'un charactère

				paramsRF.setData((itParam)->getOffset(),
					ExpressionConstructor::newChar(RANDOM::gen_char()));

//				AVM_OS_FATAL_ERROR_EXIT
//						<< "SolverFactory::setModel:> "
//							"Unexpected symbolic value for << "
//						<< str_header( *itParam ) << " >> !!!"
//						<< SEND_EXIT;
			}

			else if( paramType.isTypedMachine() )
			{
				paramsRF.setData((itParam)->getOffset(),
						RuntimeLib::RID_ENVIRONMENT);

//				AVM_OS_FATAL_ERROR_EXIT
//						<< "SolverFactory::setModel:> "
//							"Unexpected symbolic value for << "
//						<< str_header( *itParam ) << " >> !!!"
//						<< SEND_EXIT;
			}

			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "SolverFactory::setModel:> "
							"Unexpected symbolic parameter type << "
						<< str_header( *itParam ) << " >> !!!"
					<< SEND_EXIT;
			}
		}
	}
}


void SolverFactory::resetModel(ExecutionData & anED)
{
	ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();

	TableOfInstanceOfData::ref_iterator itParam = paramsRF.getParameters().begin();
	TableOfInstanceOfData::ref_iterator endParam = paramsRF.getParameters().end();
	for( ; itParam != endParam ; ++itParam )
	{
		(itParam)->getwModifier().setFeatureFinal( true );
	}
}



void SolverFactory::setRuntimeParametersSolvingValues(ExecutionData & anED)
{
	theSymbolicED = anED;

	ParametersRuntimeForm & paramsRF =
			theSymbolicED.getWritableParametersRuntimeForm();

	paramsRF.resetOffset();

	InstanceOfData::Table::raw_iterator itVar = thePCParameters.begin();
	InstanceOfData::Table::raw_iterator endVar = thePCParameters.end();
	for( avm_offset_t offset = 0 ; itVar != endVar ; ++itVar, ++offset )
	{
		(itVar)->getwModifier().setFeatureFinal( false );

		if( (itVar)->getOffset() >= paramsRF.getVariables().size() )
		{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << "SolverFactory:>setting runtime parameters solving values"
			<< std::endl << anED.getExecutionContext()->str() << std::endl
			<< "\tAdding (parameter , value) @ " << (itVar)->getOffset()
			<< " : " << (itVar)->getFQNameID()
			<< " = " << thePCParameterValues[offset] << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

				paramsRF.appendParameter(*itVar, thePCParameterValues[offset]);
		}
		else if( (itVar) != paramsRF.rawVariable((itVar)->getOffset()) )
		{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << "SolverFactory:>setting runtime parameters solving values"
			<< std::endl << anED.getExecutionContext()->str() << std::endl
			<< "\tAdding (parameter , value) @ " << (itVar)->getOffset()
			<< " : " << (itVar)->getFQNameID()
			<< " = " << thePCParameterValues[offset] << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

			paramsRF.appendParameter(*itVar, thePCParameterValues[offset]);
		}
		else
		{
			paramsRF.setData((itVar)->getOffset(), thePCParameterValues[offset]);
		}
	}

//!@!UNDO
//	paramsRF.incrRefCount();
//	anED.saveParametersRuntimeForm( & paramsRF );

//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
//	AVM_OS_TRACE << "Après setRuntimeParametersSolvingValues : paramsRF ..." << EOL_FLUSH;
//	//	aTraceEC->getExecutionData().toStreamData(AVM_OS_TRACE);
//	paramsRF.toStreamData(anED, AVM_OS_TRACE);
//
//	AVM_OS_TRACE << "Après setRuntimeParametersSolvingValues : theSymbolicED ..." << EOL_FLUSH;
//	theSymbolicED.getParametersRuntimeForm().toStreamData(anED, AVM_OS_TRACE);
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
}


void SolverFactory::updateRuntimeParametersValues(const BF & aValue)
{
	InstanceOfData::Table exprVariableVector;
	ExpressionFactory::collectVariable(aValue, exprVariableVector);

	ParametersRuntimeForm & paramsRF =
			theSymbolicED.getWritableParametersRuntimeForm();

	InstanceOfData::Table::raw_iterator itVar = exprVariableVector.begin();
	InstanceOfData::Table::raw_iterator endVar = exprVariableVector.end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( not thePCParameters.contains(*itVar) )
		{
			(itVar)->getwModifier().setFeatureFinal( false );

			if( (itVar)->hasValue() )
			{
				paramsRF.setData((itVar)->getOffset(), (itVar)->getValue());
			}
			else if( (itVar)->getOffset() >= paramsRF.getVariables().size() )
			{
					paramsRF.appendParameter((*itVar), (*itVar));
			}
			else
			{
				paramsRF.setData((itVar)->getOffset(), (*itVar));
			}
		}
	}
}



void SolverFactory::finalizeRuntimeParameters()
{
	TableOfInstanceOfData::const_raw_iterator itVar =
			theSymbolicED.getParametersRuntimeForm().getVariables().begin();
	TableOfInstanceOfData::const_raw_iterator endVar =
			theSymbolicED.getParametersRuntimeForm().getVariables().end();
	for( ; itVar != endVar ; ++itVar )
	{
		(itVar)->getwModifier().setFeatureFinal( true );
	}

	theSymbolicED.destroy();
}


////////////////////////////////////////////////////////////////////////////
// EXECUTION DATA NEWFRESH
////////////////////////////////////////////////////////////////////////////

ExecutionData SolverFactory::solveNewfresh(SolverDef::SOLVER_KIND aSolverKind,
		EvaluationEnvironment & ENV, const ExecutionContext & anEC,
		const BF & aCondition)
{
	ExecutionData anED = anEC.getExecutionData();

	ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();

	BF value;
	TableOfInstanceOfData::ref_iterator itParam = paramsRF.getParameters().begin();
	TableOfInstanceOfData::ref_iterator endParam = paramsRF.getParameters().end();
	TableOfData::const_iterator itValue = paramsRF.getDataTable()->begin();
	for( ; itParam != endParam ; ++itParam, ++itValue )
	{
		value = (*itValue);

		(itParam)->getwModifier().setFeatureFinal( false );

		if( value.isBuiltinValue() )
		{
			/* OK:> value is numeric */
		}
		else if( value != (*itParam) )
		{
			if( ENV.eval(anED, anED.getSystemRID(), value) )
			{
				paramsRF.setData((itParam)->getOffset(), ENV.outVAL);
			}
		}
		else if( (itParam)->hasValue() )
		{
			paramsRF.setData((itParam)->getOffset(), (itParam)->getValue());
		}
		else
		{
			BFList paramList;

			value = ENV.createNewFreshParam(
					paramsRF.getRID(), (itParam), paramList );

			paramsRF.setData( (itParam)->getOffset(), value );
		}
	}

	return( anED );
}


////////////////////////////////////////////////////////////////////////////
// TO_SMT
////////////////////////////////////////////////////////////////////////////

bool SolverFactory::to_smt(OutStream & os, const BF & aCondition,
		SolverDef::SOLVER_KIND aSolverKind, bool enableModelProduction)
{
	switch( aSolverKind )
	{
#if defined( _AVM_SOLVER_CVC4_ )
		case SolverDef::SOLVER_CVC4_KIND:
		case SolverDef::SOLVER_CVC_KIND:
		{
			CVC4Solver aSolver(enableModelProduction /*to set option << produce-models >>*/);

			return( aSolver.to_smt(os, aCondition) );
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if( defined( _AVM_SOLVER_Z3_ ) or defined( _AVM_SOLVER_Z3_C_ ) )
		case SolverDef::SOLVER_Z3_KIND:
		{
			Z3Solver aSolver;

			return aSolver.to_smt(os, aCondition, enableModelProduction);
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		case SolverDef::SOLVER_YICES_KIND:
		{
			Yices2Solver aSolver;

			return aSolver.to_smt(os, aCondition, enableModelProduction);
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
#endif /* _AVM_SOLVER_OMEGA_ */


		default:
		{
			AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( theDefaultSolver4ModelsProduction )
					<< "SolverFactory::to_smt:> Unknown solver << "
					<< SolverDef::strSolver( aSolverKind )
					<< " >> in this executable and and there are no default alternative solver !"
					<< SEND_EXIT;

			return theDefaultSolver4ModelsProduction->to_smt(os,
					aCondition, enableModelProduction);
		}
	}

	return false;
}


}
