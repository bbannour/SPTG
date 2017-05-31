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
#include <fml/runtime/RuntimeLib.h>

#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>


#include <solver/api/SatSolver.h>
#include <solver/api/SolverDef.h>

#include <solver/CVC4Solver.h>
#include <solver/Z3Solver.h>

#if defined( _AVM_SOLVER_YICES_V2_ )
#include <compat/solver/Yices2Solver.h>
#endif /* _AVM_SOLVER_YICES_V2_ */

// Mandatory after other Solver for compilation FIX
#include <solver/OmegaSolver.h>


namespace sep
{


SatSolver * SolverFactory::theDefaultSolver4CheckSatisfiability = NULL;
SatSolver * SolverFactory::theDefaultSolver4ModelsProduction = NULL;

BFVector SolverFactory::thePCParameters;
BFVector SolverFactory::thePCParameterValues;

APExecutionData     SolverFactory::theSymbolicED;


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
			theDefaultSolver4CheckSatisfiability = new CVC4Solver();

			theDefaultSolver4ModelsProduction =
					new CVC4Solver(true /*to set option << produce-models >>*/);
			break;
		}
#endif /* _AVM_SOLVER_CVC4_ */


#if defined( _AVM_SOLVER_Z3_ )
		case SolverDef::SOLVER_Z3_KIND:
		{
			theDefaultSolver4CheckSatisfiability = new Z3Solver();
			theDefaultSolver4ModelsProduction    = new Z3Solver();
			break;
		}
#endif /* _AVM_SOLVER_Z3_ */


#if defined( _AVM_SOLVER_YICES_V2_ )
		case SolverDef::SOLVER_YICES2_KIND:
		{
			theDefaultSolver4CheckSatisfiability = new Yices2Solver();
			theDefaultSolver4ModelsProduction    = new Yices2Solver();
			break;
		}
#endif /* _AVM_SOLVER_YICES_V2_ */


#if defined( _AVM_SOLVER_OMEGA_ )
		case SolverDef::SOLVER_OMEGA_KIND:
		{
			theDefaultSolver4CheckSatisfiability = new OmegaSolver();
			theDefaultSolver4ModelsProduction    = new OmegaSolver();
			break;
		}
#endif /* _AVM_SOLVER_OMEGA_ */


		case SolverDef::SOLVER_UNDEFINED_KIND:
		default:
		{
#if defined( _AVM_SOLVER_CVC4_ )

			theDefaultSolver4CheckSatisfiability = new CVC4Solver();

			theDefaultSolver4ModelsProduction =
					new CVC4Solver(true /*to set option << produce-models >>*/);

#else

			theDefaultSolver4CheckSatisfiability = NULL;
			theDefaultSolver4ModelsProduction    = NULL;

#endif /* _AVM_SOLVER_CVCx_ */

			break;
		}
	}

////////////////////////////////////////////////////////////////////////////////
// CACHE FOR MEMORY ALLOCATION OPTIMIZATION FOR SOLVER CALCULUS
////////////////////////////////////////////////////////////////////////////////

#if defined( _AVM_SOLVER_CVC4_ )

	CVC4Solver::initCache();

#endif /* _AVM_SOLVER_CVC4_ */


#if defined( _AVM_SOLVER_Z3_ )

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


#if defined( _AVM_SOLVER_Z3_ )

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


#if defined( _AVM_SOLVER_Z3_ )
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
	if( (aSolver != NULL)
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

	theSolver.setSelectedVariable(aMainEC.refExecutionData(), aListOfVarParam);

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

	theSolver.setSelectedVariable( aMainEC.refExecutionData() );

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


#if defined( _AVM_SOLVER_Z3_ )
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
AVM_OS_ASSERT_FATAL_ERROR_EXIT( theDefaultSolver4CheckSatisfiability == NULL )
		<< "SolverFactory::newSolver4CheckSatisfiability:> Unknown solver << "
		<< SolverDef::strSolver( aSolverKind )
		<< " >> in this executable and  there are no default alternative solver!!!"
		<< SEND_ALERT;

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


#if defined( _AVM_SOLVER_Z3_ )
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
AVM_OS_ASSERT_FATAL_ERROR_EXIT( theDefaultSolver4ModelsProduction == NULL )
		<< "SolverFactory::newSolver4ModelsProduction:> Unknown solver << "
		<< SolverDef::strSolver( aSolverKind )
		<< " >> in this executable and and there are no default alternative solver !"
		<< SEND_ALERT;

			return( theDefaultSolver4ModelsProduction );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// CONDITION PARAMETER SOLVING
////////////////////////////////////////////////////////////////////////////////

bool SolverFactory::solve(SolverDef::SOLVER_KIND aSolverKind,
		const BF & aCondition, BFVector & dataVector, BFVector & valuesVector)
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


#if defined( _AVM_SOLVER_Z3_ )
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

APExecutionData SolverFactory::solve(SolverDef::SOLVER_KIND aSolverKind,
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


#if defined( _AVM_SOLVER_Z3_ )
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
AVM_OS_ASSERT_FATAL_ERROR_EXIT( theDefaultSolver4ModelsProduction == NULL )
		<< "SolverFactory::solve:> Unknown solver << "
		<< SolverDef::strSolver( aSolverKind )
		<< " >> in this executable and and there are no default alternative solver !"
		<< SEND_ALERT;

			return( SolverFactory::solve(
				(*theDefaultSolver4ModelsProduction), ENV, anEC, aCondition) );
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
// EXECUTION DATA SOLVING
////////////////////////////////////////////////////////////////////////////////

bool SolverFactory::solve(SatSolver & aSolver, EvaluationEnvironment & ENV,
		APExecutionData & anED, const BF & aCondition)
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

			ExecutableForm * exec = NULL;
			TableOfInstanceOfData::const_raw_iterator itData;
			TableOfInstanceOfData::const_raw_iterator endData;

			TableOfRuntimeT::
			const_iterator itRF = anED->getTableOfRuntime().begin();
			TableOfRuntimeT::
			const_iterator endRF = anED->getTableOfRuntime().end();
			for( RuntimeID itRID ; itRF != endRF ; ++itRF)
			{
				itRID = (*itRF)->getRID();

				exec = itRID.getExecutable();
				if( exec->hasBasicData() )
				{
					itData = exec->getBasicData().begin();
					endData = exec->getBasicData().end();
					for( ; itData != endData ; ++itData)
					{
						const BF & rvalue = ENV.getRvalue(anED, itRID, (itData));

						updateRuntimeParametersValues(rvalue);

						if( ENV.eval(theSymbolicED,
								theSymbolicED->getParametersRID(), rvalue) )
						{
							ENV.setRvalue(anED, itRID, (itData), ENV.outVAL);
						}
						else
						{
							finalizeRuntimeParameters();
							return( false );
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

bool SolverFactory::solveParameters(APExecutionData & anED, const BF & aCondition)
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

		BFVector::raw_iterator< InstanceOfData > itParam = thePCParameters.begin();
		BFVector::raw_iterator< InstanceOfData > endParam = thePCParameters.end();
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

void SolverFactory::setModel(EvaluationEnvironment & ENV, APExecutionData & anED)
{
	ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();

	BaseTypeSpecifier * paramType = NULL;
	BF value;
	TableOfInstanceOfData::const_raw_iterator itParam =
			paramsRF.getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam =
			paramsRF.getParameters().end();
	TableOfData::const_iterator itValue = paramsRF.getDataTable()->begin();
	for( ; itParam != endParam ; ++itParam, ++itValue )
	{
		value  = (*itValue);

		(itParam)->getwModifier().setFeatureFinal( false );

		if( value.isBuiltinValue() )
		{
			/* OK:> value is numeric */
		}
		else if( value != (itParam) )
		{
			if( ENV.eval(anED, anED->getSystemRID(), value) )
			{
				paramsRF.setData((itParam)->getOffset(), ENV.outVAL);
			}
		}
		else if( (itParam)->hasValue() )
		{
			paramsRF.setData((itParam)->getOffset(), (itParam)->getValue());
		}
		else if( (itParam)->hasTypeSpecifier() &&
				(itParam)->getTypeSpecifier()->hasDefaultValue() )
		{
			paramsRF.setData((itParam)->getOffset(),
					(itParam)->getTypeSpecifier()->getDefaultValue());
		}
		else
		{
			paramType = (itParam)->referedTypeSpecifier();

			/* OK:> NO value */
			if( paramType->isTypedNumeric() )
			{
				if( paramType->isTypedInterval() )
				{
					IntervalTypeSpecifier * intervalTS = (itParam)->
							getTypeSpecifier()->as< IntervalTypeSpecifier >();

					if( intervalTS->getInfimum().isNumeric() &&
							intervalTS->getSupremum().isNumeric() )
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
							ExpressionConstructor::newInteger(
								RANDOM::gen_int(
									intervalTS->getInfimum().toInteger(),
									intervalTS->getSupremum().toInteger())) );
					}
					else if( intervalTS->isLClosed() )
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
								intervalTS->getInfimum() );
					}
					else if( intervalTS->isRClosed() )
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
								intervalTS->getSupremum() );
					}
					else
					{
						// Calcul aléatoire d'un nombre entier
						paramsRF.setData( (itParam)->getOffset(),
							ExpressionConstructor::divExpr(
									ExpressionConstructor::addExpr(
										intervalTS->getInfimum(),
										intervalTS->getSupremum()),
									ExpressionConstant::INTEGER_TWO) );
					}
				}
				else
				{
					// Calcul aléatoire d'un nombre entier
					paramsRF.setData((itParam)->getOffset(),
						ExpressionConstructor::newInteger(
							RANDOM::gen_uint(0, AVM_NUMERIC_MAX_INT8)) );
				}
			}

			else if( paramType->isTypedBoolean() )
			{
				// Calcul aléatoire d'un nombre compris entre 0 et 1
				paramsRF.setData((itParam)->getOffset(),
						ExpressionConstructor::newBoolean(
								RANDOM::gen_uint(0, 1) != 0));
			}
			else if( paramType->isTypedEnum() )
			{
				// Choix aléatoire d'un symbol du type Enum
				paramsRF.setData((itParam)->getOffset(),
						paramType->as< EnumTypeSpecifier
									>()->getRandomSymbolData());
			}

			else if( paramType->isTypedString() )
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
			else if( paramType->isTypedCharacter() )
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

			else if( paramType->isTypedMachine() )
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


void SolverFactory::resetModel(APExecutionData & anED)
{
	ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();

	TableOfInstanceOfData::const_raw_iterator itParam =
			paramsRF.getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam =
			paramsRF.getParameters().end();
	for( ; itParam != endParam ; ++itParam )
	{
		(itParam)->getwModifier().setFeatureFinal( true );
	}
}



void SolverFactory::setRuntimeParametersSolvingValues(APExecutionData & anED)
{
	theSymbolicED = anED;

	ParametersRuntimeForm & paramsRF =
			theSymbolicED.getWritableParametersRuntimeForm();

	paramsRF.resetOffset();

	BFVector::raw_iterator< InstanceOfData > itVar = thePCParameters.begin();
	BFVector::raw_iterator< InstanceOfData > endVar = thePCParameters.end();
	for( avm_offset_t offset = 0 ; itVar != endVar ; ++itVar, ++offset )
	{
		(itVar)->getwModifier().setFeatureFinal( false );

//		if( (itVar) != paramsRF.rawVariable((itVar)->getOffset()) )
//		{
//			AVM_OS_COUT << ":?!?> " << (itVar)->getFullyQualifiedNameID()
//					<< " (param: " << paramsRF.rawVariable(
//						(itVar)->getOffset())->getFullyQualifiedNameID() << ")"
//					<< " = " << paramsRF.getData((itVar)->getOffset()).str()
//					<< " <- " << thePCParameterValues[offset].str()
//					<< std::endl;
//		}

		paramsRF.setData((itVar)->getOffset(), thePCParameterValues[offset]);
	}
}


void SolverFactory::updateRuntimeParametersValues(const BF & aValue)
{
	BFVector exprVariableVector;
	ExpressionFactory::collectVariable(aValue, exprVariableVector);

	const ParametersRuntimeForm & paramsRF =
			theSymbolicED->getParametersRuntimeForm();

	BFVector::raw_iterator< InstanceOfData > itVar = exprVariableVector.begin();
	BFVector::raw_iterator< InstanceOfData > endVar = exprVariableVector.end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( not thePCParameters.contains(*itVar) )
		{
			(itVar)->getwModifier().setFeatureFinal( false );

			if( (itVar)->hasValue() )
			{
				paramsRF.setData((itVar)->getOffset(), (itVar)->getValue());
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
			theSymbolicED->getParametersRuntimeForm().getVariables().begin();
	TableOfInstanceOfData::const_raw_iterator endVar =
			theSymbolicED->getParametersRuntimeForm().getVariables().end();
	for( ; itVar != endVar ; ++itVar )
	{
		(itVar)->getwModifier().setFeatureFinal( true );
	}

	theSymbolicED.destroy();
}


////////////////////////////////////////////////////////////////////////////
// EXECUTION DATA NEWFRESH
////////////////////////////////////////////////////////////////////////////

APExecutionData SolverFactory::solveNewfresh(SolverDef::SOLVER_KIND aSolverKind,
		EvaluationEnvironment & ENV, const ExecutionContext & anEC,
		const BF & aCondition)
{
	APExecutionData anED = anEC.getAPExecutionData();

	ParametersRuntimeForm & paramsRF = anED.getWritableParametersRuntimeForm();

	BF value;
	TableOfInstanceOfData::const_raw_iterator itParam =
			paramsRF.getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam =
			paramsRF.getParameters().end();
	TableOfData::const_iterator itValue = paramsRF.getDataTable()->begin();
	for( ; itParam != endParam ; ++itParam, ++itValue )
	{
		value  = (*itValue);

		(itParam)->getwModifier().setFeatureFinal( false );

		if( value.isBuiltinValue() )
		{
			/* OK:> value is numeric */
		}
		else if( value != (itParam) )
		{
			if( ENV.eval(anED, anED->getSystemRID(), value) )
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


}
