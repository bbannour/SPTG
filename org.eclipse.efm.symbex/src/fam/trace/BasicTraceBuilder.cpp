/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BasicTraceBuilder.h"


#include <collection/Typedef.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/expression/ExpressionFactory.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/TableOfData.h>

#include <fml/template/TimedMachine.h>

#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/type/TypeManager.h>

#include <fam/trace/AvmTraceGenerator.h>
#include <fam/trace/TraceManager.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
BasicTraceBuilder::BasicTraceBuilder(AvmTraceGenerator & aProcessor,
		SolverDef::SOLVER_KIND aSolverKind, TraceFilter & aTracePointFilter)
: AbstractTraceBuilder( aProcessor ),
ENV( aProcessor.getENV() ),

isSDLFlag( false ),
printInitValuesFlag( false ),

mTraceManager( NULL ),
mSolverKind( aSolverKind ),
mTracePointFilter(  aTracePointFilter ),

mStepBeginSeparatorFlag( false ),
mStepEndSeparatorFlag( false ),

////////////////////////////////////////////////////////////////////////////
// Computing Variables
aTraceElement( NULL ),
aTracePoint( NULL ),
bfTP( ),
TP_ID( 0 ),

mTraceCache( ),
aRootEC( NULL ),
aTraceEC( NULL ),
itEC( ),
endEC( ),

code( ),
object( NULL ),
value( )
{
	//!! NOTHING
}



////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////
/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 section REPORT
 ...
 endsection REPORT

 section PROPERTY
 ...
 endsection PROPERTY

 section TRACE
  // AND --> conjunctive
  // OR  --> disjunctive
  // XOR --> exclusive
  // NOT --> negative
  @combinator = 'OR';

  @path#condition = "[*]";
  @path#timed#condition = "[*]";

  @time = "$delta";
  @time = "$time";

  @assign = "sens";

  @newfresh = "sens";

  @com    = "env";

  @signal = "sens";
  @port   = "env";

  @input  = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";

  @transition = "t8";
  @machine = "m1";
  @procedure = "[*]";
 endsection TRACE

 section FORMAT
 ...
 endsection FORMAT
endprototype
*/
bool BasicTraceBuilder::configureImpl(WObject * wfParameterObject)
{
	WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY == WObject::_NULL_ )
	{
		return false;
	}

	std::string format = Query::getWPropertyString(
			thePROPERTY, "format", "BASIC#XLIA");
	isSDLFlag = ( format.find("SDL") != std::string::npos );

	printInitValuesFlag = Query::getRegexWPropertyBoolean(thePROPERTY,
			CONS_WID2("show", "initialization") "|"
			CONS_WID3("print", "initial", "values"), false);


	WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT"));

	if( theFORMAT != WObject::_NULL_ )
	{
		mStepBeginSeparatorFlag =
				Query::hasRegexWProperty(
						theFORMAT, CONS_WID2("step", "begin"));

		mStepEndSeparatorFlag =
				Query::hasRegexWProperty(
						theFORMAT, CONS_WID2("step", "end"));
	}


	return true;
}


////////////////////////////////////////////////////////////////////////////////
// CONSTRUCTION API
////////////////////////////////////////////////////////////////////////////////

void BasicTraceBuilder::build(TraceManager & aTraceManager)
{
	mTraceManager = (& aTraceManager);

//	updateFlags();

	// Collect and Compute all TraceSequence
	build( *( mProcessor.getConfiguration().getFirstTrace() ) );
}


void BasicTraceBuilder::build(const ExecutionContext & anEC)
{
	mTraceCache.push_back( & anEC );

	if( anEC.isLeafNode() )
	{
		if( SolverFactory::isStrongSatisfiable(mSolverKind,
				anEC.refExecutionData().getAllPathCondition()) )
		{
			buildTrace();
		}
		else
		{
AVM_IF_DEBUG_FLAG2( PROCESSOR , TRACE )
	AVM_OS_TRACE << std::endl
			<< "BasicTraceBuilder::build:> Unsatisfiable PC << "
			<< anEC.refExecutionData().getAllPathCondition().str()
			<< " >> with solver << " << SolverDef::strSolver( mSolverKind )
			<< " >> for the EC:" << std::endl;
	anEC.traceDefault( AVM_OS_TRACE );
	anEC.refExecutionData().toStreamData( AVM_OS_TRACE );
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( PROCESSOR , TRACE )
		}
	}
	else
	{
		ExecutionContext::child_iterator itEC = anEC.begin();
		for( ; itEC != anEC.end() ; ++itEC )
		{
			build( *( *itEC ) );

			mTraceCache.pop_back();
		}
	}
}


void BasicTraceBuilder::buildTrace()
{
	// La tête du chemin
	aRootEC = mTraceCache.front();
	// la queue du chemin
	aTraceEC = mTraceCache.back();

	aTraceElement = new TraceSequence(aTraceEC, mTraceManager->newTID());
	mTraceManager->append( aTraceElement );

	endEC = mTraceCache.end();


	if( mTracePointFilter.hasPathConditionTracePoint()
		&& aTraceEC->refExecutionData().hasPathCondition() )
	{
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF,
				AVM_OPCODE_CHECK_SAT,
				aTraceEC->refExecutionData().getPathCondition());

		aTracePoint->tpid = ++TP_ID;
		aTraceElement->points.append( bfTP );
	}

	if( mTracePointFilter.hasPathTimedConditionTracePoint()
		&& aTraceEC->refExecutionData().hasPathTimedCondition() )
	{
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF,
				AVM_OPCODE_CHECK_SAT,
				aTraceEC->refExecutionData().getPathTimedCondition());

		aTracePoint->tpid = ++TP_ID;
		aTraceElement->points.append( bfTP );
	}


	if( mTracePointFilter.hasNodeConditionPoint()
		&& aTraceEC->refExecutionData().hasNodeCondition() )
	{
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF,
				AVM_OPCODE_CHECK_SAT,
				aTraceEC->refExecutionData().getNodeCondition());

		aTracePoint->tpid = ++TP_ID;
		aTraceElement->points.append( bfTP );
	}

	if( mTracePointFilter.hasNodeTimedConditionPoint()
		&& aTraceEC->refExecutionData().hasNodeTimedCondition() )
	{
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF,
				AVM_OPCODE_CHECK_SAT,
				aTraceEC->refExecutionData().getNodeTimedCondition());

		aTracePoint->tpid = ++TP_ID;
		aTraceElement->points.append( bfTP );
	}


	if( printInitValuesFlag )
	{
		printInitializationValues();
	}

	avm_size_t stepNumber = 0;
	for( itEC = mTraceCache.begin() ; itEC != endEC ; ++itEC, ++stepNumber )
	{
		const ExecutionData & anED = (*itEC)->refExecutionData();

		// BEGIN STEP
		if( mStepBeginSeparatorFlag )
		{
			bfTP = aTracePoint = new TracePoint(*( *itEC ),
					ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE,
					to_string(stepNumber) );
			aTraceElement->points.append( bfTP );
		}


		// the STEP
		if( mTracePointFilter.hasAssignPoint() )
		{
			buildTraceVariable(*( *itEC ), aTraceElement, stepNumber > 0);
		}

		if( mTracePointFilter.hasRunnablePoint() )
		{
			buildTraceRunnable(*( *itEC ), aTraceElement,
					anED.getRunnableElementTrace());
		}

		if( mTracePointFilter.hasIOTracePoint() )
		{
			buildTraceIO(*( *itEC ), aTraceElement, anED.getIOElementTrace());
		}


		// END STEP
		if( mStepEndSeparatorFlag )
		{
			bfTP = aTracePoint = new TracePoint(*( *itEC ),
					ENUM_TRACE_POINT::TRACE_STEP_END_NATURE,
					to_string(stepNumber) );
			aTraceElement->points.append( bfTP );
		}
	}

	mTraceManager->reduce( aTraceElement );
}


void BasicTraceBuilder::buildTraceVariable(
		const ExecutionContext & anEC, TraceSequence * aTraceElt, bool isnotRoot)
{
	const ExecutionData & anED = anEC.refExecutionData();

	TableOfInstanceOfData::const_raw_iterator itVariable;
	TableOfInstanceOfData::const_raw_iterator endVariable;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = NULL;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasData() )
		{
			itVariable = pRF->getExecutable()->getAllData().begin();
			endVariable = pRF->getExecutable()->getAllData().end();
			for( ; itVariable != endVariable ; ++itVariable )
			{
				if( mDataSelectionModifiedFlags && isnotRoot )
				{
					if( not anED.isAssigned(
							pRF->getRID(), itVariable->getOffset()) )
					{
						continue;
					}
				}

				if( mTracePointFilter.pass(pRF->getRID(),
						static_cast< InstanceOfData * >(itVariable)) )
				{
					bfTP = aTracePoint = new TracePoint(anEC,
							ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
							AVM_OPCODE_ASSIGN, pRF->getInstance(),
							itVariable, pRF->getDataTable()->get(itVariable));

					aTracePoint->RID = pRF->getRID();
					aTracePoint->tpid = ++TP_ID;
					aTraceElt->points.append( bfTP );
				}
			}
		}
	}
}


void BasicTraceBuilder::buildTraceIO(const ExecutionContext & anEC,
		TraceSequence * aTraceElt, const BF & ioTrace)
{
	if( ioTrace.invalid() )
	{
		return;
	}
	else if( ioTrace.is< ExecutionConfiguration >() )
	{
		ExecutionConfiguration * aConf =
				ioTrace.to_ptr< ExecutionConfiguration >();

		object = mTracePointFilter.objectDeltaTime;

		if( aConf->isAvmCode() )
		{
			AvmCode * aCode = aConf->getAvmCode();

			aTracePoint = NULL;

			switch( aCode->getAvmOpCode() )
			{
				case AVM_OPCODE_ASSIGN_NEWFRESH:
				{
					object = aCode->first().to_ptr< BaseInstanceForm >();
					value = aCode->second();

					if( object == mTracePointFilter.objectDeltaTime )
					{
						bfTP = aTracePoint = new TracePoint(anEC, aConf,
								ENUM_TRACE_POINT::TRACE_TIME_NATURE,
								AVM_OPCODE_TIMED_GUARD,
								aConf->getRuntimeID().getInstance(),
								object, value);
					}
					else
					{
						bfTP = aTracePoint = new TracePoint(anEC,
								aConf, aConf->getRuntimeID(), object, value);
					}

					break;
				}

				case AVM_OPCODE_INPUT:

//				case AVM_OPCODE_INPUT_FROM:
//
//				case AVM_OPCODE_INPUT_SAVE:
//
//				// Optimized version of INPUT
//				case AVM_OPCODE_INPUT_ENV:
//				case AVM_OPCODE_INPUT_VAR:
//				case AVM_OPCODE_INPUT_FLOW:
//				case AVM_OPCODE_INPUT_BUFFER:
//				case AVM_OPCODE_INPUT_RDV:
//				case AVM_OPCODE_INPUT_MULTI_RDV:
//				case AVM_OPCODE_INPUT_BROADCAST:
//				case AVM_OPCODE_INPUT_DELEGATE:

				case AVM_OPCODE_OUTPUT:

//				case AVM_OPCODE_OUTPUT_TO:
//				// Optimized version of OUTPUT
//				case AVM_OPCODE_OUTPUT_ENV:
//				case AVM_OPCODE_OUTPUT_VAR:
//				case AVM_OPCODE_OUTPUT_FLOW:
//				case AVM_OPCODE_OUTPUT_BUFFER:
//				case AVM_OPCODE_OUTPUT_RDV:
//				case AVM_OPCODE_OUTPUT_MULTI_RDV:
//				case AVM_OPCODE_OUTPUT_BROADCAST:
//				case AVM_OPCODE_OUTPUT_DELEGATE:

				default:
				{
					if( aCode->first().is< BaseInstanceForm >() )
					{
						object = aCode->first().to_ptr< BaseInstanceForm >();
						value = BF::REF_NULL;

						if( aCode->populated() )
						{
							if( aCode->size() >= 3  )
							{
								ArrayBF * values = new ArrayBF(
										TypeManager::UNIVERSAL,
										aCode->size() - (isSDLFlag? 2 : 1) );
								value.setPointer(values);

								AvmCode::const_iterator it = aCode->begin();
								AvmCode::const_iterator endIt = aCode->end();
								if( isSDLFlag )
								{
									--endIt;
								}
								avm_size_t offset = 0;
								for( ++it; it != endIt ; ++offset , ++it )
								{
									values->set(offset, (*it));
								}
							}
							else if( not isSDLFlag )
							{
								ArrayBF * values = new ArrayBF(
										TypeManager::UNIVERSAL, 1);
								value.setPointer(values);

								values->set(0, aCode->second());
							}
						}

						RuntimeID ridContainer = aConf->getRuntimeID();

						if( object->is< InstanceOfPort >() )
						{
							ridContainer = aConf->getRuntimeID().getCommunicator(
									object->to< InstanceOfPort >());

							if( ridContainer.invalid() )
							{
								ridContainer = aConf->getRuntimeID();
							}
						}

						bfTP = aTracePoint = new TracePoint(anEC, aConf,
								ridContainer, object, value);
					}
					break;
				}
			}

			if( mTracePointFilter.pass(aTracePoint) )
			{
				aTracePoint->tpid = ++TP_ID;
				aTraceElt->points.append( bfTP );
			}
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		AvmCode * ioCode = ioTrace.to_ptr< AvmCode >();

		TraceSequence * subTrace = aTraceElt;
		BF bfSubTrace;
		if( not ioCode->isOpCode(aTraceElt->combinator) )
		{
			bfSubTrace = subTrace =
					new TraceSequence(aTraceElt, ioCode->getOperator());
		}

		AvmCode::const_iterator it = ioCode->begin();
		AvmCode::const_iterator endCode = ioCode->end();
		for( ; it != endCode ; ++it )
		{
			buildTraceIO(anEC, subTrace, (*it));
		}

		if( (subTrace != aTraceElt) )
		{
			if( subTrace->points.singleton() )
			{
				aTraceElt->points.append( subTrace->points.pop_last() );
			}
			else if( subTrace->points.nonempty() )
			{
				aTraceElt->points.append( bfSubTrace );
			}
		}
	}
}


void BasicTraceBuilder::buildTraceRunnable(const ExecutionContext & anEC,
		TraceSequence * aTraceElt, const BF & aTrace)
{
	if( aTrace.invalid() )
	{
		return;
	}
	else if( aTrace.is< ExecutionConfiguration >() )
	{
		ExecutionConfiguration * aConf =
				aTrace.to_ptr< ExecutionConfiguration >();

		aTracePoint = NULL;

		if( aConf->isAvmCode() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE,
					aConf->getAvmOpCode(),
					aConf->getRuntimeID().getInstance(),
					NULL, aConf->getCode());
		}

		else if( aConf->isTransition() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
					AVM_OPCODE_INVOKE_TRANSITION,
					aConf->getRuntimeID().getInstance(),
					aConf->getTransition());
		}

		else if( aConf->isRoutine() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE,
					AVM_OPCODE_NULL, //AVM_OPCODE_INVOKE_ROUTINE,
					aConf->getRuntimeID().getInstance(), aConf->getProgram());
		}

		else if( aConf->isRunnable() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE, AVM_OPCODE_RUN,
					aConf->getRuntimeID().getInstance(), aConf->getProgram());
		}

		else if( aConf->isOperator() )
		{
			Operator * anOperator = aConf->getOperator();

			switch( anOperator->getAvmOpCode() )
			{
				case AVM_OPCODE_RUN:
				case AVM_OPCODE_IRUN:
				case AVM_OPCODE_START:
				{
					RuntimeID ridContainer =
							aConf->getRuntimeID().hasParent()
									? aConf->getRuntimeID().getParent()
									: aConf->getRuntimeID();

					bfTP = aTracePoint = new TracePoint(anEC, aConf,
							ENUM_TRACE_POINT::TRACE_MACHINE_NATURE,
							AVM_OPCODE_RUN, ridContainer,
							aConf->getRuntimeID().getInstance());

					break;
				}

				default:
				{
					bfTP = aTracePoint = new TracePoint(anEC, aConf,
							ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE,
							anOperator->getAvmOpCode(),
							aConf->getRuntimeID().getInstance(),
							& ( aConf->getRuntimeID().getExecutable()->
								getOnActivityRoutine(
										anOperator->getAvmOpCode()) ) );

					break;
				}
			}
		}

		if( mTracePointFilter.pass(aTracePoint) )
		{
			aTracePoint->tpid = ++TP_ID;
			aTraceElt->points.append( bfTP );
		}
	}
	else if( aTrace.is< AvmCode >() )
	{
		AvmCode * ioCode = aTrace.to_ptr< AvmCode >();

		TraceSequence * subTrace = aTraceElt;
		BF bfSubTrace;
		if( not ioCode->isOpCode(aTraceElt->combinator) )
		{
			bfSubTrace = subTrace =
					new TraceSequence(aTraceElt, ioCode->getOperator());
		}

		AvmCode::const_iterator it = ioCode->begin();
		AvmCode::const_iterator endCode = ioCode->end();
		for( ; it != endCode ; ++it )
		{
			buildTraceRunnable(anEC, subTrace, (*it));
		}

		if( (subTrace != aTraceElt) )
		{
			if( subTrace->points.singleton() )
			{
				aTraceElt->points.append( subTrace->points.pop_last() );
			}
			else if( subTrace->points.nonempty() )
			{
				aTraceElt->points.append( bfSubTrace );
			}
		}
	}
}


void BasicTraceBuilder::printInitializationValues()
{
	// !!!!!!!!!!!!!! Modif du 07/02/14 pour avoir les InitializationValues !!!!!!!!!!!!!!

	bool atLeastOneInitialization = false;

	TableOfInstanceOfData thePCVariableVector;
	InstanceOfData * theVariable;

	RuntimeID theRID = aTraceEC->refExecutionData().getParametersRID();
	InstanceOfMachine * theMachine = theRID.getInstance();

	ExpressionFactory::collectVariable(
			aTraceEC->refExecutionData().getPathCondition(),
			thePCVariableVector);

	// Initialization beginning marker"
	bfTP = aTracePoint = new TracePoint((* aTraceEC),
			ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE,
			to_string(aTraceElement->tid));
	aTraceElement->points.append( bfTP );

	for (avm_size_t k = 0 ; k < thePCVariableVector.size() ; k ++)
	{
		theVariable = thePCVariableVector.rawAt( k );

		std::string varName = theVariable->getFullyQualifiedNameID();
		std::string::size_type index = varName.find_last_of('#');
		if( (index != std::string::npos) && (varName[index+1] == '0') )
		{
			atLeastOneInitialization = true;

			bfTP = aTracePoint = new TracePoint((* aTraceEC), NULL,
					ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
					AVM_OPCODE_ASSIGN,
					theMachine, 	// instance de sa machine, NULL si on ne l'affiche pas
					theVariable, 	// instance de la variable
					thePCVariableVector[ k ]);	// sa valeur dans l'EC

			aTracePoint->RID = aTraceEC->refExecutionData().getParametersRID();

			// Ajout dans la trace courante
			aTraceElement->points.append( bfTP );
		}
	}

	if( atLeastOneInitialization )
	{
		// Affichage saut de ligne pour séparer les "Initialization values" du scénario
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_INIT_END_NATURE,
				to_string(aTraceElement->tid));
		aTraceElement->points.append( bfTP );
	}
	else
	{
		// Remove initialization beginning marker"
		aTraceElement->points.remove_last();
	}
}



} /* namespace sep */
