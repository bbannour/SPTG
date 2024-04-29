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

#include <fml/common/ObjectElement.h>

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

#include  <famcore/trace/AvmTraceGenerator.h>
#include  <famcore/trace/TraceManager.h>

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

isLeafAtHeaderPositionFlag (true),

pathSelectionVerdict( ExecutionContextFlags::FAM_UNDEFINED_VERDICT ),

mTraceManager( nullptr ),
mSolverKind( aSolverKind ),
mTracePointFilter(  aTracePointFilter ),

////////////////////////////////////////////////////////////////////////////
// Computing Variables
aTraceSequence( nullptr ),
aTracePoint( nullptr ),
bfTP( ),
TP_ID( 0 ),

mTraceCache( ),
aRootEC( nullptr ),
aTraceEC( nullptr ),
itEC( ),
endEC( ),

code( ),
object( nullptr ),
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
bool BasicTraceBuilder::configureImpl(const WObject * wfParameterObject)
{
	const WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string format = Query::getWPropertyString(
				thePROPERTY, "format", "BASIC#XLIA");
		isSDLFlag = ( format.find("SDL") != std::string::npos );

		printInitValuesFlag = Query::getRegexWPropertyBoolean(thePROPERTY,
				CONS_WID2("show", "initialization") "|"
				CONS_WID3("print", "initial", "values"), false);

		isLeafAtHeaderPositionFlag = Query::getRegexWPropertyBoolean(thePROPERTY,
				CONS_WID3("leaf", "header", "position"), true);

		std::string pathSelection = Query::getRegexWPropertyString(thePROPERTY,
				CONS_WID3("path", "selection", "verdict"), "FAM_UNDEFINED_VERDICT");
		if ( pathSelection == "PASS" )
		{
			pathSelectionVerdict = ExecutionContextFlags::FAM_OBJECTIVE_ACHIEVED_VERDICT;
		}
	}
	else
	{
		isSDLFlag = false;
		printInitValuesFlag = false;
		isLeafAtHeaderPositionFlag = true;
		pathSelectionVerdict = ExecutionContextFlags::FAM_UNDEFINED_VERDICT;
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// CONSTRUCTION API
////////////////////////////////////////////////////////////////////////////////

void BasicTraceBuilder::build(
		TraceManager & aTraceManager, const ListOfExecutionContext & rootECs)
{
	mTraceManager = (& aTraceManager);

//	updateFlags();

	// Collect and Compute all TraceSequence
	for( const auto & itEC : rootECs )
	{
		build( *itEC );
	}
}


void BasicTraceBuilder::build(const ExecutionContext & anEC)
{
	mTraceCache.push_back( & anEC );

	if( anEC.isLeafNode() && (pathCount < pathCountLimit) )
	{
		if ( (pathSelectionVerdict != ExecutionContextFlags::FAM_UNDEFINED_VERDICT)
			&& anEC.getFlags().hasAnalysisTrace(pathSelectionVerdict) )
		{
			buildTrace();

//			if( SolverFactory::isStrongSatisfiable(mSolverKind,
//					anEC.getExecutionData().getAllPathCondition()) )
//			{
//					buildTrace();
//			}
		}
		else if ( pathSelectionVerdict == ExecutionContextFlags::FAM_UNDEFINED_VERDICT )
		{
			if( SolverFactory::isStrongSatisfiable(mSolverKind,
					anEC.getExecutionData().getAllPathCondition()) )
			{
				buildTrace();
			}
			else
			{
AVM_IF_DEBUG_FLAG2( PROCESSOR , TRACE )
	AVM_OS_TRACE << std::endl
			<< "BasicTraceBuilder::build:> Unsatisfiable PC << "
			<< anEC.getExecutionData().getAllPathCondition().str()
			<< " >> with solver << " << SolverDef::strSolver( mSolverKind )
			<< " >> for the EC:" << std::endl;
	anEC.traceDefault( AVM_OS_TRACE );
	anEC.getExecutionData().toStreamData( AVM_OS_TRACE );
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( PROCESSOR , TRACE )
			}
		}
	}
	else
	{
		for( const auto & itChildEC : anEC.getChildContexts() )
		{
			build( *itChildEC );

			mTraceCache.pop_back();
		}
	}
}


void BasicTraceBuilder::buildTrace()
{
	// Incrementation of pathCount
	pathCount += 1;

	// La tête du chemin
	aRootEC = mTraceCache.front();
	// la queue du chemin
	aTraceEC = mTraceCache.back();

	aTraceSequence = new TraceSequence(aTraceEC, mTraceManager->newTID());
	mTraceManager->append( aTraceSequence );

	endEC = mTraceCache.end();

	// LEAF HEADER POSITION
	if ( isLeafAtHeaderPositionFlag )
	{
		buildTraceLeaf();
	}

	if( printInitValuesFlag )
	{
		printInitializationValues();
	}

	std::size_t stepNumber = 0;
	for( itEC = mTraceCache.begin() ; itEC != endEC ; ++itEC, ++stepNumber )
	{
		const ExecutionData & anED = (*itEC)->getExecutionData();

		if( (*itEC)->isRoot() )
		{
			stepNumber = 0;
		}

		// STEP HEADER
		if( mTracePointFilter.hasStepHeaderSeparator() )
		{
			bfTP = aTracePoint = new TracePoint(*( *itEC ),
					ENUM_TRACE_POINT::TRACE_STEP_HEADER_NATURE,
					to_string(stepNumber) );
			aTraceSequence->points.append( bfTP );
		}

		// BEGIN STEP
		if( mTracePointFilter.hasStepBeginSeparator() )
		{
			bfTP = aTracePoint = new TracePoint(*( *itEC ),
					ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE,
					to_string(stepNumber) );
			aTraceSequence->points.append( bfTP );
		}

		// LEAF EXECUTION INFORMATION
		if( mTracePointFilter.hasExecutionInformationPoint()
			&& (*itEC)->hasInfo() )
		{
			buildTraceInformation(*( *itEC ), aTraceSequence);
		}

		// ANY CONDITION PRINT BEFORE STATEMENT
//		if( mTracePointFilter.anyNodeConditionTracePoint() )
//		{
//			buildTraceNodeCondition(*( *itEC ));
//		}

		// the STEP
		if( mTracePointFilter.hasComBufferPoint() )
		{
			buildTraceBuffer(*( *itEC ), stepNumber > 0);
		}

		if( mTracePointFilter.hasAssignPoint() )
		{
			buildTraceVariable(*( *itEC ), stepNumber > 0);
		}

		if( mTracePointFilter.hasRunnablePoint() )
		{
			buildTraceRunnable(*( *itEC ), aTraceSequence,
					anED.getRunnableElementTrace());
		}

		if( mTracePointFilter.hasIOTracePoint() )
		{
			buildTraceIO(*( *itEC ), aTraceSequence, anED.getIOElementTrace());
		}


		// ANY CONDITION PRINT AFTER STATEMENT
		if( mTracePointFilter.anyNodeConditionTracePoint() )
		{
			buildTraceNodeCondition(*( *itEC ));
		}

		// END STEP
		if( mTracePointFilter.hasStepEndSeparator() )
		{
			bfTP = aTracePoint = new TracePoint(*( *itEC ),
					ENUM_TRACE_POINT::TRACE_STEP_END_NATURE,
					to_string(stepNumber) );
			aTraceSequence->points.append( bfTP );
		}
	}

	// LEAF HEADER POSITION
	if ( not isLeafAtHeaderPositionFlag )
	{
		buildTraceLeaf();
	}

	mTraceManager->reduce( *aTraceSequence );
}

void BasicTraceBuilder::buildTraceLeaf()
{
	// LEAF EXECUTION INFORMATION
	if( mTracePointFilter.hasExecutionInformationPoint()
		&& aTraceEC->hasInfo() )
	{
		buildTraceInformation(* aTraceEC, aTraceSequence);
	}

	// LEAF PATH CONDITION
	if( mTracePointFilter.hasOnlyPathConditionLeafNodePoint()
		&& aTraceEC->getExecutionData().hasPathCondition() )
	{
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF,
				AVM_OPCODE_CHECK_SAT,
				aTraceEC->getExecutionData().getPathCondition());

		aTracePoint->tpid = ++TP_ID;
		aTraceSequence->points.append( bfTP );
	}

	// LEAF PATH TIMED CONDITION
	if( mTracePointFilter.hasOnlyPathTimedConditionLeafNodePoint()
		&& aTraceEC->getExecutionData().hasPathTimedCondition() )
	{
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF,
				AVM_OPCODE_CHECK_SAT,
				aTraceEC->getExecutionData().getPathTimedCondition());

		aTracePoint->tpid = ++TP_ID;
		aTraceSequence->points.append( bfTP );
	}
}

void BasicTraceBuilder::buildTraceNodeCondition(const ExecutionContext & anEC)
{
	// PATH CONDITION
	if( mTracePointFilter.hasPathConditionPoint() )
	{
		buildTraceCondition(anEC,
				ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE,
				anEC.getExecutionData().getPathCondition());
	}

	// PATH TIMED CONDITION
	if( mTracePointFilter.hasPathTimedConditionPoint()  )
	{
		buildTraceCondition(anEC,
				ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE,
				anEC.getExecutionData().getPathTimedCondition());
	}


	// NODE CONDITION
	if( mTracePointFilter.hasNodeConditionPoint() )
	{
		buildTraceCondition(anEC,
				ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE,
				anEC.getExecutionData().getNodeCondition());
	}

	// NODE TIMED CONDITION
	if( mTracePointFilter.hasNodeTimedConditionPoint() )
	{
		buildTraceCondition(anEC,
				ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE,
				anEC.getExecutionData().getNodeTimedCondition());
	}
}

void BasicTraceBuilder::buildTraceCondition(const ExecutionContext & anEC,
		ENUM_TRACE_POINT::TRACE_NATURE aNature, const BF & aCondition)
{
	if( (not mDataSelectionModifiedFlags) || aCondition.isNotEqualTrue() )
	{
		bfTP = aTracePoint = new TracePoint(
				anEC, aNature, AVM_OPCODE_CHECK_SAT, aCondition );

		aTracePoint->tpid = ++TP_ID;
		aTraceSequence->points.append( bfTP );
	}
}


void BasicTraceBuilder::buildTraceBuffer(
		const ExecutionContext & anEC, bool isnotRoot)
{
	const ExecutionData & anED = anEC.getExecutionData();
	const ExecutionData & prevED = ( isnotRoot ?
			anEC.getPrevious()->getExecutionData() : ExecutionData::_NULL_ );

	avm_offset_t endOffset = 0;
	avm_offset_t offset = 0;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = nullptr;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasBuffer() )
		{
			endOffset = pRF->refExecutable().getBuffer().size();
			for( offset = 0 ; offset < endOffset ; ++offset)
			{
				const InstanceOfBuffer & aBuffer =
						pRF->refExecutable().getBuffer().get(offset).asBuffer();

				const BaseBufferForm & aBufferValue = pRF->getBuffer(& aBuffer);

				if( mDataSelectionModifiedFlags && isnotRoot )
				{
					if( aBufferValue.equals( prevED.getRuntime(
							pRF->getRID() ).getBuffer(& aBuffer) ) )
					{
						continue;
					}
				}

				if( mTracePointFilter.pass(pRF->getRID(), aBuffer) )
				{
					bfTP = aTracePoint = new TracePoint(anEC,
							ENUM_TRACE_POINT::TRACE_BUFFER_NATURE,
							AVM_OPCODE_ASSIGN, pRF->getInstance(),
							const_cast<InstanceOfBuffer *>(& aBuffer),
							pRF->getBufferTable().to_sp< BF >(
									aBuffer.getOffset() ) );

					aTracePoint->RID = pRF->getRID();
					aTracePoint->tpid = ++TP_ID;
					aTraceSequence->points.append( bfTP );
				}
			}
		}
	}
}


void BasicTraceBuilder::buildTraceVariable(
		const ExecutionContext & anEC, bool isnotRoot)
{
	const ExecutionData & anED = anEC.getExecutionData();
	const ExecutionData & prevED = ( isnotRoot ?
			anEC.getPrevious()->getExecutionData() : ExecutionData::_NULL_ );

	avm_offset_t endOffset = 0;
	avm_offset_t offset = 0;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = nullptr;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasData() )
		{
			endOffset = pRF->refExecutable().getAllVariables().size();
			for( offset = 0 ; offset < endOffset ; ++offset)
			{
				const InstanceOfData & aVariable =
						pRF->refExecutable().getAllVariables().refAt(offset);

				if( mTracePointFilter.pass(pRF->getRID(), aVariable) )
				{
					const BF & aValue = pRF->getData(& aVariable);

					if( mDataSelectionModifiedFlags && isnotRoot )
					{
//						if( not pRF->isAssigned(aVariable) )
//						if( not anED.isAssigned(pRF->getRID(), aVariable.getOffset()) )
						if( aValue == prevED.getRuntime(
								pRF->getRID()).getData(& aVariable) )
						{
							continue;
						}
					}

					bfTP = aTracePoint = new TracePoint(anEC,
							ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
							AVM_OPCODE_ASSIGN, pRF->getInstance(),
							const_cast<InstanceOfData *>(& aVariable), aValue);

					aTracePoint->RID = pRF->getRID();
					aTracePoint->tpid = ++TP_ID;
					aTraceSequence->points.append( bfTP );
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
		const ExecutionConfiguration & aConf =
				ioTrace.to< ExecutionConfiguration >();

		if( aConf.isAvmCode() )
		{
			const AvmCode & aCode = aConf.toAvmCode();

			aTracePoint = nullptr;

			switch( aCode.getAvmOpCode() )
			{
				case AVM_OPCODE_ASSIGN_RESET:
				{
					return;
				}

				case AVM_OPCODE_ASSIGN_NEWFRESH:
				{
					object = aCode.first().to_ptr< BaseInstanceForm >();
					value = aCode.second();

					if( static_cast< BaseInstanceForm * >(object)->hasTypedTime()
						&& mTracePointFilter.hasTimePoint() )
					{
						bfTP = aTracePoint = new TracePoint(anEC, aConf,
								ENUM_TRACE_POINT::TRACE_TIME_NATURE,
								AVM_OPCODE_TIMED_GUARD,
								aConf.getRuntimeID().getInstance(),
								object, value);
					}
					else
					{
						bfTP = aTracePoint = new TracePoint(anEC,
								aConf, aConf.getRuntimeID(), object, value);
					}

					break;
				}

				case AVM_OPCODE_TRACE:
				{
					if( mTracePointFilter.hasMetaTracePoint() )
					{
						object = aConf.getRuntimeID().getInstance();

						ArrayBF * operands = new ArrayBF(
								TypeManager::UNIVERSAL, aCode.size() );
						value.setPointer(operands);

						std::size_t offset = 0;
						for( const auto & itOperand : aCode.getOperands() )
						{
							operands->set(offset++, itOperand);
						}

						bfTP = aTracePoint = new TracePoint(anEC, aConf,
								ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE,
								AVM_OPCODE_TRACE,
								aConf.getRuntimeID().getInstance(),
								object, value);

						aTracePoint->tpid = ++TP_ID;
						aTraceElt->points.append( bfTP );
					}

					return;
				}
				case AVM_OPCODE_DEBUG:
				{
					if( mTracePointFilter.hasMetaTracePoint() )
					{
						object = aConf.getRuntimeID().getInstance();

						ArrayBF * operands = new ArrayBF(
								TypeManager::UNIVERSAL, aCode.size() );
						value.setPointer(operands);

						std::size_t offset = 0;
						for( const auto & itOperand : aCode.getOperands() )
						{
							operands->set(offset++, itOperand);
						}

						bfTP = aTracePoint = new TracePoint(anEC, aConf,
								ENUM_TRACE_POINT::TRACE_META_DEBUG_NATURE,
								AVM_OPCODE_DEBUG,
								aConf.getRuntimeID().getInstance(),
								object, value);

						aTracePoint->tpid = ++TP_ID;
						aTraceElt->points.append( bfTP );
					}

					return;
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
					if( aCode.first().is< BaseInstanceForm >() )
					{
						object = aCode.first().to_ptr< BaseInstanceForm >();
						value = BF::REF_NULL;

						if( aCode.hasManyOperands() )
						{
							if( aCode.size() >= 3  )
							{
								ArrayBF * values = new ArrayBF(
										TypeManager::UNIVERSAL,
										aCode.size() - (isSDLFlag? 2 : 1) );
								value.setPointer(values);

								AvmCode::const_iterator itOperand = aCode.begin();
								AvmCode::const_iterator endOperand = aCode.end();
								if( isSDLFlag )
								{
									--endOperand;
								}
								std::size_t offset = 0;
								for( ++itOperand ; itOperand != endOperand ;
										++offset , ++itOperand )
								{
									values->set(offset, (*itOperand));
								}
							}
							else if( not isSDLFlag )
							{
								ArrayBF * values = new ArrayBF(
										TypeManager::UNIVERSAL, 1);
								value.setPointer(values);

								values->set(0, aCode.second());
							}
						}

						RuntimeID ridContainer = aConf.getRuntimeID();

//						if( object->is< InstanceOfPort >()
//							&& (not object->to< InstanceOfPort >().isSignal()) )
//						{
//							ridContainer = aConf.getRuntimeID().getCommunicator(
//									object->to< InstanceOfPort >() );
//
//							if( ridContainer.invalid()
//								|| ridContainer.getSpecifier().isComponentSystem())
//							{
//								ridContainer = aConf.getRuntimeID();
//							}
//						}

						bfTP = aTracePoint = new TracePoint(anEC, aConf,
								ridContainer, object, value);
					}
					break;
				}
			}

			if( mTracePointFilter.pass(*aTracePoint) )
			{
				aTracePoint->tpid = ++TP_ID;
				aTraceElt->points.append( bfTP );
			}
		}
	}
	else if( ioTrace.is< AvmCode >() )
	{
		const AvmCode & ioCode = ioTrace.to< AvmCode >();

		TraceSequence * subTrace = aTraceElt;
		BF bfSubTrace;
		if( not ioCode.isOpCode(aTraceElt->combinator) )
		{
			bfSubTrace = subTrace =
					new TraceSequence(aTraceElt, ioCode.getOperator());
		}

		for( const auto & itOperand : ioCode.getOperands() )
		{
			buildTraceIO(anEC, subTrace, itOperand);
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
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		aTracePoint = nullptr;

		if( aConf.isAvmCode() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE,
					aConf.getAvmOpCode(),
					aConf.getRuntimeID().getInstance(),
					nullptr, aConf.getCode());
		}

		else if( aConf.isTransition() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
					AVM_OPCODE_INVOKE_TRANSITION,
					aConf.getRuntimeID().getInstance(),
					aConf.getTransition());
		}

		else if( aConf.isRoutine() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE,
					AVM_OPCODE_NULL, //AVM_OPCODE_INVOKE_ROUTINE,
					aConf.getRuntimeID().getInstance(), aConf.getProgram());
		}

		else if( aConf.isRunnable() )
		{
			bfTP = aTracePoint = new TracePoint(anEC, aConf,
					ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE, AVM_OPCODE_RUN,
					aConf.getRuntimeID().getInstance(), aConf.getProgram());
		}

		else if( aConf.isOperator() )
		{
			const Operator & anOperator = aConf.getOperator();

			switch( anOperator.getAvmOpCode() )
			{
				case AVM_OPCODE_RUN:
				case AVM_OPCODE_IRUN:
				case AVM_OPCODE_START:
				{
					RuntimeID ridContainer =
							aConf.getRuntimeID().hasParent()
									? aConf.getRuntimeID().getParent()
									: aConf.getRuntimeID();

					bfTP = aTracePoint = new TracePoint(anEC, aConf,
							ENUM_TRACE_POINT::TRACE_MACHINE_NATURE,
							AVM_OPCODE_RUN, ridContainer,
							aConf.getRuntimeID().getInstance());

					break;
				}

				default:
				{
					bfTP = aTracePoint = new TracePoint(anEC, aConf,
							ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE,
							anOperator.getAvmOpCode(),
							aConf.getRuntimeID().getInstance(),
							&( aConf.getRuntimeID().refExecutable().
								getOnActivityRoutine(
										anOperator.getAvmOpCode()) ) );

					break;
				}
			}
		}

		if( mTracePointFilter.pass(*aTracePoint) )
		{
			aTracePoint->tpid = ++TP_ID;
			aTraceElt->points.append( bfTP );
		}
	}
	else if( aTrace.is< AvmCode >() )
	{
		const AvmCode & ioCode = aTrace.to< AvmCode >();

		TraceSequence * subTrace = aTraceElt;
		BF bfSubTrace;
		if( not ioCode.isOpCode(aTraceElt->combinator) )
		{
			bfSubTrace = subTrace =
					new TraceSequence(aTraceElt, ioCode.getOperator());
		}

		for( const auto & itOperand : ioCode.getOperands() )
		{
			buildTraceRunnable(anEC, subTrace, itOperand);
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


void BasicTraceBuilder::buildTraceInformation(
		const ExecutionContext & anEC, TraceSequence * aTraceElt)
{
	const BF & firstInfo = anEC.getInfos().first();

	const BF & infoData = ( firstInfo.is< GenericInfoData >() ?
			firstInfo.to< GenericInfoData >().getData() : firstInfo );

	bfTP = aTracePoint = new TracePoint(anEC,
			ENUM_TRACE_POINT::TRACE_EXECUTION_INFORMATION_NATURE,
			AVM_OPCODE_INFORMAL, infoData);

//	if( mTracePointFilter.pass(* aTracePoint, *(anEC.getInformation())) )
	{
		aTracePoint->tpid = ++TP_ID;
		aTraceElt->points.append( bfTP );
	}
}




void BasicTraceBuilder::printInitializationValues()
{
	bool atLeastOneInitialization = false;

	TableOfInstanceOfData thePCVariableVector;
	InstanceOfData * theVariable;

	RuntimeID theRID = aTraceEC->getExecutionData().getParametersRID();
	InstanceOfMachine * theMachine = theRID.getInstance();

	ExpressionFactory::collectVariable(
			aTraceEC->getExecutionData().getPathCondition(),
			thePCVariableVector);

	// Initialization beginning marker"
	bfTP = aTracePoint = new TracePoint((* aTraceEC),
			ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE,
			to_string(aTraceSequence->tid));
	aTraceSequence->points.append( bfTP );

	for (std::size_t k = 0 ; k < thePCVariableVector.size() ; k ++)
	{
		theVariable = thePCVariableVector.rawAt( k );

		std::string varName = theVariable->getFullyQualifiedNameID();
		std::string::size_type index = varName.find_last_of('#');
		if( (index != std::string::npos) && (varName[index+1] == '0') )
		{
			atLeastOneInitialization = true;

			bfTP = aTracePoint = new TracePoint((* aTraceEC),
					ExecutionConfiguration::nullref(),
					ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
					AVM_OPCODE_ASSIGN, theMachine, theVariable,
					thePCVariableVector[ k ]);	// sa valeur dans l'EC

			aTracePoint->RID = aTraceEC->getExecutionData().getParametersRID();

			// Ajout dans la trace courante
			aTraceSequence->points.append( bfTP );
		}
	}

	if( atLeastOneInitialization )
	{
		// Affichage saut de ligne pour séparer les "Initialization values" du scénario
		bfTP = aTracePoint = new TracePoint((* aTraceEC),
				ENUM_TRACE_POINT::TRACE_INIT_END_NATURE,
				to_string(aTraceSequence->tid));
		aTraceSequence->points.append( bfTP );
	}
	else
	{
		// Remove initialization beginning marker"
		aTraceSequence->points.remove_last();
	}
}



} /* namespace sep */
