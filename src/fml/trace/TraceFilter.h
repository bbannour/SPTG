/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRACEFILTER_H_
#define TRACEFILTER_H_

#include <collection/List.h>

#include <fml/common/ObjectElement.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>

#include <fml/operator/OperatorLib.h>

#include <fml/trace/TracePoint.h>


namespace sep
{


class BF;

class AvmTransition;
class EvaluationEnvironment;
class ExecutionConfiguration;
class ExecutionInformation;
class ExecutableSystem;

class InstanceOfData;

class Port;

class TraceFilter final
{

public:
	/**
	 * ATTRIBUTE
	 */
	std::string mNameID;

	AvmCode mainTracePointFiter;

	ListOfTracePoint listOfBufferTracePoint;
	ListOfTracePoint listOfVariableTracePoint;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	InstanceOfData * objectDeltaTime;

protected:

	bool mStepHeaderSeparatorFlag;
	bool mStepBeginSeparatorFlag;
	bool mStepEndSeparatorFlag;

	bool mConditionFlag;
	bool mDecisionFlag;

	bool mPathConditionFlag;
	bool mPathTimedConditionFlag;

	bool mPathConditionLeafNodeFlag;
	bool mPathTimedConditionLeafNodeFlag;

	bool mNodeConditionFlag;
	bool mNodeTimedConditionFlag;

	bool mNodeConditionLeafNodeFlag;
	bool mNodeTimedConditionLeafNodeFlag;

	bool mTimeFilterFlag;
	bool mAssignFilterFlag;
	bool mNewfreshFilterFlag;

	bool mInputEnvFilterFlag;
	bool mInputRdvFilterFlag;

	bool mInputExternalFilterFlag;
	bool mInputInternalFilterFlag;
	bool mInputFilterFlag;

	bool mOutputEnvFilterFlag;
	bool mOutputRdvFilterFlag;

	bool mOutputExternalFilterFlag;
	bool mOutputInternalFilterFlag;
	bool mOutputFilterFlag;

	bool mMachineFilterFlag;
	bool mStateFilterFlag;
	bool mStatemachineFilterFlag;
	bool mTransitionFilterFlag;
	bool mRoutineFilterFlag;

	bool mComExternalFilterFlag;
	bool mComInternalFilterFlag;
	bool mComFilterFlag;
	bool mComBufferFilterFlag;

	bool mMetaInformalFilterFlag;
	bool mMetaTraceFilterFlag;
	bool mMetaDebugFilterFlag;

	bool mIOTraceFilterFlag;
	bool mRunnableFilterFlag;

	bool mExecutionInformationFilterFlag;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceFilter(const std::string & aNameID);

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceFilter()
	{
		//!! NOTHING
	}


	/**
	 * [RE]SET TracePoint ID
	 */
	void resetTracePointID();
	void resetTracePointID(BF & point);

	void setTracePointID(std::size_t intialTPID = 0);
	void setTracePointID(BF & point, std::size_t & intialTPID);



	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(EvaluationEnvironment & ENV,
			const WObject * wfParameterObject, const WObject * wfTraceObject);

	bool configure(EvaluationEnvironment & ENV,
			const WObject * wfParameterObject,
			const std::string & aWSequenceNameID,
			const std::string & aWSequenceElseNameID);

	inline bool configure(
			EvaluationEnvironment & ENV, const WObject * wfParameterObject)
	{
		return( configure(ENV, wfParameterObject, "trace", "TRACE") );
	}


	inline bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE op)
	{
		return( mainTracePointFiter.noOperand()
				|| ( (op == AVM_OPCODE_NULL)
					&& (nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) )
				|| contains(nature, op, mainTracePointFiter) );
	}

	inline bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature)
	{
		return( mainTracePointFiter.noOperand() ||
				(nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) ||
				contains(nature, AVM_OPCODE_NULL, mainTracePointFiter) );
	}

	inline bool contains(AVM_OPCODE op)
	{
		return( contains(ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE, op) );
	}

	inline bool containsOr(AVM_OPCODE op1, AVM_OPCODE op2)
	{
		return( contains(ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE, op1) ||
				contains(ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE, op2) );
	}

	inline bool containsCom()
	{
		return( contains(ENUM_TRACE_POINT::TRACE_COM_NATURE    ) ||
				contains(ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE) ||
				contains(ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE) ||
				contains(ENUM_TRACE_POINT::TRACE_PORT_NATURE   ) ||
				contains(ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE )  );
	}

	bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature,
			AVM_OPCODE op, const AvmCode & aCode) const;

	bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature,
			AVM_OPCODE op, const BF & arg) const;


	/**
	 * Update
	 * Filter Point Flags
	 */
//	void updateFilterFlags();


	inline bool hasStepHeaderSeparator() const
	{
		return( mStepHeaderSeparatorFlag );
	}

	inline bool hasStepBeginSeparator() const
	{
		return( mStepBeginSeparatorFlag );
	}

	inline bool hasStepEndSeparator() const
	{
		return( mStepEndSeparatorFlag );
	}

	inline void pairwiseStepBeginEndSeparator()
	{
		if( mStepBeginSeparatorFlag || mStepEndSeparatorFlag ) {
			mStepBeginSeparatorFlag = mStepEndSeparatorFlag = true;
		}
	}



	inline bool hasConditionPoint() const
	{
		return( mConditionFlag );
	}

	inline bool hasDecisionPoint() const
	{
		return( mDecisionFlag );
	}


	inline bool hasPathConditionPoint() const
	{
		return( mPathConditionFlag );
	}

	inline bool hasPathTimedConditionPoint() const
	{
		return( mPathTimedConditionFlag );
	}


	inline bool hasPathConditionLeafNodePoint() const
	{
		return( mPathConditionLeafNodeFlag );
	}

	inline bool hasOnlyPathConditionLeafNodePoint() const
	{
		return( mPathConditionLeafNodeFlag && (not mPathConditionFlag) );
	}

	inline bool hasPathTimedConditionLeafNodePoint() const
	{
		return( mPathTimedConditionLeafNodeFlag );
	}

	inline bool hasOnlyPathTimedConditionLeafNodePoint() const
	{
		return( mPathTimedConditionLeafNodeFlag && (not mPathTimedConditionFlag) );
	}


	inline bool hasPathConditionTracePoint() const
	{
		return( mPathConditionFlag || mPathConditionLeafNodeFlag );
	}

	inline bool hasPathTimedConditionTracePoint() const
	{
		return( mPathTimedConditionFlag || mPathTimedConditionLeafNodeFlag );
	}


	inline bool anyNodeConditionTracePoint() const
	{
		return( mPathConditionFlag || mPathTimedConditionFlag
			 || mNodeConditionFlag || mNodeTimedConditionFlag );
	}


	inline bool hasNodeConditionPoint() const
	{
		return( mNodeConditionFlag );
	}

	inline bool hasNodeTimedConditionPoint() const
	{
		return( mNodeTimedConditionFlag );
	}

	inline bool hasNodeConditionTracePoint() const
	{
		return( mNodeConditionFlag || mNodeTimedConditionFlag );
	}


	inline bool hasTimePoint() const
	{
		return( mTimeFilterFlag );
	}

	inline bool hasAssignPoint() const
	{
		return( mAssignFilterFlag );
	}

	inline void addAnyAssignFilter()
	{
		mAssignFilterFlag = true;

		TracePoint * aTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
				AVM_OPCODE_ASSIGN, true);

		mainTracePointFiter.append( BF(aTracePoint) );

		listOfVariableTracePoint.append( aTracePoint );
	}


	inline bool hasNewfreshPoint() const
	{
		return( mNewfreshFilterFlag );
	}


	inline bool hasInputEnvPoint() const
	{
		return( mInputEnvFilterFlag );
	}

	inline bool hasInputRdvPoint() const
	{
		return( mInputRdvFilterFlag );
	}

	inline bool hasInputPoint() const
	{
		return( mInputFilterFlag );
	}


	inline bool hasOutputEnvPoint() const
	{
		return( mOutputEnvFilterFlag );
	}

	inline bool hasOutputRdvPoint() const
	{
		return( mOutputRdvFilterFlag );
	}

	inline bool hasOutputPoint() const
	{
		return( mOutputFilterFlag );
	}


	inline bool hasMachinePoint() const
	{
		return( mMachineFilterFlag );
	}

	inline bool hasStatePoint() const
	{
		return( mStateFilterFlag );
	}

	inline bool hasStatemachinePoint() const
	{
		return( mStatemachineFilterFlag );
	}


	inline bool hasTransitionPoint() const
	{
		return( mTransitionFilterFlag );
	}

	inline void setEnabledTransitionFilter(bool enabled = true)
	{
		mTransitionFilterFlag = enabled;

		resetRunnablePoint();
	}

	inline void addAnyTransitionFilter()
	{
		setEnabledTransitionFilter( true );

		mainTracePointFiter.append( BF(new TracePoint(
				ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
				AVM_OPCODE_INVOKE_TRANSITION, true)) );
	}


	inline bool hasRoutinePoint() const
	{
		return( mRoutineFilterFlag );
	}


	inline bool hasComPoint() const
	{
		return( mComFilterFlag );
	}

	inline void setEnabledComFilter(bool enabled = true)
	{
		mComFilterFlag = enabled;

		mInputFilterFlag  = enabled;
		mInputExternalFilterFlag  = mInputEnvFilterFlag  = enabled;
		mInputInternalFilterFlag  = mInputRdvFilterFlag  = enabled;

		mOutputFilterFlag = enabled;
		mOutputExternalFilterFlag = mOutputEnvFilterFlag = enabled;
		mOutputInternalFilterFlag = mOutputRdvFilterFlag = enabled;

		resetIOTracePoint();
	}

	inline void addAnyComFilter()
	{
		setEnabledComFilter(true);

		mainTracePointFiter.append( BF(new TracePoint(
				ENUM_TRACE_POINT::TRACE_COM_NATURE,
				AVM_OPCODE_NULL, true)) );
	}


	inline bool hasComBufferPoint() const
	{
		return( mComBufferFilterFlag );
	}

	inline void addAnyComBufferFilter()
	{
		mComBufferFilterFlag = true;

		TracePoint * aTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_BUFFER_NATURE,
				AVM_OPCODE_NULL, true);

		mainTracePointFiter.append( BF(aTracePoint) );

		listOfBufferTracePoint.append( aTracePoint );
	}


	inline bool hasMetaTracePoint() const
	{
		return( mMetaTraceFilterFlag );
	}

	inline bool hasMetaDebugPoint() const
	{
		return( mMetaDebugFilterFlag );
	}


	inline bool hasMetaPoint() const
	{
		return( mMetaTraceFilterFlag | mMetaDebugFilterFlag );
	}


	inline bool hasIOTracePoint() const
	{
		return( mIOTraceFilterFlag || hasMetaPoint() );
	}

	inline void resetIOTracePoint()
	{
		mIOTraceFilterFlag = mComFilterFlag || mNewfreshFilterFlag;

	}


	inline bool hasRunnablePoint() const
	{
		return( mRunnableFilterFlag );
	}

	inline void resetRunnablePoint()
	{
		mRunnableFilterFlag = mMachineFilterFlag
				|| mStateFilterFlag      || mStatemachineFilterFlag
				|| mTransitionFilterFlag || mRoutineFilterFlag;
	}

	inline bool hasExecutionInformationPoint() const
	{
		return( mExecutionInformationFilterFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API: check if a generic reference Element pass
	////////////////////////////////////////////////////////////////////////////

	template< class T > bool pass(const T & anElement) const
	{
	AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
		AVM_OS_TRACE << std::endl;
		AVM_OS_TRACE << "candidat :> " << anElement.str() << std::endl;
		AVM_OS_TRACE << "filterTP :>" << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

		return( pass(mainTracePointFiter, anElement) );
	}

	template< class T > bool pass(const BF & filterArg, const T & anElement) const
	{
		if( filterArg.is< TracePoint >() )
		{
			const TracePoint & filterTP = filterArg.to< TracePoint >();
			if( filterTP.isComposite() )
			{
				return( passComposite(filterTP, anElement) );
			}
			else
			{
				return( pass(filterArg.to< TracePoint >(), anElement) );
			}
		}

		else if( filterArg.is< AvmCode >() )
		{
			return( pass(filterArg.to< AvmCode >(), anElement) );
		}
		return( false );
	}

	template< class T > bool passComposite(
			const TracePoint & filterTP, const T & anElement) const
	{
		const auto & anArray = filterTP.value.to< ArrayBF >();

		switch( filterTP.op )
		{
			case AVM_OPCODE_AND:
			{
				std::size_t endOffset = anArray.size();
				for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
				{
					if( not pass(anArray[offset], anElement) )
					{
						return( false );
					}
				}

				return( true );
			}

			case AVM_OPCODE_OR:
			{
				std::size_t endOffset = anArray.size();
				for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
				{
					if( pass(anArray[offset], anElement) )
					{
						return( true );
					}
				}

				return( false );
			}

			case AVM_OPCODE_XOR:
			{
				std::size_t passCount = 0;

				std::size_t endOffset = anArray.size();
				for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
				{
					if( pass(anArray[offset], anElement) )
					{
						if( ++passCount > 1 )
						{
							return( false );
						}
					}
				}

				return( passCount == 1 );
			}

			case AVM_OPCODE_NOT:
			{
				return( not pass(anArray[0], anElement) );
			}

			default:
			{
				return( false );
			}
		}
	}




	template< class T > bool pass(
			const AvmCode & filterCode, const T & anElement) const
	{
		switch( filterCode.getAvmOpCode() )
		{
			case AVM_OPCODE_AND:
			{
				for( const auto & itOperand : filterCode.getOperands() )
				{
					if( not pass(itOperand, anElement) )
					{
						return( false );
					}
				}

				return( true );
			}

			case AVM_OPCODE_OR:
			{
				for( const auto & itOperand : filterCode.getOperands() )
				{
					if( pass(itOperand, anElement) )
					{
						return( true );
					}
				}

				return( false );
			}

			case AVM_OPCODE_XOR:
			{
				std::size_t passCount = 0;

				for( const auto & itOperand : filterCode.getOperands() )
				{
					if( pass(itOperand, anElement) )
					{
						if( ++passCount > 1 )
						{
							return( false );
						}
					}
				}

				return( passCount == 1 );
			}

			case AVM_OPCODE_NOT:
			{
				return( not pass(filterCode.first(), anElement) );
			}

			default:
			{
				return( false );
			}
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if TRACE POINT pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP, const TracePoint & aTP) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if TRANSITION pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP, const AvmTransition & aTransition) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if BUFFER pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const RuntimeID & aRID, const InstanceOfBuffer & aBuffer) const;

	bool pass(const TracePoint & filterTP,
			const RuntimeID & aRID, const InstanceOfBuffer & aBuffer) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if VARIABLE pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const RuntimeID & aRID, const InstanceOfData & aVariable) const;

	bool pass(const TracePoint & filterTP,
			const RuntimeID & aRID, const InstanceOfData & aVariable) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if Execution Trace
	// a.k.a. ExecutionConfiguration pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP,
			const ExecutionConfiguration & anExecConfTP) const;


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if a Compiled Element pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP, const ObjectElement & anElement) const;

	bool pass(const TracePoint & filterTP,
			const RuntimeID & aRID, const ObjectElement & anElement) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if an AST Element pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP, const Port & aPort) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if a Runtime Machine ID pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP, const RuntimeID & aRID) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if AVM CODE pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP, const AvmCode & aCodeTP) const;

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if Execution Information pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const TracePoint & filterTP,
			const ExecutionInformation & anExecInfoTP) const;

	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const;

};



} /* namespace sep */

#endif /* TRACEFILTER_H_ */
