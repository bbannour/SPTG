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

#include <fml/expression/AvmCode.h>

#include <fml/operator/OperatorLib.h>

#include <fml/trace/TracePoint.h>


namespace sep
{


class BF;

class EvaluationEnvironment;
class ExecutionConfiguration;
class ExecutableSystem;


class InstanceOfData;

class TraceFilter
{

public:
	/**
	 * ATTRIBUTE
	 */
	AvmCode mainTracePointFiter;

	ListOfTracePoint listOfVariableTracePoint;

	InstanceOfData * objectDeltaTime;

protected:

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

	bool mIOTraceFilterFlag;
	bool mRunnableFilterFlag;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceFilter()
	: mainTracePointFiter( ),
	listOfVariableTracePoint( ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	objectDeltaTime( NULL ),

	mConditionFlag( false ),
	mDecisionFlag( false ),

	mPathConditionFlag( false ),
	mPathTimedConditionFlag( false ),

	mPathConditionLeafNodeFlag( false ),
	mPathTimedConditionLeafNodeFlag( false ),

	mNodeConditionFlag( false ),
	mNodeTimedConditionFlag( false ),

	mNodeConditionLeafNodeFlag( false ),
	mNodeTimedConditionLeafNodeFlag( false ),

	mTimeFilterFlag( false ),
	mAssignFilterFlag( false ),
	mNewfreshFilterFlag( false ),

	mInputEnvFilterFlag( false ),
	mInputRdvFilterFlag( false ),

	mInputExternalFilterFlag( false ),
	mInputInternalFilterFlag( false ),
	mInputFilterFlag( false ),

	mOutputEnvFilterFlag( false ),
	mOutputRdvFilterFlag( false ),

	mOutputExternalFilterFlag( false ),
	mOutputInternalFilterFlag( false ),
	mOutputFilterFlag( false ),

	mMachineFilterFlag( false ),
	mStateFilterFlag( false ),
	mStatemachineFilterFlag( false ),
	mTransitionFilterFlag( false ),
	mRoutineFilterFlag( false ),

	mComExternalFilterFlag( false ),
	mComInternalFilterFlag( false ),
	mComFilterFlag( false ),

	mIOTraceFilterFlag( false ),
	mRunnableFilterFlag( false )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceFilter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(EvaluationEnvironment & ENV,
			WObject * wfParameterObject, WObject * wfTraceObject);

	bool configure(EvaluationEnvironment & ENV, WObject * wfParameterObject,
			const std::string & aWSequenceNameID,
			const std::string & aWSequenceElseNameID);

	inline bool configure(
			EvaluationEnvironment & ENV, WObject * wfParameterObject)
	{
		return( configure(ENV, wfParameterObject, "trace", "TRACE") );
	}


	inline bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE op)
	{
		return( mainTracePointFiter.empty()
				|| ( (op == AVM_OPCODE_NULL)
					&& (nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) )
				|| contains(nature, op, & mainTracePointFiter) );
	}

	inline bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature)
	{
		return( mainTracePointFiter.empty() ||
				(nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) ||
				contains(nature, AVM_OPCODE_NULL, & mainTracePointFiter) );
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
			AVM_OPCODE op, AvmCode * aCode) const;

	bool contains(ENUM_TRACE_POINT::TRACE_NATURE nature,
			AVM_OPCODE op, const BF & arg) const;


	/**
	 * Update
	 * Filter Point Flags
	 */
//	void updateFilterFlags();


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

	inline bool hasPathTimedConditionLeafNodePoint() const
	{
		return( mPathTimedConditionLeafNodeFlag );
	}


	inline bool hasPathConditionTracePoint() const
	{
		return( mPathConditionFlag || mPathConditionLeafNodeFlag );
	}

	inline bool hasPathTimedConditionTracePoint() const
	{
		return( mPathTimedConditionFlag || mPathTimedConditionLeafNodeFlag );
	}


	inline bool hasNodeConditionPoint() const
	{
		return( mNodeConditionFlag );
	}

	inline bool hasNodeTimedConditionPoint() const
	{
		return( mNodeTimedConditionFlag );
	}


	inline bool hasTimePoint() const
	{
		return( mTimeFilterFlag );
	}

	inline bool hasAssignPoint() const
	{
		return( mAssignFilterFlag );
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

	inline bool hasRoutinePoint() const
	{
		return( mRoutineFilterFlag );
	}


	inline bool hasComPoint() const
	{
		return( mComFilterFlag );
	}

	inline bool hasIOTracePoint() const
	{
		return( mIOTraceFilterFlag );
	}

	inline bool hasRunnablePoint() const
	{
		return( mRunnableFilterFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API: check if a generic pointer Element pass
	////////////////////////////////////////////////////////////////////////////

	template< class T > bool pass(T * anElement)
	{
		if( anElement == NULL )
		{
			return( false );
		}


	AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
		AVM_OS_TRACE << std::endl;
		AVM_OS_TRACE << "candidat :> " << anElement->str() << std::endl;
		AVM_OS_TRACE << "filterTP :>" << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

		return( pass(& mainTracePointFiter, anElement) );
	}

	template< class T > bool pass(const BF & filterArg, T * anElement)
	{
		if( filterArg.is< TracePoint >() )
		{
			return( pass(filterArg.to_ptr< TracePoint >(), anElement) );
		}

		else if( filterArg.is< AvmCode >() )
		{
			return( pass(filterArg.to_ptr< AvmCode >(), anElement) );
		}
		return( false );
	}

	template< class T > bool pass(AvmCode * filterCode, T * anElement)
	{
		switch( filterCode->getAvmOpCode() )
		{
			case AVM_OPCODE_AND:
			{
				AvmCode::const_iterator itFilter = filterCode->begin();
				AvmCode::const_iterator endIt = filterCode->end();
				for( ; itFilter != endIt ; ++itFilter )
				{
					if( not pass((*itFilter), anElement) )
					{
						return( false );
					}
				}

				return( true );
			}

			case AVM_OPCODE_OR:
			{
				AvmCode::const_iterator itFilter = filterCode->begin();
				AvmCode::const_iterator endIt = filterCode->end();
				for( ; itFilter != endIt ; ++itFilter )
				{
					if( pass((*itFilter), anElement) )
					{
						return( true );
					}
				}

				return( false );
			}

			case AVM_OPCODE_XOR:
			{
				avm_size_t passCount = 0;

				AvmCode::const_iterator itFilter = filterCode->begin();
				AvmCode::const_iterator endIt = filterCode->end();
				for( ; itFilter != endIt ; ++itFilter )
				{
					if( pass((*itFilter), anElement) )
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
				return( not pass(filterCode->first(), anElement) );
			}

			default:
			{
				return( false );
			}
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API: check if a generic reference Element pass
	////////////////////////////////////////////////////////////////////////////

	template< class T > bool pass(T & anElement)
	{
		if( anElement == NULL )
		{
			return( false );
		}


	AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
		AVM_OS_TRACE << std::endl;
		AVM_OS_TRACE << "candidat :> " << anElement.str() << std::endl;
		AVM_OS_TRACE << "filterTP :>" << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

		return( pass(& mainTracePointFiter, anElement) );
	}

	template< class T > bool pass(const BF & filterArg, T & anElement)
	{
		if( filterArg.is< TracePoint >() )
		{
			return( pass(filterArg.to_ptr< TracePoint >(), anElement) );
		}

		else if( filterArg.is< AvmCode >() )
		{
			return( pass(filterArg.to_ptr< AvmCode >(), anElement) );
		}
		return( false );
	}

	template< class T > bool pass(AvmCode * filterCode, T & anElement)
	{
		switch( filterCode->getAvmOpCode() )
		{
			case AVM_OPCODE_AND:
			{
				AvmCode::const_iterator itFilter = filterCode->begin();
				AvmCode::const_iterator endIt = filterCode->end();
				for( ; itFilter != endIt ; ++itFilter )
				{
					if( not pass((*itFilter), anElement) )
					{
						return( false );
					}
				}

				return( true );
			}

			case AVM_OPCODE_OR:
			{
				AvmCode::const_iterator itFilter = filterCode->begin();
				AvmCode::const_iterator endIt = filterCode->end();
				for( ; itFilter != endIt ; ++itFilter )
				{
					if( pass((*itFilter), anElement) )
					{
						return( true );
					}
				}

				return( false );
			}

			case AVM_OPCODE_XOR:
			{
				avm_size_t passCount = 0;

				AvmCode::const_iterator itFilter = filterCode->begin();
				AvmCode::const_iterator endIt = filterCode->end();
				for( ; itFilter != endIt ; ++itFilter )
				{
					if( pass((*itFilter), anElement) )
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
				return( not pass(filterCode->first(), anElement) );
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

	bool pass(TracePoint * filterTP, TracePoint * aTP);


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if VARIABLE pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(const RuntimeID & aRID, InstanceOfData * aVariable);

	bool pass(TracePoint * filterTP,
			const RuntimeID & aRID, InstanceOfData * aVariable);


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if Execution Trace
	// a.k.a. ExecutionConfiguration pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(TracePoint * filterTP, ExecutionConfiguration * anExecConfTP);


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if a Compiled Element pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(TracePoint * filterTP,
			const RuntimeID & aRID, BaseCompiledForm * anElement);


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if a Runtime Machine ID pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(TracePoint * filterTP, const RuntimeID & aRID);


	////////////////////////////////////////////////////////////////////////////
	// FILTERING API : check if AVM CODE pass
	////////////////////////////////////////////////////////////////////////////

	bool pass(TracePoint * filterTP, AvmCode * aCodeTP);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const;

};



} /* namespace sep */

#endif /* TRACEFILTER_H_ */
