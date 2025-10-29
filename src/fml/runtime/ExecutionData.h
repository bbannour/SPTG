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
#ifndef EXECUTIONDATA_H_
#define EXECUTIONDATA_H_

#include <base/SmartPointer.h>
#include <base/SmartTable.h>

#include <common/AvmPointer.h>
#include <common/Element.h>
#include <common/BF.h>

#include <fml/expression/AvmCode.h>

#include <collection/Typedef.h>

#include <fml/expression/ExpressionConstructor.h>

#include <fml/runtime/ExecutionLocation.h>
#include <fml/runtime/ExecutionSynchronizationPoint.h>
#include <fml/runtime/LocalRuntime.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfRuntimeFormState.h>


namespace sep
{

class BaseBufferForm;
class BaseInstanceForm;
class Bitset;

class ExecutionContext;
class ExecutableForm;

class InstanceOfMachine;


/**
 * TYPEDEF
 */
typedef SmartTable< RuntimeForm , DestroyElementPolicy >  TableOfRuntimeT;


class ExecutionData final :
		AVM_INJECT_STATIC_NULL_REFERENCE( ExecutionData ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionData )
{

public:
	/**
	 * ATTRIBUTES
	 * static
	 */
	static std::size_t PARAM_MACHINE_RUNTIME_OFFSET;

	static std::size_t SYSTEM_RUNTIME_OFFSET;

	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static ExecutionData & nullref()
	{
		static ExecutionData _NULL_;

		return( _NULL_ );
	}

private:
	/**
	 * TYPEDEF
	 */
	typedef AvmPointer< TableOfRuntimeFormState , DestroyObjectPolicy >
			APTableOfRuntimeFormState;

	typedef AvmPointer< StackOfLocalRuntime , DestroyObjectPolicy >
			APStackOfLocalRuntime;

	class _ExecutionData_ final :  public Element ,
			AVM_INJECT_INSTANCE_COUNTER_CLASS( _ExecutionData_ )
	{

		AVM_DECLARE_CLONABLE_CLASS( _ExecutionData_ )

	public:
		/**
		 * ATTRIBUTES
		 */
		ExecutionContext * mExecutionContext;

		BF mPathCondition;
		BF mPathTimedCondition;

		bool mGlobalNodeConditionEnabledFlag;
		bool mLocalNodeConditionEnabledFlag;

		BF mNodeCondition;
		BF mNodeTimedCondition;
		BF mRunnableElementTrace;
		BF mIOElementTrace;

		BFCode mOnInit;
		BFCode mOnSchedule;

		TableOfRuntimeT mTableOfRuntime;

		APTableOfRuntimeFormState mTableOfRFStateFlags;

		APStackOfLocalRuntime mStackOfLocalRuntime;


		// public:
		RuntimeID mRID;
		bool mPreserveRID;

		// Routine Parameter[s] or Return Statement value[s]
		BF mVALUE;

		AVM_EXECUTION_ENDING_STATUS mAEES;

		ExecutionLocationQueue mSTATEMENT_QUEUE;

		ExecutionSynchronizationPoint * mEXEC_SYNC_POINT;


		/**
		 * CONSTRUCTOR
		 * Default
		 */
		_ExecutionData_( std::size_t aMachineCount )
		: Element( CLASS_KIND_T( ExecutionData ) ),
		mExecutionContext( nullptr ),

		mPathCondition( ExpressionConstant::BOOLEAN_TRUE ),
		mPathTimedCondition( ExpressionConstant::BOOLEAN_TRUE ),

		mGlobalNodeConditionEnabledFlag( false ),
		mLocalNodeConditionEnabledFlag( false ),

		mNodeCondition( ExpressionConstant::BOOLEAN_TRUE ),
		mNodeTimedCondition( ExpressionConstant::BOOLEAN_TRUE ),

		mRunnableElementTrace( ),
		mIOElementTrace( ),

		mOnInit( ),
		mOnSchedule( ),

		mTableOfRuntime( aMachineCount ),

		mTableOfRFStateFlags( new TableOfRuntimeFormState(aMachineCount) ),
		mStackOfLocalRuntime( ),

		// public Attributes
		mRID( ),
		mPreserveRID( false ),

		mVALUE( ),

		mAEES( AEES_OK ),

		mSTATEMENT_QUEUE( ),
		mEXEC_SYNC_POINT( nullptr )
		{
			//!! NOTHING
		}


		/**
		 * CONSTRUCTOR
		 * Copy
		 */
		_ExecutionData_(const _ExecutionData_ & anED)
		: Element( anED ),
		mExecutionContext( anED.mExecutionContext ),

		mPathCondition( anED.mPathCondition ),
		mPathTimedCondition( anED.mPathTimedCondition ),

		mGlobalNodeConditionEnabledFlag( anED.mGlobalNodeConditionEnabledFlag ),
		mLocalNodeConditionEnabledFlag( anED.mLocalNodeConditionEnabledFlag ),

		mNodeCondition( anED.mNodeCondition ),
		mNodeTimedCondition( anED.mNodeTimedCondition ),

		mRunnableElementTrace( anED.mRunnableElementTrace ),
		mIOElementTrace( anED.mIOElementTrace ),

		mOnInit( anED.mOnInit ),
		mOnSchedule( anED.mOnSchedule ),

		mTableOfRuntime( anED.mTableOfRuntime ),

		mTableOfRFStateFlags( anED.mTableOfRFStateFlags ),
		mStackOfLocalRuntime( anED.mStackOfLocalRuntime ),

		// public Attributes
		mRID(anED.mRID),
		mPreserveRID( anED.mPreserveRID ),

		mVALUE( anED.mVALUE ),

		mAEES( anED.mAEES ),

		mSTATEMENT_QUEUE( anED.mSTATEMENT_QUEUE ),
		mEXEC_SYNC_POINT( (anED.mEXEC_SYNC_POINT != nullptr) ?
				new ExecutionSynchronizationPoint(
						*(anED.mEXEC_SYNC_POINT) ) : nullptr )
		{
			//!! NOTHING
		}

		/**
		 * DESTRUCTOR
		 */
		virtual ~_ExecutionData_()
		{
			delete( mEXEC_SYNC_POINT );
		}

		/**
		 * Serialization
		 */
		virtual void toStream(OutStream & out) const override
		{
			//!! NOTHING
		}

	};


protected:
	/**
	 * ATTRIBUTE
	 */
	XSmartPointer< _ExecutionData_ , DestroyElementPolicy > mSmartPtr;

public:
	/**
	 * CONSTRUCTOR
	 * for _NULL_ reference
	 */
	ExecutionData( )
	: mSmartPtr( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionData( std::size_t aMachineCount )
	: mSmartPtr( new _ExecutionData_( aMachineCount ) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionData(const ExecutionData & anED)
	: mSmartPtr( anED.mSmartPtr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionData()
	{
		//!! NOTHING
	}

	inline void destroy()
	{
		mSmartPtr.destroy();
	}

	/**
	 * VALIDITY TEST
	 * _NULL_
	 */
	inline bool isNull() const
	{
		return( //(this == (& ExecutionData::nullref())) ||
				mSmartPtr.isNullptr()  );
	}

	inline bool invalid() const
	{
		return( mSmartPtr.invalid() );
	}


	inline bool isnotNull() const
	{
		return( //(this != (& ExecutionData::nullref())) &&
				mSmartPtr.isnotNullptr() );
	}

	inline bool valid() const
	{
		return( mSmartPtr.valid() );
	}

	/**
	 * OPERATORS
	 */
//	inline _ExecutionData_ * operator-> () const
//	{
//		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( mSmartPtr )
//				<< "raw_pointer in ExecutionData !!!"
//				<< SEND_EXIT;
//
//		return( mSmartPtr.raw_pointer() );
//	}

	/**
	 * WRITABILITY
	 */
	inline void makeWritable()
	{
		mSmartPtr.makeWritable();
	}

	/**
	 * COMPARISON OPERATOR
	 * TRIVIAL EQUALITY
	 */
	virtual bool operator==(const ExecutionData & anED) const
	{
		return( (this == (& anED)) || (mSmartPtr == anED.mSmartPtr) );
	}

	virtual bool isTEQ(const ExecutionData & anED) const
	{
		if( (this == (& anED)) || (mSmartPtr == anED.mSmartPtr) )
		{
			return( true );
		}
		else if( mSmartPtr->mTableOfRFStateFlags->equalsState(
				anED.mSmartPtr->mTableOfRFStateFlags ) )
		{
			return( (mSmartPtr->mTableOfRuntime
							== anED.mSmartPtr->mTableOfRuntime)

					&& mSmartPtr->mPathCondition.isTEQ(
							anED.mSmartPtr->mPathCondition)

					&& mSmartPtr->mPathTimedCondition.isTEQ(
							anED.mSmartPtr->mPathTimedCondition)

					&& (mSmartPtr->mStackOfLocalRuntime
							== anED.mSmartPtr->mStackOfLocalRuntime) );
		}
		return( false );
	}

	inline bool isTNEQ(const ExecutionData & anED) const
	{
		return( not isTEQ( anED ) );
	}

	/**
	 * RESET DATA BEFORE EVALUATION
	 */
	inline void resetVariantBeforeEvaluation()
	{
		mSmartPtr->mNodeCondition = ExpressionConstant::BOOLEAN_TRUE;

		mSmartPtr->mNodeTimedCondition = ExpressionConstant::BOOLEAN_TRUE;

		mSmartPtr->mRunnableElementTrace = BF::REF_NULL;

		mSmartPtr->mIOElementTrace = BF::REF_NULL;

		mSmartPtr->mTableOfRFStateFlags->setTableOfAssignedFlag( nullptr );
	}

	inline void storeVariantBeforeEvaluation(
			BF & aNodeCondition, BF & aNodeTimedCondition,
			BF & aRunnableElementTrace, BF & aIOElementTrace,
			TableOfRuntimeFormState::TableOfAssignedFlag & aTableOfAssignedFlag)
	{
		aNodeCondition = mSmartPtr->mNodeCondition;
		mSmartPtr->mNodeCondition = ExpressionConstant::BOOLEAN_TRUE;

		aNodeTimedCondition = mSmartPtr->mNodeTimedCondition;
		mSmartPtr->mNodeTimedCondition = ExpressionConstant::BOOLEAN_TRUE;

		aRunnableElementTrace = mSmartPtr->mRunnableElementTrace;
		mSmartPtr->mRunnableElementTrace = BF::REF_NULL;

		aIOElementTrace = mSmartPtr->mIOElementTrace;
		mSmartPtr->mIOElementTrace = BF::REF_NULL;

		// Due to basic pointer, not smart pointer
		aTableOfAssignedFlag =
				mSmartPtr->mTableOfRFStateFlags->getTableOfAssignedFlag();
		mSmartPtr->mTableOfRFStateFlags->setTableOfAssignedFlag( nullptr );
	}


	/**
	 * RESTORE DATA AFTER EVALUATION
	 */
	inline void restoreVariantAfterEvaluation(
			const BF & aNodeCondition, const BF & aNodeTimedCondition,
			const BF & aRunnableElementTrace, const BF & aIOElementTrace,
			const TableOfRuntimeFormState::
			TableOfAssignedFlag & aTableOfAssignedFlag)
	{
		mSmartPtr->mNodeCondition = aNodeCondition;
		mSmartPtr->mNodeTimedCondition = aNodeTimedCondition;

		mSmartPtr->mRunnableElementTrace = aRunnableElementTrace;
		mSmartPtr->mIOElementTrace = aIOElementTrace;

		mSmartPtr->mTableOfRFStateFlags->setTableOfAssignedFlag(
				aTableOfAssignedFlag );
	}


	/**
	 * resize
	 */
	void resize(std::size_t newMachineCount)
	{
		mSmartPtr->mTableOfRuntime.makeWritableResize( newMachineCount );

		mSmartPtr->mTableOfRFStateFlags.makeWritable();
		mSmartPtr->mTableOfRFStateFlags->resize(newMachineCount);
	}


	/**
	 * GETTER - SETTER
	 * mExecutionContext
	 */
	inline ExecutionContext * getExecutionContext() const
	{
		return( mSmartPtr->mExecutionContext );
	}

	inline bool hasExecutionContext() const
	{
		return( mSmartPtr->mExecutionContext != nullptr );
	}

	inline void setExecutionContext(ExecutionContext * anExecutionContext)
	{
		mSmartPtr->mExecutionContext = anExecutionContext;
	}

	// Previous ExecutionData
	ExecutionData & getPrevious();

	const ExecutionData & getPrevious() const;


	/**
	 * GETTER
	 * mPathCondition  &&  mPathTimedCondition
	 */
	inline BF getAllPathCondition() const
	{
		if( mSmartPtr->mPathTimedCondition.valid()
			&& mSmartPtr->mPathTimedCondition.isNotEqualTrue() )
		{
			return( ExpressionConstructor::andExpr(
					mSmartPtr->mPathCondition, mSmartPtr->mPathTimedCondition) );
		}
		else
		{
			return( mSmartPtr->mPathCondition );
		}
	}


	inline BF andPathTimedCondition(const BF & aCondition) const
	{
		if( mSmartPtr->mPathTimedCondition.valid() )
		{
			if( mSmartPtr->mPathTimedCondition.isEqualTrue() )
			{
				return( aCondition );
			}
			else if( mSmartPtr->mPathTimedCondition.isEqualFalse() )
			{
				return( mSmartPtr->mPathTimedCondition );
			}

			return( ExpressionConstructor::andExpr(
					mSmartPtr->mPathTimedCondition, aCondition) );
		}
		else
		{
			return( aCondition );
		}
	}

	/**
	 * GETTER - SETTER
	 * mPathCondition
	 */
	inline const BF & getPathCondition() const
	{
		return( mSmartPtr->mPathCondition );
	}

	inline bool hasPathCondition() const
	{
		return( mSmartPtr->mPathCondition.valid() );
	}

	inline void setPathCondition(const BF & aPathCondition)
	{
		mSmartPtr->mPathCondition = aPathCondition;
	}

	inline void mwsetPathCondition(const BF & aPathCondition)
	{
		makeWritable();

		mSmartPtr->mPathCondition = aPathCondition;
	}


	/**
	 * GETTER - SETTER
	 * mPathTimedCondition
	 */
	inline const BF & getPathTimedCondition() const
	{
		return( mSmartPtr->mPathTimedCondition );
	}

	inline bool hasPathTimedCondition() const
	{
		return( mSmartPtr->mPathTimedCondition.valid() );
	}

	inline void setPathTimedCondition(const BF & aPathTimedCondition)
	{
		mSmartPtr->mPathTimedCondition = aPathTimedCondition;
	}

	inline void mwsetPathTimedCondition(const BF & aPathTimedCondition)
	{
		makeWritable();

		mSmartPtr->mPathTimedCondition = aPathTimedCondition;
	}


	/**
	 * GETTER
	 * mNodeCondition  &&  mNodeTimedCondition
	 */
	inline BF getAllNodeCondition() const
	{
		if( mSmartPtr->mNodeTimedCondition.valid()
			&& mSmartPtr->mNodeTimedCondition.isNotEqualTrue() )
		{
			return( ExpressionConstructor::andExpr(
					mSmartPtr->mNodeCondition, mSmartPtr->mNodeTimedCondition) );
		}
		else
		{
			return( mSmartPtr->mNodeCondition );
		}
	}


	/**
	 * GETTER - SETTER
	 * mNodeCondition
	 */
	inline const BF & getNodeCondition() const
	{
		return( mSmartPtr->mNodeCondition );
	}

	inline bool hasNodeCondition() const
	{
		return( mSmartPtr->mNodeCondition.valid() );
	}

	inline void setNodeCondition(const BF & aCondition)
	{
		mSmartPtr->mNodeCondition = aCondition;
	}

	inline void resetNodeCondition()
	{
		mSmartPtr->mNodeCondition = ExpressionConstant::BOOLEAN_TRUE;
	}


	/**
	 * GETTER - SETTER
	 * mNodeTimedCondition
	 */
	inline const BF & getNodeTimedCondition() const
	{
		return( mSmartPtr->mNodeTimedCondition );
	}

	inline bool hasNodeTimedCondition() const
	{
		return( mSmartPtr->mNodeTimedCondition.valid() );
	}

	inline void setNodeTimedCondition(const BF & aTimedCondition)
	{
		mSmartPtr->mNodeTimedCondition = aTimedCondition;
	}


	/**
	 * GETTER - SETTER
	 * mGlobalNodeConditionEnabledFlag
	 * mLocalNodeConditionEnabledFlag
	 */
	inline bool isEnabledNodeCondition() const
	{
		return( //mSmartPtr->mGlobalNodeConditionEnabledFlag ||
				mSmartPtr->mLocalNodeConditionEnabledFlag );
	}

	inline void setEnabledGlobalNodeCondition(bool aCondition = true)
	{
		mSmartPtr->mGlobalNodeConditionEnabledFlag = aCondition;
	}

	inline void setEnabledLocalNodeCondition(bool aCondition = true)
	{
		mSmartPtr->mLocalNodeConditionEnabledFlag = aCondition;
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const;

	inline std::string str() const
	{
		return( strStateConf() );
	}

	void toStreamData(OutStream & out) const;

	void toFscn(OutStream & out, const ExecutionData & aPreviousExecData) const;


	/**
	 * string of a state configuration of an ExecutionData
	 * !UNUSED!
	inline std::string strStateIdleOrRunning() const
	{
		if( getSystemRuntimeForm()->hasOnSchedule()
			|| getSystemRuntimeForm()->hasChild() )
		{
			return( strStateIdleOrRunning( getSystemRuntimeForm() ) );
		}
		else
		{
			return( "(" + strStateIdleOrRunning( getSystemRuntime() ) + ")" );
		}
	}

	inline std::string strStateIdleOrRunning(const RuntimeForm & aRF) const
	{
		StringOutStream oss;

		toStreamStateIdleOrRunning(oss, aRF);

		return( oss.str() );
	}
	* !UNUSED!
	*/

	void toStreamStateIdleOrRunning(
			OutStream & out, const RuntimeForm & aRF) const;

	/**
	 * string of a state configuration of an ExecutionData
	 *
	 * LIFELINE STATE IDENTIFIER
	 * %1% --> lifeline runtime pid
	 * %2% --> lifeline identifier
	 * %3% --> state runtime pid
	 * %4% --> state identifier
	 */
	OutStream & toStreamLifelineStateFormat(
			OutStream & out, const RuntimeForm & aRF,
			const std::string & formatLifelineStatePattern = "%3%:%4%") const;

	inline std::string strStateConf(
			const std::string & formatLifelineStatePattern = "%3%:%4%") const
	{
		if( getSystemRuntime().hasOnSchedule() )
		{
			return( strStateConf(
					getSystemRuntime() , formatLifelineStatePattern ) );
		}
		else
		{
			return( "(" + strStateConf( getSystemRuntime() ,
					formatLifelineStatePattern ) + ")" );
		}
	}

	std::string strStateConf(const RuntimeForm & aRF,
			const std::string & formatLifelineStatePattern = "%3%:%4%") const
	{
		StringOutStream oss;

		toStreamStateConf(oss, aRF, formatLifelineStatePattern);

		return( oss.str() );
	}

	void toStreamStateConf(OutStream & out, const RuntimeForm & aRF,
			const std::string & formatLifelineStatePattern = "%3%:%4%") const;


	/**
	 * string of a state configuration of an ExecutionData
	 */
	inline std::string strStateConfToFscn() const
	{
		if( getSystemRuntime().hasOnSchedule()
			|| getSystemRuntime().hasChild() )
		{
			return( strStateConfToFscn( getSystemRuntime() ) );
		}
		else
		{
			return( "(" + strStateConfToFscn( getSystemRuntime() ) + ")" );
		}
	}

	inline std::string strStateConfToFscn(const RuntimeForm & aRF) const
	{
		StringOutStream oss;

		toStreamStateConfToFscn(oss, aRF);

		return( oss.str() );
	}

	void toStreamStateConfToFscn(
			OutStream & out, const RuntimeForm & aRF) const;


	/**
	 * GETTER - SETTER
	 * mRunnableElementTrace
	 */
	inline BF & getRunnableElementTrace()
	{
		return( mSmartPtr->mRunnableElementTrace );
	}

	inline const BF & getRunnableElementTrace() const
	{
		return( mSmartPtr->mRunnableElementTrace );
	}

	inline bool hasRunnableElementTrace() const
	{
		return( mSmartPtr->mRunnableElementTrace.valid() );
	}


	inline void setRunnableElementTrace(const BF & aRunnableElementTrace)
	{
		mSmartPtr->mRunnableElementTrace = aRunnableElementTrace;
	}

	inline void mwsetRunnableElementTrace(const BF & aRunnableElementTrace)
	{
		makeWritable();

		mSmartPtr->mRunnableElementTrace = aRunnableElementTrace;
	}

	/**
	 * GETTER - SETTER
	 * mIOElementTrace
	 */
	inline BF & getIOElementTrace()
	{
		return( mSmartPtr->mIOElementTrace );
	}

	inline const BF & getIOElementTrace() const
	{
		return( mSmartPtr->mIOElementTrace );
	}

	inline bool hasIOElementTrace() const
	{
		return( mSmartPtr->mIOElementTrace.valid() );
	}


	inline void setIOElementTrace(const BF & anIOElementTrace)
	{
		mSmartPtr->mIOElementTrace = anIOElementTrace;
	}

	inline void mwsetIOElementTrace(const BF & anIOElementTrace)
	{
		makeWritable();

		mSmartPtr->mIOElementTrace = anIOElementTrace;
	}


	/**
	 * GETTER
	 * mRunnableElementTrace
	 * mIOElementTrace
	 */
//$DELETE
	inline bool notEvaluated() const
	{
		return( mSmartPtr->mRunnableElementTrace.invalid()
				&& mSmartPtr->mIOElementTrace.invalid() );
	}


	/**
	 * GETTER - SETTER
	 * mOnInit
	 */
	inline const BFCode & getOnInit() const
	{
		return( mSmartPtr->mOnInit );
	}

	inline bool hasOnInit() const
	{
		return( mSmartPtr->mOnInit.valid() );
	}

	inline void setOnInit(const BFCode & onInit)
	{
		mSmartPtr->mOnInit = onInit;
	}


	/**
	 * GETTER - SETTER
	 * mOnSchedule
	 */
	inline const BFCode & getOnSchedule() const
	{
		return( mSmartPtr->mOnSchedule );
	}

	inline bool hasOnSchedule() const
	{
		return( mSmartPtr->mOnSchedule.valid() );
	}

	inline void setOnSchedule(const BFCode & onSchedule)
	{
		mSmartPtr->mOnSchedule = onSchedule;
	}


	/**
	 * GETTER - SETTER
	 * mTableOfRuntimeForm
	 */
	inline const TableOfRuntimeT & getTableOfRuntime() const
	{
		return( mSmartPtr->mTableOfRuntime );
	}


	inline RuntimeForm & getRuntime(std::size_t offset)
	{
		return( mSmartPtr->mTableOfRuntime.ref(offset) );
	}

	inline const RuntimeForm & getRuntime(std::size_t offset) const
	{
		return( mSmartPtr->mTableOfRuntime.ref(offset) );
	}


	inline RuntimeForm & getRuntime(const RuntimeID & aRID)
	{
		return( mSmartPtr->mTableOfRuntime.ref( aRID.getOffset() ) );
	}

	inline const RuntimeForm & getRuntime(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRuntime.ref( aRID.getOffset() ) );
	}


	inline const RuntimeForm * ptrRuntime(std::size_t offset) const
	{
		return( mSmartPtr->mTableOfRuntime.at(offset) );
	}

	inline RuntimeForm * ptrRuntime(const RuntimeID & aRID)
	{
		return( mSmartPtr->mTableOfRuntime.at( aRID.getOffset() ) );
	}

	inline const RuntimeForm * ptrRuntime(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRuntime.at( aRID.getOffset() ) );
	}


	inline const RuntimeID & getRuntimeID(std::size_t rid) const
	{
		return( mSmartPtr->mTableOfRuntime.at(rid)->getRID() );
	}

	const RuntimeID & getRuntimeID(const ExecutableForm & anExecutable) const;

	const RuntimeID & getRuntimeID(const InstanceOfMachine & anInstance) const;

	const RuntimeID & getRuntimeID(
			const std::string & aFullyQualifiedNameID) const;

	const RuntimeID & getRuntimeIDByNameID(const std::string & aNameID) const;

	const RuntimeID & getRuntimeIDByQualifiedNameID(
			const std::string & aQualifiedNameID) const;


	RuntimeID getRuntimeContainerRID(const RuntimeID & aRID,
			const BaseInstanceForm * anInstance) const;

	inline RuntimeID getRuntimeContainerRID(
			const BaseInstanceForm * anInstance) const
	{
		return( getRuntimeContainerRID(mSmartPtr->mRID, anInstance) );
	}


	// RuntimeForm::mOnSchedule
	inline const BFCode & getRuntimeFormOnSchedule(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRuntime.at(aRID.getOffset())->getOnSchedule() );
	}

	inline void mwsetRuntimeFormOnSchedule(
			const RuntimeID & aRID, const BFCode & onSchedule)
	{
		if( aRID.refExecutable().isMutableSchedule()
			&& (onSchedule != getRuntime(aRID).getOnSchedule()) )
		{
			makeWritable();

			getWritableRuntime(aRID).setOnSchedule( onSchedule );
		}
	}

	inline void mwsetRuntimeFormOnScheduleAndIdle(const RuntimeID & aRID)
	{
		mwsetRuntimeFormOnSchedule(aRID.getPRID(), aRID.getOnRunning());

//		mwsetRuntimeFormOnSchedule(aRID.getPRID(),
//				aRID.hasOnRunning() ? aRID.getOnRunning() :
//						StatementConstructor::newOptiNopCode(
//								OperatorManager::OPERATOR_RUN, aRID,
//								AVM_ARG_MACHINE_RID) );

		if( not isIdle() )
		{
			mwsetRuntimeFormState(aRID, PROCESS_IDLE_STATE);
		}
	}


	// RuntimeForm::mOnDefer
	inline const BFCode & getRuntimeFormOnDefer(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRuntime.at(aRID.getOffset())->getOnDefer() );
	}

	inline void mwsetRuntimeFormOnDefer(
			const RuntimeID & aRID, const BFCode & onDefer)
	{
		makeWritable();

		getWritableRuntime( aRID ).setOnDefer( onDefer );
	}


	// assign <==> release_acquire
	inline void saveRuntimeForm(std::size_t offset, RuntimeForm * aRF) const
	{
		mSmartPtr->mTableOfRuntime.set(offset, aRF);
	}

	// assign <==> release_acquire
	inline void assignRuntimeForm(std::size_t offset, RuntimeForm * aRF) const
	{
		mSmartPtr->mTableOfRuntime.assign(offset, aRF);
	}

	/**
	 * GETTER
	 * Time Value
	 */
	inline const BF & getTimeValue() const
	{
		return( getTimeValue( getRID() ) );
	}

	const BF & getTimeValue(const RuntimeID & aRID) const;


	/**
	 * GETTER
	 * Delta Time Value
	 */
	inline const BF & getDeltaTimeValue() const
	{
		return( getDeltaTimeValue( getRID() ) );
	}

	const BF & getDeltaTimeValue(const RuntimeID & aRID) const;


	/**
	 * SYNC-SETTER
	 * Synchronization of Time Values
	 */
	inline void syncTimeValues(const ExecutionData & refED)
	{
		return( syncTimeValues( getRID() , refED ) );
	}

	void syncTimeValues(const RuntimeID & aRID, const ExecutionData & refED);


	/***************************************************************************
	 ***************************************************************************
	 * GETTER - SETTER
	 * mTableOfRuntime
	 *
	 * make writable
	 ***************************************************************************
	 */
//	inline RuntimeForm & getWritableRuntime(const RuntimeID & aRID)
//	{
//		return( mSmartPtr->mTableOfRuntime.refWritable( aRID.getOffset() ) );
//	}

	inline RuntimeForm & getWritableRuntime(const RuntimeID & aRID)
	{
		makeWritable();

		return( mSmartPtr->mTableOfRuntime.refWritable( aRID.getOffset() ) );

	}

	inline APTableOfData & getWritableRuntimeDataTable(const RuntimeID & aRID)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( getRuntime(aRID).hasDataTable() )
				<< "Unexpected RuntimeForm without data !!!"
				<< SEND_EXIT;

		makeWritable();

		return( getWritableRuntime(aRID).getWritableDataTable() );
	}


	/**
	 * GETTER
	 * for data in RuntimeForm DataTable
	 */
	const BF & getDataByQualifiedNameID(
			const std::string & aQualifiedNameID, InstanceOfData * & var) const;

	const BF & getDataByNameID(const std::string & aNameID) const;


	/**
	 * GETTER - SETTER
	 * mTableOfRFStateFlags
	 */
	inline const TableOfRuntimeFormState * getRuntimeFormStateTable() const
	{
		return( mSmartPtr->mTableOfRFStateFlags );
	}

	inline TableOfRuntimeFormState * wrRuntimeFormStateTable()
	{
		return( mSmartPtr->mTableOfRFStateFlags );
	}


	inline PROCESS_EVAL_STATE getRuntimeFormState(std::size_t rid) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->stateAt(rid) );
	}

	inline  PROCESS_EVAL_STATE getRuntimeFormState(
			const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->stateAt( aRID.getOffset() ) );
	}

	bool checkRunningForm(
			const BF & aRunnableElementTrace, const RuntimeID & aRID) const;

	inline bool checkRunningForm(const RuntimeID & aRID) const
	{
		return( checkRunningForm(getRunnableElementTrace(), aRID) );
	}


	// CREATED STATE
	inline bool isCreated(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isCreated( aRID.getOffset() ) );
	}

	// LOADED STATE
	inline bool isLoaded(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isLoaded( aRID.getOffset() ) );
	}

	// STARTING STATE
	inline bool isStarting(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isStarting( aRID.getOffset() ) );
	}

	inline bool isIniting(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isIniting( aRID.getOffset() ) );
	}

	// STOPPING STATE
	inline bool isStopping(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isStopping( aRID.getOffset() ) );
	}

	// STOPPED STATE
	inline bool isStopped(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isStopped( aRID.getOffset() ) );
	}

	// FINALIZING STATE
	inline bool isFinalizing(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isFinalizing( aRID.getOffset() ) );
	}

	// FINALIZED STATE
	inline bool isFinalized(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isFinalized( aRID.getOffset() ) );
	}

	// DESTROYED STATE
	inline bool isDestroyed(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isDestroyed( aRID.getOffset() ) );
	}

	// FINALIZED or DESTROYED STATE
	inline bool isFinalizedOrDestroyed(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->
				isFinalizedOrDestroyed( aRID.getOffset() ) );
	}

	// ALIVE STATE
	inline bool isAlive(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isAlive( aRID.getOffset() ) );
	}

	// SUPENDED STATE
	inline bool isSuspended(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isSuspended( aRID.getOffset() ) );
	}

	// WAITING STATE
	inline bool isWaiting(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isWaiting( aRID.getOffset() ) );
	}

	// WAITING JOIN STATE
	inline bool isWaitingJoin(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isWaitingJoin( aRID.getOffset() ) );
	}

	// DISABLE STATE
	inline bool isDisable(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isDisable( aRID.getOffset() ) );
	}

	// DISABLE STATE
	inline bool isAborted(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isAborted( aRID.getOffset() ) );
	}

	// DISABLE or ABORTED STATE
	inline bool isDisableOrAborted(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->
				isDisableOrAborted( aRID.getOffset() ) );
	}

	// IDLE STATE
	inline bool isIdle() const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isIdle(
				mSmartPtr->mRID.getOffset() ) );
	}

	inline bool isIdle(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isIdle( aRID.getOffset() ) );
	}

	// RUNNING STATE
	inline bool isRunning(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isRunning( aRID.getOffset() ) );
	}

	// IDLE or RUNNING STATE
	inline bool isIdleOrRunning(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isIdleOrRunning( aRID.getOffset() ) );
	}

	// RUNNABLE STATE
	inline bool isRunnable(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isRunnable( aRID.getOffset() ) );
	}

	inline bool isunRunnable(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isunRunnable( aRID.getOffset() ) );
	}

	inline bool isunRunnableSystem() const
	{
		return( mSmartPtr->mTableOfRFStateFlags->
				isunRunnable( SYSTEM_RUNTIME_OFFSET ) );
	}

	// CREATED or RUNNABLE STATE
	inline bool isCreatedOrRunnable(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->
				isCreatedOrRunnable( aRID.getOffset() ) );
	}

	// DEFINED / UNDEFINED STATE
	inline bool isDefinedPES(const RuntimeID & aRID) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isDefined( aRID.getOffset() ) );
	}

	inline bool isUndefinedPES(avm_offset_t offset) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isUndefined( offset ) );
	}

	inline void makeWritableRuntimeFormStateTable()
	{
		mSmartPtr->mTableOfRFStateFlags.makeWritable();
	}

	inline void mwsetRuntimeFormState(
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES)
	{
		makeWritable();

		makeWritableRuntimeFormStateTable();

		mSmartPtr->mTableOfRFStateFlags->stateSet(aRID.getOffset(), aPES);
	}

	inline void setRuntimeFormState(
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES)
	{
		mSmartPtr->mTableOfRFStateFlags->stateSet(aRID.getOffset(), aPES);
	}


	inline void mwsetRuntimeFormState(std::size_t rid, PROCESS_EVAL_STATE aPES)
	{
		makeWritableRuntimeFormStateTable();

		mSmartPtr->mTableOfRFStateFlags->stateSet(rid, aPES);
	}

	inline void setRuntimeFormState(std::size_t rid, PROCESS_EVAL_STATE aPES)
	{
		mSmartPtr->mTableOfRFStateFlags->stateSet(rid, aPES);
	}


	inline void mwsetRuntimeFormState(PROCESS_EVAL_STATE aPES)
	{
		mwsetRuntimeFormState(mSmartPtr->mRID, aPES);
	}

	inline void mwsetRuntimeFormState(const RuntimeID & aRID,
			PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
	{
		makeWritable();

		if( getRuntimeFormState(aRID) == oldPES )
		{
			mwsetRuntimeFormState(aRID.getOffset(), aPES);

			setAEES( RuntimeDef::PES_to_AEES( aPES , getAEES() ) );
		}
	}


	/**
	 * GETTER -- SETTER
	 * ASSIGNED FLAGS
	 */
	inline const Bitset * getAssigned(std::size_t rid) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->getAssigned(rid) );
		
//		return( getRuntime(rid).getAssigned() );
	}

	inline bool isAssigned(const RuntimeID & aRID, std::size_t varOffset) const
	{
		return( mSmartPtr->mTableOfRFStateFlags->isAssigned(
				aRID.getOffset(), varOffset) );
	
//		return( getRuntime(aRID).isAssigned(varOffset) );
	}

	inline void setAssigned(const RuntimeID & aRID, avm_offset_t varOffset)
	{
		mSmartPtr->mTableOfRFStateFlags->setAssigned(
				(*this), aRID.getOffset(), varOffset);

//		getRuntime(aRID).setAssigned(assignFlags);
	}

	inline void setAssigned(std::size_t rid, const Bitset * assignFlags) const
	{
		mSmartPtr->mTableOfRFStateFlags->setAssigned(rid, assignFlags);

//		getRuntime(rid).setAssigned(assignFlags);
	}

	// TABLE OF ASSIGNED FLAGS
	TableOfRuntimeFormState::TableOfAssignedFlag getTableOfAssignedFlag()
	{
		return( mSmartPtr->mTableOfRFStateFlags->getTableOfAssignedFlag() );
	}

	void setTableOfAssignedFlag(
			TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag)
	{
		mSmartPtr->mTableOfRFStateFlags->setTableOfAssignedFlag( aTableOfAssignedFlag );
	}
	
	
	/**
	 * GETTER - SETTER
	 * RuntimeForm CHILD
	 */
	inline const RuntimeID & getRuntimeFormChild(const RuntimeID & aRID,
			const InstanceOfMachine * anInstance) const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( getRuntime(aRID).getChild(
			anInstance->getOffset() ).getInstance() == anInstance )
				<< "Fatal Error: Bad child< "
				<< anInstance->getQualifiedNameID()
				<< " > Offset in runtime machine< "
				<< aRID.getQualifiedNameID() << " >!!!"
				<< SEND_EXIT;

		return( getRuntime(aRID).getChild(anInstance->getOffset()) );
	}


	/**
	 * GETTER - SETTER
	 * mStackOfLocalRuntime
	 */
	inline void createLocalRuntimeStack() const
	{
		mSmartPtr->mStackOfLocalRuntime =
				APStackOfLocalRuntime( new StackOfLocalRuntime() );
	}

	inline void destroyLocalRuntimeStack() const
	{
		mSmartPtr->mStackOfLocalRuntime.destroy();
	}

	inline APStackOfLocalRuntime & getLocalRuntimes()
	{
		return( mSmartPtr->mStackOfLocalRuntime );
	}

	inline const APStackOfLocalRuntime & getLocalRuntimes() const
	{
		return( mSmartPtr->mStackOfLocalRuntime );
	}


	inline bool hasLocalRuntime() const
	{
		return( mSmartPtr->mStackOfLocalRuntime.valid()
				&& mSmartPtr->mStackOfLocalRuntime->nonempty() );
	}

	inline bool hasLocalRuntimeStack() const
	{
		return( mSmartPtr->mStackOfLocalRuntime.valid() );
	}

	inline void makeWritableLocalRuntimeStack()
	{
		if( mSmartPtr->mStackOfLocalRuntime.valid() )
		{
			mSmartPtr->mStackOfLocalRuntime.makeWritable();
		}
		else
		{
			mSmartPtr->mStackOfLocalRuntime.replacePointer(
					new StackOfLocalRuntime() );
		}
	}

	inline void setLocalRuntime(std::size_t offset,
			const LocalRuntime & aLocalRuntime)
	{
		mSmartPtr->mStackOfLocalRuntime->setLocalRuntime(offset, aLocalRuntime);
	}


	// Make modifiable i.e. writable

	inline void makeModifiableParamTable()
	{
		makeWritable();

		// TODO Revoir la gestion de la liste des nouveaux parametres
//		if( hasParam() && getParam()->isMultiple() )
//		{
//			decRefCounter( getParam() );
//			setParam( new TableOfInstance() );
//		}
	}

	inline void makeModifiableLocalRuntime(LocalRuntime & aLocalRuntime)
	{
		makeWritable();

		makeWritableLocalRuntimeStack();

		aLocalRuntime.makeWritable();

		setLocalRuntime( aLocalRuntime.getOffset() , aLocalRuntime );
	}


	/**
	 * GETTER - SETTER
	 * mParametersRuntimeForm
	 */
	inline const ParametersRuntimeForm & getParametersRuntimeForm() const
	{
		return( static_cast< const ParametersRuntimeForm & >(
				mSmartPtr->mTableOfRuntime.ref(PARAM_MACHINE_RUNTIME_OFFSET) ) );
	}

	inline ParametersRuntimeForm & getWritableParametersRuntimeForm()
	{
		makeWritable();

		ParametersRuntimeForm & pRF = static_cast< ParametersRuntimeForm & >(
				mSmartPtr->mTableOfRuntime.refWritable(
						PARAM_MACHINE_RUNTIME_OFFSET) );

		pRF.resetOffset();

		return( pRF );
	}

	inline BF bfParametersRuntimeForm() const
	{
		return(  mSmartPtr->mTableOfRuntime.to_sp< BF >(
				PARAM_MACHINE_RUNTIME_OFFSET ) );
	}


	inline const RuntimeID & getParametersRID() const
	{
		return( getRuntime(PARAM_MACHINE_RUNTIME_OFFSET).getRID() );
	}

	inline const BF & saveParameter(InstanceOfData * anInstance)
	{
		return( getWritableParametersRuntimeForm().saveParameter(anInstance) );
	}

	inline void appendParameters(BFList & paramsList)
	{
		getWritableParametersRuntimeForm().appendParameters(paramsList);
	}

	inline void appendConstParameters(BFVector & paramsVector)
	{
		getWritableParametersRuntimeForm().appendConstParameters(paramsVector);
	}


	inline void saveParametersRuntimeForm(
			ParametersRuntimeForm * paramsRF) const
	{
		mSmartPtr->mTableOfRuntime.set(PARAM_MACHINE_RUNTIME_OFFSET, paramsRF);
	}

	inline void assignParametersRuntimeForm(
			ParametersRuntimeForm * paramsRF) const
	{
		mSmartPtr->mTableOfRuntime.assign(PARAM_MACHINE_RUNTIME_OFFSET, paramsRF);
	}

	inline void assignParametersRuntimeForm(const BF & paramsRF) const
	{
		mSmartPtr->mTableOfRuntime.assign(PARAM_MACHINE_RUNTIME_OFFSET,
				paramsRF.to_ptr< RuntimeForm >() );
	}


	/**
	 * GETTER - SETTER
	 * System RuntimeForm
	 */
	inline const RuntimeForm & getSystemRuntime() const
	{
		return( getRuntime(SYSTEM_RUNTIME_OFFSET) );
	}

	inline const RuntimeID & getSystemRID() const
	{
		return( getRuntime(SYSTEM_RUNTIME_OFFSET).getRID() );
	}

	inline void setSystemRID()
	{
		setRID( getSystemRID() );
	}


	/**
	 * GETTER - SETTER
	 * mRID
	 */
	inline const RuntimeID & getRID() const
	{
		return( mSmartPtr->mRID );
	}

	inline void setRID(const RuntimeID & aRID) const
	{
		mSmartPtr->mRID = aRID;
	}

	inline void mwsetRID(const RuntimeID & aRID)
	{
		makeWritable();

		mSmartPtr->mRID = aRID;
	}

	/**
	 * GETTER - SETTER
	 * mPreserveRID
	 */
	inline bool isPreserveRID() const
	{
		return( mSmartPtr->mPreserveRID );
	}

	inline void setPreserveRID(bool isPreserveRID)
	{
		mSmartPtr->mPreserveRID = isPreserveRID;
	}


	/**
	 * GETTER - SETTER
	 * mVALUE
	 */
	inline const BF & getValue() const
	{
		return( mSmartPtr->mVALUE );
	}

	inline bool hasValue() const
	{
		return( mSmartPtr->mVALUE.valid() );
	}

	inline void setValue(const BF & aValue)
	{
		mSmartPtr->mVALUE = aValue;
	}


	/*
	 * GETTER - SETTER
	 * Avm Ending Execution Status
	 */
	inline AVM_EXECUTION_ENDING_STATUS getAEES() const
	{
		return( mSmartPtr->mAEES );
	}

	inline void setAEES(AVM_EXECUTION_ENDING_STATUS anAEES)
	{
		mSmartPtr->mAEES = anAEES;
	}

	inline void mwsetAEES(AVM_EXECUTION_ENDING_STATUS anAEES)
	{
		makeWritable();

		mSmartPtr->mAEES = anAEES;
	}

	/*
	 * GETTER - SETTER
	 * ExecutionLocationQueue
	 */
	inline bool hasExecutionLocation()
	{
		return( mSmartPtr->mSTATEMENT_QUEUE.nonempty() );
	}


	inline void popExecutionLocationTo(BF & anExecLocation)
	{
		mSmartPtr->mSTATEMENT_QUEUE.popTo( anExecLocation );
	}


	inline void pushExecutionLocationhCache()
	{
		mSmartPtr->mSTATEMENT_QUEUE.pushCache();
	}

	inline void pushExecutionLocation(const BFCode & aCode)
	{
		makeWritable();

		mSmartPtr->mSTATEMENT_QUEUE.push(mSmartPtr->mRID, aCode);
	}

	inline void pushExecutionLocation(const BFCode & aCode,
			const AvmCode::const_iterator & it,
			const AvmCode::const_iterator & endIt)
	{
		makeWritable();

		mSmartPtr->mSTATEMENT_QUEUE.push(mSmartPtr->mRID, aCode, it, endIt);
	}


	/*
	 * GETTER - SETTER
	 * Execution Synchronization Point
	 */
	inline void destroyExecSyncPoint()
	{
		sep::destroy( mSmartPtr->mEXEC_SYNC_POINT );

		mSmartPtr->mEXEC_SYNC_POINT = nullptr;
	}


	inline const ExecutionSynchronizationPoint * getExecSyncPoint() const
	{
		return( mSmartPtr->mEXEC_SYNC_POINT );
	}

	inline bool hasExecSyncPoint()
	{
		return( mSmartPtr->mEXEC_SYNC_POINT != nullptr );
	}

	inline void pushExecSyncPoint(
			ExecutionSynchronizationPoint * anExecSyncPoint)
	{
		makeWritable();

		if( mSmartPtr->mEXEC_SYNC_POINT == nullptr )
		{
			mSmartPtr->mEXEC_SYNC_POINT = anExecSyncPoint;
		}
		else
		{
			ExecutionSynchronizationPoint * lastESP = mSmartPtr->mEXEC_SYNC_POINT;
			while( lastESP->next != nullptr )
			{
				lastESP = lastESP->next;
			}
			lastESP->next = anExecSyncPoint;
		}
	}


	inline void printExecSyncPointTrace(OutStream & out) const
	{
		if( mSmartPtr.valid() )
		{
			out << TAB << "ED@" << mSmartPtr.raw_address();
			if( mSmartPtr->mEXEC_SYNC_POINT != nullptr )
			{
				mSmartPtr->mEXEC_SYNC_POINT->printTrace( out );
			}
			out << " " << getRunnableElementTrace().str()
				<< EOL_FLUSH;
		}
	}



	/**
	 * INSTANCIATION BOUND TEST
	 */
	bool couldBeInstanciated(InstanceOfMachine * anInstance) const;


};


////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for CONTAINER
////////////////////////////////////////////////////////////////////////////////

typedef Collection< ExecutionData >        CollectionOfExecutionData;

typedef List      < ExecutionData >        ListOfExecutionData;

typedef Vector    < ExecutionData >        VectorOfExecutionData;

}

#endif /*EXECUTIONDATA_H_*/
