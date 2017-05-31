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


class ExecutionData :  public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionData )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionData )


public:
	/**
	 * ATTRIBUTES
	 * static
	 */
	static avm_size_t PARAM_MACHINE_RUNTIME_OFFSET;

	static avm_size_t SYSTEM_RUNTIME_OFFSET;

protected:
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

public:
	/**
	 * ATTRIBUTES
	 * public
	 */
	RuntimeID mRID;
	bool mPreserveRID;

	// Routine Parameter[s] or Return Statement value[s]
	BF mVALUE;

	AVM_EXEC_ENDING_STATUS mAEES;

	ExecutionLocationQueue mSTATEMENT_QUEUE;

	ExecutionSynchronizationPoint * mEXEC_SYNC_POINT;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionData( avm_size_t aMachineCount )
	: Element( CLASS_KIND_T( ExecutionData ) ),
	mExecutionContext( NULL ),

	mPathCondition( ),
	mPathTimedCondition( ),

	mGlobalNodeConditionEnabledFlag( true ),
	mLocalNodeConditionEnabledFlag( false ),

	mNodeCondition( ),
	mNodeTimedCondition( ),

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
	mEXEC_SYNC_POINT( NULL )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionData(const ExecutionData & anED)
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
	mEXEC_SYNC_POINT( (anED.mEXEC_SYNC_POINT != NULL) ?
		new ExecutionSynchronizationPoint( *(anED.mEXEC_SYNC_POINT) ) : NULL )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionData()
	{
		delete( mEXEC_SYNC_POINT );
	}


	/**
	 * resize
	 */
	void resize(avm_size_t newMachineCount)
	{
		mTableOfRuntime.makeWritableResize( newMachineCount );

		mTableOfRFStateFlags.makeWritable();
		mTableOfRFStateFlags->resize(newMachineCount);
	}


	/**
	 * GETTER - SETTER
	 * mExecutionContext
	 */
	inline ExecutionContext * getExecutionContext() const
	{
		return( mExecutionContext );
	}

	inline bool hasExecutionContext() const
	{
		return( mExecutionContext != NULL );
	}

	inline void setExecutionContext(ExecutionContext * anExecutionContext)
	{
		mExecutionContext = anExecutionContext;
	}


	/**
	 * GETTER
	 * mPathCondition  &&  mPathTimedCondition
	 */
	inline BF getAllPathCondition() const
	{
		if( mPathTimedCondition.valid()
			&& mPathTimedCondition.isNotEqualTrue() )
		{
			return( ExpressionConstructor::andExpr(
					mPathCondition, mPathTimedCondition) );
		}
		else
		{
			return( mPathCondition );
		}
	}


	inline BF andPathTimedCondition(const BF & aCondition) const
	{
		if( mPathTimedCondition.valid() )
		{
			if( mPathTimedCondition.isEqualTrue() )
			{
				return( aCondition );
			}
			else if( mPathTimedCondition.isEqualFalse() )
			{
				return( mPathTimedCondition );
			}

			return( ExpressionConstructor::andExpr(
					mPathTimedCondition, aCondition) );
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
		return( mPathCondition );
	}

	inline bool hasPathCondition() const
	{
		return( mPathCondition.valid() );
	}

	inline void setPathCondition(const BF & aPathCondition)
	{
		mPathCondition = aPathCondition;
	}


	/**
	 * GETTER - SETTER
	 * mPathTimedCondition
	 */
	inline const BF & getPathTimedCondition() const
	{
		return( mPathTimedCondition );
	}

	inline bool hasPathTimedCondition() const
	{
		return( mPathTimedCondition.valid() );
	}

	inline void setPathTimedCondition(const BF & aPathTimedCondition)
	{
		mPathTimedCondition = aPathTimedCondition;
	}



	/**
	 * GETTER
	 * mNodeCondition  &&  mNodeTimedCondition
	 */
	inline BF getAllNodeCondition() const
	{
		if( mNodeTimedCondition.valid() && mNodeTimedCondition.isNotEqualTrue() )
		{
			return( ExpressionConstructor::andExpr(
					mNodeCondition, mNodeTimedCondition) );
		}
		else
		{
			return( mNodeCondition );
		}
	}


	/**
	 * GETTER - SETTER
	 * mNodeCondition
	 */
	inline const BF & getNodeCondition() const
	{
		return( mNodeCondition );
	}

	inline bool hasNodeCondition() const
	{
		return( mNodeCondition.valid() );
	}

	inline void setNodeCondition(const BF & aCondition)
	{
		mNodeCondition = aCondition;
	}


	/**
	 * GETTER - SETTER
	 * mNodeTimedCondition
	 */
	inline const BF & getNodeTimedCondition() const
	{
		return( mNodeTimedCondition );
	}

	inline bool hasNodeTimedCondition() const
	{
		return( mNodeTimedCondition.valid() );
	}

	inline void setNodeTimedCondition(const BF & aTimedCondition)
	{
		mNodeTimedCondition = aTimedCondition;
	}


	/**
	 * GETTER - SETTER
	 * mGlobalNodeConditionEnabledFlag
	 * mLocalNodeConditionEnabledFlag
	 */
	inline bool isEnabledNodeCondition() const
	{
		return( mGlobalNodeConditionEnabledFlag ||
				mLocalNodeConditionEnabledFlag );
	}

	inline void setEnabledGlobalNodeCondition(bool aCondition = true)
	{
		mGlobalNodeConditionEnabledFlag = aCondition;
	}

	inline void setEnabledLocalNodeCondition(bool aCondition = true)
	{
		mLocalNodeConditionEnabledFlag = aCondition;
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & os) const;

	inline std::string str() const
	{
		return( strStateConf() );
	}

	void toStreamData(OutStream & os) const;

	void toFscn(OutStream & os, const ExecutionData * aPreviousExecData) const;


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
			OutStream & os, const RuntimeForm & aRF) const;

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
			OutStream & os, const RuntimeForm & aRF,
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

	void toStreamStateConf(OutStream & os, const RuntimeForm & aRF,
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
			OutStream & os, const RuntimeForm & aRF) const;


	/**
	 * GETTER - SETTER
	 * mRunnableElementTrace
	 */
	inline BF & getRunnableElementTrace()
	{
		return( mRunnableElementTrace );
	}

	inline const BF & getRunnableElementTrace() const
	{
		return( mRunnableElementTrace );
	}

	inline bool hasRunnableElementTrace() const
	{
		return( mRunnableElementTrace.valid() );
	}

	inline void setRunnableElementTrace(const BF & aRunnableElementTrace)
	{
		mRunnableElementTrace = aRunnableElementTrace;
	}


	/**
	 * GETTER - SETTER
	 * mIOElementTrace
	 */
	inline BF & getIOElementTrace()
	{
		return( mIOElementTrace );
	}

	inline const BF & getIOElementTrace() const
	{
		return( mIOElementTrace );
	}

	inline bool hasIOElementTrace() const
	{
		return( mIOElementTrace.valid() );
	}

	inline void setIOElementTrace(const BF & anIOElementTrace)
	{
		mIOElementTrace = anIOElementTrace;
	}


	/**
	 * GETTER
	 * mRunnableElementTrace
	 * mIOElementTrace
	 */
//$DELETE
	inline bool notEvaluated() const
	{
		return( mRunnableElementTrace.invalid()
				&& mIOElementTrace.invalid() );
	}


	/**
	 * GETTER - SETTER
	 * mOnInit
	 */
	inline const BFCode & getOnInit() const
	{
		return( mOnInit );
	}

	inline bool hasOnInit() const
	{
		return( mOnInit.valid() );
	}

	inline void setOnInit(const BFCode & onInit)
	{
		mOnInit = onInit;
	}


	/**
	 * GETTER - SETTER
	 * mOnSchedule
	 */
	inline const BFCode & getOnSchedule() const
	{
		return( mOnSchedule );
	}

	inline bool hasOnSchedule() const
	{
		return( mOnSchedule.valid() );
	}

	inline void setOnSchedule(const BFCode & onSchedule)
	{
		mOnSchedule = onSchedule;
	}


	/**
	 * GETTER - SETTER
	 * mTableOfRuntimeForm
	 */
	inline const TableOfRuntimeT & getTableOfRuntime() const
	{
		return( mTableOfRuntime );
	}


	inline RuntimeForm & getRuntime(avm_size_t offset)
	{
		return( mTableOfRuntime.ref(offset) );
	}

	inline const RuntimeForm & getRuntime(avm_size_t offset) const
	{
		return( mTableOfRuntime.ref(offset) );
	}


	inline RuntimeForm & getRuntime(const RuntimeID & aRID)
	{
		return( mTableOfRuntime.ref( aRID.getOffset() ) );
	}

	inline const RuntimeForm & getRuntime(const RuntimeID & aRID) const
	{
		return( mTableOfRuntime.ref( aRID.getOffset() ) );
	}


	inline const RuntimeForm * ptrRuntime(avm_size_t offset) const
	{
		return( mTableOfRuntime.at(offset) );
	}

	inline RuntimeForm * ptrRuntime(const RuntimeID & aRID)
	{
		return( mTableOfRuntime.at( aRID.getOffset() ) );
	}

	inline const RuntimeForm * ptrRuntime(const RuntimeID & aRID) const
	{
		return( mTableOfRuntime.at( aRID.getOffset() ) );
	}


	inline const RuntimeID & getRuntimeID(avm_size_t rid) const
	{
		return( mTableOfRuntime.at(rid)->getRID() );
	}

	const RuntimeID & getRuntimeID(const ExecutableForm * anExecutable) const;

	const RuntimeID & getRuntimeID(InstanceOfMachine * anInstance) const;

	const RuntimeID & getRuntimeID(
			const std::string & aFullyQualifiedNameID) const;

	const RuntimeID & getRuntimeIDByNameID(const std::string & aNameID) const;


	RuntimeID getRuntimeContainerRID(const RuntimeID & aRID,
			BaseInstanceForm * anInstance) const;

	RuntimeID getRuntimeContainerRID(BaseInstanceForm * anInstance) const
	{
		return( getRuntimeContainerRID(mRID, anInstance) );
	}


	inline const BFCode & getRuntimeFormOnSchedule(const RuntimeID & aRID) const
	{
		return( mTableOfRuntime.at(aRID.getOffset())->getOnSchedule() );
	}

	inline const BFCode & getRuntimeFormOnDefer(const RuntimeID & aRID) const
	{
		return( mTableOfRuntime.at(aRID.getOffset())->getOnDefer() );
	}



	// assign <==> release_acquire
	inline void saveRuntimeForm(avm_size_t offset, RuntimeForm * aRF) const
	{
		mTableOfRuntime.set(offset, aRF);
	}

	// assign <==> release_acquire
	inline void assignRuntimeForm(avm_size_t offset, RuntimeForm * aRF) const
	{
		mTableOfRuntime.assign(offset, aRF);
	}


	/***************************************************************************
	 ***************************************************************************
	 * GETTER - SETTER
	 * mTableOfRuntime
	 *
	 * make writable
	 ***************************************************************************
	 */
	inline RuntimeForm & getWritableRuntime(const RuntimeID & aRID)
	{
		return( mTableOfRuntime.refWritable( aRID.getOffset() ) );
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
	inline const APTableOfRuntimeFormState & getRuntimeFormStateTable() const
	{
		return( mTableOfRFStateFlags );
	}


	inline PROCESS_EVAL_STATE getRuntimeFormState(avm_size_t rid) const
	{
		return( mTableOfRFStateFlags->stateAt(rid) );
	}

	inline  PROCESS_EVAL_STATE getRuntimeFormState(
			const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->stateAt( aRID.getOffset() ) );
	}

	bool checkRunningForm(
			const BF & aRunnableElementTrace, const RuntimeID & aRID);


	// CREATED STATE
	inline bool isCreated(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isCreated( aRID.getOffset() ) );
	}

	// LOADED STATE
	inline bool isLoaded(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isLoaded( aRID.getOffset() ) );
	}

	// STARTING STATE
	inline bool isStarting(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isStarting( aRID.getOffset() ) );
	}

	inline bool isIniting(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isIniting( aRID.getOffset() ) );
	}

	// STOPPING STATE
	inline bool isStopping(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isStopping( aRID.getOffset() ) );
	}

	// STOPPED STATE
	inline bool isStopped(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isStopped( aRID.getOffset() ) );
	}

	// FINALIZING STATE
	inline bool isFinalizing(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isFinalizing( aRID.getOffset() ) );
	}

	// FINALIZED STATE
	inline bool isFinalized(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isFinalized( aRID.getOffset() ) );
	}

	// DESTROYED STATE
	inline bool isDestroyed(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isDestroyed( aRID.getOffset() ) );
	}

	// FINALIZED or DESTROYED STATE
	inline bool isFinalizedOrDestroyed(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->
				isFinalizedOrDestroyed( aRID.getOffset() ) );
	}

	// ALIVE STATE
	inline bool isAlive(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isAlive( aRID.getOffset() ) );
	}

	// SUPENDED STATE
	inline bool isSuspended(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isSuspended( aRID.getOffset() ) );
	}

	// WAITING STATE
	inline bool isWaiting(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isWaiting( aRID.getOffset() ) );
	}

	// WAITING JOIN STATE
	inline bool isWaitingJoin(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isWaitingJoin( aRID.getOffset() ) );
	}

	// DISABLE STATE
	inline bool isDisable(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isDisable( aRID.getOffset() ) );
	}

	// DISABLE STATE
	inline bool isAborted(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isAborted( aRID.getOffset() ) );
	}

	// DISABLE or ABORTED STATE
	inline bool isDisableOrAborted(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isDisableOrAborted( aRID.getOffset() ) );
	}

	// IDLE STATE
	inline bool isIdle() const
	{
		return( mTableOfRFStateFlags->isIdle( mRID.getOffset() ) );
	}

	inline bool isIdle(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isIdle( aRID.getOffset() ) );
	}

	// RUNNING STATE
	inline bool isRunning(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isRunning( aRID.getOffset() ) );
	}

	// IDLE or RUNNING STATE
	inline bool isIdleOrRunning(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isIdleOrRunning( aRID.getOffset() ) );
	}

	// RUNNABLE STATE
	inline bool isRunnable(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isRunnable( aRID.getOffset() ) );
	}

	inline bool isunRunnable(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isunRunnable( aRID.getOffset() ) );
	}

	inline bool isunRunnableSystem() const
	{
		return( mTableOfRFStateFlags->isunRunnable( SYSTEM_RUNTIME_OFFSET ) );
	}

	// CREATED or RUNNABLE STATE
	inline bool isCreatedOrRunnable(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isCreatedOrRunnable( aRID.getOffset() ) );
	}

	// DEFINED / UNDEFINED STATE
	inline bool isDefinedPES(const RuntimeID & aRID) const
	{
		return( mTableOfRFStateFlags->isDefined( aRID.getOffset() ) );
	}

	inline bool isUndefinedPES(avm_offset_t offset) const
	{
		return( mTableOfRFStateFlags->isUndefined( offset ) );
	}

	inline void makeWritableRuntimeFormStateTable()
	{
		mTableOfRFStateFlags.makeWritable();
	}

	inline void mwsetRuntimeFormState(const RuntimeID & aRID,
			PROCESS_EVAL_STATE aPES)
	{
		makeWritableRuntimeFormStateTable();

		mTableOfRFStateFlags->stateSet(aRID.getOffset(), aPES);
	}

	inline void setRuntimeFormState(const RuntimeID & aRID,
			PROCESS_EVAL_STATE aPES)
	{
		mTableOfRFStateFlags->stateSet(aRID.getOffset(), aPES);
	}


	inline void mwsetRuntimeFormState(avm_size_t rid,
			PROCESS_EVAL_STATE aPES)
	{
		makeWritableRuntimeFormStateTable();

		mTableOfRFStateFlags->stateSet(rid, aPES);
	}

	inline void setRuntimeFormState(avm_size_t rid,
			PROCESS_EVAL_STATE aPES)
	{
		mTableOfRFStateFlags->stateSet(rid, aPES);
	}


	// ASSIGNABILITY
	inline Bitset * getAssigned(avm_size_t rid) const
	{
		return( mTableOfRFStateFlags->getAssigned(rid) );
	}

	inline bool isAssigned(const RuntimeID & aRID, avm_size_t rid) const
	{
		return( mTableOfRFStateFlags->isAssigned(aRID.getOffset(), rid) );
	}


	inline void mwsetAssigned(const RuntimeID & aRID,
			avm_offset_t varOffset, bool flag = true)
	{
		makeWritableRuntimeFormStateTable();

		mTableOfRFStateFlags->setAssigned(*this,
				aRID.getOffset(), varOffset, flag);
	}

	inline void setAssigned(const RuntimeID & aRID,
			avm_offset_t varOffset, bool flag = true)
	{
		mTableOfRFStateFlags->setAssigned(*this,
				aRID.getOffset(), varOffset, flag);
	}


	/**
	 * GETTER
	 * mTableOfAssignedFlag
	 */
	TableOfRuntimeFormState::TableOfAssignedFlag getTableOfAssignedFlag()
	{
		return( mTableOfRFStateFlags->getTableOfAssignedFlag() );
	}

	void setTableOfAssignedFlag(
			TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag)
	{
		mTableOfRFStateFlags->setTableOfAssignedFlag( aTableOfAssignedFlag );
	}


	/**
	 * GETTER
	 * mSaveTableOfAssignedFlag
	 */
	TableOfRuntimeFormState::
	TableOfAssignedFlag getSaveTableOfAssignedFlag() const;

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
	inline void createLocalRuntimeStack()
	{
		mStackOfLocalRuntime =
				APStackOfLocalRuntime( new StackOfLocalRuntime() );
	}

	inline void destroyLocalRuntimeStack()
	{
		mStackOfLocalRuntime.destroy();
	}

	inline APStackOfLocalRuntime & getLocalRuntimes()
	{
		return( mStackOfLocalRuntime );
	}

	inline const APStackOfLocalRuntime & getLocalRuntimes() const
	{
		return( mStackOfLocalRuntime );
	}


	inline bool hasLocalRuntime() const
	{
		return( mStackOfLocalRuntime.valid()
				&& mStackOfLocalRuntime->nonempty() );
	}

	inline bool hasLocalRuntimeStack() const
	{
		return( mStackOfLocalRuntime.valid() );
	}

	inline void makeWritableLocalRuntimeStack()
	{
		if( mStackOfLocalRuntime.valid() )
		{
			mStackOfLocalRuntime.makeWritable();
		}
		else
		{
			mStackOfLocalRuntime.replacePointer( new StackOfLocalRuntime() );
		}
	}

	inline void setLocalRuntime(avm_size_t offset,
			const LocalRuntime & aLocalRuntime)
	{
		mStackOfLocalRuntime->setLocalRuntime(offset, aLocalRuntime);
	}


	/**
	 * GETTER - SETTER
	 * mParametersRuntimeForm
	 */
	inline const ParametersRuntimeForm & getParametersRuntimeForm() const
	{
		return( static_cast< const ParametersRuntimeForm & >(
				mTableOfRuntime.ref(PARAM_MACHINE_RUNTIME_OFFSET) ) );
	}

	inline ParametersRuntimeForm & getWritableParametersRuntimeForm()
	{
		ParametersRuntimeForm & pRF = static_cast< ParametersRuntimeForm & >(
				mTableOfRuntime.refWritable(PARAM_MACHINE_RUNTIME_OFFSET) );

		pRF.resetOffset();

		return( pRF );

//		return( static_cast< ParametersRuntimeForm & >(
//				mTableOfRuntime.refWritable(
//						PARAM_MACHINE_RUNTIME_OFFSET) ) );
	}

	inline BF bfParametersRuntimeForm() const
	{
		return(  mTableOfRuntime.to_sp< BF >( PARAM_MACHINE_RUNTIME_OFFSET ) );
	}


	inline const RuntimeID & getParametersRID() const
	{
		return( getRuntime(PARAM_MACHINE_RUNTIME_OFFSET).getRID() );
	}

	inline const BF & saveParameter(InstanceOfData * anInstance)
	{
		return( getWritableParametersRuntimeForm().saveParameter(anInstance) );
	}

	inline void appendParameters(BFList & paramList)
	{
		getWritableParametersRuntimeForm().appendParameters(paramList);
	}


	inline void saveParametersRuntimeForm(
			ParametersRuntimeForm * paramsRF) const
	{
		mTableOfRuntime.set(PARAM_MACHINE_RUNTIME_OFFSET, paramsRF);
	}

	inline void assignParametersRuntimeForm(
			ParametersRuntimeForm * paramsRF) const
	{
		mTableOfRuntime.assign(PARAM_MACHINE_RUNTIME_OFFSET, paramsRF);
	}

	inline void assignParametersRuntimeForm(const BF & paramsRF) const
	{
		mTableOfRuntime.assign(PARAM_MACHINE_RUNTIME_OFFSET,
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
		return( mRID );
	}

	inline void setRID(const RuntimeID & aRID)
	{
		mRID = aRID;
	}

	/*
	 * GETTER - SETTER
	 * Avm Ending Execution Status
	 */
	inline AVM_EXEC_ENDING_STATUS getAEES() const
	{
		return( mAEES );
	}

	inline void setAEES(AVM_EXEC_ENDING_STATUS anAEES)
	{
		mAEES = anAEES;
	}


	/*
	 * GETTER - SETTER
	 * Avm Execution Synchronization Point
	 */
	inline void pushExecSyncPoint(
			ExecutionSynchronizationPoint * anExecSyncPoint)
	{
		if( mEXEC_SYNC_POINT == NULL  )
		{
			mEXEC_SYNC_POINT = anExecSyncPoint;
		}
		else
		{
			ExecutionSynchronizationPoint * lastESP = mEXEC_SYNC_POINT;
			while( lastESP->next != NULL )
			{
				lastESP = lastESP->next;
			}
			lastESP->next = anExecSyncPoint;
		}
	}


	/**
	 * INSTANCIATION BOUND TEST
	 */
	bool couldBeInstanciated(InstanceOfMachine * anInstance) const;


	/**
	 * COMPARISON
	 * OPERATOR
	 *
	 * TRIVIAL EQUALITY
	 */
	virtual bool isTEQ(const ExecutionData * anED) const
	{
		if( this == anED )
		{
			return( true );
		}
		else if( mTableOfRFStateFlags->equalsState(
				anED->mTableOfRFStateFlags ) )
		{
			return( (mTableOfRuntime == anED->mTableOfRuntime)
					&& mPathCondition.isTEQ(anED->mPathCondition)
					&& mPathTimedCondition.isTEQ(anED->mPathTimedCondition)
					&& (mStackOfLocalRuntime == anED->mStackOfLocalRuntime) );
		}
		return( false );
	}

	inline bool isTNEQ(const ExecutionData * anED) const
	{
		return( not isTEQ( anED ) );
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AVM SMART POINTER FOR ExecutionData
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


#define AVM_DEBUG_EXECUTION_DATA_POINTER  true
#undef AVM_DEBUG_EXECUTION_DATA_POINTER

#if defined(AVM_DEBUG_EXECUTION_DATA_POINTER)

	#define AVM_DECLARE_DEBUG_EXECUTION_DATA_PTR const ExecutionData * debugPTR;

	#define AVM_INIT_DEBUG_EXECUTION_DATA_PTR( ptr )  , debugPTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_EXECUTION_DATA_PTR( ptr )  debugPTR = ptr;

	#define AVM_ASSIGN_EXPR_DEBUG_EXECUTION_DATA_PTR( ptr )   debugPTR = ptr

#else

	#define AVM_DECLARE_DEBUG_EXECUTION_DATA_PTR

	#define AVM_INIT_DEBUG_EXECUTION_DATA_PTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_EXECUTION_DATA_PTR( ptr )

	#define AVM_ASSIGN_EXPR_DEBUG_EXECUTION_DATA_PTR( ptr )  ptr

#endif


class APExecutionData :
		public AvmPointer< ExecutionData , DestroyElementPolicy >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef  AvmPointer< ExecutionData , DestroyElementPolicy > base_this_type;


protected:
	/**
	 * Only for debug facilities
	 */
	AVM_DECLARE_DEBUG_EXECUTION_DATA_PTR


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	APExecutionData()
	: base_this_type( )
	AVM_INIT_DEBUG_EXECUTION_DATA_PTR( NULL )
	{
		//!!! NOTHING
	}

	explicit APExecutionData(ExecutionData * anED)
	: base_this_type( AVM_ASSIGN_EXPR_DEBUG_EXECUTION_DATA_PTR( anED ) )
	{
		//!!! NOTHING
	}



	/**
	 * DESTRUCTOR
	 */
	virtual ~APExecutionData()
	{
		//!!! NOTHING
	}


	/**
	 * resize
	 */
	void resize(avm_size_t newMachineCount)
	{
		makeWritable();

		raw_pointer()->resize(newMachineCount);
	}


	/**
	 * GETTER
	 * the Previous ExecutionData
	 */
	APExecutionData & getPrevious();

	const APExecutionData & getPrevious() const;

	bool hasPrevious() const;


	inline void mwsetPathCondition(const BF & mCondition)
	{
		makeWritable();

		raw_pointer()->setPathCondition( mCondition );

	}

	inline void mwsetPathTimedCondition(const BF & mCondition)
	{
		makeWritable();

		raw_pointer()->setPathTimedCondition( mCondition );

	}


	/**
	 * SETTER
	 * make Modifiable
	 */
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

		raw_pointer()->makeWritableLocalRuntimeStack();

		aLocalRuntime.makeWritable();

		raw_pointer()->setLocalRuntime(
				aLocalRuntime.getOffset() , aLocalRuntime );
	}


	inline RuntimeForm & getWritableRuntime(const RuntimeID & aRID)
	{
		makeWritable();

		return( raw_pointer()->getWritableRuntime(aRID) );

	}

	inline APTableOfData & getWritableRuntimeDataTable(const RuntimeID & aRID)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
			raw_pointer()->getRuntime(aRID).hasDataTable() )
				<< "Unexpected RuntimeForm without data !!!"
				<< SEND_EXIT;

		makeWritable();

		return( raw_pointer()->getWritableRuntime(aRID).getWritableDataTable() );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfRFStateFlags
	 */

	inline void mwsetRuntimeFormState(
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES)
	{
		makeWritable();

		raw_pointer()->mwsetRuntimeFormState(aRID.getOffset(), aPES);
	}

	inline void mwsetRuntimeFormState(PROCESS_EVAL_STATE aPES)
	{
		mwsetRuntimeFormState(raw_pointer()->mRID, aPES);
	}

	inline void mwsetRuntimeFormState(const RuntimeID & aRID,
			PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES)
	{
		makeWritable();

		if( raw_pointer()->getRuntimeFormState(aRID) == oldPES )
		{
			raw_pointer()->mwsetRuntimeFormState(aRID.getOffset(), aPES);

			raw_pointer()->setAEES( RuntimeDef::PES_to_AEES(
					aPES, raw_pointer()->getAEES() ) );
		}
	}


	/**
	 * SETTER
	 * mOnSchedule
	 */
	inline void mwsetRuntimeFormOnSchedule(
			const RuntimeID & aRID, const BFCode & onSchedule)
	{
		if( aRID.getExecutable()->isMutableSchedule() &&
			(onSchedule != raw_pointer()->getRuntime(aRID).getOnSchedule()) )
		{
			makeWritable();

			raw_pointer()->getWritableRuntime(aRID).setOnSchedule( onSchedule );
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

		if( not raw_pointer()->isIdle() )
		{
			raw_pointer()->mwsetRuntimeFormState(aRID, PROCESS_IDLE_STATE);
		}
	}


	/**
	 * SETTER
	 * mDefer
	 */
	inline void mwsetRuntimeFormOnDefer(
			const RuntimeID & aRID, const BFCode & onDefer)
	{
		makeWritable();

		raw_pointer()->getWritableRuntime( aRID ).setOnDefer( onDefer );
	}


	/*
	 * GETTER - SETTER
	 * Avm Execution Synchronization Point
	 */
	inline void pushExecSyncPoint(
			ExecutionSynchronizationPoint * anExecSyncPoint)
	{
		makeWritable();

		raw_pointer()->pushExecSyncPoint( anExecSyncPoint );
	}

	/*
	 * SETTER
	 * Avm Ending Execution Status
	 */
	inline void mwsetAEES(AVM_EXEC_ENDING_STATUS anAEES)
	{
		makeWritable();

		raw_pointer()->setAEES( anAEES );
	}


	/**
	 * SETTER
	 * mIOElementTrace
	 */
	inline void mwsetIOElementTrace(const BF & anIOElementTrace)
	{
		makeWritable();

		raw_pointer()->setIOElementTrace( anIOElementTrace );
	}


	/**
	 * SETTER
	 * mRunnableElementTrace
	 */
	inline void mwsetRunnableElementTrace(const BF & aRunnableElementTrace)
	{
		makeWritable();

		raw_pointer()->setRunnableElementTrace(aRunnableElementTrace);
	}


	/**
	 * SETTER
	 * mRID
	 */

	inline void mwsetRID(const RuntimeID & aRID)
	{
		makeWritable();
		raw_pointer()->setRID( aRID );
	}



	/**
	 * GETTER - SETTER
	 * mParametersRuntimeForm
	 */
	inline const BF & saveParameter(InstanceOfData * anInstance)
	{
		makeWritable();

		return( raw_pointer()->saveParameter(anInstance) );
	}

	inline void appendParameters(BFList & paramList)
	{
		makeWritable();

		raw_pointer()->appendParameters(paramList);
	}


	inline ParametersRuntimeForm & getWritableParametersRuntimeForm()
	{
		makeWritable();

		return( raw_pointer()->getWritableParametersRuntimeForm() );
	}




	/**
	 * COMPARISON
	 * OPERATOR
	 *
	 * TRIVIAL EQUALITY
	 */
	inline bool isTEQ(const APExecutionData & prevED)
	{
		return( raw_pointer()->isTEQ( prevED.raw_pointer() ) );
	}

	inline bool isTNEQ(const APExecutionData & prevED)
	{
		return( raw_pointer()->isTNEQ( prevED.raw_pointer() ) );
	}


	/**
	 * DEFAULT NULL
	 */
	static APExecutionData REF_NULL;

};


////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for CONTAINER
////////////////////////////////////////////////////////////////////////////////

typedef Collection< APExecutionData >        CollectionOfAPExecutionData;

typedef List      < APExecutionData >        ListOfAPExecutionData;

typedef Vector    < APExecutionData >        VectorOfAPExecutionData;

typedef Vector    < ListOfAPExecutionData >  VectorOfListOfAPExecutionData;


}

#endif /*EXECUTIONDATA_H_*/
