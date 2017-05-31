/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TABLEOFRUNTIMEFORMSTATE_H_
#define TABLEOFRUNTIMEFORMSTATE_H_

#include <common/AvmObject.h>

#include <common/AvmPointer.h>

#include <collection/Bitset.h>

#include <fml/runtime/RuntimeDef.h>


namespace sep
{


class ExecutionData;


class TableOfRuntimeFormState  :
		public AvmObject,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfRuntimeFormState )
{

	AVM_DECLARE_CLONABLE_CLASS( TableOfRuntimeFormState )


public:
	/**
	 * TYPEDEF
	 */
	typedef Bitset * * TableOfAssignedFlag;

protected :
	/**
	 * ATTRIBUTES
	 */
	avm_size_t mSize;

	PROCESS_EVAL_STATE * mEvalState;

	TableOfAssignedFlag mTableOfAssignedFlag;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfRuntimeFormState(avm_size_t aSize)
	: AvmObject( ),
	mSize( aSize ),
	mEvalState( NULL ),
	mTableOfAssignedFlag( NULL )
	{
		allocTableOfState();
		resetTableOfState();
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TableOfRuntimeFormState(const TableOfRuntimeFormState & aTable)
	: AvmObject( aTable ),
	mSize( aTable.mSize ),
	mEvalState( NULL ),
	mTableOfAssignedFlag( NULL )
	{
		allocTableOfState( aTable.mEvalState );

		if( aTable.mTableOfAssignedFlag != NULL )
		{
			allocAssignedFlag( aTable.mTableOfAssignedFlag );
		}
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TableOfRuntimeFormState()
	{
		delete [] mEvalState;

		destroyAssignedFlags();
	}


	/**
	 * ALLOCATE
	 * reset
	 */
	inline void reset(const TableOfRuntimeFormState & aTable,
			bool assignedResetFlag = true)
	{
		if( assignedResetFlag )
		{
			destroyAssignedFlags();
		}

		if( mSize == aTable.mSize  )
		{
			resetTableOfState( aTable.mEvalState );
		}
		else
		{
			mSize = aTable.mSize;

			delete [] mEvalState;

			allocTableOfState( aTable.mEvalState );
		}

		if( assignedResetFlag && (aTable.mTableOfAssignedFlag != NULL) )
		{
			allocAssignedFlag( aTable.mTableOfAssignedFlag );
		}
	}


	/**
	 * GETTER - SETTER
	 * mSize
	 */
	inline avm_size_t size() const
	{
		return( mSize );
	}

	inline bool nonempty() const
	{
		return( mSize > 0 );
	}


	void resize(avm_size_t newSize);


	/**
	 * ALLOCATE - GETTER - SETTER
	 * mEvalState
	 */
	inline void allocTableOfState()
	{
		mEvalState = ( mSize > 0 ) ?
				( new PROCESS_EVAL_STATE[ mSize ] ) : NULL;
	}


	inline void allocTableOfState(PROCESS_EVAL_STATE * tableOfState)
	{
		mEvalState = ( mSize > 0 ) ?
				( new PROCESS_EVAL_STATE[ mSize ] ) : NULL;

		resetTableOfState(tableOfState);
	}


	inline void resetTableOfState(
			PROCESS_EVAL_STATE value = PROCESS_UNDEFINED_STATE)
	{
		for( avm_size_t i = 0 ; i != mSize ; ++i )
		{
			mEvalState[i] = value;
		}
	}

	inline void resetTableOfState(PROCESS_EVAL_STATE * tableOfState)
	{
		for( avm_size_t i = 0 ; i != mSize ; ++i )
		{
			mEvalState[i] = tableOfState[i];
		}
	}


	/**
	 * GETTER - SETTER
	 * mEvalState
	 */
	inline PROCESS_EVAL_STATE * getEvalState() const
	{
		return( mEvalState );
	}

	inline PROCESS_EVAL_STATE stateAt(avm_size_t rid) const
	{
		return( mEvalState[rid] );
	}

	inline PROCESS_EVAL_STATE stateGet(avm_size_t rid) const
	{
		return( mEvalState[rid] );
	}

	inline void stateSet(avm_size_t rid, PROCESS_EVAL_STATE aEvalState)
	{
		mEvalState[rid] = aEvalState;
	}


	/**
	 * TEST
	 * mEvalState
	 */
	inline bool isCreating(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_CREATING_STATE );
	}

	inline bool isCreated(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_CREATED_STATE );
	}

	inline bool isLoaded(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_LOADED_STATE );
	}


	inline bool isStarting(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_STARTING_STATE );
	}

	inline bool isIniting(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_INITING_STATE );
	}


	inline bool isStopping(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_STOPPING_STATE );
	}

	inline bool isStopped(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_STOPPED_STATE );
	}


	inline bool isFinalizing(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_FINALIZING_STATE );
	}

	inline bool isFinalized(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_FINALIZED_STATE );
	}

	inline bool isDestroyed(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_DESTROYED_STATE );
	}

	inline bool isFinalizedOrDestroyed(avm_offset_t offset) const
	{
		return( (mEvalState[offset] == PROCESS_FINALIZED_STATE) ||
//				(mEvalState[offset] == PROCESS_CREATED_STATE  ) || // TODO !?!
				(mEvalState[offset] == PROCESS_DESTROYED_STATE) );
	}

	inline bool isAlive(avm_offset_t offset) const
	{
		return( (mEvalState[offset] != PROCESS_FINALIZED_STATE) &&
				(mEvalState[offset] != PROCESS_DESTROYED_STATE) );
	}


	inline bool isSuspended(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_SUSPENDED_STATE );
	}

	inline bool isWaiting(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_WAITING_STATE );
	}

	inline bool isWaitingJoin(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_WAITING_JOIN_STATE );
	}


	inline bool isAborted(avm_offset_t offset) const
	{
		return( (mEvalState[offset] == PROCESS_ABORTED_STATE) );
	}

	inline bool isDisable(avm_offset_t offset) const
	{
		return( (mEvalState[offset] == PROCESS_DISABLED_STATE) );
	}


	inline bool isDisableOrAborted(avm_offset_t offset) const
	{
		return( (mEvalState[offset] == PROCESS_DISABLED_STATE) ||
				(mEvalState[offset] == PROCESS_ABORTED_STATE));
	}


	inline bool isIdle(avm_offset_t offset) const
	{
		return( (mEvalState[offset] == PROCESS_IDLE_STATE) );
	}


	inline bool isRunning(avm_offset_t offset) const
	{
		return( (mEvalState[offset] == PROCESS_RUNNING_STATE) ||
				(mEvalState[offset] == PROCESS_RTC_STATE) );
	}


	inline bool isIdleOrRunning(PROCESS_EVAL_STATE aState) const
	{
		return( (aState == PROCESS_IDLE_STATE)    ||
				(aState == PROCESS_RUNNING_STATE) ||
				(aState == PROCESS_RTC_STATE) );
	}

	inline bool isnotIdleOrRunning(PROCESS_EVAL_STATE aState) const
	{
		return( (aState != PROCESS_IDLE_STATE)    &&
				(aState != PROCESS_RUNNING_STATE) &&
				(aState != PROCESS_RTC_STATE) );
	}

	inline bool isIdleOrRunning(avm_offset_t offset) const
	{
		return( isIdleOrRunning(mEvalState[offset]) );
	}


	// DEFINED / UNDEFINED STATE
	inline bool isDefined(avm_offset_t offset) const
	{
		return( mEvalState[offset] != PROCESS_UNDEFINED_STATE );
	}

	inline bool isUndefined(avm_offset_t offset) const
	{
		return( mEvalState[offset] == PROCESS_UNDEFINED_STATE );
	}


	/**
	 * TEST
	 * mEvalState
	 */
	inline bool isRunnable(avm_offset_t offset) const
	{
		switch( mEvalState[offset] )
		{
			case PROCESS_IDLE_STATE:
			case PROCESS_RUNNING_STATE:
			case PROCESS_RTC_STATE:
			case PROCESS_DISABLED_STATE:
			case PROCESS_ABORTED_STATE:
			case PROCESS_INITING_STATE:
			case PROCESS_STARTING_STATE:
			case PROCESS_LOADED_STATE:
			{
				return( true );
			}

			default:
			{
				return( false );
			}
		}
	}


	inline bool isunRunnable(avm_offset_t offset) const
	{

		switch( mEvalState[offset] )
		{
			case PROCESS_FINALIZED_STATE:
			case PROCESS_DESTROYED_STATE:
			{
				return( true );
			}

			default:
			{
				return( false );
			}
		}
	}


	// CREATED or RUNNABLE STATE
	inline bool isCreatedOrRunnable(avm_offset_t offset) const
	{
		return( isCreated(offset) || isRunnable(offset) );
	}


	/**
	 * COMPARISON
	 */
	bool equalsState(TableOfRuntimeFormState * other) const;


	inline bool isEQ(PROCESS_EVAL_STATE oneState,
			PROCESS_EVAL_STATE otherState) const
	{
		return( (oneState == otherState)
				|| (isIdleOrRunning(oneState)
					&& isIdleOrRunning(otherState)) );
	}

	inline bool isNEQ(PROCESS_EVAL_STATE oneState,
			PROCESS_EVAL_STATE otherState) const
	{
		return( (oneState != otherState)
				&& (isnotIdleOrRunning(oneState)
					|| isnotIdleOrRunning(otherState)) );
	}


	/*
	 ***************************************************************************
	 * RESET - ALLOCATION :> mTableOfAssignedFlag
	 ***************************************************************************
	 */
	inline TableOfAssignedFlag getTableOfAssignedFlag() const
	{
		return( mTableOfAssignedFlag );
	}

	inline void setTableOfAssignedFlag(TableOfAssignedFlag aTableOfAssignedFlag)
	{
		mTableOfAssignedFlag = aTableOfAssignedFlag;
	}


	// GLOBAL TABLE
	inline void destroyAssignedFlags()
	{
		if( mTableOfAssignedFlag != NULL )
		{
			for( avm_size_t i = 0 ; i < mSize ; ++i )
			{
				delete mTableOfAssignedFlag[i];
			}

			delete[] mTableOfAssignedFlag;

			mTableOfAssignedFlag = NULL;
		}
	}


	inline void resetAssignedFlags()
	{
		if( mTableOfAssignedFlag != NULL )
		{
			for( avm_size_t i = 0 ; i < mSize ; ++i )
			{
				delete mTableOfAssignedFlag[i];

				mTableOfAssignedFlag[i] = NULL;
			}
		}
	}


	inline void resetAssignedFlags(Bitset * * tableOfAssignFlag)
	{
		if( mTableOfAssignedFlag != NULL )
		{
			for( avm_size_t i = 0 ; i < mSize ; ++i )
			{
				delete mTableOfAssignedFlag[i];

				mTableOfAssignedFlag[i] = ( tableOfAssignFlag[i] != NULL ) ?
						new Bitset( *(tableOfAssignFlag[i]) ) : NULL;
			}
		}
	}


	// GLOBAL TABLE
	inline void allocAssignedFlag(Bitset * * tableOfAssignFlag)
	{
		mTableOfAssignedFlag = ( mSize > 0 ) ?
				( new Bitset *[ mSize ] ) : NULL;

		for( avm_size_t i = 0 ; i < mSize ; ++i )
		{
			mTableOfAssignedFlag[i] = ( tableOfAssignFlag[i] != NULL ) ?
					( new Bitset( *(tableOfAssignFlag[i]) ) ) : NULL;
		}
	}

	inline void reallocAssignedFlag()
	{
		destroyAssignedFlags();

		mTableOfAssignedFlag = ( mSize > 0 ) ?
				( new Bitset *[ mSize ] ) : NULL;

		for( avm_size_t i = 0 ; i < mSize ; ++i )
		{
			mTableOfAssignedFlag[i] = NULL;
		}
	}


	// RF TABLE
	inline void allocAssignedFlag(avm_size_t rid, avm_size_t aSize, bool value)
	{
		reallocAssignedFlag();

		mTableOfAssignedFlag[rid] = ( aSize > 0 ) ?
				( new Bitset( aSize, value ) ) : NULL;
	}


	// ASSIGNED TEST
	inline Bitset * getAssigned(avm_size_t rid) const
	{
		if( mTableOfAssignedFlag != NULL )
		{
			return( mTableOfAssignedFlag[rid] );
		}
		return( NULL );
	}

	inline bool isAssigned(avm_size_t rid, avm_offset_t offset) const
	{
		if( mTableOfAssignedFlag != NULL )
		{
			if( mTableOfAssignedFlag[rid] != NULL )
			{
				return( (*(mTableOfAssignedFlag[rid]))[offset] );
			}
		}
		return( false );
	}


	inline bool hasAssigned() const
	{
		return( mTableOfAssignedFlag != NULL );
	}

	inline bool zeroAssigned() const
	{
		return( mTableOfAssignedFlag == NULL );
	}


	inline bool hasAssigned(avm_size_t rid) const
	{
		if( mTableOfAssignedFlag != NULL )
		{
			return( mTableOfAssignedFlag[rid] != NULL );
		}

		return( false );
	}

	inline bool zeroAssigned(avm_size_t rid) const
	{
		if( mTableOfAssignedFlag != NULL )
		{
			return( mTableOfAssignedFlag[rid] == NULL );
		}

		return( true );
	}



	void setAssigned(const ExecutionData & anED,
			avm_size_t rid, avm_size_t offset, bool flag);


	inline void setAssigned(avm_size_t rid, Bitset * assignedTable)
	{
		if( mTableOfAssignedFlag == NULL )
		{
			reallocAssignedFlag();
		}
		else if( mTableOfAssignedFlag[rid] != NULL )
		{
			delete mTableOfAssignedFlag[rid];
		}

		mTableOfAssignedFlag[rid] = ( assignedTable != NULL ) ?
				( new Bitset( *assignedTable ) ) : NULL;
	}


	void setAssignedUnion(avm_size_t rid,
			Bitset * assignedTableA, Bitset * assignedTableB);



	/**
	 * Serialization
	 */
	inline virtual std::string str() const
	{
		StringOutStream oss( AVM_STR_INDENT );

		toStream( oss << IGNORE_FIRST_TAB );

		return( oss.str() );
	}

	virtual void toStream(OutStream & os) const;

	virtual void toStream(const ExecutionData & anED, OutStream & os) const;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

AVM_DEFINE_AP_CLASS( TableOfRuntimeFormState )



}

#endif /* TABLEOFRUNTIMEFORMSTATE_H_ */
