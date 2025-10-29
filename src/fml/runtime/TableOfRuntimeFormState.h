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
#include <common/Element.h>

#include <collection/Bitset.h>

#include <fml/runtime/RuntimeDef.h>


namespace sep
{


class ExecutionData;


class TableOfRuntimeFormState final :
		public AvmObject,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfRuntimeFormState )
{

	AVM_DECLARE_CLONABLE_BASE_CLASS( TableOfRuntimeFormState )


public:
	/**
	 * TYPEDEF
	 */
	typedef Bitset * * TableOfAssignedFlag;

protected :
	/**
	 * ATTRIBUTES
	 */
	std::size_t mSize;

	PROCESS_EVAL_STATE * mEvalState;

	TableOfAssignedFlag mTableOfAssignedFlag;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfRuntimeFormState(std::size_t aSize)
	: AvmObject( ),
	mSize( aSize ),
	mEvalState( nullptr ),
	mTableOfAssignedFlag( nullptr )
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
	mEvalState( nullptr ),
	mTableOfAssignedFlag( nullptr )
	{
		allocTableOfState( aTable.mEvalState );

		if( aTable.mTableOfAssignedFlag != nullptr )
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

		if( assignedResetFlag && (aTable.mTableOfAssignedFlag != nullptr) )
		{
			allocAssignedFlag( aTable.mTableOfAssignedFlag );
		}
	}


	/**
	 * GETTER - SETTER
	 * mSize
	 */
	inline std::size_t size() const
	{
		return( mSize );
	}

	inline bool nonempty() const
	{
		return( mSize > 0 );
	}


	void resize(std::size_t newSize);


	/**
	 * ALLOCATE - GETTER - SETTER
	 * mEvalState
	 */
	inline void allocTableOfState()
	{
		mEvalState = ( mSize > 0 ) ?
				( new PROCESS_EVAL_STATE[ mSize ] ) : nullptr;
	}


	inline void allocTableOfState(PROCESS_EVAL_STATE * tableOfState)
	{
		mEvalState = ( mSize > 0 ) ?
				( new PROCESS_EVAL_STATE[ mSize ] ) : nullptr;

		resetTableOfState(tableOfState);
	}


	inline void resetTableOfState(
			PROCESS_EVAL_STATE value = PROCESS_UNDEFINED_STATE)
	{
		for( std::size_t i = 0 ; i != mSize ; ++i )
		{
			mEvalState[i] = value;
		}
	}

	inline void resetTableOfState(PROCESS_EVAL_STATE * tableOfState)
	{
		for( std::size_t i = 0 ; i != mSize ; ++i )
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

	inline PROCESS_EVAL_STATE stateAt(std::size_t rid) const
	{
		return( mEvalState[rid] );
	}

	inline PROCESS_EVAL_STATE stateGet(std::size_t rid) const
	{
		return( mEvalState[rid] );
	}

	inline void stateSet(std::size_t rid, PROCESS_EVAL_STATE aEvalState)
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
	bool equalsState(const TableOfRuntimeFormState * other) const;


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
		if( mTableOfAssignedFlag != nullptr )
		{
			for( std::size_t i = 0 ; i < mSize ; ++i )
			{
				delete mTableOfAssignedFlag[i];
			}

			delete[] mTableOfAssignedFlag;

			mTableOfAssignedFlag = nullptr;
		}
	}


	inline void resetAssignedFlags()
	{
		if( mTableOfAssignedFlag != nullptr )
		{
			for( std::size_t i = 0 ; i < mSize ; ++i )
			{
				delete mTableOfAssignedFlag[i];

				mTableOfAssignedFlag[i] = nullptr;
			}
		}
	}


	inline void resetAssignedFlags(const Bitset * * tableOfAssignFlag)
	{
		if( mTableOfAssignedFlag != nullptr )
		{
			for( std::size_t i = 0 ; i < mSize ; ++i )
			{
				delete mTableOfAssignedFlag[i];

				mTableOfAssignedFlag[i] = ( tableOfAssignFlag[i] != nullptr ) ?
						new Bitset( *(tableOfAssignFlag[i]) ) : nullptr;
			}
		}
	}


	// GLOBAL TABLE
	inline void allocAssignedFlag(Bitset * * tableOfAssignFlag)
	{
		mTableOfAssignedFlag = ( mSize > 0 ) ?
				( new Bitset *[ mSize ] ) : nullptr;

		for( std::size_t i = 0 ; i < mSize ; ++i )
		{
			mTableOfAssignedFlag[i] = ( tableOfAssignFlag[i] != nullptr ) ?
					( new Bitset( *(tableOfAssignFlag[i]) ) ) : nullptr;
		}
	}

	inline void reallocAssignedFlag()
	{
		destroyAssignedFlags();

		mTableOfAssignedFlag = ( mSize > 0 ) ?
				( new Bitset *[ mSize ] ) : nullptr;

		for( std::size_t i = 0 ; i < mSize ; ++i )
		{
			mTableOfAssignedFlag[i] = nullptr;
		}
	}


	// RF TABLE
	inline void allocAssignedFlag(std::size_t rid, std::size_t aSize, bool value)
	{
		reallocAssignedFlag();

		mTableOfAssignedFlag[rid] = ( aSize > 0 ) ?
				( new Bitset( aSize, value ) ) : nullptr;
	}


	// ASSIGNED TEST
	inline const Bitset * getAssigned(std::size_t rid) const
	{
		if( mTableOfAssignedFlag != nullptr )
		{
			return( mTableOfAssignedFlag[rid] );
		}
		return( nullptr );
	}

	inline bool isAssigned(std::size_t rid, avm_offset_t offset) const
	{
		if( mTableOfAssignedFlag != nullptr )
		{
			if( mTableOfAssignedFlag[rid] != nullptr )
			{
				return( (*(mTableOfAssignedFlag[rid]))[offset] );
			}
		}
		return( false );
	}


	inline bool hasAssigned() const
	{
		return( mTableOfAssignedFlag != nullptr );
	}

	inline bool zeroAssigned() const
	{
		return( mTableOfAssignedFlag == nullptr );
	}


	inline bool hasAssigned(std::size_t rid) const
	{
		if( mTableOfAssignedFlag != nullptr )
		{
			return( mTableOfAssignedFlag[rid] != nullptr );
		}

		return( false );
	}

	inline bool zeroAssigned(std::size_t rid) const
	{
		if( mTableOfAssignedFlag != nullptr )
		{
			return( mTableOfAssignedFlag[rid] == nullptr );
		}

		return( true );
	}



	void setAssigned(const ExecutionData & anED,
			std::size_t rid, std::size_t offset);


	inline void setAssigned(std::size_t rid, const Bitset * assignedTable)
	{
		if( mTableOfAssignedFlag == nullptr )
		{
			reallocAssignedFlag();
		}
		else if( mTableOfAssignedFlag[rid] != nullptr )
		{
			delete mTableOfAssignedFlag[rid];
		}

		mTableOfAssignedFlag[rid] = ( assignedTable != nullptr ) ?
				( new Bitset( *assignedTable ) ) : nullptr;
	}


	void setAssignedUnion(std::size_t rid,
			const Bitset * assignedTableA, const Bitset * assignedTableB);



	/**
	 * Serialization
	 */
	inline virtual std::string str() const
	{
		StringOutStream oss( AVM_STR_INDENT );

		toStream( oss << IGNORE_FIRST_TAB );

		return( oss.str() );
	}

	virtual void toStream(OutStream & os) const override;

	virtual void toStream(const ExecutionData & anED, OutStream & os) const;

	// Due to [-Woverloaded-virtual=]
	using AvmObject::toStream;

};


}

#endif /* TABLEOFRUNTIMEFORMSTATE_H_ */
