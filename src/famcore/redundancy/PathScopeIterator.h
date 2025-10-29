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
#ifndef PATHSCOPEITERATOR_H_
#define PATHSCOPEITERATOR_H_

#include "ConfigurationComparator.h"

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>


namespace sep
{


class BasePathScopeIterator
{

protected:

	/*
	 * ATTRIBUTES
	 */
	const ExecutionContext * mInterestEC;

	BaseConfigurationComparator * mConfigurationComparator;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BasePathScopeIterator(BaseConfigurationComparator * aConfigComparator)
	: mInterestEC( nullptr ),
	mConfigurationComparator( aConfigComparator )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BasePathScopeIterator()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	virtual bool configure(const WObject * wfFilterObject)
	{
		//!! NOTHING
		return( true );
	}



	/* ITERATOR
	 * theBeginEC to theEnd using theCurrentEC
	 */
	virtual const ExecutionContext * begin(
			const ExecutionContext * anInterestEC) = 0;

	virtual const ExecutionContext * begin() = 0;


	virtual const ExecutionContext * current() = 0;


	virtual bool hasNext() = 0;

	virtual const ExecutionContext * next() = 0;


	virtual void hash(const ExecutionContext & anInterestEC) = 0;


	/**
	 * HANDLER for Event Notification
	 * Destroy Execution Context
	 */
	inline virtual void handleEventDestroyCtx(const ExecutionContext * anEC)
	{
		//!! NOTHING
	}


	/* GETTER - SETTER
	 * mInterestEC
	 */
	inline const ExecutionContext * getInterest()
	{
		return( mInterestEC );
	}

	inline bool hasInterest() const
	{
		return( mInterestEC != nullptr );
	}

	inline void setInterest(const ExecutionContext * anInterestEC)
	{
		mInterestEC = anInterestEC;
	}


	/* GETTER - SETTER
	 * mConfigurationComparator
	 */
	inline BaseConfigurationComparator * getConfigurationComparator()
	{
		return( mConfigurationComparator );
	}

	inline bool hasConfigurationComparator() const
	{
		return( mConfigurationComparator != nullptr );
	}

	inline void setConfigurationComparator(
			BaseConfigurationComparator * aConfigurationComparator)
	{
		mConfigurationComparator = aConfigurationComparator;
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ALL PATH SCOPE ITERATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class AllPathScopeIterator final : public BasePathScopeIterator
{

protected:
	/**
	 * ATTRIBUTES
	 */
	ListOfConstExecutionContext mHashTable;

	ListOfConstExecutionContext::const_iterator itBegin;
	ListOfConstExecutionContext::const_iterator itEnd;

	ListOfConstExecutionContext::const_iterator itCurrent;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AllPathScopeIterator(BaseConfigurationComparator * aConfigComparator)
	: BasePathScopeIterator( aConfigComparator )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AllPathScopeIterator()
	{
		//!! NOTHING
	}


	/* ITERATOR
	 * theBegin to theEnd using theCurrent
	 * next
	 */
	inline virtual const ExecutionContext * begin(
			const ExecutionContext * anInterestEC) override
	{
		mInterestEC = anInterestEC;

		for( itCurrent = getHashTable().begin() ;
				itCurrent != getHashTable().end() ; ++itCurrent )
		{
			if( getConfigurationComparator()->equals(
					(* mInterestEC), (* (*itCurrent))) )
			{
				break;
			}
		}

		itBegin = itCurrent;

		return( (itCurrent != getHashTable().end())? (*itCurrent) : nullptr );
	}

	inline virtual const ExecutionContext * begin() override
	{
		return( (itBegin != getHashTable().end())? (*itBegin) : nullptr );
	}

	virtual const ExecutionContext * current() override
	{
		return( (itCurrent != getHashTable().end())? (*itCurrent) : nullptr );
	}


	inline virtual bool hasNext() override
	{
		return( itCurrent != getHashTable().end() );
	}


	inline virtual const ExecutionContext * next() override
	{
		if( itCurrent != getHashTable().end() )
		{
			for( ++itCurrent ; itCurrent != getHashTable().end() ; ++itCurrent )
			{
				if( getConfigurationComparator()->equals(
						(* mInterestEC), (* (*itCurrent))) )
				{
					return( *itCurrent );
				}
			}
		}
		return( nullptr );
	}


	inline virtual void hash(const ExecutionContext & anInterestEC) override
	{
		appendHash( & anInterestEC );
	}


	/**
	 * GETTER - SETTER
	 * mHashTable
	 */
	inline void appendHash(const ExecutionContext * anEC)
	{
		mHashTable.append( anEC );
	}

	inline ListOfConstExecutionContext & getHashTable()
	{
		return( mHashTable );
	}

	inline bool hasHash() const
	{
		return( mHashTable.nonempty() );
	}


	/**
	 * HANDLER for Event Notification
	 * Destroy Execution Context
	 */
	inline virtual void handleEventDestroyCtx(
			const ExecutionContext * anEC) override
	{
		mHashTable.remove( anEC );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CURRENT PATH SCOPE ITERATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class CurrentPathScopeIterator final : public BasePathScopeIterator
{

protected:
	/*
	 * ATTRIBUTES
	 */
	const ExecutionContext * mBeginEC;
	const ExecutionContext * mCurrentEC;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CurrentPathScopeIterator(BaseConfigurationComparator * aConfigComparator)
	: BasePathScopeIterator( aConfigComparator ),
	mBeginEC( nullptr ),
	mCurrentEC( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~CurrentPathScopeIterator()
	{
		//!! NOTHING
	}


	/* ITERATOR
	 * theBegin to theEnd using theCurrent
	 * next
	 */
	inline virtual const ExecutionContext * begin(
			const ExecutionContext * anInterestEC) override
	{
		mCurrentEC = mInterestEC = anInterestEC;
		return( mBeginEC = next() );
	}

	inline virtual const ExecutionContext * begin() override
	{
		return( mBeginEC );
	}


	inline virtual const ExecutionContext * current() override
	{
		return( mCurrentEC );
	}


	inline virtual bool hasNext() override
	{
		return( mCurrentEC != nullptr );
	}

	inline virtual const ExecutionContext * next() override
	{
		if( mCurrentEC != nullptr )
		{
			mCurrentEC = mCurrentEC->getContainer();
			for( ; (mCurrentEC != nullptr) ;
					mCurrentEC = mCurrentEC->getContainer() )
			{
				if( getConfigurationComparator()
						->equals((* mInterestEC), (* mCurrentEC)) )
				{
					return( mCurrentEC->isnotRoot() ?
							mCurrentEC : (mCurrentEC = nullptr) );
				}
			}
		}

		return( mCurrentEC );
	}

	inline virtual void hash(const ExecutionContext & anInterestEC) override
	{
		//!! NOTHING
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// PARENT PATH SCOPE ITERATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ParentPathScopeIterator final :  public BasePathScopeIterator
{

protected:

	/*
	 * ATTRIBUTES
	 */
	const ExecutionContext * mCurrentEC;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ParentPathScopeIterator(BaseConfigurationComparator * aConfigComparator)
	: BasePathScopeIterator( aConfigComparator ),
	mCurrentEC( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ParentPathScopeIterator()
	{
		//!! NOTHING
	}


	/* ITERATOR
	 * theBegin to theEnd using theCurrent
	 * next
	 */
	inline virtual const ExecutionContext * begin(
			const ExecutionContext * anInterestEC) override
	{
		mInterestEC = anInterestEC;

		mCurrentEC = mInterestEC->getContainer();
		if( (mCurrentEC != nullptr)
			&& mCurrentEC->isnotRoot()
			&& getConfigurationComparator()->equals(
					(* mCurrentEC), (* mInterestEC)) )
		{
			return( mCurrentEC );
		}

		return( mCurrentEC = nullptr );
	}

	inline virtual const ExecutionContext * begin() override
	{
		return( mInterestEC );
	}


	inline virtual const ExecutionContext * current() override
	{
		return( mCurrentEC );
	}


	inline virtual bool hasNext() override
	{
		return( mCurrentEC != nullptr );
	}

	inline virtual const ExecutionContext * next() override
	{
		return( mCurrentEC = nullptr );
	}

	inline virtual void hash(const ExecutionContext & anInterestEC) override
	{
		//!! NOTHING
	}

};


}

#endif /*PATHSCOPEITERATOR_H_*/
