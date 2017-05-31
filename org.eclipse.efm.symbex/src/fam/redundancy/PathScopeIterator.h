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
	: mInterestEC( NULL ),
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
	virtual bool configure(WObject * wfFilterObject)
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
		return( mInterestEC != NULL );
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
		return( mConfigurationComparator != NULL );
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

class AllPathScopeIterator : public BasePathScopeIterator
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
			const ExecutionContext * anInterestEC)
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

		return( (itCurrent != getHashTable().end())? (*itCurrent) : NULL );
	}

	inline virtual const ExecutionContext * begin()
	{
		return( (itBegin != getHashTable().end())? (*itBegin) : NULL );
	}

	virtual const ExecutionContext * current()
	{
		return( (itCurrent != getHashTable().end())? (*itCurrent) : NULL );
	}


	inline virtual bool hasNext()
	{
		return( itCurrent != getHashTable().end() );
	}


	inline virtual const ExecutionContext * next()
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
		return( NULL );
	}


	inline virtual void hash(const ExecutionContext & anInterestEC)
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
	inline virtual void handleEventDestroyCtx(const ExecutionContext * anEC)
	{
		mHashTable.remove( anEC );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CURRENT PATH SCOPE ITERATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class CurrentPathScopeIterator : public BasePathScopeIterator
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
	mBeginEC( NULL ),
	mCurrentEC( NULL )
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
			const ExecutionContext * anInterestEC)
	{
		mCurrentEC = mInterestEC = anInterestEC;
		return( mBeginEC = next() );
	}

	inline virtual const ExecutionContext * begin()
	{
		return( mBeginEC );
	}


	inline virtual const ExecutionContext * current()
	{
		return( mCurrentEC );
	}


	inline virtual bool hasNext()
	{
		return( mCurrentEC != NULL );
	}

	inline virtual const ExecutionContext * next()
	{
		if( mCurrentEC != NULL )
		{
			mCurrentEC = mCurrentEC->getContainer();
			for( ; (mCurrentEC != NULL) ;
					mCurrentEC = mCurrentEC->getContainer() )
			{
				if( getConfigurationComparator()
						->equals((* mInterestEC), (* mCurrentEC)) )
				{
					return( mCurrentEC->isnotRoot() ?
							mCurrentEC : (mCurrentEC = NULL) );
				}
			}
		}

		return( mCurrentEC );
	}

	inline virtual void hash(const ExecutionContext & anInterestEC)
	{
		//!! NOTHING
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// PARENT PATH SCOPE ITERATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ParentPathScopeIterator  :  public BasePathScopeIterator
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
	mCurrentEC( NULL )
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
			const ExecutionContext * anInterestEC)
	{
		mInterestEC = anInterestEC;

		mInterestEC = mInterestEC->getContainer();
		if( (mInterestEC != NULL)
			&& mInterestEC->isnotRoot()
			&& getConfigurationComparator()->equals(
					(* mInterestEC), (* mInterestEC)) )
		{
			return( mInterestEC );
		}

		return( mInterestEC = NULL );
	}

	inline virtual const ExecutionContext * begin()
	{
		return( mInterestEC );
	}


	inline virtual const ExecutionContext * current()
	{
		return( mInterestEC );
	}


	inline virtual bool hasNext()
	{
		return( mInterestEC != NULL );
	}

	inline virtual const ExecutionContext * next()
	{
		return( mInterestEC = NULL );
	}

	inline virtual void hash(const ExecutionContext & anInterestEC)
	{
		//!! NOTHING
	}

};


}

#endif /*PATHSCOPEITERATOR_H_*/
