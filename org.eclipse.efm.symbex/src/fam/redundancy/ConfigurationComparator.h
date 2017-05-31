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
#ifndef CONFIGURATIONCOMPARATOR_H_
#define CONFIGURATIONCOMPARATOR_H_

#include "BaseDataComparator.h"

#include <fml/runtime/ExecutionContext.h>


namespace sep
{


class BaseConfigurationComparator : public BaseDataComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseConfigurationComparator(Configuration & aConfiguration)
	: BaseDataComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseConfigurationComparator()
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


	/*
	 * COMPARE
	 */
	inline virtual bool compare(
			const ExecutionContext & newEC, const ExecutionContext & oldEC)
	{
		return( equals(newEC, oldEC) );
	}


	virtual bool equals(
			const ExecutionContext & newEC, const ExecutionContext & oldEC)
	{
		if( ((& newEC) == (& oldEC))
			|| (newEC.getExecutionData() == oldEC.getExecutionData()) )
		{
			return( true );
		}

		if( newEC.refExecutionData().getTableOfRuntime().size() !=
				oldEC.refExecutionData().getTableOfRuntime().size() )
		{
			return( false );
		}


		return( equals(newEC.refExecutionData(),
				newEC.refExecutionData().getOnSchedule(),
				oldEC.refExecutionData(),
				oldEC.refExecutionData().getOnSchedule()) );
		/*!ALTERNATIVE!*
		return( newEC.refExecutionData().strStateConf()
				== oldEC.refExecutionData().strStateConf() );
		*!ALTERNATIVE!*/
	}


	virtual bool equals(const ExecutionData & firstED, const BF & firstSchedule,
			const ExecutionData & sndED, const BF & sndSchedule);

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const
	{
		return( "control_scope: ALL" );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ALL CONFIGURATION COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class AllConfigurationComparator  :  public BaseConfigurationComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AllConfigurationComparator(Configuration & aConfiguration)
	: BaseConfigurationComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AllConfigurationComparator()
	{
		//!! NOTHING
	}



	/*
	 * COMPARE
	 */
	virtual bool equals(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);


	virtual bool equals(
			const ExecutionData & firstED, const BF & firstSchedule,
			const ExecutionData & sndED  , const BF & sndSchedule);

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DETAILS CONFIGURATION COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class RuntimeID;

class DetailConfigurationComparator  :  public BaseConfigurationComparator
{

protected:
	/*
	 * ATTRIBUTES
	 */
	List< RuntimeID > mListOfIgnoreMachine;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	DetailConfigurationComparator(Configuration & aConfiguration)
	: BaseConfigurationComparator( aConfiguration ),
	mListOfIgnoreMachine( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~DetailConfigurationComparator()
	{
		//!! NOTHING
	}



	/**
	 * CONFIGURE
	 */
	virtual bool configure(WObject * wfParameterObject);

	void computeIgnoreMachine(const ExecutionData & anED,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance);

	void appendFamilyMachine(
			const ExecutionData & anED, const RuntimeID & aRID);


	/*
	 * COMPARE
	 */

	virtual bool equals(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	bool restrictedRunnableElementTrace(const BF & form);

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const
	{
		return( "control_scope: DETAILS" );
	}

};



}

#endif /*CONFIGURATIONCOMPARATOR_H_*/
