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
	inline virtual bool configure(const WObject * wfFilterObject) override
	{
		//!! NOTHING

		return( true );
	}


	/*
	 * COMPARE
	 */
	inline virtual bool compare(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override
	{
		return( equals(newEC, oldEC) );
	}


	inline virtual bool equals(
			const ExecutionContext & newEC, const ExecutionContext & oldEC)
	{
		if( ((& newEC) == (& oldEC)) || newEC.edTEQ( oldEC ) )
		{
			return( true );
		}

		if( newEC.getExecutionData().getTableOfRuntime().size() !=
				oldEC.getExecutionData().getTableOfRuntime().size() )
		{
			return( false );
		}


		return( equals(newEC.getExecutionData(),
				newEC.getExecutionData().getOnSchedule(),
				oldEC.getExecutionData(),
				oldEC.getExecutionData().getOnSchedule()) );
		/*!ALTERNATIVE!*
		return( newEC.getExecutionData().strStateConf()
				== oldEC.getExecutionData().strStateConf() );
		*!ALTERNATIVE!*/
	}


	virtual bool equals(const ExecutionData & firstED, const BF & firstSchedule,
			const ExecutionData & sndED, const BF & sndSchedule);

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const override
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
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;


	virtual bool equals(
			const ExecutionData & firstED, const BF & firstSchedule,
			const ExecutionData & sndED  , const BF & sndSchedule) override;

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
	virtual bool configure(const WObject * wfParameterObject) override;

	void computeIgnoreMachine(const ExecutionData & anED,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance);

	void appendFamilyMachine(
			const ExecutionData & anED, const RuntimeID & aRID);


	/*
	 * COMPARE
	 */

	virtual bool equals(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	bool restrictedRunnableElementTrace(const BF & form);

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const override
	{
		return( "control_scope: DETAILS" );
	}

};



}

#endif /*CONFIGURATIONCOMPARATOR_H_*/
