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
#ifndef BaseDataComparator_H_
#define BaseDataComparator_H_

#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


class BaseBufferForm;
class Configuration;
class ExecutableSystem;
class InstanceOfData;
class Message;
class RuntimeForm;


class BaseDataComparator
{

protected:
	/**
	 * ATTRIBUTES
	 */
	Configuration & mConfiguration;

	std::size_t mMachineCount;

	bool mCurrentPathScopeFlag;

	std::size_t mComparisonCount;


	List< RuntimeID > mListOfSelectedIOMachine;

	ListOfPairMachineData mListOfAllVariable;


	ListOfPairMachineData mListOfSelectedPresburgerVariable;

	ListOfPairMachineData mListOfCurrentPresburgerVariable;

	ListOfPairMachineData mListOfSelectedNonPresburgerVariable;

	// Heuristic
	bool mUseCommunication;
	bool mUseVariable;
	bool mIgnorePathCondition;


	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	const RuntimeForm * newRF;
	const RuntimeForm * oldRF;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseDataComparator(Configuration & aConfiguration)
	: mConfiguration( aConfiguration ),
	mMachineCount( 0 ),
	mCurrentPathScopeFlag( false ),
	mComparisonCount( 0 ),

	mListOfSelectedIOMachine( ),
	mListOfAllVariable( ),

	mListOfSelectedPresburgerVariable( ),
	mListOfCurrentPresburgerVariable( ),
	mListOfSelectedNonPresburgerVariable( ),

	// Heuristic
	mUseCommunication( true ),
	mUseVariable( true ),
	mIgnorePathCondition( false ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	newRF( nullptr ),
	oldRF( nullptr )
	{
			//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseDataComparator()
	{
		destroyMachineData();
	}

	void destroyMachineData();


	/**
	 * CONFIGURE
	 */
	virtual bool configure(const WObject * wfParameterObject);

	void computeAllMachineData(const ExecutionData & anED);

	void computeDetailsIncludeMachineData(const ExecutionData & anED,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance,
			ListOfInstanceOfData & listOfVariable);

	void computeDetailsExcludeMachineData(const ExecutionData & anED,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance,
			ListOfInstanceOfData & listOfVariable);


	/*
	 * COMPARE
	 */
	inline virtual bool compareDATA(
			const ExecutionContext & newEC, const ExecutionContext & oldEC)
	{
		return( true );
	}

	virtual bool compareIO(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	virtual bool compareBUFFER(
			const BaseBufferForm * newBuf, const BaseBufferForm *oldBuf);

	virtual bool compareMESSAGE(const Message & newMsg, const Message & oldMsg);


	inline virtual bool compareTEQ(
			const ExecutionContext & newEC, const ExecutionContext & oldEC)
	{
		return( newEC.edTEQ( oldEC ) );
	}

	virtual bool compare(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);


	/**
	 * GETTER - SETTER
	 * mCurrentPathScopeFlag
	 */
	inline bool isCurrentPathScope()
	{
		return( mCurrentPathScopeFlag );
	}


	/**
	 * GETTER - SETTER
	 * the List Of Selected Machine and Variable
	 */

	// IO Machine
	inline const List< RuntimeID > & getSelectedIOMachine()
	{
		return( mListOfSelectedIOMachine );
	}

	static void selectDetailsIOMachine(const ExecutionData & anED,
			List< RuntimeID > & aListOfSelectedIOMachine,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance);

	static void selectIOMachine(const ExecutionData & anED,
			List< RuntimeID > & aListOfSelectedIOMachine);


	// ALL Variable
	inline ListOfPairMachineData & getAllVariable()
	{
		return( mListOfAllVariable );
	}

	static void selectAllVariable(const ExecutionData & anED,
			ListOfPairMachineData & aListOfSelectedVariable);


	static std::size_t selectVariable(
			ListOfInstanceOfData & listOfData, const InstanceOfData * pData);

	static std::size_t selectPresburgerVariable(
			ListOfInstanceOfData & listOfData, const InstanceOfData * pData);

	static std::size_t selectNonPresburgerVariable(
			ListOfInstanceOfData & listOfData, const InstanceOfData * pData);


	static void selectDetailsVariable(const ExecutionData & anED,
			ListOfPairMachineData & aListOfSelectedVariable,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance,
			ListOfInstanceOfData & listOfVariable);


	// PRESBURGER Variable
	inline ListOfPairMachineData & getSelectedPresburgerVariable()
	{
		return( mListOfSelectedPresburgerVariable );
	}

	static void selectPresburgerVariable(const ExecutionData & anED,
			ListOfPairMachineData & aListOfSelectedVariable);

	static void selectDetailsPresburgerVariable(const ExecutionData & anED,
			ListOfPairMachineData & aListOfSelectedVariable,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance,
			ListOfInstanceOfData & listOfVariable);


	inline ListOfPairMachineData & getCurrentPresburgerVariable()
	{
		return( mListOfCurrentPresburgerVariable );
	}

	static void refreshCurrentVariables(
			ListOfPairMachineData & currentVariables,
			ListOfPairMachineData & referenceVariables,
			const ExecutionData & newED, const ExecutionData & oldED);

	// NON PRESBURGER Variable
	inline ListOfPairMachineData & getSelectedNonPresburgerVariable()
	{
		return( mListOfSelectedNonPresburgerVariable );
	}


	static void selectNonPresburgerVariable(const ExecutionData & anED,
			ListOfPairMachineData & aListOfSelectedVariable);

	static void selectDetailsNonPresburgerVariable(const ExecutionData & anED,
			ListOfPairMachineData & aListOfSelectedVariable,
			ListOfExecutableForm & listOfExecutable,
			ListOfInstanceOfMachine & listOfInstance,
			ListOfInstanceOfData & listOfVariable);


	inline virtual bool hasVariableComparison()
	{
		return( (mMachineCount > 0) && mListOfAllVariable.nonempty() );
	}

	/**
	 * strComparer
	 */
	virtual std::string strComparer() const = 0;
};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TRIVIALLY DATA COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class TriviallyDataComparison final :  public BaseDataComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TriviallyDataComparison(Configuration & aConfiguration)
	: BaseDataComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TriviallyDataComparison()
	{
		//!! NOTHING
	}


	/*
	 * COMPARE
	 */
	virtual bool compareDATA(const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	virtual bool compare(const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override
	{
		return( newEC.edTEQ( oldEC )
				|| (mUseVariable ? compareDATA(newEC, oldEC) : true) );
	}

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const override
	{
		return( "=&= i.e. TEQ" );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// NONE DATA COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class NoneDataComparison final :  public BaseDataComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	NoneDataComparison(Configuration & aConfiguration)
	: BaseDataComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~NoneDataComparison()
	{
		//!! NOTHING
	}

	/**
	 * CONFIGURE
	 */
	inline virtual bool configure(const WObject * wfFilterObject) override
	{
		return( true );
	}


	/*
	 * COMPARE
	 */
	inline virtual bool compareDATA(
			const ExecutionContext & newEC, const ExecutionContext & oldEC) override
	{
		return( true );
	}

	inline virtual bool compareIO(
			const ExecutionContext & newEC, const ExecutionContext & oldEC) override
	{
		return( true );
	}

	inline virtual bool compareBUFFER(
			const BaseBufferForm * newBuf, const BaseBufferForm *oldBuf) override
	{
		return( true );
	}

	inline virtual bool compareMESSAGE(
			const Message & newMsg, const Message & oldMsg) override
	{
		return( true );
	}


	inline virtual bool compare(
			const ExecutionContext & newEC, const ExecutionContext & oldEC) override
	{
		return( true );
	}

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const override
	{
		return( "NONE" );
	}

};


}

#endif /*BaseDataComparator_H_*/
