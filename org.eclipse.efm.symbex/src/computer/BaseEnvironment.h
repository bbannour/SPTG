/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASEENVIRONMENT_H_
#define BASEENVIRONMENT_H_

#include <common/AvmObject.h>

#include <common/BF.h>

#include <collection/Typedef.h>

#include <fml/symbol/Symbol.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>



namespace sep
{


class ARGS_ENV;
class AvmPrimitiveProcessor;

class BuiltinArray;
class Builder;
class BuiltinContainer;

class Configuration;

class ExecutableSystem;

class Loader;
class LocalRuntime;

class SymbexEngine;

class TypeSpecifier;


class BaseEnvironment :
		public AvmObject,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseEnvironment )
{

public :
	/**
	 * ATTRIBUTES
	 */
	////////////////////////////////////////////////////////////////////////////
	// INPUTs
	////////////////////////////////////////////////////////////////////////////

	AvmPrimitiveProcessor & PRIMITIVE_PROCESSOR;

	const ExecutionContext * inEC;

	BF inFORM;

	BFCode inCODE;

	APExecutionData inED;


	////////////////////////////////////////////////////////////////////////////
	// ARGS ENV
	////////////////////////////////////////////////////////////////////////////

	ARGS_ENV * mARG;


	////////////////////////////////////////////////////////////////////////////
	// FAILED Execution Data
	////////////////////////////////////////////////////////////////////////////

	ListOfAPExecutionData failureEDS;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseEnvironment(AvmPrimitiveProcessor & aPrimitiveProcessor)
	: AvmObject( ),
	PRIMITIVE_PROCESSOR( aPrimitiveProcessor ),
	inEC( NULL ),
	inFORM( ),
	inCODE( ),
	inED( ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(AvmPrimitiveProcessor & aPrimitiveProcessor,
			const ExecutionContext * anEC)
	: AvmObject( ),
	PRIMITIVE_PROCESSOR( aPrimitiveProcessor ),
	inEC( anEC ),
	inFORM( ),
	inCODE( ),
	inED( anEC->getAPExecutionData() ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}

	/**
	* CONSTRUCTOR
	* Copy
	*/
	BaseEnvironment(const BaseEnvironment & form)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( form.inFORM ),
	inCODE( form.inCODE ),
	inED( form.inED ),
	mARG( NULL ),
	failureEDS( form.failureEDS )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form, const BFCode & aCode)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( aCode ),
	inCODE( aCode ),
	inED( form.inED ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const RuntimeID & aRID, const BFCode & aCode)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( aCode ),
	inCODE( aCode ),
	inED( form.inED ),
	mARG( NULL ),
	failureEDS( )
	{
		inED.mwsetRID(aRID);
	}


	BaseEnvironment(const BaseEnvironment & form, const APExecutionData & apED)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( ),
	inCODE( ),
	inED( apED ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const APExecutionData & apED, const BF & bf)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( bf ),
	inCODE( (bf.is< AvmCode >()) ? bf.bfCode() : BFCode::REF_NULL ),
	inED( apED ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const APExecutionData & apED, const BFCode & aCode)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( aCode ),
	inCODE( aCode ),
	inED( apED ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const APExecutionData & apED, const RuntimeID & aRID)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( form.inFORM ),
	inCODE( form.inCODE ),
	inED( apED ),
	mARG( NULL ),
	failureEDS( )
	{
		inED.mwsetRID(aRID);
	}

	BaseEnvironment(const BaseEnvironment & form, const APExecutionData & apED,
			const RuntimeID & aRID, const BFCode & aCode)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( aCode ),
	inCODE( aCode ),
	inED( apED ),
	mARG( NULL ),
	failureEDS( )
	{
		inED.mwsetRID(aRID);
	}


	BaseEnvironment(const BaseEnvironment & form, const BF & bf)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( bf ),
	inCODE( (bf.is< AvmCode >()) ? bf.bfCode() : BFCode::REF_NULL ),
	inED( form.inED ),
	mARG( NULL ),
	failureEDS( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseEnvironment()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Builder
	 * Configuration
	 * ExecutableSystem
	 */
	Builder & getBuilder() const;

	Loader & getLoader() const;

	SymbexEngine & getSymbexEngine() const;

	Configuration & getConfiguration() const;

	ExecutableSystem & getExecutableSystem() const;


	/**
	 * GETTER - SETTER
	 * PROGRAM
	*/
	inline void setCode(const BFCode & aCode)
	{
		inFORM = inCODE = aCode;
	}


	/**
	 * GETTER - SETTER
	 * INPUT ED
	*/
	inline bool hasInputED() const
	{
		return( inED.valid() );
	}

	/**
	 * GETTER - SETTER
	 * OUTPUT EDS
	*/
	virtual bool hasOutput() const = 0;

	virtual bool hasntOutput() const = 0;


	/**
	 * GETTER - SETTER
	 * FAILED EDS
	 */
	inline void appendFailure(const APExecutionData & anED)
	{
		failureEDS.append(anED);
	}

	inline void spliceFailure(BaseEnvironment & ENV)
	{
		failureEDS.splice( ENV.failureEDS );
	}

	inline bool hasFailure() const
	{
		return( failureEDS.nonempty() );
	}

	inline bool isFailure() const
	{
		return( hasntOutput() && failureEDS.nonempty() );
	}



	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;



	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	///// SYMBOLIC PARAMETRE CREATION
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfData * create(const RuntimeID & aRID,
			BaseTypeSpecifier * aTypeSpecifier, InstanceOfData * lvalue);

	inline InstanceOfData * create(
			const RuntimeID & aRID, InstanceOfData * lvalue)
	{
		return( create(aRID, lvalue->getTypeSpecifier(), lvalue));
	}

	BF evalInitial(APExecutionData & anED, const RuntimeID & aRID,
			InstanceOfData * lvalue, const BF & anInitialValue);

	BF createInitial(APExecutionData & anED,
			const RuntimeID & aRID, InstanceOfData * lvalue);

	inline BF createInitial(APExecutionData & anED,
			const RuntimeID & aRID, const Symbol & lvalue)
	{
		return( createInitial(anED, aRID, lvalue.rawData()) );
	}

	BF createInitial(APExecutionData & anED, const RuntimeID & aRID,
			InstanceOfData * lvalue, BuiltinArray * initialArray);


	BF createNewFreshParam(const RuntimeID & aPRID,
			BaseTypeSpecifier * aTypeSpecifier,
			InstanceOfData * lvalue, BFList & paramList);

	inline BF createNewFreshParam(const RuntimeID & aPRID,
			InstanceOfData * lvalue, BFList & paramList)
	{
		return( createNewFreshParam(aPRID, lvalue->getTypeSpecifier(),
				lvalue, paramList) );
	}

	inline BF createNewFreshParam(const RuntimeID & aPRID,
			BaseTypeSpecifier * aTypeSpecifier,
			const Symbol & lvalue, BFList & paramList)
	{
		return( createNewFreshParam(aPRID, aTypeSpecifier,
				lvalue.rawData(), paramList) );
	}

	inline BF createNewFreshParam(const RuntimeID & aPRID,
			const Symbol & lvalue, BFList & paramList)
	{
		return( createNewFreshParam(aPRID, lvalue.rawData(), paramList) );
	}


	Symbol create(const RuntimeID & aRID, const std::string & paramID,
			const TypeSpecifier & aTypeSpecifier, const BF & aValue);


	Symbol create4ArrayAccess(APExecutionData & anED,
			const RuntimeID & aRID, const BF & arrayValue,
			InstanceOfData * lvalueOfIndex);



	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	///// the DATA ACCESS statement
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/*
	 * GETTER
	 * Assigned Flags
	 */
	static bool isAssigned(const APExecutionData & apED,
			const RuntimeID & aRID, InstanceOfData * lvalue);


	/*
	 * GETTER
	 * Runtime instance
	 */
	static bool getRuntimeForm(
			const APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvalue, RuntimeID & aDataRID);

	static bool getRuntimeForm(const APExecutionData & apED,
			InstanceOfData * lvalue, LocalRuntime & aLocalRuntime);


	/**
	 * Generate numeric offset for array access using symbolic expression
	 */
	avm_size_t genNumericOffset(
			APExecutionData & apED, const RuntimeID & aRID,
			const Symbol & lvSymbolicOffset, const BF & rvEvaluatedOffset,
			avm_size_t offsetMin, avm_size_t offsetMax);

	/*
	 * GETTER
	 * rvalue for an lvalue
	 */
	BF & getRvalue(APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvUFI, BF & rvalue, const Symbol & offsetValue);

	BF & getRvalue(APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvalue);

	inline BF & getRvalue(APExecutionData & apED, InstanceOfData * lvalue)
	{
		return( getRvalue(apED, apED->mRID, lvalue) );
	}

	inline BF & getRvalue(InstanceOfData * lvalue)
	{
		return( getRvalue(inED, inED->mRID, lvalue) );
	}

	inline BF & getRvalue(const RuntimeID & aRID, InstanceOfData * lvalue)
	{
		return( getRvalue(inED, aRID, lvalue) );
	}


	/*
	 * GETTER
	 * writable rvalue for an lvalue
	 */
	BF & getWvalue(APExecutionData & apED, const RuntimeID & aRID,
			ArrayBF * rvArray, const Symbol & lvalue);

	BF & getWvalue(APExecutionData & apED, const RuntimeID & aRID,
			BuiltinContainer * rvArray, const Symbol & lvalue);


	BF & getWvalue(APExecutionData & apED,
			const RuntimeID & aRID, InstanceOfData * lvalue);

	inline BF & getWvalue(APExecutionData & apED, InstanceOfData * lvalue)
	{
		return( getWvalue(apED, apED->mRID, lvalue) );
	}


	/*
	 * SETTER
	 * lvalue := rvalue
	 */
	inline bool setRvalue(InstanceOfData * lvalue, const BF & rvalue)
	{
		return( setRvalue(inED, lvalue, rvalue) );
	}

	bool setRvalue(APExecutionData & apED,
			InstanceOfData * lvalue, const BF & rvalue);

	inline bool setRvalue(
			APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvalue, const BF & rvalue)
	{
		const RuntimeID prevRID = apED->mRID;
		apED->mRID = aRID;

		bool rt = setRvalue(apED, lvalue, rvalue);

		apED->mRID = prevRID;

		return( rt );
	}


	bool invokeOnWriteRoutine(
			APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvalue, const BF & rvalue);

	inline bool writeData(
			APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvalue, const BF & rvalue)
	{
		if( invokeOnWriteRoutine(apED, aRID, lvalue, rvalue) )
		{
			return( setData(apED, aRID, lvalue, rvalue) );
		}

		return( false );
	}


	/**
	 * set[Local]Data
	 */
	bool setData(APExecutionData & apED, const RuntimeID & aRID,
			InstanceOfData * lvalue, const BF & rvalue);

	bool setLocalRuntime(APExecutionData & apED, LocalRuntime & aLocalRuntime,
			InstanceOfData * lvalue, const BF & rvalue);


	/**
	 * TOOLS
	 */
	BFCode searchTraceIO(const BF & aTrace, AvmCode * ioFormula);


	/*
	 * STATIC ATTRIBUTES
	 */
	static avm_uint32_t NEW_PARAM_OFFSET;

};


} /* namespace sep */
#endif /* BASEENVIRONMENT_H_ */
