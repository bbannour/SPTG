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
class ExecutionConfiguration;

class InstanceOfData;
class InstanceOfPort;

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

	ExecutionData inED;


	////////////////////////////////////////////////////////////////////////////
	// ARGS ENV
	////////////////////////////////////////////////////////////////////////////

	ARGS_ENV * mARG;


	////////////////////////////////////////////////////////////////////////////
	// FAILED Execution Data
	////////////////////////////////////////////////////////////////////////////

	ListOfExecutionData failureEDS;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseEnvironment(AvmPrimitiveProcessor & aPrimitiveProcessor)
	: AvmObject( ),
	PRIMITIVE_PROCESSOR( aPrimitiveProcessor ),
	inEC( nullptr ),
	inFORM( ),
	inCODE( ),
	inED( ),
	mARG( nullptr ),
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
	inED( anEC->getExecutionData() ),
	mARG( nullptr ),
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
	mARG( nullptr ),
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
	mARG( nullptr ),
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
	mARG( nullptr ),
	failureEDS( )
	{
		inED.mwsetRID(aRID);
	}


	BaseEnvironment(const BaseEnvironment & form, const ExecutionData & apED)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( ),
	inCODE( ),
	inED( apED ),
	mARG( nullptr ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const ExecutionData & apED, const BF & bf)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( bf ),
	inCODE( (bf.is< AvmCode >()) ? bf.bfCode() : BFCode::REF_NULL ),
	inED( apED ),
	mARG( nullptr ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const ExecutionData & apED, const BFCode & aCode)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( aCode ),
	inCODE( aCode ),
	inED( apED ),
	mARG( nullptr ),
	failureEDS( )
	{
		//!! NOTHING
	}

	BaseEnvironment(const BaseEnvironment & form,
			const ExecutionData & apED, const RuntimeID & aRID)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( form.inFORM ),
	inCODE( form.inCODE ),
	inED( apED ),
	mARG( nullptr ),
	failureEDS( )
	{
		inED.mwsetRID(aRID);
	}

	BaseEnvironment(const BaseEnvironment & form, const ExecutionData & apED,
			const RuntimeID & aRID, const BFCode & aCode)
	: AvmObject( form ),
	PRIMITIVE_PROCESSOR( form.PRIMITIVE_PROCESSOR ),
	inEC( form.inEC ),
	inFORM( aCode ),
	inCODE( aCode ),
	inED( apED ),
	mARG( nullptr ),
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
	mARG( nullptr ),
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

	virtual bool hasnoOutput() const = 0;


	/**
	 * GETTER - SETTER
	 * FAILED EDS
	 */
	inline void appendFailure(const ExecutionData & anED)
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
		return( hasnoOutput() && failureEDS.nonempty() );
	}



	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override;

	// Due to [-Woverloaded-virtual=]
	using AvmObject::toStream;



	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	///// SYMBOLIC PARAMETRE CREATION
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	InstanceOfData * create(const RuntimeID & aRID,
			const BaseTypeSpecifier & aTypeSpecifier,
			const InstanceOfData & lvalue);

	inline InstanceOfData * create(
			const RuntimeID & aRID, const InstanceOfData & lvalue)
	{
		return( create(aRID, lvalue.getTypeSpecifier(), lvalue));
	}

	static BF evalInitial(ExecutionData & anED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, const BF & anInitialValue);

	BF createInitial(ExecutionData & anED,
			const RuntimeID & aRID, const InstanceOfData & lvalue);

	inline BF createInitial(ExecutionData & anED,
			const RuntimeID & aRID, const Symbol & lvalue)
	{
		return( createInitial(anED, aRID,
				const_cast< InstanceOfData & >(lvalue.variable())) );
	}

	BF createInitial(ExecutionData & anED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, BuiltinArray * initialArray);


	BF createNewFreshParam(const RuntimeID & aPRID,
			const BaseTypeSpecifier & aTypeSpecifier,
			const InstanceOfData & lvalue, BFCollection & paramList);

	inline BF createNewFreshParam(const RuntimeID & aPRID,
			const InstanceOfData & lvalue, BFCollection & paramList)
	{
		return( createNewFreshParam(
				aPRID, lvalue.getTypeSpecifier(), lvalue, paramList) );
	}


	inline BF createNewFreshParam(const RuntimeID & aPRID,
			const Symbol & lvalue, BFCollection & paramList)
	{
		return( createNewFreshParam(aPRID,
				const_cast< InstanceOfData & >(lvalue.variable()),
				paramList) );
	}

	void createNewFreshParam(
			const RuntimeID & aPRID, const InstanceOfPort & port,
			BFCollection & newfreshList, BFCollection & paramList);


	Symbol create(const RuntimeID & aRID, const std::string & newfreshParamID,
			const BaseTypeSpecifier & aTypeSpecifier, const BF & aValue);


	Symbol create4ArrayAccess(ExecutionData & anED,
			const RuntimeID & aRID, const BF & arrayValue,
			const InstanceOfData & lvalueOfIndex);



	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	///// the DATA ACCESS statement
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/*
	 * GETTER
	 * Assigned Flags
	 */
	static bool isAssigned(const ExecutionData & apED,
			const RuntimeID & aRID, const InstanceOfData & lvalue);


	/*
	 * GETTER
	 * Runtime instance
	 */
	static bool getRuntimeForm(
			const ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, RuntimeID & aDataRID);

	static bool getRuntimeForm(const ExecutionData & apED,
			const InstanceOfData & lvalue, LocalRuntime & aLocalRuntime);


	/**
	 * Generate numeric offset for array access using symbolic expression
	 */
	std::size_t genNumericOffset(
			ExecutionData & apED, const RuntimeID & aRID,
			const Symbol & lvSymbolicOffset, const BF & rvEvaluatedOffset,
			std::size_t offsetMin, std::size_t offsetMax);

	/*
	 * GETTER
	 * rvalue for an lvalue
	 */
	BF & getRvalue(ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvUFI, BF & rvalue, const Symbol & offsetValue);

	BF & getRvalue(ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvalue);

	inline BF & getRvalue(ExecutionData & apED, const InstanceOfData & lvalue)
	{
		return( getRvalue(apED, apED.getRID(), lvalue) );
	}

	inline BF & getRvalue(const InstanceOfData & lvalue)
	{
		return( getRvalue(inED, inED.getRID(), lvalue) );
	}

	inline BF & getRvalue(const RuntimeID & aRID, const InstanceOfData & lvalue)
	{
		return( getRvalue(inED, aRID, lvalue) );
	}


	/*
	 * GETTER
	 * writable rvalue for an lvalue
	 */
	BF & getWvalue(ExecutionData & apED, const RuntimeID & aRID,
			ArrayBF * rvArray, const Symbol & lvalue);

	BF & getWvalue(ExecutionData & apED, const RuntimeID & aRID,
			BuiltinContainer * rvArray, const Symbol & lvalue);


	BF & getWvalue(ExecutionData & apED,
			const RuntimeID & aRID, const InstanceOfData & lvalue);

	inline BF & getWvalue(ExecutionData & apED, const InstanceOfData & lvalue)
	{
		return( getWvalue(apED, apED.getRID(), lvalue) );
	}


	/*
	 * SETTER
	 * lvalue := rvalue
	 */
	inline bool setRvalue(const InstanceOfData & lvalue, const BF & rvalue)
	{
		return( setRvalue(inED, lvalue, rvalue) );
	}

	bool setRvalue(ExecutionData & apED,
			const InstanceOfData & lvalue, const BF & rvalue);

	inline bool setRvalue(
			ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, const BF & rvalue)
	{
		const RuntimeID prevRID = apED.getRID();
		apED.setRID( aRID );

		bool rt = setRvalue(apED, lvalue, rvalue);

		apED.setRID( prevRID );

		return( rt );
	}


	bool invokeOnWriteRoutine(
			ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, const BF & rvalue);

	inline bool writeData(
			ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, const BF & rvalue)
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
	bool setData(ExecutionData & apED, const RuntimeID & aRID,
			const InstanceOfData & lvalue, const BF & rvalue);

	static bool setLocalRuntime(ExecutionData & apED, LocalRuntime & aLocalRuntime,
			const InstanceOfData & lvalue, const BF & rvalue);


	/**
	 * TOOLS
	 */
	static const BFCode & searchTraceIO(const BF & aTrace);

	static const BFCode & searchTraceIO(const BF & aTrace, const AvmCode & ioFormula);

	static const BFCode & searchTraceIO(const BF & aTrace,
			const RuntimeID & ctxRID, const AvmCode & ioFormula);


	static const ExecutionConfiguration & searchTraceIOExecConf(const BF & aTrace);

	/*
	 * STATIC ATTRIBUTES
	 */
	static std::uint32_t NEW_PARAM_OFFSET;

};


} /* namespace sep */
#endif /* BASEENVIRONMENT_H_ */
