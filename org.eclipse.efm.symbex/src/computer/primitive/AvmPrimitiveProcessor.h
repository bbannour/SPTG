/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMPRIMITIVEPROCESSOR_H_
#define AVMPRIMITIVEPROCESSOR_H_

#include <collection/Typedef.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


class AvmPrimitive_EvalExpressionALU;
class AvmPrimitive_InvokeRoutine;
class AvmProgram;

class BaseAvmPrimitive;
class Builder;

class Configuration;

class EvaluationEnvironment;
class ExecutionEnvironment;

class Loader;

class SymbexEngine;


class AvmPrimitiveProcessor
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef Vector< BaseAvmPrimitive * >  VectorOfAvmPrimitive;

	/**
	 * ATTRIBUTES
	 */
	SymbexEngine & mSymbexEngine;

	Configuration & mConfiguration;

	VectorOfAvmPrimitive AVM_PRIMITIVE_TABLE;

	AvmPrimitive_EvalExpressionALU * DEFAULT_EVAL_EXPRESSION_ALU;

	AvmPrimitive_InvokeRoutine * DEFAULT_INVOKE_ROUTINE;

	BaseAvmPrimitive * DEFAULT_AVM_PRIMITIVE;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmPrimitiveProcessor(
			SymbexEngine & aSymbexEngine, Configuration & aConfiguration)
	: mSymbexEngine( aSymbexEngine ),
	mConfiguration( aConfiguration ),

	AVM_PRIMITIVE_TABLE( ),
	DEFAULT_EVAL_EXPRESSION_ALU( NULL ),
	DEFAULT_INVOKE_ROUTINE( NULL ),
	DEFAULT_AVM_PRIMITIVE( NULL )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmPrimitiveProcessor();


	/**
	 * GETTER - SETTER
	 * mConfiguration
	 * mSymbexEngine
	 */
	inline SymbexEngine & getSymbexEngine()
	{
		return( mSymbexEngine );
	}

	inline Configuration & getConfiguration()
	{
		return( mConfiguration );
	}


	/**
	 * GETTER
	 * Builder
	 * Loader
	 */
	Builder & getBuilder();

	Loader & getLoader();


	/**
	 * CONFIGURE
	 */
	bool configure();

	bool configureOther();

	bool configureMeta();

	bool configureLambdaPrimitive();

	bool configureActivityPrimitive();

	bool configureStatusPrimitive();

	bool configureConcurrencyPrimitive();
	bool configureBasicPrimitive();

	bool configureArithmeticPrimitive();
	bool configureBitwisePrimitive();
	bool configureLogicPrimitive();

	bool configureLookupPrimitive();
	bool configureMathematicPrimitive();

	bool configureStringPrimitive();

	bool configureIoltPrimitive();



	/**
	 * the RUN statement
	 */

	void postRun(ExecutionContext & anEC, ListOfAPExecutionData & runEDS);
	void postRun(ExecutionContext & anEC, ExecutionEnvironment & ENV);


	void init(ExecutionContext & anEC);


	void run(ExecutionContext & anEC);

	bool run(avm_offset_t opOffset, ExecutionEnvironment & ENV);


	bool invokeRoutine(ExecutionEnvironment & ENV,
			AvmProgram * aProgram, const BF & aParam);


	/**
	 * the RESUME instruction
	 */
	bool resume(ExecutionEnvironment & ENV);

	bool decode_resume(ExecutionEnvironment & ENV);


	/**
	 * the DECODE EVAL instruction
	 */
	bool seval(EvaluationEnvironment & ENV);

	bool seval_wrt_ARG(EvaluationEnvironment & ENV);


	bool decode_seval(EvaluationEnvironment & ENV);

};


} /* namespace sep */

#endif /* AVMPRIMITIVEPROCESSOR_H_ */
