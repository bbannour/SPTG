/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EVALUATIONENVIRONMENT_H_
#define EVALUATIONENVIRONMENT_H_

#include <computer/BaseEnvironment.h>

#include <common/AvmPointer.h>

#include <computer/primitive/AvmPrimitiveProcessor.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>


namespace sep
{


class AvmCode;
class AvmPrimitiveProcessor;
class AvmProgram;

class BF;
class BuiltinForm;

class RuntimeID;

class UniFormIdentifier;


class EvaluationEnvironment :
		public BaseEnvironment ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( EvaluationEnvironment )
{

public :
	/**
	 * ATTRIBUTES
	 */

	////////////////////////////////////////////////////////////////////////////
	// OUTPUTs
	///////////////////////////////////////////////////////////////////////////
	APExecutionData outED;

	BF outVAL;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	EvaluationEnvironment(AvmPrimitiveProcessor & aPrimitiveProcessor)
	: BaseEnvironment( aPrimitiveProcessor ),
	outED( inED ),
	outVAL( )
	{
		//!! NOTHING
	}


	/**
	* CONSTRUCTOR
	* Copy
	*/
	explicit EvaluationEnvironment(const EvaluationEnvironment & form)
	: BaseEnvironment( form ),
	outED( form.outED ),
	outVAL( form.outVAL )
	{
		//!! NOTHING
	}


	/**
	* CONSTRUCTOR
	* Copy for eval
	*/
	EvaluationEnvironment(BaseEnvironment & form)
	: BaseEnvironment( form ),
	outED( inED ),
	outVAL( )
	{
		//!! NOTHING
	}

	EvaluationEnvironment(BaseEnvironment & form, const BF & bf)
	: BaseEnvironment( form , bf ),
	outED( inED ),
	outVAL( )
	{
		//!! NOTHING
	}

	EvaluationEnvironment(BaseEnvironment & form, const APExecutionData & anED)
	: BaseEnvironment( form , anED ),
	outED( anED ),
	outVAL( )
	{
		//!! NOTHING
	}

	EvaluationEnvironment(BaseEnvironment & form, const APExecutionData & anED,
			const BFCode & aCode)
	: BaseEnvironment(form , anED , aCode),
	outED( anED ),
	outVAL( )
	{
		//!! NOTHING
	}

	EvaluationEnvironment(BaseEnvironment & form, const APExecutionData & anED,
			const RuntimeID & aRID)
	: BaseEnvironment( form , anED , aRID ),
	outED( anED ),
	outVAL( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~EvaluationEnvironment()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * OUTPUTS
	*/
	inline virtual bool hasOutput() const
	{
		return( outED.valid() );
	}

	inline virtual bool hasntOutput() const
	{
		return( outED.invalid() && outVAL.invalid() );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	///// the EVAL statement
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	inline bool eval(const BF & bf)
	{
		return( seval( bf ) );
	}

	inline bool evalCondition(const BF & bf)
	{
		return( seval( bf ) );
	}

	inline bool evalBoolean(const BF & bf)
	{
		return( seval( bf ) );
	}

	inline bool evalOffset(const BF & bf)
	{
		return( seval( bf ) );
	}


	// For filters
	bool eval(const APExecutionData & anED, const RuntimeID & aRID,
			const BF & bf);

	bool eval(const APExecutionData & anED, const RuntimeID & aRID,
			const BFCode & aCode);


	////////////////////////////////////////////////////////////////////////////
	///// the EVAL statement
	////////////////////////////////////////////////////////////////////////////


	inline bool decode_seval()
	{
		return( PRIMITIVE_PROCESSOR.decode_seval(*this) );
	}

	inline bool seval()
	{
		return( PRIMITIVE_PROCESSOR.seval(*this) );
	}

	inline bool seval(ARGS_ENV * anARG)
	{
		mARG = anARG;

		return( PRIMITIVE_PROCESSOR.seval_wrt_ARG(*this) );
	}

	inline bool seval(const BF & bf)
	{
		inFORM = bf;

		return( PRIMITIVE_PROCESSOR.decode_seval(*this) );
	}

	inline bool sevalChained(const BF & bf)
	{
		inED = outED;

		inFORM = bf;

		return( PRIMITIVE_PROCESSOR.decode_seval(*this) );
	}


	/**
	 * TOOLS
	 */
	BF ioSubst(const APExecutionData & apED, AvmProgram * aProgram,
			AvmCode * progIO, AvmCode * traceIO, const BF & aCode);


	/**
	 * CHECK SATISFIABILITY
	 */
	bool evalFormula(const APExecutionData & anED, const RuntimeID & aRID,
			AvmProgram * aProgram, const BF & anExpr);

	inline bool evalFormula(const APExecutionData & anED,
			const RuntimeID & aRID, const BF & anExpr)
	{
		return( evalFormula(anED, aRID, NULL, anExpr) );
	}

	inline bool evalFormula(const ExecutionContext & anEC,
			AvmProgram * aProgram, const BF & anExpr)
	{
		inEC = (& anEC);

		inED = anEC.getAPExecutionData();

		return( evalFormula(inED, inED->getSystemRID(), aProgram, anExpr) );
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;

};


}

#endif /* EVALUATIONENVIRONMENT_H_ */
