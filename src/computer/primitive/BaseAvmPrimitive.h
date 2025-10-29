/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASEAVMPRIMITIVE_H_
#define BASEAVMPRIMITIVE_H_

#include <common/AvmObject.h>

#include <computer/instruction/InstructionEnvironment.h>


namespace sep
{


class AvmCode;
class AvmPrimitiveProcessor;

class ExecutionData;
class EvaluationEnvironment;
class ExecutionEnvironment;



class BaseAvmPrimitive   :   public AvmObject
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseAvmPrimitive(AvmPrimitiveProcessor & aProcessor)
	: AvmObject( ),
	PRIMITIVE_PROCESSOR( aProcessor )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseAvmPrimitive()
	{
		//!! NOTHING
	}


	/**
	 * the RUN statement
	 */

	inline virtual bool run(ExecutionEnvironment & ENV)
	{
		//!! NOTHING

		return( true );
	}


	/**
	 * the RESUME instruction
	 */
	virtual bool resume(ExecutionEnvironment & ENV);


	/**
	 * the EVAL instruction
	 */
	virtual bool seval(EvaluationEnvironment & ENV);

	/**
	 * the EVAL x 2 instruction
	 */
	virtual bool sevalx2(EvaluationEnvironment & ENV);



protected:
	/**
	 * ATTRIBUTES
	 */
	AvmPrimitiveProcessor & PRIMITIVE_PROCESSOR;


};




/**
 * Macro for smart primitive declaration.
 */
#define AVM_PRIMITIVE_CLASS_HEADER(classname, supername)                       \
class classname :  public supername                                            \
{                                                                              \
public:                                                                        \
	classname(AvmPrimitiveProcessor & aProcessor)                              \
	: supername( aProcessor )                                                  \
	{ /*!! NOTHING !!*/ }                                                      \
	virtual ~classname()                                                       \
	{ /*!! NOTHING !!*/ }



////////////////////////////////////////////////////////////////////////////////
///// PRIMITIVE:> RUN
////////////////////////////////////////////////////////////////////////////////

#define AVM_PRIMITIVE_RUN_CLASS_HEADER(classname, supername)                   \
AVM_PRIMITIVE_CLASS_HEADER(AvmPrimitive_##classname, supername)                \
	virtual bool run(ExecutionEnvironment & ENV) override;


#define AVM_PRIMITIVE_RUN_CLASS(classname, supername)                          \
AVM_PRIMITIVE_RUN_CLASS_HEADER(classname, supername)                           \
};


#define AVM_PRIMITIVE_BASE_RUN_CLASS(classname)                                \
AVM_PRIMITIVE_RUN_CLASS_HEADER(classname, BaseAvmPrimitive)                    \
};



#define AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(classname, supername)            \
AVM_PRIMITIVE_CLASS_HEADER(AvmPrimitive_##classname, supername)                \
	virtual bool run(ExecutionEnvironment & ENV) override;                     \
	virtual bool resume(ExecutionEnvironment & ENV) override;


#define AVM_PRIMITIVE_RUN_RESUME_CLASS(classname, supername)                   \
AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(classname, supername)                    \
};



////////////////////////////////////////////////////////////////////////////////
///// PRIMITIVE:> SEVAL
////////////////////////////////////////////////////////////////////////////////

#define AVM_PRIMITIVE_EVAL_CLASS_HEADER(classname, supername)                  \
AVM_PRIMITIVE_CLASS_HEADER(AvmPrimitive_##classname, supername)                \
	virtual bool seval(EvaluationEnvironment & ENV) override;


#define AVM_PRIMITIVE_EVAL_CLASS(classname, supername)                         \
AVM_PRIMITIVE_EVAL_CLASS_HEADER(classname, supername)                          \
};



////////////////////////////////////////////////////////////////////////////////
///// PRIMITIVE:> RUN & SEVAL
////////////////////////////////////////////////////////////////////////////////

#define AVM_PRIMITIVE_RUN_EVAL_CLASS_HEADER(classname, supername)              \
AVM_PRIMITIVE_CLASS_HEADER(AvmPrimitive_##classname, supername)                \
	virtual bool run(ExecutionEnvironment & ENV) override;                     \
	virtual bool seval(EvaluationEnvironment & ENV) override;


#define AVM_PRIMITIVE_RUN_EVAL_CLASS(classname, supername)                     \
AVM_PRIMITIVE_RUN_EVAL_CLASS_HEADER(classname, supername)                      \
};




}

#endif /* BASEAVMPRIMITIVE_H_ */
