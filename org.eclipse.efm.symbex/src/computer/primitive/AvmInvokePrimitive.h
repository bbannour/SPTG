/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMINVOKEPRIMITIVE_H_
#define AVMINVOKEPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


class AvmProgram;
class APExecutionData;
class ArrayBF;
class BF;
class BaseAvmProgram;


AVM_PRIMITIVE_RUN_EVAL_CLASS(InvokeNew, BaseAvmPrimitive)


AVM_PRIMITIVE_CLASS_HEADER(AvmBaseInvokePrimitive, BaseAvmPrimitive)
	bool pushLocalVar1(ExecutionEnvironment & ENV,
			const BaseAvmProgram & aProgram, const BF & aParam);

	bool pushLocalVars(ExecutionEnvironment & ENV,
			const BaseAvmProgram & aProgram, ArrayBF * params);

	bool pushLocalVars(ExecutionEnvironment & ENV,
			const BaseAvmProgram & aProgram);

	bool popLocalVars(APExecutionData & anED);
};


AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(InvokeRoutine, AvmBaseInvokePrimitive)
		bool run(ExecutionEnvironment & ENV, const AvmProgram & anAvmProgram);

		bool run(ExecutionEnvironment & ENV,
				const AvmProgram & anAvmProgram, const BF & aParam);
};

AVM_PRIMITIVE_RUN_RESUME_CLASS(InvokeTransition, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_EVAL_CLASS(InvokeMethod, BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(InvokeFunction, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_RESUME_CLASS(InvokeProgram, AvmBaseInvokePrimitive)


AVM_PRIMITIVE_EVAL_CLASS(InvokeLambdaApply, BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(InvokeLambdaLet, BaseAvmPrimitive)




}

#endif /* AVMINVOKEPRIMITIVE_H_ */
