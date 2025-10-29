/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 juin 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMMATHPRIMITIVE_H_
#define AVMMATHPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


// MIN - MAX
AVM_PRIMITIVE_EVAL_CLASS(MIN,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(MAX,  BaseAvmPrimitive)

// RANDOM
AVM_PRIMITIVE_EVAL_CLASS(RANDOM,  BaseAvmPrimitive)

// ABS
AVM_PRIMITIVE_EVAL_CLASS(ABS,  BaseAvmPrimitive)

// ROUNDING
AVM_PRIMITIVE_EVAL_CLASS(CEIL,     BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(FLOOR,    BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ROUND,    BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(TRUNCATE, BaseAvmPrimitive)


// MOD
AVM_PRIMITIVE_EVAL_CLASS(MOD,   BaseAvmPrimitive)

// EXP - LOG
AVM_PRIMITIVE_EVAL_CLASS(SQRT,  BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(EXP,   BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(LOG,   BaseAvmPrimitive)

// TRIGONOMETRIC
AVM_PRIMITIVE_EVAL_CLASS(SIN,   BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(COS,   BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(TAN,   BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(SINH,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(COSH,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(TANH,  BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(ASIN,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ACOS,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ATAN,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ATAN2, BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(ASINH, BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ACOSH, BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ATANH, BaseAvmPrimitive)



}

#endif /* AVMMATHPRIMITIVE_H_ */
