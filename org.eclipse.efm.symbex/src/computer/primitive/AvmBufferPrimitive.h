/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 janv. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMBUFFERPRIMITIVE_H_
#define AVMBUFFERPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{

// BUFFER MANAGEMENT
AVM_PRIMITIVE_RUN_CLASS(APPEND,  BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(REMOVE,  BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(CLEAR,   BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RESIZE,  BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(PUSH,            BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_EVAL_CLASS(ASSIGN_TOP, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_EVAL_CLASS(TOP,        BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_EVAL_CLASS(POP,        BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_EVAL_CLASS(POP_FROM,   BaseAvmPrimitive)


AVM_PRIMITIVE_EVAL_CLASS(EMPTY,     BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(NONEMPTY,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(SINGLETON, BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(POPULATED, BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(FULL,      BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(CONTAINS,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(IN,  		 BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(NOTIN,     BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(SIZE,      BaseAvmPrimitive)


}

#endif /* AVMBUFFERPRIMITIVE_H_ */
