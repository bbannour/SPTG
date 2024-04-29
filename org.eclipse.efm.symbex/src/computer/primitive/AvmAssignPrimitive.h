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

#ifndef AVMASSIGNPRIMITIVE_H_
#define AVMASSIGNPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


AVM_PRIMITIVE_RUN_EVAL_CLASS(Assignment, BaseAvmPrimitive)

//AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignmentOr, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignmentAfter, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignmentOpAfter, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignmentRef, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignmentMacro, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignNewFresh, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(AssignReset, BaseAvmPrimitive)


}

#endif /* AVMASSIGNPRIMITIVE_H_ */
