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

#ifndef AVMBITWISEPRIMITIVE_H_
#define AVMBITWISEPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


AVM_PRIMITIVE_EVAL_CLASS(BNOT,   BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(BAND,   BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(BOR,    BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(BXOR,   BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(LSHIFT, BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(RSHIFT, BaseAvmPrimitive)



}

#endif /* AVMBITWISEPRIMITIVE_H_ */
