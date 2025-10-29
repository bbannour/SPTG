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

#ifndef AVMSTATUSPRIMITIVE_H_
#define AVMSTATUSPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


AVM_PRIMITIVE_EVAL_CLASS(StatusWas,    BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(StatusIs,     BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(StatusBeing,  BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(StatusWill,   BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(Changed,    BaseAvmPrimitive)
AVM_PRIMITIVE_EVAL_CLASS(ChangedTo,  BaseAvmPrimitive)



}

#endif /* AVMSTATUSPRIMITIVE_H_ */
