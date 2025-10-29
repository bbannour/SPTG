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

#ifndef AVMJUMPPRIMITIVE_H_
#define AVMJUMPPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{

AVM_PRIMITIVE_RUN_CLASS(Break, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Continue, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Return, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Exit, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(StepMark, BaseAvmPrimitive)



}

#endif /* AVMJUMPPRIMITIVE_H_ */
