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

#ifndef AVMSCHEDULINGPRIMITIVE_H_
#define AVMSCHEDULINGPRIMITIVE_H_

#include <computer/primitive/AvmBaseConcurrencyPrimitive.h>
#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{

AVM_PRIMITIVE_RUN_CLASS(Exclusive, sep::AvmBaseConcurrencyPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Nondeterminism, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Prior, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(ScheduleAndThen, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(ScheduleOrElse, BaseAvmPrimitive)


}

#endif /* AVMSCHEDULINGPRIMITIVE_H_ */
