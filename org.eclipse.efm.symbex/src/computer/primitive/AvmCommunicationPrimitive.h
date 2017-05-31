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

#ifndef AVMCOMMUNICATIONPRIMITIVE_H_
#define AVMCOMMUNICATIONPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


AVM_PRIMITIVE_RUN_CLASS(Input, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(InputVar, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(InputEnv, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(InputBuffer, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(InputRdv, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(InputFrom, BaseAvmPrimitive)



AVM_PRIMITIVE_RUN_CLASS(Output, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(OutputTo, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(OutputVar, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(OutputEnv, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(OutputBuffer, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(OutputRdv, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_EVAL_CLASS(Present, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(Absent, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_EVAL_CLASS(OBS, BaseAvmPrimitive)


/*
 ***************************************************************************
 * AVM BUFFER MANAGING
 ***************************************************************************
 */
AVM_PRIMITIVE_RUN_CLASS(UpdateBuffer, BaseAvmPrimitive)



}

#endif /* AVMCOMMUNICATIONPRIMITIVE_H_ */
