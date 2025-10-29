/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 mars 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMMETAPRIMITIVE_H_
#define AVMMETAPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


AVM_PRIMITIVE_RUN_EVAL_CLASS(Informal, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(Trace, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(Debug, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(Comment, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_EVAL_CLASS(Quote, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_EVAL_CLASS(MetaEval, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(MetaRun, BaseAvmPrimitive)



} /* namespace sep */
#endif /* AVMMETAPRIMITIVE_H_ */
