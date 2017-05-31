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

#ifndef AVMITERATIONPRIMITIVE_H_
#define AVMITERATIONPRIMITIVE_H_

#include <common/BF.h>
#include <computer/primitive/BaseAvmPrimitive.h>


namespace sep
{


AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(For, BaseAvmPrimitive)
	bool run(ExecutionEnvironment & ENV, const BF & initStmnt);
};


AVM_PRIMITIVE_RUN_CLASS(Foreach, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_RESUME_CLASS(WhileDo, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_RESUME_CLASS(DoWhile, BaseAvmPrimitive)


}

#endif /* AVMITERATIONPRIMITIVE_H_ */
