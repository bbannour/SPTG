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

#ifndef AVMSEQUENCEPRIMITIVE_H_
#define AVMSEQUENCEPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/expression/AvmCode.h>


namespace sep
{


AVM_PRIMITIVE_RUN_CLASS(AtomicSequence, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(Sequence, BaseAvmPrimitive)
	bool run(ExecutionEnvironment & ENV,
		AvmCode::const_iterator itOperand, AvmCode::const_iterator endOperand);
};


AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(SideSequence, BaseAvmPrimitive)
	bool run(ExecutionEnvironment & ENV,
		AvmCode::const_iterator itOperand, AvmCode::const_iterator endOperand);
};


AVM_PRIMITIVE_RUN_RESUME_CLASS_HEADER(WeakSequence, BaseAvmPrimitive)
	bool run(ExecutionEnvironment & ENV,
		AvmCode::const_iterator itOperand, AvmCode::const_iterator endOperand);
};



}

#endif /* AVMSEQUENCEPRIMITIVE_H_ */
