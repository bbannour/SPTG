/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 juin 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMLOOKUPPRIMITIVE_H_
#define AVMLOOKUPPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/expression/BuiltinArray.h>



namespace sep
{


AVM_PRIMITIVE_EVAL_CLASS_HEADER(Lookup_Int,  BaseAvmPrimitive)
		static double lookup(double anInput,
				ArrayFloat * anInputTable, ArrayFloat * anOutputTable);
};


AVM_PRIMITIVE_EVAL_CLASS_HEADER(Lookup_IntExt,  BaseAvmPrimitive)
	static double lookup(double anInput,
			ArrayFloat * anInputTable, ArrayFloat * anOutputTable);
};


AVM_PRIMITIVE_EVAL_CLASS_HEADER(Lookup_Nearest,  BaseAvmPrimitive)
	static double lookup(double anInput,
			ArrayFloat * anInputTable, ArrayFloat * anOutputTable);
};


AVM_PRIMITIVE_EVAL_CLASS_HEADER(Lookup_Below, BaseAvmPrimitive)
	static double lookup(double anInput,
			ArrayFloat * anInputTable, ArrayFloat * anOutputTable);
};


AVM_PRIMITIVE_EVAL_CLASS_HEADER(Lookup_Above, BaseAvmPrimitive)
	static double lookup(double anInput,
			ArrayFloat * anInputTable, ArrayFloat * anOutputTable);
};


AVM_PRIMITIVE_EVAL_CLASS_HEADER(Lookup2D_IntExt, BaseAvmPrimitive)
	static double lookup2D(double anInput1, double anInput2,
			ArrayFloat * anInputTable1, ArrayFloat * anInputTable2,
			ArrayBF * anOutputTable);
};



}

#endif /* AVMLOOKUPPRIMITIVE_H_ */
