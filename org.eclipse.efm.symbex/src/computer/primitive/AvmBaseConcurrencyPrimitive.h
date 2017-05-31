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

#ifndef AVMBASESCHEDULINGPRIMITIVE_H_
#define AVMBASESCHEDULINGPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{

AVM_PRIMITIVE_CLASS_HEADER(AvmBaseConcurrencyPrimitive, BaseAvmPrimitive)

	bool evalExclusive(APExecutionData & anInputED, APExecutionData & evalED,
			APExecutionData & otherED, CollectionOfAPExecutionData & listOfOutputED);

	bool evalExclusive(APExecutionData & anInputED, APExecutionData & evalED,
			ListOfAPExecutionData & listOfOtherED, CollectionOfAPExecutionData & listOfOutputED);

	bool evalExclusive(APExecutionData & anInputED, ListOfAPExecutionData & oneListOfED,
			APExecutionData & otherED, CollectionOfAPExecutionData & listOfOutputED);

};


}

#endif /* AVMBASESCHEDULINGPRIMITIVE_H_ */
