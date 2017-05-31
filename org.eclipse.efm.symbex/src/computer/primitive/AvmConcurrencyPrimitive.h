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

#ifndef AVMCONCURRENCYPRIMITIVE_H_
#define AVMCONCURRENCYPRIMITIVE_H_

#include <computer/primitive/AvmBaseConcurrencyPrimitive.h>
#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/runtime/ExecutionData.h>



namespace sep
{


class RdvConfigurationData;


AVM_PRIMITIVE_RUN_CLASS(Interleaving, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvInterleaving, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Asynchronous, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvAsynchronous, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(StrongSynchronous, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvStrongSynchronous, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS_HEADER(WeakSynchronous, AvmBaseConcurrencyPrimitive)
	bool computeWeakSynchronous(APExecutionData & anInputED,
			APExecutionData & oneED, APExecutionData & otherED,
			CollectionOfAPExecutionData & listOfOutputED);

	bool computeWeakSynchronous(
			APExecutionData & anInputED, APExecutionData & oneED,
			ListOfAPExecutionData & listOfOtherED,
			CollectionOfAPExecutionData & listOfOutputED);

	bool computeWeakSynchronous(APExecutionData & anInputED,
			ListOfAPExecutionData & oneListOfED,
			ListOfAPExecutionData & otherListOfED,
			ListOfAPExecutionData & resultListOfED);
};

AVM_PRIMITIVE_RUN_CLASS(RdvWeakSynchronous, AvmPrimitive_WeakSynchronous)



AVM_PRIMITIVE_RUN_CLASS_HEADER(Parallel, BaseAvmPrimitive)
	void computeParallel(APExecutionData & refED,
			ListOfAPExecutionData & outEDS,
			ListOfAPExecutionData & parallelListOfOutputED,
			ListOfAPExecutionData & listOfOutputED);
};

AVM_PRIMITIVE_RUN_CLASS_HEADER(RdvParallel, AvmPrimitive_Parallel)
	void configureRdv(RdvConfigurationData & aRdvConf,
			ListOfAPExecutionData & syncEDS, bool & checkRdv,
			bool & checkMultiRdv, bool & hasCom, avm_offset_t & idx);
};




AVM_PRIMITIVE_RUN_CLASS_HEADER(Product, AvmBaseConcurrencyPrimitive)
	bool computeProduct(APExecutionData & anInputED, APExecutionData & oneED,
			APExecutionData & otherED,
			CollectionOfAPExecutionData & listOfOutputED);

	bool computeProduct(APExecutionData & anInputED, APExecutionData & oneED,
			ListOfAPExecutionData & listOfOtherED,
			CollectionOfAPExecutionData & listOfOutputED);

	bool computeProduct(APExecutionData & anInputED,
			ListOfAPExecutionData & oneListOfED,
			ListOfAPExecutionData & otherListOfED,
			ListOfAPExecutionData & resultListOfED);
};



AVM_PRIMITIVE_RUN_CLASS(Synchronize, BaseAvmPrimitive)



}

#endif /* AVMCONCURRENCYPRIMITIVE_H_ */
