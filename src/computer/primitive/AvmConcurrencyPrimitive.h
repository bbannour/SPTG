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

AVM_PRIMITIVE_CLASS_HEADER(AvmBaseRdvPrimitive, BaseAvmPrimitive)

	bool buildRdvConfiguration(RdvConfigurationData & aRdvConf,
			avm_offset_t idx, ListOfExecutionData & syncEDS,
			bool & hasPossibleRdv, bool & hasPossibleMultiRdv);

	void computeRdv(ExecutionEnvironment & ENV,
			RdvConfigurationData & aRdvConf, avm_offset_t idx,
			bool & hasPossibleRdv, bool & hasPossibleMultiRdv);

};



AVM_PRIMITIVE_RUN_CLASS(Interleaving, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvInterleaving, AvmBaseRdvPrimitive)

AVM_PRIMITIVE_RUN_CLASS(PartialOrder, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvPartialOrder, AvmBaseRdvPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Asynchronous, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvAsynchronous, AvmBaseRdvPrimitive)

AVM_PRIMITIVE_RUN_CLASS(StrongSynchronous, BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(RdvStrongSynchronous, AvmBaseRdvPrimitive)


AVM_PRIMITIVE_RUN_CLASS_HEADER(WeakSynchronous, AvmBaseConcurrencyPrimitive)
	bool computeWeakSynchronous(ExecutionData & anInputED,
			ExecutionData & oneED, ExecutionData & otherED,
			CollectionOfExecutionData & listOfOutputED);

	bool computeWeakSynchronous(
			ExecutionData & anInputED, ExecutionData & oneED,
			ListOfExecutionData & listOfOtherED,
			CollectionOfExecutionData & listOfOutputED);

	bool computeWeakSynchronous(ExecutionData & anInputED,
			ListOfExecutionData & oneListOfED,
			ListOfExecutionData & otherListOfED,
			ListOfExecutionData & resultListOfED);
};

AVM_PRIMITIVE_RUN_CLASS(RdvWeakSynchronous, AvmPrimitive_WeakSynchronous)



AVM_PRIMITIVE_RUN_CLASS_HEADER(Parallel, BaseAvmPrimitive)
	void computeParallel(ExecutionData & refED,
			ListOfExecutionData & outEDS,
			ListOfExecutionData & parallelListOfOutputED,
			ListOfExecutionData & listOfOutputED);
};

AVM_PRIMITIVE_RUN_CLASS_HEADER(RdvParallel, AvmPrimitive_Parallel)
	void configureRdv(RdvConfigurationData & aRdvConf,
			ListOfExecutionData & syncEDS,
			bool & checkRdv, bool & hasMultiRdv, avm_offset_t idx);
};




AVM_PRIMITIVE_RUN_CLASS_HEADER(Product, AvmBaseConcurrencyPrimitive)
	bool computeProduct(ExecutionData & anInputED, ExecutionData & oneED,
			ExecutionData & otherED,
			CollectionOfExecutionData & listOfOutputED);

	bool computeProduct(ExecutionData & anInputED, ExecutionData & oneED,
			ListOfExecutionData & listOfOtherED,
			CollectionOfExecutionData & listOfOutputED);

	bool computeProduct(ExecutionData & anInputED,
			ListOfExecutionData & oneListOfED,
			ListOfExecutionData & otherListOfED,
			ListOfExecutionData & resultListOfED);
};



AVM_PRIMITIVE_RUN_CLASS(Synchronize, BaseAvmPrimitive)



}

#endif /* AVMCONCURRENCYPRIMITIVE_H_ */
