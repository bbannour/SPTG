/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_MODELOFCOMPUTATIONPART_H_
#define FML_INFRASTRUCTURE_MODELOFCOMPUTATIONPART_H_

#include <fml/common/ObjectClassifier.h>

#include <common/AvmPointer.h>


namespace sep
{

class Machine;


class ModelOfComputationPart :
		public ObjectClassifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ModelOfComputationPart )
{

	AVM_DECLARE_CLONABLE_CLASS( ModelOfComputationPart )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ModelOfComputationPart(Machine * aContainer,
			const std::string aNameID = "moc");


	/**
	 * DESTRUCTOR
	 */
	virtual ~ModelOfComputationPart()
	{
		//!! NOTHING
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & os) const;


};


}

#endif /* FML_INFRASTRUCTURE_MODELOFCOMPUTATIONPART_H_ */
