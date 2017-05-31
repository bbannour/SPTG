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

#include "ModelOfComputationPart.h"

#include <fml/infrastructure/Machine.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
ModelOfComputationPart::ModelOfComputationPart(
		Machine * aContainer, const std::string aNameID)
: ObjectClassifier( CLASS_KIND_T( ModelOfComputationPart ) ,
		aContainer , aNameID)
{
	//!! NOTHING
}


/**
 * Serialization
 */
void ModelOfComputationPart::toStream(OutStream & os) const
{
	os << TAB << "@" << getNameID() << ":" << EOL;
}


}
