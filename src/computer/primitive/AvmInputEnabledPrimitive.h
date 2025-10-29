/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 févr. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMINPUTENABLEDPRIMITIVE_H_
#define AVMINPUTENABLEDPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/Message.h>


namespace sep
{


AVM_PRIMITIVE_RUN_CLASS_HEADER(InputEnabled, BaseAvmPrimitive)
	void restoreMessage(
			const RuntimeID & rieRID, const InstanceOfBuffer * ieBuffer,
			ListOfMessage & saveMessages, ListOfExecutionData EDS);
};


} /* namespace sep */

#endif /* AVMINPUTENABLEDPRIMITIVE_H_ */
