/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASE_SMARTPOINTERUTIL_H_
#define BASE_SMARTPOINTERUTIL_H_

#include <cstddef>

namespace sep
{

/**
 * MEMORY MANAGEMENT
 * INCR - DECR
 * REFCOUNT
 */

template< class T >
T * incrReferenceCount(T * anElement)
{
	if( anElement != NULL )
	{
		anElement->incrRefCount();
	}

	return( anElement );
}


/**
 * MEMORY MANAGEMENT
 * DESTROY
 * FORM
 */

class AvmObject;
class Element;


/**
 * SMART DESTROY POLICY
 * FORM
 */
struct DestroyObjectPolicy
{
	static void destroy(AvmObject * anObject);
};

void destroy(AvmObject * anObject);


struct DestroyElementPolicy
{
	static void destroy(Element * anObject);
};

extern void destroyElement(Element * anElement);


} /* namespace sep */

#endif /* BASE_SMARTPOINTERUTIL_H_ */
