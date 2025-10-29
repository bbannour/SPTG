/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef CONTAINER_TYPEDEF_COLOLECTION_H_
#define CONTAINER_TYPEDEF_COLOLECTION_H_


#include <collection/List.h>

#include <collection/Vector.h>



namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// MACRO FOR TYPEDEF DEFINITION
////////////////////////////////////////////////////////////////////////////////


#define AVM_TYPEDEF_COLLECTION_CLASS(ClassName)            \
public:                                                    \
	typedef List  < ClassName * > ListOfPtr;               \
	typedef Vector< ClassName * > VectorOfPtr;             \
	typedef List  < const ClassName * > ListOfConstPtr;    \
	typedef Vector< const ClassName * > VectorOfConstPtr;  \
private:


}

#endif /*CONTAINER_TYPEDEF_COLOLECTION_H_*/

