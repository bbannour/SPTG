/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 avr. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#include "PropertyElement.h"

#include <fml/infrastructure/Machine.h>


namespace sep
{


PropertyElement::PropertyElement(class_kind_t aClassKind, Machine * aContainer,
		const Modifier & aModifier, const PropertyElement & aPattern)
: ObjectElement( aClassKind , aContainer , aModifier , aPattern )
{
	//!! NOTHING
}


} /* namespace sep */
