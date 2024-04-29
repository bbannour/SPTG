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
#include "BaseCompiledForm.h"

#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfPort.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
BaseCompiledForm::BaseCompiledForm(class_kind_t aClassKind,
		BaseAvmProgram * aContainer, const ObjectElement & astElement)
: ObjectElement( aClassKind , aContainer , astElement.getModifier() ),
//		( (astElement != nullptr) ?
//		astElement.getModifier() : Modifier::PROPERTY_UNDEFINED_MODIFIER ) ),
mAstElement( astElement )
{
	//!! NOTHING

//		updateFullyQualifiedNameID();
}

BaseCompiledForm::BaseCompiledForm(
		class_kind_t aClassKind, BaseAvmProgram * aContainer,
		const ObjectElement & astElement, const std::string & aNameID)
: ObjectElement( aClassKind , aContainer, aNameID ),
mAstElement( astElement )
{
	//!! NOTHING
}

BaseCompiledForm::BaseCompiledForm(
		class_kind_t aClassKind, BaseAvmProgram * aContainer,
		const ObjectElement & astElement, const Modifier & aModifier)
: ObjectElement( aClassKind , aContainer , aModifier ),
mAstElement( astElement )
{
	updateNameID();
}

/**
 * CONSTRUCTOR
 * Other
 */
BaseCompiledForm::BaseCompiledForm(class_kind_t aClassKind,
		BaseAvmProgram * aContainer, const ObjectElement & astElement,
		const Modifier & aModifier, const std::string & aFullyQualifiedNameID)
: ObjectElement( aClassKind , aContainer ,
		aModifier , aFullyQualifiedNameID , "" ),
mAstElement( astElement )
{
	updateNameID();
}

BaseCompiledForm::BaseCompiledForm(
		class_kind_t aClassKind, BaseAvmProgram * aContainer,
		const ObjectElement & astElement, const Modifier & aModifier,
		const std::string & aFullyQualifiedNameID, const std::string & aNameID)
: ObjectElement( aClassKind , aContainer ,
		aModifier , aFullyQualifiedNameID , aNameID ),
mAstElement( astElement )
{
	//!! NOTHING
}


}
