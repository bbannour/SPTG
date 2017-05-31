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


bool BaseCompiledForm::USE_ONLY_ID = false;



/**
 * CONSTRUCTOR
 * Default
 */
BaseCompiledForm::BaseCompiledForm(class_kind_t aClassKind,
		BaseAvmProgram * aContainer, const ObjectElement * astElement)
: ObjectElement( aClassKind , aContainer , ( (astElement != NULL) ?
		astElement->getModifier() : Modifier::PROPERTY_UNDEFINED_MODIFIER ) ),
mAstElement( astElement )
{
	//!! NOTHING

//		updateFullyQualifiedNameID();
}

BaseCompiledForm::BaseCompiledForm(class_kind_t aClassKind,
		BaseAvmProgram * aContainer, const std::string & aNameID)
: ObjectElement( aClassKind , aContainer, aNameID ),
mAstElement( NULL )
{
	//!! NOTHING
}

BaseCompiledForm::BaseCompiledForm(
		class_kind_t aClassKind, BaseAvmProgram * aContainer,
		const ObjectElement * astElement, const Modifier & aModifier)
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
		BaseAvmProgram * aContainer, const ObjectElement * astElement,
		const Modifier & aModifier, const std::string & aFullyQualifiedNameID)
: ObjectElement( aClassKind , aContainer ,
		aModifier , aFullyQualifiedNameID , "" ),
mAstElement( astElement )
{
	updateNameID();
}

BaseCompiledForm::BaseCompiledForm(
		class_kind_t aClassKind, BaseAvmProgram * aContainer,
		const ObjectElement * astElement, const Modifier & aModifier,
		const std::string & aFullyQualifiedNameID, const std::string & aNameID)
: ObjectElement( aClassKind , aContainer ,
		aModifier , aFullyQualifiedNameID , aNameID ),
mAstElement( astElement )
{
	//!! NOTHING
}


/**
 * Serialization
 */
void BaseCompiledForm::toStreamStaticCom(OutStream & out, const BF & comBF)
{
	out << /*TAB <<*/ "{";

	if( comBF.is< BaseInstanceForm >() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )

		out << EOL_TAB2 << str_header( comBF.to_ptr< BaseInstanceForm >() ) << EOL;

AVM_ELSE

		out << EOL_TAB2
			<< comBF.to_ptr< BaseInstanceForm >()->getFullyQualifiedNameID()
			<< EOL;

AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
	}
	else if( comBF.is< AvmCode >() )
	{
		if( comBF.to_ptr< AvmCode >()->nonempty() )
		{
			ScopeIncrIndent asii(out);

			comBF.to_ptr< AvmCode >()->toStreamRoutine( out );
		}
		else
		{
			//!! EMPTY
		}
	}
	else
	{
		comBF.toStream( out << EOL_INCR_INDENT );
		out << DECR_EOL;
	}

	out << TAB << "}" << EOL;
}


void BaseCompiledForm::toStreamStaticCom(OutStream & out,
		const ListOfInstanceOfBuffer & ieBuffers)
{
	ListOfInstanceOfBuffer::const_iterator itBuffer = ieBuffers.begin();
	ListOfInstanceOfBuffer::const_iterator itBufferEnd = ieBuffers.end();
	for( ; itBuffer != itBufferEnd ; ++itBuffer )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
		out << TAB2 << str_header( *itBuffer ) << EOL;
AVM_ELSE
		out << TAB2 << (*itBuffer)->getFullyQualifiedNameID() << EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
	}
}


void BaseCompiledForm::toStreamStaticCom(OutStream & out,
		const ListOfInstanceOfPort & iePorts)
{
	ListOfInstanceOfPort::const_iterator itPort = iePorts.begin();
	ListOfInstanceOfPort::const_iterator itPortEnd = iePorts.end();
	for( ; itPort != itPortEnd ; ++itPort )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
		out << TAB2 << str_header( *itPort ) << EOL;
AVM_ELSE
		out << TAB2 << (*itPort)->getFullyQualifiedNameID() << EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
	}
}


}
