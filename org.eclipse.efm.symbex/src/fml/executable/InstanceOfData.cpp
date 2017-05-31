/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "InstanceOfData.h"

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionFactory.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>


namespace sep
{


/**
 * DEFAULT
 * Empty TableOfSymbol
 */
TableOfSymbol InstanceOfData::NULL_TABLE_OF_SYMBOL(0);


/**
 * SETTER
 * updateFullyQualifiedNameID()
 */
void InstanceOfData::updateFullyQualifiedNameID()
{
	if( hasAstElement() )
	{
		std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();

		std::string::size_type pos =
				aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
		if( pos != std::string::npos )
		{
			setFullyQualifiedNameID( (getModifier().hasFeatureConst() ?
					"const" : "inst") + aFullyQualifiedNameID.substr(pos) );
		}
		else
		{
			setFullyQualifiedNameID( aFullyQualifiedNameID );
		}
	}
	else if( isTypedEnum() )
	{
		std::string aFullyQualifiedNameID = getFullyQualifiedNameID();

		std::string::size_type pos =
				aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

		if( pos != std::string::npos )
		{
			setFullyQualifiedNameID( "enum" + aFullyQualifiedNameID.substr(pos) );
		}
	}
	else
	{
		setFullyQualifiedNameID("");
	}

	updateNameID();
}


/**
 * GETTER - SETTER
 * The Identifier
 */
void InstanceOfData::updateNameID()
{
	if( hasParent() )
	{
		std::string ufiSuffix =
				NamedElement::extractNameID( mFullyQualifiedNameID );

		if( getParent()->getTypeSpecifier()->isTypedArray() )
		{
			InstanceOfData * aParent = getParent();
			while( (aParent != NULL) &&
					aParent->getTypeSpecifier()->isTypedArray() )
			{
				aParent = aParent->getParent();
			}

			if( aParent != NULL )
			{
				setNameID( aParent->getNameID() + "." + ufiSuffix );
			}
			else
			{
				setNameID( ufiSuffix );
			}
		}
		else
		{
			setNameID( getParent()->getNameID() + "." + ufiSuffix );
		}
	}
	else if( hasDataPath() )
	{
		std::ostringstream oss;

		TableOfSymbol::const_iterator it = getDataPath()->begin();
		TableOfSymbol::const_iterator itEnd = getDataPath()->end();
		for( ; it != itEnd ; ++it )
		{
			switch( (*it).getPointerNature() )
			{
				case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
				case IPointerDataNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
				case IPointerDataNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
				{
					oss << "." << NamedElement::extractNameID( (*it).getFullyQualifiedNameID() );
					break;
				}
				case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
				{
					oss << "[" << (*it).getOffset() << "]";
					break;
				}
				case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
				{
					oss << "[" << (*it).strValue() << "]";
					break;
				}
				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "InstanceOfData::updateNameID:> Unexpected "
								"POINTER NATURE for the instance of data :>\n"
							<< (*it).toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;
					break;
				}
			}
		}
		setNameID( oss.str() );
	}
	else
	{
		BaseInstanceForm::updateNameID();
	}
}


/**
 * GETTER
 * mOnWriteRoutine
 */
const BFCode & InstanceOfData::getOnWriteCode() const
{
	return( (mOnWriteRoutine != NULL) ?
			mOnWriteRoutine->getCode() : BFCode::REF_NULL );
}


/**
 * GETTER - SETTER
 * mValue
 */
ArrayBF * InstanceOfData::getArrayValue() const
{
	return( mValue.as_ptr< ArrayBF >() );
}

bool InstanceOfData::hasArrayValue() const
{
	return( mValue.is< ArrayBF >() );
}


BuiltinArray * InstanceOfData::getBuiltinArrayValue() const
{
	return( mValue.as_ptr< BuiltinArray >() );
}

bool InstanceOfData::hasBuiltinArrayValue() const
{
	return( mValue.is< BuiltinArray >() );
}


/**
 * GETTER - SETTER
 * mRelativeOffsetPath
 */
std::string InstanceOfData::strOffsetPath(const std::string & tab) const
{
	if( hasDataPath() )
	{
		std::ostringstream oss;

		// +1 for << this >> which is the root of the path
		avm_size_t pathLength = mRelativeDataPath->size() + 1;

		oss << tab << "[ " << mRelativeOffsetPath[0];
		for( avm_size_t k = 1 ; k < pathLength ; ++k )
		{
			oss << " , " << mRelativeOffsetPath[k];
		}
		oss << " ]";

		return( oss.str() );
	}

	return( "" );
}

void InstanceOfData::updateOffsetPath()
{
	if( isUfiOffsetPointer() && hasDataPath() )
	{
		// +1 for << this >> which is the root of the path
		avm_size_t pathLength = mRelativeDataPath->size() + 1;

		mRelativeOffsetPath = new avm_size_t[ pathLength ];

		mRelativeOffsetPath[0] = this->getOffset();
		TableOfSymbol::const_iterator itPath = getDataPath()->begin();
		for( avm_size_t k = 1 ; k < pathLength ; ++k, ++itPath )
		{
			mRelativeOffsetPath[k] = (*itPath).getOffset();
		}
	}
}


/**
 * GETTER - SETTER
 * mPointerNature
 */
bool InstanceOfData::isConcreteArrayIndex()
{
	return( isUfiOffsetPointer() && hasParent()
			&& getParent()->isTypedArray() );
}

bool InstanceOfData::isConcreteStructAttribute()
{
	return( hasParent() && isUfiOffsetPointer()
			&& getParent()->hasTypeStructureOrChoiceOrUnion() );
}


/**
 * Format a value w.r.t. its type
 */
void InstanceOfData::formatStream(
		OutStream & out, const BF & bfValue) const
{
	if( bfValue.is< ArrayBF >() )
	{
		formatStream(out, bfValue.as_ref< ArrayBF >());
	}
	else if( hasTypeSpecifier() )
	{
		getTypeSpecifier()->formatStream(out, bfValue);
	}
	else
	{
		out << bfValue.str();
	}
}


void InstanceOfData::formatStream(
		OutStream & out, const ArrayBF & arrayValue) const
{
	if( hasTypeSpecifier() )
	{
		getTypeSpecifier()->formatStream(out, arrayValue);
	}
	else
	{
		out << arrayValue[0].str();
		for( avm_size_t offset = 1 ; offset < arrayValue.size() ; ++offset )
		{
			out << " , " << arrayValue[offset].str();
		}
	}
}


/**
 * Serialization
 */
void InstanceOfData::strHeader(OutStream & out) const
{
	out << getModifier().toString() << "var< id:" << getOffset() << ", ptr:"
		<< IPointerDataNature::strPointer( getPointerNature() )
		<< ( hasOffsetPath() ? strOffsetPath(", mem:") : "" ) << " > "
		<< ( hasTypeSpecifier() ? getTypeSpecifier()->strT() : "" )
		<< " " << getFullyQualifiedNameID();

AVM_IF_DEBUG_FLAG2_AND( COMPILING , QUALIFIED_NAME_ID , hasValue() )
	out << " =";
	strValue( out );
AVM_ENDIF_DEBUG_FLAG2_AND( COMPILING , QUALIFIED_NAME_ID )

	AVM_DEBUG_REF_COUNTER(out);
}

std::string InstanceOfData::strHeaderId() const
{
	StringOutStream oss;

	oss << getModifier().toString() << "var< id:" << getOffset() << ", ptr:"
			<< IPointerDataNature::strPointer( getPointerNature() )
			<< ( hasOffsetPath() ? strOffsetPath(", mem:") : "" ) << " > "
			<< ( hasTypeSpecifier() ? getTypeSpecifier()->strT() : "" )
			<< " " << getNameID();

AVM_IF_DEBUG_FLAG2_AND( COMPILING , QUALIFIED_NAME_ID , hasValue() )
	oss << " =";
	strValue( oss );
AVM_ENDIF_DEBUG_FLAG2_AND( COMPILING , QUALIFIED_NAME_ID )

	return( oss.str() );
}


void InstanceOfData::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	bool isEmpty = true;

	out << TAB << getModifier().toString_not( Modifier::FEATURE_CONST_KIND )
		<< ( getModifier().hasFeatureConst() ? "const" : "var" )
		<< "< id:" << getOffset() << ", ptr:"
		<< IPointerDataNature::strPointer( getPointerNature() )
		<< ( hasOffsetPath() ? strOffsetPath(", mem:") : "" )
		<< " > " ;

	if( hasTypeSpecifier() )
	{
		out << getTypeSpecifier()->strT();
	}

	out << " " << getFullyQualifiedNameID() << " '" << getNameID() << "'";
	AVM_DEBUG_REF_COUNTER(out);


AVM_IF_DEBUG_FLAG( COMPILING )
	out << " {" << EOL; isEmpty = false;

	if( hasAstElement() )
	{
		out << TAB2 << "//compiled = "
			<< getAstFullyQualifiedNameID() << ";" << EOL;
	}

	out << TAB2 << "//container = "
		<< (hasContainer() ? getContainer()->getFullyQualifiedNameID() : "NULL")
		<< ";" << EOL;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	if( hasParent() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "parent = " << str_header( getParent() ) << ";" << EOL;
	}

	if( hasAliasTarget() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "target = "
			<< str_header( getAliasTarget()->as< InstanceOfData >() )
			<< ";" << EOL;
	}

	if( hasCreatorContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#creator = " << getCreatorContainerRID().str()
			<< ";" << EOL;
	}

	if( hasRuntimeContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#container = " << getRuntimeContainerRID().str()
			<< ";" << EOL;
	}

	if( hasValue() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "value =";
		if( getValue().is< AvmCode >() )
		{
			out << str_indent( getValue().to_ptr< AvmCode >() ) << ";" << EOL;
		}
		else
		{
			strValue( out );
			out << ";" << EOL;
		}
	}

	if( hasBValue() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "bvalue =";
		if( getBValue().is< AvmCode >() )
		{
			out << str_indent( getBValue().to_ptr< AvmCode >() ) << ";" << EOL;
		}
		else
		{
			strBValue( out );
			out << ";" << EOL;
		}
	}

	if( hasMachinePath() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "path#machine:" << EOL;
		ArrayOfInstanceOfMachine::const_iterator it = getMachinePath()->begin();
		ArrayOfInstanceOfMachine::const_iterator itEnd = getMachinePath()->end();
		for( ; it != itEnd ; ++it )
		{
			out << TAB2 << (*it)->getFullyQualifiedNameID() << EOL;
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , DATA )
	if( hasDataPath() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "path#data:" << EOL_INCR_INDENT;

		getDataPath()->toStream(out);

		out << DECR_INDENT;
   }
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , DATA )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , DATA )
	if( hasAttribute() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "attribute:" << EOL_INCR_INDENT;

		getAttribute()->toStream(out);

		out << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , DATA )

	if(hasOnWriteRoutine() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "moe:" << EOL;

		if( hasOnWriteRoutine() )
		{
			out << TAB2 << "on_write = " << EOL_INCR2_INDENT;
			getOnWriteRoutine()->toStream(out);
			out << DECR2_INDENT;
		}
	}

	( isEmpty ? (out << ";") : (out << TAB << "}") ) << EOL_FLUSH;
}


}
