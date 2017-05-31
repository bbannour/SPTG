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
#include "BaseCompiler.h"

#include <fml/executable/ExecutableLib.h>

#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ChoiceTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/UnionTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/workflow/UniFormIdentifier.h>

#include <sew/Configuration.h>


namespace sep
{


/**
 * Pre-Compiling type specifier
 */
void BaseCompiler::precompileTypeSpecifier(
		AvmProgram * aContainer, const BF & bfType)
{
	TypeSpecifier aTypeSpecifier;

	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( bfType )
			<< "typedef for compiling !!!"
			<< SEND_EXIT;

	if( bfType.is< DataType >() )
	{
		DataType * aDataType = bfType.to_ptr< DataType >();

		if( aDataType->hasTypeContainer() )
		{
			aTypeSpecifier = compileContainerSpecifier(aContainer, aDataType);
		}
		else if( aDataType->isTypedInterval() )
		{
			aTypeSpecifier = compileIntervalSpecifier(aContainer, aDataType);
		}
		else if( aDataType->isTypedEnum() )
		{
			aTypeSpecifier = compileEnumerationSpecifier(aContainer, aDataType);
		}
		else if( aDataType->isTypedStructure() )
		{
			aTypeSpecifier = compileStructureSpecifier(aContainer, aDataType);
		}

		else if( aDataType->isTypedChoice() )
		{
			aTypeSpecifier = compileChoiceSpecifier(aContainer, aDataType);
		}

		else if( aDataType->isTypedUnion() )
		{
			aTypeSpecifier = compileUnionSpecifier(aContainer, aDataType);
		}

		else if( aDataType->isTypedAlias() )
		{
			aTypeSpecifier = compileTypeAliasSpecifier(aContainer, aDataType);
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected a typedef << " << bfType.str()
					<< " >> for compiling !!!"
					<< SEND_EXIT;
		}
	}

	else if( bfType.is< BaseTypeSpecifier >() )
	{
		//!! OK
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a typedef << " << bfType.str()
				<< " >> for compiling !!!"
				<< SEND_EXIT;
	}

	if( aTypeSpecifier.valid() )
	{
		aContainer->appendTypeSpecifier( aTypeSpecifier );
	}
}



/**
 * Compiling type specifier
 */
TypeSpecifier BaseCompiler::compileTypeSpecifier(
		AvmProgram * aContainer, const std::string & aTypeID)
{
	const TypeSpecifier & aType = TypeManager::getPrimitiveType( aTypeID );

	if( aType.valid() )
	{
		return( aType );
	}
	else
	{
		CompilationEnvironment compilENV(aContainer);

		const TypeSpecifier & aType = SymbolTable::searchTypeSpecifier(
				getConfiguration().getExecutableSystem(),
				compilENV.mCTX, aTypeID);

		if( aType.valid() )
		{
			return( aType );
		}
		else
		{
			aContainer->getAstElement()->errorLocation(AVM_OS_WARN)
					<< "Error while compiling type specifier << "
					<< aTypeID << " >>" << std::endl << std::endl;

			return( TypeManager::UNIVERSAL );
		}
	}
}


TypeSpecifier BaseCompiler::compileTypeSpecifier(
		AvmProgram * aContainer, const BF & bfType)
{
	if( bfType.invalid() )
	{
		return( TypeManager::UNIVERSAL );
	}

	else if( bfType.is< BaseTypeSpecifier >() )
	{
		return( bfType.as_bf< TypeSpecifier >() );
	}

	else if( bfType.is< UniFormIdentifier >() )
	{
		CompilationEnvironment compilENV(aContainer);

		const TypeSpecifier & aType = SymbolTable::searchTypeSpecifier(
				getConfiguration().getExecutableSystem(),
				compilENV.mCTX, bfType.str());

		if( aType.valid() )
		{
			return( aType );
		}
		else
		{
//			incrErrorCount();
			AVM_OS_WARN << bfType.to_ptr< UniFormIdentifier >()
					->errorLocation(aContainer->getAstElement())
					<< "Unfound data type form << " << bfType.str()
					<< " >>" << std::endl << std::endl;

			return( TypeManager::UNIVERSAL );
		}
	}

	else if( bfType.isnot< ObjectElement /*!DataType!*/ >() )
	{
		const TypeSpecifier & aType =
				TypeManager::getPrimitiveType( bfType.str() );

		if( aType.valid() )
		{
			return( aType );
		}
		else
		{
			AVM_OS_TODO_ALERT
					<< "Compilation of unknown type specificier << "
					<< bfType.str() << " >> !!!"
					<< SEND_ALERT;

			return( TypeManager::UNIVERSAL );
		}
	}

	else
	{
		CompilationEnvironment compilENV(aContainer);

		TypeSpecifier bfTS =  SymbolTable::searchTypeSpecifier(
				getConfiguration().getExecutableSystem(),
				compilENV.mCTX, bfType.to_ptr< ObjectElement >() );

		if( bfTS.valid() )
		{
			return( bfTS );
		}

		else  if( bfType.is< DataType >() )
		{
			DataType * aDataType = bfType.to_ptr< DataType >();

			if( aDataType->hasTypeContainer() )
			{
				bfTS = compileContainerSpecifier(aContainer, aDataType);
			}
			else if( aDataType->isTypedInterval() )
			{
				bfTS = compileIntervalSpecifier(aContainer, aDataType);
			}
			else if( aDataType->isTypedEnum() )
			{
				bfTS = compileEnumerationSpecifier(aContainer, aDataType);
			}
			else if( aDataType->isTypedStructure() )
			{
				bfTS = compileStructureSpecifier(aContainer, aDataType);
			}

			else if( aDataType->isTypedChoice() )
			{
				bfTS = compileChoiceSpecifier(aContainer, aDataType);
			}

			else if( aDataType->isTypedUnion() )
			{
				bfTS = compileUnionSpecifier(aContainer, aDataType);
			}

			else// if( aDataType->isTypedAlias() )
			{
				bfTS = compileTypeAliasSpecifier(aContainer, aDataType);
			}
		}

		if( bfTS.valid() )
		{
			if( bfTS.hasTypeEnumOrComposite() &&
					SymbolTable::searchTypeSpecifier(
							getConfiguration().getExecutableSystem(),
							compilENV.mCTX, bfTS.getAstElement()).invalid() )
			{
				aContainer->appendTypeSpecifier( bfTS );
			}

			return( bfTS );
		}
		else
		{
			aContainer->getAstElement()->errorLocation(AVM_OS_WARN)
					<< "Error while compiling type specifier << "
					<< bfType.str() << " >>" << std::endl << std::endl;

			return( TypeManager::UNIVERSAL );
		}


//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT
				<< "TODO:> compilation of unknown type specificier like : << "
				<< bfType.str() << " >> !!!"
				<< SEND_ALERT;

		return( TypeManager::UNIVERSAL );
	}
}


TypeSpecifier BaseCompiler::compileStructureSpecifier(
		AvmProgram * aContainer, DataType * aStructureT)
{
	ClassTypeSpecifier * theClassType;
	TypeSpecifier bfTS( theClassType = TypeManager::newClass(aStructureT) );

	BF aValue;
	TypeSpecifier aTypeSpecifier;

	TableOfVariable::const_raw_iterator it =
			aStructureT->getPropertyPart()->getVariables().begin();
	TableOfVariable::const_raw_iterator endIt =
			aStructureT->getPropertyPart()->getVariables().end();
	for( ; it != endIt ; ++it )
	{
		aTypeSpecifier = compileTypeSpecifier(aContainer, (it)->getType());

		InstanceOfData * anInstanceAttribute = new InstanceOfData(
				IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE,
				NULL, (it), aTypeSpecifier,
				theClassType->getSymbolData().size(), (it)->getModifier() );
		anInstanceAttribute->setNameID( (it)->getNameID() );

		aValue = (it)->getValue();
		if( aValue.valid() )
		{
			switch( aValue.classKind() )
			{
				case FORM_OPERATOR_KIND:

				case FORM_BUILTIN_BOOLEAN_KIND:
				case FORM_BUILTIN_CHARACTER_KIND:
				case FORM_BUILTIN_INTEGER_KIND:
				case FORM_BUILTIN_RATIONAL_KIND:
				case FORM_BUILTIN_FLOAT_KIND:
				case FORM_BUILTIN_STRING_KIND:
				case FORM_BUILTIN_IDENTIFIER_KIND:
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				//@deprecated
				//case FORM_EXPRESSION_GINAC_KIND:
				{
					anInstanceAttribute->setValue( aValue );

					break;
				}

				default:
				{
					if( (aValue == ExecutableLib::MACHINE_NULL)
						|| (aValue == ExecutableLib::CHANNEL_NIL)
						|| (aValue == ExecutableLib::PORT_NIL   )
						|| (aValue == ExecutableLib::BUFFER_NIL ) )
					{
						anInstanceAttribute->setValue( aValue );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Unexpected STRUCTURE ATTRIBUTE value "
									"for compileStructureSpecifier :>\n"
								<< aValue.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

//						anInstanceAttribute->setValue( mAvmcodeCompiler.
//								decode_compileExpression(aContainer, aValue) );
					}

					break;
				}
			}

		}

		theClassType->saveSymbolData(anInstanceAttribute);
	}

	theClassType->updateSize();

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileChoiceSpecifier(
		AvmProgram * aContainer, DataType * aChoiceT)
{
	ChoiceTypeSpecifier * theChoiceType;
	TypeSpecifier bfTS( theChoiceType = TypeManager::newChoice(aChoiceT) );

	BF aValue;
	TypeSpecifier aTypeSpecifier;

	TableOfVariable::const_raw_iterator it =
			aChoiceT->getPropertyPart()->getVariables().begin();
	TableOfVariable::const_raw_iterator endIt =
			aChoiceT->getPropertyPart()->getVariables().end();
	for( ; it != endIt ; ++it )
	{
		aTypeSpecifier = compileTypeSpecifier(aContainer, (it)->getType());

		InstanceOfData * anInstanceAttribute = new InstanceOfData(
				IPointerDataNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE,
				NULL, (it), aTypeSpecifier,
				theChoiceType->getSymbolData().size(), (it)->getModifier() );
		anInstanceAttribute->setNameID( (it)->getNameID() );

		aValue = (it)->getValue();
		if( aValue.valid() )
		{
			switch( aValue.classKind() )
			{
				case FORM_OPERATOR_KIND:

				case FORM_BUILTIN_BOOLEAN_KIND:
				case FORM_BUILTIN_CHARACTER_KIND:
				case FORM_BUILTIN_INTEGER_KIND:
				case FORM_BUILTIN_RATIONAL_KIND:
				case FORM_BUILTIN_FLOAT_KIND:
				case FORM_BUILTIN_STRING_KIND:
				case FORM_BUILTIN_IDENTIFIER_KIND:
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				//@deprecated
				//case FORM_EXPRESSION_GINAC_KIND:
				{
					anInstanceAttribute->setValue( aValue );

					break;
				}

				default:
				{
					if( (aValue == ExecutableLib::MACHINE_NULL)
						|| (aValue == ExecutableLib::CHANNEL_NIL)
						|| (aValue == ExecutableLib::PORT_NIL   )
						|| (aValue == ExecutableLib::BUFFER_NIL ) )
					{
						anInstanceAttribute->setValue( aValue );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Unexpected STRUCTURE ATTRIBUTE value "
									"for compileChoiceSpecifier :>\n"
								<< aValue.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

//						anInstanceAttribute->setValue( mAvmcodeCompiler.
//								decode_compileExpression(aContainer, aValue) );
					}

					break;
				}
			}

		}

		theChoiceType->saveSymbolData(anInstanceAttribute);
	}

	theChoiceType->updateSize();

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileUnionSpecifier(
		AvmProgram * aContainer, DataType * anUnionT)
{
	UnionTypeSpecifier * theUnionType;
	TypeSpecifier bfTS( theUnionType = TypeManager::newUnion(anUnionT) );

	BF aValue;
	TypeSpecifier aTypeSpecifier;

	TableOfVariable::const_raw_iterator it =
			anUnionT->getPropertyPart()->getVariables().begin();
	TableOfVariable::const_raw_iterator endIt =
			anUnionT->getPropertyPart()->getVariables().end();
	for( ; it != endIt ; ++it )
	{
		aTypeSpecifier = compileTypeSpecifier(aContainer, (it)->getType());

		InstanceOfData * anInstanceAttribute = new InstanceOfData(
				IPointerDataNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE,
				NULL, (it), aTypeSpecifier, 0, (it)->getModifier());
		anInstanceAttribute->setNameID( (it)->getNameID() );

		aValue = (it)->getValue();
		if( aValue.valid() )
		{
			switch( aValue.classKind() )
			{
				case FORM_OPERATOR_KIND:

				case FORM_BUILTIN_BOOLEAN_KIND:
				case FORM_BUILTIN_CHARACTER_KIND:
				case FORM_BUILTIN_INTEGER_KIND:
				case FORM_BUILTIN_RATIONAL_KIND:
				case FORM_BUILTIN_FLOAT_KIND:
				case FORM_BUILTIN_STRING_KIND:
				case FORM_BUILTIN_IDENTIFIER_KIND:
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				//@deprecated
				//case FORM_EXPRESSION_GINAC_KIND:
				{
					anInstanceAttribute->setValue( aValue );

					break;
				}

				default:
				{
					if( (aValue == ExecutableLib::MACHINE_NULL)
						|| (aValue == ExecutableLib::CHANNEL_NIL)
						|| (aValue == ExecutableLib::PORT_NIL   )
						|| (aValue == ExecutableLib::BUFFER_NIL ) )
					{
						anInstanceAttribute->setValue( aValue );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Unexpected UNION ATTRIBUTE value "
									"for compileUnionSpecifier :>\n"
								<< aValue.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

//						anInstanceAttribute->setValue( mAvmcodeCompiler.
//								decode_compileExpression(aContainer, aValue) );
					}

					break;
				}
			}

		}

		theUnionType->saveSymbolData(anInstanceAttribute);
	}

	theUnionType->updateSize();

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileContainerSpecifier(
		AvmProgram * aContainer, DataType * aCollectionT)
{
	TypeSpecifier theContainerType = compileTypeSpecifier(
			aContainer, aCollectionT->getContentsTypeSpecifier());

	if( theContainerType.invalid() )
	{
		theContainerType = TypeManager::UNIVERSAL;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileCollectionSpecifier : << "
				<< aCollectionT->strT() << " >> !!!"
				<< SEND_ALERT;
	}


	int theSize = aCollectionT->size();

	if( (aCollectionT->getContainerSpecifierKind() == TYPE_ARRAY_SPECIFIER)
		&& (theSize < 1) )
	{
		theSize = 1;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileCollectionSpecifier : << "
				<< aCollectionT->strT() << " >> !!!"
				<< SEND_ALERT;
	}

	TypeSpecifier bfTS( TypeManager::newCollection(aCollectionT,
			aCollectionT->getContainerSpecifierKind(), theContainerType,
			(theSize < 0)? AVM_NUMERIC_MAX_INTEGER : theSize ) );

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileIntervalSpecifier(
		AvmProgram * aContainer, DataType * anIntervalT)
{
	TypeSpecifier theBaseType = compileTypeSpecifier(
			aContainer, anIntervalT->getIntervalTypeSpecifier());

	if( theBaseType.invalid() )
	{
		theBaseType = TypeManager::INTEGER;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileIntervalSpecifier : << "
				<< anIntervalT->strT() << " >> !!!"
				<< SEND_ALERT;
	}

	BF aMin = mAvmcodeCompiler.decode_compileExpression(
			aContainer, anIntervalT->getIntervalInfimum());

	BF aMax = mAvmcodeCompiler.decode_compileExpression(
			aContainer, anIntervalT->getIntervalSupremum());

	TypeSpecifier bfTS( TypeManager::newInterval(anIntervalT,
			theBaseType, anIntervalT->getIntervalKind(), aMin, aMax) );

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileEnumerationSpecifier(
		AvmProgram * aContainer, DataType * anEnumT)
{
	EnumTypeSpecifier * theEnumType;
	TypeSpecifier bfTS( theEnumType = TypeManager::newEnum(anEnumT));

	BF aValue;

	TableOfVariable::const_raw_iterator it =
			anEnumT->getPropertyPart()->getVariables().begin();
	TableOfVariable::const_raw_iterator endIt =
			anEnumT->getPropertyPart()->getVariables().end();
	for( ; it != endIt ; ++it )
	{
		InstanceOfData * anInstanceSymbol = new InstanceOfData(
				IPointerDataNature::POINTER_ENUM_SYMBOL_NATURE,
				aContainer, (it), bfTS, (it)->getFullyQualifiedNameID(),
				theEnumType->getSymbolData().size(),
				Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);
		anInstanceSymbol->updateFullyQualifiedNameID();

		aValue = (it)->getValue();
		if( aValue.valid() )
		{
			if( aValue.isBuiltinValue() )
			{
				anInstanceSymbol->setValue( aValue );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENUM value for "
							"compileEnumerationSpecifier :>\n"
						<< aValue.toString( AVM_TAB1_INDENT )
						<< SEND_EXIT;

//				anInstanceSymbol->setValue( mAvmcodeCompiler.
//						decode_compileExpression(aContainer, aValue) );
			}
		}
		else
		{
			anInstanceSymbol->setValue( theEnumType->newfreshSymbolValue() );
		}

		theEnumType->saveSymbolData(anInstanceSymbol);
	}

	theEnumType->updateSize();
	theEnumType->updateBound();

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileTypeAliasSpecifier(
		AvmProgram * aContainer, DataType * aDataType)
{
	TypeSpecifier theTypeSpecifier = compileTypeSpecifier(
			aContainer, aDataType->getTypeSpecifier());

	if( theTypeSpecifier.invalid() )
	{
		theTypeSpecifier = TypeManager::UNIVERSAL;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileTypeAliasSpecifier : << "
				<< aDataType->toString() << " >> !!!"
				<< SEND_ALERT;
	}

	TypeSpecifier bfTS(
			TypeManager::newTypeAlias(aDataType, theTypeSpecifier) );

	if( aDataType->hasConstraintRoutine() &&
		aDataType->getConstraintRoutine()->doSomething() )
	{
		bfTS.saveConstraint(
				mAvmcodeCompiler.compileRoutine(
						this, aContainer, theTypeSpecifier,
						aDataType->getConstraintRoutine() ) );
	}

	return( bfTS );
}


}
