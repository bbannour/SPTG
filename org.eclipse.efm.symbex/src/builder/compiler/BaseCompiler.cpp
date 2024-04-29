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
		AvmProgram & aContainer, const BF & bfType) const
{
	TypeSpecifier aTypeSpecifier;

	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( bfType )
			<< "typedef for compiling !!!"
			<< SEND_EXIT;

	if( bfType.is< DataType >() )
	{
		const DataType & aDataType = bfType.to< DataType >();

		if( aDataType.hasTypeContainer() )
		{
			aTypeSpecifier = compileContainerSpecifier(aContainer, aDataType);
		}
		else if( aDataType.isTypedInterval() )
		{
			aTypeSpecifier = compileIntervalSpecifier(aContainer, aDataType);
		}
		else if( aDataType.isTypedEnum() )
		{
			aTypeSpecifier = compileEnumerationSpecifier(aContainer, aDataType);
		}
		else if( aDataType.isTypedStructure() )
		{
			aTypeSpecifier = compileStructureSpecifier(aContainer, aDataType);
		}

		else if( aDataType.isTypedChoice() )
		{
			aTypeSpecifier = compileChoiceSpecifier(aContainer, aDataType);
		}

		else if( aDataType.isTypedUnion() )
		{
			aTypeSpecifier = compileUnionSpecifier(aContainer, aDataType);
		}

		else if( aDataType.isDataTypeAlias() )
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
		aContainer.appendTypeSpecifier( aTypeSpecifier );
	}
}



/**
 * Compiling type specifier
 */
TypeSpecifier BaseCompiler::compileTypeSpecifier(
		AvmProgram & aContainer, const std::string & aTypeID) const
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
			aContainer.safeAstElement().errorLocation(AVM_OS_WARN)
					<< "Error while compiling type specifier << "
					<< aTypeID << " >>" << std::endl << std::endl;

			return( TypeManager::UNIVERSAL );
		}
	}
}


TypeSpecifier BaseCompiler::compileTypeSpecifier(
		AvmProgram & aContainer, const BF & bfType) const
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
			AVM_OS_WARN << bfType.to< UniFormIdentifier >()
					.errorLocation(aContainer.safeAstElement())
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
				compilENV.mCTX, bfType.to< ObjectElement >() );

		if( bfTS.valid() )
		{
			return( bfTS );
		}

		else  if( bfType.is< DataType >() )
		{
			const DataType & aDataType = bfType.to< DataType >();

			if( aDataType.hasTypeContainer() )
			{
				bfTS = compileContainerSpecifier(aContainer, aDataType);
			}
			else if( aDataType.isTypedInterval() )
			{
				bfTS = compileIntervalSpecifier(aContainer, aDataType);
			}
			else if( aDataType.isTypedEnum() )
			{
				bfTS = compileEnumerationSpecifier(aContainer, aDataType);
			}
			else if( aDataType.isTypedStructure() )
			{
				bfTS = compileStructureSpecifier(aContainer, aDataType);
			}

			else if( aDataType.isTypedChoice() )
			{
				bfTS = compileChoiceSpecifier(aContainer, aDataType);
			}

			else if( aDataType.isTypedUnion() )
			{
				bfTS = compileUnionSpecifier(aContainer, aDataType);
			}

			else// if( aDataType.isDataTypeAlias() )
			{
				bfTS = compileTypeAliasSpecifier(aContainer, aDataType);
			}
		}

		if( bfTS.valid() )
		{
			if( bfTS.hasTypeEnumOrComposite() &&
					SymbolTable::searchTypeSpecifier(
							getConfiguration().getExecutableSystem(),
							compilENV.mCTX, bfTS.safeAstElement()).invalid() )
			{
				aContainer.appendTypeSpecifier( bfTS );
			}

			return( bfTS );
		}
		else
		{
			aContainer.safeAstElement().errorLocation(AVM_OS_WARN)
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
		AvmProgram & aContainer, const DataType & aStructureT) const
{
	ClassTypeSpecifier * theClassType;
	TypeSpecifier bfTS( theClassType = TypeManager::newClass(aStructureT) );

	BF aValue;
	TypeSpecifier aTypeSpecifier;

	TableOfVariable::const_ref_iterator itVariable =
			aStructureT.getPropertyPart()->getVariables().begin();
	TableOfVariable::const_ref_iterator endVariable =
			aStructureT.getPropertyPart()->getVariables().end();
	for( ; itVariable != endVariable ; ++itVariable )
	{
		aTypeSpecifier = compileTypeSpecifier(aContainer, (itVariable)->getType());

		InstanceOfData * anInstanceAttribute = new InstanceOfData(
				IPointerVariableNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE,
				nullptr, (itVariable), aTypeSpecifier,
				theClassType->getSymbolData().size(), (itVariable)->getModifier() );
		anInstanceAttribute->setNameID( (itVariable)->getNameID() );

		aValue = (itVariable)->getValue();
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
		AvmProgram & aContainer, const DataType & aChoiceT) const
{
	ChoiceTypeSpecifier * theChoiceType;
	TypeSpecifier bfTS( theChoiceType = TypeManager::newChoice(aChoiceT) );

	BF aValue;
	TypeSpecifier aTypeSpecifier;

	TableOfVariable::const_ref_iterator itVariable =
			aChoiceT.getPropertyPart()->getVariables().begin();
	TableOfVariable::const_ref_iterator endVariable =
			aChoiceT.getPropertyPart()->getVariables().end();
	for( ; itVariable != endVariable ; ++itVariable )
	{
		aTypeSpecifier = compileTypeSpecifier(aContainer, (itVariable)->getType());

		InstanceOfData * anInstanceAttribute = new InstanceOfData(
				IPointerVariableNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE,
				nullptr, (itVariable), aTypeSpecifier,
				theChoiceType->getSymbolData().size(), (itVariable)->getModifier() );
		anInstanceAttribute->setNameID( (itVariable)->getNameID() );

		aValue = (itVariable)->getValue();
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
		AvmProgram & aContainer, const DataType & anUnionT) const
{
	UnionTypeSpecifier * theUnionType;
	TypeSpecifier bfTS( theUnionType = TypeManager::newUnion(anUnionT) );

	BF aValue;
	TypeSpecifier aTypeSpecifier;

	TableOfVariable::const_ref_iterator itVariable =
			anUnionT.getPropertyPart()->getVariables().begin();
	TableOfVariable::const_ref_iterator endVariable =
			anUnionT.getPropertyPart()->getVariables().end();
	for( ; itVariable != endVariable ; ++itVariable )
	{
		aTypeSpecifier = compileTypeSpecifier(aContainer, (itVariable)->getType());

		InstanceOfData * anInstanceAttribute = new InstanceOfData(
				IPointerVariableNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE,
				nullptr, (itVariable), aTypeSpecifier, 0, (itVariable)->getModifier());
		anInstanceAttribute->setNameID( (itVariable)->getNameID() );

		aValue = (itVariable)->getValue();
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
		AvmProgram & aContainer, const DataType & aCollectionT) const
{
	TypeSpecifier theContainerType = compileTypeSpecifier(
			aContainer, aCollectionT.getContentsTypeSpecifier());

	if( theContainerType.invalid() )
	{
		theContainerType = TypeManager::UNIVERSAL;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileCollectionSpecifier : << "
				<< aCollectionT.strT() << " >> !!!"
				<< SEND_ALERT;
	}


	long theSize = aCollectionT.getMaximumSize();

	if( (aCollectionT.getContainerSpecifierKind() == TYPE_ARRAY_SPECIFIER)
		&& (theSize < 1) )
	{
		theSize = 1;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileCollectionSpecifier : << "
				<< aCollectionT.strT() << " >> !!!"
				<< SEND_ALERT;
	}

	TypeSpecifier bfTS( TypeManager::newCollection(aCollectionT,
			aCollectionT.getContainerSpecifierKind(), theContainerType,
			(theSize < 0)? AVM_NUMERIC_MAX_SIZE_T : theSize ) );

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileIntervalSpecifier(
		AvmProgram & aContainer, const DataType & anIntervalT) const
{
	TypeSpecifier theBaseType = compileTypeSpecifier(
			aContainer, anIntervalT.getIntervalTypeSpecifier());

	if( theBaseType.invalid() )
	{
		theBaseType = TypeManager::INTEGER;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileIntervalSpecifier : << "
				<< anIntervalT.strT() << " >> !!!"
				<< SEND_ALERT;
	}

	BF aMin = mAvmcodeCompiler.decode_compileExpression(
			aContainer, anIntervalT.getIntervalInfimum());

	BF aMax = mAvmcodeCompiler.decode_compileExpression(
			aContainer, anIntervalT.getIntervalSupremum());

	TypeSpecifier bfTS( TypeManager::newInterval(anIntervalT,
			theBaseType, anIntervalT.getIntervalKind(), aMin, aMax) );

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileEnumerationSpecifier(
		AvmProgram & aContainer, const DataType & anEnumT) const
{
	EnumTypeSpecifier * theEnumType;
	TypeSpecifier bfTS( theEnumType = TypeManager::newEnum(anEnumT) );

	if( anEnumT.hasSuperTypeSpecifier() )
	{
		const TypeSpecifier & aType = SymbolTable::searchTypeSpecifier(
				getConfiguration().getExecutableSystem(), (& aContainer),
				anEnumT.getTypeSpecifier().to< DataType >());

		theEnumType->setSuperTypeSpecifier( aType );

		const EnumTypeSpecifier & superEnumTS = aType.enumT();

		TableOfVariable::const_ref_iterator itVariable =
				anEnumT.getPropertyPart()->getVariables().begin();
		TableOfVariable::const_ref_iterator endVariable =
				anEnumT.getPropertyPart()->getVariables().end();
		for( ; itVariable != endVariable ; ++itVariable )
		{
			const Symbol & foundEnumSymbol =
					superEnumTS.getDataByAstElement(itVariable);
			if( foundEnumSymbol.valid() )
			{
				theEnumType->appendSymbolData( foundEnumSymbol );
			}
			else
			{

			}
		}
	}
	else
	{
		BF aValue;

		TableOfVariable::const_ref_iterator itVariable =
				anEnumT.getPropertyPart()->getVariables().begin();
		TableOfVariable::const_ref_iterator endVariable =
				anEnumT.getPropertyPart()->getVariables().end();
		for( ; itVariable != endVariable ; ++itVariable )
		{
			InstanceOfData * anInstanceSymbol = new InstanceOfData(
					IPointerVariableNature::POINTER_ENUM_SYMBOL_NATURE,
					(& aContainer), (itVariable), bfTS, (itVariable)->getFullyQualifiedNameID(),
					theEnumType->getSymbolData().size(),
					Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER);
			anInstanceSymbol->updateFullyQualifiedNameID();

			aValue = (itVariable)->getValue();
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
	}

	theEnumType->updateSize();
	theEnumType->updateBound();

	return( bfTS );
}


TypeSpecifier BaseCompiler::compileTypeAliasSpecifier(
		AvmProgram & aContainer, const DataType & aDataType) const
{
	TypeSpecifier theTypeSpecifier = compileTypeSpecifier(
			aContainer, aDataType.getTypeSpecifier());

	if( theTypeSpecifier.invalid() )
	{
		theTypeSpecifier = TypeManager::UNIVERSAL;

//		incrErrorCount();
		++AVM_ERROR_COUNT;

		AVM_OS_ERROR_ALERT << "BaseCompiler::compileTypeAliasSpecifier : << "
				<< aDataType.toString() << " >> !!!"
				<< SEND_ALERT;
	}

	TypeSpecifier bfTS(	TypeManager::newTypeAlias(aDataType, theTypeSpecifier) );

	if( aDataType.hasConstraintRoutine() &&
		aDataType.getConstraintRoutine().doSomething() )
	{
		bfTS.saveConstraint(
				mAvmcodeCompiler.compileRoutine( (*this), aContainer,
						theTypeSpecifier,aDataType.getConstraintRoutine() ) );
	}

	return( bfTS );
}


}
