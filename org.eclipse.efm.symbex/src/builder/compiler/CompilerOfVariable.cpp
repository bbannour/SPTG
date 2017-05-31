/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompilerOfVariable.h"

#include <builder/primitive/AvmcodeCompiler.h>
#include <builder/compiler/Compiler.h>

#include <fml/executable/AvmLambda.h>
#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>

#include <fml/common/SpecifierElement.h>

#include <fml/numeric/Integer.h>
#include <fml/numeric/Number.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/operator/OperatorManager.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Variable.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
CompilerOfVariable::CompilerOfVariable(Compiler & aCompiler)
: BaseCompiler(aCompiler)
{
	//!! NOTHING
}


/**
 *******************************************************************************
 * PRE-COMPILATION
 *******************************************************************************
 */

void CompilerOfVariable::addPrecompileData(
		AvmProgram * aContainer, Symbol & aVariable,
		TableOfInstanceOfData & tableOfVariable, bool collectVarEnabled)
{
	getSymbolTable().addDataInstance(aVariable);

	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aVariable.hasTypeSpecifier() )
			<< "addPrecompileData:> Unexpected a "
				"variable without type-specifier !!!"
			<< SEND_EXIT;

	BaseTypeSpecifier * aTypeSpecifier = aVariable.getTypeSpecifier();

	if( aTypeSpecifier->is< TypeAliasSpecifier >() )
	{
		aTypeSpecifier = aTypeSpecifier->
				to< TypeAliasSpecifier >()->targetTypeSpecifier();
	}

	ArrayBF * arrayValue = ( aVariable.hasArrayValue() ) ?
			aVariable.getArrayValue() : NULL;

//	if( arrayValue->getTypeSpecifier() != aTypeSpecifier )
//	{
//		aTypeSpecifier = NULL;
//	}

	switch( aTypeSpecifier->getTypeSpecifierKind() )
	{
		case TYPE_BOOLEAN_SPECIFIER:
		case TYPE_CHARACTER_SPECIFIER:
		case TYPE_REAL_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_INTEGER_SPECIFIER:

		case TYPE_INTERVAL_SPECIFIER:

		case TYPE_ENUM_SPECIFIER:

		case TYPE_STRING_SPECIFIER:

		case TYPE_MACHINE_SPECIFIER:
		{
			if( collectVarEnabled )
			{
				tableOfVariable.append(aVariable);
			}

			break;
		}

		case TYPE_CLASS_SPECIFIER:
		{
			ClassTypeSpecifier * classType =
					aTypeSpecifier->to< ClassTypeSpecifier >();

			aVariable.setAttribute( new TableOfSymbol(classType->size()) );

			InstanceOfData * newInstance;
			Symbol newSymbol;

			TableOfSymbol::iterator it = classType->getSymbolData().begin();
			TableOfSymbol::iterator endIt = classType->getSymbolData().end();
			for( avm_offset_t offset = 0 ; it != endIt ; ++it, ++offset )
			{
				newSymbol = newInstance = new InstanceOfData(
						IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE,
						aVariable.getContainer(), (*it).getAstElement(),
						(*it).getTypeSpecifier(), aVariable.getFullyQualifiedNameID() + "." +
						(*it).getAstNameID(), offset, aVariable.rawData() );

				newInstance->getwModifier().setNatureKind(
						(*it).getAstElement()->getModifier().getNatureKind() );

				newInstance->getwModifier().setFeatureVolatile(
						(*it).getAstElement()->getModifier().hasFeatureVolatile() );
				newInstance->getwModifier().setFeatureTransient(
						(*it).getAstElement()->getModifier().hasFeatureTransient() );

				aVariable.setAttribute(offset, newSymbol);

				if( (arrayValue != NULL) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}
				else
				{
					newInstance->setValue( (*it).getValue() );
				}

				newInstance->setParent( aVariable.rawData() );
				newInstance->updateNameID();

				precompileData_initialValue(aContainer, newInstance);

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer->getModifier().hasFeatureUnsafe() )
				{
					compileTypeConstraint(aContainer, newInstance);
				}

				// ADD DATA
				addPrecompileData(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}

		case TYPE_CHOICE_SPECIFIER:
		{
			ClassTypeSpecifier * classType =
					aTypeSpecifier->to< ClassTypeSpecifier >();

			aVariable.setAttribute( new TableOfSymbol(classType->size()) );

			InstanceOfData * newInstance;
			Symbol newSymbol;

			TableOfSymbol::iterator it = classType->getSymbolData().begin();
			TableOfSymbol::iterator endIt = classType->getSymbolData().end();
			for( avm_offset_t offset = 0 ; it != endIt ; ++it, ++offset )
			{
				newSymbol = newInstance = new InstanceOfData(
						IPointerDataNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE,
						aVariable.getContainer(), (*it).getAstElement(),
						(*it).getTypeSpecifier(), aVariable.getFullyQualifiedNameID() + "." +
						(*it).getAstNameID(), offset, aVariable.rawData() );

				newInstance->getwModifier().setNatureKind(
						(*it).getAstElement()->getModifier().getNatureKind() );

				newInstance->getwModifier().setFeatureVolatile(
						(*it).getAstElement()->getModifier().hasFeatureVolatile() );
				newInstance->getwModifier().setFeatureTransient(
						(*it).getAstElement()->getModifier().hasFeatureTransient() );

				aVariable.setAttribute(offset, newSymbol);

				if( (arrayValue != NULL) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}
				else
				{
					newInstance->setValue( (*it).getValue() );
				}

				newInstance->setParent( aVariable.rawData() );
				newInstance->updateNameID();

				precompileData_initialValue(aContainer, newInstance);

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer->getModifier().hasFeatureUnsafe() )
				{
					compileTypeConstraint(aContainer, newInstance);
				}

				// ADD DATA
				addPrecompileData(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}

		case TYPE_UNION_SPECIFIER:
		{
			UnionTypeSpecifier * unionType =
					aTypeSpecifier->to< UnionTypeSpecifier >();
			aVariable.setAttribute( new TableOfSymbol(unionType->size()) );

			InstanceOfData * newInstance;
			Symbol newSymbol;

			TableOfSymbol::iterator it = unionType->getSymbolData().begin();
			TableOfSymbol::iterator endIt = unionType->getSymbolData().end();
			for( avm_offset_t offset = 0 ; it != endIt ; ++it, ++offset )
			{
				if( (*it).hasTypeArrayOrStructure() )
				{
					incrErrorCount();
					AVM_OS_WARN << aVariable.getAstElement()
							->errorLocation(aContainer->getAstElement())
							<< "CompilerOfVariable::addPrecompileData : "
							<< "Unsupported \"composite type\" "
								"in a \"union type\" << "
							<< str_header( *it ) << " >>!" << std::endl;
				}

				newSymbol = newInstance = new InstanceOfData(
						IPointerDataNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE,
						aVariable.getContainer(), (*it).getAstElement(),
						(*it).getTypeSpecifier(),
						aVariable.getFullyQualifiedNameID() + "." +
								(*it).getAstNameID(),
						aVariable.getOffset(),
						aVariable.rawData() );

				newInstance->getwModifier().setNatureKind(
						(*it).getAstElement()->getModifier().getNatureKind() );

				newInstance->getwModifier().setFeatureVolatile(
						(*it).getAstElement()->getModifier().hasFeatureVolatile() );
				newInstance->getwModifier().setFeatureTransient(
						(*it).getAstElement()->getModifier().hasFeatureTransient() );

				aVariable.setAttribute(offset, newSymbol);

				if( (arrayValue != NULL) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}
				else
				{
					newInstance->setValue( (*it).getValue() );
				}

				newInstance->setParent( aVariable.rawData() );
				newInstance->updateNameID();

				precompileData_initialValue(aContainer, newInstance);

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer->getModifier().hasFeatureUnsafe() )
				{
					compileTypeConstraint(aContainer, newInstance);
				}

				// ADD DATA
				addPrecompileData(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}


		case TYPE_ARRAY_SPECIFIER:
		{
			ContainerTypeSpecifier * collectionT =
					aTypeSpecifier->to< ContainerTypeSpecifier >();

			aVariable.setAttribute( new TableOfSymbol(collectionT->size()) );

			std::ostringstream ossID;

			InstanceOfData * newInstance;
			Symbol newSymbol;

			avm_offset_t offset = 0;
			for( ; offset < collectionT->size() ; ++offset )
			{
				ossID.str("");
				ossID << "[" << offset << "]";

				newSymbol = newInstance = new InstanceOfData(
						IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE,
						aVariable.getContainer(), aVariable.getAstElement(),
						collectionT->getContentsTypeSpecifier(),
						aVariable.getFullyQualifiedNameID() + ossID.str(),
						offset, aVariable.getModifier() );

				newInstance->setParent( aVariable.rawData() );
				newInstance->updateNameID();

				aVariable.setAttribute(offset, newSymbol);

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer->getModifier().hasFeatureUnsafe() )
				{
					compileTypeConstraint(aContainer, newInstance);
				}

				if( (arrayValue != NULL) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}

				// ADD DATA
				addPrecompileData(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}


		case TYPE_FIFO_SPECIFIER:
		case TYPE_LIFO_SPECIFIER:
		case TYPE_MULTI_FIFO_SPECIFIER:
		case TYPE_MULTI_LIFO_SPECIFIER:
		case TYPE_LIST_SPECIFIER:
		case TYPE_SET_SPECIFIER:
		{
			if( collectVarEnabled )
			{
				tableOfVariable.append(aVariable);
			}

			break;
		}

		case TYPE_UNIVERSAL_SPECIFIER:
		{
			if( collectVarEnabled )
			{
				tableOfVariable.append(aVariable);
			}

			break;
		}

		case TYPE_NULL_SPECIFIER:
		{
			// TODO ERROR
			break;
		}

		default :
		{
			// TODO ERROR
			break;
		}
	}
}


avm_size_t CompilerOfVariable::nextOffset(
		TableOfInstanceOfData & tableOfVariable)
{
	return( tableOfVariable.size() );

//	if( tableOfVariable.nonempty() )
//	{
//		InstanceOfData * lastVar = tableOfVariable.last().to_ptr< InstanceOfData >();
//		avm_offset_t offset = 0;
//
//		if( lastVar->getModifier().hasNatureReference() )
//		{
//			offset = 1;
//		}
//		else
//		{
//			offset = lastVar->getTypeSpecifier()->getDataSize();
//		}
//
//		return( offset + lastVar->getOffset() );
//	}
//	else
//	{
//		return( 0 );
//	}
}


void CompilerOfVariable::precompileData(AvmProgram * aContainer,
		Variable * aVariable, TableOfInstanceOfData & tableOfVariable)
{
	TypeSpecifier aTypeSpecifier;
	InstanceOfData * newInstance;
	Symbol newSymbol;

	aTypeSpecifier = compileTypeSpecifier(aContainer, aVariable->getType());

	newSymbol = newInstance = new InstanceOfData(
			IPointerDataNature::POINTER_STANDARD_NATURE,
			aContainer, aVariable, aTypeSpecifier,
			nextOffset(tableOfVariable), aVariable->getModifier() );
	newInstance->setNameID( aVariable->getNameID() );
//	newInstance->fullyUpdateAllNameID( aNewInstance->getFullyQualifiedNameID() );

	precompileData_initialValue(aContainer, newInstance);

	if( aVariable->getModifier().hasNatureReference() )
	{
		tableOfVariable.append(newSymbol);
	}
	else if( aVariable->getModifier().hasFeatureFinal() )
	{
		aContainer->appendConstData(newSymbol);

		TableOfInstanceOfData tableOfConstant;

		addPrecompileData(aContainer, newSymbol, tableOfConstant, true);

		if( tableOfConstant.populated() )
		{
			TableOfInstanceOfData::const_iterator it = tableOfConstant.begin();
			TableOfInstanceOfData::const_iterator endIt = tableOfConstant.end();
			for( ; it != endIt ; ++it )
			{
				if( (*it).isNTEQ(newInstance) )
				{
					aContainer->appendConstData( *it );
				}
			}
		}
		else if( tableOfConstant.singleton() &&
				tableOfConstant.front().isNTEQ(newInstance) )
		{
			aContainer->appendConstData( tableOfConstant.front() );
		}
	}
	else
	{
		if( newInstance->getModifier().hasFeatureUnsafe()
			|| aContainer->getModifier().hasFeatureUnsafe() )
		{
			compileTypeConstraint(aContainer, newInstance);
		}

		// ADD DATA
		tableOfVariable.append(newSymbol);

		addPrecompileData(aContainer, newSymbol, tableOfVariable);
	}

}


/**
 *******************************************************************************
 * COMPILATION
 *******************************************************************************
 */

void CompilerOfVariable::compileData(ExecutableForm * anExecutable)
{
	TableOfInstanceOfData::const_raw_iterator itData =
			anExecutable->getConstData().begin();
	TableOfInstanceOfData::const_raw_iterator endData =
			anExecutable->getConstData().end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->hasAstVariable() )
		{
			compileConstData(anExecutable, (itData));
		}
	}


	BFCode onInitialize( OperatorManager::OPERATOR_SEQUENCE );

	itData = anExecutable->getAllData().begin();
	endData = anExecutable->getAllData().end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->hasAstVariable() )
		{
			compileDataOnCreate(anExecutable, itData, onInitialize);

			compileData(anExecutable, (itData));
		}
	}

	if( onInitialize->nonempty() )
	{
//!![TRACE]: to delete
//AVM_OS_DEBUG << std::endl << "compileData() => onCreate:> "
//		<< onInitialize << std::endl;

		BehavioralPart * theBehavioralPart = const_cast< Machine * >(
				anExecutable->getAstMachine() )->getUniqBehaviorPart();

		onInitialize = StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onInitialize, theBehavioralPart->getOnCreate() );

		theBehavioralPart->setOnCreate( onInitialize->populated() ?
				onInitialize : onInitialize->first().bfCode() );
	}
}


void CompilerOfVariable::compileDataOnCreate(
		ExecutableForm * anExecutable,
		TableOfInstanceOfData::const_raw_iterator itData,
		BFCode & onInitialize)
{
	const Variable * aVariable = (itData)->getAstVariable();

	const BF & aValue = ( (itData)->hasAliasTarget() &&
			(itData)->getAliasTarget()->as< InstanceOfData >()->hasValue() )?
				(itData)->getAliasTarget()->as< InstanceOfData >()->getValue() :
					( (itData)->hasValue() ?
							(itData)->getValue() : aVariable->getValue() );
//!![TRACE]: to delete
//!![MIGRATION]:TRACE
//	AVM_OS_DEBUG << std::endl
//			<< "compileData() => onCreate:>\n"
//			<< to_stream( *itData ) << to_stream( aVariable ) << std::endl;

	if( aValue.valid() )
	{
		/*if( (itData)->hasTypeArrayOrStructure()
			&& (not aValue.is< BuiltinCollection >()) )
		{
			AVM_OS_DEBUG << std::endl
					<< "compileData() => onCreate:> unexpected\n"
					<< "type:> " << aValue.classKindInfo() << std::endl
					<< to_stream( *itData ) << std::endl;
		}
		else*/ if( not ( (itData)->hasParent()
				&& (itData)->getParent()->hasValue() ) )
//				&& (itData)->getParent()->hasTypeArrayOrStructure()
//				&& (itData)->getParent()->getValue().is< BuiltinCollection >() ) )
		{
//AVM_OS_DEBUG << std::endl << "compileData() => onCreate:>\n"
//		<< to_stream( *itData ) << std::endl;
////	<< str_header( *itData ) << std::endl;

			onInitialize->append( StatementConstructor::newCode(
					aVariable->getAssignOperator(), (*itData), aValue ) );
		}
	}
}

void CompilerOfVariable::compileData(AvmProgram * aProgram)
{
	TableOfInstanceOfData::const_raw_iterator itData =
			aProgram->getConstData().begin();
	TableOfInstanceOfData::const_raw_iterator endData =
			aProgram->getConstData().end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->hasAstVariable() )
		{
			compileConstData(aProgram, (itData));
		}
	}


	itData = aProgram->getAllData().begin();
	endData = aProgram->getAllData().end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->hasAstVariable() )
		{
			compileData(aProgram, (itData));
		}
	}
}


void CompilerOfVariable::compileConstData(
		AvmProgram * aContainer, InstanceOfData * aVarInstance)
{
	if( aVarInstance->hasAstVariable() )
	{
		const Variable * aCompiledVar = aVarInstance->getAstVariable();
		if( aCompiledVar->hasOnWrite() )
		{
			//!!! ERROR
		}

		compileData_initialValue(aContainer, aVarInstance);
	}
}


void CompilerOfVariable::compileData(
		AvmProgram * aContainer, InstanceOfData * aVarInstance)
{
	const Variable * aCompiledVar = aVarInstance->getAstVariable();

	if( aCompiledVar->hasOnWrite() &&
		aCompiledVar->getOnWriteRoutine()->doSomething() )
	{
		AvmProgram * onWriteProg = mAvmcodeCompiler.compileRoutine(this,
				aContainer, aVarInstance, aCompiledVar->getOnWriteRoutine());

		if( aVarInstance->isConcreteStructAttribute() )
		{
			onWriteProg->setFullyQualifiedNameContainer( aVarInstance );
		}

		aVarInstance->setOnWriteRoutine( onWriteProg );

		aContainer->getExecutable()->saveAnonymousInnerRoutine( onWriteProg );
	}

	else if( aVarInstance->hasTypeSpecifier() &&
			aVarInstance->getTypeSpecifier()->hasConstraint() )
	{
		aVarInstance->setOnWriteRoutine( aVarInstance->getTypeSpecifier()->
				getConstraint().as_ptr< AvmProgram >() );
	}
//	else if( aCompiledVar->hasDataType() &&
//			aCompiledVar->getDataType()->getConstraintRoutine().doSomething() )
//	{
//		aVarInstance->setOnWriteRoutine( compileData_monitor(
//				aContainer, aVarInstance,
//				aCompiledVar->getDataType()->getConstraintRoutine()) );
//	}

	compileData_initialValue(aContainer, aVarInstance);
}


BF CompilerOfVariable::precompileData_initialValue(AvmProgram * aContainer,
		BaseTypeSpecifier * aTypeSpecifier, const BF & aValue)
{
	if( aValue.invalid() )
	{
		return( BF::REF_NULL );
	}

	else if( aValue.is< InstanceOfData >() )
	{
		if( aValue.to_ptr< InstanceOfData >()->hasValue() &&
			ExpressionTypeChecker::isFinalSymbolicBasicSymbol(
					aValue.to_ptr< InstanceOfData >()->getValue()) )
		{
			return( aValue.to_ptr< InstanceOfData >()->getValue() );
		}
		else if( aValue.to_ptr< InstanceOfData >()->getModifier().
					hasModifierPublicFinalStaticParameter() )
		{
			return( aValue );
		}
	}

	else if( aValue.is_strictly< BuiltinArray >() )
	{
		BuiltinArray * aBuiltinArrayValue = aValue.to_ptr< BuiltinArray >();

		if( aBuiltinArrayValue->is< ArrayIdentifier >()
			|| aBuiltinArrayValue->is< ArrayQualifiedIdentifier >() )
		{
			return( BF::REF_NULL );
		}
		else if( aTypeSpecifier->hasTypeListCollection() )
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					aTypeSpecifier->as< ContainerTypeSpecifier >() );

			containerValue->copy(aBuiltinArrayValue, std::min(
					containerValue->capacity(), aBuiltinArrayValue->size()) );

			return( BF(containerValue) );
		}

		else
		{
			ArrayBF * bfArray = aBuiltinArrayValue->getArrayBF();

			if( (bfArray->getTypeSpecifier() != aTypeSpecifier)
				&& ExpressionTypeChecker::isTyped(aTypeSpecifier, aValue) )
			{
				bfArray->setTypeSpecifier( aTypeSpecifier );
			}

			if( bfArray->getTypeSpecifier()->is< ContainerTypeSpecifier >()
				&& bfArray->getTypeSpecifier()->to<
						ContainerTypeSpecifier >()->weaklyTypedIdentifier() )
			{
				delete bfArray;
			}
			else
			{
				return( BF( bfArray ) );
			}
		}
	}

	else if( aValue.is< ArrayBF >()
			/*&& aVarInstance->getModifier().hasFeatureFinal
			&& ExpressionTypeChecker::isFinalSymbolicCompositeSymbol(
					aValue.to_ptr< ArrayBF >())*/ )
	{
		bool isFinalSymbol = true;

		CompilationEnvironment compilENV(aContainer);

		ArrayBF * bfArray = aValue.to_ptr< ArrayBF >();
		for( avm_size_t idx = 0 ; idx < bfArray->size() ; ++idx )
		{
			const BF & arg = bfArray->at(idx);
			if( arg.is< Variable >() )
			{
				if( arg.to_ptr< Variable >()->hasValue()
					&& ExpressionTypeChecker::isFinalSymbolicSymbol(
							arg.to_ptr< Variable >()->getValue()) )
				{
					const BF & compiledVar =
							mAvmcodeCompiler.getSymbolTable().searchSemSymbol(
									compilENV.mCTX, arg.to_ptr< Variable >() );

					if( compiledVar.valid()
						&& compiledVar.is< InstanceOfData >()
						&& compiledVar.to_ptr< InstanceOfData >()->hasValue() )
					{
						bfArray->set(idx,
							compiledVar.to_ptr< InstanceOfData >()->getValue() );
					}
					else if( aTypeSpecifier->hasTypeContainer() )
					{
						bfArray->set(idx, precompileData_initialValue(aContainer,
								aTypeSpecifier->as< ContainerTypeSpecifier >()
										->getContentsTypeSpecifier(),
								arg.to_ptr< Variable >()->getValue()) );
					}
					else if( aTypeSpecifier->isTypedClass() )
					{
						bfArray->set(idx, precompileData_initialValue(aContainer,
								aTypeSpecifier->as< ClassTypeSpecifier >()
										->getSymbolData(idx).getTypeSpecifier(),
								arg.to_ptr< Variable >()->getValue()) );
					}
					else
					{
						bfArray->set(idx, arg.to_ptr< Variable >()->getValue() );
					}
				}
				else
				{
					isFinalSymbol = false;
				}
			}
			else if( not ExpressionTypeChecker::isFinalSymbolicSymbol( arg ) )
			{
				isFinalSymbol = false;
			}
		}

		if( isFinalSymbol )
		{
			if( (aValue.to_ptr< ArrayBF >()->getTypeSpecifier() != aTypeSpecifier)
				&& ExpressionTypeChecker::isTyped(aTypeSpecifier, aValue) )
			{
				aValue.to_ptr< ArrayBF >()->setTypeSpecifier( aTypeSpecifier );
			}

			return( aValue );
		}
	}

	else if( aTypeSpecifier->isTypedArray() )
	{
		if( ExpressionTypeChecker::isFinalSymbolicBasicSymbol(aValue) )
		{
			return( BF( new ArrayBF(aTypeSpecifier,
					aTypeSpecifier->size(), aValue) ) );
		}
	}

	else if( aTypeSpecifier->isTypedEnum() )
	{
		if( aValue.is< Variable >() )
		{
			return( aTypeSpecifier->as< EnumTypeSpecifier >()->getSymbolData().
					getByAstElement( aValue.to_ptr< Variable >() ) );
		}
		else if( aValue.is< Identifier >() )
		{
			return( aTypeSpecifier->as< EnumTypeSpecifier >()->getSymbolData().
					getByNameID( aValue.to_ptr< Identifier >()->getValue() ) );
		}
		else
		{
			return( aTypeSpecifier->as< EnumTypeSpecifier >()->
					getSymbolData().getByQualifiedNameID( aValue.str() ) );
		}
	}

	else if( aValue.is< Number >()   || aValue.is< Boolean >() ||
			aValue.is< Character >() || aValue.is< String >() )
	{
		return( aValue );
	}

	return( BF::REF_NULL );
}

void CompilerOfVariable::precompileData_initialValue(
		AvmProgram * aContainer, InstanceOfData * aVarInstance)
{
	const Variable * aVar = aVarInstance->getAstVariable();

	BF aValue = aVar->getValue();
	if( aValue.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "variable:precompile#value> " << str_header( aVar ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		aVarInstance->setValue( precompileData_initialValue(aContainer,
				aVarInstance->getTypeSpecifier(), aValue) );

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "instance:> " << str_header( aVarInstance ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	}
}



void CompilerOfVariable::compileData_initialValue(
		AvmProgram * aContainer, InstanceOfData * aVarInstance)
{
	const Variable * aVar = aVarInstance->getAstVariable();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "variable:compile#value> " << str_header( aVar ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	if( not aVarInstance->hasValue() )
	{
		const BF & aValue = aVar->getValue();
		if( aValue.valid() )
		{
			CompilationEnvironment compilENV(aContainer);
			compilENV.mCTX->mType = aVarInstance->getTypeSpecifier();

			aVarInstance->setValue(	mAvmcodeCompiler.
					decode_compileExpression(compilENV.mCTX, aValue) );

			if( aVarInstance->getValue().is< ArrayBF >() )
			{
				ArrayBF * bfArray = aVarInstance->getValue().to_ptr< ArrayBF >();
				for( avm_size_t idx = 0 ; idx < bfArray->size() ; ++idx )
				{
					const BF & arg = bfArray->at(idx);
					if( arg.is< InstanceOfData >() &&
							arg.to_ptr< InstanceOfData >()->hasValue() &&
							ExpressionTypeChecker::isFinalSymbolicSymbol(
								arg.to_ptr< InstanceOfData >()->getValue()) )
					{
						bfArray->set(idx,
							arg.to_ptr< InstanceOfData >()->getValue() );
					}
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "instance:> " << str_header( aVarInstance ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
}


// TODO Verifier la généralisation, hors des types énumérés!!!
void CompilerOfVariable::compileTypeConstraint(
		AvmProgram * aContainer, InstanceOfData * aVarInstance)
{
	AVM_OS_ASSERT_WARNING_ALERT( aVarInstance->getModifier().hasFeatureUnsafe()
			|| aContainer->getModifier().hasFeatureUnsafe() )
			<< "Unexpected a << non-unsafe >> InstanceOfData !!!"
			<< SEND_ALERT;

	BaseTypeSpecifier * aTypeSpecifier = aVarInstance->getTypeSpecifier();
	if( aTypeSpecifier->couldGenerateConstraint() )
	{
		AvmProgram * onWriteProg = new AvmProgram(
				Specifier::SCOPE_ROUTINE_KIND,
				aContainer, aVarInstance->getAstElement(), 1);
		onWriteProg->updateUfid( "#onWriteTypeConstraint" );
		onWriteProg->setParamOffsetCount(0, 1);

		BF newValue( new InstanceOfData(
				IPointerDataNature::POINTER_STANDARD_NATURE, onWriteProg,
				aVarInstance->getAstElement(), aTypeSpecifier, "newValue",  0) );
		onWriteProg->setData(0, newValue);
		onWriteProg->updateDataTable();

		BFCode code(OperatorManager::OPERATOR_GUARD,
				aTypeSpecifier->genConstraint(newValue) );

		onWriteProg->setCode(code);

		aVarInstance->setOnWriteRoutine( onWriteProg );

		aContainer->getExecutable()->saveAnonymousInnerRoutine( onWriteProg );
	}
}


}
