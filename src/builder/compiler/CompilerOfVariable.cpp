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

#include <computer/PathConditionProcessor.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>

#include <fml/common/SpecifierElement.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Variable.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/numeric/Integer.h>
#include <fml/numeric/Number.h>

#include <fml/operator/OperatorManager.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/type/BaseSymbolTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>


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

void CompilerOfVariable::addPrecompileVariable(
		AvmProgram & aContainer, Symbol & aVariable,
		TableOfInstanceOfData & tableOfVariable, bool collectVarEnabled)
{
	getSymbolTable().addDataInstance(aVariable);

	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aVariable.hasTypeSpecifier() )
			<< "addPrecompileVariable:> Unexpected a "
				"variable without type-specifier !!!"
			<< SEND_EXIT;

	const BaseTypeSpecifier & aTypeSpecifier = aVariable.referedTypeSpecifier();

	ArrayBF * arrayValue = ( aVariable.hasArrayValue() ) ?
			aVariable.getArrayValue() : nullptr;

//	if( arrayValue->getTypeSpecifier() != aTypeSpecifier )
//	{
//		aTypeSpecifier = nullptr;
//	}

	switch( aTypeSpecifier.getTypeSpecifierKind() )
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
			const ClassTypeSpecifier & classType =
					aTypeSpecifier.to< ClassTypeSpecifier >();

			aVariable.setAttribute( new TableOfSymbol(classType.size()) );

			InstanceOfData * newInstance;
			Symbol newSymbol;

			TableOfSymbol::const_iterator it = classType.getSymbolData().begin();
			TableOfSymbol::const_iterator endIt = classType.getSymbolData().end();
			for( avm_offset_t offset = 0 ; it != endIt ; ++it, ++offset )
			{
				newSymbol = newInstance = new InstanceOfData(
						IPointerVariableNature::
								POINTER_FIELD_CLASS_ATTRIBUTE_NATURE,
						aVariable.getContainer(), (*it).safeAstElement(),
						(*it).getTypeSpecifier(),
						aVariable.getFullyQualifiedNameID() + "." +
						(*it).getAstNameID(), offset, aVariable.variable() );

				newInstance->getwModifier().setNatureKind(
						(*it).getAstElement().getModifier().getNatureKind() );

				newInstance->getwModifier().setFeatureVolatile(
					(*it).getAstElement().getModifier().hasFeatureVolatile() );
				newInstance->getwModifier().setFeatureTransient(
					(*it).getAstElement().getModifier().hasFeatureTransient() );

				aVariable.setAttribute(offset, newSymbol);

				if( (arrayValue != nullptr) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}
				else
				{
					newInstance->setValue( (*it).getValue() );
				}

				newInstance->setParent( aVariable.rawVariable() );
				newInstance->updateNameID();

				precompileVariable_initialValue(aContainer, (* newInstance));

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer.getModifier().hasFeatureUnsafe()
					|| PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
				{
					compileTypeConstraint(aContainer, (* newInstance));
				}

				// ADD DATA
				addPrecompileVariable(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}

		case TYPE_CHOICE_SPECIFIER:
		{
			const ClassTypeSpecifier & classType =
					aTypeSpecifier.to< ClassTypeSpecifier >();

			aVariable.setAttribute( new TableOfSymbol(classType.size()) );

			InstanceOfData * newInstance;
			Symbol newSymbol;

			TableOfSymbol::const_iterator it = classType.getSymbolData().begin();
			TableOfSymbol::const_iterator endIt = classType.getSymbolData().end();
			for( avm_offset_t offset = 0 ; it != endIt ; ++it, ++offset )
			{
				newSymbol = newInstance = new InstanceOfData(
						IPointerVariableNature::
								POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE,
						aVariable.getContainer(), (*it).safeAstElement(),
						(*it).getTypeSpecifier(),
						aVariable.getFullyQualifiedNameID() + "." +
						(*it).getAstNameID(), offset, aVariable.variable() );

				newInstance->getwModifier().setNatureKind(
						(*it).getAstElement().getModifier().getNatureKind() );

				newInstance->getwModifier().setFeatureVolatile(
						(*it).getAstElement().getModifier().hasFeatureVolatile() );
				newInstance->getwModifier().setFeatureTransient(
						(*it).getAstElement().getModifier().hasFeatureTransient() );

				aVariable.setAttribute(offset, newSymbol);

				if( (arrayValue != nullptr) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}
				else
				{
					newInstance->setValue( (*it).getValue() );
				}

				newInstance->setParent( aVariable.rawVariable() );
				newInstance->updateNameID();

				precompileVariable_initialValue(aContainer, (* newInstance));

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer.getModifier().hasFeatureUnsafe()
					|| PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
				{
					compileTypeConstraint(aContainer, (* newInstance));
				}

				// ADD DATA
				addPrecompileVariable(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}

		case TYPE_UNION_SPECIFIER:
		{
			const UnionTypeSpecifier & unionType =
					aTypeSpecifier.to< UnionTypeSpecifier >();
			aVariable.setAttribute( new TableOfSymbol(unionType.size()) );

			InstanceOfData * newInstance;
			Symbol newSymbol;

			TableOfSymbol::const_iterator it = unionType.getSymbolData().begin();
			TableOfSymbol::const_iterator endIt = unionType.getSymbolData().end();
			for( avm_offset_t offset = 0 ; it != endIt ; ++it, ++offset )
			{
				if( (*it).hasTypeArrayOrStructure() )
				{
					incrErrorCount();
					AVM_OS_WARN << aVariable.safeAstElement().
							errorLocation( aContainer.safeAstElement() )
							<< "CompilerOfVariable::addPrecompileVariable : "
							<< "Unsupported \"composite type\" "
								"in a \"union type\" << "
							<< str_header( *it ) << " >>!" << std::endl;
				}

				newSymbol = newInstance = new InstanceOfData(
						IPointerVariableNature::
								POINTER_FIELD_UNION_ATTRIBUTE_NATURE,
						aVariable.getContainer(), (*it).safeAstElement(),
						(*it).getTypeSpecifier(),
						aVariable.getFullyQualifiedNameID() + "." +
								(*it).getAstNameID(),
						aVariable.getOffset(),
						aVariable.variable() );

				newInstance->getwModifier().setNatureKind(
					(*it).getAstElement().getModifier().getNatureKind() );

				newInstance->getwModifier().setFeatureVolatile(
					(*it).getAstElement().getModifier().hasFeatureVolatile() );
				newInstance->getwModifier().setFeatureTransient(
					(*it).getAstElement().getModifier().hasFeatureTransient() );

				aVariable.setAttribute(offset, newSymbol);

				if( (arrayValue != nullptr) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}
				else
				{
					newInstance->setValue( (*it).getValue() );
				}

				newInstance->setParent( aVariable.rawVariable() );
				newInstance->updateNameID();

				precompileVariable_initialValue(aContainer, (* newInstance));

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer.getModifier().hasFeatureUnsafe()
					|| PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
				{
					compileTypeConstraint(aContainer, (* newInstance));
				}

				// ADD DATA
				addPrecompileVariable(aContainer, newSymbol,
						tableOfVariable, collectVarEnabled);
			}

			break;
		}


		case TYPE_ARRAY_SPECIFIER:
		{
			const ContainerTypeSpecifier & collectionT =
					aTypeSpecifier.to< ContainerTypeSpecifier >();

			aVariable.setAttribute( new TableOfSymbol(collectionT.size()) );

			std::ostringstream ossID;

			InstanceOfData * newInstance;
			Symbol newSymbol;

			avm_offset_t offset = 0;
			for( ; offset < collectionT.size() ; ++offset )
			{
				ossID.str("");
				ossID << "[" << offset << "]";

				newSymbol = newInstance = new InstanceOfData(
						IPointerVariableNature::POINTER_FIELD_ARRAY_OFFSET_NATURE,
						aVariable.getContainer(), aVariable.getAstElement(),
						collectionT.getContentsTypeSpecifier(),
						aVariable.getFullyQualifiedNameID() + ossID.str(),
						offset, aVariable.getModifier() );

				newInstance->setParent( aVariable.rawVariable() );
				newInstance->updateNameID();

				aVariable.setAttribute(offset, newSymbol);

				if( newInstance->getModifier().hasFeatureUnsafe()
					|| aContainer.getModifier().hasFeatureUnsafe()
					|| PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
				{
					compileTypeConstraint(aContainer, (* newInstance));
				}

				if( (arrayValue != nullptr) && (arrayValue->size() > offset) )
				{
					newInstance->setValue( arrayValue->at(offset) );
				}

				// ADD DATA
				addPrecompileVariable(aContainer, newSymbol,
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


std::size_t CompilerOfVariable::nextOffset(
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
//			offset = lastVar->getTypeSpecifier().getDataSize();
//		}
//
//		return( offset + lastVar->getOffset() );
//	}
//	else
//	{
//		return( 0 );
//	}
}


void CompilerOfVariable::precompileVariable( AvmProgram & aContainer,
		const Variable & aVariable, TableOfInstanceOfData & tableOfVariable)
{
	InstanceOfData * newInstance;
	Symbol newSymbol;

	TypeSpecifier aTypeSpecifier =
			compileTypeSpecifier(aContainer, aVariable.getType());

	newSymbol = newInstance = new InstanceOfData(
			IPointerVariableNature::POINTER_STANDARD_NATURE,
			(& aContainer), aVariable, aTypeSpecifier,
			nextOffset(tableOfVariable), aVariable.getModifier() );
	newInstance->setNameID( aVariable.getNameID() );
//	newInstance->fullyUpdateAllNameID( aNewInstance->getFullyQualifiedNameID() );

	precompileVariable_initialValue(aContainer, (* newInstance));

	if( aVariable.getModifier().hasNatureReference() )
	{
		tableOfVariable.append(newSymbol);
	}
	else if( aVariable.getModifier().hasFeatureFinal() )
	{
		aContainer.appendConstVariable(newSymbol);

		TableOfInstanceOfData tableOfConstant;

		addPrecompileVariable(aContainer, newSymbol, tableOfConstant, true);

		if( tableOfConstant.populated() )
		{
			for( const auto & itConstant : tableOfConstant )
			{
				if( itConstant.isNTEQ(newInstance) )
				{
					aContainer.appendConstVariable( itConstant );
				}
			}
		}
		else if( tableOfConstant.singleton() &&
				tableOfConstant.front().isNTEQ(newInstance) )
		{
			aContainer.appendConstVariable( tableOfConstant.front() );
		}
	}
	else
	{
		if( newInstance->getModifier().hasFeatureUnsafe()
			|| aContainer.getModifier().hasFeatureUnsafe()
			|| PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
		{
			compileTypeConstraint(aContainer, (* newInstance));
		}

		// ADD DATA
		tableOfVariable.append(newSymbol);

		addPrecompileVariable(aContainer, newSymbol, tableOfVariable);
	}

}


/**
 *******************************************************************************
 * COMPILATION
 *******************************************************************************
 */

void CompilerOfVariable::compileVariable(ExecutableForm & anExecutable)
{
	TableOfInstanceOfData::ref_iterator itVar =
			anExecutable.getConstVariable().begin();
	TableOfInstanceOfData::ref_iterator endVar =
			anExecutable.getConstVariable().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->hasAstVariable() )
		{
			compileConstVariable(anExecutable, (itVar));
		}
	}


	BFCode onInitialize( OperatorManager::OPERATOR_SEQUENCE );

	itVar = anExecutable.getAllVariables().begin();
	endVar = anExecutable.getAllVariables().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->hasAstVariable() )
		{
			compileVariableOnCreate(anExecutable, itVar, onInitialize);

			compileVariable(anExecutable, (itVar));
		}
	}

	if( onInitialize->hasOperand() )
	{
		BehavioralPart * theBehavioralPart = const_cast< Machine & >(
				anExecutable.getAstMachine() ).getUniqBehaviorPart();

		onInitialize = StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						onInitialize, theBehavioralPart->getOnCreate() );

		theBehavioralPart->setOnCreate( onInitialize->hasManyOperands() ?
				onInitialize : onInitialize->first().bfCode() );
	}
}


void CompilerOfVariable::compileVariableOnCreate(ExecutableForm & anExecutable,
		TableOfInstanceOfData::ref_iterator itVar, BFCode & onInitialize)
{
	const Variable & aVariable = (itVar)->getAstVariable();

	const BF & aValue = ( (itVar)->hasAliasTarget() &&
			(itVar)->getAliasTarget()->as< InstanceOfData >().hasValue() )?
				(itVar)->getAliasTarget()->as< InstanceOfData >().getValue() :
					( (itVar)->hasValue() ?
							(itVar)->getValue() : aVariable.getValue() );

	if( aValue.valid() )
	{
		if( not ( (itVar)->hasParent()
				&& (itVar)->getParent()->hasValue() ) )
		{
			onInitialize->append( StatementConstructor::newCode(
					aVariable.getAssignOperator(), (*itVar), aValue ) );
		}
	}
}

void CompilerOfVariable::compileVariable(AvmProgram & aProgram)
{
	TableOfInstanceOfData::ref_iterator itVar =
			aProgram.getConstVariable().begin();
	TableOfInstanceOfData::ref_iterator endVar =
			aProgram.getConstVariable().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->hasAstVariable() )
		{
			compileConstVariable(aProgram, (itVar));
		}
	}


	itVar = aProgram.getAllVariables().begin();
	endVar = aProgram.getAllVariables().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->hasAstVariable() )
		{
			compileVariable(aProgram, (itVar));
		}
	}
}


void CompilerOfVariable::compileConstVariable(
		AvmProgram & aContainer, InstanceOfData & aVarInstance)
{
	if( aVarInstance.hasAstVariable() )
	{
		const Variable & astVariable = aVarInstance.getAstVariable();
		if( astVariable.hasOnWrite() )
		{
			//!!! ERROR
		}

		compileVariable_initialValue(aContainer, aVarInstance);
	}
}


void CompilerOfVariable::compileVariable(
		AvmProgram & aContainer, InstanceOfData & aVarInstance)
{
	const Variable & astVariable = aVarInstance.getAstVariable();

	if( astVariable.hasOnWrite() &&
			astVariable.getOnWriteRoutine().doSomething() )
	{
		AvmProgram * onWriteProg = mAvmcodeCompiler.compileRoutine(*this,
				aContainer, (& aVarInstance), astVariable.getOnWriteRoutine());

		if( aVarInstance.isConcreteStructAttribute() )
		{
			onWriteProg->setFullyQualifiedNameContainer( aVarInstance );
		}

		aVarInstance.setOnWriteRoutine( onWriteProg );

		aContainer.refExecutable().saveAnonymousInnerRoutine( onWriteProg );
	}

	else if( aVarInstance.hasTypeSpecifier() &&
			aVarInstance.getTypeSpecifier().hasConstraint() )
	{
		aVarInstance.setOnWriteRoutine( aVarInstance.getTypeSpecifier().
				getConstraint().as_ptr< AvmProgram >() );
	}
	else if( aVarInstance.hasTypeSpecifier() &&
			aVarInstance.getTypeSpecifier().referedTypeSpecifier().hasConstraint() )
	{
		aVarInstance.setOnWriteRoutine(
				aVarInstance.getTypeSpecifier().referedTypeSpecifier().
							getConstraint().as_ptr< AvmProgram >() );
	}
//	else if( astVariable.hasDataType() &&
//			astVariable.getDataType()->getConstraintRoutine().doSomething() )
//	{
//		aVarInstance.setOnWriteRoutine( compileVariable_monitor(
//				aContainer, aVarInstance,
//				astVariable.getDataType()->getConstraintRoutine()) );
//	}

	compileVariable_initialValue(aContainer, aVarInstance);
}


BF CompilerOfVariable::precompileVariable_initialValue(AvmProgram & aContainer,
		const BaseTypeSpecifier & aTypeSpecifier, const BF & aValue)
{
	if( aValue.invalid() )
	{
		return( BF::REF_NULL );
	}

	else if( aValue.is< Number >()   || aValue.is< Boolean >() ||
			aValue.is< Character >() || aValue.is< String >() )
	{
		return( aValue );
	}

	else if( aValue.is< InstanceOfData >() )
	{
		if( aValue.to< InstanceOfData >().hasValue() &&
			ExpressionTypeChecker::isFinalSymbolicBasicSymbol(
					aValue.to< InstanceOfData >().getValue()) )
		{
			return( aValue.to< InstanceOfData >().getValue() );
		}
		else if( aValue.to< InstanceOfData >().getModifier().
					hasModifierPublicFinalStaticParameter() )
		{
			return( aValue );
		}
	}

	else if( aValue.is_strictly< BuiltinArray >() )
	{
		const BuiltinArray & aBuiltinArrayValue = aValue.to< BuiltinArray >();

		if( aBuiltinArrayValue.is< ArrayIdentifier >()
			|| aBuiltinArrayValue.is< ArrayQualifiedIdentifier >() )
		{
			return( BF::REF_NULL );
		}
		else if( aTypeSpecifier.hasTypeListCollection() )
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					aTypeSpecifier.as< ContainerTypeSpecifier >() );

			containerValue->copy(aBuiltinArrayValue, std::min(
					containerValue->capacity(), aBuiltinArrayValue.size()) );

			return( BF(containerValue) );
		}

		else
		{
			ArrayBF * bfArray = aBuiltinArrayValue.getArrayBF();

			if( bfArray->getTypeSpecifier().isNTEQ( aTypeSpecifier )
				&& ExpressionTypeChecker::isTyped(aTypeSpecifier, aValue) )
			{
				bfArray->setTypeSpecifier( aTypeSpecifier );
			}

			if( bfArray->getTypeSpecifier().is< ContainerTypeSpecifier >()
				&& bfArray->getTypeSpecifier().to<
						ContainerTypeSpecifier >().weaklyTypedIdentifier() )
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
			/*&& aVarInstance.getModifier().hasFeatureFinal
			&& ExpressionTypeChecker::isFinalSymbolicCompositeSymbol(
					aValue.to_ptr< ArrayBF >())*/ )
	{
		bool isFinalSymbol = true;

		CompilationEnvironment compilENV(aContainer);

		ArrayBF * bfArray = aValue.to_ptr< ArrayBF >();
		for( std::size_t idx = 0 ; idx < bfArray->size() ; ++idx )
		{
			const BF & arg = bfArray->at(idx);
			if( arg.is< Variable >() )
			{
				if( arg.to< Variable >().hasValue()
					&& ExpressionTypeChecker::isFinalSymbolicSymbol(
							arg.to< Variable >().getValue()) )
				{
					const BF & compiledVar =
							mAvmcodeCompiler.getSymbolTable().searchSemSymbol(
									compilENV.mCTX, arg.to< Variable >() );

					if( compiledVar.valid()
						&& compiledVar.is< InstanceOfData >()
						&& compiledVar.to< InstanceOfData >().hasValue() )
					{
						bfArray->set(idx,
							compiledVar.to< InstanceOfData >().getValue() );
					}
					else if( aTypeSpecifier.hasTypeContainer() )
					{
						BF constVal = precompileVariable_initialValue(
								aContainer,
								aTypeSpecifier.as< ContainerTypeSpecifier >()
										.getContentsTypeSpecifier(),
								arg.to< Variable >().getValue());

						if( constVal.valid() )
						{
							bfArray->set(idx, constVal);
						}
						else
						{
							isFinalSymbol = false;
							break;
						}
					}
					else if( aTypeSpecifier.isTypedClass() )
					{
						BF constVal = precompileVariable_initialValue(
								aContainer,
								aTypeSpecifier.as< ClassTypeSpecifier >()
										.getSymbolData(idx).getTypeSpecifier(),
								arg.to< Variable >().getValue());

						if( constVal.valid() )
						{
							bfArray->set(idx, constVal);
						}
						else
						{
							isFinalSymbol = false;
							break;
						}
					}
					else
					{
						bfArray->set(idx, arg.to< Variable >().getValue() );
					}
				}
				else
				{
					isFinalSymbol = false;
					break;
				}
			}
			else if( not ExpressionTypeChecker::isFinalSymbolicSymbol( arg ) )
			{
				isFinalSymbol = false;
				break;
			}
		}

		if( isFinalSymbol )
		{
			if( aValue.to< ArrayBF >().getTypeSpecifier().isNTEQ(
					aTypeSpecifier )
				&& ExpressionTypeChecker::isTyped(aTypeSpecifier, aValue) )
			{
				aValue.to_ptr< ArrayBF >()->setTypeSpecifier( aTypeSpecifier );
			}

			return( aValue );
		}
	}

	else if( aTypeSpecifier.isTypedArray() )
	{
		if( ExpressionTypeChecker::isFinalSymbolicBasicSymbol(aValue) )
		{
			return( BF( new ArrayBF(aTypeSpecifier,
					aTypeSpecifier.size(), aValue) ) );
		}
	}

	else if( aTypeSpecifier.isTypedEnum() )
	{
		if( aValue.is< Variable >() )
		{
			return( aTypeSpecifier.as< EnumTypeSpecifier >().getSymbolData().
					getByAstElement( aValue.to< Variable >() ) );
		}
		else if( aValue.is< Identifier >() )
		{
			return( aTypeSpecifier.as< EnumTypeSpecifier >().getSymbolData().
					getByNameID( aValue.to< Identifier >().getValue() ) );
		}
		else
		{
			return( aTypeSpecifier.as< EnumTypeSpecifier >()
					.getSymbolData().getByQualifiedNameID( aValue.str() ) );
		}
	}

	return( BF::REF_NULL );
}

void CompilerOfVariable::precompileVariable_initialValue(
		AvmProgram & aContainer, InstanceOfData & aVarInstance)
{
	const Variable & astVariable = aVarInstance.getAstVariable();

	BF aValue = astVariable.getValue();
	if( aValue.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "variable:precompile#value> " << str_header( astVariable )
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		aVarInstance.setValue( precompileVariable_initialValue(aContainer,
				aVarInstance.getTypeSpecifier(), aValue) );

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "instance:> " << str_header( aVarInstance ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	}
}



void CompilerOfVariable::compileVariable_initialValue(
		AvmProgram & aContainer, InstanceOfData & aVarInstance)
{
	const Variable & astVariable = aVarInstance.getAstVariable();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << "variable:compile#value> " << str_header( astVariable )
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	if( not aVarInstance.hasValue() )
	{
		const BF & aValue = astVariable.getValue();
		if( aValue.valid() )
		{
			CompilationEnvironment compilENV(aContainer);
			compilENV.mCTX->mType = aVarInstance.ptrTypeSpecifier();

			aVarInstance.setValue(	mAvmcodeCompiler.
					decode_compileExpression(compilENV.mCTX, aValue) );

			if( aVarInstance.getValue().is< ArrayBF >() )
			{
				ArrayBF * bfArray = aVarInstance.getValue().to_ptr< ArrayBF >();
				for( std::size_t idx = 0 ; idx < bfArray->size() ; ++idx )
				{
					const BF & arg = bfArray->at(idx);
					if( arg.is< InstanceOfData >() &&
							arg.to< InstanceOfData >().hasValue() &&
							ExpressionTypeChecker::isFinalSymbolicSymbol(
								arg.to< InstanceOfData >().getValue()) )
					{
						bfArray->set(idx,
							arg.to< InstanceOfData >().getValue() );
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
		AvmProgram & aContainer, InstanceOfData & aVarInstance)
{
	AVM_OS_ASSERT_WARNING_ALERT( aVarInstance.getModifier().hasFeatureUnsafe()
			|| aContainer.getModifier().hasFeatureUnsafe()
			|| PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
			<< "Unexpected a << non-unsafe >> InstanceOfData !!!"
			<< SEND_ALERT;

	const BaseTypeSpecifier & aTypeSpecifier = aVarInstance.getTypeSpecifier();
	if( aTypeSpecifier.couldGenerateConstraint() )
	{
		AvmProgram * onWriteProg = new AvmProgram(
				Specifier::SCOPE_ROUTINE_KIND,
				(& aContainer), aVarInstance.getAstElement(), 1);
		onWriteProg->updateUfid( "#onWriteTypeConstraint" );
		onWriteProg->setParamOffsetCount(0, 1);

		BF newValue( new InstanceOfData(
				IPointerVariableNature::POINTER_STANDARD_NATURE, onWriteProg,
				aVarInstance.getAstElement(), aTypeSpecifier, "newValue",  0) );
		onWriteProg->setVariable(0, newValue);
		onWriteProg->updateVariableTable();

		BFCode code( aVarInstance.hasTypedClockTime()
					? OperatorManager::OPERATOR_TIMED_GUARD
					: OperatorManager::OPERATOR_GUARD,
				aTypeSpecifier.genConstraint(newValue) );

		onWriteProg->setCode(code);

		aVarInstance.setOnWriteRoutine( onWriteProg );

		aContainer.refExecutable().saveAnonymousInnerRoutine( onWriteProg );
	}
}


}
