/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionTypeChecker.h"

#include <fml/executable/InstanceOfMachine.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>
#include <fml/type/TypeManager.h>


namespace sep
{


bool ExpressionTypeChecker::isFinalSymbolicBasicSymbol(const BF & anElement)
{
	if( anElement.is< Identifier >() || anElement.is< QualifiedIdentifier >() )
	{
		return( false );
	}
	else if( anElement.is< BuiltinForm >() )
	{
		return( true );
	}

	else if( anElement.is< InstanceOfData >()  )
	{
		InstanceOfData * anInstance = anElement.to_ptr< InstanceOfData >();

		if( anInstance->isTypedEnum() )
		{
			return( anInstance->isEnumSymbolPointer() );
		}
		else if( anInstance->isTypedMachine() )
		{
			return( true );
		}
//		else if( anInstance->getModifier().hasModifierPublicFinalStatic() )
//		{
//			return( true );
//		}
	}

	else if( anElement.is< InstanceOfMachine >()
			&& anElement.to< InstanceOfMachine >()
					.getModifier().hasModifierPublicFinalStatic() )
	{
		return( true );
	}

	else if( anElement.is< BaseInstanceForm >()
			&& anElement.to< BaseInstanceForm >()
					.getModifier().hasModifierPublicFinalStatic() )
	{
		return( true );
	}

	else if( anElement.is_strictly< BuiltinArray >() )
	{
		return( true );
	}

	return( false );
}


bool ExpressionTypeChecker::isFinalSymbolicCompositeSymbol(const BF & anElement)
{
	if( anElement.is< BuiltinArray >() )
	{
		return( isFinalSymbolicCompositeSymbol(anElement.to_ptr< BuiltinArray >()) );
	}
	else
	{
		return( false );
	}
}


bool ExpressionTypeChecker::isFinalSymbolicCompositeSymbol(
		BuiltinArray * arrayForm)
{
	if( arrayForm->is_strictly< ArrayBF >() )
	{
		return( true );
	}
	if( arrayForm->is< ArrayBF >() )
	{
		ArrayBF * bfArray = arrayForm->to_ptr< ArrayBF >();
		for( std::size_t idx = 0 ; idx < bfArray->size() ; ++idx )
		{
			if( not isFinalSymbolicSymbol( bfArray->at(idx) ) )
			{
				return( false );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isMachine(
		const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< BaseInstanceForm >()
		&& ( ExpressionTypeChecker::isTyped(refTypeSpecifier,
				anExpr.to< BaseInstanceForm >().getTypeSpecifier())
			|| anExpr.to< BaseInstanceForm >().isTypedMachine() ) )
	{
		return( true );
	}
	else if( anExpr.is< RuntimeID >() )
	{
		return( true );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		switch( aCode.getAvmOpCode() )
		{
			case AVM_OPCODE_SELF:
			case AVM_OPCODE_SUPER:

			case AVM_OPCODE_SCHEDULE_GET:
			case AVM_OPCODE_INVOKE_NEW:
			{
				return( true );
			}

			case AVM_OPCODE_POP:
			case AVM_OPCODE_TOP:
			case AVM_OPCODE_ASSIGN_TOP:
			{

				return( aCode.hasOperand()
						&& isCollectionOfTypedElement(
								TypeManager::MACHINE, aCode.first()) );
			}

			default:
			{
				return( false );
			}
		}

//		return( StatementTypeChecker::isMachine( anExpr ) );
	}

	return( false );
}


bool ExpressionTypeChecker::isArray(
		const ContainerTypeSpecifier & refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< ArrayBF >() )
	{
		ArrayBF * bArray = anExpr.to_ptr< ArrayBF >();
		for( std::size_t idx = 1 ; idx < bArray->size() ; ++idx )
		{
			if( not ExpressionTypeChecker::isTyped(
					refTypeSpecifier.getContentsTypeSpecifier(),
					bArray->at(idx)) )
			{
				return( false );
			}
		}
		return( true );
	}
	else if( anExpr.is< BuiltinArray >() )
	{
		BuiltinArray * bArray = anExpr.to_ptr< BuiltinArray >();

		if( ExpressionTypeChecker::isTyped(
				refTypeSpecifier, bArray->getTypeSpecifier()) )
		{
			return( true );
		}
		else if( bArray->getTypeSpecifier().isTypedArray() &&
				(refTypeSpecifier.getContentsTypeSpecifier()
				== bArray->getTypeSpecifier().as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier()) )
		{
			return( true );
		}
		else
		{
			AVM_OS_WARN << "ExpressionTypeChecker::isArray :> ref< @ "
					<< refTypeSpecifier.raw_address()
					<< "->" << refTypeSpecifier.strT()
					<< " > =/=  dtype< @ "
					<< bArray->getTypeSpecifier().raw_address()
					<< "-> " << bArray->getTypeSpecifier().strT()
					<< " >" << std::endl;

//			bArray->getTypeSpecifier().toStream(AVM_OS_WARN);
		}
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier.getContentsTypeSpecifier(),
				bArray->getTypeSpecifier()) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier.getContentsTypeSpecifier(),
				anExpr.to< BaseInstanceForm >().getTypeSpecifier()) );
	}

	return( false );
}


bool ExpressionTypeChecker::isClass(
		const ClassTypeSpecifier & refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< BuiltinArray >() )
	{
		BuiltinArray * bArray = anExpr.to_ptr< BuiltinArray >();

		if( ExpressionTypeChecker::isTyped(
				refTypeSpecifier, bArray->getTypeSpecifier()) )
		{
			return( true );
		}
		else if( refTypeSpecifier.size() != bArray->size() )
		{
			return( false );
		}
		else if( bArray->hasTypeSpecifier() &&
				anExpr.is_strictly< BuiltinArray >() &&
				bArray->getTypeSpecifier().hasTypeContainer() )
		{
			const BaseTypeSpecifier & eltTS = bArray->getTypeSpecifier()
					.as< ContainerTypeSpecifier >().getContentsTypeSpecifier();

			if( ExpressionTypeChecker::isTyped(refTypeSpecifier, eltTS) )
			{
				return( true );
			}
			else if( eltTS.isTypedClass() )
			{
				const ClassTypeSpecifier & eltClassTS =
						eltTS.to< ClassTypeSpecifier >();

				 if( eltClassTS.getSymbolData().size()
					!= refTypeSpecifier.getSymbolData().size() )
				 {
						AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
								<< refTypeSpecifier.strT()
								<< " > =/=  dtype< " << eltClassTS.strT() << " >"
								<< std::endl;

						return( false );
				 }

				 TableOfSymbol::const_iterator itElt =
						 eltClassTS.getSymbolData().begin();

				TableOfSymbol::const_iterator itRef =
						refTypeSpecifier.getSymbolData().begin();
				TableOfSymbol::const_iterator endItRef =
						refTypeSpecifier.getSymbolData().end();
				for( ; itRef != endItRef ; ++itRef , ++itElt )
				{
					if( not ExpressionTypeChecker::isTyped(
							(*itRef).getTypeSpecifier(), (*itElt).getTypeSpecifier()) )
					{
						AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
								<< (*itRef).getTypeSpecifier().strT()
								<< " > =/=  dtype< "
								<< (*itElt).getTypeSpecifier().strT() << " >"
								<< std::endl;

						return( false );
					}
				}
				return( true );
			}
			else //if( eltTS.isTypedUniversal() )
			{
				TableOfSymbol::const_iterator it =
						refTypeSpecifier.getSymbolData().begin();
				TableOfSymbol::const_iterator endIt =
						refTypeSpecifier.getSymbolData().end();
				for( std::size_t offset = 0; it != endIt ; ++it , ++offset )
				{
					if( not ExpressionTypeChecker::isTyped(
							(*it).getTypeSpecifier(), bArray->at(offset)) )
					{
						AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
								<< (*it).getTypeSpecifier().strT() << " > =/= arg<"
								<< str_indent( bArray->at(offset) ) << " >"
								<< std::endl;

						return( false );
					}
				}
				return( true );
			}
		}
		else if( bArray->is< ArrayBF >() )
		{
			ArrayBF * bfArray = bArray->to_ptr< ArrayBF >();

			TableOfSymbol::const_iterator it =
					refTypeSpecifier.getSymbolData().begin();
			TableOfSymbol::const_iterator endIt =
					refTypeSpecifier.getSymbolData().end();
			for( std::size_t offset = 0; it != endIt ; ++it , ++offset )
			{
				if( not ExpressionTypeChecker::isTyped(
						(*it).getTypeSpecifier(), bfArray->at(offset)) )
				{
					AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
							<< (*it).getTypeSpecifier().strT() << " > =/= arg<"
							<< str_indent( bfArray->at(offset) ) << " >"
							<< std::endl;

					return( false );
				}
			}
			return( true );
		}
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::isTyped(refTypeSpecifier,
				anExpr.to< BaseInstanceForm >().getTypeSpecifier()) );
	}
	else if( anExpr.is< ArrayBF >() )
	{
		ArrayBF * bfArray = anExpr.to_ptr< ArrayBF >();

		if( refTypeSpecifier.getSymbolData().size() !=  bfArray->size() )
		{
			return( false );
		}

		TableOfSymbol::const_iterator it =
				refTypeSpecifier.getSymbolData().begin();
		TableOfSymbol::const_iterator endIt =
				refTypeSpecifier.getSymbolData().end();
		for( std::size_t offset = 0; it != endIt ; ++it , ++offset )
		{
			if( not ExpressionTypeChecker::isTyped(
					(*it).getTypeSpecifier(), bfArray->get(offset)) )
			{
				AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
						<< (*it).getTypeSpecifier().strT()
						<< " > =/=  dtype< " << bfArray->get(offset).str()
						<< " >" << std::endl;
				return( false );
			}
		}
		return( true );
	}

	return( false );
}


bool ExpressionTypeChecker::isCollection(
		const ContainerTypeSpecifier & refTypeSpecifier, const BF & anExpr)
{
	if(  anExpr.is< ArrayBF >() )
	{
		ArrayBF * bArray = anExpr.to_ptr< ArrayBF >();
		for( std::size_t idx = 1 ; idx < bArray->size() ; ++idx )
		{
			if( not ExpressionTypeChecker::isTyped(
					refTypeSpecifier.getContentsTypeSpecifier(),
					bArray->at(idx)) )
			{
				return( false );
			}
		}
		return( true );
	}
	else if(  anExpr.is< BuiltinContainer >() )
	{
		BuiltinContainer * bArray = anExpr.to_ptr< BuiltinContainer >();
		for( std::size_t idx = 1 ; idx < bArray->size() ; ++idx )
		{
			if( not ExpressionTypeChecker::isTyped(
					refTypeSpecifier.getContentsTypeSpecifier(),
					bArray->at(idx)) )
			{
				return( false );
			}
		}
		return( true );
	}
	else if( anExpr.is< BuiltinArray >() )
	{
		BuiltinArray * bArray = anExpr.to_ptr< BuiltinArray >();

		if( ExpressionTypeChecker::isTyped(
				refTypeSpecifier, bArray->getTypeSpecifier()) )
		{
			return( true );
		}
		else if( bArray->getTypeSpecifier().isTypedArray() &&
				(refTypeSpecifier.getContentsTypeSpecifier()
				== bArray->getTypeSpecifier().as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier()) )
		{
			return( true );
		}
		else
		{
			AVM_OS_WARN << "ExpressionTypeChecker::isCollection :> ref< @ "
					<< refTypeSpecifier.raw_address()
					<< "->" << refTypeSpecifier.strT()
					<< " > =/=  dtype< @ "
					<< bArray->getTypeSpecifier().raw_address()
					<< "-> " << bArray->getTypeSpecifier().strT()
					<< " >" << std::endl;

//			bArray->getTypeSpecifier().toStream(AVM_OS_WARN);
		}
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier.getContentsTypeSpecifier(),
				bArray->getTypeSpecifier()) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier.getContentsTypeSpecifier(),
				anExpr.to< BaseInstanceForm >().getTypeSpecifier()) );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isContainerOperation(aCode.getOperator()) )
		{
			return( ExpressionTypeChecker::isTyped(
					refTypeSpecifier, aCode.first()) );
		}
		if( OperatorManager::isContainerElementAccess(aCode.getOperator()) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						ExpressionTypeChecker::isTyped(refTypeSpecifier,
							bts.as< ContainerTypeSpecifier >()
								.getContentsTypeSpecifier()) );
			}
		}
	}

	return( false );
}

bool ExpressionTypeChecker::isCollectionOfTypedElement(
		const BaseTypeSpecifier & refTypeSpecifier, const BF & anExpr)
{
	if(  anExpr.is< ArrayBF >() )
	{
		const BaseTypeSpecifier & bts =
				anExpr.to< ArrayBF >().getTypeSpecifier();

		return( bts.isnotNullref()
				&& bts.hasTypeContainer()
				&& ExpressionTypeChecker::isTyped(refTypeSpecifier,
					bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier()) );
	}
	else if(  anExpr.is< BuiltinContainer >() )
	{
		BuiltinContainer * bArray = anExpr.to_ptr< BuiltinContainer >();

		return( bArray->nonempty()
				&& ExpressionTypeChecker::isCollectionOfTypedElement(
						refTypeSpecifier, bArray->first()) );
	}
	else if( anExpr.is< BuiltinArray >() )
	{
		const BaseTypeSpecifier & bts =
				anExpr.to< BuiltinArray >().getTypeSpecifier();

		return( bts.isnotNullref()
				&& bts.hasTypeContainer()
				&& ExpressionTypeChecker::isTyped(refTypeSpecifier,
					bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier()) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		const BaseTypeSpecifier & bts =
				anExpr.to< BaseInstanceForm >().getTypeSpecifier();

		return( bts.hasTypeContainer()
				&& ExpressionTypeChecker::isTyped(refTypeSpecifier,
					bts.as< ContainerTypeSpecifier >()
							.getContentsTypeSpecifier()) );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isContainerOperation(aCode.getOperator()) )
		{
			return( ExpressionTypeChecker::isCollectionOfTypedElement(
					refTypeSpecifier, aCode.first()) );
		}
		if( OperatorManager::isContainerElementAccess(aCode.getOperator()) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer()
						&& ExpressionTypeChecker::isTyped(refTypeSpecifier,
							bts.as< ContainerTypeSpecifier >()
									.getContentsTypeSpecifier()) );
			}
		}
	}

	return( false );
}

bool ExpressionTypeChecker::isVector(const BF & anExpr)
{
	if(  anExpr.is< BuiltinVector >() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >()
				.getTypeSpecifier().hasTypeVector() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isContainerOperation(aCode.getOperator()) )
		{
			return( ExpressionTypeChecker::isVector( aCode.first() ) );
		}
		else if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to<
							BaseTypeSpecifier >().hasTypeVector() );
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isEnum(
		const EnumTypeSpecifier & refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< InstanceOfData >() )
	{
		if( ExpressionTypeChecker::isTyped(refTypeSpecifier,
				anExpr.to< InstanceOfData >().getTypeSpecifier()) )
		{
			return( true );
		}
		else
		{
			AVM_OS_WARN << "ExpressionTypeChecker::isEnum :> ref< @ "
					<< refTypeSpecifier.strT() << " > =/=  dtype< @ "
					<< anExpr.to< InstanceOfData >().getTypeSpecifier().strT()
					<< " >" << std::endl;

			return( false);
		}
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::isTyped(refTypeSpecifier,
				anExpr.to< BaseInstanceForm >().getTypeSpecifier()) );
	}

	else if( anExpr.isNumeric() )
	{
		return( refTypeSpecifier.hasSymbolDataWithValue(anExpr) );
	}

	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isContainerElementAccess(aCode.getOperator()) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						ExpressionTypeChecker::isTyped(refTypeSpecifier,
								bts.as< ContainerTypeSpecifier >()
								.getContentsTypeSpecifier()) );
			}
		}
	}

	return( false );
}



bool ExpressionTypeChecker::isEnum(const BF & anExpr)
{
	if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedEnum() );
	}

	return( false );
}



bool ExpressionTypeChecker::isCharacter(const BF & anExpr)
{
	if( anExpr.isCharacter() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedCharacter() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( aCode.hasInstruction() && (aCode.getInstruction()->
				getMainProcessor() == AVM_ARG_CHARACTER_CPU) )
		{
			return( true );
		}

		else if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							isTypedCharacter() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >()
						.isTypedCharacter() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isCharacter(aCode.second()) );
			}
		}
		else if( OperatorManager::isCharacter( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isCharacter( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().isTypedCharacter() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isString(const BF & anExpr)
{
	if( anExpr.isBuiltinString() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedString() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( aCode.hasInstruction() && (aCode.getInstruction()->
				getMainProcessor() == AVM_ARG_STRING_CPU) )
		{
			return( true );
		}

		else if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
				aCode.first().to< BaseTypeSpecifier >().isTypedString() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >()
						.isTypedString() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isString(aCode.second()) );
			}
		}
		else if( OperatorManager::isString( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isString( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().isTypedString() );
			}
		}
	}

	return( false );
}



bool ExpressionTypeChecker::isBoolean(const BF & anExpr, bool stronglyTypedFlag)
{
	if( anExpr.isBoolean() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedBoolean() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							isTypedBoolean() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return(aCode.first().to< BaseInstanceForm >()
						.isTypedBoolean() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isBoolean(aCode.second(),
						stronglyTypedFlag) );
			}
		}
		else if( OperatorManager::isRelational( aCode.getOperator() )
				|| OperatorManager::isQuantifier( aCode.getOperator() ) )
		{
			return( true );
		}

		else if( OperatorManager::isPropositional( aCode.getOperator() ) )
		{
			if( stronglyTypedFlag )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					if( not ExpressionTypeChecker::isBoolean( itOperand ) )
					{
						return( false );
					}
				}
			}
			return( true );
		}

		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().isTypedBoolean() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isInteger(const BF & anExpr)
{
	if( anExpr.isWeakInteger() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().weaklyTypedInteger() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							weaklyTypedInteger() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >()
						.weaklyTypedInteger() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isInteger(aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isInteger( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainInteger( aCode.getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedInteger() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isRational(const BF & anExpr)
{
	if( anExpr.isWeakRational() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().weaklyTypedRational() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							weaklyTypedRational() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >()
						.weaklyTypedRational() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isRational(aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isRational( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainRational( aCode.getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedRational() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isFloat(const BF & anExpr)
{
	if( anExpr.isWeakFloat() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().weaklyTypedFloat() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							weaklyTypedFloat() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >()
						.weaklyTypedFloat() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isFloat(aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isFloat( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainFloat( aCode.getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedFloat() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isReal(const BF & anExpr)
{
	if( anExpr.isWeakReal() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().weaklyTypedReal() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to<
							BaseTypeSpecifier >().weaklyTypedReal() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to<
						BaseInstanceForm >().weaklyTypedReal() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isReal(aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isReal( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainReal( aCode.getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedReal() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isOperator(const BF & anExpr)
{
	if( anExpr.is< Operator >() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(TypeManager::OPERATOR,
				anExpr.to< BaseInstanceForm >().getTypeSpecifier()) );
	}

	return( false );
}


bool ExpressionTypeChecker::isAvmCode(const BF & anExpr)
{
	if( anExpr.is< AvmCode >() )
	{
		return( true );
	}

	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(TypeManager::AVMCODE,
				anExpr.to< BaseInstanceForm >().getTypeSpecifier()) );
	}

	return( false );
}


// CLOCK & TIME type checking
//bool ExpressionTypeChecker::isClock(
//		const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
//{
//	if( anExpr.isBuiltinValue() )
//	{
//		return( isTyped(typeSpecifier.getContentsTypeSpecifier(), anExpr) );
//	}
//	else if( anExpr.is< BaseInstanceForm >() )
//	{
//		return( anExpr.to< BaseInstanceForm >().isTypedClock() );
//	}
//	else if( anExpr.is< AvmCode >() )
//	{
//		const AvmCode & aCode = anExpr.to< AvmCode >();
//
//		if( OperatorManager::isCtor( aCode.getOperator() ) )
//		{
//			return( aCode.first().is< BaseTypeSpecifier >() &&
//					aCode.first().to<
//					BaseTypeSpecifier >().isTypedClock() );
//		}
//		else if( OperatorManager::isAssign( aCode.getOperator() ) )
//		{
//			if( aCode.first().is< BaseInstanceForm >() )
//			{
//				return( aCode.first().to<
//						BaseInstanceForm >().isTypedClock() );
//			}
//			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
//			{
//				return( ExpressionTypeChecker::isClock(
//						typeSpecifier, aCode.second()) );
//			}
//		}
//		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
//		{
//			for( const auto & itOperand : aCode.getOperands() )
//			{
//				if( not ExpressionTypeChecker::isClock(
//						typeSpecifier, itOperand ) )
//				{
//					return( false );
//				}
//			}
//			return( true );
//		}
//		else if( OperatorManager::isContainerElementAccess(
//				aCode.getOperator() ) )
//		{
//			if( aCode.first().is< BaseInstanceForm >() )
//			{
//				const BaseTypeSpecifier & bts = aCode.first().
//						to< BaseInstanceForm >().getTypeSpecifier();
//
//				return( bts.hasTypeContainer() &&
//						bts.as< ContainerTypeSpecifier >().
//						getContentsTypeSpecifier().isTypedClock() );
//			}
//		}
//	}
//
//	return( false );
//}
//
//bool ExpressionTypeChecker::isTime(
//		const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
//{
//	if( anExpr.isBuiltinValue() )
//	{
//		return( isTyped(typeSpecifier.getContentsTypeSpecifier(), anExpr) );
//	}
//	else if( anExpr.is< BaseInstanceForm >() )
//	{
//		return( anExpr.to< BaseInstanceForm >().isTypedTime() );
//	}
//	else if( anExpr.is< AvmCode >() )
//	{
//		const AvmCode & aCode = anExpr.to< AvmCode >();
//
//		if( OperatorManager::isCtor( aCode.getOperator() ) )
//		{
//			return( aCode.first().is< BaseTypeSpecifier >() &&
//					aCode.first().to<
//					BaseTypeSpecifier >().isTypedTime() );
//		}
//		else if( OperatorManager::isAssign( aCode.getOperator() ) )
//		{
//			if( aCode.first().is< BaseInstanceForm >() )
//			{
//				return( aCode.first().to<
//						BaseInstanceForm >().isTypedTime() );
//			}
//			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
//			{
//				return( ExpressionTypeChecker::isTime(
//						typeSpecifier, aCode.second()) );
//			}
//		}
//		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
//		{
//			for( const auto & itOperand : aCode.getOperands() )
//			{
//				if( not ExpressionTypeChecker::isTime(
//						typeSpecifier,  itOperand ) )
//				{
//					return( false );
//				}
//			}
//			return( true );
//		}
//		else if( OperatorManager::isContainerElementAccess(
//				aCode.getOperator() ) )
//		{
//			if( aCode.first().is< BaseInstanceForm >() )
//			{
//				const BaseTypeSpecifier & bts = aCode.first().
//						to< BaseInstanceForm >().getTypeSpecifier();
//
//				return( bts.hasTypeContainer() &&
//						bts.as< ContainerTypeSpecifier >().
//						getContentsTypeSpecifier().isTypedTime() );
//			}
//		}
//	}
//
//	return( false );
//}

bool ExpressionTypeChecker::isClockTime(
		const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
{
	if( anExpr.isBuiltinValue() )
	{
		return( isTyped(typeSpecifier.getContentsTypeSpecifier(), anExpr) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().hasTypedClockTime() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to<
							BaseTypeSpecifier >().hasTypedClockTime() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to<
						BaseInstanceForm >().hasTypedClockTime() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isClockTime(
						typeSpecifier, aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( ExpressionTypeChecker::isClockTime(typeSpecifier, itOperand ) )
				{
					continue;
				}
				else if( ExpressionTypeChecker::isTyped(
						typeSpecifier.getContentsTypeSpecifier(), itOperand ) )
				{
					continue;
				}
				else
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().hasTypedClockTime() );
			}
		}
	}

	return( false );
}



bool ExpressionTypeChecker::isClockTime(const BF & anExpr)
{
	if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().hasTypedClockTime() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().hasTypedClockTime() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to<
						BaseInstanceForm >().hasTypedClockTime() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isClockTime(aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isClockTime( itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().hasTypedClockTime() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isContinuousTime(
		const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
{
	if( anExpr.isBuiltinValue() )
	{
		return( isTyped(typeSpecifier.getContentsTypeSpecifier(), anExpr) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedContinuousTime() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							isTypedContinuousTime() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >().
								isTypedContinuousTime() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isContinuousTime(
						typeSpecifier, aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isContinuousTime(
						typeSpecifier,  itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().isTypedContinuousTime() );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isDenseTime(
		const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
{
	if( anExpr.isBuiltinValue() )
	{
		return( isTyped(typeSpecifier.getContentsTypeSpecifier(), anExpr) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedDenseTime() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().isTypedDenseTime() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >().isTypedDenseTime() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isDenseTime(
						typeSpecifier, aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isDenseTime(
						typeSpecifier,  itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().isTypedDenseTime() );
			}
		}
	}

	return( false );
}

bool ExpressionTypeChecker::isDiscreteTime(
		const ContainerTypeSpecifier & typeSpecifier, const BF & anExpr)
{
	if( anExpr.isBuiltinValue() )
	{
		return( isTyped(typeSpecifier.getContentsTypeSpecifier(), anExpr) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to< BaseInstanceForm >().isTypedDiscreteTime() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		const AvmCode & aCode = anExpr.to< AvmCode >();

		if( OperatorManager::isCtor( aCode.getOperator() ) )
		{
			return( aCode.first().is< BaseTypeSpecifier >() &&
					aCode.first().to< BaseTypeSpecifier >().
							isTypedDiscreteTime() );
		}
		else if( OperatorManager::isAssign( aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				return( aCode.first().to< BaseInstanceForm >().
								isTypedDiscreteTime() );
			}
			else if( OperatorManager::isAssignBinary( aCode.getOperator() ) )
			{
				return( ExpressionTypeChecker::isDiscreteTime(
						typeSpecifier, aCode.second()) );
			}
		}
		else if( OperatorManager::isArithmetic( aCode.getOperator() ) )
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not ExpressionTypeChecker::isDiscreteTime(
						typeSpecifier,  itOperand ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode.getOperator() ) )
		{
			if( aCode.first().is< BaseInstanceForm >() )
			{
				const BaseTypeSpecifier & bts = aCode.first().
						to< BaseInstanceForm >().getTypeSpecifier();

				return( bts.hasTypeContainer() &&
						bts.as< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().isTypedDiscreteTime() );
			}
		}
	}

	return( false );
}


// CAST type checking
bool ExpressionTypeChecker::isCtor(
		const BaseTypeSpecifier & refTypeSpecifier, const AvmCode & aCode)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
		OperatorManager::isCtor( aCode.getOperator() ) )
			<< "Unexpected ctor< ? >( ? ) expression :> "
			<< IGNORE_FIRST_TAB << aCode.str()
			<< SEND_EXIT;

	return( aCode.first().is< BaseTypeSpecifier >() &&
			ExpressionTypeChecker::weaklyTyped(refTypeSpecifier,
					aCode.first().to< BaseTypeSpecifier >()) );
}


bool ExpressionTypeChecker::isNewfresh(
		const BaseTypeSpecifier & refTypeSpecifier, const AvmCode & aCode)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
		OperatorManager::isNewfresh( aCode.getOperator() ) )
			<< "Unexpected newfresh( ? ) expression :> "
			<< IGNORE_FIRST_TAB << aCode.str()
			<< SEND_EXIT;

	return( aCode.first().is< BaseInstanceForm >() &&
			ExpressionTypeChecker::weaklyTyped(refTypeSpecifier,
				aCode.first().to< BaseInstanceForm >().getTypeSpecifier()) );
}


static bool isPointerTyped(
		const BaseTypeSpecifier * refTypeSpecifier,
		const BaseTypeSpecifier * aTypeSpecifier)
{
	if( refTypeSpecifier == aTypeSpecifier )
	{
		return( true );
	}

	while( true )
	{
		if( refTypeSpecifier->is< TypeAliasSpecifier >() )
		{
			refTypeSpecifier = & (refTypeSpecifier->
					to< TypeAliasSpecifier >().targetTypeSpecifier() );
		}
		else if( refTypeSpecifier->is< IntervalTypeSpecifier >() )
		{
			refTypeSpecifier = refTypeSpecifier->
					to< IntervalTypeSpecifier >().getSupportTypeSpecifier();
		}
		else
		{
			break;
		}
	}

	while( true )
	{
		if( aTypeSpecifier->is< TypeAliasSpecifier >() )
		{
			aTypeSpecifier = & ( aTypeSpecifier->
					to< TypeAliasSpecifier >().targetTypeSpecifier() );
		}
		else if( aTypeSpecifier->is< IntervalTypeSpecifier >() )
		{
			aTypeSpecifier = aTypeSpecifier->
					to< IntervalTypeSpecifier >().getSupportTypeSpecifier();
		}
		else
		{
			break;
		}
	}

	if( refTypeSpecifier == aTypeSpecifier )
	{
		return( true );
	}


//	else if( refTypeSpecifier->isTypeSpecifierKind( aTypeSpecifier ) )
//	{
//		return( true );
//	}

	return( false );
}



bool ExpressionTypeChecker::isTyped(const BaseTypeSpecifier & refTypeSpecifier,
		const BaseTypeSpecifier & aTypeSpecifier)
{
	return( isPointerTyped((& refTypeSpecifier), (& aTypeSpecifier)) );
}



bool ExpressionTypeChecker::isTyped(
		const BaseTypeSpecifier & aRefTypeSpecifier, const BF & arg)
{
	const BaseTypeSpecifier * ptrRefTypeSpecifier = (& aRefTypeSpecifier);
	while( true )
	{
		if( ptrRefTypeSpecifier->is< TypeAliasSpecifier >() )
		{
			ptrRefTypeSpecifier = &( ptrRefTypeSpecifier->
					to< TypeAliasSpecifier >().targetTypeSpecifier() );
		}
		else if( ptrRefTypeSpecifier->is< IntervalTypeSpecifier >() )
		{
			ptrRefTypeSpecifier = ptrRefTypeSpecifier->
					to< IntervalTypeSpecifier >().getSupportTypeSpecifier();
		}
		else
		{
			break;
		}
	}

	const BaseTypeSpecifier & refTypeSpecifier = (* ptrRefTypeSpecifier);

	if( refTypeSpecifier.hasTypedClockTime() )
	{
		if( refTypeSpecifier.is< ContainerTypeSpecifier >() )
		{
			ptrRefTypeSpecifier = ptrRefTypeSpecifier->
					to< ContainerTypeSpecifier >().getContentsTypeSpecifier();
		}
	}

	if( arg.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(refTypeSpecifier,
				arg.to< BaseInstanceForm >().getTypeSpecifier()) );
	}

	else if( ExpressionTypeChecker::isCtor(arg) )
	{
		return( ExpressionTypeChecker::isCtor(
				refTypeSpecifier, arg.to< AvmCode >() ) );
	}

	else if( ExpressionTypeChecker::isNewfresh(arg) )
	{
		return( ExpressionTypeChecker::isNewfresh(
				refTypeSpecifier, arg.to< AvmCode >() ) );
	}

	switch( refTypeSpecifier.getTypeSpecifierKind() )
	{
		case TYPE_BOOLEAN_SPECIFIER:
		{
			return( ExpressionTypeChecker::isBoolean(arg) );
		}

		case TYPE_CHARACTER_SPECIFIER:
		{
			return( ExpressionTypeChecker::isCharacter(arg) );
		}

		case TYPE_STRING_SPECIFIER:
		{
			return( ExpressionTypeChecker::isString(arg) );
		}

		case TYPE_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_POS_INTEGER_SPECIFIER:
		{
			return( ExpressionTypeChecker::isInteger(arg) );
		}

		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_POS_RATIONAL_SPECIFIER:
		{
			return( ExpressionTypeChecker::isRational(arg) );
		}

		case TYPE_FLOAT_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_POS_FLOAT_SPECIFIER:
		{
			return( ExpressionTypeChecker::isFloat(arg) );
		}

		case TYPE_REAL_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
		case TYPE_POS_REAL_SPECIFIER:
		{
			return( ExpressionTypeChecker::isReal(arg) );
		}


		case TYPE_INTERVAL_SPECIFIER:
		{
			return( ExpressionTypeChecker::isTyped(
					refTypeSpecifier.to< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier(), arg) );
		}


		case TYPE_CLOCK_SPECIFIER:
		{
			return( ExpressionTypeChecker::isClock(
					refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
		}

		case TYPE_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isTime(
					refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
		}
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isContinuousTime(
					refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
		}
		case TYPE_DENSE_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isDenseTime(
					refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
		}
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isDiscreteTime(
					refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
		}


		case TYPE_MACHINE_SPECIFIER:
		{
			return( ExpressionTypeChecker::isMachine(refTypeSpecifier, arg) );
		}

		case TYPE_PORT_SPECIFIER:
		{
			return( ExpressionTypeChecker::isPort(refTypeSpecifier, arg) );
		}

		case TYPE_BUFFER_SPECIFIER:
		{
			return( ExpressionTypeChecker::isBuffer(refTypeSpecifier, arg) );
		}

		case TYPE_MESSAGE_SPECIFIER:
		{
			return( ExpressionTypeChecker::isMessage(refTypeSpecifier, arg) );
		}


		case TYPE_OPERATOR_SPECIFIER:
		{
			return( ExpressionTypeChecker::isOperator(arg) );
		}

		case TYPE_AVMCODE_SPECIFIER:
		{
			return( ExpressionTypeChecker::isAvmCode(arg) );
		}

		case TYPE_ENUM_SPECIFIER:
		{
			return( ExpressionTypeChecker::isEnum(
					refTypeSpecifier.to< EnumTypeSpecifier >(), arg) );
		}

		case TYPE_ARRAY_SPECIFIER:
		{
			return( ExpressionTypeChecker::isArray(
					refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
		}

		case TYPE_CLASS_SPECIFIER:
		{
			return( ExpressionTypeChecker::isClass(
					refTypeSpecifier.to< ClassTypeSpecifier >(), arg) );
		}

		case TYPE_UNIVERSAL_SPECIFIER:
		{
			return( true );
		}

		default:
		{
			if( refTypeSpecifier.hasTypeCollection() )
			{
				return( ExpressionTypeChecker::isCollection(
						refTypeSpecifier.to< ContainerTypeSpecifier >(), arg) );
			}

			else if( arg.is< AvmCode >() )
			{

			}

			return( false );
		}
	}

	return( true );
}


}
