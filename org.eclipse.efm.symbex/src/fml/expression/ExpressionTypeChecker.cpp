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
			&& anElement.to_ptr< InstanceOfMachine >()->
					getModifier().hasModifierPublicFinalStatic() )
	{
		return( true );
	}

	else if( anElement.is< BaseInstanceForm >()
			&& anElement.to_ptr< BaseInstanceForm >()->
					getModifier().hasModifierPublicFinalStatic() )
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
		ArrayBF * bfArray = arrayForm->to< ArrayBF >();
		for( avm_size_t idx = 0 ; idx < bfArray->size() ; ++idx )
		{
			if( not isFinalSymbolicSymbol( bfArray->at(idx) ) )
			{
				return( false );
			}
		}
	}

	return( false );
}


bool ExpressionTypeChecker::isMachine(const BF & anExpr)
{
	if( (anExpr.is< BaseInstanceForm >() &&
		anExpr.to_ptr< BaseInstanceForm >()->isTypedMachine()) ||
		anExpr.is< RuntimeID >() )
	{
		return( true );
	}
	else
	{
		return( StatementTypeChecker::isMachine( anExpr ) );
	}
}


bool ExpressionTypeChecker::isArray(
		ContainerTypeSpecifier * refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< ArrayBF >() )
	{
		ArrayBF * bArray = anExpr.to_ptr< ArrayBF >();
		for( avm_size_t idx = 1 ; idx < bArray->size() ; ++idx )
		{
			if( not isTyped(refTypeSpecifier->getContentsTypeSpecifier(),
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

		if( refTypeSpecifier == bArray->getTypeSpecifier() )
		{
			return( true );
		}
		else if( bArray->getTypeSpecifier()->isTypedArray() &&
				(refTypeSpecifier->getContentsTypeSpecifier() == bArray->
						getTypeSpecifier()->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier()) )
		{
			return( true );
		}
		else
		{
			AVM_OS_WARN << "ExpressionTypeChecker::isArray :> ref< @ "
					<< refTypeSpecifier << "->" << refTypeSpecifier->strT()
					<< " > =/=  dtype< @ "
					<< bArray->getTypeSpecifier()
					<< "-> " << bArray->getTypeSpecifier()->strT()
					<< " >" << std::endl;

//			bArray->getTypeSpecifier()->toStream(AVM_OS_WARN);
		}
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier->getContentsTypeSpecifier(),
				bArray->getTypeSpecifier()) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier->getContentsTypeSpecifier(),
				anExpr.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}

	else return( false );
}


bool ExpressionTypeChecker::isClass(
		ClassTypeSpecifier * refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< BuiltinArray >() )
	{
		BuiltinArray * bArray = anExpr.to_ptr< BuiltinArray >();

		if( refTypeSpecifier == bArray->getTypeSpecifier() )
		{
			return( true );
		}
		else if( refTypeSpecifier->size() != bArray->size() )
		{
			return( false );
		}
		else if( bArray->hasTypeSpecifier() &&
				anExpr.is_strictly< BuiltinArray >() &&
				bArray->getTypeSpecifier()->hasTypeContainer() )
		{
			BaseTypeSpecifier * eltTS = bArray->getTypeSpecifier()->
					as< ContainerTypeSpecifier >()->getContentsTypeSpecifier();

			TableOfSymbol::const_iterator it =
					refTypeSpecifier->getSymbolData().begin();
			TableOfSymbol::const_iterator endIt =
					refTypeSpecifier->getSymbolData().end();
			for( ; it != endIt ; ++it )
			{
				if( not ExpressionTypeChecker::isTyped(
						(*it).getTypeSpecifier(), eltTS) )
				{
					AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
							<< (*it).getTypeSpecifier()->strT()
							<< " > =/=  dtype< " << eltTS->strT() << " >"
							<< std::endl;

					return( false );
				}
			}
			return( true );
		}
		else if( bArray->is< ArrayBF >() )
		{
			ArrayBF * bfArray = bArray->to< ArrayBF >();

			TableOfSymbol::const_iterator it =
					refTypeSpecifier->getSymbolData().begin();
			TableOfSymbol::const_iterator endIt =
					refTypeSpecifier->getSymbolData().end();
			for( avm_size_t offset = 0; it != endIt ; ++it , ++offset )
			{
				if( not ExpressionTypeChecker::isTyped(
						(*it).getTypeSpecifier(), bfArray->at(offset)) )
				{
					AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
							<< (*it).getTypeSpecifier()->strT() << " > =/= arg<"
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
				anExpr.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}
	else if( anExpr.is< ArrayBF >() )
	{
		ArrayBF * bfArray = anExpr.to_ptr< ArrayBF >();

		if( refTypeSpecifier->getSymbolData().size() !=  bfArray->size() )
		{
			return( false );
		}

		TableOfSymbol::const_iterator it =
				refTypeSpecifier->getSymbolData().begin();
		TableOfSymbol::const_iterator endIt =
				refTypeSpecifier->getSymbolData().end();
		for( avm_size_t offset = 0; it != endIt ; ++it , ++offset )
		{
			if( not ExpressionTypeChecker::isTyped(
					(*it).getTypeSpecifier(), bfArray->get(offset)) )
			{
				AVM_OS_WARN << "ExpressionTypeChecker::isClass :> ref< "
						<< (*it).getTypeSpecifier()->strT()
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
		ContainerTypeSpecifier * refTypeSpecifier, const BF & anExpr)
{
	if(  anExpr.is< ArrayBF >() )
	{
		ArrayBF * bArray = anExpr.to_ptr< ArrayBF >();
		for( avm_size_t idx = 1 ; idx < bArray->size() ; ++idx )
		{
			if( not isTyped(refTypeSpecifier->getContentsTypeSpecifier(),
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
		for( avm_size_t idx = 1 ; idx < bArray->size() ; ++idx )
		{
			if( not isTyped(refTypeSpecifier->getContentsTypeSpecifier(),
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

		if( refTypeSpecifier == bArray->getTypeSpecifier() )
		{
			return( true );
		}
		else if( bArray->getTypeSpecifier()->isTypedArray() &&
				(refTypeSpecifier->getContentsTypeSpecifier() == bArray->
						getTypeSpecifier()->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier()) )
		{
			return( true );
		}
		else
		{
			AVM_OS_WARN << "ExpressionTypeChecker::isCollection :> ref< @ "
					<< refTypeSpecifier << "->" << refTypeSpecifier->strT()
					<< " > =/=  dtype< @ "
					<< bArray->getTypeSpecifier()
					<< "-> " << bArray->getTypeSpecifier()->strT()
					<< " >" << std::endl;

//			bArray->getTypeSpecifier()->toStream(AVM_OS_WARN);
		}
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier->getContentsTypeSpecifier(),
				bArray->getTypeSpecifier()) );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(
				refTypeSpecifier->getContentsTypeSpecifier(),
				anExpr.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isContainerOperation(aCode->getOperator()) )
		{
			return( ExpressionTypeChecker::isTyped(
					refTypeSpecifier, aCode->first()) );
		}
		if( OperatorManager::isContainerElementAccess(aCode->getOperator()) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						ExpressionTypeChecker::isTyped(refTypeSpecifier,
								bts->as< ContainerTypeSpecifier >()->
								getContentsTypeSpecifier()) );
			}
			else
			{
				return( false );
			}
		}

		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isVector(const BF & anExpr)
{
	if(  anExpr.is< BuiltinVector >() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->
				getTypeSpecifier()->hasTypeVector() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isContainerOperation(aCode->getOperator()) )
		{
			return( ExpressionTypeChecker::isVector( aCode->first() ) );
		}
		else if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr<
							BaseTypeSpecifier >()->hasTypeVector() );
		}

		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isEnum(
		EnumTypeSpecifier * refTypeSpecifier, const BF & anExpr)
{
	if( anExpr.is< InstanceOfData >() )
	{
		if( refTypeSpecifier == anExpr.to_ptr< InstanceOfData >()->getTypeSpecifier() )
		{
			return( true );
		}
		else
		{
			AVM_OS_WARN << "ExpressionTypeChecker::isEnum :> ref< @ "
					<< refTypeSpecifier->strT() << " > =/=  dtype< @ "
					<< anExpr.to_ptr< InstanceOfData >()->getTypeSpecifier()->strT()
					<< " >" << std::endl;

			return( false);
		}
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::isTyped(refTypeSpecifier,
				anExpr.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}

	else if( anExpr.isNumeric() )
	{
		return( refTypeSpecifier->hasSymbolDataWithValue(anExpr) );
	}

	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isContainerElementAccess(aCode->getOperator()) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						ExpressionTypeChecker::isTyped(refTypeSpecifier,
								bts->as< ContainerTypeSpecifier >()->
								getContentsTypeSpecifier()) );
			}
		}
	}

	return( false );
}



bool ExpressionTypeChecker::isEnum(const BF & anExpr)
{
	if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->isTypedEnum() );
	}

	else return( false );
}



bool ExpressionTypeChecker::isCharacter(const BF & anExpr)
{
	if( anExpr.isCharacter() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->isTypedCharacter() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( aCode->hasInstruction() && (aCode->getInstruction()->
				getMainProcessor() == AVM_ARG_CHARACTER_CPU) )
		{
			return( true );
		}

		else if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr< BaseTypeSpecifier >()->
							isTypedCharacter() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return( aCode->first().to_ptr< BaseInstanceForm >()
						->isTypedCharacter() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isCharacter(aCode->second()) );
			}
			return( false );
		}
		else if( OperatorManager::isCharacter( aCode->getOperator() ) )
		{
			for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
			{
				if( not ExpressionTypeChecker::isCharacter( *it ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().isTypedCharacter() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isString(const BF & anExpr)
{
	if( anExpr.isBuiltinString() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->isTypedString() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( aCode->hasInstruction() && (aCode->getInstruction()->
				getMainProcessor() == AVM_ARG_STRING_CPU) )
		{
			return( true );
		}

		else if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
				aCode->first().to_ptr< BaseTypeSpecifier >()->isTypedString() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return( aCode->first().to_ptr< BaseInstanceForm >()
						->isTypedString() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isString(aCode->second()) );
			}
			return( false );
		}
		else if( OperatorManager::isString( aCode->getOperator() ) )
		{
			for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
			{
				if( not ExpressionTypeChecker::isString( *it ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().isTypedString() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
}



bool ExpressionTypeChecker::isBoolean(const BF & anExpr, bool stronglyTypedFlag)
{
	if( anExpr.isBoolean() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->isTypedBoolean() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr< BaseTypeSpecifier >()->
							isTypedBoolean() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return(aCode->first().to_ptr< BaseInstanceForm >()
						->isTypedBoolean() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isBoolean(aCode->second(),
						stronglyTypedFlag) );
			}
			return( false );
		}
		else if( OperatorManager::isRelational( aCode->getOperator() ) )
		{
			return( true );
		}

		else if( OperatorManager::isPropositional( aCode->getOperator() ) )
		{
			if( stronglyTypedFlag )
			{
				for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
				{
					if( not ExpressionTypeChecker::isBoolean( *it ) )
					{
						return( false );
					}
				}
			}
			return( true );
		}

		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().isTypedBoolean() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isInteger(const BF & anExpr)
{
	if( anExpr.isWeakInteger() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->weaklyTypedInteger() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr< BaseTypeSpecifier >()->
							weaklyTypedInteger() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return( aCode->first().to_ptr< BaseInstanceForm >()
						->weaklyTypedInteger() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isInteger(aCode->second()) );
			}
			return( false );
		}
		else if( OperatorManager::isArithmetic( aCode->getOperator() ) )
		{
			for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
			{
				if( not ExpressionTypeChecker::isInteger( *it ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainInteger( aCode->getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().weaklyTypedInteger() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isRational(const BF & anExpr)
{
	if( anExpr.isWeakRational() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->weaklyTypedRational() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr< BaseTypeSpecifier >()->
							weaklyTypedRational() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return( aCode->first().to_ptr< BaseInstanceForm >()
						->weaklyTypedRational() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isRational(aCode->second()) );
			}
			return( false );
		}
		else if( OperatorManager::isArithmetic( aCode->getOperator() ) )
		{
			for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
			{
				if( not ExpressionTypeChecker::isRational( *it ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainRational( aCode->getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().weaklyTypedRational() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isFloat(const BF & anExpr)
{
	if( anExpr.isWeakFloat() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->weaklyTypedFloat() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr< BaseTypeSpecifier >()->
							weaklyTypedFloat() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return( aCode->first().to_ptr< BaseInstanceForm >()
						->weaklyTypedFloat() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isFloat(aCode->second()) );
			}
			return( false );
		}
		else if( OperatorManager::isArithmetic( aCode->getOperator() ) )
		{
			for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
			{
				if( not ExpressionTypeChecker::isFloat( *it ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainFloat( aCode->getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().weaklyTypedFloat() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
}


bool ExpressionTypeChecker::isReal(const BF & anExpr)
{
	if( anExpr.isWeakReal() )
	{
		return( true );
	}
	else if( anExpr.is< BaseInstanceForm >() )
	{
		return( anExpr.to_ptr< BaseInstanceForm >()->weaklyTypedReal() );
	}
	else if( anExpr.is< AvmCode >() )
	{
		AvmCode * aCode = anExpr.to_ptr< AvmCode >();

		if( OperatorManager::isCtor( aCode->getOperator() ) )
		{
			return( aCode->first().is< BaseTypeSpecifier >() &&
					aCode->first().to_ptr< BaseTypeSpecifier >()->
							weaklyTypedReal() );
		}
		else if( OperatorManager::isAssign( aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				return( aCode->first().to_ptr<
						BaseInstanceForm >()->weaklyTypedReal() );
			}
			else if( OperatorManager::isAssignBinary( aCode->getOperator() ) )
			{
				return( ExpressionTypeChecker::isReal(aCode->second()) );
			}
			return( false );
		}
		else if( OperatorManager::isArithmetic( aCode->getOperator() ) )
		{
			for(AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it)
			{
				if( not ExpressionTypeChecker::isReal( *it ) )
				{
					return( false );
				}
			}
			return( true );
		}
		else if( OperatorManager::isCodomainReal( aCode->getOperator() ) )
		{
			return( true );
		}
		else if( OperatorManager::isContainerElementAccess(
				aCode->getOperator() ) )
		{
			if( aCode->first().is< BaseInstanceForm >() )
			{
				BaseTypeSpecifier * bts = aCode->first().
						to_ptr< BaseInstanceForm >()->getTypeSpecifier();

				return( bts->hasTypeContainer() &&
						bts->as< ContainerTypeSpecifier >()->
						getContentsTypeSpecifier().weaklyTypedReal() );
			}
			else
			{
				return( false );
			}
		}
		else return( false );
	}

	else return( false );
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
				anExpr.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}

	else return( false );
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
				anExpr.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}

	else return( false );
}


bool ExpressionTypeChecker::isCtor(
		BaseTypeSpecifier * refTypeSpecifier, AvmCode * aCode)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
		OperatorManager::isCtor( aCode->getOperator() ) )
			<< "Unexpected ctor< ? >( ? ) expression :> "
			<< IGNORE_FIRST_TAB << aCode
			<< SEND_EXIT;

	return( aCode->first().is< BaseTypeSpecifier >() &&
			ExpressionTypeChecker::weaklyTyped(refTypeSpecifier,
					aCode->first().to_ptr< BaseTypeSpecifier >()) );
}


bool ExpressionTypeChecker::isNewfresh(
		BaseTypeSpecifier * refTypeSpecifier, AvmCode * aCode)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
		OperatorManager::isNewfresh( aCode->getOperator() ) )
			<< "Unexpected newfresh( ? ) expression :> "
			<< IGNORE_FIRST_TAB << aCode
			<< SEND_EXIT;

	return( aCode->first().is< BaseInstanceForm >() &&
			ExpressionTypeChecker::weaklyTyped(refTypeSpecifier,
				aCode->first().to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
}


bool ExpressionTypeChecker::isTyped(BaseTypeSpecifier * refTypeSpecifier,
		BaseTypeSpecifier * aTypeSpecifier)
{
	if( refTypeSpecifier == aTypeSpecifier )
	{
		return( true );
	}

	while( true )
	{
		if( refTypeSpecifier->is< TypeAliasSpecifier >() )
		{
			refTypeSpecifier = refTypeSpecifier->
					to< TypeAliasSpecifier >()->targetTypeSpecifier();
		}
		else if( refTypeSpecifier->is< IntervalTypeSpecifier >() )
		{
			refTypeSpecifier = refTypeSpecifier->
					to< IntervalTypeSpecifier >()->getSupportTypeSpecifier();
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
			aTypeSpecifier = aTypeSpecifier->
					to< TypeAliasSpecifier >()->targetTypeSpecifier();
		}
		else if( aTypeSpecifier->is< IntervalTypeSpecifier >() )
		{
			aTypeSpecifier = aTypeSpecifier->
					to< IntervalTypeSpecifier >()->getSupportTypeSpecifier();
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



bool ExpressionTypeChecker::isTyped(
		BaseTypeSpecifier * refTypeSpecifier, const BF & arg)
{
	while( true )
	{
		if( refTypeSpecifier->is< TypeAliasSpecifier >() )
		{
			refTypeSpecifier = refTypeSpecifier->
					to< TypeAliasSpecifier >()->targetTypeSpecifier();
		}
		else if( refTypeSpecifier->is< IntervalTypeSpecifier >() )
		{
			refTypeSpecifier = refTypeSpecifier->
					to< IntervalTypeSpecifier >()->getSupportTypeSpecifier();
		}
		else
		{
			break;
		}
	}

	if( refTypeSpecifier->hasTypedClockTime() )
	{
		if( refTypeSpecifier->is< ContainerTypeSpecifier >() )
		{
			refTypeSpecifier = refTypeSpecifier->
					to< ContainerTypeSpecifier >()->getContentsTypeSpecifier();
		}
	}

	if( arg.is< BaseInstanceForm >() )
	{
		return( ExpressionTypeChecker::weaklyTyped(refTypeSpecifier,
				arg.to_ptr< BaseInstanceForm >()->getTypeSpecifier()) );
	}

	else if( ExpressionTypeChecker::isCtor(arg) )
	{
		return( ExpressionTypeChecker::isCtor(
				refTypeSpecifier, arg.to_ptr< AvmCode >() ) );
	}

	else if( ExpressionTypeChecker::isNewfresh(arg) )
	{
		return( ExpressionTypeChecker::isNewfresh(
				refTypeSpecifier, arg.to_ptr< AvmCode >() ) );
	}

	switch( refTypeSpecifier->getTypeSpecifierKind() )
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
		{
			return( ExpressionTypeChecker::isRational(arg) );
		}

		case TYPE_FLOAT_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		{
			return( ExpressionTypeChecker::isFloat(arg) );
		}

		case TYPE_REAL_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
		{
			return( ExpressionTypeChecker::isReal(arg) );
		}


		case TYPE_INTERVAL_SPECIFIER:
		{
			return( ExpressionTypeChecker::isTyped( refTypeSpecifier->to<
					IntervalTypeSpecifier >()->getSupportTypeSpecifier(), arg) );
		}


		case TYPE_CLOCK_SPECIFIER:
		{
			return( ExpressionTypeChecker::isClock(arg) );
		}

		case TYPE_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isTime(arg) );
		}
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isCTime(arg) );
		}
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
			return( ExpressionTypeChecker::isDTime(arg) );
		}


		case TYPE_MACHINE_SPECIFIER:
		{
			return( ExpressionTypeChecker::isMachine(arg) );
		}

		case TYPE_PORT_SPECIFIER:
		{
			return( ExpressionTypeChecker::isPort(arg) );
		}

		case TYPE_BUFFER_SPECIFIER:
		{
			return( ExpressionTypeChecker::isBuffer(arg) );
		}

		case TYPE_MESSAGE_SPECIFIER:
		{
			return( ExpressionTypeChecker::isMessage(arg) );
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
					refTypeSpecifier->to< EnumTypeSpecifier >(), arg) );
		}

		case TYPE_ARRAY_SPECIFIER:
		{
			return( ExpressionTypeChecker::isArray(
					refTypeSpecifier->to< ContainerTypeSpecifier >(), arg) );
		}

		case TYPE_CLASS_SPECIFIER:
		{
			return( ExpressionTypeChecker::isClass(
					refTypeSpecifier->to< ClassTypeSpecifier >(), arg) );
		}

		case TYPE_UNIVERSAL_SPECIFIER:
		{
			return( true );
		}

		default:
		{
			if( refTypeSpecifier->hasTypeCollection() )
			{
				return( ExpressionTypeChecker::isCollection(
						refTypeSpecifier->to< ContainerTypeSpecifier >(), arg) );
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
