/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionFactory.h"

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/String.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>

#include <fml/lib/AvmOperationFactory.h>


namespace sep
{


/**
 * LOADER
 */
void ExpressionFactory::load()
{
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// SPECIFIC EDEN IMPLEMENTATION  or NOT
	////////////////////////////////////////////////////////////////////////////

	ExpressionConstant::load();

	String::load();

	OperatorManager::load();

	AvmOperationFactory::load();
}


/**
 * DISPOSER
 */
void ExpressionFactory::dispose()
{
	AvmOperationFactory::dispose();

	OperatorManager::dispose();

	String::dispose();

	ExpressionConstant::dispose();
}


/**
 * CONFIGURE
 */
bool ExpressionFactory::configure()
{
	return( true );
}



/**
 * COMPARISON
 * with TRUE & FALSE
 */

bool ExpressionFactory::isBoolean(const BF & value)
{
	switch( value.classKind() )
	{
		//case CLASS_KIND_T( Boolean ):
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

bool ExpressionFactory::toBoolean(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( value.to< Boolean >().getValue() );
		}

		default:
		{
			return( false );
		}
	}
}


bool ExpressionFactory::isEqualFalse(const BF & value)
{
	switch ( value.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( value.to< Boolean >().getValue() == false );
		}

		default :
		{
			return( false );
		}
	}
}

bool ExpressionFactory::isNotEqualFalse(const BF & value)
{
	switch ( value.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( value.to< Boolean >().getValue() != false );
		}

		default :
		{
			return( true );
		}
	}
}


bool ExpressionFactory::isEqualTrue(const BF & value)
{
	switch ( value.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( value.to< Boolean >().getValue() == true );
		}

		default :
		{
			return( false );
		}
	}
}

bool ExpressionFactory::isNotEqualTrue(const BF & value)
{
	switch ( value.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( value.to< Boolean >().getValue() != true );
		}

		default :
		{
			return( true );
		}
	}
}





/**
 * GETTER
 * for simple or numeric kind
 */

bool ExpressionFactory::isNumber(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}


bool ExpressionFactory::isInt32(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().isInt32() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().isInt32() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().isInt32() );
		}

		default:
		{
			return( false );
		}
	}
}

std::int32_t ExpressionFactory::toInt32(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toInt32() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toInt32() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toInt32() );
		}

		default:
		{
			return( 0 );
		}
	}
}


bool ExpressionFactory::isInt64(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().isInt64() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().isInt64() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().isInt64() );
		}

		default:
		{
			return( false );
		}
	}
}

std::int64_t ExpressionFactory::toInt64(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toInt64() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toInt64() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toInt64() );
		}

		default:
		{
			return( 0 );
		}
	}
}


bool ExpressionFactory::isInteger(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( true );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().isInteger() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().isInteger() );
		}

		default:
		{
			return( false );
		}
	}
}

avm_integer_t ExpressionFactory::toInteger(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toInteger() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toInteger() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toInteger() );
		}

		default:
		{
			return( 0 );
		}
	}
}


bool ExpressionFactory::isPosInteger(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().isPosInteger() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().isPosInteger() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().isPosInteger() );
		}

		default:
		{
			return( false );
		}
	}
}


bool ExpressionFactory::isUInteger(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().isUInteger() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().isUInteger() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().isUInteger() );
		}

		default:
		{
			return( false );
		}
	}
}

avm_uinteger_t ExpressionFactory::toUInteger(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toUInteger() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toUInteger() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toUInteger() );
		}

		default:
		{
			return( 0 );
		}
	}
}





bool ExpressionFactory::isRational(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( true );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().isRational() );
		}

		default:
		{
			return( false );
		}
	}
}

avm_integer_t ExpressionFactory::toDenominator(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toDenominator() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toDenominator() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toDenominator() );
		}

		default:
		{
			return( 0 );
		}
	}
}
avm_integer_t ExpressionFactory::toNumerator(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toNumerator() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toNumerator() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toNumerator() );
		}

		default:
		{
			return( 0 );
		}
	}
}


bool ExpressionFactory::isFloat(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

avm_float_t ExpressionFactory::toFloat(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toFloat() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toFloat() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toFloat() );
		}

		default:
		{
			return( 0 );
		}
	}
}


bool ExpressionFactory::isReal(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

avm_real_t ExpressionFactory::toReal(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( value.to< Integer >().toReal() );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( value.to< Rational >().toReal() );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( value.to< Float >().toReal() );
		}

		default:
		{
			return( 0 );
		}
	}
}



bool ExpressionFactory::isCharacter(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_CHARACTER_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

char ExpressionFactory::toCharacter(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_CHARACTER_KIND:
		{
			return( value.to< Character >().getValue() );
		}

		default:
		{
			return( 0 );
		}
	}
}



bool ExpressionFactory::isIdentifier(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}

	return( false );
}

std::string ExpressionFactory::toIdentifier(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			return( value.to< Identifier >().getValue() );
		}

		default:
		{
			return( "" );
		}
	}
}


bool ExpressionFactory::isUfi(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

std::string ExpressionFactory::toUfi(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( value.to< QualifiedIdentifier >().getValue() );
		}

		default:
		{
			return( "" );
		}
	}
}


bool ExpressionFactory::isUfid(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}

std::string ExpressionFactory::toUfid(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			return( value.to< Identifier >().getValue() );
		}
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( value.to< QualifiedIdentifier >().getValue() );
		}

		default:
		{
			return( "" );
		}
	}
}


bool ExpressionFactory::isEnumSymbol(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_INSTANCE_DATA_KIND:
		{
			return( value.to< InstanceOfData >().isEnumSymbolPointer() );
		}

		default:
		{
			return( false );
		}
	}

	return( false );
}

std::string ExpressionFactory::strEnumSymbol(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_INSTANCE_DATA_KIND:
		{
			return( value.to< InstanceOfData >().getFullyQualifiedNameID() );
		}

		default:
		{
			return( "" );
		}
	}
}


bool ExpressionFactory::isBuiltinString(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_STRING_KIND:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}

	return( false );
}

std::string ExpressionFactory::toBuiltinString(const BF & value)
{
	switch( value.classKind() )
	{
		case FORM_BUILTIN_STRING_KIND:
		{
			return( value.to< String >().getValue() );
		}

		default:
		{
			return( "" );
		}
	}
}



bool ExpressionFactory::isBuiltinValue(const BF & value)
{
	switch( value.classKind() )
	{
		default:
		{
			return( value.is< BuiltinForm >() );
		}
	}
}



bool ExpressionFactory::isConstValue(const BF & value)
{
	switch( value.classKind() )
	{
		// BUILTIN VALUE
		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:

		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_STRING_KIND:

		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:

			// BUILTIN OPERATOR
		case FORM_OPERATOR_KIND:

		// BUILTIN ARRAY
		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:

		{
			return( true );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			return( value.to< InstanceOfData >().isEnumSymbolPointer() );
		}

		default:
		{
			return( false );
		}
	}
}


/**
 * COLLECT VARIABLE
 * Using Variable::Table
 * For only Variable typed var
 */
void ExpressionFactory::collectSpecVariable(const BF & anExpr, Variable::Table & listOfVar)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			collectSpecVariable(anExpr.bfCode(), listOfVar);

			break;
		}

		case FORM_XFSP_VARIABLE_KIND:
		{
			listOfVar.add_unique( anExpr );

			break;
		}

		default:
		{
			break;
		}
	}
}


/**
 * COLLECT VARIABLE
 * Using InstanceOfData::Table
 * For only InstanceOfData typed var
 */
void ExpressionFactory::collectVariable(
		const BF & anExpr, InstanceOfData::Table & listOfElement)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			collectVariable(anExpr.bfCode(), listOfElement);

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			listOfElement.add_unique( anExpr );

			break;
		}

		default:
		{
			break;
		}
	}
}


/**
 * COLLECT ANY VARIABLE
 * Using BFCollection
 * For Variable or InstanceOfData typed var
 */
void ExpressionFactory::collectAnyVariable(
		const BF & anExpr, BFCollection & listOfVar)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			collectAnyVariable(anExpr.bfCode(), listOfVar);

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		case FORM_XFSP_VARIABLE_KIND:
		{
			listOfVar.add_unique( anExpr );

			break;
		}

		default:
		{
			break;
		}
	}
}


void ExpressionFactory::collectAnyVariable(
		const BFCode & aCode, BFCollection & listOfVar)
{
	for( const auto & itOperand : aCode.getOperands() )
	{
		collectAnyVariable(itOperand, listOfVar);
	}
}



/**
 * COLLECT FREE VARIABLE
 * Using BFCollection
 * For InstanceOfData typed var
 */
void ExpressionFactory::collectsFreeVariable(const BF & anExpr,
		InstanceOfData::Table & listOfBoundVar, InstanceOfData::Table & listOfVar)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			collectsFreeVariable(anExpr.bfCode(), listOfBoundVar, listOfVar);

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			if( not listOfBoundVar.contains(anExpr) )
			{
				listOfVar.add_unique( anExpr );
			}

			break;
		}

		default:
		{
			break;
		}
	}
}

void ExpressionFactory::collectsFreeVariable(const BFCode & aCode,
		InstanceOfData::Table & listOfBoundVar, InstanceOfData::Table & listOfVar)
{
	switch( aCode.getAvmOpCode() )
	{
		case AVM_OPCODE_EXISTS:
		case AVM_OPCODE_FORALL:
		{
			BFList boundVars;
			boundVars.append( aCode.getOperands() );
			boundVars.pop_last();
			listOfBoundVar.append(boundVars);

			collectsFreeVariable(aCode->last(), listOfBoundVar, listOfVar);

			listOfBoundVar.remove(boundVars);
			break;
		}
		default:
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				collectsFreeVariable(itOperand, listOfBoundVar, listOfVar);
			}
			break;
		}
	}
}

/**
 * UTILS
 * For only InstanceOfData typed var
 */
bool ExpressionFactory::containsVariable(
		const BF & anExpr, InstanceOfData * aVariable)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( containsVariable(anExpr.bfCode() , aVariable) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			if( anExpr.to_ptr< InstanceOfData >() == aVariable )
			{
				return( true );
			}

			return( false );
		}

		default:
		{
			return( false );
		}
	}
}

bool ExpressionFactory::containsVariable(
		const BFCode & aCode, InstanceOfData * aVariable)
{

	for( const auto & itOperand : aCode.getOperands() )
	{
		if( containsVariable(itOperand, aVariable) )
		{
			return( true );
		}
	}

	return( false );
}


bool ExpressionFactory::containsVariable(
		const BF & anExpr, BFCollection & listOfVar)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( containsVariable(anExpr.bfCode() , listOfVar) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			if( listOfVar.contains( anExpr ) )
			{
				return( true );
			}

			return( false );
		}

		default:
		{
			return( false );
		}
	}
}


bool ExpressionFactory::containsVariable(
		const BFCode & aCode, BFCollection & listOfVar)
{
	for( const auto & itOperand : aCode.getOperands() )
	{
		if( containsVariable(itOperand, listOfVar) )
		{
			return( true );
		}
	}

	return( false );
}


/**
 * COLLECT CLAUSE
 */
void ExpressionFactory::collectsClause(
		const BF & anExpr, BFCollection & listOfClause)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			collectsClause(anExpr.bfCode() , listOfClause);

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			listOfClause.append( anExpr );

			break;
		}

		default:
		{
			break;
		}
	}
}

void ExpressionFactory::collectsClause(
		const BFCode & aCode, BFCollection & listOfClause)
{
	if( aCode->isOpCode( AVM_OPCODE_AND ) )
	{
		for( const auto & itOperand : aCode.getOperands() )
		{
			listOfClause.append( itOperand );
		}
	}
	else
	{
		listOfClause.append( aCode );
	}
}


void ExpressionFactory::collectsClause(
		const BF & anExpr, BFCollection & listOfBoundVar,
		BFCollection & listOfBoundClause, BFCollection & listOfFreeClause)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			collectsClause( anExpr.bfCode() , listOfBoundVar,
					listOfBoundClause, listOfFreeClause );

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			if( ExpressionFactory::containsVariable(anExpr, listOfBoundVar) )
			{
				listOfBoundClause.append( anExpr );
			}
			else
			{
				listOfFreeClause.append( anExpr );
			}

			break;
		}

		default:
		{
			break;
		}
	}
}


void ExpressionFactory::collectsClause(
		const BFCode & aCode, BFCollection & listOfBoundVar,
		BFCollection & listOfBoundClause, BFCollection & listOfFreeClause)
{
	if( aCode->isOpCode( AVM_OPCODE_AND ) )
	{
		for( const auto & itOperand : aCode.getOperands() )
		{
			if( containsVariable(itOperand, listOfBoundVar) )
			{
				listOfBoundClause.append( itOperand );
			}
			else
			{
				listOfFreeClause.append( itOperand );
			}
		}
	}
	else
	{
		if( ExpressionFactory::containsVariable(aCode, listOfBoundVar) )
		{
			listOfBoundClause.append( aCode );
		}
		else
		{
			listOfFreeClause.append( aCode );
		}
	}
}


void ExpressionFactory::deduceTrivialAssignmentsFromConjonction(
		const BF & anExpr, BFCodeCollection & listOfAssignments)
{
	switch( anExpr.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const BFCode & aCode = anExpr.bfCode();

			if( aCode->isOpCode( AVM_OPCODE_AND ) )
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					deduceTrivialAssignmentsFromConjonction(
							itOperand, listOfAssignments);
				}
			}
			else if( aCode->hasOpCode( AVM_OPCODE_EQ, AVM_OPCODE_SEQ ) )
			{
				if( aCode->first().is< InstanceOfData >()
					&& aCode->first().to< InstanceOfData >().
							getModifier().noneModifierFinalReferenceMacro()
					&& ExpressionTypeChecker::
							isFinalSymbolicBasicSymbol(aCode->second()) )
				{
					listOfAssignments.append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_ASSIGN,
							aCode->first(), aCode->second()) );
				}
				else if( aCode->second().is< InstanceOfData >()
						&& aCode->second().to<InstanceOfData >().
								getModifier().noneModifierFinalReferenceMacro()
						&& ExpressionTypeChecker::
								isFinalSymbolicBasicSymbol(aCode->first()) )
				{
					listOfAssignments.append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_ASSIGN,
							aCode->second(), aCode->first()) );
				}
			}
			else if( aCode->isOpCode( AVM_OPCODE_NOT ) )
			{
				if( aCode->first().is< InstanceOfData >()
					&& aCode->first().to< InstanceOfData >().
							getModifier().noneModifierFinalReferenceMacro()
					&& aCode->first().to< InstanceOfData >().isTypedBoolean() )
				{
					listOfAssignments.append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_ASSIGN,
							aCode->first(), ExpressionConstant::BOOLEAN_FALSE) );
				}
			}

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			if( anExpr.to< InstanceOfData >().
					getModifier().noneModifierFinalReferenceMacro()
				&& anExpr.to< InstanceOfData >().isTypedBoolean() )
			{
				listOfAssignments.append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_ASSIGN,
						anExpr, ExpressionConstant::BOOLEAN_TRUE) );
			}

			break;
		}

		default:
		{
			break;
		}
	}
}



}

