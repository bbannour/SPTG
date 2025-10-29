/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionConstructor.h"

#include <fml/executable/ExecutableLib.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/RuntimeLib.h>
#include <fml/runtime/RuntimeQuery.h>

#include <fml/type/EnumTypeSpecifier.h>

#include <fml/infrastructure/Machine.h>

#include <sew/Configuration.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// Decimal / UDecimal
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructor::newDecimal(const std::string & aValue, char sep)
{
	std::string::size_type pos = aValue.find(sep);
	if( pos != std::string::npos )
	{
		avm_integer_t aDecimalPart;
		if( sep::from_string< avm_integer_t >(
				aValue.substr(pos+1), aDecimalPart) )
		{
			if( aDecimalPart == 0 )
			{
				return( ExpressionConstructor::newInteger(
						aValue.substr(0, pos) ) );
			}
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "fail:> sep::from_string< integer_t>( "
					<< aValue.substr(pos+1) << ") !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}

		std::string strNumer = std::string(aValue).erase(pos, 1);

		std::string strDenom = OSS() <<
				( std::pow(10.0, aValue.size() - (pos + 1)) );

		return( ExpressionConstructor::newRational(strNumer, strDenom) );
	}
	else
	{
		return( ExpressionConstructor::newInteger(aValue) );
	}
}


BF ExpressionConstructor::newUDecimal(const std::string & aValue, char sep)
{
	std::string::size_type pos = aValue.find(sep);
	if( pos != std::string::npos )
	{
		avm_uinteger_t aDecimalPart;
		if( sep::from_string< avm_uinteger_t >(
				aValue.substr(pos+1), aDecimalPart) )
		{
			if( aDecimalPart == 0 )
			{
				return( ExpressionConstructor::newInteger(
						aValue.substr(0, pos) ) );
			}
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "fail:> sep::from_string< uinteger_t>( "
					<< aValue.substr(pos+1) << ") !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}

		std::string strNumer = std::string(aValue).erase(pos, 1);

		std::string strDenom = OSS() <<
				( std::pow(10.0, aValue.size() - (pos + 1)) );

		return( ExpressionConstructor::newRational(strNumer, strDenom) );
	}
	else
	{
		return( ExpressionConstructor::newInteger(aValue) );
	}
}


BF ExpressionConstructor::newQualifiedIdentifier(
		const Machine & machine, const std::string & aNameID)
{
	return( ExpressionConstructor::newQualifiedIdentifier(
			OSS() << machine.getFullyQualifiedNameID() << '.' << aNameID ) );
}

// new instance of Element Access FQN-ID :> machine<fqn>.element<name-id>
BF ExpressionConstructor::newQualifiedIdentifier(
		const Machine & machine, const ObjectElement & objElement)
{
	return( ExpressionConstructor::newQualifiedIdentifier(
			OSS() << machine.getFullyQualifiedNameID()
					<< '.' << objElement.getNameID() ) );
}


BF ExpressionConstructor::newQualifiedPositionalIdentifier(
		const Machine & machine, avm_offset_t aPositionOffset )
{
	return( BF(new QualifiedIdentifier(
			machine.getFullyQualifiedNameID(), aPositionOffset ) ) );
}


/**
 * SPECIFIC TYPED STRING VALUE as BUILTIN EXPRESSION
 */
BF ExpressionConstructor::newExpr(const Configuration & aConfiguration,
		const ITypeSpecifier & aTypeSpecifier, const std::string & aValue)
{
	if( aTypeSpecifier.isTypedBoolean() )
	{
		return( ExpressionConstructor::newBoolean(aValue) );
	}

	if( aTypeSpecifier.isTypedCharacter() )
	{
		return( ExpressionConstructor::newChar(aValue) );
	}
	if( aTypeSpecifier.isTypedString() )
	{
		return( ExpressionConstructor::newString(aValue) );
	}

	else if( aTypeSpecifier.weaklyTypedUInteger() )
	{
		return( ExpressionConstructor::newInteger(aValue) );
	}
	else if( aTypeSpecifier.weaklyTypedInteger() )
	{
		return( ExpressionConstructor::newInteger(aValue) );
	}

	else if( aTypeSpecifier.weaklyTypedURational() )
	{
		return( ExpressionConstructor::newRational(aValue) );
	}
	else if( aTypeSpecifier.weaklyTypedRational() )
	{
		return( ExpressionConstructor::newRational(aValue) );
	}

	else if( aTypeSpecifier.weaklyTypedFloat() )
	{
		return( ExpressionConstructor::newFloat(aValue) );
	}

	else if( aTypeSpecifier.weaklyTypedUReal() )
	{
		return( ExpressionConstructor::newUDecimal(aValue) );
	}
	else if( aTypeSpecifier.weaklyTypedReal() )
	{
		return( ExpressionConstructor::newDecimal(aValue) );
	}

	else if( aTypeSpecifier.isTypedMachine() )
	{
		return( ExpressionConstructor::
				newExprMachine(aConfiguration, aValue) );
	}

	else if( aTypeSpecifier.isTypedEnum() )
	{
		return( aTypeSpecifier.thisTypeSpecifier()
				.as< EnumTypeSpecifier >().getDataByNameID(aValue) );
	}

	return( BF::REF_NULL );
}


BF ExpressionConstructor::newExprMachine(
		const Configuration & aConfiguration, const std::string & aValue)
{
	ExecutableQuery XQuery( aConfiguration );

	const Symbol & foundMachine =
			XQuery.getMachineByQualifiedNameID(
					Specifier::DESIGN_INSTANCE_KIND, aValue);

	if( foundMachine.valid() )
	{
		return( foundMachine );
	}
	else if( aValue == ExecutableLib::MACHINE_ENVIRONMENT.getNameID() )
	{
		return( ExecutableLib::MACHINE_ENVIRONMENT );
	}
	else if( aValue == ExecutableLib::MACHINE_NULL.getNameID() )
	{
		return( ExecutableLib::MACHINE_NULL );
	}

	return( BF::REF_NULL );
}

BF ExpressionConstructor::newExprRuntime(
		const Configuration & aConfiguration, const std::string & aValue)
{
	RuntimeQuery RQuery( aConfiguration );

	const RuntimeID & foundRuntime = RQuery.getRuntimeByQualifiedNameID(aValue);

	if( foundRuntime.valid() )
	{
		return( foundRuntime );
	}
	else if( aValue == RuntimeLib::RID_ENVIRONMENT.getNameID() )
	{
		return( RuntimeLib::RID_ENVIRONMENT );
	}
	else if( aValue == RuntimeLib::RID_NIL.getNameID() )
	{
		return( RuntimeLib::RID_NIL );
	}

	return( RuntimeLib::RID_ENVIRONMENT );
}


/**
 * SPECIFIC AVMCODE EXPRESSION
 */

////////////////////////////////////////////////////////////////////////////////
// ADD < INCR | DECR > EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructor::addExpr(const BF & arg, avm_integer_t val)
{
	switch( arg.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			BF res = arg;
			res.makeWritable();
			res.to< Integer >().addExpr(val);

			return( res );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			BF res = arg;
			res.makeWritable();
			res.to< Rational >().addExpr(val);

			return( res );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			BF res = arg;
			res.makeWritable();
			res.to< Float >().addExpr(val);

			return( res );
		}

		default:
		{
			return( addExpr(arg, newUInteger(val)) );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// FOR ALL EXPRESSION IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructor::newExpr(const Operator * anOperator, const BF & arg)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_AND:
		case AVM_OPCODE_OR:
		case AVM_OPCODE_PLUS:
		case AVM_OPCODE_MULT:
		case AVM_OPCODE_POW:
		case AVM_OPCODE_DIV:
		{
			return( arg );
		}

		case AVM_OPCODE_NOT:
		{
			return( notExpr(arg) );
		}

		case AVM_OPCODE_UMINUS:
		{
			return( uminusExpr(arg) );
		}

		default:
		{
			return( newCode(anOperator, arg) );
		}
	}
}

BF ExpressionConstructor::newExpr(
		const Operator * anOperator, const BF & arg1, const BF & arg2)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_AND:
		{
			return( andExpr(arg1, arg2) );
		}
		case AVM_OPCODE_OR:
		{
			return( orExpr(arg1, arg2) );
		}

		case AVM_OPCODE_EXISTS:
		{
			return( existsExpr(arg1, arg2) );
		}
		case AVM_OPCODE_FORALL:
		{
			return( forallExpr(arg1, arg2) );
		}

		case AVM_OPCODE_EQ:
		{
			return( eqExpr(arg1, arg2) );
		}
		case AVM_OPCODE_NEQ:
		{
			return( neqExpr(arg1, arg2) );
		}

		case AVM_OPCODE_SEQ:
		{
			return( seqExpr(arg1, arg2) );
		}
		case AVM_OPCODE_NSEQ:
		{
			return( nseqExpr(arg1, arg2) );
		}

		case AVM_OPCODE_LT:
		{
			return( ltExpr(arg1, arg2) );
		}
		case AVM_OPCODE_LTE:
		{
			return( lteExpr(arg1, arg2) );
		}
		case AVM_OPCODE_GT:
		{
			return( gtExpr(arg1, arg2) );
		}
		case AVM_OPCODE_GTE:
		{
			return( gteExpr(arg1, arg2) );
		}

		case AVM_OPCODE_PLUS:
		{
			return( addExpr(arg1, arg2) );
		}
		case AVM_OPCODE_MINUS:
		{
			return( minusExpr(arg1, arg2) );
		}

		case AVM_OPCODE_MULT:
		{
			return( multExpr(arg1, arg2) );
		}
		case AVM_OPCODE_POW:
		{
			return( powExpr(arg1, arg2) );
		}

		case AVM_OPCODE_DIV:
		{
			return( divExpr(arg1, arg2) );
		}

		default:
		{
			return( newCode(anOperator, arg1, arg2) );
		}
	}
}


BF ExpressionConstructor::newExpr(const Operator * anOperator,
		const AvmCode::OperandCollectionT & operands)
{
	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_AND:
		{
			return( andExpr(operands) );
		}
		case AVM_OPCODE_OR:
		{
			return( orExpr(operands) );
		}

		case AVM_OPCODE_EXISTS:
		{
			return( existsExpr(operands) );
		}
		case AVM_OPCODE_FORALL:
		{
			return( forallExpr(operands) );
		}

		case AVM_OPCODE_PLUS:
		{
			return( addExpr(operands) );
		}
		case AVM_OPCODE_MULT:
		{
			return( multExpr(operands) );
		}

		default:
		{
			return( newCode(anOperator, operands) );
		}
	}
}


BF ExpressionConstructor::assignOpExpr(
		const Operator * anOperator, const BF & arg1, const BF & arg2)
{
	return( newCode(OperatorManager::OPERATOR_ASSIGN_OP, arg1,
			newCode(anOperator, arg2)) );
}



}
