/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 feb. 2018
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_EXPRESSION_EXPRESSIONMAPPER_H_
#define FML_EXPRESSION_EXPRESSIONMAPPER_H_

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/String.h>

#include <fml/expression/AvmCode.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Numeric.h>
#include <fml/numeric/Rational.h>

#include <fml/operator/Operator.h>

#include <util/avm_assert.h>

#include <string>
#include <strings.h>


namespace sep
{

template < class Expr_T >
class ExpressionMapper
{

public:
	/**
	 * PRIMITIVE EXPRESSION
	 */
	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW BOOLEAN VALUE
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newBoolean(bool aValue) = 0;

	inline Expr_T newBoolean(const char * aValue)
	{
		return( newBoolean( ::strcasecmp("true", aValue) == 0 ) );
	}

	inline Expr_T newBoolean(const std::string & aValue)
	{
		return( newBoolean( ::strcasecmp("true", aValue.c_str()) == 0 ) );
	}

	inline Expr_T newBoolean(Boolean & aValue)
	{
		return( newBoolean( aValue.getValue() ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW INTEGER VALUE
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newInteger(Integer & aValue) = 0;

	virtual Expr_T newInteger(avm_integer_t aValue) = 0;

	virtual Expr_T newUInteger(avm_uinteger_t aValue) = 0;

	virtual Expr_T newUInteger(
			avm_uinteger_t aValue, avm_uinteger_t anExponent) = 0;

	virtual Expr_T newInteger(const std::string & aValue) = 0;

#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

	virtual Expr_T newInteger(const Integer::RawValueType & aValue) = 0;

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */

#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

	virtual Expr_T newInteger(const mpz_t & aValue) = 0;

	virtual Expr_T newInteger(const Integer::RawValueType & aValue) = 0;

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW RATIONAL VALUE
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newRational(Rational & aValue) = 0;

	virtual Expr_T newRational(avm_integer_t aNumer) = 0;

	virtual Expr_T newURational(avm_uinteger_t aNumer) = 0;

	virtual Expr_T newRational(avm_integer_t aNumer, avm_integer_t aDenom) = 0;

	virtual Expr_T newRational(avm_integer_t aNumer, avm_uinteger_t aDenom) = 0;

	virtual Expr_T newURational(avm_uinteger_t aNumer, avm_uinteger_t aDenom) = 0;

	virtual Expr_T newRational(const std::string & aValue) = 0;

	virtual Expr_T newRational(
			const std::string & strNumer, const std::string & strDenom) = 0;


#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

	virtual Expr_T newRational(
			const Integer::RawValueType & aNumer,
			const Integer::RawValueType & aDenom) = 0;

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

	virtual Expr_T newRational(const mpz_t & aNumer, const mpz_t & aDenom) = 0;

	virtual Expr_T newRational(
			const Integer::RawValueType & aNumer,
			const Integer::RawValueType & aDenom) = 0;


	virtual Expr_T newRational(const mpq_t & aValue) = 0;

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */

	virtual Expr_T newRational(const Rational::RawValueType & aValue) = 0;


	////////////////////////////////////////////////////////////////////////////
	// Decimal / UDecimal
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newDecimal(const std::string & aValue, char sep = '.');

	virtual Expr_T newUDecimal(const std::string & aValue, char sep = '.');


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW FLOAT VALUE
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newFloat(Float & aValue) = 0;

	virtual Expr_T newFloat(avm_integer_t aValue) = 0;

	virtual Expr_T newUFloat(avm_uinteger_t aValue) = 0;

	virtual Expr_T newFloat(avm_float_t aValue) = 0;

	virtual Expr_T newFloat(const std::string & aValue) = 0;


#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

	virtual Expr_T newFloat(const Rational::RawValueType & aValue) = 0;

	virtual Expr_T newFloat(const Float::RawValueType & aValue) = 0;

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

	virtual Expr_T newFloat(const mpq_t & aValue) = 0;

	virtual Expr_T newFloat(const Rational::RawValueType & aValue) = 0;

	virtual Expr_T newFloat(const mpf_t & aValue) = 0;

	virtual Expr_T newFloat(const Float::RawValueType & aValue) = 0;

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW NUMERIC VALUE
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newNumeric(const Numeric & aNumeric) = 0;

	////////////////////////////////////////////////////////////////////////////
	// Char / String / Identifier / QualifiedIdentifier
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newChar(Character & aValue) = 0;

	virtual Expr_T newChar(char aValue = ' ') = 0;

	virtual Expr_T newChar(const std::string & aValue) = 0;

	virtual Expr_T newString(const std::string & aValue = "",
			char aQuote = String::DEFAULT_DELIMITER) = 0;


	/**
	 * SPECIFIC NUMERIC EXPRESSION
	 */
	virtual Expr_T newExpr(bool aValue) = 0;

	virtual Expr_T newExpr(avm_integer_t aValue) = 0;


	virtual Expr_T newExpr(avm_integer_t  aNumer, avm_integer_t  aDenom) = 0;

	virtual Expr_T newExpr(avm_integer_t aNumer, avm_uinteger_t aDenom) = 0;

	virtual Expr_T newExpr(avm_uinteger_t aNumer, avm_uinteger_t aDenom) = 0;

	virtual Expr_T newExpr(const Integer & aNumer, const Integer & aDenom) = 0;


	virtual Expr_T newExpr(float aValue) = 0;

	virtual Expr_T newExpr(double aValue) = 0;


	/**
	 * SPECIFIC STRING VALUE as BUILTIN EXPRESSION
	 */
	virtual Expr_T newExprBoolean(const std::string & aValue) = 0;

	virtual Expr_T newExprBoolean(const char * aValue) = 0;


	virtual Expr_T newExprInteger(const std::string & aValue) = 0;

	virtual Expr_T newExprInteger(const char * aValue) = 0;


	virtual Expr_T newExprRational(const std::string & aValue) = 0;

	virtual Expr_T newExprRational(const char * aValue) = 0;


	virtual Expr_T newExprFloat(const std::string & aValue) = 0;

	virtual Expr_T newExprFloat(const char * aValue) = 0;


	virtual Expr_T newExprNumber(const std::string & aValue) = 0;

	virtual Expr_T newExprNumber(const char * aValue) = 0;

	/**
	 * SPECIFIC AVMCODE EXPRESSION
	 */
	virtual Expr_T newExpr(const BF & anElement) = 0;


	////////////////////////////////////////////////////////////////////////////
	// QUANTIFIER EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T existsExpr(const BF & boundVar, const BF & formula) = 0;

	virtual Expr_T existsExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T existsExpr(const AvmCode & aCode) = 0;


	virtual Expr_T forallExpr(const BF & boundVar, const BF & formula) = 0;

	virtual Expr_T forallExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T forallExpr(const AvmCode & aCode) = 0;


	////////////////////////////////////////////////////////////////////////////
	// AND EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T andExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T andExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T andExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// OR EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T orExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T orExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T orExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// NOT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T notExpr(const BF & arg) = 0;

	virtual Expr_T notExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T notExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// [ NOT ] EQUAL EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T eqExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T eqExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T eqExpr(const AvmCode & aCode) = 0;


	virtual Expr_T neqExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T neqExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T neqExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// [ NOT ] SYNTAXIC EQUAL EXPRESSION
	// FOR ALL EXPRESSION IMPLEMENTATION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T seqExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T seqExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T seqExpr(const AvmCode & aCode) = 0;


	virtual Expr_T nseqExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T nseqExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T nseqExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// COMPARE EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T gtExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T gtExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T gtExpr(const AvmCode & aCode) = 0;


	virtual Expr_T gteExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T gteExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T gteExpr(const AvmCode & aCode) = 0;


	virtual Expr_T ltExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T ltExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T ltExpr(const AvmCode & aCode) = 0;


	virtual Expr_T lteExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T lteExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T lteExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// ADD EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T addExpr(const BF & arg, avm_integer_t val);

	virtual Expr_T addExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T addExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T addExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// UMINUS EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T uminusExpr(const BF & arg) = 0;

	virtual Expr_T uminusExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T uminusExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// MINUS EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T minusExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T minusExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T minusExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// MULT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T multExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T multExpr(const AvmCode::OperandCollectionT & operands) = 0;

	virtual Expr_T multExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// POW EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T powExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T powExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// DIV EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T divExpr(const BF & arg0, const BF & arg1) = 0;

	virtual Expr_T divExpr(const AvmCode & aCode) = 0;

	////////////////////////////////////////////////////////////////////////////
	// FOR ALL EXPRESSION IMPLEMENTATION
	////////////////////////////////////////////////////////////////////////////

	virtual Expr_T newExpr(const Operator * anOperator, const BF & arg) = 0;

	virtual Expr_T newExpr(const Operator * anOperator,
			const BF & arg1, const BF & arg2)
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
				AVM_OS_FATAL_ERROR_EXIT
						<< "ExpressionWrapper: Unsupported operator in newExpr( "
						<< anOperator->strOp() << " , " << arg1.str()
						<< " , " << arg2.str() <<  " ) !!!" << std::endl
						<< SEND_EXIT;

				return( addExpr(anOperator, arg1, arg2) );
			}
		}
	}

	virtual Expr_T newExpr(const Operator * anOperator,
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

			case AVM_OPCODE_EQ:
			{
				return( eqExpr(operands) );
			}
			case AVM_OPCODE_NEQ:
			{
				return( neqExpr(operands) );
			}

			case AVM_OPCODE_SEQ:
			{
				return( seqExpr(operands) );
			}
			case AVM_OPCODE_NSEQ:
			{
				return( nseqExpr(operands) );
			}

			case AVM_OPCODE_LT:
			{
				return( ltExpr(operands) );
			}
			case AVM_OPCODE_LTE:
			{
				return( lteExpr(operands) );
			}
			case AVM_OPCODE_GT:
			{
				return( gtExpr(operands) );
			}
			case AVM_OPCODE_GTE:
			{
				return( gteExpr(operands) );
			}

			case AVM_OPCODE_PLUS:
			{
				return( addExpr(operands) );
			}
			case AVM_OPCODE_MINUS:
			{
				return( minusExpr(operands) );
			}

			case AVM_OPCODE_MULT:
			{
				return( multExpr(operands) );
			}
			case AVM_OPCODE_POW:
			{
				return( powExpr(operands) );
			}

			case AVM_OPCODE_DIV:
			{
				return( divExpr(operands) );
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "ExpressionWrapper: Unsupported operator in newExpr( "
						<< anOperator->strOp() << " , " << operands <<  " ) !!!"
						<< std::endl
						<< SEND_EXIT;

				return( addExpr(operands) );
			}
		}
	}

	virtual Expr_T newExpr(const AvmCode & aCode) = 0;

};


} /* namespace sep */

#endif /* FML_EXPRESSION_EXPRESSIONMAPPER_H_ */
