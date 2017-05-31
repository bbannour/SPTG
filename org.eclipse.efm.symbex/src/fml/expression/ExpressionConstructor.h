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

#ifndef EXPRESSIONCONSTRUCTOR_H_
#define EXPRESSIONCONSTRUCTOR_H_

#include <fml/expression/AvmCodeFactory.h>

#include <common/BF.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/String.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>

#include <fml/numeric/Numeric.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructorImpl.h>

#include <fml/lib/ITypeSpecifier.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <fml/workflow/UniFormIdentifier.h>

#include <cmath>



namespace sep
{

class Configuration;
class ObjectElement;
class Machine;


class ExpressionConstructor  :   public AvmCodeFactory
{


////////////////////////////////////////////////////////////////////////////////
// DEFAULT EXPRESSION CONSTRUCTOR IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////
#if( true )

	#define DEFAULT_EXPRESSION_IMPL  EXPRESSION::NATIVE_IMPL

#endif


public:

	/**
	 * PRIMITIVE EXPRESSION
	 */
	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW BOOLEAN VALUE
	////////////////////////////////////////////////////////////////////////////

	inline static const BF & newBoolean(bool aValue = false)
	{
		return( ( aValue )
				? ExpressionConstant::BOOLEAN_TRUE
				: ExpressionConstant::BOOLEAN_FALSE );
	}

	inline static BF newBoolean(const char * aValue)
	{
		return( ( ::strcasecmp("true", aValue) == 0 )
				? ExpressionConstant::BOOLEAN_TRUE
				: ExpressionConstant::BOOLEAN_FALSE );
	}

	inline static BF newBoolean(const std::string & aValue)
	{
		return( ( ::strcasecmp("true", aValue.c_str()) ==  0)
				? ExpressionConstant::BOOLEAN_TRUE
				: ExpressionConstant::BOOLEAN_FALSE );
	}


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW INTEGER VALUE
	////////////////////////////////////////////////////////////////////////////

	inline static BF newInteger(Integer * aValue)
	{
		return( BF( aValue ) );
	}

	inline static BF newInteger(avm_integer_t aValue)
	{
		switch( aValue )
		{
			case  0: return( ExpressionConstant::INTEGER_ZERO );

			case  1: return( ExpressionConstant::INTEGER_ONE );
			case  2: return( ExpressionConstant::INTEGER_TWO );

			case -1: return( ExpressionConstant::INTEGER_MINUS_ONE );
			case -2: return( ExpressionConstant::INTEGER_MINUS_TWO );

			default: return( BF( new Integer(aValue) ) );
		}
	}

	inline static BF newUInteger(avm_uinteger_t aValue)
	{
		switch( aValue )
		{
			case  0: return( ExpressionConstant::INTEGER_ZERO );

			case  1: return( ExpressionConstant::INTEGER_ONE );
			case  2: return( ExpressionConstant::INTEGER_TWO );

			default: return( BF( new Integer(aValue) ) );
		}
	}

	inline static BF newInteger(const std::string & aValue)
	{
		return( BF( new Integer(aValue) ) );
	}


#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

	inline static BF newInteger(const Integer::RawValueType & aValue)
	{
		return( BF( new Integer(aValue) ) );
	}

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

	inline static BF newInteger(const mpz_t & aValue)
	{
		return( BF( new Integer(aValue) ) );
	}

	inline static BF newInteger(const Integer::RawValueType & aValue)
	{
		return( BF( new Integer(aValue) ) );
	}

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW RATIONAL VALUE
	////////////////////////////////////////////////////////////////////////////

	inline static BF newRational(Rational * aValue)
	{
		return( BF( aValue ) );
	}

	inline static BF newRational(avm_integer_t aNumer)
	{
		return( BF( new Rational(aNumer) ) );
	}

	inline static BF newURational(avm_uinteger_t aNumer)
	{
		return( BF( new Rational(aNumer) ) );
	}

	inline static BF newRational(avm_integer_t aNumer, avm_integer_t aDenom)
	{
		if( aDenom != 0 )
		{
			return( (aNumer == 0) ? ExpressionConstant::INTEGER_ZERO :
					BF( new Rational(aNumer, aDenom) ) );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "fail:> newRational< "
					<< aNumer << " / " << aDenom << " > !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}

	inline static BF newRational(avm_integer_t aNumer, avm_uinteger_t aDenom)
	{
		if( aDenom != 0 )
		{
			return( (aNumer == 0) ? ExpressionConstant::INTEGER_ZERO :
					BF( new Rational(aNumer, aDenom) ) );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "fail:> newRational< "
					<< aNumer << " / " << aDenom << " > !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}

	inline static BF newURational(avm_uinteger_t aNumer, avm_uinteger_t aDenom)
	{
		if( aDenom != 0 )
		{
			return( (aNumer == 0) ? ExpressionConstant::INTEGER_ZERO :
					BF( new Rational(aNumer, aDenom) ) );
		}
		else
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "fail:> newRational< "
					<< aNumer << " / " << aDenom << " > !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
	}

	inline static BF newRational(const std::string & aValue)
	{
		return( BF( new Rational(aValue) ) );
	}

	inline static BF newRational(
			const std::string & strNumer, const std::string & strDenom)
	{
		return( BF( new Rational(strNumer, strDenom) ) );
	}


#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

	inline static BF newRational(
			const Integer::RawValueType & aNumer,
			const Integer::RawValueType & aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

	inline static BF newRational(const mpz_t & aNumer, const mpz_t & aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newRational(
			const Integer::RawValueType & aNumer,
			const Integer::RawValueType & aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}


	inline static BF newRational(const mpq_t & aValue)
	{
		return( BF( new Rational( aValue ) ) );
	}

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */

	inline static BF newRational(const Rational::RawValueType & aValue)
	{
		return( BF( new Rational(aValue) ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// Decimal / UDecimal
	////////////////////////////////////////////////////////////////////////////

	static BF newDecimal(const std::string & aValue, char sep = '.');

	static BF newUDecimal(const std::string & aValue, char sep = '.');


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW FLOAT VALUE
	////////////////////////////////////////////////////////////////////////////

	inline static BF newFloat(Float * aValue)
	{
		return( BF( aValue ) );
	}

	inline static BF newFloat(avm_integer_t aValue)
	{
		return( BF( new Float(static_cast< avm_float_t >(aValue)) ) );
	}

	inline static BF newUFloat(avm_uinteger_t aValue)
	{
		return( BF( new Float(static_cast< avm_float_t >(aValue)) ) );
	}

	inline static BF newFloat(avm_float_t aValue)
	{
		return( BF( new Float(aValue) ) );
	}

	inline static BF newFloat(const std::string & aValue)
	{
		return( BF( new Float(aValue) ) );
	}


#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

	inline static BF newFloat(const Rational::RawValueType & aValue)
	{
		return( BF( new Float( Float::RawValueType(aValue) ) ) );
	}

	inline static BF newFloat(const Float::RawValueType & aValue)
	{
		return( BF( new Float(aValue) ) );
	}

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

	inline static BF newFloat(const mpq_t & aValue)
	{
		return( BF( new Float( Float::RawValueType(
				Rational::RawValueType(aValue)) ) ) );
	}

	inline static BF newFloat(const Rational::RawValueType & aValue)
	{
		return( BF( new Float( Float::RawValueType(aValue) ) ) );
	}

	inline static BF newFloat(const mpf_t & aValue)
	{
		return( BF( new Float( Float::RawValueType(aValue) ) ) );
	}

	inline static BF newFloat(const Float::RawValueType & aValue)
	{
		return( BF( new Float(aValue) ) );
	}

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT NEW NUMERIC VALUE
	////////////////////////////////////////////////////////////////////////////

	inline static BF newNumeric(const Numeric & aNumeric)
	{
		return( BF( aNumeric ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// Char / String / Identifier / QualifiedIdentifier
	////////////////////////////////////////////////////////////////////////////

	inline static BF newChar(Character * aValue)
	{
		return( BF( aValue ) );
	}

	inline static BF newChar(char aValue = ' ')
	{
		return( BF( new Character(aValue) ) );
	}

	inline static BF newChar(const std::string & aValue)
	{
		return( BF( new Character(aValue.at(0)) ) );
	}

	inline static BF newString(const std::string & aValue = "",
			char aQuote = String::DEFAULT_DELIMITER)
	{
		return( String::create(aValue, aQuote) );
	}

	inline static BF newSingleQuoteString(const std::string & aValue = "",
			char aQuote = String::SINGLE_QUOTE_DELIMITER)
	{
		return( String::create(aValue, aQuote) );
	}

	inline static BF newDoubleQuoteString(const std::string & aValue = "",
			char aQuote = String::DOUBLE_QUOTE_DELIMITER)
	{
		return( String::create(aValue, aQuote) );
	}

	inline static BF newIdentifier(const std::string & aValue = "")
	{
		return( BF( new Identifier(aValue) ) );
	}

	inline static BF newQualifiedIdentifier(const std::string & aValue = "")
	{
		return( BF( new QualifiedIdentifier(aValue) ) );
	}

	// new instance of Element Access FQN-ID :> machine<fqn>.element<name-id>
	static BF newQualifiedIdentifier(
			Machine * machine, const std::string & aNameID);

	static BF newQualifiedIdentifier(Machine * machine,
			const ObjectElement * objElement);

	static BF newQualifiedPositionalIdentifier(
			Machine * machine, avm_offset_t aPositionOffset );


	inline static BF newMachineVarUFI(
			const BF & aMachine, const BF & aVariable)
	{
		UniFormIdentifier * anUFI = new UniFormIdentifier(false);
		anUFI->appendFieldMachine( aMachine );
		anUFI->appendFieldVariable( aVariable );

		return( BF( anUFI ) );
	}


	/**
	 * SPECIFIC NUMERIC EXPRESSION
	 */
	inline static BF newExpr(bool aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aValue ) );
	}

	inline static BF newExpr(avm_integer_t aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aValue ) );
	}


	inline static BF newExpr(avm_integer_t  aNumer, avm_integer_t  aDenom)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aNumer, aDenom ) );
	}

	inline static BF newExpr(avm_integer_t aNumer, avm_uinteger_t aDenom)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aNumer, aDenom ) );
	}

	inline static BF newExpr(avm_uinteger_t aNumer, avm_uinteger_t aDenom)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aNumer, aDenom ) );
	}

	inline static BF newExpr(
			const Integer & aNumer, const Integer & aDenom)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aNumer, aDenom ) );
	}


	inline static BF newExpr(float aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aValue ) );
	}

	inline static BF newExpr(double aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( aValue ) );
	}


	/**
	 * SPECIFIC STRING VALUE as BUILTIN EXPRESSION
	 */
	inline static BF newExprBoolean(const std::string & aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newBoolean( aValue ) );
	}

	inline static BF newExprBoolean(const char * aValue)
	{
		return( (aValue != NULL)
				? ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newBoolean( std::string(aValue) )
				: ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newBoolean( false ) );
	}


	inline static BF newExprInteger(const std::string & aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newInteger( aValue ) );
	}

	inline static BF newExprInteger(const char * aValue)
	{
		return( (aValue != NULL)
				? ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newInteger( std::string(aValue) )
				: ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newInteger( 0 ) );
	}


	inline static BF newExprRational(const std::string & aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newRational( aValue ) );
	}

	inline static BF newExprRational(const char * aValue)
	{
		return( (aValue != NULL)
				? ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newRational( std::string(aValue) )
				: ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newRational( 0 ) );
	}


	inline static BF newExprFloat(const std::string & aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newFloat( aValue ) );
	}

	inline static BF newExprFloat(const char * aValue)
	{
		return( (aValue != NULL)
				? ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newFloat( std::string(aValue) )
				: ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newFloat( 0.0 ) );
	}


	inline static BF newExprNumber(const std::string & aValue)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExprNumber( aValue ) );
	}

	inline static BF newExprNumber(const char * aValue)
	{
		return( (aValue != NULL)
				? ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newExprNumber( std::string(aValue) )
				: ExpressionConstructorImpl< DEFAULT_EXPRESSION_IMPL >::
						newInteger( 0 ) );
	}


	static BF newExprMachine(const Configuration & aConfiguration,
			const std::string & aValue);

	static BF newExprRuntine(const Configuration & aConfiguration,
			const std::string & aValue);


	/**
	 * SPECIFIC TYPED STRING VALUE as BUILTIN EXPRESSION
	 */
	static BF newExpr(const Configuration & aConfiguration,
			const ITypeSpecifier & aTypeSpecifier, const std::string & aValue);


	/**
	 * SPECIFIC AVMCODE EXPRESSION
	 */
	inline static BF newExpr(const BF & anElement)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::newExpr( anElement ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// QUANTIFIER EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF existExpr(const BF & boundVar, const BF & formula)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::existExpr( boundVar, formula ) );
	}

	static BF existExpr(const AvmCode::this_container_type & listOfArg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::existExpr( listOfArg ) );
	}


	static BF forallExpr(const BF & boundVar, const BF & formula)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::forallExpr( boundVar, formula ) );
	}

	static BF forallExpr(const AvmCode::this_container_type & listOfArg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::forallExpr( listOfArg ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// AND EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF andExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::andExpr( arg0, arg1 ) );
	}

	inline static BF andExpr(const AvmCode::this_container_type & listOfArg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::andExpr( listOfArg ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// OR EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF orExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::orExpr( arg0, arg1 ) );
	}

	inline static BF orExpr(const AvmCode::this_container_type & listOfArg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::orExpr( listOfArg ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// NOT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF notExpr(const BF & arg)
	{
		if( arg.isEqualTrue() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE );

//			return( ExpressionConstructorImpl<
//					DEFAULT_EXPRESSION_IMPL >::newExpr( false ) );
		}
		else if( arg.isEqualFalse() )
		{
			return( ExpressionConstant::BOOLEAN_TRUE );

//			return( ExpressionConstructorImpl<
//					DEFAULT_EXPRESSION_IMPL >::newExpr( true ) );
		}
		else
		{
			return( ExpressionConstructorImpl<
					DEFAULT_EXPRESSION_IMPL >::notExpr( arg ) );
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// [ NOT ] EQUAL EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF eqExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::eqExpr( arg0, arg1 ) );
	}

	inline static BF neqExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::neqExpr( arg0, arg1 ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// [ NOT ] SYNTAXIC EQUAL EXPRESSION
	// FOR ALL EXPRESSION IMPLEMENTATION
	////////////////////////////////////////////////////////////////////////////

	inline static BF seqExpr(const BF & arg0, const BF & arg1)
	{
		return( newCode(OperatorManager::OPERATOR_SEQ, arg0, arg1) );
	}

	inline static BF nseqExpr(const BF & arg0, const BF & arg1)
	{
		return( newCode(OperatorManager::OPERATOR_NSEQ, arg0, arg1) );
	}


	////////////////////////////////////////////////////////////////////////////
	// COMPARE EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF gtExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::gtExpr( arg0, arg1 ) );
	}

	inline static BF gteExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::gteExpr( arg0, arg1 ) );
	}

	inline static BF ltExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::ltExpr( arg0, arg1 ) );
	}

	inline static BF lteExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::lteExpr( arg0, arg1 ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// ADD EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF addExpr(const BF & arg, avm_integer_t val);

	inline static BF addExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::addExpr( arg0, arg1 ) );
	}

	inline static BF addExpr(const AvmCode::this_container_type & listOfArg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::addExpr( listOfArg ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// UMINUS EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF uminusExpr(const BF & arg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::uminusExpr( arg ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// MINUS EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF minusExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::minusExpr( arg0, arg1 ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// MULT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF multExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::multExpr( arg0, arg1 ) );
	}

	inline static BF multExpr(const AvmCode::this_container_type & listOfArg)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::multExpr( listOfArg ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// POW EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF powExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::powExpr( arg0, arg1 ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// DIV EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF divExpr(const BF & arg0, const BF & arg1)
	{
		return( ExpressionConstructorImpl<
				DEFAULT_EXPRESSION_IMPL >::divExpr( arg0, arg1 ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// FOR ALL EXPRESSION IMPLEMENTATION
	////////////////////////////////////////////////////////////////////////////

	static BF newExpr(Operator * anOperator, const BF & arg);

	static BF newExpr(Operator * anOperator, const BF & arg1, const BF & arg2);

	static BF newExpr(Operator * anOperator,
			const AvmCode::this_container_type & listOfArg);

};


}

#endif /* EXPRESSIONCONSTRUCTOR_H_ */
