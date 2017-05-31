/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juin 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXPRESSIONCONSTRUCTORIMPL_H_
#define EXPRESSIONCONSTRUCTORIMPL_H_

/**
 * DEFINE MACRO W.R.T. LICENSE CONSTRAINT
 */
#if defined( _ECLIPSE_PUBLIC_LICENSE_ )

#else

#endif /* _ECLIPSE_PUBLIC_LICENSE_ */


#include <fml/lib/AvmLang.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/AvmCodeFactory.h>
#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/numeric/Float.h>
#include <fml/builtin/Identifier.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>
#include <fml/builtin/String.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/expression/ExpressionConstant.h>

#include <cmath>
#include <cstring>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// COMMON IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< class EpressionCtr >
class CommonExpressionConstructorImpl
{

public:
	inline static BF seqExpr(const BF & arg0, const BF & arg1)
	{
		return( EpressionCtr::newBoolean( arg0.isEQ(arg1) ) );
	}

	inline static BF nseqExpr(const BF & arg0, const BF & arg1)
	{
		return( EpressionCtr::newBoolean( arg0.isNEQ(arg1) ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF newExpr(Operator * anOperator, const BF & arg)
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
				return( EpressionCtr::notExpr(arg) );
			}

			case AVM_OPCODE_UMINUS:
			{
				return( EpressionCtr::uminusExpr(arg) );
			}

			default:
			{
				return( AvmCodeFactory::newCode(anOperator, arg) );
			}
		}
	}

	inline static BF newExpr(
			Operator * anOperator, const BF & arg1, const BF & arg2)
	{
		switch( anOperator->getAvmOpCode() )
		{
			case AVM_OPCODE_AND:
			{
				return( EpressionCtr::andExpr(arg1, arg2) );
			}
			case AVM_OPCODE_OR:
			{
				return( EpressionCtr::orExpr(arg1, arg2) );
			}

			case AVM_OPCODE_EXIST:
			{
				return( EpressionCtr::existExpr(arg1, arg2) );
			}
			case AVM_OPCODE_FORALL:
			{
				return( EpressionCtr::forallExpr(arg1, arg2) );
			}

			case AVM_OPCODE_EQ:
			{
				return( EpressionCtr::eqExpr(arg1, arg2) );
			}
			case AVM_OPCODE_NEQ:
			{
				return( EpressionCtr::neqExpr(arg1, arg2) );
			}

			case AVM_OPCODE_SEQ:
			{
				return( EpressionCtr::seqExpr(arg1, arg2) );
			}
			case AVM_OPCODE_NSEQ:
			{
				return( EpressionCtr::nseqExpr(arg1, arg2) );
			}

			case AVM_OPCODE_LT:
			{
				return( EpressionCtr::ltExpr(arg1, arg2) );
			}
			case AVM_OPCODE_LTE:
			{
				return( EpressionCtr::lteExpr(arg1, arg2) );
			}
			case AVM_OPCODE_GT:
			{
				return( EpressionCtr::gtExpr(arg1, arg2) );
			}
			case AVM_OPCODE_GTE:
			{
				return( EpressionCtr::gteExpr(arg1, arg2) );
			}

			case AVM_OPCODE_PLUS:
			{
				return( EpressionCtr::addExpr(arg1, arg2) );
			}
			case AVM_OPCODE_MINUS:
			{
				return( EpressionCtr::minusExpr(arg1, arg2) );
			}

			case AVM_OPCODE_MULT:
			{
				return( EpressionCtr::multExpr(arg1, arg2) );
			}
			case AVM_OPCODE_POW:
			{
				return( EpressionCtr::powExpr(arg1, arg2) );
			}

			case AVM_OPCODE_DIV:
			{
				return( EpressionCtr::divExpr(arg1, arg2) );
			}

			default:
			{
				return( AvmCodeFactory::newCode(anOperator, arg1, arg2) );
			}
		}
	}


	inline static BF newExpr(Operator * anOperator,
			const AvmCode::this_container_type & listOfArg)
	{
		switch( anOperator->getAvmOpCode() )
		{
			case AVM_OPCODE_AND:
			{
				return( EpressionCtr::andExpr(listOfArg) );
			}
			case AVM_OPCODE_OR:
			{
				return( EpressionCtr::orExpr(listOfArg) );
			}

			case AVM_OPCODE_PLUS:
			{
				return( EpressionCtr::addExpr(listOfArg) );
			}
			case AVM_OPCODE_MULT:
			{
				return( EpressionCtr::multExpr(listOfArg) );
			}

			default:
			{
				return( AvmCodeFactory::newCode(anOperator, listOfArg) );
			}
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// INCR / DECR  EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF addExpr(const BF & arg, avm_integer_t val)
	{
		switch( arg.classKind() )
		{
			case FORM_BUILTIN_INTEGER_KIND:
			{
				BF res = arg;
				res.makeWritable();
				res.to_ptr< Integer >()->addExpr(val);
				return( res );
			}

			case FORM_BUILTIN_RATIONAL_KIND:
			{
				BF res = arg;
				res.makeWritable();
				res.to_ptr< Rational >()->addExpr(val);
				return( res );
			}

			case FORM_BUILTIN_FLOAT_KIND:
			{
				BF res = arg;
				res.makeWritable();
				res.to_ptr< Float >()->addExpr(val);
				return( res );
			}

			default:
			{
				return( EpressionCtr::addExpr(arg,
						EpressionCtr::newInteger(val)) );
			}
		}
	}

	inline static BF powExpr(const BF & arg, avm_uinteger_t val)
	{
		switch( arg.classKind() )
		{
			case FORM_BUILTIN_INTEGER_KIND:
			{
				BF res = arg;
				res.makeWritable();
				res.to_ptr< Integer >()->set_pow(val);
				return( res );
			}

			case FORM_BUILTIN_RATIONAL_KIND:
			{
				BF res = arg;
				res.makeWritable();
				res.to_ptr< Rational >()->set_pow(val);
				return( res );
			}

			case FORM_BUILTIN_FLOAT_KIND:
			{
				BF res = arg;
				res.makeWritable();
				res.to_ptr< Float >()->set_pow(val);
				return( res );
			}

			default:
			{
				return( EpressionCtr::powExpr(arg,
						EpressionCtr::newUInteger(val)) );
			}
		}
	}

};


/**
 * ExpressionConstructorImpl
 * TRAITS
 */
template< EXPRESSION::IMPLEMENTATION_KIND expr_impl_kind >
class ExpressionConstructorImpl;





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// NATIVE_IMPL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ExpressionConstructorNative  :
		public CommonExpressionConstructorImpl< ExpressionConstructorNative >
{

public:
	/**
	 * PRIMITIVE EXPRESSION
	 */
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
	// NEW INTEGER VALUE
	////////////////////////////////////////////////////////////////////////////

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


	////////////////////////////////////////////////////////////////////////////
	// NEW RATIONAL VALUE
	////////////////////////////////////////////////////////////////////////////

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
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newRational(avm_integer_t aNumer, avm_uinteger_t aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newURational(avm_uinteger_t aNumer, avm_uinteger_t aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newRational(const std::string & aValue)
	{
		std::string::size_type pos = aValue.find('/');
		if( pos != std::string::npos )
		{
			return( BF( new Rational(
					aValue.substr(0, pos), aValue.substr(pos+1)) ) );
		}
		else if( (pos = aValue.find('.')) != std::string::npos )
		{
			Integer aNumer( std::string(aValue).erase(pos, 1) );

			Integer aDenom( 10 );
			aDenom.set_pow( aValue.size() - (pos + 1) );

			return( BF( new Rational(aNumer, aDenom) ) );
		}
		else
		{
			return( BF( new Rational(aValue, 1) ) );
			}
			}

	inline static BF newRational(
			const std::string & strNumer, const std::string & strDenom)
			{
		return( BF( new Rational(strNumer,  strDenom) ) );
	}



	////////////////////////////////////////////////////////////////////////////
	// NEW FLOAT VALUE
	////////////////////////////////////////////////////////////////////////////

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


	/**
	 * SPECIFIC NUMERIC EXPRESSION
	 */
	inline static BF newExpr(bool aValue)
	{
		return( newBoolean(aValue) );
	}


	inline static BF newExpr(avm_integer_t aValue)
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


	inline static BF newExpr(avm_integer_t aNumer, avm_integer_t aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newExpr(avm_integer_t aNumer, avm_uinteger_t aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newExpr(avm_uinteger_t aNumer, avm_uinteger_t aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}

	inline static BF newExpr(
			const Integer & aNumer, const Integer & aDenom)
	{
		return( BF( new Rational(aNumer, aDenom) ) );
	}


	inline static BF newExpr(float aValue)
	{
		return( BF( new Float(aValue) ) );
	}

	inline static BF newExpr(double aValue)
	{
		return( BF( new Float(aValue) ) );
	}


	inline static BF newExprNumber(const std::string & aValue)
	{
		std::string::size_type pos = aValue.find('/');
		if( pos != std::string::npos )
		{
			return( BF( new Rational(
					aValue.substr(0, pos), aValue.substr(pos+1)) ) );
		}
		else if( (pos = aValue.find('.')) != std::string::npos )
		{
			Integer aNumer( std::string(aValue).erase(pos, 1) );

			Integer aDenom( 10 );
			aDenom.set_pow( aValue.size() - (pos + 1) );

			return( BF( new Rational(aNumer, aDenom) ) );
		}
		else
		{
			return( BF( new Integer(aValue) ) );
		}
	}


	/**
	 * SPECIFIC AVMCODE EXPRESSION
	 */

	inline static BF newExpr(const BF & anElement)
	{
		return( anElement );
	}

	////////////////////////////////////////////////////////////////////////////
	// AND EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF andExpr(const BF & arg0, const BF & arg1);

	static BF andExpr(const AvmCode::this_container_type & listOfArg);

	////////////////////////////////////////////////////////////////////////////
	// OR EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF orExpr(const BF & arg0, const BF & arg1);

	static BF orExpr(const AvmCode::this_container_type & listOfArg);


	////////////////////////////////////////////////////////////////////////////
	// QUANTIFIER EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF existExpr(const BF & boundVar, const BF & formula);

	static BF existExpr(const AvmCode::this_container_type & listOfArg);


	static BF forallExpr(const BF & boundVar, const BF & formula);

	static BF forallExpr(const AvmCode::this_container_type & listOfArg);


	////////////////////////////////////////////////////////////////////////////
	// NOT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF notExpr(const BF & arg);


	////////////////////////////////////////////////////////////////////////////
	// COMPARE EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF eqExpr(const BF & arg0, const BF & arg1);

	static BF neqExpr(const BF & arg0, const BF & arg1);

	static BF gtExpr(const BF & arg0, const BF & arg1);

	static BF gteExpr(const BF & arg0, const BF & arg1);

	static BF ltExpr(const BF & arg0, const BF & arg1);

	static BF lteExpr(const BF & arg0, const BF & arg1);


	////////////////////////////////////////////////////////////////////////////
	// ADD EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF addNumber(const BF & num0, const BF & num1);

	static BF addExpr(const BF & arg0, const BF & arg1);

	static BF addExpr(const AvmCode::this_container_type & listOfArg);



	////////////////////////////////////////////////////////////////////////////
	// MINUS EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF minusExpr(const BF & arg0, const BF & arg1);


	////////////////////////////////////////////////////////////////////////////
	// UMINUS EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF uminusExpr(const BF & arg);

	////////////////////////////////////////////////////////////////////////////
	// MULT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF multExpr(const BF & arg0, const BF & arg1);

	static BF multExpr(const AvmCode::this_container_type & listOfArg);


	////////////////////////////////////////////////////////////////////////////
	// POW EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF powExpr(const BF & arg0, const BF & arg1);


	////////////////////////////////////////////////////////////////////////////
	// DIV EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	static BF divExpr(const BF & arg0, const BF & arg1);


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	inline static BF newExpr(Operator * anOperator,
			const AvmCode::this_container_type & listOfArg)
	{
		return( CommonExpressionConstructorImpl::newExpr(anOperator, listOfArg) );
	}

};


template< >
class ExpressionConstructorImpl< EXPRESSION::NATIVE_IMPL >  :
		public ExpressionConstructorNative
{
	/* NOTHING ELSE */
};


} /* namespace sep */
#endif /* EXPRESSIONCONSTRUCTORIMPL_H_ */
