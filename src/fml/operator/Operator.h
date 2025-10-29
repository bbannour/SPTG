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
#ifndef OPERATOR_H_
#define OPERATOR_H_

#include <common/NamedElement.h>

#include <fml/operator/OperatorLib.h>


namespace sep
{


class Operator final : public NamedElement ,
		AVM_INJECT_STATIC_NULL_REFERENCE( Operator ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Operator )
{

	AVM_DECLARE_UNCLONABLE_CLASS( Operator )


protected:
	/**
	 * ATTRIBUTES
	 */
	AVM_OPCODE mAvmOpCode;

	AVM_OPCODE mOptimizedOpCode;

	avm_offset_t mOffset;

	ALGEBRA_QUALIFIER mAlgebraQualifier;
	FIX_NOTATION mFixNotation;

	std::string mStandardSymbol;

	std::string mSyntaxMIXFIX;

	std::string mSymbolQEPCAD;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Operator(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			AVM_OPCODE anAvmOpCode, AVM_OPCODE anOptimizedOpCode,
			ALGEBRA_QUALIFIER anAlgebraQualifier, FIX_NOTATION aFixNotation,
			const std::string & aStandardSymbol,
			const std::string & aSyntaxMIXFIX,
			const std::string & aSymbolQEPCAD);


	/**
	 * DESTRUCTOR
	 */
	virtual ~Operator()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static Operator & nullref()
	{
		static Operator _NULL_( "_::null<Operator>", "$null<Operator>",
				AVM_OPCODE_NULL, AVM_OPCODE_NULL,
				ALGEBRA_QUALIFIER::ALGEBRA_STD, FIX_NOTATION::NOTATION_INFIX,
				"$null<Operator>", "$null<Operator>", "$null<Operator>" );

		return( _NULL_ );
	}


	/**
	 * VALIDITY TEST
	 * _NULL_
	 */
	inline bool isNull() const
	{
		return( (mAvmOpCode == AVM_OPCODE_NULL) );
//				&& (mOptimizedOpCode == AVM_OPCODE_NULL) );
	}

	inline bool isnotNull() const
	{
		return( (mAvmOpCode != AVM_OPCODE_NULL) );
//				|| (mOptimizedOpCode != AVM_OPCODE_NULL) );
	}


	/*
	 * GETTER
	 * mAvmOpCode
	 */
	inline AVM_OPCODE getAvmOpCode() const
	{
		return( mAvmOpCode );
	}

	/*
	 * GETTER
	 * mOptimizedOpCode
	 */
	inline AVM_OPCODE getOptimizedOpCode() const
	{
		return( mOptimizedOpCode );
	}


	/**
	 * GETTER - SETTER
	 * mOffset
	 */
	inline avm_offset_t getOffset() const
	{
		return( mOffset );
	}

	inline void setOffset(avm_offset_t anOffset)
	{
		mOffset = anOffset;
	}


	/*
	 * GETTER
	 * mAlgebraQualifier
	 */
	inline ALGEBRA_QUALIFIER getAlgebraQualifier() const
	{
		return( mAlgebraQualifier );
	}

	inline bool isAssociative() const
	{
		return( (mAlgebraQualifier == ALGEBRA_ASSOC     ) ||
				(mAlgebraQualifier == ALGEBRA_ASSOC_COMM) );
	}

	inline bool isWeakAssociative() const
	{
		return( (mAlgebraQualifier == ALGEBRA_ASSOC      ) ||
				(mAlgebraQualifier == ALGEBRA_ASSOC_COMM ) ||
				(mAlgebraQualifier == ALGEBRA_LEFT_ASSOC ) ||
				(mAlgebraQualifier == ALGEBRA_RIGHT_ASSOC) );
	}

	inline bool isCommutative() const
	{
		return( (mAlgebraQualifier == ALGEBRA_COMM      ) ||
				(mAlgebraQualifier == ALGEBRA_ASSOC_COMM) );
	}

	/*
	 * GETTER
	 * the NAME
	 */

	inline const std::string & standardSymbol() const
	{
		return( mStandardSymbol );
	}

	inline const std::string & mixfixSyntax() const
	{
		return( mSyntaxMIXFIX );
	}

	inline const std::string & qepcadSymbol() const
	{
		return( mSymbolQEPCAD );
	}


	/*
	 * GETTER
	 * mFixNotation
	 */
	inline FIX_NOTATION getFixNotation() const
	{
		return( mFixNotation );
	}


	/**
	 * COMPARISON EQUAL
	 * for mOperator
	 */
	inline bool isEQ(const Operator & op) const
	{
		return( (this == &op) || (mAvmOpCode == op.mAvmOpCode) );
	}

	inline bool isEQ(const Operator * op) const
	{
		return( (this == op) || (mAvmOpCode == op->mAvmOpCode) );
	}

	// Due to [-Woverloaded-virtual=]
	using Element::isEQ;


	inline bool isOpCode(AVM_OPCODE opCode) const
	{
		return( mAvmOpCode == opCode );
	}

	inline bool hasOpCode(AVM_OPCODE opCode1, AVM_OPCODE opCode2) const
	{
		return( (mAvmOpCode == opCode1) ||
				(mAvmOpCode == opCode2) );
	}

	inline bool hasOpCode(AVM_OPCODE opCode1,
			AVM_OPCODE opCode2, AVM_OPCODE opCode3) const
	{
		return( (mAvmOpCode == opCode1) ||
				(mAvmOpCode == opCode2) ||
				(mAvmOpCode == opCode3) );
	}

	inline bool isOpCode(const Operator * op) const
	{
		return( mAvmOpCode == op->mAvmOpCode );
	}

	inline bool isOptimizedOpCode(AVM_OPCODE opCode) const
	{
		return( mOptimizedOpCode == opCode );
	}


	inline bool isnotOpCode(AVM_OPCODE opCode) const
	{
		return( mAvmOpCode != opCode );
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const override
	{
		os << TAB;
		toStream(os, PRINT_OPERATOR_SYMBOL_FORMAT);
		os << EOL;
	}

	virtual void toStream(OutStream & os,
			ENUM_PRINT_OPERATOR_FORMAT printFormat) const;


	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss;

		oss << TAB;
		toStream(oss, PRINT_OPERATOR_SYMBOL_FORMAT);
		oss << EOL;

		return( oss.str() );
	}

	inline virtual std::string str() const override
	{
		return( mStandardSymbol );
	}


	inline std::string strOp(ENUM_PRINT_OPERATOR_FORMAT
			printFormat = PRINT_OPERATOR_SYMBOL_FORMAT) const
	{
		StringOutStream oss;

		toStream(oss, printFormat);

		return( oss.str() );
	}


	inline const std::string & strSMT() const
	{
		return( mStandardSymbol );
	}

};


}

#endif /*OPERATOR_H_*/
