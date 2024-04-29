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
#ifndef AVMCODE_H_
#define AVMCODE_H_

#include <common/Element.h>

#include <common/BF.h>

//#include <collection/BFContainer.h>
#include <collection/List.h>
#include <collection/Vector.h>

#include <fml/executable/AvmInstruction.h>


#include <fml/operator/Operator.h>


namespace sep
{

class BaseTypeSpecifier;

class BFCode;


class AvmCode : public Element ,
		AVM_INJECT_STATIC_NULL_REFERENCE( AvmCode ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AvmCode )
{

	AVM_DECLARE_CLONABLE_CLASS( AvmCode )

public:
	/**
	 * TYPEDEF
	 */
	typedef Vector< BF >                               OperandCollectionT;

	typedef OperandCollectionT::const_iterator         const_iterator;

	typedef OperandCollectionT::iterator               iterator;

	typedef OperandCollectionT::size_type              size_type;

	/**
	* PRETTY PRINTING OPTIONS
	*/
	static bool EXPRESSION_PRETTY_PRINTER_BASED_FQN;


protected:
	/*
	 * ATTRIBUTES
	 */
	const Operator * mOperator;

	OperandCollectionT mOperands;

	AvmInstruction * mInstruction;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCode(const Operator * anOperator)
	: Element( CLASS_KIND_T( AvmCode ) ),
	mOperator( anOperator ),
	mOperands( ),
	mInstruction( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmCode(const AvmCode & anElement)
	: Element( anElement ),
	mOperator( anElement.mOperator ),
	mOperands( anElement.mOperands ),
	mInstruction( (anElement.mInstruction == nullptr) ? nullptr
			: new AvmInstruction( *(anElement.mInstruction) ) )
	{
		//!! NOTHING
	}


	AvmCode(const Operator * anOperator, const BF & arg)
	: Element( CLASS_KIND_T( AvmCode ) ),
	mOperator( anOperator ),
	mOperands( arg ),
	mInstruction( nullptr )
	{
		//!! NOTHING
	}

	AvmCode(const Operator * anOperator, const BF & arg1, const BF & arg2)
	: Element( CLASS_KIND_T( AvmCode ) ),
	mOperator( anOperator ),
	mOperands( arg1 , arg2 ),
	mInstruction( nullptr )
	{
		//!! NOTHING
	}

	AvmCode(const Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3)
	: Element( CLASS_KIND_T( AvmCode ) ),
	mOperator( anOperator ),
	mOperands( arg1 , arg2 , arg3 ),
	mInstruction( nullptr )
	{
		//!! NOTHING
	}

	AvmCode(const Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3, const BF & arg4)
	: Element( CLASS_KIND_T( AvmCode ) ),
	mOperator( anOperator ),
	mOperands( arg1 , arg2 , arg3 , arg4 ),
	mInstruction( nullptr )
	{
		//!! NOTHING
	}

	AvmCode(const Operator * anOperator, const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4, const BF & arg5)
	: Element( CLASS_KIND_T( AvmCode ) ),
	mOperator( anOperator ),
	mOperands( arg1 , arg2 , arg3 , arg4 , arg5 ),
	mInstruction( nullptr )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCode()
	{
		delete ( mInstruction );
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static AvmCode & nullref()
	{
		static AvmCode _NULL_( Operator::nullref_ptr() );

		return( _NULL_ );
	}


	/**
	 * GETTER
	 * mOperands
	 */
	inline const OperandCollectionT & getOperands() const
	{
		return( mOperands );
	}

	inline OperandCollectionT & getOperands()
	{
		return( mOperands );
	}

	inline bool hasOperand() const
	{
		return( mOperands.nonempty() );
	}

	inline bool hasOneOperand() const
	{
		return( mOperands.singleton() );
	}

	inline bool hasManyOperands() const
	{
		return( mOperands.populated() );
	}

	inline bool noOperand() const
	{
		return( mOperands.empty() );
	}


	/**
	 * GETTER
	 * for iterators
	 */
	inline AvmCode::iterator begin()
	{
		return( mOperands.begin() );
	}

	inline AvmCode::iterator end()
	{
		return( mOperands.end() );
	}

	inline AvmCode::const_iterator begin() const
	{
		return( mOperands.begin() );
	}

	inline AvmCode::const_iterator end() const
	{
		return( mOperands.end() );
	}


	/**
	 * APPEND
	 * OperandCollectionT
	 */
	inline void append(const BF & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!" !!!"
//				<< SEND_EXIT;

		mOperands.append( anElement );
	}

	inline void append(const OperandCollectionT & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		mOperands.append( anElement );
	}

	inline void appendTail(const OperandCollectionT & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		mOperands.appendTail( anElement );
	}

	inline void append(const List< BF > & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		mOperands.append( anElement );
	}

	inline void append(const List< BFCode > & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		mOperands.append( anElement );
	}


	inline void appendFlat(const BF & anElement)
	{
		if( anElement.is< AvmCode >()
			&& getOperator()->isWeakAssociative()
			&& (anElement.to< AvmCode >().getOperator() == getOperator()) )
		{
			append( anElement.to< AvmCode >().getOperands() );
		}
		else
		{
			append( anElement );
		}
	}


	/**
	 * GETTER - SETTER
	 * for element in mOperands
	 */
	inline virtual const BF & operand(std::size_t offset) const
	{
		return( mOperands.get(offset) );
	}

	inline virtual BF & operand(std::size_t offset)
	{
		return( mOperands.get(offset) );
	}

	inline virtual BF & at(std::size_t offset) override
	{
		return( mOperands.at(offset) );
	}

	inline virtual const BF & at(std::size_t offset) const override
	{
		return( mOperands.at(offset) );
	}


	inline virtual BF & operator[](std::size_t offset) override
	{
		return( mOperands[offset] );
	}

	inline virtual const BF & operator[](std::size_t offset) const override
	{
		return( mOperands[offset] );
	}


	inline virtual BF & getWritable(std::size_t offset) override
	{
		mOperands.at(offset).makeWritable();

		return( mOperands[offset] );
	}

	inline virtual void makeWritable(std::size_t offset) override
	{
		mOperands.at(offset).makeWritable();
	}


	inline virtual void safe_set(std::size_t offset, const BF & anElement)
	{
		mOperands[offset] = anElement;
	}

	inline virtual void set(std::size_t offset, const BF & anElement) override
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		////////////////////////////////////////////////////////////////////////
		//!!! OPTIMISATION
		////////////////////////////////////////////////////////////////////////
//		mOperands.set(offset, anElement);

		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( offset , size() )
				<< SEND_EXIT;

		mOperands.operator[](offset) = anElement;
	}

	inline std::size_t size() const override
	{
		return( mOperands.size() );
	}


	/**
	 * GETTER UTILS
	 */
	inline const BF & first() const
	{
		return( mOperands.first() );
	}

	inline BF & first()
	{
		return( mOperands.first() );
	}


	inline const BF & second() const
	{
		return( mOperands.second() );
	}

	inline BF & second()
	{
		return( mOperands.second() );
	}


	inline const BF & third() const
	{
		return( mOperands.third() );
	}

	inline BF & third()
	{
		return( mOperands.third() );
	}


	inline const BF & last() const
	{
		return( mOperands.last() );
	}

	inline BF & last()
	{
		return( mOperands.last() );
	}


	/**
	 * GETTER - SETTER
	 * for mOperator
	 */
	inline const Operator * getOperator() const
	{
		return( mOperator );
	}

	inline AVM_OPCODE getAvmOpCode() const
	{
		return( mOperator->getAvmOpCode() );
	}

	inline AVM_OPCODE getOptimizedOpCode() const
	{
		return( mOperator->getOptimizedOpCode() );
	}

	inline avm_offset_t getOpOffset() const
	{
		return( mOperator->getOffset() );
	}


	inline bool isOperator(const Operator * anOperator) const
	{
		return( mOperator->isEQ( anOperator ) );
	}

	inline bool isOpCode(AVM_OPCODE opCode) const
	{
		return( mOperator->isOpCode( opCode ) );
	}

	inline bool hasOpCode(AVM_OPCODE opCode1, AVM_OPCODE opCode2) const
	{
		return( mOperator->hasOpCode( opCode1 , opCode2 ) );
	}

	inline bool hasOpCode(AVM_OPCODE opCode1,
			AVM_OPCODE opCode2, AVM_OPCODE opCode3) const
	{
		return( mOperator->hasOpCode( opCode1 , opCode2 , opCode3 ) );
	}

	inline bool isOpCode(const Operator * op) const
	{
		return( mOperator->isOpCode( op ) );
	}

	inline bool isOptimizedOpCode(AVM_OPCODE opCode) const
	{
		return( mOperator->isOptimizedOpCode( opCode ) );
	}

	inline bool sameOperator(const AvmCode & aCode) const
	{
		return( mOperator->isEQ( aCode.mOperator ) );
	}

	inline bool sameOperator(const AvmCode * aCode) const
	{
		return( mOperator->isEQ( aCode->mOperator ) );
	}


	inline bool isnotOpCode(AVM_OPCODE opCode) const
	{
		return( mOperator->isnotOpCode( opCode ) );
	}


	inline void setOperator(const Operator * anOperator)
	{
		mOperator = anOperator;
	}

	inline const std::string & strOperator() const
	{
		return( mOperator->standardSymbol() );
	}


	/**
	 * GETTER - SETTER
	 * for mInstruction
	 */
	inline AvmInstruction * getInstruction() const
	{
		return( mInstruction );
	}

	inline bool hasInstruction() const
	{
		return( mInstruction != nullptr );
	}


	inline AvmInstruction * newEmptyInstruction()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInstruction == nullptr )
				<< "Unexpected a code with AvmInstruction: "
				<< toStringWithBytecode()
				<< SEND_EXIT;

		return( mInstruction = new AvmInstruction() );
	}

	inline AvmInstruction * newInstruction(std::size_t aSize)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInstruction == nullptr )
				<< "Unexpected a code with AvmInstruction: "
				<< toStringWithBytecode()
				<< SEND_EXIT;

		return( mInstruction = new AvmInstruction( aSize ) );
	}

	inline AvmInstruction * genInstruction()
	{
		return( newInstruction( size() ) );
	}


	inline void setInstruction(AvmInstruction * anInstruction)
	{
		mInstruction = anInstruction;
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	int compare(const AvmCode & other) const;

	inline bool operator==(const AvmCode & other) const
	{
		return( AvmCode::isEQ( other ) );
	}

	inline bool operator==(const AvmCode * other) const
	{
		return( (other != nullptr) && AvmCode::isEQ( *other ) );
	}

	inline bool operator!=(const AvmCode & other) const
	{
		return( (this != &other) && (not AvmCode::isEQ( other )) );
	}

	inline bool operator!=(const AvmCode * other) const
	{
		return( (other == nullptr)
				|| ((this != other)
					&& (not AvmCode::isEQ( *other ) ) ) );
	}


	bool isEQ(const AvmCode & other) const;

	inline bool isEQ(const AvmCode * other) const
	{
		return( (other != nullptr) && AvmCode::isEQ( *other ) );
	}

	// Due to [-Woverloaded-virtual=]
	using Element::isEQ;


	/**
	 * Serialization
	 */
	inline std::string strDebug(const AvmIndent & indent = AVM_SPC_INDENT) const
	{
		StringOutStream oss(indent);

		toDebug( oss );

		return( oss.str() );
	}

	OutStream & toDebug(OutStream & out) const;

	OutStream & toStreamWithBytecode(OutStream & out) const;

	inline std::string toStringWithBytecode(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStreamWithBytecode( oss );

		return( oss.str() );
	}

	OutStream & toStreamRoutine(OutStream & out) const;


	void toStreamPrefix(OutStream & out, bool printEOL = true) const;

	static void toStreamPrefix(OutStream & out, const BF & arg);


	inline static void toStream(OutStream & out, const BF & arg)
	{
//		toStreamPrefix(out, arg);

		prettyPrinter(out, arg);
	}

	inline virtual void toStream(OutStream & out) const override
	{
AVM_IF_DEBUG_FLAG( BYTECODE )

	toStreamPrefix( out );

	return;

AVM_ENDIF_DEBUG_FLAG( BYTECODE )

		prettyPrinter( out );
	}


	/**
	 * PRETTY PRINTER
	 */
	void prettyPrinter(OutStream & out, bool isStatement = true) const;

	void prettyPrinterBasicStatement(
			OutStream & out, bool isStatement = true) const;

	void prettyPrinterBlockStatement(
			OutStream & out, bool isStatement = true) const;

	void prettyPrinterDefault(OutStream & out, bool isStatement = true) const;

	void prettyPrinterFunctional(OutStream & out, bool isExpression = true) const;
	void prettyPrinterInfix(OutStream & out, bool isExpression = true) const;
	void prettyPrinterPrefix(OutStream & out, bool isExpression = true) const;
	void prettyPrinterSuffix(OutStream & out, bool isExpression = true) const;

	static void prettyPrinter(OutStream & out,
			const BF & arg, bool isStatement = true);

	static void prettyPrinter(OutStream & out,
			const BF & arg, const BaseTypeSpecifier & aType);

	static void prettyPrinterCondition(OutStream & out, const BF & arg);

	static void prettyPrinterBlock(OutStream & out, const BF & arg);


	/**
	 * toString
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss(indent);

//		toStream(oss);
		prettyPrinter(oss);

		return( oss.str() );
	}

	inline virtual std::string str() const override
	{
		StringOutStream oss( AVM_STR_INDENT );

//		toStream(oss);
		prettyPrinter( oss << IGNORE_FIRST_TAB );

		return( oss.str() );
	}

};


/**
 * operator<<
 */
AVM_OS_STREAM( AvmCode )



#define AVM_DEBUG_BFCODE_POINTER  true
#undef AVM_DEBUG_BFCODE_POINTER

#if defined(AVM_DEBUG_BFCODE_POINTER)

//	#define AVM_DECLARE_DEBUG_BFCODE_PTR        const AvmCode * debugPTR;
//
//	#define AVM_INIT_DEBUG_BFCODE_PTR( ptr )    , debugPTR( ptr )
//
//	#define AVM_ASSIGN_STMNT_DEBUG_BFCODE_PTR( ptr )  debugPTR = ptr;
//
//	#define AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR( ptr )   debugPTR = ptr


	#define AVM_DECLARE_DEBUG_BFCODE_PTR        public: std::string dbgPTR;


	#define AVM_STR_BFCODE_PTR( ptr )  ( (ptr != nullptr) ? ptr->str() : "BFCode<null>" )

	#define AVM_INIT_DEBUG_BFCODE_PTR_NULL      , dbgPTR( "BFCode<null>" )

	#define AVM_INIT_DEBUG_BFCODE_PTR( ptr )    , dbgPTR( AVM_STR_BFCODE_PTR(ptr) )

	#define AVM_COPY_DEBUG_BFCODE_PTR( bf )     , dbgPTR( bf.dbgPTR )

	#define AVM_ASSIGN_DEBUG_BFCODE_PTR( ptr )  dbgPTR = AVM_STR_BFCODE_PTR(ptr);

#else

	#define AVM_DECLARE_DEBUG_BFCODE_PTR

	#define AVM_INIT_DEBUG_BFCODE_PTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_BFCODE_PTR( ptr )

	#define AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR( ptr )  ptr

#endif




class BFCode :
		public BF ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BFCode )
{


protected:
	/**
	 * Only for debug facilities
	 */
	AVM_DECLARE_DEBUG_BFCODE_PTR

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BFCode()
	: BF()
	AVM_INIT_DEBUG_BFCODE_PTR( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BFCode(const BFCode & other)
	: BF( other )
	AVM_INIT_DEBUG_BFCODE_PTR( other.debugPTR )
	{
		//!! NOTHING
	}

//	explicit BFCode(const BF & other)
//	: BF( ( other.is< AvmCode >() ) ? other : BFCode::REF_NULL )
//	AVM_INIT_DEBUG_BFCODE_PTR( ( other.is< AvmCode >() ) ?
//			static_cast< const AvmCode * >( other.raw_pointer() ) : nullptr )
//	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( other.invalid() || other.is< AvmCode >() )
//				<< "Invalid Constructor Cast of a BF to a BFCode !!!"
//				<< SEND_EXIT;
//	}

	explicit BFCode(AvmCode * aCode)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(  aCode ) )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	BFCode(const Operator * anOperator)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator) ) )
	{
		//!! NOTHING
	}

	BFCode(const Operator * anOperator, const BF & arg)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg) ) )
	{
		//!! NOTHING
	}

	BFCode(const Operator * anOperator, const BF & arg1, const BF & arg2)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2) ) )
	{
		//!! NOTHING
	}

	BFCode(const Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2, arg3) ) )
	{
		//!! NOTHING
	}

	BFCode(const Operator * anOperator, const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2, arg3, arg4) ) )
	{
		//!! NOTHING
	}

	BFCode(const Operator * anOperator, const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4, const BF & arg5)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2, arg3, arg4, arg5) ) )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BFCode()
	{
		//!! NOTHING
	}


	/**
	 * CAST
	 */

//protected:
	inline operator AvmCode * () const
	{
		return( static_cast< AvmCode * >( mPTR ) );
	}

	inline AvmCode * raw_pointer() const
	{
		return( static_cast< AvmCode * >( mPTR ) );
	}

	inline AvmCode & raw_reference() const
	{
		return( static_cast< AvmCode & >( * mPTR ) );
	}


	/**
	 * OPERATORS
	 */
	inline  const AvmCode & operator * () const
	{
		return( static_cast< AvmCode & >( *mPTR ) );
	}

	inline AvmCode * operator-> () const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "Unexpected a BFCode with a NULL Pointer !!!"
				<< SEND_EXIT;

		return( static_cast< AvmCode * >( mPTR )  );
	}


	/**
	 * ASSIGNMENT
	 */
	inline BFCode & operator=(AvmCode * aPtr)
	{
		if( mPTR != aPtr )
		{
			AVM_ASSIGN_STMNT_DEBUG_BFCODE_PTR( aPtr )

			release( aPtr );
		}
		return( *this );
	}

	inline BFCode & operator=(const BFCode & other)
	{
		if( mPTR != other.mPTR )
		{
			AVM_ASSIGN_STMNT_DEBUG_BFCODE_PTR( other.debugPTR )

			release_acquire( other.mPTR );
		}
		return( *this );
	}

	inline BFCode & operator=(const BF & other)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT(
				other.invalid() || other.is< AvmCode >() )
				<< "Invalid Assignment Cast of a BF to a BFCode !!!"
				<< SEND_EXIT;

		if( mPTR != other.raw_pointer() )
		{
			AVM_ASSIGN_STMNT_DEBUG_BFCODE_PTR(
					static_cast< AvmCode * >( other.raw_pointer() ) )

			release_acquire( other.raw_pointer() );
		}
		return( *this );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline bool operator==(const AvmCode & other) const
	{
		return( other.operator==( raw_pointer() ) );
	}

	inline bool operator==(const AvmCode * other) const
	{
		return( (mPTR == other)
				|| ((mPTR != nullptr)
					&& raw_pointer()->operator==( other ) ) );
	}


	inline bool operator==(const BFCode & other) const
	{
		return( (mPTR == other.raw_pointer())
				|| ((mPTR != nullptr)
					&& raw_pointer()->operator==( other.raw_pointer() ) ) );
	}

	inline bool operator==(const BF & other) const
	{
		return( (mPTR == other.raw_pointer())
				|| ((mPTR != nullptr)
					&& other.is< AvmCode >()
					&& raw_pointer()->operator==(
							other.to_ptr< AvmCode >() ) ) );
	}


	inline bool operator!=(const AvmCode & other) const
	{
		return( other.operator!=( raw_pointer() ) );
	}

	inline bool operator!=(const AvmCode * other) const
	{
		return( (mPTR != other)
				&& ((mPTR == nullptr)
					|| raw_pointer()->operator!=( other ) ) );
	}


	inline bool operator!=(const BFCode & other) const
	{
		return( (mPTR != other.raw_pointer())
				&& ((mPTR == nullptr)
					|| raw_pointer()->operator!=( other.raw_pointer() ) ) );
	}

	inline bool operator!=(const BF & other) const
	{
		return( (mPTR != other.raw_pointer())
				&& ((mPTR == nullptr)
					|| (other.is< AvmCode >()
						&& raw_pointer()->operator!=(
								other.to_ptr< AvmCode >() ) ) ) );
	}

	/**
	 * COMPARISON
	 */
	inline bool isEQ(const BF & other) const
	{
		return( BF::isEQ(other) );
	}

	inline bool isEQ(const BFCode & other) const
	{
		return( (mPTR == other.mPTR)
				|| ((mPTR != nullptr)
					&& raw_pointer()->isEQ( other.raw_pointer() ) ) );
	}


	inline bool isNEQ(const BF & other) const
	{
		return( BF::isNEQ(other) );
	}

	inline bool isNEQ(const BFCode & other) const
	{
		return( not BFCode::isEQ(other) );
	}


public:

	/**
	 * SETTER
	 * mOperands
	 */
	inline void append(const BF & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->append(anElement);
	}

	inline void append(const List< BF > & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->append( anElement );
	}

	inline void append(const List< BFCode > & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->append( anElement );
	}

	inline void append(const AvmCode::OperandCollectionT & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->append( anElement );
	}


	inline void appendFlat(const BF & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->appendFlat( anElement );
	}


	inline const AvmCode::OperandCollectionT & getOperands() const
	{
		return( static_cast< AvmCode * >( mPTR )->getOperands() );
	}

	inline AvmCode::OperandCollectionT & getOperands()
	{
		return( static_cast< AvmCode * >( mPTR )->getOperands() );
	}


	/**
	 * GETTER - SETTER
	 * for element in mOperands
	 */
	inline BF & operator[](std::size_t offset)
	{
		return( static_cast< AvmCode * >( mPTR )->at(offset) );
	}

	inline  const BF & operator[](std::size_t offset) const
	{
		return( static_cast< AvmCode * >( mPTR )->at(offset) );
	}


	inline void set(std::size_t offset, const BF & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->set( offset , anElement );
	}


	/**
	 * GETTER
	 * for iterators
	 */
	inline AvmCode::iterator begin()
	{
		return( static_cast< AvmCode * >( mPTR )->begin() );
	}

	inline AvmCode::iterator end()
	{
		return( static_cast< AvmCode * >( mPTR )->end() );
	}

	inline AvmCode::const_iterator begin() const
	{
		return( static_cast< AvmCode * >( mPTR )->begin() );
	}

	inline AvmCode::const_iterator end() const
	{
		return( static_cast< AvmCode * >( mPTR )->end() );
	}


	/**
	 * GETTER - SETTER
	 * for mOperator
	 */
	inline const Operator * getOperator() const
	{
		return( static_cast< AvmCode * >( mPTR )->getOperator() );
	}

	inline AVM_OPCODE getAvmOpCode() const
	{
		return( static_cast< AvmCode * >( mPTR )->getAvmOpCode() );
	}


	/**
	 * DEFAULT NULL
	 */
	static BFCode REF_NULL;

	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual void toStream(OutStream & out) const override
	{
		if( mPTR != nullptr )
		{
			static_cast< AvmCode * >( mPTR )->toStream(out);
		}
		else
		{
			out << TAB << "BFCode<null>" << EOL_FLUSH;
		}
	}

	// Due to [-Woverloaded-virtual=]
	using BF::toStream;


	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss(indent);

		toStream(oss);

		return( oss.str() );
	}

	inline virtual std::string str() const override
	{
		return( ( mPTR == nullptr ) ?  "BFCode<null>" :
				static_cast< AvmCode * >( mPTR )->str() );
	}


	inline virtual void AVM_DEBUG_REF_COUNTER(OutStream & out) const override
	{
		if( mPTR != nullptr )
		{
			mPTR->AVM_DEBUG_REF_COUNTER(out);
		}
		else
		{
			out << "BFCode<null, ref:0>" << std::flush;
		}
	}

	inline virtual std::string AVM_DEBUG_REF_COUNTER() const override
	{
		return( ( mPTR != nullptr )  ?  mPTR->AVM_DEBUG_REF_COUNTER() :
				"BFCode<null, ref:0>" );
	}

	inline virtual std::string strRefCount() const
	{
		return( ( mPTR != nullptr )  ?  mPTR->strRefCount() :
				"BFCode<null, ref:0>" );
	}

};


/**
 * operator<<
 */
AVM_OS_STREAM( BFCode )


}

#endif /*AVMCODE_H_*/
