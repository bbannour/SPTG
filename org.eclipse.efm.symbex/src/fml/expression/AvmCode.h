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

#include <common/AvmPointer.h>
#include <common/Element.h>

//#include <collection/BFContainer.h>
#include <collection/List.h>
#include <collection/Vector.h>

#include <computer/instruction/AvmInstruction.h>


#include <fml/operator/Operator.h>


namespace sep
{

class BaseTypeSpecifier;


class AvmCode :
		public Element ,
		public Vector< BF > ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AvmCode )
{

	AVM_DECLARE_CLONABLE_CLASS( AvmCode )

public:
	/**
	 * TYPEDEF
	 */
	typedef Vector< BF >                                this_container_type;

	typedef this_container_type::const_iterator         const_iterator;

	typedef this_container_type::iterator               iterator;

	typedef this_container_type::const_reverse_iterator const_reverse_iterator;

	typedef this_container_type::reverse_iterator       reverse_iterator;

	typedef this_container_type::size_type              size_type;


protected:
	/*
	 * ATTRIBUTES
	 */
	Operator * mOperator;

	AvmInstruction * mInstruction;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCode()
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type(),
	mOperator( NULL ),
	mInstruction( NULL )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmCode(const AvmCode & anElement)
	: Element( anElement ),
	this_container_type( anElement ),
	mOperator( anElement.mOperator ),
	mInstruction( (anElement.mInstruction == NULL) ? NULL
			: new AvmInstruction( *(anElement.mInstruction) ) )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	AvmCode(Operator * anOperator)
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type( ),
	mOperator( anOperator ),
	mInstruction( NULL )
	{
		//!! NOTHING
	}

	AvmCode(Operator * anOperator, const BF & arg)
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type( arg ),
	mOperator( anOperator ),
	mInstruction( NULL )
	{
		//!! NOTHING
	}

	AvmCode(Operator * anOperator, const BF & arg1, const BF & arg2)
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type( arg1 , arg2 ),
	mOperator( anOperator ),
	mInstruction( NULL )
	{
		//!! NOTHING
	}

	AvmCode(Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3)
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type( arg1 , arg2 , arg3 ),
	mOperator( anOperator ),
	mInstruction( NULL )
	{
		//!! NOTHING
	}

	AvmCode(Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3, const BF & arg4)
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type( arg1 , arg2 , arg3 , arg4 ),
	mOperator( anOperator ),
	mInstruction( NULL )
	{
		//!! NOTHING
	}

	AvmCode(Operator * anOperator, const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4, const BF & arg5)
	: Element( CLASS_KIND_T( AvmCode ) ),
	this_container_type( arg1 , arg2 , arg3 , arg4 , arg5 ),
	mOperator( anOperator ),
	mInstruction( NULL )
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
	 * this_container_type
	 */
	inline this_container_type & getArgs()
	{
		return( *this );
	}

	inline const this_container_type & getArgs() const
	{
		return( *this );
	}


	/**
	 * APPEND
	 * this_container_type
	 */
	inline void append(const BF & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!" !!!"
//				<< SEND_EXIT;

		this_container_type::append( anElement );
	}

	inline void append(const this_container_type & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		this_container_type::append( anElement );
	}

	inline void appendTail(const this_container_type & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		this_container_type::appendTail( anElement );
	}

	inline void append(const List< BF > & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		this_container_type::append( anElement );
	}

	inline void append(const List< BFCode > & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		this_container_type::append( anElement );
	}


	inline void appendFlat(const BF & anElement)
	{
		if( anElement.is< AvmCode >()
			&& getOperator()->isWeakAssociative()
			&& (anElement.to_ptr< AvmCode >()->getOperator() == getOperator()) )
		{
			append( anElement.to_ptr< AvmCode >()->getArgs() );
		}
		else
		{
			append( anElement );
		}
	}


	/**
	 * GETTER - SETTER
	 * for element of this_container_type
	 */
	inline virtual BF & at(avm_size_t offset)
	{
		return( this_container_type::at(offset) );
	}

	inline virtual const BF & at(avm_size_t offset) const
	{
		return( this_container_type::at(offset) );
	}


	inline AvmCode * codeAt(avm_size_t offset)
	{
		return( this_container_type::at(offset).as_ptr< AvmCode >() );
	}

	inline const AvmCode * codeAt(avm_size_t offset) const
	{
		return( this_container_type::at(offset).as_ptr< AvmCode >() );
	}


	virtual BF & operator[](avm_size_t offset)
	{
		return( this_container_type::operator[](offset) );
	}

	virtual const BF & operator[](avm_size_t offset) const
	{
		return( this_container_type::operator[](offset) );
	}


	inline virtual BF & getWritable(avm_size_t offset)
	{
		this_container_type::at(offset).makeWritable();

		return( this_container_type::operator[](offset) );
	}

	inline virtual void makeWritable(avm_size_t offset)
	{
		this_container_type::at(offset).makeWritable();
	}


	inline virtual void safe_set(avm_size_t index, const BF & anElement)
	{
		this_container_type::operator[](index) = anElement;
	}

	inline virtual void set(avm_size_t index, const BF & anElement)
	{
//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isUnique() )
//				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
//				<< strRefCount() << " " << str() << " !!!"
//				<< SEND_EXIT;

		////////////////////////////////////////////////////////////////////////
		//!!! OPTIMISATION
		////////////////////////////////////////////////////////////////////////
//		this_container_type::set(index, anElement);

		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( index , size() )
				<< SEND_EXIT;

		this_container_type::operator[](index) = anElement;
	}

	inline avm_size_t size() const
	{
		return( this_container_type::size() );
	}


	/**
	 * GETTER - SETTER
	 * for mOperator
	 */
	inline Operator * getOperator() const
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


	inline bool hasOperator() const
	{
		return( mOperator != NULL );
	}

	inline bool isOperator(Operator * op) const
	{
		return( mOperator->isEQ( op ) );
	}

	inline bool isnotOperator(Operator * op) const
	{
		return( mOperator->isNEQ( op ) );
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

	inline bool isOpCode(Operator * op) const
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

	inline bool sameOperator(AvmCode * aCode) const
	{
		return( mOperator->isEQ( aCode->mOperator ) );
	}


	inline bool isnotOpCode(AVM_OPCODE opCode) const
	{
		return( mOperator->isnotOpCode( opCode ) );
	}


	inline void setOperator(Operator * anOperator)
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
		return( mInstruction != NULL );
	}


	inline AvmInstruction * newEmptyInstruction()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInstruction == NULL )
				<< "Unexpected a code with AvmInstruction: "
				<< toStringWithBytecode()
				<< SEND_EXIT;

		return( mInstruction = new AvmInstruction() );
	}

	inline AvmInstruction * newInstruction(avm_size_t aSize)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInstruction == NULL )
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

	inline bool operator==(AvmCode * other) const
	{
		return( (other != NULL) && AvmCode::isEQ( *other ) );
	}

	inline bool operator!=(const AvmCode & other) const
	{
		return( (this != &other) && (not AvmCode::isEQ( other )) );
	}

	inline bool operator!=(AvmCode * other) const
	{
		return( (other == NULL)
				|| ((this != other)
					&& (not AvmCode::isEQ( *other ) ) ) );
	}


	bool isEQ(const AvmCode & other) const;

	inline bool isEQ(AvmCode * other) const
	{
		return( (other != NULL) && AvmCode::isEQ( *other ) );
	}


	/**
	 * Serialization
	 */
	std::string strDebug(const AvmIndent & indent = AVM_SPC_INDENT) const
	{
		StringOutStream oss(indent);

		toDebug( oss );

		return( oss.str() );
	}

	OutStream & toDebug(OutStream & out) const;

	OutStream & toStreamWithBytecode(OutStream & out) const;

	std::string toStringWithBytecode(
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

	inline virtual void toStream(OutStream & out) const
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

	void prettyPrinterFunctional(OutStream & out) const;
	void prettyPrinterInfix(OutStream & out) const;
	void prettyPrinterPrefix(OutStream & out) const;
	void prettyPrinterSuffix(OutStream & out) const;

	static void prettyPrinter(OutStream & out,
			const BF & arg, bool isStatement = true);

	static void prettyPrinter(OutStream & out,
			const BF & arg, BaseTypeSpecifier * aType);

	static void prettyPrinterCondition(OutStream & out, const BF & arg);

	static void prettyPrinterBlock(OutStream & out, const BF & arg);


	/**
	 * toString
	 */
	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

//		toStream(oss);
		prettyPrinter(oss);

		return( oss.str() );
	}

	inline virtual std::string str() const
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


	#define AVM_STR_BFCODE_PTR( ptr )  ( (ptr != NULL) ? ptr->str() : "BFCode<null>" )

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
	AVM_INIT_DEBUG_BFCODE_PTR( NULL )
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
//			static_cast< const AvmCode * >( other.raw_pointer() ) : NULL )
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
	BFCode(Operator * anOperator)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator) ) )
	{
		//!! NOTHING
	}

	BFCode(Operator * anOperator, const BF & arg)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg) ) )
	{
		//!! NOTHING
	}

	BFCode(Operator * anOperator, const BF & arg1, const BF & arg2)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2) ) )
	{
		//!! NOTHING
	}

	BFCode(Operator * anOperator, const BF & arg1,
			const BF & arg2, const BF & arg3)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2, arg3) ) )
	{
		//!! NOTHING
	}

	BFCode(Operator * anOperator, const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4)
	: BF( AVM_ASSIGN_EXPR_DEBUG_BFCODE_PTR(
			new AvmCode(anOperator, arg1, arg2, arg3, arg4) ) )
	{
		//!! NOTHING
	}

	BFCode(Operator * anOperator, const BF & arg1, const BF & arg2,
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
		return( static_cast< AvmCode * >( mPTR )  );
	}


	inline AvmCode * raw_pointer() const
	{
		return( static_cast< AvmCode * >( mPTR )  );
	}


	/**
	 * OPERATORS
	 */
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

	inline bool operator==(AvmCode * other) const
	{
		return( (mPTR == other)
				|| ((mPTR != NULL)
					&& raw_pointer()->operator==( other ) ) );
	}


	inline bool operator==(const BFCode & other) const
	{
		return( (mPTR == other.raw_pointer())
				|| ((mPTR != NULL)
					&& raw_pointer()->operator==( other.raw_pointer() ) ) );
	}

	inline bool operator==(const BF & other) const
	{
		return( (mPTR == other.raw_pointer())
				|| ((mPTR != NULL)
					&& other.is< AvmCode >()
					&& raw_pointer()->operator==(
							other.to_ptr< AvmCode >() ) ) );
	}


	inline bool operator!=(const AvmCode & other) const
	{
		return( other.operator!=( raw_pointer() ) );
	}

	inline bool operator!=(AvmCode * other) const
	{
		return( (mPTR != other)
				&& ((mPTR == NULL)
					|| raw_pointer()->operator!=( other ) ) );
	}


	inline bool operator!=(const BFCode & other) const
	{
		return( (mPTR != other.raw_pointer())
				&& ((mPTR == NULL)
					|| raw_pointer()->operator!=( other.raw_pointer() ) ) );
	}

	inline bool operator!=(const BF & other) const
	{
		return( (mPTR != other.raw_pointer())
				&& ((mPTR == NULL)
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
				|| ((mPTR != NULL)
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
	 * this_container_type
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

	inline void append(AvmCode::this_container_type & anElement)
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


	inline AvmCode::this_container_type & getArgs()
	{
		return( static_cast< AvmCode * >( mPTR )->getArgs() );
	}


	inline void set(avm_size_t index, const BF & anElement)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( isWritable() )
				<< "ILLEGAL MODIFICATION OF A NON UNIQUE REFERENCE :> "
				<< strRefCount() << " " << str() << " !!!"
				<< SEND_EXIT;

		static_cast< AvmCode * >( mPTR )->set( index , anElement );
	}

	/**
	 * GETTER
	 * for BFCode
	 */
	inline virtual BFCode & codeAt(avm_size_t offset)
	{
		return( static_cast< AvmCode * >( mPTR )->at(offset).bfCode() );
	}

	inline virtual const BFCode & codeAt(avm_size_t offset) const
	{
		return( static_cast< AvmCode * >( mPTR )->at(offset).bfCode() );
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
	 * GETTER
	 * for reverse_iterators
	 */
	inline AvmCode::reverse_iterator rbegin()
	{
		return( static_cast< AvmCode * >( mPTR )->rbegin() );
	}

	inline AvmCode::reverse_iterator rend()
	{
		return( static_cast< AvmCode * >( mPTR )->rend() );
	}

	inline AvmCode::const_reverse_iterator rbegin() const
	{
		return( static_cast< AvmCode * >( mPTR )->rbegin() );
	}

	inline AvmCode::const_reverse_iterator rend() const
	{
		return( static_cast< AvmCode * >( mPTR )->rend() );
	}


	/**
	 * GETTER - SETTER
	 * for mOperator
	 */
	inline Operator * getOperator() const
	{
		return( static_cast< AvmCode * >( mPTR )->getOperator() );
	}

	inline AVM_OPCODE getAvmOpCode() const
	{
		return( static_cast< AvmCode * >( mPTR )->getAvmOpCode() );
	}

	inline bool hasOperator() const
	{
		return( static_cast< AvmCode * >( mPTR )->hasOperator() );
	}

	inline void setOperator(Operator * anOperator)
	{
		static_cast< AvmCode * >( mPTR )->setOperator( anOperator );
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
	inline virtual void toStream(OutStream & out) const
	{
		if( mPTR != NULL )
		{
			static_cast< AvmCode * >( mPTR )->toStream(out);
		}
		else
		{
			out << TAB << "BFCode<null>" << EOL_FLUSH;
		}
	}


	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream(oss);

		return( oss.str() );
	}

	inline virtual std::string str() const
	{
		return( ( mPTR == NULL ) ?  "BFCode<null>" :
				static_cast< AvmCode * >( mPTR )->str() );
	}


	inline virtual void AVM_DEBUG_REF_COUNTER(OutStream & out) const
	{
		if( mPTR != NULL )
		{
			mPTR->AVM_DEBUG_REF_COUNTER(out);
		}
		else
		{
			out << "BFCode<null, ref:0>" << std::flush;
		}
	}

	inline virtual std::string AVM_DEBUG_REF_COUNTER() const
	{
		return( ( mPTR != NULL )  ?  mPTR->AVM_DEBUG_REF_COUNTER() :
				"BFCode<null, ref:0>" );
	}

	inline virtual std::string strRefCount() const
	{
		return( ( mPTR != NULL )  ?  mPTR->strRefCount() :
				"BFCode<null, ref:0>" );
	}

};


/**
 * operator<<
 */
AVM_OS_STREAM( BFCode )


}

#endif /*AVMCODE_H_*/
