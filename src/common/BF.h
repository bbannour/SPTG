/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BF_H_
#define BF_H_

#include <base/ClassKindInfo.h>
#include <base/SmartPointer.h>
#include <common/Element.h>

#include <util/avm_assert.h>
#include <util/avm_string.h>


#define AVM_DEBUG_BF_POINTER  true
#undef AVM_DEBUG_BF_POINTER

#if defined(AVM_DEBUG_BF_POINTER)

	#define AVM_DECLARE_DEBUG_BF_PTR         public: std::string dbgPTR;


	#define AVM_STR_BF_PTR( ptr )   ( (ptr != nullptr) ? ptr->str() : "BF<null>" )

	#define AVM_INIT_DEBUG_BF_PTR_NULL       , dbgPTR( "BF<null>" )

	#define AVM_INIT_DEBUG_BF_PTR( ptr )     , dbgPTR( AVM_STR_BF_PTR(ptr) )

	#define AVM_COPY_DEBUG_BF_PTR( bf )      , dbgPTR( bf.dbgPTR )

	#define AVM_ASSIGN_DEBUG_BF_PTR( ptr )   dbgPTR = AVM_STR_BF_PTR(ptr);

#else

	#define AVM_INIT_DEBUG_BF_PTR_NULL

	#define AVM_DECLARE_DEBUG_BF_PTR

	#define AVM_INIT_DEBUG_BF_PTR( ptr )

	#define AVM_COPY_DEBUG_BF_PTR( ptr )

	#define AVM_ASSIGN_DEBUG_BF_PTR( ptr )

#endif


namespace sep
{


class BFCode;

class Operator;

class RuntimeID;

//class Symbol;
//class Type;



class BF :
		public SmartPointer< Element , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BF )
{


private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< Element , DestroyElementPolicy >  base_this_type;

	AVM_DECLARE_DEBUG_BF_PTR

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BF() throw()
	: base_this_type()
	AVM_INIT_DEBUG_BF_PTR_NULL
	{
		//!! NOTHING
	}

	explicit BF(Element * anElement)
	: base_this_type( anElement )
	AVM_INIT_DEBUG_BF_PTR( anElement )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BF(const BF & anElement)
	: base_this_type( anElement )
	AVM_COPY_DEBUG_BF_PTR( anElement )
	{
		//!! NOTHING
	}


	static std::uint64_t INSTANCE_COUNTER_ASP;

	template< class U >
	BF(const SmartPointer< U , DestroyElementPolicy > & other)
	: base_this_type( other )
	{
		//!! NOTHING
		++INSTANCE_COUNTER_ASP;
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BF()
	{
		//!! NOTHING
	}


	void finalize();


	/**
	* NUMERIC or SIMPLE TYPE TEST & CAST
	*/
	virtual bool isBoolean() const final;
	virtual bool toBoolean() const final;

	/**
	 * COMPARISON
	 * with TRUE & FALSE
	 */
	virtual bool isEqualFalse() const final;
	virtual bool isNotEqualFalse() const final;

	virtual bool isEqualTrue() const final;
	virtual bool isNotEqualTrue()const final;


	virtual bool isEqualZero() const final;
	virtual bool isEqualOne() const final;

	virtual bool isNumber() const final;
	virtual bool isNumeric() const final;

	virtual bool isExpression() const final;


	virtual bool isInt32() const final;
	virtual std::int32_t toInt32() const final;

	virtual bool isInt64() const final;
	virtual std::int64_t toInt64() const final;


	virtual bool isInteger() const final;
	virtual avm_integer_t toInteger() const final;

	virtual bool isWeakInteger() const final
	{
		return( isInteger() );
	}

	virtual bool isPosInteger() const final;

	virtual bool isUInteger() const final;
	virtual avm_uinteger_t toUInteger() const final;


	virtual bool isRational() const final;
	virtual avm_integer_t toDenominator() const final;
	virtual avm_integer_t toNumerator() const final;

	virtual bool isWeakRational() const final
	{
		return( isRational() || isWeakInteger() );
	}


	virtual bool isFloat() const final;
	virtual avm_float_t toFloat() const final;

	virtual bool isWeakFloat() const final
	{
		return( isFloat() || isWeakRational() );
	}


	virtual bool isReal() const final;
	virtual avm_real_t toReal() const final;

	inline virtual bool isWeakReal() const final
	{
		return( isReal() || isWeakFloat() );
	}



	virtual bool isCharacter() const final;
	virtual char toCharacter() const final;

	bool isBuiltinString() const;
	std::string toBuiltinString() const;


	bool isIdentifier() const;
	std::string toIdentifier() const;

	bool isUfi() const;
	std::string toUfi() const;

	inline bool isUfid() const
	{
		return( isUfi() || isIdentifier() );
	}
	std::string toUfid() const;

	bool isEnumSymbol() const;
	std::string strEnumSymbol() const;

	bool isUFID() const;

	bool isBuiltinValue() const;

	bool isConstValue() const;



	/**
	 * REFERENCE
	 * CAST
	 */
	BFCode & bfCode() ;

	const BFCode & bfCode() const;

	const RuntimeID & bfRID() const;



	/**
	 * MEMORY MANAGEMENT
	 */

	void incrRefCount() const
	{
		if( mPTR != nullptr )
		{
			mPTR->incrRefCount();
		}
	}


	/**
	 * GETTER
	 * ClassKindInfo
	 */
	inline class_kind_t classKind() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BF::classKind() !!!"
				<< SEND_EXIT;

		return( mPTR->classKind() );
	}

	inline const std::string & classKindName() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BF::classKindName() !!!"
				<< SEND_EXIT;

		return( mPTR->classKindName() );
	}

	inline std::string classKindInfo() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BF::classKindInfo() !!!"
				<< SEND_EXIT;

		return( mPTR->classKindInfo() );
	}


	////////////////////////////////////////////////////////////////////////////
	// TYPE CHECKER
	////////////////////////////////////////////////////////////////////////////

	// Check if BF is a handle to a T, including base classes.
	template<class T >
	inline bool is() const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in BF::is< T >() !!!"
//				<< SEND_EXIT;

		return( (mPTR != nullptr) && mPTR->is< T >() );
	}

	template<class T >
	inline bool isnot() const
	{
		return(( mPTR == nullptr) || mPTR->isnot< T >() );
	}

	// Check if BF is a handle to a T, not including base classes.
	template< class T >
	inline bool is_weakly() const
	{
		return( (mPTR == nullptr) || mPTR->is< T >() );
	}

	// Check if BF is a handle to a T, not including base classes.
	template< class T >
	inline bool is_exactly() const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in BF::is_exactly< T >() !!!"
//				<< SEND_EXIT;

		return( (mPTR != nullptr) && mPTR->is_exactly< T >() );
	}

	template< class T >
	inline bool isnot_exactly() const
	{
		return( (mPTR == nullptr) || mPTR->isnot_exactly< T >() );
	}

	// Check if BF is a handle to a T, not including specific classes.
	template< class T >
	inline bool is_strictly() const
	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in BF::is_strictly< T >() !!!"
//				<< SEND_EXIT;

		return( (mPTR != nullptr) && mPTR->is_strictly< T >() );
	}

	template< class T >
	inline bool isnot_strictly() const
	{
		return( (mPTR == nullptr) || mPTR->isnot_strictly< T >() );
	}


	// cast BF as specified reference
	template< class T >
	inline T & as()
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BF::as_ref< T >() !!!"
				<< SEND_EXIT;

		return( mPTR->as< T >() );
	}

	template< class T >
	inline const T & as() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BF::as< T >() !!!"
				<< SEND_EXIT;

		return( mPTR->as< T >() );
	}

	// cast BF as specified pointer
	template< class T >
	inline T * as_ptr() const
	{
		// previous:> AVM_OS_ASSERT_WARNING_ALERT
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BF::as_ptr< T >() !!!"
				<< SEND_EXIT;

		return( (mPTR != nullptr) ? mPTR->as_ptr< T >() : nullptr );
	}


	template< class T >
	inline T & to()
	{
		return( mPTR->to< T >() );
	}

	template< class T >
	inline const T & to() const
	{
		return( mPTR->to< T >() );
	}

	template< class T >
	inline T * to_ptr() const
	{
		return( mPTR->to_ptr< T >() );
	}


	// cast BF as derived BF
//	template< class T >
//	inline T & as_bf()
//	{
//		return( static_cast< T & >( *this ) );
//	}

	template< class T >
	inline const T & as_bf() const
	{
		return( static_cast< const T & >( *this ) );
	}



	/**
	 * CAST
	 */
//	inline operator Element * () const
//	{
//		return( mPTR );
//	}

	// Desactive call of << delete >> using compiler ambiguous mecanism
//	inline operator void * () const
//	{
//		return( mPTR );
//	}


//	template< class T >
//	inline operator T * ()
//	{
//		return( static_cast< T * >( mPTR ) );
//	}
//
//	/**
//	 * OPERATORS
//	 */
//	template< class T >
//	inline T * operator-> ()
//	{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
//				<< "raw_pointer in BF::operator->< T >() !!!"
//				<< SEND_EXIT;
//
//		return( static_cast< T * >( mPTR ) );
//	}


	/**
	 * GETTER - SETTER
	 * for container of BF
	 */
	// Generally with range check
	inline const BF & at(std::size_t offset) const
	{
		return( mPTR->at(offset) );
	}

	inline BF & at(std::size_t offset)
	{
		return( mPTR->at(offset) );
	}

	// move to contained element at position < offset >
	inline void moveAt(std::size_t offset)
	{
		mPTR->decrRefCount();

		mPTR = mPTR->at( offset ).mPTR;

		mPTR->incrRefCount();
	}


	// Generally without range check
	inline BF & operator[](std::size_t offset)
	{
		return( mPTR->operator[](offset) );
	}

	// Generally without range check
	inline const BF & operator[](std::size_t offset) const
	{
		return( mPTR->operator[](offset) );
	}


	inline BF & getWritable()
	{
		base_this_type::makeWritable();
		return( *this );
	}

	inline BF & getWritable(std::size_t offset)
	{
		return( mPTR->getWritable(offset) );
	}

	inline void makeWritable()
	{
		base_this_type::makeWritable();
	}

	inline void makeWritable(std::size_t offset)
	{
		mPTR->makeWritable( offset );
	}

	// move to writable contained element at position < offset >
	inline void moveAtWritable(std::size_t offset)
	{
		mPTR->decrRefCount();

		mPTR = mPTR->getWritable( offset ).mPTR;

		mPTR->incrRefCount();
	}


	inline void set(const BF & bf)
	{
		base_this_type::release_acquire( bf.mPTR );
	}

	inline void set(std::size_t offset, const BF & bf)
	{
		mPTR->set(offset, bf);
	}

//	inline void mw_set(std::size_t offset, const BF & bf)
//	{
//		base_this_type::makeWritable();
//		mPTR->set(offset, bf);
//	}


	inline std::size_t size() const
	{
		return( mPTR->size() );
	}


	/**
	 * ASSIGNMENT
	 */
//	template< class U >
//	inline BF & operator=(
//			const SmartPointer< U , DestroyElementPolicy > & other)
//	{
//		if( mPTR != other.raw_pointer() )
//		{
//			AVM_ASSIGN_DEBUG_BF_PTR( other.raw_pointer() )
//
//			release_acquire( other.raw_pointer() );
//		}
//		return( *this );
//	}
//
//	// Symbol
//	BF & operator=(const Symbol & aSymbol);
//
//	// Type
//	BF & operator=(const Type & aType);

	inline BF & operator=(pointer_t aPtr)
	{
		if( mPTR != aPtr )
		{
			AVM_ASSIGN_DEBUG_BF_PTR( aPtr )

			release( aPtr );
		}
		return( *this );
	}


	inline void renew(pointer_t aPtr)
	{
		if( mPTR != aPtr )
		{
			release( aPtr );
		}
	}

	inline void newincr(pointer_t aPtr)
	{
		if( mPTR != aPtr )
		{
			release_acquire( aPtr );
		}
	}

	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline bool operator==(const BF & other) const
	{
		return( (mPTR == other.mPTR) || isEQ(other) );
	}

	inline bool operator==(const Element & aPtr) const
	{
		return( (mPTR == &aPtr) || mPTR->isEQ(aPtr) );
	}

	inline bool operator==(const Element * aPtr) const
	{
		return( (mPTR == aPtr) ||
				((aPtr != nullptr) && (mPTR != nullptr) && mPTR->isEQ(*aPtr)) );
	}


	inline bool operator!=(const BF & other) const
	{
		return( (mPTR != other.mPTR) || isNEQ(other) );
	}

	inline bool operator!=(const Element & aPtr) const
	{
		return( (mPTR != &aPtr) && mPTR->isNEQ(aPtr) );
	}

	inline bool operator!=(const Element * aPtr) const
	{
		return( (mPTR != aPtr) &&
				((mPTR == nullptr) || (aPtr == nullptr) || mPTR->isNEQ(*aPtr)) );
	}


	/**
	 * POINTER TRIVIALLY EQUAL COMPARISON
	 */
	inline bool isTEQ(const Element & bf) const
	{
		return( mPTR == (& bf) );
	}

	inline bool isTEQ(const Element * bf) const
	{
		return( mPTR == bf );
	}

	inline bool isTEQ(const BF & other) const
	{
		return( mPTR == other.mPTR );
	}


	inline bool isNTEQ(const Element & bf) const
	{
		return( mPTR != (& bf) );
	}

	inline bool isNTEQ(const Element * bf) const
	{
		return( mPTR != bf );
	}

	inline bool isNTEQ(const BF & other) const
	{
		return( mPTR != other.mPTR );
	}


	/**
	 * COMPARISON
	 */
	int compare(const BF & other) const;

	int compare_share(BF & other);


	bool isEQ(const BF & other) const;

	inline bool isNEQ(const BF & other) const
	{
		return( not isEQ(other) );
	}


	bool strEQ(const BF & other) const
	{
		return( (mPTR == other.mPTR)
				|| ((mPTR != nullptr) && (other.mPTR != nullptr)
					&& (mPTR->str() == other.mPTR->str())) );
	}

	bool strNEQ(const BF & other) const
	{
		return( (mPTR != other.mPTR)
				&& ((mPTR == nullptr) || (other.mPTR == nullptr)
					|| (mPTR->str() != other.mPTR->str())) );
	}



	/**
	 * BUILD NEW EXPRESSION
	 */
	BF & opExpr(const Operator * anOperator, const BF & arg);

	BF & eqExpr(const BF & arg);
	BF & neqExpr(const BF & arg);

	BF & ltExpr(const BF & arg);
	BF & lteExpr(const BF & arg);

	BF & gtExpr(const BF & arg);
	BF & gteExpr(const BF & arg);


	BF & andExpr(const BF & arg);
	BF & orExpr(const BF & arg);
	BF & notExpr();

	BF & addExpr(const BF & arg);
	BF & incrExpr(avm_uinteger_t val = 1);

	BF & minusExpr(const BF & arg);
	BF & uminusExpr();
	BF & decrExpr(avm_uinteger_t val = 1);

	BF & multExpr(const BF & arg);
	BF & powExpr(const BF & arg);
	BF & divExpr(const BF & arg);
	BF & invExpr();



	/**
	 * DEFAULT NULL
	 */
	static BF REF_NULL;


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const
	{
		if( mPTR != nullptr )
		{
			mPTR->toStream( os );
		}
		else
		{
			os << TAB << "BF<null>" << EOL_FLUSH;
		}
	}

	virtual void toStream(PairOutStream & os) const
	{
		if( mPTR != nullptr )
		{
			mPTR->toStream( os.OS1 );
			mPTR->toStream( os.OS2 );
		}
		else
		{
			os << TAB << "BF<null>" << EOL_FLUSH;
		}
	}

	virtual void toStream(TripleOutStream & os) const
	{
		if( mPTR != nullptr )
		{
			mPTR->toStream( os.OS1 );
			mPTR->toStream( os.OS2 );
			mPTR->toStream( os.OS3 );
		}
		else
		{
			os << TAB << "BF<null>" << EOL_FLUSH;
		}
	}


	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream( oss );

		return( oss.str() );
	}

	inline virtual std::string wrapString(
			const WrapData & wrapData = DEFAULT_WRAP_DATA,
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream woss(wrapData, indent);

		toStream( woss );

		return( woss.str() );
	}


	/**
	 * strHeader
	 */
	virtual std::string strHeader() const
	{
		StringOutStream oss;

		strHeader( oss );

		return( oss.str() );
	}

	virtual void strHeader(OutStream & os) const;

	virtual void strHeader(PairOutStream & os) const
	{
		strHeader( os.OS1 );
		strHeader( os.OS2 );
	}

	virtual void strHeader(TripleOutStream & os) const
	{
		toStream( os.OS1 );
		toStream( os.OS2 );
		toStream( os.OS3 );
	}


	inline virtual std::string str() const
	{
		return( ( mPTR != nullptr ) ? mPTR->str() : ("BF<null>") );
	}

	inline virtual std::string wrapStr(
			const WrapData & wrapData = DEFAULT_WRAP_DATA) const final
	{
		StringOutStream woss(DEFAULT_WRAP_DATA, AVM_STR_INDENT);

		toStream( woss << IGNORE_FIRST_TAB );

		return( woss.str() );
	}


	// LEFT TRIM the result
	inline virtual std::string _str() const
	{
		if( mPTR != nullptr )
		{
			std::string strTmp = mPTR->str();

			return( StringTools::ltrim(strTmp) );

		}

		return( "BF<null>" );
	}

	// RIGTH TRIM the result
	inline virtual std::string str_() const
	{
		if( mPTR != nullptr )
		{
			std::string strTmp = mPTR->str();

			return( StringTools::rtrim(strTmp) );

		}

		return( "BF<null>" );
	}

	// LEFT & RIGTH TRIM the result
	inline virtual std::string _str_() const
	{
		if( mPTR != nullptr )
		{
			std::string strTmp = mPTR->str();

			return( StringTools::trim(strTmp) );

		}

		return( "BF<null>" );
	}


	inline virtual std::string strNum(
			uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( ( mPTR != nullptr ) ? mPTR->strNum(precision) : "BF<null>" );
	}


	inline virtual void AVM_DEBUG_REF_COUNTER(OutStream & os) const
	{
		if( mPTR != nullptr )
		{
			mPTR->AVM_DEBUG_REF_COUNTER(os);
		}
		else
		{
			os << "BF<null, ref:0>" << std::flush;
		}
	}

	inline virtual std::string AVM_DEBUG_REF_COUNTER() const
	{
		return( ( mPTR != nullptr ) ?
				mPTR->AVM_DEBUG_REF_COUNTER() : "BF<null, ref:0>" );
	}


private:

	/** Share equal objects between expressions.
	 */
	inline void share(BF & other)
	{
		if( getRefCount() <= other.getRefCount() )
		{
			acquirePointer( other.mPTR );
		}
		else
		{
			other.acquirePointer( mPTR );
		}
	}

};


/**
 * operator<<
 */
AVM_OS_STREAM( BF )

////////////////////////////////////////////////////////////////////////////////
// INCR_BF
////////////////////////////////////////////////////////////////////////////////


#define INCR_BF(A)   \
		sep::BF( sep::incrReferenceCount(A) )


}

#endif /* BF_H_ */
