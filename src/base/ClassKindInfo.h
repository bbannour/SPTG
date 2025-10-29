/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASE_CLASSKINDINFO_H_
#define BASE_CLASSKINDINFO_H_

#include <iomanip>
#include <string>
#include <typeinfo>
#include <vector>

#include <base/Injector.h>

#include <util/avm_assert.h>
#include <util/avm_numeric.h>


namespace sep
{

class OutStream;


typedef std::uint8_t          class_kind_t;


enum ENUM_CLASS_KIND
{
	// UNDEFINED
	FORM_UNDEFINED_KIND = 0,

	// BUILTIN
	FORM_BUILTIN_BOOLEAN_KIND,

	FORM_BUILTIN_CHARACTER_KIND,

	FORM_BUILTIN_INTEGER_KIND,
	FORM_BUILTIN_RATIONAL_KIND,
	FORM_BUILTIN_FLOAT_KIND,

	FORM_BUILTIN_STRING_KIND,
	FORM_BUILTIN_IDENTIFIER_KIND,
	FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND,

	// OPERATOR
	FORM_OPERATOR_KIND,

	// EXPRESSION , STATEMENT
	FORM_AVMCODE_KIND,


	// EXECUTABLE OBJECT INSTANCE
	FORM_INSTANCE_BUFFER_KIND,
	FORM_INSTANCE_CONNECTOR_KIND,
	FORM_INSTANCE_DATA_KIND,
	FORM_INSTANCE_MACHINE_KIND,
	FORM_INSTANCE_PORT_KIND,

	// EXECUTABLE OBJECT
	FORM_AVMLAMBDA_KIND,
	FORM_AVMPROGRAM_KIND,
	FORM_AVMTRANSITION_KIND,
	FORM_EXECUTABLE_MACHINE_KIND,
	FORM_EXECUTABLE_SYSTEM_KIND,

	// RUNTIME OBJECT
	FORM_RUNTIME_ID_KIND,
	FORM_RUNTIME_KIND,

	// EXECUTION OBJECT
	FORM_EXECUTION_CONFIGURATION_KIND,
	FORM_EXECUTION_DATA_KIND,
	FORM_EXECUTION_CONTEXT_KIND,

	// WORKFLOW CONFIGURATION
	FORM_WOBJECT_KIND,

	// LIA or FSP
	FORM_UFI_KIND,

	// XLIA or XFSP
	FORM_XFSP_BUFFER_KIND,
	FORM_XFSP_CHANNEL_KIND,
	FORM_XFSP_COM_POINT_KIND,
	FORM_XFSP_COM_ROUTE_KIND,
	FORM_XFSP_CONNECTOR_KIND,
	FORM_XFSP_MACHINE_KIND,
//	FORM_XFSP_INSTANCE_KIND,
	FORM_XFSP_PACKAGE_KIND,
	FORM_XFSP_PORT_KIND,
	FORM_XFSP_ROUTINE_KIND,
	FORM_XFSP_SYSTEM_KIND,
	FORM_XFSP_TRANSITION_KIND,
	FORM_XFSP_VARIABLE_KIND,
	// DATA TYPE
	FORM_XFSP_DATATYPE_KIND,

	// FUNCTION
	FORM_XFSP_FUNCTION_KIND,

	// TYPE SPECIFIER
	FORM_TYPE_SPECIFIER_KIND,

	// ARRAY
	FORM_ARRAY_BOOLEAN_KIND,
	FORM_ARRAY_CHARACTER_KIND,
	FORM_ARRAY_INTEGER_KIND,
	FORM_ARRAY_RATIONAL_KIND,
	FORM_ARRAY_FLOAT_KIND,
	FORM_ARRAY_STRING_KIND,
	FORM_ARRAY_IDENTIFIER_KIND,
	FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND,
	FORM_ARRAY_BF_KIND,

	// CONTAINER
	FORM_CONTAINER_VECTOR_KIND,
	FORM_CONTAINER_REVERSE_VECTOR_KIND,
	FORM_CONTAINER_LIST_KIND,
	FORM_CONTAINER_SET_KIND,
	FORM_CONTAINER_BAG_KIND,
	FORM_CONTAINER_FIFO_KIND,
	FORM_CONTAINER_LIFO_KIND,

	// BUFFER
	FORM_BUFFER_FIFO_KIND,
	FORM_BUFFER_LIFO_KIND,
	FORM_BUFFER_MULTI_FIFO_KIND,
	FORM_BUFFER_MULTI_LIFO_KIND,

	FORM_BUFFER_MULTISET_KIND,
	FORM_BUFFER_SET_KIND,

	FORM_BUFFER_BROADCAST_KIND,
	FORM_BUFFER_RAM_KIND,

	// COM
	FORM_MESSAGE_KIND,
	FORM_ROUTER_KIND,
	FORM_ROUTING_DATA_KIND,

	// OTHER
	FORM_EXEC_FILTER_FORMULA_DATA_KIND,

	// EXECUTION TRACE
	FORM_TRACE_POINT_KIND,
	FORM_TRACE_SEQUENCE_KIND,

	// DESTROYED
	FORM_DESTROYED_KIND
};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CLASS KIND INFO
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

struct ClassKindInfo final :
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ClassKindInfo )
{

public:
	/**
	 * ATTRIBUTES
	 */
	static ClassKindInfo * TYPE_UNDEFINED_INFO;

	const class_kind_t mKIND;

	std::string mTNAME;

	std::string mNAME;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClassKindInfo(class_kind_t aClassKind,
			const std::string & tname, const std::string & aName);

	/**
	 * info
	 */
	std::string info() const;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CLASS KIND INFO INITIALIZER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

static struct ClassKindInfoInitializer
{

	/**
	 * CONSTRUCTOR
	 * Default
	 * Ensures equality between ENUM_CLASS_KIND literal
	 * and ClassKindInfo::mKIND of base classes !
	 * Due to dependencies, implementation in main/StaticInitializer
	 */
	ClassKindInfoInitializer();

	/**
	 * DESTRUCTOR
	 */
	~ClassKindInfoInitializer();


	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////

	static void load();
	static void dispose();


	/**
	 * ATTRIBUTES
	 */
	static std::uint16_t NIFTY_COUNTER;

	static const class_kind_t TYPE_UNDEFINED_ID = 0;


	static class_kind_t generateNewTypeID()
	{
		static class_kind_t NEW_TYPE_ID = TYPE_UNDEFINED_ID;

		// assert( NEW_TYPE_ID == 0 ) for ClassKindInfo::TYPE_UNDEFINED_INFO

		return( ++NEW_TYPE_ID );
	}


	static std::vector< ClassKindInfo * > * CKI_TABLE;


	template< class T >
	static ClassKindInfo & classKindInfo(
			ENUM_CLASS_KIND aTypeId = FORM_UNDEFINED_KIND,
			std::string atypeName = "")
	{
		static ClassKindInfo _TYPE_INFO_(
				(aTypeId != FORM_UNDEFINED_KIND) ? aTypeId : generateNewTypeID(),
				typeid(T).name(),
				atypeName.empty() ? typeid(T).name() : atypeName );

		return( _TYPE_INFO_ );
	}


	/**
	 * Loader
	 * Checking equality between ENUM_CLASS_KIND literal
	 * and ClassKindInfo::mKIND of base classes !
	 * Mandatory, call by load()
	 * Due to dependencies, implementation in main/StaticInitializer
	 */
	static void checkingAssertions();

	// For debug trace
	static void toStreamTable(OutStream & out, const std::string & msg);

	// Mandatory for debug trace in constructor ClassKindInfoInitializer()
	static void toStreamTable(const std::string & msg);

}  CLASS_KIND_INFO_INITIALIZER;


#define CKII_TABLE_INFO( aClassKind )  \
		(*ClassKindInfoInitializer::CKI_TABLE)[ aClassKind ]

#define CKII_TABLE_INFO_T( aClassKind )  \
		(*ClassKindInfoInitializer::CKI_TABLE)  \
				[ ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND ]



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CLASS KIND INFO IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< class T >
class ClassKindInfoImpl
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClassKindInfoImpl()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ClassKindInfoImpl()
	{
		//!! NOTHING
	}


	/**
	 * ATTRIBUTES
	 */
	static ClassKindInfo & CLASS_KIND_INFO;


	/**
	 * GETTER
	 * classKind
	 * classKindName
	 */
	inline static std::string info()
	{
		return( ClassKindInfoImpl< T >::CLASS_KIND_INFO.info() );
	}

};

template< class T >
ClassKindInfo & ClassKindInfoImpl< T >::CLASS_KIND_INFO =
		ClassKindInfoInitializer::classKindInfo< T >();


#define CLASS_KIND_T( T )       ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND

#define CLASS_KIND_NAME_T( T )  ClassKindInfoImpl< T >::CLASS_KIND_INFO.mNAME




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CLASS KIND DEFAULT IMPLEMENTATION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ClassKindImpl
{

	friend class ClassKindInfoInitializer;

protected:
	/**
	 * ATTRIBUTES
	 */
	class_kind_t mClassKind;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClassKindImpl(class_kind_t aClassKind)
	: mClassKind( aClassKind )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClassKindImpl(const ClassKindImpl & aCKI)
	: mClassKind( aCKI.mClassKind )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ClassKindImpl()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CLASS KIND CHECKER & CAST API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER
	 * classKind
	 * classKindName
	 */
	inline class_kind_t classKind() const
	{
		return( mClassKind );
	}

	inline const std::string & classKindName() const
	{
		return( CKII_TABLE_INFO( mClassKind )->mNAME );
	}

	inline std::string classKindInfo() const
	{
		return( OSS() << "classKindInfo< "
				<< static_cast< std::size_t>( mClassKind ) << " , "
				<< CKII_TABLE_INFO( mClassKind )->mNAME
				<< " >" );
	}


	////////////////////////////////////////////////////////////////////////////
	// CLASS KIND CHECKER & CAST API
	////////////////////////////////////////////////////////////////////////////

	template< typename T >
	inline bool is_a() const
	{
		return( dynamic_cast< const T * >( this ) != nullptr );
	}

	template< typename T >
	inline bool is_not_a() const
	{
		return( dynamic_cast< const T * >( this ) == nullptr );
	}

	template< typename T >
	inline bool is_exactly_a() const
	{
		return( typeid(T) == typeid(*this) );
	}

	template< typename T >
	inline bool is_not_exactly_a() const
	{
		return( typeid(T) != typeid(*this) );
	}


#define TEST_TYPEID_TRACE( method , tester )   \
	AVM_OS_LOG << "==kind== " << (ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND == mClassKind)   \
		<< "  " << #tester << "< T > " << tester< T >() << " \tthis( " << typeid( *this ).name() \
		<< " )->" << #method << "< " << typeid( T ).name() << " >" << std::endl << std::flush;

	// Check if BF is a handle to a T, including base classes.
	template< typename T >
	inline bool is() const
	{
//		TEST_TYPEID_TRACE( is , is_a )

		return( (ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND == mClassKind)
				|| is_a< T >() );
	}

	template< typename T >
	inline bool isnot() const
	{
//		TEST_TYPEID_TRACE( isnot , is_not_a )

		return( is_not_a< T >() );
	}

	// Check if BF is a handle to a T, not including base classes.
	template< typename T >
	inline bool is_exactly() const
	{
//		TEST_TYPEID_TRACE( is_exactly , is_exactly_a )

		return( (ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND == mClassKind)
				|| is_exactly_a< T >() );
	}

	template< typename T >
	inline bool isnot_exactly() const
	{
//		TEST_TYPEID_TRACE( isnot_exactly , is_not_exactly_a )

		return( (ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND != mClassKind)
				|| is_not_exactly_a< T >() );
	}

	// Check if BF is a handle to a T, not including specific classes.

	template< typename T >
	inline bool is_strictly() const
	{
//		TEST_TYPEID_TRACE( is_strictly , is_a )

		return( (ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND == mClassKind)
				|| is_a< T >() );
	}

	template< typename T >
	inline bool isnot_strictly() const
	{
//		TEST_TYPEID_TRACE( isnot_strictly , is_not_a )

		return( is_not_a< T >() );
	}



#define ASSERT_TYPE_CASTING( method )                       \
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( method< T >() )     \
				<< "Invalid type casting :> static_cast< "  \
				<< typeid( T ).name() << " * >( "           \
				<< typeid( *this ).name() << " * )"         \
				<< SEND_EXIT;

//		AVM_OS_ASSERT_FATAL_ERROR_EXIT( is< T >() )
//				<< "Invalid type casting :> static_cast< "
//				<< CKII_TABLE_INFO_T( T )->mNAME
//				<< " * >( "
//				<< CKII_TABLE_INFO( mClassKind )->mNAME
//				<< " * )"
//				<< SEND_EXIT;

	/**
	 * safe cast
	 * Check type compliance & null pointer
	 */
	// cast as specified pointer
	template< typename T >
	inline T * as_ptr()
	{
		ASSERT_TYPE_CASTING( is )

		return( static_cast< T * >( this ) );
	}

	template< typename T >
	inline const T * as_ptr() const
	{
		ASSERT_TYPE_CASTING( is )

		return( static_cast< const T * >( this ) );
	}

	// cast as specified reference
	template< typename T >
	inline T & as()
	{
		ASSERT_TYPE_CASTING( is )

		return( static_cast< T & >( *this ) );
	}

	template< typename T >
	inline const T & as() const
	{
		ASSERT_TYPE_CASTING( is )

		return( static_cast< const T & >( *this ) );
	}


	/**
	 * unsafe cast
	 * Assume type compliance & null pointer checking
	 */
	// cast to specified pointer
	template< typename T >
	inline T * to_ptr()
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< T * >( this ) );
	}

	template< typename T >
	inline const T * to_ptr() const
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< const T * >( this ) );
	}

	// cast to specified reference
	template< typename T >
	inline T & to()
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< T & >( *this ) );
	}

	template< typename T >
	inline const T & to() const
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< const T & >( *this ) );
	}

};


} /* namespace sep */
#endif /* BASE_CLASSKINDINFO_H_ */
