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

#include <printer/OutStream.h>

#include <util/avm_assert.h>
#include <util/avm_injector.h>
#include <util/avm_numeric.h>
#include <util/avm_string.h>


namespace sep
{


typedef avm_uint8_t          class_kind_t;


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
	// TYPE
	FORM_XFSP_DATATYPE_KIND,

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
	FORM_COM_ROUTE_DATA_KIND,
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

struct ClassKindInfo :
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ClassKindInfo )
{

	friend class ClassKindInfoInitializer;


public:
	/**
	 * ATTRIBUTES
	 */
	static ClassKindInfo * TYPE_UNDEFINED_INFO;

	const class_kind_t mKIND;

	const char * mTNAME;

	std::string mNAME;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClassKindInfo(class_kind_t aClassKind, const char * tname);

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

static class ClassKindInfoInitializer
{

public:
	////////////////////////////////////////////////////////////////////////////////
	// INITIALIZATION / DESTRUCTION  INVARIANT
	////////////////////////////////////////////////////////////////////////////////

	ClassKindInfoInitializer();

	~ClassKindInfoInitializer();


public:
	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////

	static void load();
	static void dispose();


public:
	/**
	 * ATTRIBUTES
	 */
	static const class_kind_t TYPE_UNDEFINED_ID = 0;

	static class_kind_t TYPE_NEW_ID;


	static std::vector< ClassKindInfo * > * CKI_TABLE;


	template< class T >
	static ClassKindInfo & classKindInfo()
	{
		static ClassKindInfo _TYPE_INFO_( TYPE_NEW_ID++ , typeid(T).name() );

		return( _TYPE_INFO_ );
	}


	static void toStreamTable(OutStream & os, const std::string & msg);

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

	friend class ClassKindInfoInitializer;

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


#define CLASS_KIND_T( T )  ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND

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
	~ClassKindImpl()
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
				<< static_cast< avm_size_t>( mClassKind ) << " , "
				<< CKII_TABLE_INFO( mClassKind )->mNAME
				<< " >" );
	}


	////////////////////////////////////////////////////////////////////////////
	// CLASS KIND CHECKER & CAST API
	////////////////////////////////////////////////////////////////////////////

	// Check if BF is a handle to a T, including base classes.
	template< typename T >
	inline bool is() const
	{
		return( ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND == mClassKind );
	}

	template< typename T >
	inline bool isnot() const
	{
		return( ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND != mClassKind );
	}

	// Check if BF is a handle to a T, not including base classes.
	template< typename T >
	inline bool is_exactly() const
	{
		return( ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND == mClassKind );
	}

	template< typename T >
	inline bool isnot_exactly() const
	{
		return( ClassKindInfoImpl< T >::CLASS_KIND_INFO.mKIND != mClassKind );
	}

	// Check if BF is a handle to a T, not including specific classes.
	template< typename T >
	inline bool is_strictly() const
	{
		return( is< T >() );
	}

	template< typename T >
	inline bool isnot_strictly() const
	{
		return( not is_strictly< T >() );
	}


	// cast as specified pointer
	template< typename T >
	inline T * as()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( is< T >() )
				<< "Invalid type casting :> static_cast< "
				<< CKII_TABLE_INFO_T( T )->mNAME
				<< " * >( "
				<< CKII_TABLE_INFO( mClassKind )->mNAME
				<< " * )"
				<< SEND_EXIT;

		return( static_cast< T * >( this ) );
	}

	template< typename T >
	inline const T * as() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( is< T >() )
				<< "Invalid type casting :> static_cast< "
				<< CKII_TABLE_INFO_T( T )->mNAME
				<< " * >( "
				<< CKII_TABLE_INFO( mClassKind )->mNAME
				<< " * )"
				<< SEND_EXIT;

		return( static_cast< const T * >( this ) );
	}


	template< typename T >
	inline T * to()
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< T * >( this ) );
	}

	template< typename T >
	inline const T * to() const
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< const T * >( this ) );
	}

	template< typename T >
	inline const T & to_ref() const
	{
		// NO ASSERT
		// Assumes that the type checking has been done by the user
		return( static_cast< const T & >( *this ) );
	}

};



/**
 * CLASS KIND CHECKER
 * CAST
 */
class Machine;
template<> bool ClassKindImpl::is< Machine    >() const;
template<> bool ClassKindImpl::isnot< Machine >() const;


class BehavioralElement;
template<> bool ClassKindImpl::is< BehavioralElement    >() const;
template<> bool ClassKindImpl::isnot< BehavioralElement >() const;

class PropertyElement;
template<> bool ClassKindImpl::is< PropertyElement    >() const;
template<> bool ClassKindImpl::isnot< PropertyElement >() const;


class ObjectElement;
template<> bool ClassKindImpl::is< ObjectElement    >() const;
template<> bool ClassKindImpl::isnot< ObjectElement >() const;


class Number;
template<> bool ClassKindImpl::is< Number    >() const;
template<> bool ClassKindImpl::isnot< Number >() const;


class BuiltinQueue;
template<> bool ClassKindImpl::is< BuiltinQueue    >() const;
template<> bool ClassKindImpl::isnot< BuiltinQueue >() const;


class BuiltinList;
template<> bool ClassKindImpl::is< BuiltinList    >() const;
template<> bool ClassKindImpl::isnot< BuiltinList >() const;


class BuiltinVector;
template<> bool ClassKindImpl::is< BuiltinVector    >() const;
template<> bool ClassKindImpl::isnot< BuiltinVector >() const;


class BuiltinArray;
template<> bool ClassKindImpl::is< BuiltinArray    >() const;
template<> bool ClassKindImpl::isnot< BuiltinArray >() const;

template<> bool ClassKindImpl::is_strictly< BuiltinArray    >() const;
template<> bool ClassKindImpl::isnot_strictly< BuiltinArray >() const;


class BuiltinContainer;
template<> bool ClassKindImpl::is< BuiltinContainer    >() const;
template<> bool ClassKindImpl::isnot< BuiltinContainer >() const;


class BuiltinCollection;
template<> bool ClassKindImpl::is< BuiltinCollection    >() const;
template<> bool ClassKindImpl::isnot< BuiltinCollection >() const;


class BuiltinForm;
template<> bool ClassKindImpl::is< BuiltinForm    >() const;
template<> bool ClassKindImpl::isnot< BuiltinForm >() const;


class BaseInstanceForm;
template<> bool ClassKindImpl::is< BaseInstanceForm    >() const;
template<> bool ClassKindImpl::isnot< BaseInstanceForm >() const;



class AvmProgram;
template<> bool ClassKindImpl::is< AvmProgram    >() const;
template<> bool ClassKindImpl::isnot< AvmProgram >() const;

class BaseAvmProgram;
template<> bool ClassKindImpl::is< BaseAvmProgram    >() const;
template<> bool ClassKindImpl::isnot< BaseAvmProgram >() const;


class BaseSymbolTypeSpecifier;
template<> bool ClassKindImpl::is< BaseSymbolTypeSpecifier    >() const;
template<> bool ClassKindImpl::isnot< BaseSymbolTypeSpecifier >() const;

class BaseTypeSpecifier;
template<> bool ClassKindImpl::is< BaseTypeSpecifier    >() const;
template<> bool ClassKindImpl::isnot< BaseTypeSpecifier >() const;


class BaseCompiledForm;
template<> bool ClassKindImpl::is< BaseCompiledForm    >() const;
template<> bool ClassKindImpl::isnot< BaseCompiledForm >() const;



class RamBuffer;
template<> bool ClassKindImpl::is< RamBuffer    >() const;
template<> bool ClassKindImpl::isnot< RamBuffer >() const;


class BaseBufferQueue;
template<> bool ClassKindImpl::is< BaseBufferQueue    >() const;
template<> bool ClassKindImpl::isnot< BaseBufferQueue >() const;


class BaseBufferForm;
template<> bool ClassKindImpl::is< BaseBufferForm    >() const;
template<> bool ClassKindImpl::isnot< BaseBufferForm >() const;


} /* namespace sep */
#endif /* BASE_CLASSKINDINFO_H_ */
