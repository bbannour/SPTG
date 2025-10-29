/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_ASSERT_H_
#define AVM_ASSERT_H_


#include <exception>

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <string>

#include <printer/OutStream.h>
#include <util/avm_string.h>
#include <util/avm_util.h>


namespace sep
{

/**
 * EXIT EXCEPTION
 */
struct AvmExitException final :  public std::exception
{
	/**
	 * ATTRIBUTES
	 */
	StringOutStream OS;

	AVM_EXIT_CODE_KIND mExitCode;

	std::string mDescription;

	// for debug
	std::string mSourcePath;
	long mLine;

	/**
	 * CONSTRUCTOR / DESTRUCTOR
	 */
	AvmExitException( AVM_EXIT_CODE_KIND anExitCode,
			const std::string & aDescription = "",
			const std::string & aSourcePath = "", long aLine = -1 )
	: std::exception( ),
	OS( WrapData( 80, 0, 4, "\n\t" ) , AvmIndent("" , "\t", "\n") ),
	mExitCode( anExitCode ),
	mDescription( aDescription ),
	mSourcePath( aSourcePath ),
	mLine( aLine )
	{
		prologue();
	}

	AvmExitException( const AvmExitException & anExitException )
	: std::exception( ),
	OS( WrapData( 80, 0, 4, "\n\t" ) , AvmIndent("" , "\t", "\n") ),
	mExitCode( anExitException.mExitCode ),
	mDescription( anExitException.mDescription ),
	mSourcePath( anExitException.mSourcePath ),
	mLine( anExitException.mLine )
	{
		OS << anExitException.OS.str();
	}


	virtual ~AvmExitException() throw()
	{
		//!! NOTHING
	}

	/**
	 * API
	 */
	inline virtual const char * what() const throw() override
	{
		return( mDescription.c_str() );
	}

	inline virtual std::string info() const
	{
		return( OS.str() );
	}

	void prologue();


	/**
	 * operator<<
	 */
	template< class T >
	inline AvmExitException & operator<<( const T & x )
	{
		OS << x;

		return( *this );
	}


	inline AvmExitException & operator<<(AvmEXIT_SIGNAL exit_signal)
	{
		mExitCode = exit_signal.code;

		throw( *this );

		return( *this );
	}

	inline AvmExitException & operator<<(
			void (*op) ( AvmExitException & os ) )
	{
		op( *this );

		return( *this );
	}


	inline AvmExitException & operator<<(
			void (*op) ( OutStream & os ) )
	{
		OS.operator<<( op );

		return( *this );
	}

	inline AvmExitException & operator<<(
			std::ostream & (*op) ( std::ostream & ) )
	{
		OS.operator<<( op );

		return( *this );
	}

};


extern AvmExitException AVM_OS_THROW_EXCEPTION;


inline AvmExitException & osAssert(
		AVM_EXIT_CODE_KIND anExitCode,
		const std::string & aDescription,
		const std::string & aSourcePath, long aLine )
{
	AVM_OS_THROW_EXCEPTION.OS.str("");
	AVM_OS_THROW_EXCEPTION.mExitCode = anExitCode;
	AVM_OS_THROW_EXCEPTION.mDescription = aDescription;
	AVM_OS_THROW_EXCEPTION.mSourcePath = aSourcePath;
	AVM_OS_THROW_EXCEPTION.mLine = aLine;

	AVM_OS_THROW_EXCEPTION.prologue();

	return( AVM_OS_THROW_EXCEPTION );
}


extern AvmExitException AVM_OS_THROW_ALERT;

inline AvmExitException & osAlert(
		AVM_EXIT_CODE_KIND anExitCode,
		const std::string & aDescription,
		const std::string & aSourcePath, long aLine )
{
	AVM_OS_THROW_ALERT.OS.str("");
	AVM_OS_THROW_ALERT.mExitCode = anExitCode;
	AVM_OS_THROW_ALERT.mDescription = aDescription;
	AVM_OS_THROW_ALERT.mSourcePath = aSourcePath;
	AVM_OS_THROW_ALERT.mLine = aLine;

	AVM_OS_THROW_ALERT.prologue();

	return( AVM_OS_THROW_ALERT );
}


inline void SEND_EXIT(AvmExitException & aee)
{
AVM_IF_DEBUG_ENABLED

	AVM_OS_WARN << std::endl << aee.info() << std::endl
			<< REPEAT( '<' , 80 ) << std::endl << std::flush;

AVM_DEBUG_ELSE

	AVM_OS_CERR << std::endl << aee.info() << std::endl
			<< REPEAT( '<' , 80 ) << std::endl << std::flush;

AVM_ENDIF_DEBUG_ENABLED

	throw( aee );
}

inline void SEND_ALERT(AvmExitException & aee)
{
AVM_IF_DEBUG_ENABLED

	AVM_OS_WARN << std::endl << aee.info() << std::endl
			<< REPEAT( '<' , 80 ) << std::endl << std::flush;

AVM_DEBUG_ELSE

	AVM_OS_CERR << std::endl << aee.info() << std::endl
			<< REPEAT( '<' , 80 ) << std::endl << std::flush;

AVM_ENDIF_DEBUG_ENABLED
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


/**
 * AVM OSTREAM EXIT
 */
#define AVM_OS_EXIT( KIND )  \
	osAssert( AVM_EXIT_##KIND##_CODE, QUOTEME(SYMBEX_##KIND), __FILE__, __LINE__ )

#define AVM_OS_FATAL_ERROR_EXIT  AVM_OS_EXIT( FATAL_ERROR )


/**
 * AVM OSTREAM ASSERT EXIT
 */
#define AVM_OS_ASSERT_EXIT( KIND , assert_cond )   \
	if( not (assert_cond) )  \
		osAssert( AVM_EXIT_##KIND##_CODE, QUOTEME(KIND), __FILE__, __LINE__ )


#define AVM_OS_ASSERT_OUT_OF_MEMORY_EXIT( aPtr )   \
	AVM_OS_ASSERT_EXIT( OUT_OF_MEMORY , ((aPtr) != nullptr) )


#define AVM_OS_ASSERT_FATAL_ERROR_EXIT( assert_cond )  \
	AVM_OS_ASSERT_EXIT( FATAL_ERROR , assert_cond )


#define AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT( index , aSize )      \
	AVM_OS_ASSERT_EXIT( FATAL_ERROR , ((aSize > index) && (index >= 0)) ) \
			<< " index:" << index << " is not in [ 0 , " << aSize  \
			<< " [ : Unbound array index !!!"


#define AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset , aSize )  \
	AVM_OS_ASSERT_EXIT( FATAL_ERROR , ((aSize > offset) && (offset >= 0)) ) \
			<< " offset:" << offset << " is not in [ 0, " << aSize << " [ : "

#define AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aPtr )     \
	AVM_OS_ASSERT_EXIT( FATAL_ERROR , ((aPtr) != nullptr) )  \
			<< "Unexpected a <null> "

#define AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aPtr )  \
	AVM_OS_ASSERT_EXIT( FATAL_ERROR , aPtr.valid() )         \
			<< "Unexpected a <null> "

#define AVM_OS_ASSERT_FATAL_EMPTY_COLLECTION_EXIT( aPtr )  \
	AVM_OS_ASSERT_EXIT( FATAL_ERROR , aPtr.nonempty() )    \
			<< "Unexpected an empty "


/**
 * AVM OSTREAM ALERT
 */
#define AVM_OS_ALERT( DESC )  \
	osAlert( AVM_EXIT_GOOD_CODE, DESC, __FILE__, __LINE__ )


#define AVM_OS_ERROR_ALERT      AVM_OS_ALERT( "ERROR"   )

#define AVM_OS_WARNING_ALERT    AVM_OS_ALERT( "WARNING" )

#define AVM_OS_TODO_ALERT       AVM_OS_ALERT( "TODO"    )


/**
 * AVM OSTREAM ASSERT ALERT
 */
#define AVM_OS_ASSERT_ALERT( DESC , assert_cond )   \
	if( not (assert_cond) )  \
		osAlert( AVM_EXIT_GOOD_CODE, DESC, __FILE__, __LINE__ )

#define AVM_OS_ASSERT_ERROR_ALERT( assert_cond )    \
	AVM_OS_ASSERT_ALERT( "ERROR" , assert_cond )

#define AVM_OS_ASSERT_WARNING_ALERT( assert_cond )  \
	AVM_OS_ASSERT_ALERT( "WARNING" , assert_cond )


/**
 * AVM_ERROR_COUNT
 * AVM_WARNING_COUNT
 */
extern std::size_t AVM_ERROR_COUNT;

extern std::size_t AVM_WARNING_COUNT;


} /* namespace sep */
#endif /* AVM_ASSERT_H_ */
