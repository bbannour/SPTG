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

#ifndef PRINTER_OUTSTREAM_H_
#define PRINTER_OUTSTREAM_H_

#include <fstream>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <stack>
#include <string>

#include <util/avm_debug.h>
#include <util/avm_util.h>

#include <printer/Manipulators.h>
#include <printer/WrapStream.h>


namespace sep
{


#define AVM_CHAR_SPC           " "

#define AVM_CHAR_TAB           " "
//#define AVM_CHAR_TAB         "\t"


class ParameterManager;
class Workflow;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// OutStream
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

extern std::ostream * _avm_os_null_;


class OutStream
{

public:

	/**
	 * ATTRIBUTE
	 */
	std::ostream * OS;

	WrapOstream * WRAP_OS;

	AvmIndent INDENT;

	std::size_t DEPTH;

	std::stack< AvmIndent > STACK;

	SymbexValueCSS VALUE_ARRAY_CSS;
	SymbexValueCSS VALUE_PARAMS_CSS;
	SymbexValueCSS VALUE_STRUCT_CSS;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	OutStream(std::ostream * os = NULL,
			const std::string & tabs   = "",
			const std::string & _char_ = "\t",
			const std::string & eol    = "\n")
	: OS( os ),
	WRAP_OS( NULL ),
	INDENT( tabs, _char_ , eol ),
	DEPTH( 0 ),
	STACK( ),
	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
	{
		STACK.push( INDENT );
	}

	OutStream(std::ostream * os, const AvmIndent & indent)
	: OS( os ),
	WRAP_OS( NULL ),
	INDENT( indent ),
	DEPTH( 0 ),
	STACK( ),
	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
	{
		STACK.push( INDENT );
	}

	OutStream(std::ostream * os, const OutStream & aos)
	: OS( os ),
	WRAP_OS( NULL ),
	INDENT( aos.INDENT ),
	DEPTH( 0 ),
	STACK( ),
	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
	{
		STACK.push( INDENT );
	}


	OutStream(std::ostream & os, const AvmIndent & indent)
	: OS( & os ),
	WRAP_OS( NULL ),
	INDENT( indent ),
	DEPTH( 0 ),
	STACK( ),
	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
	{
		STACK.push( INDENT );
	}

//	OutStream(std::ostream & os,
//			const WrapData & wrapData, const AvmIndent & indent)
//	: OS( & os ),
//	WRAP_OS( new WrapOstream(os, wrapData) ),
//	INDENT( indent ),
//	DEPTH( 0 ),
//	STACK( ),
//	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
//	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
//	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
//	{
//		STACK.push( INDENT );
//
//		OS = WRAP_OS;
//	}

	OutStream(std::ostream & os, const OutStream & aos)
	: OS( & os ),
	WRAP_OS( NULL ),
	INDENT( aos.INDENT ),
	DEPTH( 0 ),
	STACK( ),
	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
	{
		STACK.push( INDENT );
	}

	OutStream(std::ostream & os,
			const std::string & tabs   = "",
			const std::string & _char_ = "\t",
			const std::string & eol    = "\n")
	: OS( & os ),
	WRAP_OS( NULL ),
	INDENT(tabs, _char_ , eol ),
	DEPTH( 0 ),
	STACK( ),
	VALUE_ARRAY_CSS ( "[ ", " , ", " ]" ),
	VALUE_PARAMS_CSS( "( ", " , ", " )" ),
	VALUE_STRUCT_CSS( "{ ", " , ", " }" )
	{
		STACK.push( INDENT );
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~OutStream()
	{
		delete( WRAP_OS );
	}


	/**
	 * OS
	 * delete / destroy
	 */
	inline virtual void deleteOS()
	{
		delete( OS );

		OS = NULL;
	}

	inline void destroy()
	{
		if( (OS != NULL) && (OS != _avm_os_null_) &&
			(OS != &(std::cout)) && (OS != &(std::cerr)) )
		{
			if( OS->good() )
			{
				(*OS) << std::flush;
			}

			deleteOS();
		}
	}


	/**
	 * OS
	 * fail / good
	 */
	inline virtual bool fail()
	{
		return( (OS == NULL) || OS->fail() );
	}

	inline virtual bool good()
	{
		return( (OS != NULL) && OS->good() );
	}


	/**
	 * OS
	 * isOpen / open / reopen
	 */
	inline bool isOpen()
	{
		return( (OS != NULL) &&
				(dynamic_cast< std::ofstream * >(OS) != NULL) &&
				dynamic_cast< std::ofstream * >(OS)->is_open() );
	}

	inline bool open(const std::string & aFileLocation,
			std::ios_base::openmode aMode)
	{
		OS = new std::ofstream(aFileLocation.c_str(), aMode);

		return( (OS != NULL) && OS->good() );
	}

	inline bool reopen(const std::string & aFileLocation,
			std::ios_base::openmode aMode)
	{
		if( isOpen() )
		{
			destroy();
		}

		return( open(aFileLocation.c_str(), aMode) );
	}


	/**
	 * TEST
	 * If is preferable...
	 */
	inline bool preferablySTR()
	{
		return( INDENT.preferablySTR() );
	}

	inline bool preferablyFQN()
	{
		return( INDENT.preferablyFQN() );
	}


	/**
	 * restore default Symbex Value CSS
	 */
	inline void restoreSymbexValueCSS()
	{
		VALUE_ARRAY_CSS  = DEFAULT_SYMBEX_VALUE_ARRAY_CSS;
		VALUE_PARAMS_CSS = DEFAULT_SYMBEX_VALUE_PARAMS_CSS;
		VALUE_STRUCT_CSS = DEFAULT_SYMBEX_VALUE_STRUCT_CSS;
	}

	inline void setSymbexValueCSS(const SymbexValueCSS & vac,
			const SymbexValueCSS & vpc, const SymbexValueCSS & vsc)
	{
		VALUE_ARRAY_CSS  = vac;
		VALUE_PARAMS_CSS = vpc;
		VALUE_STRUCT_CSS = vsc;
	}

	/**
	 * flush()
	 */
	inline virtual void flush() const
	{
		if( WRAP_OS != NULL )
		{
			WRAP_OS->flush();
		}

		if( OS != NULL )
		{
			OS->flush();
		}
	}


	/**
	 * operator<<
	 */
	// Need for polymorphism in functor like TAB or EOL family
	inline virtual OutStream & operator<<( const std::string & x )
	{
		( *OS ) << x;

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<( const T & x )
	{
		( *OS ) << x;

		return( *this );
	}


	inline OutStream & operator<<( void (*op) ( OutStream & ) )
	{
		op( *this );

		return( *this );
	}

	inline OutStream & operator<<(
			std::ostream & (*op) ( std::ostream & ) )
	{
		op( *OS );

		return( *this );
	}


	inline static void backspace(std::ostream * os)
	{
		if( os == &(std::cout) )
		{
			( *os ) << '\b';
		}
		else if( os != NULL )
		{
			os->seekp(-1, std::ios::end);
		}
	}

	inline virtual void backspace()
	{
		OutStream::backspace( OS  );
	}


	inline void push()
	{
		if( /*STACK.empty() ||*/ (STACK.top() != INDENT) )
		{
			STACK.push( INDENT );
		}
		else
		{
			++(STACK.top().REF_COUNT);
		}
	}

	inline void pop()
	{
		INDENT = STACK.top();

		if( STACK.top().REF_COUNT == 1 )
		{
			STACK.pop();
		}
		else
		{
			--(STACK.top().REF_COUNT);
		}
	}


	/**
	 * MANIPULATORS
	 */
	inline OutStream & operator<<(const WrapData & newWrap)
	{
		if( good() )
		{
			if( WRAP_OS != NULL )
			{
				delete( WRAP_OS );
			}

			OS->flush();

			WRAP_OS = new WrapOstream(*OS, newWrap);

			OS = WRAP_OS;
		}

		return( *this );
	}

	inline void end_wrap()
	{
		if( good() && (WRAP_OS != NULL) )
		{
			OS = WRAP_OS->mOS;

			OS->flush();

			delete( WRAP_OS );

			WRAP_OS = NULL;
		}
	}


	inline OutStream & operator<<(const AvmIndent & newIndent)
	{
		push();

		INDENT = newIndent;

		return( *this );
	}


//	inline OutStream & operator<<(const AvmTAB & tab)
//	{
//		( *OS ) << INDENT.TABS;
//
//		for( ; tab.count > 1  ; --tab.count )
//		{
//			( *OS ) << INDENT.CHAR;
//		}
//
//		return( *this );
//	}
//
//	inline OutStream & operator<<(const AvmEOL & eol)
//	{
//		for( ; eol.count > 0  ; --eol.count )
//		{
//			( *OS ) << INDENT.EOL;
//		}
//
//		return( *this );
//	}


	inline OutStream & operator<<(const AvmINCR & incr)
	{
		OutStream::incr( incr.count );

		return( *this );
	}

	inline OutStream & operator<<(const AvmDECR & decr)
	{
		OutStream::decr( decr.count );

		return( *this );
	}


	/**
	 * <reference|pointer>.toStream( os )
	 */
	template< class T >
	inline OutStream & operator<<(const _refStream_< T > & obj)
	{
		obj.ref.toStream( *this );

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const _ptrStream_< T > & obj)
	{
		if( obj.ptr != NULL )
		{
			obj.ptr->toStream( *this );
		}
		else
		{
			( *OS ) << INDENT.TABS << "to_stream(<null>)" << INDENT.EOL;
		}

		return( *this );
	}


	/**
	 * <reference|pointer>.strHeader( os )
	 */
	template< class T >
	inline OutStream & operator<<(const _refHeader_< T > & obj)
	{
		obj.ref.strHeader( *this );

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const _ptrHeader_< T > & obj)
	{
		if( obj.ptr != NULL )
		{
			obj.ptr->strHeader( *this );
		}
		else
		{
			( *OS ) << "str_header(<null>)";
		}

		return( *this );
	}


	/**
	 * <reference|pointer>.strFQN( os )
	 */
	template< class T >
	inline OutStream & operator<<(const _refFQN_< T > & obj)
	{
		obj.ref.strFQN( *this );

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const _ptrFQN_< T > & obj)
	{
		if( obj.ptr != NULL )
		{
			obj.ptr->strFQN( *this );
		}
		else
		{
			( *OS ) << INDENT.TABS << "str_fqn(<null>)" << INDENT.EOL;
		}

		return( *this );
	}




	/**
	 * INCR  <reference|pointer>.toStream( os )  DECR
	 */
	template< class T >
	inline OutStream & operator<<(const _refIncrIndent_< T > & obj)
	{
		incr();

		obj.ref.toStream( *this );

		decr();

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const _ptrIncrIndent_< T > & obj)
	{
		if( obj.ptr != NULL )
		{
			incr();

			obj.ptr->toStream( *this );

			decr();
		}
		else
		{
			( *OS ) << INDENT.TABS << INDENT.CHAR
					<< "incr_stream(<null>)" << INDENT.EOL;
		}

		return( *this );
	}


	/**
	 * INCR< count >  <reference|pointer>.toStream( os )  DECR< count >
	 */
	template< class T >
	inline OutStream & operator<<(const _refIncrIndentCount_< T > & obj)
	{
		incr( obj.count );

		obj.ref.toStream( *this );

		decr( obj.count );

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const _ptrIncrIndentCount_< T > & obj)
	{
		if( obj.ptr != NULL )
		{
			incr( obj.count );

			obj.ptr->toStream( *this );

			decr( obj.count );
		}
		else
		{
			OutStream::operator<<( tab(obj.count) );
			( *OS ) << "incr_count_stream(<null>)" << INDENT.EOL;
		}

		return( *this );
	}


	/**
	 * PUSH< AvmIndent >  <reference|pointer>.toStream( os )  POP< AvmIndent >
	 */
	template< class T >
	inline OutStream & operator<<(const _refIndent_< T > & obj)
	{
		obj.ref.toStream( OutStream::operator<<( obj.indent ) );

		pop();

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const _ptrIndent_< T > & obj)
	{
		if( obj.ptr != NULL )
		{
			obj.ptr->toStream( OutStream::operator<<( obj.indent ) );

			pop();
		}
		else
		{
			( *OS ) << obj.indent.TABS << "push_stream_pop(<null>)" << obj.indent.EOL;
		}

		return( *this );
	}


	/**
	 * REPEAT
	 * COLUMN
	 * EMPHASIS
	 */
	template< class T >
	inline OutStream & repeat( const T & x , std::size_t count)
	{
		for( ; count > 0  ; --count )
		{
			( *OS ) << x;
		}

		return( *this );
	}

	template< class T >
	inline OutStream & operator<<(const AvmREPEAT< T > & aRepeat)
	{
		return( repeat< T >(aRepeat.pattern, aRepeat.count) );
	}

	OutStream & operator<<(const AvmEMPHASIS & emphasis);


	/**
	 * INCR
	 * TAB DEPTH
	 */
	inline void incr(std::size_t count)
	{
		INDENT.incr(count);

		DEPTH += count;
	}

	inline void incr()
	{
		INDENT.incr();

		DEPTH += 1;
	}


	inline OutStream & operator++()
	{
		incr();

		return( *this );
	}


	/**
	 * DECR
	 * TAB DEPTH
	 */
	inline void decr(std::size_t count)
	{
		INDENT.decr(count);

		DEPTH = ( DEPTH > count ) ? (DEPTH - count) : 0;
	}

	inline void decr()
	{
		INDENT.decr();

		DEPTH = ( DEPTH > 1 ) ? (DEPTH - 1) : 0;
	}


	inline OutStream & operator--()
	{
		decr();

		return( *this );
	}


	/**
	 * save current INDENT
	 * set newIndent
	 * x.toStream( os , arg )
	 * restore old INDENT
	 */
	template< class T , class P >
	inline OutStream & toStream(const T & x,
			const P & arg, const AvmIndent & newIndent)
	{
		push();

		INDENT = newIndent;

		x.toStream( *this , arg );

		pop();

		return( *this );
	}


	/**
	 * CAST
	 * std::ostream &
	 */
	inline operator std::ostream & () const
	{
		return( *OS );
	}


	/**
	 * LOAD
	 * DISPOSE
	 */
	static void load();
	static void dispose();

	/**
	 * CONFIGURE
	 */
	static bool configure(Workflow * aWorkflow);

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CONSOLE PROMPT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

extern const std::string & CONSOLE_DEBUG_PROMPT;
extern const std::string & CONSOLE_SEW_PROMPT;
extern const std::string & CONSOLE_CONFIG_PROMPT;
extern const std::string & CONSOLE_SYMBEX_PROMPT;


inline void _DBG_(OutStream & os)
{
	os << CONSOLE_DEBUG_PROMPT;
}

inline void _SEW_(OutStream & os)
{
	os << CONSOLE_SEW_PROMPT;
}

inline void _CFG_(OutStream & os)
{
	os << CONSOLE_CONFIG_PROMPT;
}

inline void _SBX_(OutStream & os)
{
	os << CONSOLE_SYMBEX_PROMPT;
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// SCOPE : for automatic PUSH / POP  AvmIndent
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

struct ScopeNewIndent
{
	OutStream & OS;

	AvmIndent INDENT;

	ScopeNewIndent(OutStream & os, const AvmIndent & indent)
	: OS( os ),
	// save current indent
	INDENT( os.INDENT )
	{
		// set new indent
		os.INDENT = indent;
	}

	ScopeNewIndent(OutStream & os,
			const std::string & tabs   = "",
			const std::string & _char_ = "\t",
			const std::string & eol    = "\n")
	: OS( os ),
	// save current indent
	INDENT( os.INDENT )
	{
		// set new indent
		os.INDENT = AvmIndent(tabs, _char_,eol);
	}

	~ScopeNewIndent()
	{
		// restore old indent
		OS.INDENT = INDENT;
	}
};


/**
 * SCOPE
 * for automatic INCREMENT / DECREMENT
 */
struct ScopeIncrIndent
{
	OutStream & OS;

	ScopeIncrIndent(OutStream & os)
	: OS( os )
	{
		// increment indent
		os.incr();
	}

	~ScopeIncrIndent()
	{
		// decrement indent
		OS.decr();
	}
};


/**
 * WrapData Manipulators
 */
inline void END_WRAP(OutStream & os)
{
	os.end_wrap();
}

inline void END_WRAP_EOL(OutStream & os)
{
	os.end_wrap();

	os << os.INDENT.EOL;
}

/**
 * AvmTAB
 */
inline void IGNORE_FIRST_TAB(OutStream & os)
{
	os.INDENT.IGNORE_FIRST_TAB = true;
}


inline void TAB(OutStream & os)
{
	if( os.INDENT.IGNORE_FIRST_TAB )
	{
		os.INDENT.IGNORE_FIRST_TAB = false;
	}
	else
	{
		os << os.INDENT.TABS;
	}
}

inline void TAB1(OutStream & os)
{
	if( os.INDENT.IGNORE_FIRST_TAB )
	{
		os.INDENT.IGNORE_FIRST_TAB = false;
	}
	else
	{
		os << os.INDENT.TABS;
	}
}


inline void TAB2(OutStream & os)
{
	os << os.INDENT.TABS << os.INDENT.CHAR;
}

inline void TAB3(OutStream & os)
{
	os << os.INDENT.TABS << os.INDENT.CHAR << os.INDENT.CHAR;
}

inline void TAB4(OutStream & os)
{
	os << os.INDENT.TABS << os.INDENT.CHAR << os.INDENT.CHAR
			<< os.INDENT.CHAR;
}

inline void TAB5(OutStream & os)
{
	os << os.INDENT.TABS << os.INDENT.CHAR << os.INDENT.CHAR
			<< os.INDENT.CHAR << os.INDENT.CHAR;
}


/**
 * ++TAB
 * --TAB
 */
inline void INCR_INDENT_TAB(OutStream & os)
{
	os.incr();

	os << os.INDENT.TABS;
}

inline void DECR_INDENT_TAB(OutStream & os)
{
	os.decr();

	os << os.INDENT.TABS;
}

inline void DECR_INDENT_TAB2(OutStream & os)
{
	os.decr();

	os << os.INDENT.TABS << os.INDENT.CHAR;
}


inline void INCR2_INDENT_TAB(OutStream & os)
{
	os.incr(2);

	os << os.INDENT.TABS;
}

inline void DECR2_INDENT_TAB(OutStream & os)
{
	os.decr(2);

	os << os.INDENT.TABS;
}

inline void DECR2_INDENT_TAB2(OutStream & os)
{
	os.decr(2);

	os << os.INDENT.TABS << os.INDENT.CHAR;
}


/**
 * TAB++
 * TAB--
 */
inline void TAB_INCR_INDENT(OutStream & os)
{
	os << os.INDENT.TABS;

	os.incr();
}

inline void TAB_DECR_INDENT(OutStream & os)
{
	os << os.INDENT.TABS;

	os.decr();
}


inline void TAB_INCR2_INDENT(OutStream & os)
{
	os << os.INDENT.TABS;

	os.incr(2);
}

inline void TAB_DECR2_INDENT(OutStream & os)
{
	os << os.INDENT.TABS;

	os.decr(2);
}


/**
 * INCR
 * DECR
 * INDENTATION
 */
inline void INCR_INDENT(OutStream & os)
{
	os.incr();
}

inline void DECR_INDENT(OutStream & os)
{
	os.decr();
}


inline void INCR2_INDENT(OutStream & os)
{
	os.incr(2);
}

inline void DECR2_INDENT(OutStream & os)
{
	os.decr(2);
}


inline void INCR3_INDENT(OutStream & os)
{
	os.incr(3);
}

inline void DECR3_INDENT(OutStream & os)
{
	os.decr(3);
}

/**
 * NEW
 * END
 * INDENTATION
 */
inline AvmIndent NEW_INDENT(
		const std::string & tabs   = "",
		const std::string & _char_ = "\t",
		const std::string & eol    = "\n")
{
	return( AvmIndent(tabs, _char_, eol) );
}

inline AvmIndent & NEW_INDENT(AvmIndent & indent)
{
	return( indent );
}


inline AvmIndent NEW_LTRIM_INDENT(const AvmIndent & indent)
{
	return( AvmIndent("", indent.CHAR, indent.EOL) );
}

inline AvmIndent NEW_LTRIM_INDENT(OutStream & os)
{
	return( AvmIndent("", os.INDENT.CHAR, os.INDENT.EOL) );
}


inline void END_INDENT(OutStream & os)
{
	os.pop();
}

inline void END_INDENT_EOL(OutStream & os)
{
	os.pop();

	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}


/**
 * BackSpace
 */
inline void BACKSPACE(OutStream & os)
{
	os.backspace();
}

inline void BACKSPACE_TAB(OutStream & os)
{
	os.backspace();

	os << os.INDENT.TABS;
}


/**
 * AvmEOL
 */
inline void EOL(OutStream & os)
{
	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void EOL_TAB(OutStream & os)
{
	os << os.INDENT.EOL << os.INDENT.TABS;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void EOL_TAB2(OutStream & os)
{
	os << os.INDENT.EOL << os.INDENT.TABS << os.INDENT.CHAR;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void EOL_TAB3(OutStream & os)
{
	os << os.INDENT.EOL << os.INDENT.TABS
			<< os.INDENT.CHAR << os.INDENT.CHAR;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void EOL_FLUSH(OutStream & os)
{
	os << os.INDENT.EOL << std::flush;
}


inline void EOL2(OutStream & os)
{
	os << os.INDENT.EOL << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void EOL2_TAB(OutStream & os)
{
	os << os.INDENT.EOL << os.INDENT.EOL << os.INDENT.TABS;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void EOL2_FLUSH(OutStream & os)
{
	os << os.INDENT.EOL << os.INDENT.EOL << std::flush;
}


/**
 * ++TAB
 * --TAB
 */
inline void INCR_EOL(OutStream & os)
{
	os.incr();

	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}

inline void DECR_EOL(OutStream & os)
{
	os.decr();

	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM
}


inline void EOL_INCR_INDENT(OutStream & os)
{
	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	os.incr();
}

inline void EOL_DECR_INDENT(OutStream & os)
{
	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	os.decr();
}


inline void EOL_INCR2_INDENT(OutStream & os)
{
	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	os.incr(2);
}

inline void EOL_DECR2_INDENT(OutStream & os)
{
	os << os.INDENT.EOL;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	os << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	os.decr(2);
}

inline void EOL_FLUSH_DECR_INDENT(OutStream & os)
{
	os << os.INDENT.EOL << std::flush;

	os.decr();
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// StringOutStream
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class StringOutStream  :  public OutStream
{

protected:
	/**
	 * ATTRIBUTE
	 */
	std::ostringstream oss;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	StringOutStream(const AvmIndent & indent = AVM_TAB_INDENT)
	: OutStream( oss , indent )
	{
		//!! NOTHING
	}

	StringOutStream(
			const std::string & tabs,
			const std::string & _char_ = "\t",
			const std::string & eol    = "\n")
	: OutStream( oss , tabs , _char_ , eol )
	{
		//!! NOTHING
	}

	StringOutStream(const WrapData & wrapData,
			const AvmIndent & indent = AVM_TAB_INDENT)
	: OutStream( oss , indent )
	{
		OutStream::operator<<( wrapData );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~StringOutStream()
	{
		//!! NOTHING
	}


	/**
	 * str()
	 */
	inline std::string str() const
	{
		OutStream::flush();

		return( oss.str() );
	}

	inline void str(const std::string & buf)
	{
		OutStream::flush();

		oss.str( buf );
	}

	/**
	 * c_str()
	 */
	inline const char * c_str() const
	{
		OutStream::flush();

		return( oss.str().c_str() );
	}


	/**
	 * CAST
	 * std::string
	 * const char *
	 */
	inline operator std::string () const
	{
		OutStream::flush();

		return( oss.str() );
	}

//	inline operator const char * () const
//	{
//		OutStream::flush();
//
//		return( oss.str().c_str() );
//	}


	/**
	 * operator<<
	 */
	template< class T >
	inline StringOutStream & operator<<( const T & x )
	{
		OutStream::operator<<( x );

		return( *this );
	}


	inline StringOutStream & operator<<(
			void (*op) ( StringOutStream & ) )
	{
		op( *this );

		return( *this );
	}

	inline StringOutStream & operator<<( void (*op) ( OutStream & ) )
	{
		op( *this );

		return( *this );
	}

	inline StringOutStream & operator<<(
			std::ostream & (*op) ( std::ostream & ) )
	{
		op( *this );

		return( *this );
	}

};

/**
 * TYPEDEF
 * to_string() template replacement by OSS()
 */
typedef StringOutStream  OSS;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class NullOutStream  :  public OutStream
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	NullOutStream()
	: OutStream( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~NullOutStream()
	{
		//!! NOTHING
	}


	/**
	 * operator<<
	 */
	template< class T >
	inline NullOutStream & operator<<(const T & x)
	{
		return( *this );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// PairOutStream
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class PairOutStream
{

public:
	/**
	 * ATTRIBUTES
	 */
	OutStream & OS1;
	OutStream & OS2;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	PairOutStream(OutStream & os1, OutStream & os2)
	: OS1( os1 ) , OS2( os2 )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~PairOutStream()
	{
		//!! NOTHING
	}


	/**
	 * operator<<
	 */
	template< class T >
	inline PairOutStream & operator<<( const T & x )
	{
		OS1 << x;
		OS2 << x;

		return( *this );
	}


	inline PairOutStream & operator<<( void (*op) ( OutStream & ) )
	{
		op( OS1 );
		op( OS2 );

		return( *this );
	}

	inline PairOutStream & operator<<(
			std::ostream & (*op) ( std::ostream & ) )
	{
		op( OS1 );
		op( OS2 );

		return( *this );
	}


	inline virtual void backspace()
	{
		OS1.backspace();
		OS2.backspace();
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TripleOutStream
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class TripleOutStream
{

public:
	/**
	 * ATRIBUTES
	 */
	OutStream & OS1;
	OutStream & OS2;
	OutStream & OS3;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TripleOutStream(OutStream & os1, OutStream & os2, OutStream & os3)
	: OS1( os1 ) , OS2( os2 ) , OS3( os3 )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TripleOutStream()
	{
		//!! NOTHING
	}


	/**
	 * operator<<
	 */
	template< class T >
	inline TripleOutStream & operator<<( const T & x )
	{
		OS1 << x;
		OS2 << x;
		OS3 << x;

		return( *this );
	}


	inline TripleOutStream & operator<<( void (*op) ( OutStream & ) )
	{
		op( OS1 );
		op( OS2 );
		op( OS3 );

		return( *this );
	}

	inline TripleOutStream & operator<<(
			std::ostream & (*op) ( std::ostream & ) )
	{
		op( OS1 );
		op( OS2 );
		op( OS3 );

		return( *this );
	}


	inline virtual void backspace()
	{
		OS1.backspace();
		OS2.backspace();
		OS3.backspace();
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// operator<<
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#define AVM_OS_STREAM( T )  \
inline OutStream & operator<<(OutStream & os, const T & anElement) \
{ \
	anElement.toStream( os ); \
	return( os ); \
} \
inline StringOutStream & operator<<(StringOutStream & os, const T & anElement) \
{ \
	anElement.toStream( os ); \
	return( os ); \
} \
inline PairOutStream & operator<<(PairOutStream & os, const T & anElement) \
{ \
	anElement.toStream( os.OS1 ); \
	anElement.toStream( os.OS2 ); \
	return( os ); \
} \
inline TripleOutStream & operator<<(TripleOutStream & os, const T & anElement) \
{ \
	anElement.toStream( os.OS1 ); \
	anElement.toStream( os.OS2 ); \
	anElement.toStream( os.OS3 ); \
	return( os ); \
}


#define AVM_OS_STREAM_COLLECTION( T )  \
inline OutStream & operator<<(OutStream & os, const T & anElement) \
{ \
	T::const_iterator endIt = anElement.end(); \
	for( T::const_iterator it = anElement.begin() ; it != endIt ; ++it ) \
	{ \
		os << (*it); \
	} \
	return( os ); \
} \
inline PairOutStream & operator<<(PairOutStream & os, const T & anElement) \
{ \
	T::const_iterator endIt = anElement.end(); \
	for( T::const_iterator it = anElement.begin() ; it != endIt ; ++it ) \
	{ \
		os << (*it); \
	} \
	return( os ); \
} \
inline TripleOutStream & operator<<(TripleOutStream & os, const T & anElement) \
{ \
	T::const_iterator endIt = anElement.end(); \
	for( T::const_iterator it = anElement.begin() ; it != endIt ; ++it ) \
	{ \
		os << (*it); \
	} \
	return( os ); \
} \


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// SAVE & REDIRECT & RESTORE STREAMBUF
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// save original stream::sbuf
// redirect stream::sbuf
#define STREAMBUF_SAVE_REDIRECT( originalStream , targetStream ) \
		std::streambuf * saveSBUF = originalStream.rdbuf(); \
		originalStream.rdbuf( targetStream.rdbuf() );


// restore the original stream::sbuf
#define STREAMBUF_RESTORE( originalStream ) \
		originalStream.rdbuf( saveSBUF );



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// GLOBAL PRE-DEFINED STREAM
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * UTIL VARIABLE
 * AVM_OS_NULL
 */
extern std::ostream * _avm_os_null_;

extern NullOutStream AVM_OS_NULL;


/**
 * AVM COUT & CERR & DEBUG
 */
extern OutStream AVM_OS_COUT;

extern OutStream AVM_OS_CERR;

extern OutStream AVM_OS_DEBUG;


/**
 * AVM LOG & TRACE FILE LOCATION
 */
extern std::string AVM_LOG_FILE_LOCATION;

extern std::string AVM_TRACE_FILE_LOCATION;


/**
 * UTIL VARIABLE
 * AVM_OS_LOG
 */
extern std::ostream * _avm_os_log_;

extern OutStream AVM_OS_LOG;


/**
 * UTIL VARIABLE
 * AVM_OS_TRACE
 */
extern std::ostream * _avm_os_trace_;

extern OutStream AVM_OS_TRACE;


/**
 * UTIL VARIABLE
 * AVM_OS_WARN as AVM_OS_CERR & AVM_OS_TRACE
 */
typedef PairOutStream WarnOutstreamT;

extern WarnOutstreamT  AVM_OS_WARN;

/**
 * UTIL VARIABLE
 * AVM_OS_INFO as AVM_OS_COUT & AVM_OS_TRACE
 */
typedef PairOutStream  InfoOutstreamT;

extern InfoOutstreamT AVM_OS_INFO;

/**
 * UTIL VARIABLE
 * AVM_OS_CLOG as AVM_OS_COUT & AVM_OS_LOG
 */
typedef PairOutStream  CLogOutstreamT;

extern InfoOutstreamT AVM_OS_CLOG;

/**
 * UTIL VARIABLE
 * AVM_OS_TDD
 * for Test Driven Development
 */
extern std::ostream * _avm_os_tdd_;

extern OutStream AVM_OS_TDD;


} /* namespace sep */
#endif /* PRINTER_OUTSTREAM_H_ */
