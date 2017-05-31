/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 juin 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef PRINTER_MANIPULATORS_H_
#define PRINTER_MANIPULATORS_H_

#include <string>


namespace sep {


//class Manipulators {
//public:
//	Manipulators() {
//		// TODO Auto-generated constructor stub
//
//	}
//	virtual ~Manipulators() {
//		// TODO Auto-generated destructor stub
//	}
//};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// MANIPULATORS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



/**
 * AvmTAB
 */
struct AvmTAB
{
	std::size_t count;

	AvmTAB(std::size_t n)
	: count( n )
	{
		//!! NOTHING
	}
};

inline AvmTAB tab(std::size_t n)
{
	return( n );
}


/**
 * AvmEOL
 */
struct AvmEOL
{
	std::size_t count;

	AvmEOL(std::size_t n)
	: count( n )
	{
		//!! NOTHING
	}
};

inline AvmEOL eol(std::size_t n)
{
	return( n );
}


/**
 * AvmINCR
 */
struct AvmINCR
{
	std::size_t count;

	AvmINCR(std::size_t n)
	: count( n )
	{
		//!! NOTHING
	}
};

inline AvmINCR incr(std::size_t n)
{
	return( n );
}


/**
 * AvmDECR
 */
struct AvmDECR
{
	std::size_t count;

	AvmDECR(std::size_t n)
	: count( n )
	{
		//!! NOTHING
	}
};

inline AvmDECR decr(std::size_t n)
{
	return( n );
}



/**
 * Automatic mechanism for
 * <reference>.toStream( os )
 */
template< class T >
struct _refStream_
{
	const T & ref;

	// CONSTRUCTOR
	_refStream_(const T & aRef)
	: ref( aRef )
	{
		//!! NOTHING
	}
};

/**
 * Automatic mechanism for
 * <pointer>->toStream( os )
 */
template< class T >
struct _ptrStream_
{
	T * ptr;

	// CONSTRUCTOR
	_ptrStream_(T * aPtr)
	: ptr( aPtr )
	{
		//!! NOTHING
	}
};


/**
 * toStream FUNCTORS
 */
template< class T >
inline _refStream_< T > to_stream( const T & ref )
{
	return( ref );
}

template< class T >
inline _ptrStream_< T > to_stream( T * ptr )
{
	return( ptr );
}


/**
 * Automatic mechanism for
 * <named_element>.toFQN( os )
 */
template< class T >
struct _refFQN_
{
	const T & ref;

	// CONSTRUCTOR
	_refFQN_(const T & aRef)
	: ref( aRef )
	{
		//!! NOTHING
	}
};

/**
 * Automatic mechanism for
 * <named_element>->toFQN( os )
 */
template< class T >
struct _ptrFQN_
{
	T * ptr;

	// CONSTRUCTOR
	_ptrFQN_(T * aPtr)
	: ptr( aPtr )
	{
		//!! NOTHING
	}
};

/**
 * toStream FUNCTORS
 */
template< class T >
inline _refFQN_< T > str_fqn( const T & ref )
{
	return( ref );
}

template< class T >
inline _ptrFQN_< T > str_fqn( T * ptr )
{
	return( ptr );
}


/**
 * Automatic mechanism for
 * <reference>.strHeader( os )
 */
template< class T >
struct _refHeader_
{
	const T & ref;

	// CONSTRUCTOR
	_refHeader_(const T & aRef)
	: ref( aRef )
	{
		//!! NOTHING
	}
};

/**
 * Automatic mechanism for
 * <pointer>->toHeader( os )
 */
template< class T >
struct _ptrHeader_
{
	T * ptr;

	// CONSTRUCTOR
	_ptrHeader_(T * aPtr)
	: ptr( aPtr )
	{
		//!! NOTHING
	}
};


/**
 * toHeader FUNCTORS
 */
template< class T >
inline _refHeader_< T > str_header( const T & ref )
{
	return( ref );
}

template< class T >
inline _ptrHeader_< T > str_header( T * ptr )
{
	return( ptr );
}


/**
 * Automatic mechanism for
 * INCR
 * <reference>.toHeader( os )
 * DECR
 */
template< class T >
struct _refIncrIndent_
{
	const T & ref;

	// CONSTRUCTOR
	_refIncrIndent_(const T & aRef)
	: ref( aRef )
	{
		//!! NOTHING
	}
};

/**
 * Automatic mechanism for
 * INCR
 * <pointer>.toStream( os )
 * DECR
 */
template< class T >
struct _ptrIncrIndent_
{
	T * ptr;

	// CONSTRUCTOR
	_ptrIncrIndent_(T * aPtr)
	: ptr( aPtr )
	{
		//!! NOTHING
	}
};


/**
 * Increment(1) AvmIndent FUNCTORS
 */
template< class T >
inline _refIncrIndent_< T > incr_stream( const T & ref )
{
	return( ref );
}

template< class T >
inline _ptrIncrIndent_< T > incr_stream( T * ptr )
{
	return( ptr );
}


/**
 * Automatic mechanism for
 * INCR< count >
 * <reference>.toStream( os )
 * DECR< count >
 */
template< class T >
struct _refIncrIndentCount_
{
	const T & ref;

	std::size_t count;

	// CONSTRUCTOR
	_refIncrIndentCount_(const T & aRef, std::size_t aCount)
	: ref( aRef ), count( aCount )
	{
		//!! NOTHING
	}
};

/**
 * Automatic mechanism for
 * INCR< count >
 * <pointer>.toStream( os )
 * DECR< count >
 */
template< class T >
struct _ptrIncrIndentCount_
{
	T * ptr;

	std::size_t count;

	// CONSTRUCTOR
	_ptrIncrIndentCount_(T * aPtr, std::size_t aCount)
	: ptr( aPtr ), count( aCount )
	{
		//!! NOTHING
	}
};


/**
 * Increment(<count>) AvmIndent FUNCTORS
 */
template< class T >
inline _refIncrIndentCount_< T > incr_stream( const T & ref , std::size_t count )
{
	return( _refIncrIndentCount_< T >(ref, count) );
}

template< class T >
inline _ptrIncrIndentCount_< T > incr_stream( T * ptr , std::size_t count )
{
	return( _ptrIncrIndentCount_< T >(ptr, count) );
}



/**
 * AvmREPEAT
 */
template< class T >
struct AvmREPEAT
{
	const T & pattern;
	std::size_t count;

	AvmREPEAT(const T & aPattern, std::size_t aCount)
	: pattern( aPattern ),
	count( aCount )
	{
		//!! NOTHING
	}

};

template< class T >
inline AvmREPEAT< T > REPEAT(const T & aPattern, std::size_t aCount)
{
	return( AvmREPEAT< T >(aPattern, aCount) );
}


/**
 * AvmEMPHASIS
 */
struct AvmEMPHASIS
{
	std::string header;
	std::string body;
	char        emph;
	std::size_t  count;

	bool enableTab;

	AvmEMPHASIS(const std::string & aHeader, const std::string & aBody,
			char anEmph, std::size_t aCount = 80, bool enableTab = true)
	: header( aHeader ),
	body( aBody ),
	emph( anEmph ),
	count( aCount ),
	enableTab( true )
	{
		//!! NOTHING
	}

	AvmEMPHASIS(const std::string & aText, char anEmph,
			std::size_t aCount = 80, bool enableTab = true)
	: header( "" ),
	body( aText ),
	emph( anEmph ),
	count( aCount ),
	enableTab( true )
	{
		//!! NOTHING
	}

};

inline AvmEMPHASIS EMPHASIS(const std::string & aText,
		char anEmph = '*', std::size_t aCount = 80, bool enableTab = true)
{
	return( AvmEMPHASIS(aText, anEmph, aCount, enableTab) );
}

inline AvmEMPHASIS EMPHASIS(
		const std::string & aHeader, const std::string & aBody,
		char anEmph = '*', std::size_t aCount = 80, bool enableTab = true)
{
	return( AvmEMPHASIS(aHeader, aBody, anEmph, aCount, enableTab) );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// SYMBEX VALUE CSS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

struct SymbexValueCSS
{

	std::string BEGIN;

	std::string SEPARATOR;

	std::string END;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexValueCSS(
			const std::string & begin     = "{ " ,
			const std::string & separator = " , ",
			const std::string & end       = " }" )
	: BEGIN(  begin ),
	SEPARATOR( separator ),
	END( end )
	{
		//!! NOTHING
	}

};


/**
 * DEFAULT AVM Multi-Value Formatter
 */
extern SymbexValueCSS DEFAULT_SYMBEX_VALUE_ARRAY_CSS;

extern SymbexValueCSS DEFAULT_SYMBEX_VALUE_PARAMS_CSS;

extern SymbexValueCSS DEFAULT_SYMBEX_VALUE_STRUCT_CSS;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AvmIndent
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

struct AvmIndent
{

	std::size_t  COUNT;

	std::string TABS;

	std::string CHAR;

	std::string EOL;

	std::string EOL_WRAP;

	std::size_t REF_COUNT;

	bool IGNORE_FIRST_TAB;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmIndent(const std::string & tabs   = "",
			const std::string & _char_   = "\t",
			const std::string & eol      = "\n",
			const std::string & eol_wrap = "\n")
	: COUNT( 0 ),
	TABS(  tabs ),
	CHAR( _char_ ),
	EOL( eol ),
	EOL_WRAP( eol_wrap ),
	REF_COUNT( 1 ),
	IGNORE_FIRST_TAB( false )
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 */
	inline std::string wrapSeparator() const
	{
		return( EOL_WRAP + CHAR );
	}

	inline std::size_t tabSize(std::size_t offset = 0)
	{
		return( TABS.size() + offset );
	}

	inline std::size_t tab2Size(std::size_t offset = 0)
	{
		return( TABS.size() + CHAR.size() + offset );
	}


	/**
	 * TEST
	 * If is prefera
	 */
	inline bool preferablySTR()
	{
		return( /*TAB.empty() &&*/ CHAR.empty() /*&& EOL.empty()*/ );
	}

	inline bool preferablyFQN()
	{
		return( /*TAB.empty() &&*/ CHAR.empty() && EOL.empty() );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline bool operator==(const AvmIndent & other) const
	{
		return( (TABS == other.TABS)   &&
				(CHAR == other.CHAR)   &&
//				(COUNT == other.COUNT) &&
				(EOL == other.EOL)     );
	}

	inline bool operator!=(const AvmIndent & other) const
	{
		return( (TABS != other.TABS)   ||
				(CHAR != other.CHAR)   ||
//				(COUNT != other.COUNT) ||
				(EOL != other.EOL)     );
	}


	/**
	 * INCR
	 * TAB LEVEL
	 */
	inline void incr(std::size_t count)
	{
		COUNT += count;

		for( ; count > 0 ; --count )
		{
			TABS = CHAR + TABS;
		}
	}

	inline void incr()
	{
		COUNT += 1;

		TABS = CHAR + TABS;
	}


	inline void operator++()
	{
		COUNT += 1;

		TABS = CHAR + TABS;
	}


	/**
	 * DECR
	 * TAB LEVEL
	 */
	inline void decr(std::size_t count)
	{
		COUNT = ( COUNT >= count ) ? (COUNT - count) : 0;

		for( ; count > 0 ; --count )
		{
//			TABS = TABS.substr( TABS.find_first_of(CHAR) );
			TABS = TABS.substr( CHAR.size() );
		}
	}

	inline void decr()
	{
		if( COUNT >= 1 )
		{
			COUNT = (COUNT - 1);

//			TABS = TABS.substr( TABS.find_first_of(CHAR) );
			TABS = TABS.substr( CHAR.size() );
		}
	}


	inline void operator--()
	{
		if( COUNT >= 1 )
		{
			COUNT += -1;

//			TABS = TABS.substr( TABS.find_first_of(CHAR) );
			TABS = TABS.substr( CHAR.size() );
		}
	}

};


/**
 * DEFAULT AVM INDENT
 */
extern AvmIndent AVM_TAB_INDENT;

extern AvmIndent AVM_TAB1_INDENT;

extern AvmIndent AVM_SPC_INDENT;

extern AvmIndent AVM_SPC1_INDENT;

extern AvmIndent AVM_STR_INDENT;

extern AvmIndent AVM_RTS_INDENT;

extern AvmIndent AVM_NO_INDENT;

// Default output / fscn file indent
extern AvmIndent AVM_OUTPUT_INDENT;

extern AvmIndent AVM_FSCN_INDENT;


/**
 * Automatic mechanism for
 * PUSH< AvmIndent >
 * <reference>.toStream( os )
 * POP< AvmIndent >
 */
template< class T >
struct _refIndent_
{
	const T & ref;

	const AvmIndent & indent;

	// CONSTRUCTOR
	_refIndent_(const T & aRef, const AvmIndent & anIndent)
	: ref( aRef ), indent( anIndent )
	{
		//!! NOTHING
	}
};

/**
 * Automatic mechanism for
 * PUSH< AvmIndent >
 * <pointer>.toStream( os )
 * POP< AvmIndent >
 */
template< class T >
struct _ptrIndent_
{
	T * ptr;

	const AvmIndent & indent;

	// CONSTRUCTOR
	_ptrIndent_(T * aPtr, const AvmIndent & anIndent)
	: ptr( aPtr ), indent( anIndent )
	{
		//!! NOTHING
	}
};


/**
 * toStream FUNCTORS
 */
template< class T >
inline _refIndent_< T > to_stream( const T & ref , const AvmIndent & anIndent )
{
	return( _refIndent_< T >(ref, anIndent) );
}

template< class T >
inline _ptrIndent_< T > to_stream( T * ptr , const AvmIndent & anIndent )
{
	return( _ptrIndent_< T >(ptr, anIndent) );
}


// AVM_SPC_INDENT("" , " ", "\n")
template< class T >
inline _refIndent_< T > spc_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_SPC_INDENT) );
}

template< class T >
inline _ptrIndent_< T > spc_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_SPC_INDENT) );
}

// AVM_SPC1_INDENT(" " , " ", "\n")
template< class T >
inline _refIndent_< T > spc1_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_SPC1_INDENT) );
}

template< class T >
inline _ptrIndent_< T > spc1_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_SPC1_INDENT) );
}


// AVM_TAB_INDENT(""  , "\t", "\n")
template< class T >
inline _refIndent_< T > tab_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_TAB_INDENT) );
}

template< class T >
inline _ptrIndent_< T > tab_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_TAB_INDENT) );
}

// AVM_TAB1_INDENT("\t"  , "\t", "\n")
template< class T >
inline _refIndent_< T > tab1_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_TAB1_INDENT) );
}

template< class T >
inline _ptrIndent_< T > tab1_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_TAB1_INDENT) );
}


// AVM_STR_INDENT(" ", "", "")
template< class T >
inline _refIndent_< T > str_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_STR_INDENT) );
}

template< class T >
inline _ptrIndent_< T > str_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_STR_INDENT) );
}

// AVM_RTS_INDENT("", "", " ")
template< class T >
inline _refIndent_< T > rts_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_RTS_INDENT) );
}

template< class T >
inline _ptrIndent_< T > rts_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_RTS_INDENT) );
}


// AVM_NO_INDENT("" , "", "")
template< class T >
inline _refIndent_< T > no_indent( const T & ref )
{
	return( _refIndent_< T >(ref, AVM_NO_INDENT) );
}

template< class T >
inline _ptrIndent_< T > no_indent( T * ptr )
{
	return( _ptrIndent_< T >(ptr, AVM_NO_INDENT) );
}


} /* namespace sep */

#endif /* PRINTER_MANIPULATORS_H_ */
