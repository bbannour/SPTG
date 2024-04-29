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
 *******************************************************************************/
/* CPP */

lexer grammar SEWLexer;

options {
	language = Cpp;
}

//options
//{
//	charVocabulary = '\0'..'\377';
//	k = 6;						// four characters of lookahead
//
//	testLiterals = false;		// don't automatically test for literals
//
//	caseSensitive = true;
//	caseSensitiveLiterals = true;
//}


// These are all supported lexer sections:

// Lexer file header. Appears at the top of h + cpp files. Use e.g. for copyrights.
@lexer::header {
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
 *   - Initial API and Implementation
 *******************************************************************************/

/* lexer header section */
}

// Appears before any #include in h + cpp files.
@lexer::preinclude {/* lexer precinclude section */

	#include <printer/OutStream.h>

}

// Follows directly after the standard #includes in h + cpp files.
@lexer::postinclude {
/* lexer postinclude section */
#ifndef _WIN32
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif
}

// Directly preceds the lexer class declaration in the h file (e.g. for additional types etc.).
@lexer::context {/* lexer context section */}

// Appears in the public part of the lexer in the h file.
@lexer::members {/* public lexer declarations section */
bool canTestFoo() { return true; }
bool isItFoo() { return true; }
bool isItBar() { return true; }

void myFooLexerAction() { /* do something*/ };
void myBarLexerAction() { /* do something*/ };


	/**
	 * GETTER - SETTER
	 * mFilename
	 */
	inline const std::string & getFilename() const
	{
		return mFilename;
	}
	
	inline void setFilename(const std::string & aFilename)
	{
		mFilename = aFilename;
	}

	/**
	 * GETTER - SETTER
	 * noOfErrors
	 */
	inline std::size_t hasError()
	{
		return( numberOfErrors() > 0 );
	}

	inline std::size_t numberOfErrors()
	{
		return( noOfErrors + getNumberOfSyntaxErrors() );
	}

	inline void resetErrors()
	{
		noOfErrors = 0;
	}

}

// Appears in the private part of the lexer in the h file.
@lexer::declarations {/* private lexer declarations/members section */

	std::string mFilename;
	
	std::size_t noOfErrors;

	void reportError( const std::string & errorMessage )
	{
		reportMessage( errorMessage );
		++noOfErrors;
	}

	void reportMessage( const std::string & message ) const
	{
		if ( getFilename().length() > 0 )
		{
			AVM_OS_CERR << getFilename() << ":";
		}

		AVM_OS_CERR << this->getLine() << ":"
				<< const_cast< SEWLexer * >(this)->getCharPositionInLine()
				<< " [error] " << message << std::endl;
	}

}

// Appears in line with the other class member definitions in the cpp file.
@lexer::definitions {/* lexer definitions section */}

//channels { CommentsChannel, DirectiveChannel }

tokens {
	DUMMY
}

/* end CPP */


////////////////////////////////////////////////////////////////////////////////
///// KEYWORDS
////////////////////////////////////////////////////////////////////////////////

Version      : 'version:'     ;

Public       : 'public'       ;
Final        : 'final'        ;
Static       : 'static'       ;
Volatile     : 'volatile'     ;
Buffered     : 'buffered'     ;
Reference    : 'reference'    ;
Meta         : 'meta'         ;
Form         : 'form'         ;
Endform      : 'endform'      ;
Prototype    : 'prototype'    ;
Endprototype : 'endprototype' ;
Section      : 'section'      ;
Endsection   : 'endsection'   ;

Provided     : 'provided'     ;
Activity     : 'activity'     ;

From         : 'from'         ;

As           : 'as'           ;
Is           : 'is'           ;
To           : 'to'           ;

True         : 'true'         ;
False        : 'false'        ;


////////////////////////////////////////////////////////////////////////////////
///// OPERATORS SYMBOLS LITERAL
////////////////////////////////////////////////////////////////////////////////

AT                : '@'   ;

PLUS              : '+'   ;
MINUS             : '-'   ;
MOD				  : '%'	  ;
MULT              : '*'   ;
DIV	              : '/'   ;

POW	              : '**'  ;//| //'^' ;

ASSIGN            : ':='  ;

PUSH              : '<=<' ;
ASSIGN_TOP        : '^=<' ;
TOP               : '^=>' ;
POP               : '>=>' ;

EQ                : '='   ;

BANDEQ            : '&='  ;
BOREQ             : '|='  ;
BXOREQ            : '^='  ;
BNOTEQ            : '~='  ;

PLUSEQ            : '+='  ;
MINUSEQ           : '-='  ;
MULTEQ            : '*='  ;
DIVEQ             : '/='  ;
MODEQ             : '%='  ;

EQEQ              : '=='  ;
NEQ               : '!='  ;
SEQ               : '===' ;
NSEQ              : '=/=' ;

GT                : '>'   ;
GTE               : '>='  ;
LT_               : '<'   ;
LTE               : '<='  ;

BAND              : '&'   ;
BOR               : '|'   ;
BXOR              : '^'   ;
BNOT              : '~'   ;

LSHIFT            : '<<'  ;
RSHIFT            : '>>'  ;


LAND              : '&&'  ;
LOR               : '||'  ;
LNOT              : '!'   ;

LPAREN            : '('   ;
RPAREN            : ')'   ;

LPAREN_INVOKE     : '(:'  ;

LBRACK            : '['   ;
RBRACK            : ']'   ;


LCURLY            : '{'   ;
RCURLY            : '}'   ;

LPROG             : '${'  ;

LGENERIC          : '<%'  ;
RGENERIC          : '%>'  ;

COMMA             : ','   ;
SEMI              : ';'   ;
COLON             : ':'   ;
COLON2            : '::'  ;
DOT               : '.'   ;
QUESTION          : '?'   ;

GT_COLON          : '>:'  ;

ARROW             : '->'  ;


INTERLEAVING      : '|i|'   ;
PARTIAL_ORDER     : '|~|'   ;

ASYNC             : '|a|'   ;
STRONG_SYNC       : '|and|' ;
WEAK_SYNC         : '|or|'  ;
PARALLEL          : '|,|'   ;
PRODUCT           : '|x|'   ;

EXCLUSIVE         : '|xor|' ;
NONDETERMINISM    : '|/\\|' ;

PRIOR_GT          : '|>|'   ;
PRIOR_LT          : '|<|'   ;

SEQUENCE          : '|;|'   ;
SEQUENCE_SIDE     : '|/;|'  ;
SEQUENCE_WEAK     : '|;;|'  ;


////////////////////////////////////////////////////////////////////////////////
///// ATTRIBUTE LVALUE
////////////////////////////////////////////////////////////////////////////////

Attr_PUBLIC
  : '@public'
  ;

Attr_STATIC
  : '@static'
  ;

Attr_FINAL
  : '@final'
  ;

Attr_VOLATILE
  : '@volatile'
  ;

Attr_REFERENCE
  : '@reference'
  ;

Attr_UFI
  : '@ufi'
  ;

Attr_NAME
  : '@name'
  ;

Attr_TYPE
  : '@type'
  ;

Attr_DESIGN
  : '@design'
  ;

Attr_DIVERSITY
  : '@diversity'
  ;

Attr_FAVM
  : '@favm'
  ;

Attr_SEW
  : '@sew'
  ;




AtLeftValueIdentifier
  :	AT  LeftValueIdentifier
  { setText( getText().substr(1) ); }
  ;

fragment
LeftValueIdentifier
  : ( ~( ':' | '=' | '<' | '{' | '[' | ' ' | '\t' | '\f' | '\n' |'\r' ) )+
  ;


////////////////////////////////////////////////////////////////////////////////
///// NUMERIC LITERAL
////////////////////////////////////////////////////////////////////////////////


// Numeric Constants:

fragment
LongSuffix
	:	'l'
	|	'L'
	;

fragment
UnsignedSuffix
	:	'u'
	|	'U'
	;

fragment
FloatSuffix
	:	'f'
	|	'F'
	|	'd'
	|	'D'
	;

fragment
Exponent
	:
		('e'|'E') ('+'|'-')? (Digit)+
	;

FloatingPointNumber
	: (Digit)+
		( '.' (Digit)* (Exponent)?
		| Exponent
		)
		( FloatSuffix
		| LongSuffix
		)?

	| '.'
		(	(Digit)+ (Exponent)?
			( FloatSuffix
			| LongSuffix
			)?
		)
	;


IntegerNumber
	: (Digit)+
		( LongSuffix
		| UnsignedSuffix
		)*
	;





////////////////////////////////////////////////////////////////////////////////
///// CHAR STRING LITERAL
////////////////////////////////////////////////////////////////////////////////


CharacterLiteral
 	: '\''  CHAR  '\''
	{ setText( std::string( 1 , getText().at(1) ) ); }
	;

fragment
CHAR
  : ( EscapeSequence | ~('\''|'\\') )
  ;


DoubleQuotedString
	: '"'  DQS  '"'
	{ 
		if( (getText() == "\"\"") || (getText().size() < 3) ) { setText( "" ); }
		else { setText( getText().substr(1, getText().length() - 2) ); }
	}
	;

fragment
DQS
  : ( EscapeSequence | ~( '\\' | '"' ) )*
  ;


SingleQuotedString
	: '\''  SQS  '\''
	{ 
		if( getText().size() < 3 )   { setText( "" ); }
		else { setText( getText().substr(1, getText().length() - 2) ); }
	}
	;

fragment
SQS
  : ( EscapeSequence | ~( '\\' | '\'' ) ) ( EscapeSequence | ~( '\\' | '\'' ) )+
  ;


fragment
EscapeSequence
  : '\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')
  | UnicodeEscape
  | OctalEscape
  ;

fragment
OctalEscape
  : '\\' ('0'..'3') ('0'..'7') ('0'..'7')
  | '\\' ('0'..'7') ('0'..'7')
  | '\\' ('0'..'7')
  ;

fragment
UnicodeEscape
  :   '\\' 'u' HexDigit HexDigit HexDigit HexDigit
  ;

fragment
HexDigit
  : ( Digit | 'a'..'f' | 'A'..'F' )
  ;


////////////////////////////////////////////////////////////////////////////////
///// IDENTIFIER
////////////////////////////////////////////////////////////////////////////////

/*
UFI
  : Identifier ( '.' Identifier )+
  ;
UfiLocator
	: Letter ( Letter | Digit )* ( '#' ( Digit )+ )?  COLON2!
	;

*/


Identifier
//options { testLiterals=true; }
  :   Letter ( Letter | Digit | '#' | '/' )*
  ;

/**I found this char range in JavaCC's grammar, but Letter and Digit overlap.
   Still works, but...
*/
fragment
Letter
	:	'A'..'Z'
	|	'a'..'z'

	|	'$'
	|	'_'
	;

fragment
Digit
	: '0'..'9'
	;



////////////////////////////////////////////////////////////////////////////////
///// COMMENT RULE
////////////////////////////////////////////////////////////////////////////////

// Single or Multi line comments
//COMMENT
//	: '//' ~[\r\n]*  -> skip
//	| '/*' .*? '*/'  -> skip
//	| '(*' .*? '*)'  -> skip
//	;


// Single-line comments
COMMENT_SINGLE_LINE
  :	'//'  (~('\n'|'\r'))* ('\n'|'\r'('\n')?)?  -> skip
  ;

// Multi-line comments
COMMENT_MULTI_LINE
  : '/*' .*? ('*/' | EOF)  -> skip
  ;

COMMENT_MULTI_LINE_2
  : '(*' .*? ('*)' | EOF)  -> skip
  ;


////////////////////////////////////////////////////////////////////////////////
///// WHITESPACE IGNORED
////////////////////////////////////////////////////////////////////////////////

//WHITESPACE
//	: [ \t\r\n\u000C]+ -> skip
//	;

WHITESPACE
  : ( ' ' |	'\t' | '\f' |
    // handle newlines
      (
        '\r\n'  // Evil DOS
      |	'\r'    // Macintosh
      |	'\n'    // Unix (the right way)
      )
//    { newline(); }
	)  -> skip
  ;


