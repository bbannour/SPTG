
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


// Generated from SEWLexer.g4 by ANTLR 4.11.1

#pragma once

/* lexer precinclude section */

	#include <printer/OutStream.h>



#include "antlr4-runtime.h"


/* lexer postinclude section */
#ifndef _WIN32
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif


namespace sep {

/* lexer context section */

class  SEWLexer : public antlr4::Lexer {
public:
  enum {
    DUMMY = 1, Version = 2, Public = 3, Final = 4, Static = 5, Volatile = 6, 
    Buffered = 7, Reference = 8, Meta = 9, Form = 10, Endform = 11, Prototype = 12, 
    Endprototype = 13, Section = 14, Endsection = 15, Provided = 16, Activity = 17, 
    From = 18, As = 19, Is = 20, To = 21, True = 22, False = 23, AT = 24, 
    PLUS = 25, MINUS = 26, MOD = 27, MULT = 28, DIV = 29, POW = 30, ASSIGN = 31, 
    PUSH = 32, ASSIGN_TOP = 33, TOP = 34, POP = 35, EQ = 36, BANDEQ = 37, 
    BOREQ = 38, BXOREQ = 39, BNOTEQ = 40, PLUSEQ = 41, MINUSEQ = 42, MULTEQ = 43, 
    DIVEQ = 44, MODEQ = 45, EQEQ = 46, NEQ = 47, SEQ = 48, NSEQ = 49, GT = 50, 
    GTE = 51, LT_ = 52, LTE = 53, BAND = 54, BOR = 55, BXOR = 56, BNOT = 57, 
    LSHIFT = 58, RSHIFT = 59, LAND = 60, LOR = 61, LNOT = 62, LPAREN = 63, 
    RPAREN = 64, LPAREN_INVOKE = 65, LBRACK = 66, RBRACK = 67, LCURLY = 68, 
    RCURLY = 69, LPROG = 70, LGENERIC = 71, RGENERIC = 72, COMMA = 73, SEMI = 74, 
    COLON = 75, COLON2 = 76, DOT = 77, QUESTION = 78, GT_COLON = 79, ARROW = 80, 
    INTERLEAVING = 81, PARTIAL_ORDER = 82, ASYNC = 83, STRONG_SYNC = 84, 
    WEAK_SYNC = 85, PARALLEL = 86, PRODUCT = 87, EXCLUSIVE = 88, NONDETERMINISM = 89, 
    PRIOR_GT = 90, PRIOR_LT = 91, SEQUENCE = 92, SEQUENCE_SIDE = 93, SEQUENCE_WEAK = 94, 
    Attr_PUBLIC = 95, Attr_STATIC = 96, Attr_FINAL = 97, Attr_VOLATILE = 98, 
    Attr_REFERENCE = 99, Attr_UFI = 100, Attr_NAME = 101, Attr_TYPE = 102, 
    Attr_DESIGN = 103, Attr_DIVERSITY = 104, Attr_FAVM = 105, Attr_SEW = 106, 
    AtLeftValueIdentifier = 107, FloatingPointNumber = 108, IntegerNumber = 109, 
    CharacterLiteral = 110, DoubleQuotedString = 111, SingleQuotedString = 112, 
    Identifier = 113, COMMENT_SINGLE_LINE = 114, COMMENT_MULTI_LINE = 115, 
    COMMENT_MULTI_LINE_2 = 116, WHITESPACE = 117
  };

  explicit SEWLexer(antlr4::CharStream *input);

  ~SEWLexer() override;

  /* public lexer declarations section */
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



  std::string getGrammarFileName() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const std::vector<std::string>& getChannelNames() const override;

  const std::vector<std::string>& getModeNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;

  const antlr4::atn::ATN& getATN() const override;

  void action(antlr4::RuleContext *context, size_t ruleIndex, size_t actionIndex) override;

  // By default the static state used to implement the lexer is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
  /* private lexer declarations/members section */

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



  // Individual action functions triggered by action() above.
  void AtLeftValueIdentifierAction(antlr4::RuleContext *context, size_t actionIndex);
  void CharacterLiteralAction(antlr4::RuleContext *context, size_t actionIndex);
  void DoubleQuotedStringAction(antlr4::RuleContext *context, size_t actionIndex);
  void SingleQuotedStringAction(antlr4::RuleContext *context, size_t actionIndex);

  // Individual semantic predicate functions triggered by sempred() above.

};

}  // namespace sep
