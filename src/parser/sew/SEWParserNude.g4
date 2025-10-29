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

/* CPP */

parser grammar SEWParserNude;

options {
	language   = Cpp;
	
	tokenVocab = SEWLexer;
}

//options
//{
//  language  = "Cpp";
//  namespace = "sep";
//  namespaceStd = "std";
//  namespaceAntlr = "antlr";
//  genHashLines = false;         // too many compiler warnings when generating #line statements
//}

//options
//{
//	defaultErrorHandler = true;
//	codeGenMakeSwitchThreshold = 10;
//
////	backtrack = true;
//	k = 4;
//}


// These are all supported parser sections:

// Parser file header. Appears at the top in all parser related files. Use e.g. for copyrights.
@parser::header {
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
	
/* parser/listener/visitor header section */
}

// Appears before any #include in h + cpp files.
@parser::preinclude {/* parser precinclude section */

	#include <map>
	#include <string>

	#include <common/BF.h>
	#include <common/Element.h>
	#include <common/NamedElement.h>

	#include <parser/model/ParserUtil.h>

	#include <fml/common/LocationElement.h>

	#include <fml/expression/AvmCode.h>
	#include <fml/expression/BuiltinArray.h>
	#include <fml/expression/ExpressionConstructor.h>
	#include <fml/expression/StatementConstructor.h>

	#include <fml/operator/Operator.h>
	#include <fml/operator/OperatorManager.h>

	#include <fml/workflow/Query.h>
	#include <fml/workflow/UniFormIdentifier.h>

	#include <fml/workflow/WObject.h>

}

// Follows directly after the standard #includes in h + cpp files.
@parser::postinclude {
/* parser postinclude section */
#ifndef _WIN32
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif
}

// Directly preceeds the parser class declaration in the h file (e.g. for additional types etc.).
@parser::context {/* parser context section */}

// Appears in the private part of the parser in the h file.
// The function bodies could also appear in the definitions section, but I want to maximize
// Java compatibility, so we can also create a Java parser from this grammar.
// Still, some tweaking is necessary after the Java file generation (e.g. bool -> boolean).
@parser::members {
/* public parser declarations/members section */
bool myAction() { return true; }
bool doesItBlend() { return true; }
void cleanUp() {}
void doInit() {}
void doAfter() {}

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
	inline std::size_t hasError() const
	{
		return( noOfErrors > 0 );
	}

	inline std::size_t numberOfErrors() const
	{
		return noOfErrors;
	}

	inline void resetErrors()
	{
		noOfErrors = 0;
	}

//	static const std::string versionInfo()
//	{
//		static std::string   info = "$ Id: WorkflowParser.g, v 0.1 2017/12/21 Lapitre $";
//
//		return info;
//	}


	void reportError( const std::string & errorMessage )
	{
		reportMessage( errorMessage );
		++noOfErrors;
	}

//	void reportError( const antlr::RecognitionException & ex )
//	{
//		AVM_OS_CERR << std::endl << ex.toString().c_str();
//		++noOfErrors;
//	}

	void reportMessage( const std::string & message )
	{
		if( getFilename().length() > 0 )
		{
			AVM_OS_CERR << getFilename() << ":";
		}

		AVM_OS_CERR << getCurrentToken()->getLine() << ":"
				<< getCurrentToken()->getCharPositionInLine()
				<< " [error] " << message << std::endl;
	}


	void setLocation(WObject * wfObject, int bLine, int eLine,
			int bOffset, int eOffset)
	{
		wfObject->setLocation(getFilename(), bLine, eLine);
	}

	void setLocation(TraceableElement & aTraceableElement, int bLine, int eLine,
			int bOffset, int eOffset)
	{
		aTraceableElement.setLocation(getFilename(), bLine, eLine);
	}

	void setLocation(TraceableElement * aTraceableElement, int bLine, int eLine,
			int bOffset, int eOffset)
	{
		aTraceableElement->setLocation(getFilename(), bLine, eLine);
	}


	void setLocation(TraceableElement * aTraceableElement, int bLine, int eLine)
	{
		aTraceableElement->setLocation(getFilename(), bLine, eLine);
	}


	int getNextTokenLine()
	{
		return( getCurrentToken()->getLine() );
	}

	int getNextTokenStartIndex()
	{
		return 1;//( getCurrentToken()(1).getLine() );
	}

	int getNextTokenStopIndex()
	{
		return 1;//( getCurrentToken().getLine() );
	}


	void addElement(WObject * wfContainer, WObject * wfObject)
	{
		if( (wfContainer != WObject::_NULL_) && (wfObject != WObject::_NULL_) )
		{
			wfContainer->append( wfObject );
		}
	}

}


// Appears in the public part of the parser in the h file.
@parser::declarations {/* private parser declarations section */
	
	std::string mFilename;
	
	std::size_t   noOfErrors;

	WObjectManager * mWObjectManager;

}

// Appears in line with the other class member definitions in the cpp file.
@parser::definitions {/* parser definitions section */}

// Additionally there are similar sections for (base)listener and (base)visitor files.
@parser::listenerpreinclude {/* listener preinclude section */}
@parser::listenerpostinclude {/* listener postinclude section */}
@parser::listenerdeclarations {/* listener public declarations/members section */}
@parser::listenermembers {/* listener private declarations/members section */}
@parser::listenerdefinitions {/* listener definitions section */}

@parser::baselistenerpreinclude {/* base listener preinclude section */}
@parser::baselistenerpostinclude {/* base listener postinclude section */}
@parser::baselistenerdeclarations {/* base listener public declarations/members section */}
@parser::baselistenermembers {/* base listener private declarations/members section */}
@parser::baselistenerdefinitions {/* base listener definitions section */}

@parser::visitorpreinclude {/* visitor preinclude section */}
@parser::visitorpostinclude {/* visitor postinclude section */}
@parser::visitordeclarations {/* visitor public declarations/members section */}
@parser::visitormembers {/* visitor private declarations/members section */}
@parser::visitordefinitions {/* visitor definitions section */}

@parser::basevisitorpreinclude {/* base visitor preinclude section */}
@parser::basevisitorpostinclude {/* base visitor postinclude section */}
@parser::basevisitordeclarations {/* base visitor public declarations/members section */}
@parser::basevisitormembers {/* base visitor private declarations/members section */}
@parser::basevisitordefinitions {/* base visitor definitions section */}

// Actual grammar start.

////////////////////////////////////////////////////////////////////////////////
///// UNIQ FORM IDENTIFIER
////////////////////////////////////////////////////////////////////////////////

qualifiedNameID
	: ( ( 'form' COLON2 )
  	  | ( 'meta' COLON2 )
	  | ( Identifier COLON2 )
      | COLON2
	  )?

	  Identifier

	  (  DOT
	  	( Identifier
	  	|  kw_public
	  	|  kw_static
	  	|  kw_final
	  	|  kw_volatile
	  	|  kw_reference
	  	|  kw_buffered
	  	)
	  )*
	;


ufiString
	: ( ( 'form' COLON2 )
  	  | ( 'meta' COLON2 )
	  | ( Identifier COLON2 )

      | COLON2
	  )?

	  Identifier

	  (  DOT
	  	( Identifier
	  	|  kw_public
	  	|  kw_static
	  	|  kw_final
	  	|  kw_volatile
	  	|  kw_reference
	  	|  kw_buffered
	  	)

	  |	LBRACK  avmProgram  RBRACK
	  )*
	;




////////////////////////////////////////////////////////////////////////////////
///// KEYWORD XLIA
////////////////////////////////////////////////////////////////////////////////


kw_public
//	: { getCurrentToken()->getText() == "public" }? Identifier
	: 'public'
	;

kw_static
//	: { getCurrentToken()->getText() == "static" }? Identifier
	: 'static'
	;

kw_final
//	: { getCurrentToken()->getText() == "final" }? Identifier
	: 'final'
	;

kw_reference
//	: { getCurrentToken()->getText() == "reference" }? Identifier
	: 'reference'
	;

kw_buffered
//	: { getCurrentToken()->getText() == "buffered" }? Identifier
	: 'buffered'
	;

kw_volatile
//	: { getCurrentToken()->getText() == "volatile" }? Identifier
	: 'volatile'
	;


kw_form
//	: { getCurrentToken()->getText() == "form" }? Identifier
	: 'form'
	;

kw_endform
//	: { getCurrentToken()->getText() == "endform" }? Identifier
	: 'endform'
	;

kw_prototype
//	: { getCurrentToken()->getText() == "prototype" }? Identifier
	: 'prototype'
	;

kw_endprototype
//	: { getCurrentToken()->getText() == "endprototype" }? Identifier
	: 'endprototype'
	;


kw_as
//	: { getCurrentToken()->getText() == "as" }? Identifier
	: 'as'
	;

kw_is
//	: { getCurrentToken()->getText() == "is" }? Identifier
	: 'is'
	;

////////////////////////////////////////////////////////////////////////////////
///// GRAMMAR FILE DEFINITION
////////////////////////////////////////////////////////////////////////////////

favmProlog
	: ( Attr_DIVERSITY | Attr_SEW | Attr_FAVM )
	  LT_
		Identifier //( 'workflow' | 'configuration' )
		( COMMA ( FloatingPointNumber | qualifiedNameID
				| DoubleQuotedString  | SingleQuotedString )
		)*
	  GT_COLON
	;


//form_grammar
form_grammar
	: ( favmProlog )?
	  ( aNormalForm
	  | aWorkflow
	  )
	;



////////////////////////////////////////////////////////////////////////////////
///// WORKFLOW CONFIGURATION DEFINITION
////////////////////////////////////////////////////////////////////////////////

aWorkflow
	: aWorkflowObject
	;


aWorkflowObject
	: qualifiedNameID

	  ( qualifiedNameID )?

	  ( DoubleQuotedString
	  | SingleQuotedString
	  )?

	  LCURLY
	    ( aComponent )*
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
///// NORMAL FORM DEFINITION
////////////////////////////////////////////////////////////////////////////////

formHEADER
	: qualifiedNameID

	  ( DoubleQuotedString
	  | SingleQuotedString
	  )?

	  kw_as  ( BAND )?  qualifiedNameID
	;


formBODY
	: kw_is  ( aComponent )*
	;


formDECL
	: formHEADER  ( formBODY )?
	;


aNormalForm
	: aForm
	| aPrototype
	| aWObject
	;


aWObject
	: qualifiedNameID

	  ( qualifiedNameID )?

	  ( DoubleQuotedString
	  | SingleQuotedString
	  )?

	  LCURLY
	    ( aComponent )*
	  RCURLY
	;


aForm
	: kw_form  formDECL  kw_endform
	;


aPrototype
	: kw_prototype  formDECL  kw_endprototype
	;


////////////////////////////////////////////////////////////////////////////////
///// COMPONENT DEFINITION
////////////////////////////////////////////////////////////////////////////////

aComponent
	: aWProperty
	| aWSequence
	| aNormalForm
	| tagProgram
	;


////////////////////////////////////////////////////////////////////////////////
///// section <% ID %>
////////////////////////////////////////////////////////////////////////////////

aSequenceComponent
	: aWProperty
	| aNormalForm
	| tagProgram
	;


aWSequence
	: // LeftValueIdentifier
	  Identifier

	  ( DoubleQuotedString
	  | SingleQuotedString
	  )?
	  
	  LBRACK
	  ( aSequenceComponent )*
	  RBRACK

	////////////////////////////////////////////////////////////////////////////
	// DEPRECATED SYNTAX

	| Identifier            COLON  ( aSequenceComponent )*
	| AtLeftValueIdentifier COLON  ( aSequenceComponent )*

	////////////////////////////////////////////////////////////////////////////
	// DEPRECATED SYNTAX

	| 'section' Identifier
	  ( aComponent )*
	  'endsection'?  Identifier
	;




////////////////////////////////////////////////////////////////////////////////
///// ATTRIBUT
////////////////////////////////////////////////////////////////////////////////

aWProperty
///// PREDEFINED ATTRIBUT
	: ( Attr_UFI  EQ  aWPropertyValue
	| Attr_NAME   EQ  aWPropertyValue
	| Attr_TYPE   EQ  aWPropertyValue
	| Attr_DESIGN EQ  aWPropertyValue

	| Attr_PUBLIC EQ  aWPropertyValue
	| Attr_STATIC EQ  aWPropertyValue
	| Attr_FINAL  EQ  aWPropertyValue

	| Attr_VOLATILE  EQ  aWPropertyValue
	| Attr_REFERENCE EQ  aWPropertyValue

	| 'form' anAssignOp  aWPropertyValue
	| 'meta' anAssignOp  aWPropertyValue

	| AtLeftValueIdentifier anAssignOp
	  aWPropertyValue

	| Identifier anAssignOp
	  aWPropertyValue
	)

	( SEMI )?
	;


anAssignOp
	: ASSIGN

	| EQ
	| EQEQ
	| NEQ

	| SEQ
	| NSEQ

	| BANDEQ
	| BOREQ
	| BXOREQ
	| BNOTEQ

	| PLUSEQ
	| MINUSEQ
	| MULTEQ
	| DIVEQ
	| MODEQ

	| GT
	| GTE
	| LT_
	| LTE
	;


//aWPropertyValue
aWPropertyValue
//	: avmProgram
//	;

	: LPROG  anOperator
		( avmProgram  )*
	  RCURLY

	| LPAREN expression RPAREN

	| expression_invoke

	| 'true'
	| 'false'

	| MINUS IntegerNumber

	| PLUS  IntegerNumber

	| IntegerNumber

	| MINUS FloatingPointNumber

	| PLUS  FloatingPointNumber

	| FloatingPointNumber

	| CharacterLiteral

	| DoubleQuotedString

	| SingleQuotedString

	| ufiString

	| BAND ufiString

	| aSymbolOperator

	| anArrayForm
	;

////////////////////////////////////////////////////////////////////////////////
///// GENERIC DEFINITION
////////////////////////////////////////////////////////////////////////////////

aReference
	: BAND ufiString
	;


////////////////////////////////////////////////////////////////////////////////
///// TAG PROGRAM DEFINITION
////////////////////////////////////////////////////////////////////////////////

tagProgram
	: AtLeftValueIdentifier LCURLY  avmProgram
	RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
///// PROGRAM DEFINITION
////////////////////////////////////////////////////////////////////////////////

avmProgram
	: LPROG  anOperator
	  ( avmProgram  )*
	  RCURLY

	| LPAREN expression RPAREN

	| expression_invoke

	| anAtom
	;


anOperator
	: aSymbolOperator

//!g4!	| { ($operation = OperatorManager::getOp(getCurrentToken()->getText())) != NULL }? Identifier
//	| { OperatorManager::getOp(getCurrentToken()->getText()) != NULL }? Identifier
    | Identifier
	;


aSymbolOperator
	: PLUS
	| MINUS
	| MULT
	| DIV
	| MOD

	| POW

	| EQ
	| EQEQ
	| NEQ

	| SEQ
	| NSEQ

	| GT
	| GTE
	| LT_
	| LTE

	| BNOT
	| BAND
	| BOR
	| BXOR

	| LSHIFT
	| RSHIFT

	| LNOT
	| LAND
	| LOR

	| ASSIGN

	| PUSH
	| POP
	| TOP
	
	| ASSIGN_TOP

	| SEQUENCE
	| SEQUENCE_SIDE
	| SEQUENCE_WEAK

	| INTERLEAVING
	| PARTIAL_ORDER

	| EXCLUSIVE
	| NONDETERMINISM

	| PRIOR_GT
	| PRIOR_LT

	| PARALLEL
	| PRODUCT

	| ASYNC
	| STRONG_SYNC
	| WEAK_SYNC
	;


anAtom
	: 'true'
	| 'false'

	| MINUS IntegerNumber
	| PLUS  IntegerNumber
	| IntegerNumber

	| MINUS FloatingPointNumber
	| PLUS  FloatingPointNumber
	| FloatingPointNumber

	| CharacterLiteral

	| DoubleQuotedString
	| SingleQuotedString

	| ufiString

	| aReference

	| aSymbolOperator

	| anArrayForm
	;


anArrayForm
	: LBRACK
	  ( avmProgram
	    ( COMMA
	    avmProgram
	    )*
	  )?
	 RBRACK
	;




////////////////////////////////////////////////////////////////////////////////
///// EXPRESSION DEFINITION
////////////////////////////////////////////////////////////////////////////////

expression_invoke
	: LPAREN_INVOKE
	    unaryExpression
	    ( Identifier
	    | aSymbolOperator
	    )
	    ( expression )*
	    ( 'provided'  expression
	    | 'from'      unaryExpression
	    | 'to'        unaryExpression
	    | 'activity'  anOperator
	    )?
	  RPAREN
	;


expression
	: conditionalExpression
	;

conditionalExpression
	: conditionalOrExpression
	( QUESTION  expression  COLON  expression )?
	;

conditionalOrExpression
	: conditionalAndExpression
	( LOR  conditionalAndExpression )*
	;

conditionalAndExpression
	: bitwiseOrExpression
	( LAND  bitwiseOrExpression )*
	;

bitwiseOrExpression
	: bitwiseXorExpression
	( BOR  bitwiseXorExpression )*
	;

bitwiseXorExpression
	: bitwiseAndExpression
	( BXOR  bitwiseAndExpression )*
	;

bitwiseAndExpression
	: equalityExpression
	( BAND  equalityExpression )*
	;


equalityExpression
	: relationalExpression
	( equalOp relationalExpression )?
	;

equalOp
	: EQ
	| EQEQ
	| NEQ
	| SEQ
	| NSEQ
	;


relationalExpression
	: shiftExpression
	( relationalOp  shiftExpression )?
	;

relationalOp
	: LTE
	| GTE
	| LT_
	| GT
	;


shiftExpression
	: additiveExpression
	( shiftOp  additiveExpression )*
	;

shiftOp
	: LSHIFT
	| RSHIFT
	;


additiveExpression
	: multiplicativeExpression
	( additiveOp  multiplicativeExpression )*
	;

additiveOp
	: PLUS
	| MINUS
	;


multiplicativeExpression
	: unaryExpression
	( multiplicativeOp  unaryExpression )*
	;

multiplicativeOp
	: MULT
	| DIV
	| MOD
	;


unaryExpression
	: literal
/*
	| PLUS   unaryExpression
	| MINUS  unaryExpression

	| INCR   unaryExpression
	| DECR   unaryExpression
*/
	| LNOT   unaryExpression
	| BNOT   unaryExpression

//	| primary ( INCR | DECR )?

	| expression_invoke

	| LPAREN expression RPAREN
	;
/*
primary
	: ID
	( ( DOT ID )
	| ( LBRACKET expression RBRACKET )
	| LPAREN ( expression ( COMMA expression )* )? RPAREN
	)*
	;
*/

literal
	: 'true'
	| 'false'

	| MINUS IntegerNumber
	| PLUS  IntegerNumber
	| IntegerNumber

	| MINUS FloatingPointNumber
	| PLUS  FloatingPointNumber
	| FloatingPointNumber

	| CharacterLiteral

	| DoubleQuotedString
	| SingleQuotedString

	| ufiString

	| aReference

//	| aSymbolOperator

	| anArrayForm
	;


/* end CPP */

