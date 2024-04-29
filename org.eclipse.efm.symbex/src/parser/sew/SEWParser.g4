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

parser grammar SEWParser;

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

	#include <parser/ParserUtil.h>

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

qualifiedNameID returns [ std::string qNameID ]
	: ( ( 'form' COLON2 { $qNameID = "form::"; } )
  	  | ( 'meta' COLON2 { $qNameID = "meta::"; } )

	  | ( Identifier COLON2  { $qNameID = $Identifier->getText() + "::"; } )

      | COLON2  { $qNameID = "::"; }
	  )?

	  Identifier  { $qNameID = $qNameID + $Identifier->getText(); }

	  (  DOT
	  	( Identifier
	  	|  kw_public    |  kw_static
	  	|  kw_final     |  kw_volatile
	  	|  kw_reference |  kw_buffered
	  	)
		{ $qNameID = $qNameID + "." + $Identifier->getText(); }
	  )*
	;


ufiString returns [ BF bfUFI ]
@init{
  UniFormIdentifier * UFI = new UniFormIdentifier(false);
  $bfUFI = UFI; // for automatic destruction of << UFI >> if need

  int bLine = getNextTokenLine();
  int bOffset = getNextTokenStartIndex();
}
	: ( ( 'form' COLON2 { UFI->setLocator( "form" ); UFI->setAbsolute(); } )
  	  | ( 'meta' COLON2 { UFI->setLocator( "meta" ); UFI->setAbsolute(); } )

	  | ( Identifier COLON2
	    { UFI->setLocator( $Identifier->getText() ); UFI->setAbsolute(); } )

      | COLON2  { UFI->setAbsolute(); }
	  )?

	  Identifier  { UFI->appendField( $Identifier->getText() ); }

	  (  DOT
	  	( id3=Identifier   { UFI->appendField( $id3->getText() ); }
	  	|  kw_public       { UFI->appendField( "public" ); }
	  	|  kw_static       { UFI->appendField( "static" ); }
	  	|  kw_final        { UFI->appendField( "final" ); }
	  	|  kw_volatile     { UFI->appendField( "volatile" ); }
	  	|  kw_reference    { UFI->appendField( "reference" ); }
	  	|  kw_buffered     { UFI->appendField( "buffered" ); }
	  	)

	  |	LBRACK ap=avmProgram[NULL] RBRACK  { UFI->appendIndex( $ap.code ); }
	  )*

	{
		if( UFI->isPureIdentifier() )
		{
			$bfUFI = UFI->popIdentifier();
		}
		else
		{
			setLocation(UFI, bLine, bLine, bOffset, getNextTokenStopIndex());
		}
	}
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
		( COMMA ( 'version:' )? 
			( FloatingPointNumber | qualifiedNameID
			| DoubleQuotedString  | SingleQuotedString )
		)*
	  GT_COLON
	;


//form_grammar[ WObjectManager & aWObjectManager ]
form_grammar[ WObjectManager * aWObjectManager ]
returns [ WObject * wfObject = WObject::_NULL_ ]
@init{
//	mWObjectManager = (& $aWObjectManager);
	mWObjectManager = $aWObjectManager;
}
	: ( favmProlog )?
	  ( nf=aNormalForm[ &( mWObjectManager->ROOT_WOBJECT ) ]
	  { $wfObject = $nf.wfObject; }
	  | wf=aWorkflow  [ &( mWObjectManager->ROOT_WOBJECT ) ]
	  { $wfObject = $wf.wfObject; }
	  )
	{
		$wfObject->setContainer(WObject::_NULL_);

		if( hasError() )
		{
			AVM_OS_CERR << std::endl;
		}
	}
	;



////////////////////////////////////////////////////////////////////////////////
///// WORKFLOW CONFIGURATION DEFINITION
////////////////////////////////////////////////////////////////////////////////

aWorkflow [ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
@init{
	$wfObject = mWObjectManager->newWObject($wfContainer, "", "");

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: aWorkflowObject[$wfContainer, $wfObject, bLine, bOffset]
	;


aWorkflowObject[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
	: qnid=qualifiedNameID  { $wfObject->setQualifiedTypeNameID( $qnid.qNameID ); }

	  ( qnid=qualifiedNameID )?
	  {
		if( NamedElement::isRelative($qnid.qNameID) )
		{
			mWObjectManager->registerWObject($wfObject, $qnid.qNameID);

			$qnid.qNameID = mWObjectManager->makeFQN( $wfContainer, $qnid.qNameID );
		}
		$wfObject->setFullyQualifiedNameID($qnid.qNameID);

		mWObjectManager->registerWObject( $wfObject );
	  }

	  ( dqs=DoubleQuotedString  { $wfObject->setUnrestrictedName( $dqs->getText() ); }
	  | sqs=SingleQuotedString  { $wfObject->setUnrestrictedName( $sqs->getText() ); }
	  )?

	  LCURLY

	    ( wComp=aComponent[$wfObject]  { addElement($wfObject, $wComp.wfObject); } )*

	  { setLocation($wfObject, $bLine, getNextTokenLine(), $bOffset, getNextTokenStopIndex()); }
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
///// NORMAL FORM DEFINITION
////////////////////////////////////////////////////////////////////////////////

formHEADER [ WObject * wfContainer, WObject * wfObject ]
	: qnid=qualifiedNameID
	  {
		if( NamedElement::isRelative($qnid.qNameID) ) {
			mWObjectManager->registerWObject($wfObject, $qnid.qNameID);

			$qnid.qNameID = mWObjectManager->makeFQN( $wfContainer, $qnid.qNameID );
		}
		$wfObject->setFullyQualifiedNameID($qnid.qNameID);

		mWObjectManager->registerWObject( $wfObject );
	  }

	  ( dqs=DoubleQuotedString  { $wfObject->setUnrestrictedName( $dqs->getText() ); }
	  | sqs=SingleQuotedString  { $wfObject->setUnrestrictedName( $sqs->getText() ); }
	  )?

	  kw_as ( BAND )? qnid=qualifiedNameID
	  { $wfObject->setQualifiedTypeNameID( $qnid.qNameID ); }
	;


formBODY[ WObject * wfContainer , WObject * wfObject]
	: kw_is  ( wComp=aComponent[$wfObject]  { addElement($wfObject, $wComp.wfObject); } )*
	;



formDECL [ WObject * wfContainer , WObject * wfObject]
	: formHEADER[$wfContainer, $wfObject]

	  {
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "parsing wfObject :> "
			<< str_header( $wfObject ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( formBODY[$wfContainer, $wfObject] )?

	  {
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "end" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }
	;


aNormalForm[ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
@init{
	$wfObject = mWObjectManager->newWObject($wfContainer, "", "");

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: aForm[$wfContainer, $wfObject, bLine, bOffset]

	| aPrototype[$wfContainer, $wfObject, bLine, bOffset]

	| aWObject[$wfContainer, $wfObject, bLine, bOffset]
	;


aWObject[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
	: qnid=qualifiedNameID  { $wfObject->setQualifiedTypeNameID( $qnid.qNameID ); }

	  ( qnid=qualifiedNameID )?
	  {
		if( NamedElement::isRelative($qnid.qNameID) ) {
			mWObjectManager->registerWObject($wfObject, $qnid.qNameID);

			$qnid.qNameID = mWObjectManager->makeFQN( $wfContainer, $qnid.qNameID );
		}
		$wfObject->setFullyQualifiedNameID($qnid.qNameID);

		mWObjectManager->registerWObject( $wfObject );
	  }

	  ( dqs=DoubleQuotedString  { $wfObject->setUnrestrictedName( $dqs->getText() ); }
	  | sqs=SingleQuotedString  { $wfObject->setUnrestrictedName( $sqs->getText() ); }
	  )?

	  LCURLY

	    ( wComp=aComponent[$wfObject]  { addElement($wfObject, $wComp.wfObject); } )*

	  { setLocation($wfObject, $bLine, getNextTokenLine(), $bOffset, getNextTokenStopIndex()); }
	  RCURLY
	;


aForm[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
	: kw_form

	  formDECL[$wfContainer, $wfObject]

	  { setLocation($wfObject, $bLine, getNextTokenLine(), $bOffset, getNextTokenStopIndex()); }
	  kw_endform
	;


aPrototype[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
	: kw_prototype

	  formDECL[$wfContainer, $wfObject]

	  { setLocation($wfObject, $bLine, getNextTokenLine(), $bOffset, getNextTokenStopIndex()); }
	  kw_endprototype
	;


////////////////////////////////////////////////////////////////////////////////
///// COMPONENT DEFINITION
////////////////////////////////////////////////////////////////////////////////

aComponent [ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
	: wp=aWProperty[$wfContainer]   { $wfObject = $wp.wfProperty; }

	| ws=aWSequence[$wfContainer]   { $wfObject = $ws.wfSequence; }

	| nf=aNormalForm[$wfContainer]  { $wfObject = $nf.wfObject;   }

	| tp=tagProgram[$wfContainer]   { $wfObject = $tp.wfObject;   }
	;


//////////////////////////////////////////////////////////////////////////////
///// section <% ID %>
////////////////////////////////////////////////////////////////////////////////

aSequenceComponent [ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
	: wp=aWProperty[$wfContainer]   { $wfObject = $wp.wfProperty; }

	| nf=aNormalForm[$wfContainer]  { $wfObject = $nf.wfObject; }

	| tp=tagProgram[$wfContainer]   { $wfObject = $tp.wfObject; }
	;


aWSequence [ WObject * wfContainer ] returns [ WObject * wfSequence = WObject::_NULL_ ]
@init{
	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: // lvi=LeftValueIdentifier
	  Identifier
	  {
	  	$wfSequence = mWObjectManager->newWSequence($wfContainer, $Identifier->getText());
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "->@section :> " << $wfSequence->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( dqs=DoubleQuotedString  { $wfSequence->setUnrestrictedName( $dqs->getText() ); }
	  | sqs=SingleQuotedString  { $wfSequence->setUnrestrictedName( $sqs->getText() ); }
	  )?
	  LBRACK

	  ( wSeq=aSequenceComponent[$wfSequence] { addElement($wfSequence, $wSeq.wfObject); } )*

	  { setLocation($wfSequence, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  RBRACK

	////////////////////////////////////////////////////////////////////////////
	// DEPRECATED SYNTAX

	| Identifier  COLON
	  {
	  	$wfSequence = mWObjectManager->newWSequence($wfContainer, $Identifier->getText());

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "->@section :> " << $wfSequence->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( wSeq=aSequenceComponent[$wfSequence] { addElement($wfSequence, $wSeq.wfObject); } )*

	  { setLocation($wfSequence, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }

	| AtLeftValueIdentifier   COLON
	  {
	  	$wfSequence = mWObjectManager->newWSequence($wfContainer, $AtLeftValueIdentifier->getText());

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "->@section :> " << $wfSequence->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( wSeq=aSequenceComponent[$wfSequence] { addElement($wfSequence, $wSeq.wfObject); } )*

	  { setLocation($wfSequence, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }

	////////////////////////////////////////////////////////////////////////////
	// DEPRECATED SYNTAX

	| 'section' Identifier
	  {
	  	$wfSequence = mWObjectManager->newWSequence($wfContainer, $Identifier->getText());

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "->section :> " << $wfSequence->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( wComp=aComponent[$wfSequence] { addElement($wfSequence, $wComp.wfObject); } )*

	  { setLocation($wfSequence, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  'endsection'  { getCurrentToken()->getText() == $Identifier->getText() }?  eId=Identifier
	  //{ setLocation($wfSequence, bLine, eId.getLine(), bOffset, ((Token) (eId)).getStopIndex()); }
	;




//////////////////////////////////////////////////////////////////////////////
///// ATTRIBUT
////////////////////////////////////////////////////////////////////////////////

aWProperty [ WObject * wfContainer ]
returns [ WObject * wfProperty = WObject::_NULL_ ]
@init{
	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
///// PREDEFINED ATTRIBUT
	: ( Attr_UFI  EQ  wu=aWPropertyValue[$wfContainer, "ufi"]
	{ $wfProperty = $wu.wfProperty; }
	
	| Attr_NAME   EQ  wn=aWPropertyValue[$wfContainer, "name"]
	{ $wfProperty = $wn.wfProperty; }

	| Attr_TYPE   EQ  wt=aWPropertyValue[$wfContainer, "type"]
	{ $wfProperty = $wt.wfProperty; }

	| Attr_DESIGN EQ  wd=aWPropertyValue[$wfContainer, "design"]
	{ $wfProperty = $wd.wfProperty; }


	| Attr_PUBLIC EQ  wp=aWPropertyValue[$wfContainer, "public"]
	{ $wfProperty = $wp.wfProperty; }

	| Attr_STATIC EQ  ws=aWPropertyValue[$wfContainer, "static"]
	{ $wfProperty = $ws.wfProperty; }

	| Attr_FINAL  EQ  wf=aWPropertyValue[$wfContainer, "final"]
	{ $wfProperty = $wf.wfProperty; }


	| Attr_VOLATILE  EQ  wv=aWPropertyValue[$wfContainer, "volatile"]
	{ $wfProperty = $wv.wfProperty; }

	| Attr_REFERENCE EQ  wr=aWPropertyValue[$wfContainer, "reference"]
	{ $wfProperty = $wr.wfProperty; }


	| 'form' ao=anAssignOp  wform=aWPropertyValue[$wfContainer, "form"]
	{ $wfProperty = $wform.wfProperty;  $wfProperty->setSpecifierOp( $ao.operation ); }

	| 'meta' ao=anAssignOp  wm=aWPropertyValue[$wfContainer, "meta"]
	{ $wfProperty = $wm.wfProperty;  $wfProperty->setSpecifierOp( $ao.operation ); }


	| at_lv=AtLeftValueIdentifier ao=anAssignOp
	  wlva=aWPropertyValue[$wfContainer, $at_lv->getText()]
	{ $wfProperty = $wlva.wfProperty;  $wfProperty->setSpecifierOp( $ao.operation ); }


	| lv=Identifier ao=anAssignOp
	  wida=aWPropertyValue[$wfContainer, $lv->getText()]
	{ $wfProperty = $wida.wfProperty;  $wfProperty->setSpecifierOp( $ao.operation ); }
	)

	{ setLocation($wfProperty, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	( SEMI )?
	;


anAssignOp returns [ AVM_OPCODE operation ]
	: ASSIGN  { $operation = AVM_OPCODE_ASSIGN; }

	| EQ      { $operation = AVM_OPCODE_EQ;     }
	| EQEQ    { $operation = AVM_OPCODE_EQ;     }
	| NEQ     { $operation = AVM_OPCODE_NEQ;    }

	| SEQ     { $operation = AVM_OPCODE_SEQ;    }
	| NSEQ    { $operation = AVM_OPCODE_NSEQ;   }

	| BANDEQ  { $operation = AVM_OPCODE_BAND;   }
	| BOREQ   { $operation = AVM_OPCODE_BOR;    }
	| BXOREQ  { $operation = AVM_OPCODE_BXOR;   }
	| BNOTEQ  { $operation = AVM_OPCODE_BNOT;   }

	| PLUSEQ  { $operation = AVM_OPCODE_PLUS;   }
	| MINUSEQ { $operation = AVM_OPCODE_MINUS;  }
	| MULTEQ  { $operation = AVM_OPCODE_MULT;   }
	| DIVEQ   { $operation = AVM_OPCODE_DIV;    }
	| MODEQ   { $operation = AVM_OPCODE_MOD;    }

	| GT      { $operation = AVM_OPCODE_GT;     }
	| GTE     { $operation = AVM_OPCODE_GTE;    }
	| LT_     { $operation = AVM_OPCODE_LT;     }
	| LTE     { $operation = AVM_OPCODE_LTE;    }
	;


//aWPropertyValue [ WObject * wfContainer , const std::string & aNameID ]
aWPropertyValue [ WObject * wfContainer , std::string aNameID ]
returns [ WObject * wfProperty = WObject::_NULL_ ]
@init{
	BFCode prog;
}
//	: value=avmProgram[$wfContainer]
//	  { $wfProperty = mWObjectManager->newWProperty($wfContainer, aNameID, $value.code); }
//	;

	: LPROG  op=anOperator  
	  { prog = StatementConstructor::newCode($op.operation); }

		( ap=avmProgram[$wfContainer]  { prog->append($ap.code); }  )*

	  //{ setLocation(prog, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  RCURLY
	{
		if( prog.invalid() || ($op.operation == NULL) )
		{
			//!! PARSE ERROR !!
		}
		else if( $op.operation->isOpCode( AVM_OPCODE_MINUS ) && (prog->size() == 1) )
		{
			prog->setOperator( OperatorManager::OPERATOR_UMINUS );
		}
		else if( $op.operation->isOpCode( AVM_OPCODE_IF ) && (prog->size() == 3) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IFE );
		}
		else if( $op.operation->isOpCode( AVM_OPCODE_IFE ) && (prog->size() == 2) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IF );
		}

		$wfProperty = mWObjectManager
				->newWPropertyExpression($wfContainer, aNameID, prog);
	}

	| LPAREN e=expression RPAREN
	{ $wfProperty = mWObjectManager
				->newWPropertyExpression($wfContainer, aNameID, $e.expr);
	}

	| ei=expression_invoke
	{ $wfProperty = mWObjectManager
				->newWPropertyExpression($wfContainer, aNameID, $ei.expr);
	}

	| 'true'
	{ $wfProperty = mWObjectManager
			->newWPropertyBoolean($wfContainer, aNameID, true);
	}

	| 'false'
	{ $wfProperty = mWObjectManager->newWPropertyBoolean(
							$wfContainer, aNameID, false); }

	| MINUS IntegerNumber
	{ $wfProperty = mWObjectManager->newWPropertyInteger(
					$wfContainer, aNameID, "-" + $IntegerNumber->getText() );
	}

	| PLUS  IntegerNumber
	{ $wfProperty = mWObjectManager->newWPropertyInteger(
					$wfContainer, aNameID, $IntegerNumber->getText() );
	}

	| IntegerNumber
	{ $wfProperty = mWObjectManager->newWPropertyInteger(
					$wfContainer, aNameID, $IntegerNumber->getText() );
	}

	| MINUS FloatingPointNumber
	{ $wfProperty = mWObjectManager->newWPropertyFloat(
				$wfContainer, aNameID, "-" + $FloatingPointNumber->getText() );
	}

	| PLUS  FloatingPointNumber
	{ $wfProperty = mWObjectManager->newWPropertyFloat(
					$wfContainer, aNameID, $FloatingPointNumber->getText() );
	}

	| FloatingPointNumber
	{ $wfProperty = mWObjectManager->newWPropertyFloat(
					$wfContainer, aNameID, $FloatingPointNumber->getText() );
	}

	| cl=CharacterLiteral
	{ $wfProperty = mWObjectManager->newWPropertyCharacter(
					$wfContainer, aNameID, $cl->getText().c_str()[0]);
	}

	| dqs=DoubleQuotedString
	{ $wfProperty = mWObjectManager->newWPropertyDoubleQuoteString(
						$wfContainer, aNameID, $dqs->getText());
	}

	| sqs=SingleQuotedString
	{ $wfProperty = mWObjectManager->newWPropertySingleQuoteString(
						$wfContainer, aNameID, $sqs->getText());
	}

	| ufi=ufiString
	{ $wfProperty = mWObjectManager
			->newWPropertyParsedIdentifier($wfContainer, aNameID, $ufi.bfUFI);
	}

	| BAND bufi=ufiString
	{ $wfProperty = mWObjectManager
			->newWPropertyParsedIdentifier($wfContainer, aNameID, $bufi.bfUFI);
	}

	| sop=aSymbolOperator
	{ $wfProperty = mWObjectManager
			->newWPropertyOperator($wfContainer, aNameID, $sop.operation);
	}

	| aa=anArray[WObject::_NULL_]
	{ $wfProperty = mWObjectManager
			->newWPropertyArray($wfContainer, aNameID, $aa.array);
	}

	| al=aList[WObject::_NULL_]
	{ $wfProperty = mWObjectManager
			->newWPropertyArray($wfContainer, aNameID, $al.plist);
	}
	;

////////////////////////////////////////////////////////////////////////////////
///// GENERIC DEFINITION
////////////////////////////////////////////////////////////////////////////////

aReference returns [ BF form ]
	: BAND ufi=ufiString
	{
		$form = mWObjectManager->bfRegisteredWObject( $ufi.bfUFI.str() );
		if( $form.invalid() )
		{
			$form = $ufi.bfUFI;
		}
	}
	;


////////////////////////////////////////////////////////////////////////////////
///// TAG PROGRAM DEFINITION
////////////////////////////////////////////////////////////////////////////////

tagProgram [ WObject * wfContainer ] returns [ WObject * wfObject = WObject::_NULL_ ]
@init{
	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: at_lv=AtLeftValueIdentifier LCURLY  ap=avmProgram[$wfContainer]
	{ $wfObject = mWObjectManager->newWProperty($wfContainer, $at_lv->getText(), $ap.code); }

	{ setLocation($wfObject, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
///// PROGRAM DEFINITION
////////////////////////////////////////////////////////////////////////////////

avmProgram [ WObject * wfContainer ] returns [ BF code ]
@init{
	BFCode prog;

//	int bLine = getNextTokenLine();
//	int bOffset = getNextTokenStartIndex();
}
	: LPROG  op=anOperator
	  { $code = prog = StatementConstructor::newCode($op.operation); }

	( ap=avmProgram[$wfContainer]  { prog->append($ap.code); }  )*

	//{ setLocation(prog, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	RCURLY
	{
		if( prog.invalid() || ($op.operation == NULL) )
		{
			//!! PARSE ERROR !!
		}
		else if( $op.operation->isOpCode( AVM_OPCODE_MINUS ) && (prog->size() == 1) )
		{
			prog->setOperator( OperatorManager::OPERATOR_UMINUS );
		}
		else if( $op.operation->isOpCode( AVM_OPCODE_IF ) && (prog->size() == 3) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IFE );
		}
		else if( $op.operation->isOpCode( AVM_OPCODE_IFE ) && (prog->size() == 2) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IF );
		}
	}

	| LPAREN pe=expression RPAREN  { $code = $pe.expr;  }

	| ie=expression_invoke         { $code = $ie.expr;  }

	| atom=anAtom                  { $code = $atom.form;   }
	;


anOperator returns [ Operator * operation ]
	: s=aSymbolOperator  { $operation = $s.operation; }

//!g4!	| { ($operation = OperatorManager::getOp(getCurrentToken()->getText())) != NULL }? Identifier
	| { OperatorManager::getOp(getCurrentToken()->getText()) != NULL }? Identifier
	{ $operation = OperatorManager::getOp($Identifier->getText()); }
	;


aSymbolOperator returns [ Operator * operation ]
	: PLUS           { $operation = OperatorManager::OPERATOR_PLUS;   }
	| MINUS          { $operation = OperatorManager::OPERATOR_MINUS;  }
	| MULT           { $operation = OperatorManager::OPERATOR_MULT;   }
	| DIV            { $operation = OperatorManager::OPERATOR_DIV;    }
	| MOD            { $operation = OperatorManager::OPERATOR_MOD;    }

	| POW            { $operation = OperatorManager::OPERATOR_POW;    }

	| EQ             { $operation = OperatorManager::OPERATOR_EQ;     }
	| EQEQ           { $operation = OperatorManager::OPERATOR_EQ;     }
	| NEQ            { $operation = OperatorManager::OPERATOR_NEQ;    }

	| SEQ            { $operation = OperatorManager::OPERATOR_SEQ;    }
	| NSEQ           { $operation = OperatorManager::OPERATOR_NSEQ;   }

	| GT             { $operation = OperatorManager::OPERATOR_GT;     }
	| GTE            { $operation = OperatorManager::OPERATOR_GTE;    }
	| LT_            { $operation = OperatorManager::OPERATOR_LT;     }
	| LTE            { $operation = OperatorManager::OPERATOR_LTE;    }

	| BNOT           { $operation = OperatorManager::OPERATOR_BNOT;   }
	| BAND           { $operation = OperatorManager::OPERATOR_BAND;   }
	| BOR            { $operation = OperatorManager::OPERATOR_BOR;    }
	| BXOR           { $operation = OperatorManager::OPERATOR_BXOR;   }

	| LSHIFT         { $operation = OperatorManager::OPERATOR_LSHIFT; }
	| RSHIFT         { $operation = OperatorManager::OPERATOR_RSHIFT; }

	| LNOT           { $operation = OperatorManager::OPERATOR_NOT;    }
	| LAND           { $operation = OperatorManager::OPERATOR_AND;    }
	| LOR            { $operation = OperatorManager::OPERATOR_OR;     }

	| ASSIGN         { $operation = OperatorManager::OPERATOR_ASSIGN; }

	| PUSH           { $operation = OperatorManager::OPERATOR_PUSH;   }
	| POP            { $operation = OperatorManager::OPERATOR_POP;    }
	| TOP            { $operation = OperatorManager::OPERATOR_TOP;    }
	
	| ASSIGN_TOP     { $operation = OperatorManager::OPERATOR_ASSIGN_TOP;     }

	| SEQUENCE       { $operation = OperatorManager::OPERATOR_SEQUENCE;       }
	| SEQUENCE_SIDE  { $operation = OperatorManager::OPERATOR_SEQUENCE_SIDE;  }
	| SEQUENCE_WEAK  { $operation = OperatorManager::OPERATOR_SEQUENCE_WEAK;  }

	| INTERLEAVING   { $operation = OperatorManager::OPERATOR_INTERLEAVING;   }
	| PARTIAL_ORDER  { $operation = OperatorManager::OPERATOR_PARTIAL_ORDER;  }

	| EXCLUSIVE      { $operation = OperatorManager::OPERATOR_EXCLUSIVE;      }
	| NONDETERMINISM { $operation = OperatorManager::OPERATOR_NONDETERMINISM; }

	| PRIOR_GT       { $operation = OperatorManager::OPERATOR_PRIOR_GT; }
	| PRIOR_LT       { $operation = OperatorManager::OPERATOR_PRIOR_LT; }

	| PARALLEL       { $operation = OperatorManager::OPERATOR_PARALLEL; }
	| PRODUCT        { $operation = OperatorManager::OPERATOR_PRODUCT;  }

	| ASYNC          { $operation = OperatorManager::OPERATOR_ASYNCHRONOUS;       }
	| STRONG_SYNC    { $operation = OperatorManager::OPERATOR_STRONG_SYNCHRONOUS; }
	| WEAK_SYNC      { $operation = OperatorManager::OPERATOR_WEAK_SYNCHRONOUS;   }
	;


anAtom returns [ BF form ]
	: 'true'   { $form = ExpressionConstructor::newBoolean(true); }
	| 'false'  { $form = ExpressionConstructor::newBoolean(false); }

	| MINUS mn=IntegerNumber
	{ $form = ExpressionConstructor::newInteger( "-" + $mn->getText() ); }
	
	| PLUS  pn=IntegerNumber
	{ $form = ExpressionConstructor::newInteger( $pn->getText() ); }
	
	| n=IntegerNumber
	{ $form = ExpressionConstructor::newInteger( $n->getText() ); }

	| MINUS mf=FloatingPointNumber
	{ $form = ExpressionConstructor::newFloat( "-" + $mf->getText() ); }
	
	| PLUS  pf=FloatingPointNumber
	{ $form = ExpressionConstructor::newFloat( $pf->getText() ); }
	
	| f=FloatingPointNumber
	{ $form = ExpressionConstructor::newFloat( $f->getText() ); }

	| cl=CharacterLiteral
	{ $form = ExpressionConstructor::newChar( $cl->getText().c_str()[0] ); }

	| dqs=DoubleQuotedString
	{ $form = ExpressionConstructor::newString(
				$dqs->getText() , String::DOUBLE_QUOTE_DELIMITER ); }

	| sqs=SingleQuotedString
	{ $form = ExpressionConstructor::newString(
				$sqs->getText() , String::SINGLE_QUOTE_DELIMITER ); }

	| us=ufiString        { $form = $us.bfUFI;  }

	| ref=aReference      { $form = $ref.form;  }

	| so=aSymbolOperator  { $form = CONST_BF_OP( $so.operation ); }

	| aa=anArray[WObject::_NULL_]  { $form = $aa.array; }

	| al=aList[WObject::_NULL_]    { $form = $al.plist; }
	;


anArray [WObject * wfContainer]  returns [ BF array ]
@init{
	BFVector array;
}
	: LBRACK
	  ( ap=avmProgram[$wfContainer]  { array.append($ap.code); }
	    ( COMMA
	    ap=avmProgram[$wfContainer]  { array.append($ap.code); }
	    )*
	  )?
	 RBRACK
	{
		$array = BuiltinArray::create(array);
	}
	;

aList [WObject * wfContainer]  returns [ BF plist ]
@init{
	BFVector plist;
}
	: LCURLY
	  ( ap=avmProgram[$wfContainer]  { plist.append($ap.code); }
	    ( COMMA
	    ap=avmProgram[$wfContainer]  { plist.append($ap.code); }
	    )*
	  )?
	 RCURLY
	{
		$plist = BuiltinArray::create(plist);
	}
	;




////////////////////////////////////////////////////////////////////////////////
///// EXPRESSION DEFINITION
////////////////////////////////////////////////////////////////////////////////

expression_invoke  returns [ BFCode expr ]
	: LPAREN_INVOKE
	    ue=unaryExpression
	    { $expr = ExpressionConstructor::newCode(
	    			OperatorManager::OPERATOR_INVOKE_METHOD, $ue.expr);
	    }
	    ( id=Identifier       
	    { $expr->append(ParserUtil::getInvokable($ue.expr, $id->getText())); }
	    | sop=aSymbolOperator
	    { $expr->append( INCR_BF($sop.operation) ); }
	    )
	    ( arg=expression                   { $expr->append( $arg.expr  ); } )*
	    ( 'provided'  prov=expression      { $expr->append( $prov.expr ); }
	    | 'from'      from=unaryExpression { $expr->append( $from.expr ); }
	    | 'to'        to=unaryExpression   { $expr->append( $to.expr   ); }
	    | 'activity'  op=anOperator { $expr->append( INCR_BF($op.operation) ); }
	    )?
	  RPAREN
	;


expression  returns [ BF expr ]
	: cond=conditionalExpression  { $expr = $cond.expr; }
	;

conditionalExpression  returns [ BF expr ]
	: cond=conditionalOrExpression         { $expr = $cond.expr; }
	( QUESTION  arg1=expression  COLON  arg2=expression
	{ $expr = ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_IFE, $cond.expr, $arg1.expr, $arg2.expr); }
	)?
	;

conditionalOrExpression  returns [ BF expr ]
	: cond=conditionalAndExpression          { $expr = $cond.expr; }
	( LOR  arg=conditionalAndExpression
	{ $expr = ExpressionConstructor::newCodeFlat(
				OperatorManager::OPERATOR_OR, $cond.expr, $arg.expr); }
	)*
	;

conditionalAndExpression  returns [ BF expr ]
	: bwor=bitwiseOrExpression                { $expr = $bwor.expr; }
	( LAND  arg=bitwiseOrExpression
	{ $expr = ExpressionConstructor::newCodeFlat(
				OperatorManager::OPERATOR_AND, $bwor.expr, $arg.expr); }
	)*
	;

bitwiseOrExpression  returns [ BF expr ]
	: bwxor=bitwiseXorExpression         { $expr = $bwxor.expr; }
	( BOR  arg=bitwiseXorExpression
	{ $expr = ExpressionConstructor::newCodeFlat(
				OperatorManager::OPERATOR_BOR, $bwxor.expr, $arg.expr); }
	)*
	;

bitwiseXorExpression  returns [ BF expr ]
	: bwand=bitwiseAndExpression          { $expr = $bwand.expr; }
	( BXOR  arg=bitwiseAndExpression
	{ $expr = ExpressionConstructor::newCodeFlat(
				OperatorManager::OPERATOR_BXOR, $bwand.expr, $arg.expr); }
	)*
	;

bitwiseAndExpression  returns [ BF expr ]
	: eq=equalityExpression               { $expr = $eq.expr; }
	( BAND  arg=equalityExpression
	{ $expr = ExpressionConstructor::newCodeFlat(
				OperatorManager::OPERATOR_BAND, $eq.expr, $arg.expr); }
	)*
	;


equalityExpression  returns [ BF expr ]
	: rel=relationalExpression          { $expr = $rel.expr; }
	( eo=equalOp arg=relationalExpression
	{ $expr = ExpressionConstructor::newCode($eo.operation, $rel.expr, $arg.expr); }
	)?
	;

equalOp  returns [ const Operator * operation ]
	: EQ    { $operation = OperatorManager::OPERATOR_EQ;   }
	| EQEQ  { $operation = OperatorManager::OPERATOR_EQ;   }
	| NEQ   { $operation = OperatorManager::OPERATOR_NEQ;  }
	| SEQ   { $operation = OperatorManager::OPERATOR_SEQ;  }
	| NSEQ  { $operation = OperatorManager::OPERATOR_NSEQ; }
	;


relationalExpression  returns [ BF expr ]
	: se=shiftExpression                  { $expr = $se.expr; }
	( ro=relationalOp  arg=shiftExpression
	{ $expr = ExpressionConstructor::newCode($ro.operation, $se.expr, $arg.expr); }
	)?
	;

relationalOp  returns [ const Operator * operation ]
	: LTE  { $operation = OperatorManager::OPERATOR_LTE; }
	| GTE  { $operation = OperatorManager::OPERATOR_GTE; }
	| LT_  { $operation = OperatorManager::OPERATOR_LT;  }
	| GT   { $operation = OperatorManager::OPERATOR_GT;  }
	;


shiftExpression  returns [ BF expr ]
	: ae=additiveExpression          { $expr = $ae.expr; }
	( so=shiftOp  arg=additiveExpression
	{ $expr = ExpressionConstructor::newCode($so.operation, $ae.expr, $arg.expr); }
	)*
	;

shiftOp  returns [ const Operator * operation ]
	: LSHIFT  { $operation = OperatorManager::OPERATOR_LSHIFT;  }
	| RSHIFT  { $operation = OperatorManager::OPERATOR_RSHIFT;  }
	;


additiveExpression  returns [ BF expr ]
	: me=multiplicativeExpression       { $expr = $me.expr; }
	( ao=additiveOp  arg=multiplicativeExpression
	{ $expr = ExpressionConstructor::newCode($ao.operation, $me.expr, $arg.expr); }
	)*
	;

additiveOp  returns [ const Operator * operation ]
	: PLUS   { $operation = OperatorManager::OPERATOR_PLUS;  }
	| MINUS  { $operation = OperatorManager::OPERATOR_MINUS;  }
	;


multiplicativeExpression  returns [ BF expr ]
	: ue=unaryExpression                      { $expr = $ue.expr; }
	( mo=multiplicativeOp  arg=unaryExpression
	{ $expr = ExpressionConstructor::newCode($mo.operation, $ue.expr, $arg.expr); }
	)*
	;

multiplicativeOp  returns [ const Operator * operation ]
	: MULT  { $operation = OperatorManager::OPERATOR_MULT; }
	| DIV   { $operation = OperatorManager::OPERATOR_DIV;  }
	| MOD   { $operation = OperatorManager::OPERATOR_MOD;  }
	;


unaryExpression  returns [ BF expr ]
	: lit=literal  { $expr = $lit.expr; }

/*
	| PLUS   pe=unaryExpression
	{ $expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_PLUS, $pe.expr); }

	| MINUS  me=unaryExpression
	{ $expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_UMINUS, $me.expr); }

	| INCR   ier=unaryExpression
	{ $expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_INCR, $ie.expr); }

	| DECR   de=unaryExpression
	{ $expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_DECR, $de.expr); }
*/

	| LNOT   le=unaryExpression
	{ $expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_NOT, $le.expr); }

	| BNOT   be=unaryExpression
	{ $expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_BNOT, $be.expr); }


//	| p=primary ( INCR | DECR )?  { $expr = $p.expr; }


	| i=expression_invoke         { $expr = $i.expr; }

	| LPAREN p=expression RPAREN  { $expr = $p.expr; }
	;
/*
primary  returns [ BF expr ]
	: ID
	( ( DOT ID )
	| ( LBRACKET expression RBRACKET )
	| LPAREN ( expression ( COMMA expression )* )? RPAREN
	)*
	;
*/

literal  returns [ BF expr ]
	: 'true'   
	{ $expr = ExpressionConstructor::newBoolean(true); }
	| 'false' 
	{ $expr = ExpressionConstructor::newBoolean(false); }

	| MINUS mn=IntegerNumber  
	{ $expr = ExpressionConstructor::newInteger( "-" + $mn->getText() ); }

	| PLUS  pn=IntegerNumber
	{ $expr = ExpressionConstructor::newInteger( $pn->getText() ); }

	| n=IntegerNumber         
	{ $expr = ExpressionConstructor::newInteger( $n->getText() ); }

	| MINUS mf=FloatingPointNumber
	{ $expr = ExpressionConstructor::newFloat( "-" + $mf->getText() ); }

	| PLUS  pf=FloatingPointNumber
	{ $expr = ExpressionConstructor::newFloat( $pf->getText() ); }

	| f=FloatingPointNumber
	{ $expr = ExpressionConstructor::newFloat( $f->getText() ); }

	| cl=CharacterLiteral
	{ $expr = ExpressionConstructor::newChar( $cl->getText().c_str()[0] ); }

	| dqs=DoubleQuotedString
	{ $expr = ExpressionConstructor::newString(
				$dqs->getText() , String::DOUBLE_QUOTE_DELIMITER );
	}

	| sqs=SingleQuotedString
	{ $expr = ExpressionConstructor::newString(
				$sqs->getText() , String::SINGLE_QUOTE_DELIMITER );
	}

	| u=ufiString                     { $expr = $u.bfUFI; }

	| r=aReference                    { $expr = $r.form;  }

//	| so=aSymbolOperator              { $expr = CONST_BF_OP( $so.operation ); }

	| aa=anArray[WObject::_NULL_]     { $expr = $aa.array; }

	| al=aList[WObject::_NULL_]       { $expr = $al.plist; }
	;


/* end CPP */

