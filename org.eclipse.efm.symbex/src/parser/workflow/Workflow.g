
/* CPP */
header "pre_include_hpp"
{
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

#include <string>

#include <common/Element.h>
#include <common/NamedElement.h>
#include <common/BF.h>

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


options
{
	language  = "Cpp";
	namespace = "sep";
	namespaceStd = "std";
	namespaceAntlr = "antlr";
	genHashLines = false;         // too many compiler warnings when generating #line statements
}
/* end CPP */


class WorkflowParser extends Parser;

options
{
	defaultErrorHandler = true;
	codeGenMakeSwitchThreshold = 10;

//	backtrack = true;
	k = 4;
}


{


private:
	avm_size_t   noOfErrors;

	WObjectManager * mWObjectManager;


public:

avm_size_t hasError() const
{
	return( noOfErrors > 0 );
}

avm_size_t numberOfErrors() const
{
	return noOfErrors;
}

void resetErrors()
{
	noOfErrors = 0;
}

static const std::string versionInfo()
{
	static std::string   info = "$Id: LiaParser.g, v 0.1 2005/08/23 Lapitre $";

	return info;
}


protected:

void reportError( const std::string & errorMessage )
{
	reportMessage( errorMessage );
	++noOfErrors;
}

void reportError( const antlr::RecognitionException & ex )
{
	AVM_OS_CERR << std::endl << ex.toString().c_str();
	++noOfErrors;
}

void reportMessage( const std::string & message )
{
	if( getFilename().length() > 0 )
	{
		AVM_OS_CERR << getFilename() << ":";
	}

	AVM_OS_CERR << LT( 1 ) -> getLine() << ":" << LT( 1 )->getColumn()
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
	return( LT(1)->getLine() );
}

int getNextTokenStartIndex()
{
	return 1;//( LT(1).getLine() );
}

int getNextTokenStopIndex()
{
	return 1;//( LT(1).getLine() );
}


void addElement(WObject * wfContainer, WObject * wfObject)
{
	if( (wfContainer != WObject::_NULL_) && (wfObject != WObject::_NULL_) )
	{
		wfContainer->append( wfObject );
	}
}


}



////////////////////////////////////////////////////////////////////////////////
///// UNIQ FORM IDENTIFIER
////////////////////////////////////////////////////////////////////////////////

qualifiedNameID returns [ std::string qNameID ]
	: ( "form"
		( COLON_SLASH  { qNameID = std::string("form") + FQN_ID_SCHEME_PATH_SEPARATOR; }
		| COLON2       { qNameID = std::string("form") + FQN_ID_ROOT_SEPARATOR;        }
		)
	  | "meta"
		( COLON_SLASH  { qNameID = std::string("meta") + FQN_ID_SCHEME_PATH_SEPARATOR; }
		| COLON2       { qNameID = std::string("meta") + FQN_ID_ROOT_SEPARATOR;        }
		)

	  | id:Identifier
		( COLON_SLASH  { qNameID = id->getText() + FQN_ID_SCHEME_PATH_SEPARATOR; }
		| COLON2       { qNameID = id->getText() + FQN_ID_ROOT_SEPARATOR;        }
		)

	  | COLON_SLASH  { qNameID = FQN_ID_SCHEME_PATH_SEPARATOR; }
	  | COLON2       { qNameID = FQN_ID_ROOT_SEPARATOR;        }
	  )?

	  id2:Identifier  { qNameID = qNameID + id2->getText(); }

	  (  DOT
	  	( id3:Identifier
	  	|  kw_public    |  kw_static
	  	|  kw_final     |  kw_volatile
	  	|  kw_reference |  kw_buffered
	  	)
		{ qNameID = qNameID + "." + id3->getText(); }
	  )*
	;


ufiString returns [ BF bfUFI ]
{
	std::string s;

	UniFormIdentifier * UFI = new UniFormIdentifier(false);
	bfUFI = UFI; // for automatic destruction of << UFI >> if need

	BF ap;

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: ( ( "form" COLON2 { UFI->setLocator( "form" ); UFI->setAbsolute(); } )
	  | ( "meta" COLON2 { UFI->setLocator( "meta" ); UFI->setAbsolute(); } )

	  | ( id:Identifier COLON2
	    { UFI->setLocator( id->getText() ); UFI->setAbsolute(); } )

	  | COLON2  { UFI->setAbsolute(); }
	  )?

	  id2:Identifier  { UFI->appendField( id2->getText() ); }

	  (  DOT
	  	( id3:Identifier   { UFI->appendField( id3->getText() ); }
	  	|  kw_public       { UFI->appendField( "public" ); }
	  	|  kw_static       { UFI->appendField( "static" ); }
	  	|  kw_final        { UFI->appendField( "final" ); }
	  	|  kw_volatile     { UFI->appendField( "volatile" ); }
	  	|  kw_reference    { UFI->appendField( "reference" ); }
	  	|  kw_buffered     { UFI->appendField( "buffered" ); }
	  	)

	  |	( LBRACK avmProgram[WObject::_NULL_] RBRACK )
	    => LBRACK ap=avmProgram[WObject::_NULL_] RBRACK  { UFI->appendIndex( ap ); }
	  )*

	{
		if( UFI->isPureIdentifier() )
		{
			bfUFI = UFI->popIdentifier();
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
//	: { LT(1)->getText() == "public" }? Identifier
	: "public"
	;

kw_static
//	: { LT(1)->getText() == "static" }? Identifier
	: "static"
	;

kw_final
//	: { LT(1)->getText() == "final" }? Identifier
	: "final"
	;

kw_reference
//	: { LT(1)->getText() == "reference" }? Identifier
	: "reference"
	;

kw_buffered
//	: { LT(1)->getText() == "buffered" }? Identifier
	: "buffered"
	;

kw_volatile
//	: { LT(1)->getText() == "volatile" }? Identifier
	: "volatile"
	;


kw_form
//	: { LT(1)->getText() == "form" }? Identifier
	: "form"
	;

kw_endform
//	: { LT(1)->getText() == "endform" }? Identifier
	: "endform"
	;

kw_prototype
//	: { LT(1)->getText() == "prototype" }? Identifier
	: "prototype"
	;

kw_endprototype
//	: { LT(1)->getText() == "endprototype" }? Identifier
	: "endprototype"
	;


kw_as
//	: { LT(1)->getText() == "as" }? Identifier
	: "as"
	;

kw_is
//	: { LT(1)->getText() == "is" }? Identifier
	: "is"
	;

////////////////////////////////////////////////////////////////////////////////
///// GRAMMAR FILE DEFINITION
////////////////////////////////////////////////////////////////////////////////

favmProlog
	: ( Attr_DIVERSITY | Attr_SEW | Attr_FAVM )
	  LT_
		Identifier //( "workflow" | "configuration" )
		( COMMA ( FloatingPointNumber | UFI | EString ) )*
	  GT_COLON
	;


form_grammar[ WObjectManager & aWObjectManager ]
returns [ WObject * wfObject = WObject::_NULL_ ]
{
	mWObjectManager = &( aWObjectManager );
}
	: ( favmProlog )?
	  ( wfObject=aNormalForm[ &( mWObjectManager->ROOT_WOBJECT ) ]
	  |  wfObject=aWorkflow [ &( mWObjectManager->ROOT_WOBJECT ) ]
	  )
	{
		wfObject->setContainer(WObject::_NULL_);

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
{
	wfObject = mWObjectManager->newWObject(wfContainer, "", "");

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: aWorkflowObject[wfContainer, wfObject, bLine, bOffset]
	;


aWorkflowObject[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
{
	WObject * wobject = WObject::_NULL_;

	std::string qnid = "workflow";
}
	: qnid=qualifiedNameID  { wfObject->setQualifiedTypeNameID( qnid ); }

	  ( qnid=qualifiedNameID )?
	  {
		if( NamedElement::isRelative(qnid) )
		{
			mWObjectManager->registerWObject(wfObject, qnid);

			qnid = mWObjectManager->makeFQN( wfContainer, qnid );
		}
		wfObject->setFullyQualifiedNameID(qnid);

		mWObjectManager->registerWObject( wfObject );
	  }

	  ( dqs:DoubleQuotedString  { wfObject->setUnrestrictedName( dqs->getText() ); }
	  | sqs:SingleQuotedString  { wfObject->setUnrestrictedName( sqs->getText() ); }
	  )?

	  LCURLY

	    ( wobject=aComponent[wfObject]  { addElement(wfObject, wobject); } )*

	  { setLocation(wfObject, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
///// NORMAL FORM DEFINITION
////////////////////////////////////////////////////////////////////////////////

formHEADER [ WObject * wfContainer, WObject * wfObject ]
{
	std::string qnid = "";
}
	: qnid=qualifiedNameID
	  {
		if( NamedElement::isRelative(qnid) ) {
			mWObjectManager->registerWObject(wfObject, qnid);

			qnid = mWObjectManager->makeFQN( wfContainer, qnid );
		}
		wfObject->setFullyQualifiedNameID(qnid);

		mWObjectManager->registerWObject( wfObject );
	  }

	  ( dqs:DoubleQuotedString  { wfObject->setUnrestrictedName( dqs->getText() ); }
	  | sqs:SingleQuotedString  { wfObject->setUnrestrictedName( sqs->getText() ); }
	  )?

	  kw_as ( BAND )? qnid=qualifiedNameID
	  { wfObject->setQualifiedTypeNameID( qnid ); }
	;


formBODY[ WObject * wfContainer , WObject * wfObject]
{
	WObject * wobject = WObject::_NULL_;
}
	: kw_is  ( wobject=aComponent[wfObject]  { addElement(wfObject, wobject); } )*
	;



formDECL [ WObject * wfContainer , WObject * wfObject]
	: formHEADER[wfContainer, wfObject]

	  {
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "parsing wfObject :> "
			<< str_header( wfObject ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( formBODY[wfContainer, wfObject] )?

	  {
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "end" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }
	;


aNormalForm[ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
{
	wfObject = mWObjectManager->newWObject(wfContainer, "", "");

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: aForm[wfContainer, wfObject, bLine, bOffset]

	| aPrototype[wfContainer, wfObject, bLine, bOffset]

	| aWObject[wfContainer, wfObject, bLine, bOffset]
	;


aWObject[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
{
	WObject * wobject = WObject::_NULL_;

	std::string qnid = "";
}
	: qnid=qualifiedNameID  { wfObject->setQualifiedTypeNameID( qnid ); }

	  ( qnid=qualifiedNameID )?
	  {
		if( NamedElement::isRelative(qnid) ) {
			mWObjectManager->registerWObject(wfObject, qnid);

			qnid = mWObjectManager->makeFQN( wfContainer, qnid );
		}
		wfObject->setFullyQualifiedNameID(qnid);

		mWObjectManager->registerWObject( wfObject );
	  }

	  ( dqs:DoubleQuotedString  { wfObject->setUnrestrictedName( dqs->getText() ); }
	  | sqs:SingleQuotedString  { wfObject->setUnrestrictedName( sqs->getText() ); }
	  )?

	  LCURLY

	    ( wobject=aComponent[wfObject]  { addElement(wfObject, wobject); } )*

	  { setLocation(wfObject, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  RCURLY
	;


aForm[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
	: kw_form

	  formDECL[wfContainer, wfObject]

	  { setLocation(wfObject, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  kw_endform
	;


aPrototype[ WObject * wfContainer , WObject * wfObject , int bLine , int bOffset ]
	: kw_prototype

	  formDECL[wfContainer, wfObject]

	  { setLocation(wfObject, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  kw_endprototype
	;


////////////////////////////////////////////////////////////////////////////////
///// COMPONENT DEFINITION
////////////////////////////////////////////////////////////////////////////////

aComponent [ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
	: wfObject=aWProperty[wfContainer]

	| wfObject=aWSequence[wfContainer]

	| wfObject=aNormalForm[wfContainer]

	| wfObject=tagProgram[wfContainer]
	;


//////////////////////////////////////////////////////////////////////////////
///// section <% ID %>
////////////////////////////////////////////////////////////////////////////////

aSequenceComponent [ WObject * wfContainer ]
returns [ WObject * wfObject = WObject::_NULL_ ]
	: wfObject=aWProperty[wfContainer]

	| wfObject=aNormalForm[wfContainer]

	| wfObject=tagProgram[wfContainer]
	;


aWSequence [ WObject * wfContainer ] returns [ WObject * section = WObject::_NULL_ ]
{
	WObject * wobject = WObject::_NULL_;

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: // lvi:LeftValueIdentifier
	  lvi:Identifier
	  {
	  	section = mWObjectManager->newWSequence(wfContainer, lvi->getText());
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "=>@section :> " << section->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( dqs:DoubleQuotedString  { section->setUnrestrictedName( dqs->getText() ); }
	  | sqs:SingleQuotedString  { section->setUnrestrictedName( sqs->getText() ); }
	  )?
	  LBRACK

	  ( wobject=aSequenceComponent[section] { addElement(section, wobject); } )*

	  { setLocation(section, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  RBRACK

	////////////////////////////////////////////////////////////////////////////
	// DEPRECATED SYNTAX

	| lvic:Identifier  COLON
	  {
	  	section = mWObjectManager->newWSequence(wfContainer, lvic->getText());

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "=>@section :> " << section->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( wobject=aSequenceComponent[section] { addElement(section, wobject); } )*

	  { setLocation(section, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }

	| at_lv:AtLeftValueIdentifier   COLON
	  {
	  	section = mWObjectManager->newWSequence(wfContainer, at_lv->getText());

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "=>@section :> " << section->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( wobject=aSequenceComponent[section] { addElement(section, wobject); } )*

	  { setLocation(section, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }

	////////////////////////////////////////////////////////////////////////////
	// DEPRECATED SYNTAX

	| "section" id:Identifier
	  {
	  	section = mWObjectManager->newWSequence(wfContainer, id->getText());

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	AVM_OS_TRACE << TAB << "=>section :> " << section->getNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PARSING )
	  }

	  ( wobject=aComponent[section] { addElement(section, wobject); } )*

	  { setLocation(section, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  "endsection"  { LT(1)->getText() == id->getText() }?  eId:Identifier
	  //{ setLocation(section, bLine, eId.getLine(), bOffset, ((Token) (eId)).getStopIndex()); }
	;




//////////////////////////////////////////////////////////////////////////////
///// ATTRIBUT
////////////////////////////////////////////////////////////////////////////////

aWProperty [ WObject * wfContainer ]
returns [ WObject * wfProperty = WObject::_NULL_ ]
{
	AVM_OPCODE op;

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
///// PREDEFINED ATTRIBUT
	: ( Attr_UFI    EQ  wfProperty=aWPropertyValue[wfContainer, "ufi"]

	| Attr_NAME   EQ  wfProperty=aWPropertyValue[wfContainer, "name"]

	| Attr_TYPE   EQ  wfProperty=aWPropertyValue[wfContainer, "type"]

	| Attr_DESIGN EQ  wfProperty=aWPropertyValue[wfContainer, "design"]


	| Attr_PUBLIC EQ  wfProperty=aWPropertyValue[wfContainer, "public"]

	| Attr_STATIC EQ  wfProperty=aWPropertyValue[wfContainer, "static"]

	| Attr_FINAL  EQ  wfProperty=aWPropertyValue[wfContainer, "final"]


	| Attr_VOLATILE  EQ  wfProperty=aWPropertyValue[wfContainer, "volatile"]

	| Attr_REFERENCE EQ  wfProperty=aWPropertyValue[wfContainer, "reference"]


	| "form" op=anAssignOp  wfProperty=aWPropertyValue[wfContainer, "form"]
	  { wfProperty->setSpecifierOp( op ); }

	| "meta" op=anAssignOp  wfProperty=aWPropertyValue[wfContainer, "meta"]
	  { wfProperty->setSpecifierOp( op ); }


	| at_lv:AtLeftValueIdentifier op=anAssignOp
	  wfProperty=aWPropertyValue[wfContainer, at_lv->getText()]
	  { wfProperty->setSpecifierOp( op ); }


	| lv:Identifier op=anAssignOp
	  wfProperty=aWPropertyValue[wfContainer, lv->getText()]
	  { wfProperty->setSpecifierOp( op ); }
	)

	{ setLocation(wfProperty, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	( SEMI )?
	;


anAssignOp returns [ AVM_OPCODE op ]
	: ASSIGN  { op = AVM_OPCODE_ASSIGN; }

	| EQ      { op = AVM_OPCODE_EQ;     }
	| EQEQ    { op = AVM_OPCODE_EQ;     }
	| NEQ     { op = AVM_OPCODE_NEQ;    }

	| SEQ     { op = AVM_OPCODE_SEQ;    }
	| NSEQ    { op = AVM_OPCODE_NSEQ;   }

	| BANDEQ  { op = AVM_OPCODE_BAND;   }
	| BOREQ   { op = AVM_OPCODE_BOR;    }
	| BXOREQ  { op = AVM_OPCODE_BXOR;   }
	| BNOTEQ  { op = AVM_OPCODE_BNOT;   }

	| PLUSEQ  { op = AVM_OPCODE_PLUS;   }
	| MINUSEQ { op = AVM_OPCODE_MINUS;  }
	| MULTEQ  { op = AVM_OPCODE_MULT;   }
	| DIVEQ   { op = AVM_OPCODE_DIV;    }
	| MODEQ   { op = AVM_OPCODE_MOD;    }

	| GT      { op = AVM_OPCODE_GT;     }
	| GTE     { op = AVM_OPCODE_GTE;    }
	| LT_     { op = AVM_OPCODE_LT;     }
	| LTE     { op = AVM_OPCODE_LTE;    }
	;


aWPropertyValue [ WObject * wfContainer , const std::string & aNameID ]
returns [ WObject * wfProperty = WObject::_NULL_ ]
{
	BF value;

	BFCode prog;
	Operator * op = NULL;
	BF ap;
}
//	: value=avmProgram[wfContainer]
//	  { wfProperty = mWObjectManager->newWProperty(wfContainer, aNameID, value); }
//	;

	: LPROG  op=anOperator  { value = prog = StatementConstructor::newCode(op); }

		( ap=avmProgram[wfContainer]  { prog->append(ap); }  )*

	  //{ setLocation(prog, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	  RCURLY
	{
		if( prog.invalid() || (op == NULL) )
		{
			//!! PARSE ERROR !!
		}
		else if( op->isOpCode( AVM_OPCODE_MINUS ) && (prog->size() == 1) )
		{
			prog->setOperator( OperatorManager::OPERATOR_UMINUS );
		}
		else if( op->isOpCode( AVM_OPCODE_IF ) && (prog->size() == 3) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IFE );
		}
		else if( op->isOpCode( AVM_OPCODE_IFE ) && (prog->size() == 2) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IF );
		}

		wfProperty = mWObjectManager
				->newWPropertyExpression(wfContainer, aNameID, value);
	}

	| LPAREN value=expression RPAREN
	{ wfProperty = mWObjectManager
				->newWPropertyExpression(wfContainer, aNameID, value); }

	| value=expression_invoke
	{ wfProperty = mWObjectManager
				->newWPropertyExpression(wfContainer, aNameID, value); }

	| "true"
	{ wfProperty = mWObjectManager
			->newWPropertyBoolean(wfContainer, aNameID, true); }

	| "false"
	{ wfProperty = mWObjectManager->newWPropertyBoolean(
							wfContainer, aNameID, false); }

	| MINUS mn:IntegerNumber
	{ wfProperty = mWObjectManager
			->newWPropertyInteger(wfContainer, aNameID, "-" + mn->getText()); }

	| PLUS  pn:IntegerNumber
	{ wfProperty = mWObjectManager
			->newWPropertyInteger(wfContainer, aNameID, pn->getText()); }

	| n:IntegerNumber
	{ wfProperty = mWObjectManager
			->newWPropertyInteger(wfContainer, aNameID, n->getText()); }

	| MINUS mf:FloatingPointNumber
	{ wfProperty = mWObjectManager
			->newWPropertyFloat(wfContainer, aNameID, "-" + mf->getText()); }

	| PLUS  pf:FloatingPointNumber
	{ wfProperty = mWObjectManager
			->newWPropertyFloat(wfContainer, aNameID, pf->getText()); }

	| f:FloatingPointNumber
	{ wfProperty = mWObjectManager
			->newWPropertyFloat(wfContainer, aNameID, f->getText()); }

	| cl:CharacterLiteral
	{ wfProperty = mWObjectManager->newWPropertyCharacter(
						wfContainer, aNameID, cl->getText().c_str()[0]); }

	| dqs:DoubleQuotedString
	{ wfProperty = mWObjectManager->newWPropertyDoubleQuoteString(
						wfContainer, aNameID, dqs->getText()); }

	| sqs:SingleQuotedString
	{ wfProperty = mWObjectManager->newWPropertySingleQuoteString(
						wfContainer, aNameID, sqs->getText()); }

	| value=ufiString
	{ wfProperty = mWObjectManager
			->newWPropertyParsedIdentifier(wfContainer, aNameID, value); }

	| BAND value=ufiString
	{ wfProperty = mWObjectManager
			->newWPropertyParsedIdentifier(wfContainer, aNameID, value); }

	| op=aSymbolOperator
	{ wfProperty = mWObjectManager
			->newWPropertyOperator(wfContainer, aNameID, op); }

	| value=anArrayForm[WObject::_NULL_]
	{ wfProperty = mWObjectManager
			->newWPropertyArray(wfContainer, aNameID, value); }
	;

////////////////////////////////////////////////////////////////////////////////
///// GENERIC DEFINITION
////////////////////////////////////////////////////////////////////////////////

aReference returns [ BF form ]
{
	BF bfUFI;
}
	: BAND bfUFI=ufiString
	{
		form = mWObjectManager->bfRegisteredWObject( bfUFI.str() );
		if( form.invalid() )
		{
			form = bfUFI;
		}
	}
	;


////////////////////////////////////////////////////////////////////////////////
///// TAG PROGRAM DEFINITION
////////////////////////////////////////////////////////////////////////////////

tagProgram [ WObject * wfContainer ] returns [ WObject * attr = WObject::_NULL_ ]
{
	BF ap;

	int bLine = getNextTokenLine();
	int bOffset = getNextTokenStartIndex();
}
	: at_lv:AtLeftValueIdentifier LCURLY  ap=avmProgram[wfContainer]
	{ attr = mWObjectManager->newWProperty(wfContainer, at_lv->getText(), ap); }

	{ setLocation(attr, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
///// PROGRAM DEFINITION
////////////////////////////////////////////////////////////////////////////////

avmProgram [ WObject * wfContainer ]returns [ BF form ]
{
	BFCode prog;
	Operator * op = NULL;
	BF ap;

//	int bLine = getNextTokenLine();
//	int bOffset = getNextTokenStartIndex();
}
	: LPROG  op=anOperator  { form = prog = StatementConstructor::newCode(op); }

	( ap=avmProgram[wfContainer]  { prog->append(ap); }  )*

	//{ setLocation(prog, bLine, getNextTokenLine(), bOffset, getNextTokenStopIndex()); }
	RCURLY
	{
		if( prog.invalid() || (op == NULL) )
		{
			//!! PARSE ERROR !!
		}
		else if( op->isOpCode( AVM_OPCODE_MINUS ) && (prog->size() == 1) )
		{
			prog->setOperator( OperatorManager::OPERATOR_UMINUS );
		}
		else if( op->isOpCode( AVM_OPCODE_IF ) && (prog->size() == 3) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IFE );
		}
		else if( op->isOpCode( AVM_OPCODE_IFE ) && (prog->size() == 2) )
		{
			prog->setOperator( OperatorManager::OPERATOR_IF );
		}
	}

	| LPAREN form=expression RPAREN

	| form=expression_invoke

	| form=anAtom
	;


anOperator returns [ Operator * op ]
	: op=aSymbolOperator

	| { (op = OperatorManager::getOp(LT(1)->getText())) != NULL }? Identifier
	;


aSymbolOperator returns [ Operator * op ]
	: PLUS   { op = OperatorManager::OPERATOR_PLUS;   }
	| MINUS  { op = OperatorManager::OPERATOR_MINUS;  }
	| MULT   { op = OperatorManager::OPERATOR_MULT;   }
	| DIV    { op = OperatorManager::OPERATOR_DIV;    }
	| MOD    { op = OperatorManager::OPERATOR_MOD;    }

	| POW    { op = OperatorManager::OPERATOR_POW;    }

	| EQ     { op = OperatorManager::OPERATOR_EQ;     }
	| EQEQ   { op = OperatorManager::OPERATOR_EQ;     }
	| NEQ    { op = OperatorManager::OPERATOR_NEQ;    }

	| SEQ    { op = OperatorManager::OPERATOR_SEQ;    }
	| NSEQ   { op = OperatorManager::OPERATOR_NSEQ;   }

	| GT     { op = OperatorManager::OPERATOR_GT;     }
	| GTE    { op = OperatorManager::OPERATOR_GTE;    }
	| LT_    { op = OperatorManager::OPERATOR_LT;     }
	| LTE    { op = OperatorManager::OPERATOR_LTE;    }

	| BNOT   { op = OperatorManager::OPERATOR_BNOT;   }
	| BAND   { op = OperatorManager::OPERATOR_BAND;   }
	| BOR    { op = OperatorManager::OPERATOR_BOR;    }
	| BXOR   { op = OperatorManager::OPERATOR_BXOR;   }

	| LSHIFT { op = OperatorManager::OPERATOR_LSHIFT; }
	| RSHIFT { op = OperatorManager::OPERATOR_RSHIFT; }

	| LNOT   { op = OperatorManager::OPERATOR_NOT;    }
	| LAND   { op = OperatorManager::OPERATOR_AND;    }
	| LOR    { op = OperatorManager::OPERATOR_OR;     }

	| ASSIGN         { op = OperatorManager::OPERATOR_ASSIGN; }

	| PUSH           { op = OperatorManager::OPERATOR_PUSH;   }
	| POP            { op = OperatorManager::OPERATOR_POP;    }
	| TOP            { op = OperatorManager::OPERATOR_TOP;    }
	| ASSIGN_TOP     { op = OperatorManager::OPERATOR_ASSIGN_TOP;     }

	| SEQUENCE       { op = OperatorManager::OPERATOR_SEQUENCE;       }
	| SEQUENCE_SIDE  { op = OperatorManager::OPERATOR_SEQUENCE_SIDE;  }
	| SEQUENCE_WEAK  { op = OperatorManager::OPERATOR_SEQUENCE_WEAK;  }

	|	INTERLEAVING   { op = OperatorManager::OPERATOR_INTERLEAVING;   }

	|	EXCLUSIVE      { op = OperatorManager::OPERATOR_EXCLUSIVE;      }
	| NONDETERMINISM { op = OperatorManager::OPERATOR_NONDETERMINISM; }

	| PRIOR_GT       { op = OperatorManager::OPERATOR_PRIOR_GT; }
	| PRIOR_LT       { op = OperatorManager::OPERATOR_PRIOR_LT; }

	| PARALLEL       { op = OperatorManager::OPERATOR_PARALLEL; }
	| PRODUCT        { op = OperatorManager::OPERATOR_PRODUCT;  }

	| ASYNC          { op = OperatorManager::OPERATOR_ASYNCHRONOUS;       }
	| STRONG_SYNC    { op = OperatorManager::OPERATOR_STRONG_SYNCHRONOUS; }
	| WEAK_SYNC      { op = OperatorManager::OPERATOR_WEAK_SYNCHRONOUS;   }
	;


anAtom returns [ BF form ]
{
	Operator * op = NULL;
}
	: "true"   { form = ExpressionConstructor::newBoolean(true); }
	| "false"  { form = ExpressionConstructor::newBoolean(false); }

	| MINUS mn:IntegerNumber  { form = ExpressionConstructor::newInteger( "-" + mn->getText() ); }
	| PLUS  pn:IntegerNumber  { form = ExpressionConstructor::newInteger( pn->getText() ); }
	| n:IntegerNumber         { form = ExpressionConstructor::newInteger( n->getText() ); }

	| MINUS mf:FloatingPointNumber  { form = ExpressionConstructor::newFloat( "-" + mf->getText() ); }
	| PLUS  pf:FloatingPointNumber  { form = ExpressionConstructor::newFloat( pf->getText() ); }
	| f:FloatingPointNumber         { form = ExpressionConstructor::newFloat( f->getText() ); }

	| cl:CharacterLiteral     { form = ExpressionConstructor::newChar( cl->getText().c_str()[0] ); }

	| dqs:DoubleQuotedString  { form = ExpressionConstructor::newString(
									 dqs->getText() , String::DOUBLE_QUOTE_DELIMITER ); }

	| sqs:SingleQuotedString  { form = ExpressionConstructor::newString(
									 sqs->getText() , String::SINGLE_QUOTE_DELIMITER ); }

	| form=ufiString

	| form=aReference

	| op=aSymbolOperator      { form = CONST_BF_OP( op ); }

	| form=anArrayForm[WObject::_NULL_]
	;


anArrayForm [WObject * wfContainer]  returns [ BF form ]
{
	BFVector array;

	BF ap;
}
	: LBRACK
	  ( ap=avmProgram[wfContainer]  { array.append(ap); }
	    ( COMMA
	    ap=avmProgram[wfContainer]  { array.append(ap); }
	    )*
	  )?
	 RBRACK
	{
	form = BuiltinArray::create(array);
	}
	;




////////////////////////////////////////////////////////////////////////////////
///// EXPRESSION DEFINITION
////////////////////////////////////////////////////////////////////////////////

expression_invoke  returns [ BFCode ac ]
{
	BF e;
	Operator * op = NULL;
}
	: LPAREN_INVOKE
	    e=unaryExpression
	    { ac = ExpressionConstructor::newCode(OperatorManager::OPERATOR_INVOKE_METHOD, e); }
	    ( id:Identifier       { ac->append(ParserUtil::getInvokable(e, id->getText())); }
	    | op=aSymbolOperator  { ac->append( INCR_BF(op) ); }
	    )
	    ( e=expression                     { ac->append(e); } )*
	    ( "provided:"  e=expression        { ac->append(e); }
	    | "from:"      e=unaryExpression   { ac->append(e); }
	    | "to:"        e=unaryExpression   { ac->append(e); }
	    | "activity:"  op=anOperator       { ac->append( INCR_BF(op) ); }
	    )?
	  RPAREN
	;


expression  returns [ BF expr ]
	: expr=conditionalExpression
	;

conditionalExpression  returns [ BF expr ]
{
	BF arg1;
	BF arg2;
}
	: expr=conditionalOrExpression
	( QUESTION  arg1=expression  COLON  arg2=expression
	{ expr = ExpressionConstructor::newCode(
		OperatorManager::OPERATOR_IFE, expr, arg1, arg2); }
	)?
	;

conditionalOrExpression  returns [ BF expr ]
{
	BF arg;
}
	: expr=conditionalAndExpression
	( LOR  arg=conditionalAndExpression
	{ expr = ExpressionConstructor::newCodeFlat(
		OperatorManager::OPERATOR_OR, expr, arg); }
	)*
	;

conditionalAndExpression  returns [ BF expr ]
{
	BF arg;
}
	: expr=bitwiseOrExpression
	( LAND  arg=bitwiseOrExpression
	{ expr = ExpressionConstructor::newCodeFlat(
		OperatorManager::OPERATOR_AND, expr, arg); }
	)*
	;

bitwiseOrExpression  returns [ BF expr ]
{
	BF arg;
}
	: expr=bitwiseXorExpression
	( BOR  arg=bitwiseXorExpression
	{ expr = ExpressionConstructor::newCodeFlat(
		OperatorManager::OPERATOR_BOR, expr, arg); }
	)*
	;

bitwiseXorExpression  returns [ BF expr ]
{
	BF arg;
}
	: expr=bitwiseAndExpression
	( BXOR  arg=bitwiseAndExpression
	{ expr = ExpressionConstructor::newCodeFlat(
		OperatorManager::OPERATOR_BXOR, expr, arg); }
	)*
	;

bitwiseAndExpression  returns [ BF expr ]
{
	BF arg;
}
	: expr=equalityExpression
	( BAND  arg=equalityExpression
	{ expr = ExpressionConstructor::newCodeFlat(
		OperatorManager::OPERATOR_BAND, expr, arg); }
	)*
	;


equalityExpression  returns [ BF expr ]
{
	Operator * op = NULL;
	BF arg;
}
	: expr=relationalExpression
	( op=equalOp arg=relationalExpression
	{ expr = ExpressionConstructor::newCode(op, expr, arg); }
	)?
	;

equalOp  returns [ Operator * op ]
	: EQ    { op = OperatorManager::OPERATOR_EQ;   }
	| EQEQ  { op = OperatorManager::OPERATOR_EQ;   }
	| NEQ   { op = OperatorManager::OPERATOR_NEQ;  }
	| SEQ   { op = OperatorManager::OPERATOR_SEQ;  }
	| NSEQ  { op = OperatorManager::OPERATOR_NSEQ; }
	;


relationalExpression  returns [ BF expr ]
{
	Operator * op = NULL;
	BF arg;
}
	: expr=shiftExpression
	( op=relationalOp  arg=shiftExpression
	{ expr = ExpressionConstructor::newCode(op, expr, arg); }
	)?
	;

relationalOp  returns [ Operator * op ]
	: LTE  { op = OperatorManager::OPERATOR_LTE; }
	| GTE  { op = OperatorManager::OPERATOR_GTE; }
	| LT_  { op = OperatorManager::OPERATOR_LT;  }
	| GT   { op = OperatorManager::OPERATOR_GT;  }
	;


shiftExpression  returns [ BF expr ]
{
	Operator * op = NULL;
	BF arg;
}
	: expr=additiveExpression
	( op=shiftOp  arg=additiveExpression
	{ expr = ExpressionConstructor::newCode(op, expr, arg); }
	)*
	;

shiftOp  returns [ Operator * op ]
	: LSHIFT  { op = OperatorManager::OPERATOR_LSHIFT;  }
	| RSHIFT  { op = OperatorManager::OPERATOR_RSHIFT;  }
	;


additiveExpression  returns [ BF expr ]
{
	Operator * op = NULL;
	BF arg;
}
	: expr=multiplicativeExpression
	( op=additiveOp  arg=multiplicativeExpression
	{ expr = ExpressionConstructor::newCode(op, expr, arg); }
	)*
	;

additiveOp  returns [ Operator * op ]
	: PLUS   { op = OperatorManager::OPERATOR_PLUS;  }
	| MINUS  { op = OperatorManager::OPERATOR_MINUS;  }
	;


multiplicativeExpression  returns [ BF expr ]
{
	Operator * op = NULL;
	BF arg;
}
	: expr=unaryExpression
	( op=multiplicativeOp  arg=unaryExpression
	{ expr = ExpressionConstructor::newCode(op, expr, arg); }
	)*
	;

multiplicativeOp  returns [ Operator * op ]
	: MULT  { op = OperatorManager::OPERATOR_MULT; }
	| DIV   { op = OperatorManager::OPERATOR_DIV;  }
	| MOD   { op = OperatorManager::OPERATOR_MOD;  }
	;


unaryExpression  returns [ BF expr ]
	: expr=literal

/*
	| PLUS   expr=unaryExpression
	{ expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_PLUS, expr); }

	| MINUS  expr=unaryExpression
	{ expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_UMINUS, expr); }

	| INCR   expr=unaryExpression
	{ expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_INCR, expr); }

	| DECR   expr=unaryExpression
	{ expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_DECR, expr); }
*/

	| LNOT   expr=unaryExpression
	{ expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_NOT, expr); }

	| BNOT   expr=unaryExpression
	{ expr = ExpressionConstructor::newCode(OperatorManager::OPERATOR_BNOT, expr); }


//	| primary ( INCR | DECR )?


	| expr=expression_invoke

	| LPAREN expr=expression RPAREN
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
{
//	Operator * op = NULL;
}
	: "true"   { expr = ExpressionConstructor::newBoolean(true); }
	| "false"  { expr = ExpressionConstructor::newBoolean(false); }

	| MINUS mn:IntegerNumber  { expr = ExpressionConstructor::newInteger( "-" + mn->getText() ); }
	| PLUS  pn:IntegerNumber  { expr = ExpressionConstructor::newInteger( pn->getText() ); }
	| n:IntegerNumber         { expr = ExpressionConstructor::newInteger( n->getText() ); }

	| MINUS mf:FloatingPointNumber  { expr = ExpressionConstructor::newFloat( "-" + mf->getText() ); }
	| PLUS  pf:FloatingPointNumber  { expr = ExpressionConstructor::newFloat( pf->getText() ); }
	| f:FloatingPointNumber         { expr = ExpressionConstructor::newFloat( f->getText() ); }

	| cl:CharacterLiteral     { expr = ExpressionConstructor::newChar( cl->getText().c_str()[0] ); }

	| dqs:DoubleQuotedString  { expr = ExpressionConstructor::newString(
									 dqs->getText() , String::DOUBLE_QUOTE_DELIMITER ); }

	| sqs:SingleQuotedString  { expr = ExpressionConstructor::newString(
									 sqs->getText() , String::SINGLE_QUOTE_DELIMITER ); }

	| expr=ufiString

	| expr=aReference

//| op=aSymbolOperator      { expr = CONST_BF_OP( op ); }

	| expr=anArrayForm[WObject::_NULL_]
	;




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


class WorkflowLexer extends Lexer;

options
{
	charVocabulary = '\0'..'\377';
	k = 6;						// four characters of lookahead

	testLiterals = false;		// don't automatically test for literals

	caseSensitive = true;
	caseSensitiveLiterals = true;
}

/* CPP */
{

private:

	avm_size_t   noOfErrors;


public:

avm_size_t hasError() const
{
	return( noOfErrors > 0 );
}

avm_size_t numberOfErrors() const
{
	return noOfErrors;
}

void resetErrors()
{
	noOfErrors = 0;
}

static const std::string versionInfo()
{
	static std::string   info = "$Id: LiaLexer.g, v 0.1 2005/10/20 Lapitre $";

	return info;
}


protected:

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

	AVM_OS_CERR << getLine() << ":" << getColumn()
				<< " [error] " << message << std::endl;
}

}
/* end CPP */



////////////////////////////////////////////////////////////////////////////////
///// OPERATORS SYMBOLS LITERAL
////////////////////////////////////////////////////////////////////////////////

AT                : '@'   ;

PLUS              : '+'   ;
MINUS             : '-'   ;
MOD				  : '%'	  ;
MULT              : '*'   ;
DIV	              : '/'   ;

POW	              : '^' | "**" ;

ASSIGN            : ":="  ;

PUSH              : "<=<" ;
ASSIGN_TOP        : "^=<" ;
TOP               : "^=>" ;
POP               : ">=>" ;

EQ                : '='   ;

BANDEQ            : "&="  ;
BOREQ             : "|="  ;
BXOREQ            : "^="  ;
BNOTEQ            : "~="  ;

PLUSEQ            : "+="  ;
MINUSEQ           : "-="  ;
MULTEQ            : "*="  ;
DIVEQ             : "/="  ;
MODEQ             : "%="  ;

EQEQ              : "=="  ;
NEQ               : "!="  ;
SEQ               : "===" ;
NSEQ              : "=/=" ;

GT                : '>'   ;
GTE               : ">="  ;
LT_               : '<'   ;
LTE               : "<="  ;

BAND              : '&'   ;
BOR               : '|'   ;
BXOR              : '^'   ;
BNOT              : '~'   ;

LSHIFT            : "<<"  ;
RSHIFT            : ">>"  ;


LAND              : "&&"  ;
LOR               : "||"  ;
LNOT              : '!'   ;

LPAREN            : '('   ;
RPAREN            : ')'   ;

LPAREN_INVOKE     : "(:"  ;

LBRACK            : '['   ;
RBRACK            : ']'   ;


LCURLY            : '{'   ;
RCURLY            : '}'   ;

LPROG             : "${"  ;

LGENERIC          : "<%"  ;
RGENERIC          : "%>"  ;

COMMA             : ','   ;
SEMI              : ';'   ;
COLON             : ':'   ;
COLON2            : "::"  ;
COLON_SLASH       : ":/"  ;
DOT               : '.'   ;
QUESTION          : '?'   ;

GT_COLON          : ">:"  ;

ARROW             : "->"  ;


INTERLEAVING      : "|i|"   ;

ASYNC             : "|a|"   ;
STRONG_SYNC       : "|and|" ;
WEAK_SYNC         : "|or|"  ;
PARALLEL          : "|,|"   ;
PRODUCT           : "|x|"   ;

EXCLUSIVE         : "|xor|" ;
NONDETERMINISM    : "|/\\|" ;

PRIOR_GT          : "|>|"   ;
PRIOR_LT          : "|<|"   ;

SEQUENCE          : "|;|"   ;
SEQUENCE_SIDE     : "|/;|"  ;
SEQUENCE_WEAK     : "|;;|"  ;




////////////////////////////////////////////////////////////////////////////////
///// ATTRIBUTE LVALUE
////////////////////////////////////////////////////////////////////////////////

Attr_PUBLIC
	: "@public"
	;

Attr_STATIC
	: "@static"
	;

Attr_FINAL
	: "@final"
	;

Attr_VOLATILE
	: "@volatile"
	;

Attr_REFERENCE
	: "@reference"
	;

Attr_UFI
	: "@ufi"
	;

Attr_NAME
	: "@name"
	;

Attr_TYPE
	: "@type"
	;

Attr_DESIGN
	: "@design"
	;

Attr_DIVERSITY
	: "@diversity"
	;

Attr_FAVM
	: "@favm"
	;

Attr_SEW
	: "@sew"
	;




AtLeftValueIdentifier
	:	AT !  LeftValueIdentifier
	;

protected
LeftValueIdentifier
	: ( ~( ':' | '=' | '{' | '[' | ' ' | '\t' | '\f' | '\n' |'\r' ) )+
	;


////////////////////////////////////////////////////////////////////////////////
///// NUMERIC LITERAL
////////////////////////////////////////////////////////////////////////////////


// Numeric Constants:

protected
LongSuffix
	:	'l'
	|	'L'
	;

protected
UnsignedSuffix
	:	'u'
	|	'U'
	;

protected
FloatSuffix
	:	'f'
	|	'F'
	|	'd'
	|	'D'
	;

protected
Exponent
	:
		('e'|'E') ('+'|'-')? (Digit)+
	;

Number
	: ( (Digit)+ ('.' | 'e' | 'E') )=>
		(Digit)+
		( '.' (Digit)* (Exponent)?
		| Exponent
		)
		(FloatSuffix
		|LongSuffix
		)?                         {_ttype = FloatingPointNumber;}

	| '.'
		(	(Digit)+ (Exponent)?
			(FloatSuffix
			|LongSuffix
			)?
		)                          {_ttype = FloatingPointNumber;}

	| (Digit)+
		(LongSuffix
		|UnsignedSuffix
		)*                         {_ttype = IntegerNumber;}
	;





////////////////////////////////////////////////////////////////////////////////
///// CHAR STRING LITERAL
////////////////////////////////////////////////////////////////////////////////


CharacterLiteral
	: '\''! CHAR '\''!
	;

protected
CHAR
	: ( EscapeSequence | ~('\''|'\\') )
	;


DoubleQuotedString
	: '"'!  DQS  '"'!
	;

protected
DQS
	: ( EscapeSequence | ~( '\\' | '"' ) )*
	;


SingleQuotedString
	: '\''!  SQS  '\''!
	;

protected
SQS
	: ( EscapeSequence | ~( '\\' | '\'' ) ) ( EscapeSequence | ~( '\\' | '\'' ) )+
	;


protected
EscapeSequence
	: '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\')
	| UnicodeEscape
	| OctalEscape
	;

protected
OctalEscape
	: '\\' ('0'..'3') ('0'..'7') ('0'..'7')
	| '\\' ('0'..'7') ('0'..'7')
	| '\\' ('0'..'7')
	;

protected
UnicodeEscape
	:   '\\' 'u' HexDigit HexDigit HexDigit HexDigit
	;

protected
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
	: Letter ( Letter | Digit )* ( '#' ( Digit )+ )?  (COLON_SLASH|COLON2)!
	;

*/


Identifier
options { testLiterals=true; }
	:   Letter ( Letter | Digit | '#' | '/' )*
	;

/**I found this char range in JavaCC's grammar, but Letter and Digit overlap.
   Still works, but...
*/
protected
Letter
	:	'A'..'Z'
	|	'a'..'z'

	|	'$'
	|	'_'
	;

protected
Digit
	: '0'..'9'
	;



////////////////////////////////////////////////////////////////////////////////
///// COMMENT RULE
////////////////////////////////////////////////////////////////////////////////

// Single-line comments
SL_COMMENT
	:	"//"  (~('\n'|'\r'))* ('\n'|'\r'('\n')?)?
	{
	$setType(antlr::Token::SKIP);
	newline();
	}
	;

// Multi-line comments
COMMENT_MULTI_LINE
	: "/*"
	( options { generateAmbigWarnings=false; }
	:	{ LA(2) != '/' }? '*'
	|	'\r' '\n'	{ newline(); }
	|	'\r'		{ newline(); }
	|	'\n'		{ newline(); }
	|   ~('*' | '\n' | '\r')
	)*
	"*/"
	{
	$setType(antlr::Token::SKIP);
	}
	;

COMMENT_MULTI_LINE_2
	: "(*"
	( options { generateAmbigWarnings=false; }
	:	{ LA(2) != ')' }? '*'
	|	'\r' '\n'	{ newline(); }
	|	'\r'		{ newline(); }
	|	'\n'		{ newline(); }
	|   ~('*' | '\n' | '\r')
	)*
	"*)"
	{
	$setType(antlr::Token::SKIP);
	}
	;


////////////////////////////////////////////////////////////////////////////////
///// WHITESPACE IGNORED
////////////////////////////////////////////////////////////////////////////////

WHITESPACE
	: ( ' ' |	'\t' | '\f' |
	// handle newlines
	  (
	    "\r\n"  // Evil DOS
	  |	'\r'    // Macintosh
	  |	'\n'    // Unix (the right way)
	  )
	  { newline(); }
	)
	{
		$setType(antlr::Token::SKIP);
	}
	;


