
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


// Generated from SEWParser.g4 by ANTLR 4.13.2

#pragma once

/* parser precinclude section */

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



#include "antlr4-runtime.h"


/* parser postinclude section */
#ifndef _WIN32
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif


namespace sep {

/* parser context section */

class  SEWParser : public antlr4::Parser {
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

  enum {
    RuleQualifiedNameID = 0, RuleUfiString = 1, RuleKw_public = 2, RuleKw_static = 3, 
    RuleKw_final = 4, RuleKw_reference = 5, RuleKw_buffered = 6, RuleKw_volatile = 7, 
    RuleKw_form = 8, RuleKw_endform = 9, RuleKw_prototype = 10, RuleKw_endprototype = 11, 
    RuleKw_as = 12, RuleKw_is = 13, RuleFavmProlog = 14, RuleForm_grammar = 15, 
    RuleAWorkflow = 16, RuleAWorkflowObject = 17, RuleFormHEADER = 18, RuleFormBODY = 19, 
    RuleFormDECL = 20, RuleANormalForm = 21, RuleAWObject = 22, RuleAForm = 23, 
    RuleAPrototype = 24, RuleAComponent = 25, RuleASequenceComponent = 26, 
    RuleAWSequence = 27, RuleAWProperty = 28, RuleAnAssignOp = 29, RuleAWPropertyValue = 30, 
    RuleAReference = 31, RuleTagProgram = 32, RuleAvmProgram = 33, RuleAnOperator = 34, 
    RuleASymbolOperator = 35, RuleAnAtom = 36, RuleAnArray = 37, RuleAList = 38, 
    RuleExpression_invoke = 39, RuleExpression = 40, RuleConditionalExpression = 41, 
    RuleConditionalOrExpression = 42, RuleConditionalAndExpression = 43, 
    RuleBitwiseOrExpression = 44, RuleBitwiseXorExpression = 45, RuleBitwiseAndExpression = 46, 
    RuleEqualityExpression = 47, RuleEqualOp = 48, RuleRelationalExpression = 49, 
    RuleRelationalOp = 50, RuleShiftExpression = 51, RuleShiftOp = 52, RuleAdditiveExpression = 53, 
    RuleAdditiveOp = 54, RuleMultiplicativeExpression = 55, RuleMultiplicativeOp = 56, 
    RuleUnaryExpression = 57, RuleLiteral = 58
  };

  explicit SEWParser(antlr4::TokenStream *input);

  SEWParser(antlr4::TokenStream *input, const antlr4::atn::ParserATNSimulatorOptions &options);

  ~SEWParser() override;

  std::string getGrammarFileName() const override;

  const antlr4::atn::ATN& getATN() const override;

  const std::vector<std::string>& getRuleNames() const override;

  const antlr4::dfa::Vocabulary& getVocabulary() const override;

  antlr4::atn::SerializedATNView getSerializedATN() const override;


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



  class QualifiedNameIDContext;
  class UfiStringContext;
  class Kw_publicContext;
  class Kw_staticContext;
  class Kw_finalContext;
  class Kw_referenceContext;
  class Kw_bufferedContext;
  class Kw_volatileContext;
  class Kw_formContext;
  class Kw_endformContext;
  class Kw_prototypeContext;
  class Kw_endprototypeContext;
  class Kw_asContext;
  class Kw_isContext;
  class FavmPrologContext;
  class Form_grammarContext;
  class AWorkflowContext;
  class AWorkflowObjectContext;
  class FormHEADERContext;
  class FormBODYContext;
  class FormDECLContext;
  class ANormalFormContext;
  class AWObjectContext;
  class AFormContext;
  class APrototypeContext;
  class AComponentContext;
  class ASequenceComponentContext;
  class AWSequenceContext;
  class AWPropertyContext;
  class AnAssignOpContext;
  class AWPropertyValueContext;
  class AReferenceContext;
  class TagProgramContext;
  class AvmProgramContext;
  class AnOperatorContext;
  class ASymbolOperatorContext;
  class AnAtomContext;
  class AnArrayContext;
  class AListContext;
  class Expression_invokeContext;
  class ExpressionContext;
  class ConditionalExpressionContext;
  class ConditionalOrExpressionContext;
  class ConditionalAndExpressionContext;
  class BitwiseOrExpressionContext;
  class BitwiseXorExpressionContext;
  class BitwiseAndExpressionContext;
  class EqualityExpressionContext;
  class EqualOpContext;
  class RelationalExpressionContext;
  class RelationalOpContext;
  class ShiftExpressionContext;
  class ShiftOpContext;
  class AdditiveExpressionContext;
  class AdditiveOpContext;
  class MultiplicativeExpressionContext;
  class MultiplicativeOpContext;
  class UnaryExpressionContext;
  class LiteralContext; 

  class  QualifiedNameIDContext : public antlr4::ParserRuleContext {
  public:
    std::string qNameID;
    antlr4::Token *identifierToken = nullptr;
    QualifiedNameIDContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    antlr4::tree::TerminalNode *COLON2();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    antlr4::tree::TerminalNode *Form();
    antlr4::tree::TerminalNode *Meta();
    std::vector<Kw_publicContext *> kw_public();
    Kw_publicContext* kw_public(size_t i);
    std::vector<Kw_staticContext *> kw_static();
    Kw_staticContext* kw_static(size_t i);
    std::vector<Kw_finalContext *> kw_final();
    Kw_finalContext* kw_final(size_t i);
    std::vector<Kw_volatileContext *> kw_volatile();
    Kw_volatileContext* kw_volatile(size_t i);
    std::vector<Kw_referenceContext *> kw_reference();
    Kw_referenceContext* kw_reference(size_t i);
    std::vector<Kw_bufferedContext *> kw_buffered();
    Kw_bufferedContext* kw_buffered(size_t i);

   
  };

  QualifiedNameIDContext* qualifiedNameID();

  class  UfiStringContext : public antlr4::ParserRuleContext {
  public:
    BF bfUFI;
    antlr4::Token *identifierToken = nullptr;
    antlr4::Token *id3 = nullptr;
    SEWParser::AvmProgramContext *ap = nullptr;
    UfiStringContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    antlr4::tree::TerminalNode *COLON2();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LBRACK();
    antlr4::tree::TerminalNode* LBRACK(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RBRACK();
    antlr4::tree::TerminalNode* RBRACK(size_t i);
    std::vector<AvmProgramContext *> avmProgram();
    AvmProgramContext* avmProgram(size_t i);
    antlr4::tree::TerminalNode *Form();
    antlr4::tree::TerminalNode *Meta();
    std::vector<Kw_publicContext *> kw_public();
    Kw_publicContext* kw_public(size_t i);
    std::vector<Kw_staticContext *> kw_static();
    Kw_staticContext* kw_static(size_t i);
    std::vector<Kw_finalContext *> kw_final();
    Kw_finalContext* kw_final(size_t i);
    std::vector<Kw_volatileContext *> kw_volatile();
    Kw_volatileContext* kw_volatile(size_t i);
    std::vector<Kw_referenceContext *> kw_reference();
    Kw_referenceContext* kw_reference(size_t i);
    std::vector<Kw_bufferedContext *> kw_buffered();
    Kw_bufferedContext* kw_buffered(size_t i);

   
  };

  UfiStringContext* ufiString();

  class  Kw_publicContext : public antlr4::ParserRuleContext {
  public:
    Kw_publicContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Public();

   
  };

  Kw_publicContext* kw_public();

  class  Kw_staticContext : public antlr4::ParserRuleContext {
  public:
    Kw_staticContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Static();

   
  };

  Kw_staticContext* kw_static();

  class  Kw_finalContext : public antlr4::ParserRuleContext {
  public:
    Kw_finalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Final();

   
  };

  Kw_finalContext* kw_final();

  class  Kw_referenceContext : public antlr4::ParserRuleContext {
  public:
    Kw_referenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Reference();

   
  };

  Kw_referenceContext* kw_reference();

  class  Kw_bufferedContext : public antlr4::ParserRuleContext {
  public:
    Kw_bufferedContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Buffered();

   
  };

  Kw_bufferedContext* kw_buffered();

  class  Kw_volatileContext : public antlr4::ParserRuleContext {
  public:
    Kw_volatileContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Volatile();

   
  };

  Kw_volatileContext* kw_volatile();

  class  Kw_formContext : public antlr4::ParserRuleContext {
  public:
    Kw_formContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Form();

   
  };

  Kw_formContext* kw_form();

  class  Kw_endformContext : public antlr4::ParserRuleContext {
  public:
    Kw_endformContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Endform();

   
  };

  Kw_endformContext* kw_endform();

  class  Kw_prototypeContext : public antlr4::ParserRuleContext {
  public:
    Kw_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Prototype();

   
  };

  Kw_prototypeContext* kw_prototype();

  class  Kw_endprototypeContext : public antlr4::ParserRuleContext {
  public:
    Kw_endprototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Endprototype();

   
  };

  Kw_endprototypeContext* kw_endprototype();

  class  Kw_asContext : public antlr4::ParserRuleContext {
  public:
    Kw_asContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *As();

   
  };

  Kw_asContext* kw_as();

  class  Kw_isContext : public antlr4::ParserRuleContext {
  public:
    Kw_isContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Is();

   
  };

  Kw_isContext* kw_is();

  class  FavmPrologContext : public antlr4::ParserRuleContext {
  public:
    FavmPrologContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *Identifier();
    antlr4::tree::TerminalNode *GT_COLON();
    antlr4::tree::TerminalNode *Attr_DIVERSITY();
    antlr4::tree::TerminalNode *Attr_SEW();
    antlr4::tree::TerminalNode *Attr_FAVM();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> FloatingPointNumber();
    antlr4::tree::TerminalNode* FloatingPointNumber(size_t i);
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DoubleQuotedString();
    antlr4::tree::TerminalNode* DoubleQuotedString(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SingleQuotedString();
    antlr4::tree::TerminalNode* SingleQuotedString(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Version();
    antlr4::tree::TerminalNode* Version(size_t i);

   
  };

  FavmPrologContext* favmProlog();

  class  Form_grammarContext : public antlr4::ParserRuleContext {
  public:
    WObjectManager * aWObjectManager;
    WObject * wfObject = WObject::_NULL_;
    SEWParser::ANormalFormContext *nf = nullptr;
    SEWParser::AWorkflowContext *wf = nullptr;
    Form_grammarContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    Form_grammarContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObjectManager * aWObjectManager);
    virtual size_t getRuleIndex() const override;
    FavmPrologContext *favmProlog();
    ANormalFormContext *aNormalForm();
    AWorkflowContext *aWorkflow();

   
  };

  Form_grammarContext* form_grammar(WObjectManager * aWObjectManager);

  class  AWorkflowContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject = WObject::_NULL_;
    AWorkflowContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AWorkflowContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    AWorkflowObjectContext *aWorkflowObject();

   
  };

  AWorkflowContext* aWorkflow(WObject * wfContainer);

  class  AWorkflowObjectContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    int bLine;
    int bOffset;
    SEWParser::QualifiedNameIDContext *qnid = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    SEWParser::AComponentContext *wComp = nullptr;
    AWorkflowObjectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AWorkflowObjectContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject, int bLine, int bOffset);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();
    std::vector<AComponentContext *> aComponent();
    AComponentContext* aComponent(size_t i);

   
  };

  AWorkflowObjectContext* aWorkflowObject(WObject * wfContainer,WObject * wfObject,int bLine,int bOffset);

  class  FormHEADERContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    SEWParser::QualifiedNameIDContext *qnid = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    FormHEADERContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    FormHEADERContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject);
    virtual size_t getRuleIndex() const override;
    Kw_asContext *kw_as();
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    antlr4::tree::TerminalNode *BAND();
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();

   
  };

  FormHEADERContext* formHEADER(WObject * wfContainer,WObject * wfObject);

  class  FormBODYContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    SEWParser::AComponentContext *wComp = nullptr;
    FormBODYContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    FormBODYContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject);
    virtual size_t getRuleIndex() const override;
    Kw_isContext *kw_is();
    std::vector<AComponentContext *> aComponent();
    AComponentContext* aComponent(size_t i);

   
  };

  FormBODYContext* formBODY(WObject * wfContainer,WObject * wfObject);

  class  FormDECLContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    FormDECLContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    FormDECLContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject);
    virtual size_t getRuleIndex() const override;
    FormHEADERContext *formHEADER();
    FormBODYContext *formBODY();

   
  };

  FormDECLContext* formDECL(WObject * wfContainer,WObject * wfObject);

  class  ANormalFormContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject = WObject::_NULL_;
    ANormalFormContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    ANormalFormContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    AFormContext *aForm();
    APrototypeContext *aPrototype();
    AWObjectContext *aWObject();

   
  };

  ANormalFormContext* aNormalForm(WObject * wfContainer);

  class  AWObjectContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    int bLine;
    int bOffset;
    SEWParser::QualifiedNameIDContext *qnid = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    SEWParser::AComponentContext *wComp = nullptr;
    AWObjectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AWObjectContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject, int bLine, int bOffset);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<QualifiedNameIDContext *> qualifiedNameID();
    QualifiedNameIDContext* qualifiedNameID(size_t i);
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();
    std::vector<AComponentContext *> aComponent();
    AComponentContext* aComponent(size_t i);

   
  };

  AWObjectContext* aWObject(WObject * wfContainer,WObject * wfObject,int bLine,int bOffset);

  class  AFormContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    int bLine;
    int bOffset;
    AFormContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AFormContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject, int bLine, int bOffset);
    virtual size_t getRuleIndex() const override;
    Kw_formContext *kw_form();
    FormDECLContext *formDECL();
    Kw_endformContext *kw_endform();

   
  };

  AFormContext* aForm(WObject * wfContainer,WObject * wfObject,int bLine,int bOffset);

  class  APrototypeContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject;
    int bLine;
    int bOffset;
    APrototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    APrototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, WObject * wfObject, int bLine, int bOffset);
    virtual size_t getRuleIndex() const override;
    Kw_prototypeContext *kw_prototype();
    FormDECLContext *formDECL();
    Kw_endprototypeContext *kw_endprototype();

   
  };

  APrototypeContext* aPrototype(WObject * wfContainer,WObject * wfObject,int bLine,int bOffset);

  class  AComponentContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject = WObject::_NULL_;
    SEWParser::AWPropertyContext *wp = nullptr;
    SEWParser::AWSequenceContext *ws = nullptr;
    SEWParser::ANormalFormContext *nf = nullptr;
    SEWParser::TagProgramContext *tp = nullptr;
    AComponentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AComponentContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    AWPropertyContext *aWProperty();
    AWSequenceContext *aWSequence();
    ANormalFormContext *aNormalForm();
    TagProgramContext *tagProgram();

   
  };

  AComponentContext* aComponent(WObject * wfContainer);

  class  ASequenceComponentContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject = WObject::_NULL_;
    SEWParser::AWPropertyContext *wp = nullptr;
    SEWParser::ANormalFormContext *nf = nullptr;
    SEWParser::TagProgramContext *tp = nullptr;
    ASequenceComponentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    ASequenceComponentContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    AWPropertyContext *aWProperty();
    ANormalFormContext *aNormalForm();
    TagProgramContext *tagProgram();

   
  };

  ASequenceComponentContext* aSequenceComponent(WObject * wfContainer);

  class  AWSequenceContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfSequence = WObject::_NULL_;
    antlr4::Token *identifierToken = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    SEWParser::ASequenceComponentContext *wSeq = nullptr;
    antlr4::Token *atleftvalueidentifierToken = nullptr;
    SEWParser::AComponentContext *wComp = nullptr;
    antlr4::Token *eId = nullptr;
    AWSequenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AWSequenceContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    antlr4::tree::TerminalNode *LBRACK();
    antlr4::tree::TerminalNode *RBRACK();
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();
    std::vector<ASequenceComponentContext *> aSequenceComponent();
    ASequenceComponentContext* aSequenceComponent(size_t i);
    antlr4::tree::TerminalNode *COLON();
    antlr4::tree::TerminalNode *AtLeftValueIdentifier();
    antlr4::tree::TerminalNode *Section();
    antlr4::tree::TerminalNode *Endsection();
    std::vector<AComponentContext *> aComponent();
    AComponentContext* aComponent(size_t i);

   
  };

  AWSequenceContext* aWSequence(WObject * wfContainer);

  class  AWPropertyContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfProperty = WObject::_NULL_;
    SEWParser::AWPropertyValueContext *wu = nullptr;
    SEWParser::AWPropertyValueContext *wn = nullptr;
    SEWParser::AWPropertyValueContext *wt = nullptr;
    SEWParser::AWPropertyValueContext *wd = nullptr;
    SEWParser::AWPropertyValueContext *wp = nullptr;
    SEWParser::AWPropertyValueContext *ws = nullptr;
    SEWParser::AWPropertyValueContext *wf = nullptr;
    SEWParser::AWPropertyValueContext *wv = nullptr;
    SEWParser::AWPropertyValueContext *wr = nullptr;
    SEWParser::AnAssignOpContext *ao = nullptr;
    SEWParser::AWPropertyValueContext *wform = nullptr;
    SEWParser::AWPropertyValueContext *wm = nullptr;
    antlr4::Token *at_lv = nullptr;
    SEWParser::AWPropertyValueContext *wlva = nullptr;
    antlr4::Token *lv = nullptr;
    SEWParser::AWPropertyValueContext *wida = nullptr;
    AWPropertyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AWPropertyContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Attr_UFI();
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *Attr_NAME();
    antlr4::tree::TerminalNode *Attr_TYPE();
    antlr4::tree::TerminalNode *Attr_DESIGN();
    antlr4::tree::TerminalNode *Attr_PUBLIC();
    antlr4::tree::TerminalNode *Attr_STATIC();
    antlr4::tree::TerminalNode *Attr_FINAL();
    antlr4::tree::TerminalNode *Attr_VOLATILE();
    antlr4::tree::TerminalNode *Attr_REFERENCE();
    antlr4::tree::TerminalNode *Form();
    antlr4::tree::TerminalNode *Meta();
    AWPropertyValueContext *aWPropertyValue();
    AnAssignOpContext *anAssignOp();
    antlr4::tree::TerminalNode *AtLeftValueIdentifier();
    antlr4::tree::TerminalNode *Identifier();
    antlr4::tree::TerminalNode *SEMI();

   
  };

  AWPropertyContext* aWProperty(WObject * wfContainer);

  class  AnAssignOpContext : public antlr4::ParserRuleContext {
  public:
    AVM_OPCODE operation;
    AnAssignOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *EQEQ();
    antlr4::tree::TerminalNode *NEQ();
    antlr4::tree::TerminalNode *SEQ();
    antlr4::tree::TerminalNode *NSEQ();
    antlr4::tree::TerminalNode *BANDEQ();
    antlr4::tree::TerminalNode *BOREQ();
    antlr4::tree::TerminalNode *BXOREQ();
    antlr4::tree::TerminalNode *BNOTEQ();
    antlr4::tree::TerminalNode *PLUSEQ();
    antlr4::tree::TerminalNode *MINUSEQ();
    antlr4::tree::TerminalNode *MULTEQ();
    antlr4::tree::TerminalNode *DIVEQ();
    antlr4::tree::TerminalNode *MODEQ();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *GTE();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *LTE();

   
  };

  AnAssignOpContext* anAssignOp();

  class  AWPropertyValueContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    std::string aNameID;
    WObject * wfProperty = WObject::_NULL_;
    SEWParser::AnOperatorContext *op = nullptr;
    SEWParser::AvmProgramContext *ap = nullptr;
    SEWParser::ExpressionContext *e = nullptr;
    SEWParser::Expression_invokeContext *ei = nullptr;
    antlr4::Token *integernumberToken = nullptr;
    antlr4::Token *floatingpointnumberToken = nullptr;
    antlr4::Token *cl = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    SEWParser::UfiStringContext *ufi = nullptr;
    SEWParser::UfiStringContext *bufi = nullptr;
    SEWParser::ASymbolOperatorContext *sop = nullptr;
    SEWParser::AnArrayContext *aa = nullptr;
    SEWParser::AListContext *al = nullptr;
    AWPropertyValueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AWPropertyValueContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer, std::string aNameID);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPROG();
    antlr4::tree::TerminalNode *RCURLY();
    AnOperatorContext *anOperator();
    std::vector<AvmProgramContext *> avmProgram();
    AvmProgramContext* avmProgram(size_t i);
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    ExpressionContext *expression();
    Expression_invokeContext *expression_invoke();
    antlr4::tree::TerminalNode *True();
    antlr4::tree::TerminalNode *False();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *IntegerNumber();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *FloatingPointNumber();
    antlr4::tree::TerminalNode *CharacterLiteral();
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();
    UfiStringContext *ufiString();
    antlr4::tree::TerminalNode *BAND();
    ASymbolOperatorContext *aSymbolOperator();
    AnArrayContext *anArray();
    AListContext *aList();

   
  };

  AWPropertyValueContext* aWPropertyValue(WObject * wfContainer,std::string aNameID);

  class  AReferenceContext : public antlr4::ParserRuleContext {
  public:
    BF form;
    SEWParser::UfiStringContext *ufi = nullptr;
    AReferenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BAND();
    UfiStringContext *ufiString();

   
  };

  AReferenceContext* aReference();

  class  TagProgramContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    WObject * wfObject = WObject::_NULL_;
    antlr4::Token *at_lv = nullptr;
    SEWParser::AvmProgramContext *ap = nullptr;
    TagProgramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    TagProgramContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    antlr4::tree::TerminalNode *AtLeftValueIdentifier();
    AvmProgramContext *avmProgram();

   
  };

  TagProgramContext* tagProgram(WObject * wfContainer);

  class  AvmProgramContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    BF code;
    SEWParser::AnOperatorContext *op = nullptr;
    SEWParser::AvmProgramContext *ap = nullptr;
    SEWParser::ExpressionContext *pe = nullptr;
    SEWParser::Expression_invokeContext *ie = nullptr;
    SEWParser::AnAtomContext *atom = nullptr;
    AvmProgramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AvmProgramContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPROG();
    antlr4::tree::TerminalNode *RCURLY();
    AnOperatorContext *anOperator();
    std::vector<AvmProgramContext *> avmProgram();
    AvmProgramContext* avmProgram(size_t i);
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    ExpressionContext *expression();
    Expression_invokeContext *expression_invoke();
    AnAtomContext *anAtom();

   
  };

  AvmProgramContext* avmProgram(WObject * wfContainer);

  class  AnOperatorContext : public antlr4::ParserRuleContext {
  public:
    Operator * operation;
    SEWParser::ASymbolOperatorContext *s = nullptr;
    antlr4::Token *identifierToken = nullptr;
    AnOperatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ASymbolOperatorContext *aSymbolOperator();
    antlr4::tree::TerminalNode *Identifier();

   
  };

  AnOperatorContext* anOperator();

  class  ASymbolOperatorContext : public antlr4::ParserRuleContext {
  public:
    Operator * operation;
    ASymbolOperatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *MULT();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *MOD();
    antlr4::tree::TerminalNode *POW();
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *EQEQ();
    antlr4::tree::TerminalNode *NEQ();
    antlr4::tree::TerminalNode *SEQ();
    antlr4::tree::TerminalNode *NSEQ();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *GTE();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *LTE();
    antlr4::tree::TerminalNode *BNOT();
    antlr4::tree::TerminalNode *BAND();
    antlr4::tree::TerminalNode *BOR();
    antlr4::tree::TerminalNode *BXOR();
    antlr4::tree::TerminalNode *LSHIFT();
    antlr4::tree::TerminalNode *RSHIFT();
    antlr4::tree::TerminalNode *LNOT();
    antlr4::tree::TerminalNode *LAND();
    antlr4::tree::TerminalNode *LOR();
    antlr4::tree::TerminalNode *ASSIGN();
    antlr4::tree::TerminalNode *PUSH();
    antlr4::tree::TerminalNode *POP();
    antlr4::tree::TerminalNode *TOP();
    antlr4::tree::TerminalNode *ASSIGN_TOP();
    antlr4::tree::TerminalNode *SEQUENCE();
    antlr4::tree::TerminalNode *SEQUENCE_SIDE();
    antlr4::tree::TerminalNode *SEQUENCE_WEAK();
    antlr4::tree::TerminalNode *INTERLEAVING();
    antlr4::tree::TerminalNode *PARTIAL_ORDER();
    antlr4::tree::TerminalNode *EXCLUSIVE();
    antlr4::tree::TerminalNode *NONDETERMINISM();
    antlr4::tree::TerminalNode *PRIOR_GT();
    antlr4::tree::TerminalNode *PRIOR_LT();
    antlr4::tree::TerminalNode *PARALLEL();
    antlr4::tree::TerminalNode *PRODUCT();
    antlr4::tree::TerminalNode *ASYNC();
    antlr4::tree::TerminalNode *STRONG_SYNC();
    antlr4::tree::TerminalNode *WEAK_SYNC();

   
  };

  ASymbolOperatorContext* aSymbolOperator();

  class  AnAtomContext : public antlr4::ParserRuleContext {
  public:
    BF form;
    antlr4::Token *mn = nullptr;
    antlr4::Token *pn = nullptr;
    antlr4::Token *n = nullptr;
    antlr4::Token *mf = nullptr;
    antlr4::Token *pf = nullptr;
    antlr4::Token *f = nullptr;
    antlr4::Token *cl = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    SEWParser::UfiStringContext *us = nullptr;
    SEWParser::AReferenceContext *ref = nullptr;
    SEWParser::ASymbolOperatorContext *so = nullptr;
    SEWParser::AnArrayContext *aa = nullptr;
    SEWParser::AListContext *al = nullptr;
    AnAtomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *True();
    antlr4::tree::TerminalNode *False();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *IntegerNumber();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *FloatingPointNumber();
    antlr4::tree::TerminalNode *CharacterLiteral();
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();
    UfiStringContext *ufiString();
    AReferenceContext *aReference();
    ASymbolOperatorContext *aSymbolOperator();
    AnArrayContext *anArray();
    AListContext *aList();

   
  };

  AnAtomContext* anAtom();

  class  AnArrayContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    BF array;
    SEWParser::AvmProgramContext *ap = nullptr;
    AnArrayContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AnArrayContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LBRACK();
    antlr4::tree::TerminalNode *RBRACK();
    std::vector<AvmProgramContext *> avmProgram();
    AvmProgramContext* avmProgram(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  AnArrayContext* anArray(WObject * wfContainer);

  class  AListContext : public antlr4::ParserRuleContext {
  public:
    WObject * wfContainer;
    BF plist;
    SEWParser::AvmProgramContext *ap = nullptr;
    AListContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    AListContext(antlr4::ParserRuleContext *parent, size_t invokingState, WObject * wfContainer);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LCURLY();
    antlr4::tree::TerminalNode *RCURLY();
    std::vector<AvmProgramContext *> avmProgram();
    AvmProgramContext* avmProgram(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

   
  };

  AListContext* aList(WObject * wfContainer);

  class  Expression_invokeContext : public antlr4::ParserRuleContext {
  public:
    BFCode expr;
    SEWParser::UnaryExpressionContext *ue = nullptr;
    antlr4::Token *id = nullptr;
    SEWParser::ASymbolOperatorContext *sop = nullptr;
    SEWParser::ExpressionContext *arg = nullptr;
    SEWParser::ExpressionContext *prov = nullptr;
    SEWParser::UnaryExpressionContext *from = nullptr;
    SEWParser::UnaryExpressionContext *to = nullptr;
    SEWParser::AnOperatorContext *op = nullptr;
    Expression_invokeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LPAREN_INVOKE();
    antlr4::tree::TerminalNode *RPAREN();
    std::vector<UnaryExpressionContext *> unaryExpression();
    UnaryExpressionContext* unaryExpression(size_t i);
    antlr4::tree::TerminalNode *Identifier();
    ASymbolOperatorContext *aSymbolOperator();
    antlr4::tree::TerminalNode *Provided();
    antlr4::tree::TerminalNode *From();
    antlr4::tree::TerminalNode *To();
    antlr4::tree::TerminalNode *Activity();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    AnOperatorContext *anOperator();

   
  };

  Expression_invokeContext* expression_invoke();

  class  ExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::ConditionalExpressionContext *cond = nullptr;
    ExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ConditionalExpressionContext *conditionalExpression();

   
  };

  ExpressionContext* expression();

  class  ConditionalExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::ConditionalOrExpressionContext *cond = nullptr;
    SEWParser::ExpressionContext *arg1 = nullptr;
    SEWParser::ExpressionContext *arg2 = nullptr;
    ConditionalExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ConditionalOrExpressionContext *conditionalOrExpression();
    antlr4::tree::TerminalNode *QUESTION();
    antlr4::tree::TerminalNode *COLON();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

   
  };

  ConditionalExpressionContext* conditionalExpression();

  class  ConditionalOrExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::ConditionalAndExpressionContext *cond = nullptr;
    SEWParser::ConditionalAndExpressionContext *arg = nullptr;
    ConditionalOrExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ConditionalAndExpressionContext *> conditionalAndExpression();
    ConditionalAndExpressionContext* conditionalAndExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LOR();
    antlr4::tree::TerminalNode* LOR(size_t i);

   
  };

  ConditionalOrExpressionContext* conditionalOrExpression();

  class  ConditionalAndExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::BitwiseOrExpressionContext *bwor = nullptr;
    SEWParser::BitwiseOrExpressionContext *arg = nullptr;
    ConditionalAndExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<BitwiseOrExpressionContext *> bitwiseOrExpression();
    BitwiseOrExpressionContext* bitwiseOrExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> LAND();
    antlr4::tree::TerminalNode* LAND(size_t i);

   
  };

  ConditionalAndExpressionContext* conditionalAndExpression();

  class  BitwiseOrExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::BitwiseXorExpressionContext *bwxor = nullptr;
    SEWParser::BitwiseXorExpressionContext *arg = nullptr;
    BitwiseOrExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<BitwiseXorExpressionContext *> bitwiseXorExpression();
    BitwiseXorExpressionContext* bitwiseXorExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BOR();
    antlr4::tree::TerminalNode* BOR(size_t i);

   
  };

  BitwiseOrExpressionContext* bitwiseOrExpression();

  class  BitwiseXorExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::BitwiseAndExpressionContext *bwand = nullptr;
    SEWParser::BitwiseAndExpressionContext *arg = nullptr;
    BitwiseXorExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<BitwiseAndExpressionContext *> bitwiseAndExpression();
    BitwiseAndExpressionContext* bitwiseAndExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BXOR();
    antlr4::tree::TerminalNode* BXOR(size_t i);

   
  };

  BitwiseXorExpressionContext* bitwiseXorExpression();

  class  BitwiseAndExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::EqualityExpressionContext *eq = nullptr;
    SEWParser::EqualityExpressionContext *arg = nullptr;
    BitwiseAndExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<EqualityExpressionContext *> equalityExpression();
    EqualityExpressionContext* equalityExpression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> BAND();
    antlr4::tree::TerminalNode* BAND(size_t i);

   
  };

  BitwiseAndExpressionContext* bitwiseAndExpression();

  class  EqualityExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::RelationalExpressionContext *rel = nullptr;
    SEWParser::EqualOpContext *eo = nullptr;
    SEWParser::RelationalExpressionContext *arg = nullptr;
    EqualityExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<RelationalExpressionContext *> relationalExpression();
    RelationalExpressionContext* relationalExpression(size_t i);
    EqualOpContext *equalOp();

   
  };

  EqualityExpressionContext* equalityExpression();

  class  EqualOpContext : public antlr4::ParserRuleContext {
  public:
    const Operator * operation;
    EqualOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *EQEQ();
    antlr4::tree::TerminalNode *NEQ();
    antlr4::tree::TerminalNode *SEQ();
    antlr4::tree::TerminalNode *NSEQ();

   
  };

  EqualOpContext* equalOp();

  class  RelationalExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::ShiftExpressionContext *se = nullptr;
    SEWParser::RelationalOpContext *ro = nullptr;
    SEWParser::ShiftExpressionContext *arg = nullptr;
    RelationalExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ShiftExpressionContext *> shiftExpression();
    ShiftExpressionContext* shiftExpression(size_t i);
    RelationalOpContext *relationalOp();

   
  };

  RelationalExpressionContext* relationalExpression();

  class  RelationalOpContext : public antlr4::ParserRuleContext {
  public:
    const Operator * operation;
    RelationalOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LTE();
    antlr4::tree::TerminalNode *GTE();
    antlr4::tree::TerminalNode *LT_();
    antlr4::tree::TerminalNode *GT();

   
  };

  RelationalOpContext* relationalOp();

  class  ShiftExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::AdditiveExpressionContext *ae = nullptr;
    SEWParser::ShiftOpContext *so = nullptr;
    SEWParser::AdditiveExpressionContext *arg = nullptr;
    ShiftExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<AdditiveExpressionContext *> additiveExpression();
    AdditiveExpressionContext* additiveExpression(size_t i);
    std::vector<ShiftOpContext *> shiftOp();
    ShiftOpContext* shiftOp(size_t i);

   
  };

  ShiftExpressionContext* shiftExpression();

  class  ShiftOpContext : public antlr4::ParserRuleContext {
  public:
    const Operator * operation;
    ShiftOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LSHIFT();
    antlr4::tree::TerminalNode *RSHIFT();

   
  };

  ShiftOpContext* shiftOp();

  class  AdditiveExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::MultiplicativeExpressionContext *me = nullptr;
    SEWParser::AdditiveOpContext *ao = nullptr;
    SEWParser::MultiplicativeExpressionContext *arg = nullptr;
    AdditiveExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<MultiplicativeExpressionContext *> multiplicativeExpression();
    MultiplicativeExpressionContext* multiplicativeExpression(size_t i);
    std::vector<AdditiveOpContext *> additiveOp();
    AdditiveOpContext* additiveOp(size_t i);

   
  };

  AdditiveExpressionContext* additiveExpression();

  class  AdditiveOpContext : public antlr4::ParserRuleContext {
  public:
    const Operator * operation;
    AdditiveOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();

   
  };

  AdditiveOpContext* additiveOp();

  class  MultiplicativeExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::UnaryExpressionContext *ue = nullptr;
    SEWParser::MultiplicativeOpContext *mo = nullptr;
    SEWParser::UnaryExpressionContext *arg = nullptr;
    MultiplicativeExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<UnaryExpressionContext *> unaryExpression();
    UnaryExpressionContext* unaryExpression(size_t i);
    std::vector<MultiplicativeOpContext *> multiplicativeOp();
    MultiplicativeOpContext* multiplicativeOp(size_t i);

   
  };

  MultiplicativeExpressionContext* multiplicativeExpression();

  class  MultiplicativeOpContext : public antlr4::ParserRuleContext {
  public:
    const Operator * operation;
    MultiplicativeOpContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *MULT();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *MOD();

   
  };

  MultiplicativeOpContext* multiplicativeOp();

  class  UnaryExpressionContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    SEWParser::LiteralContext *lit = nullptr;
    SEWParser::UnaryExpressionContext *le = nullptr;
    SEWParser::UnaryExpressionContext *be = nullptr;
    SEWParser::Expression_invokeContext *i = nullptr;
    SEWParser::ExpressionContext *p = nullptr;
    UnaryExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    LiteralContext *literal();
    antlr4::tree::TerminalNode *LNOT();
    UnaryExpressionContext *unaryExpression();
    antlr4::tree::TerminalNode *BNOT();
    Expression_invokeContext *expression_invoke();
    antlr4::tree::TerminalNode *LPAREN();
    antlr4::tree::TerminalNode *RPAREN();
    ExpressionContext *expression();

   
  };

  UnaryExpressionContext* unaryExpression();

  class  LiteralContext : public antlr4::ParserRuleContext {
  public:
    BF expr;
    antlr4::Token *mn = nullptr;
    antlr4::Token *pn = nullptr;
    antlr4::Token *n = nullptr;
    antlr4::Token *mf = nullptr;
    antlr4::Token *pf = nullptr;
    antlr4::Token *f = nullptr;
    antlr4::Token *cl = nullptr;
    antlr4::Token *dqs = nullptr;
    antlr4::Token *sqs = nullptr;
    SEWParser::UfiStringContext *u = nullptr;
    SEWParser::AReferenceContext *r = nullptr;
    SEWParser::AnArrayContext *aa = nullptr;
    SEWParser::AListContext *al = nullptr;
    LiteralContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *True();
    antlr4::tree::TerminalNode *False();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *IntegerNumber();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *FloatingPointNumber();
    antlr4::tree::TerminalNode *CharacterLiteral();
    antlr4::tree::TerminalNode *DoubleQuotedString();
    antlr4::tree::TerminalNode *SingleQuotedString();
    UfiStringContext *ufiString();
    AReferenceContext *aReference();
    AnArrayContext *anArray();
    AListContext *aList();

   
  };

  LiteralContext* literal();


  bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;

  bool aWSequenceSempred(AWSequenceContext *_localctx, size_t predicateIndex);
  bool anOperatorSempred(AnOperatorContext *_localctx, size_t predicateIndex);

  // By default the static state used to implement the parser is lazily initialized during the first
  // call to the constructor. You can call this function if you wish to initialize the static state
  // ahead of time.
  static void initialize();

private:
  /* private parser declarations section */
  	
  	std::string mFilename;
  	
  	std::size_t   noOfErrors;

  	WObjectManager * mWObjectManager;


};

}  // namespace sep
