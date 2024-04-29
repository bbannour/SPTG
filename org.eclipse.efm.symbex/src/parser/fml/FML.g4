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

grammar FML;

options {
//	language   = Cpp
//	tokenVocab = FMLLexer;
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
 * Copyright (c) 2021 CEA LIST.
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
	
	#include <common/BF.h>
	
	#include <collection/BFContainer.h>
	
	#include <fml/common/BehavioralElement.h>
	#include <fml/common/ModifierElement.h>
	#include <fml/common/SpecifierElement.h>
	
	#include <fml/executable/ExecutableLib.h>
	
	#include <fml/expression/AvmCode.h>
	#include <fml/expression/BuiltinArray.h>
	#include <fml/expression/ExpressionConstant.h>
	#include <fml/expression/ExpressionConstructor.h>
	#include <fml/expression/StatementConstructor.h>
	
	#include <fml/lib/IComPoint.h>
	
	#include <fml/operator/Operator.h>
	#include <fml/operator/OperatorManager.h>
	
	#include <fml/template/TemplateFactory.h>
	
	#include <fml/type/TypeSpecifier.h>
	
	#include <fml/type/TypeManager.h>
	
	#include <fml/infrastructure/Buffer.h>
	#include <fml/infrastructure/Channel.h>
	#include <fml/infrastructure/ComPoint.h>
	#include <fml/infrastructure/ComProtocol.h>
	#include <fml/infrastructure/ComRoute.h>
	#include <fml/infrastructure/Connector.h>
	#include <fml/infrastructure/DataType.h>
	#include <fml/infrastructure/Machine.h>
	#include <fml/infrastructure/Package.h>
	#include <fml/infrastructure/Port.h>
	#include <fml/infrastructure/Routine.h>
	#include <fml/infrastructure/System.h>
	#include <fml/infrastructure/Transition.h>
	#include <fml/infrastructure/Variable.h>
	
	#include <fml/infrastructure/BehavioralPart.h>
	#include <fml/infrastructure/CompositePart.h>
	#include <fml/infrastructure/InstanceSpecifierPart.h>
	#include <fml/infrastructure/InteractionPart.h>
	#include <fml/infrastructure/ModelOfComputationPart.h>
	//#include <fml/infrastructure/PropertyPart.h>
	
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
@parser::context { /* parser context section */ }

// Appears in the private part of the parser in the h file.
// The function bodies could also appear in the definitions section, but I want to maximize
// Java compatibility, so we can also create a Java parser from this grammar.
// Still, some tweaking is necessary after the Java file generation (e.g. bool -> boolean).
@parser::members {
/* public parser declarations/members section */

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
//		static std::string   info = "$ Id: FML.g, v 1.0 2021/10/29 Lapitre $";
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
		return 1;//( getCurrentToken(1).getLine() );
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


	////////////////////////////////////////////////////////////////////////////
	// PARSER GLOBAL VARIABLE
	////////////////////////////////////////////////////////////////////////////
	
	// WObject Manager
	sep::WObjectManager * mWObjectManager = nullptr;
	
	// Current Parse System
	sep::System * _SYSTEM_ = nullptr;
	
	// Current Parse Machine
	sep::Machine * _CPM_ = nullptr;
	
	#define PUSH_CTX_CPM( cpm )   sep::ParserUtil::pushCTX( _CPM_ = cpm )
	
	#define PUSH_CTX_NEW( cpm )   sep::ParserUtil::pushDynamicCTX( _CPM_ = cpm )
	
	
	// Current Parse Routine
	sep::Routine * _CPR_ = nullptr;
	
	#define PUSH_CTX_CPR( cpr )   sep::ParserUtil::pushCTX( _CPR_ = cpr )
	
	// Current Parse Local PropertyPart
	#define PUSH_CTX_LOCAL( cpl )   sep::ParserUtil::pushCTX( cpl )
	
	
	// Pop old local parse context & update current machine & routine
	#define POP_CTX               sep::ParserUtil::popCTX( _CPM_ , _CPR_ )
	
	#define POP_CTX_IF( cpm )   \
			if( _CPM_ == cpm ) { sep::ParserUtil::popCTX( _CPM_ , _CPR_ ); }
	
	// Current Parse Routine | Machine | System
	#define _CPRMS_  ( ( _CPR_ != nullptr )  \
			? static_cast< sep::BehavioralElement * >(_CPR_)  \
			: ( ( _CPM_ != nullptr )  \
					? static_cast< sep::BehavioralElement * >(_CPM_)  \
					: static_cast< sep::BehavioralElement * >(_SYSTEM_) ) )
	
	
	// Current Parse [ [ Fully ] Qualified ] Name ID
	std::string cpLOCATOR;
	std::vector< std::string > cpQNID;
	
	
	////////////////////////////////////////////////////////////////////////////
	// DEFAULT STATE  #final, #terminal, #return
	////////////////////////////////////////////////////////////////////////////
	
	sep::ListOfMachine needDefaultStateFinal;
	
	sep::ListOfMachine needDefaultStateTerminal;
	
	sep::ListOfMachine needDefaultStateReturn;
	
	
	////////////////////////////////////////////////////////////////////////////
	// TRANSITION ID
	////////////////////////////////////////////////////////////////////////////
	
	std::size_t transition_id = 0;
	
	void resetTransitionID()
	{
		transition_id = 0;
	}
	
	std::string newTransitionID(
			const std::string & id, const std::string & prefix = "t")
	{
		return( id.empty() ?
				(sep::OSS() << prefix << sep::NamedElement::NAME_ID_SEPARATOR
							<< transition_id++).str() : id );
	}
	
	
	int mInvokeNewInstanceCount = 0;
	
	std::string newInvokeNewInstanceNameID(
			sep::Machine * container, const std::string modelNameID)
	{
		return( sep::OSS() << modelNameID << sep::NamedElement::NAME_ID_SEPARATOR
							<< mInvokeNewInstanceCount++ );
	}
	
	
	
	int mProcedureCallCount = 0;
	
	
	
	////////////////////////////////////////////////////////////////////////////
	// BUFFER ID
	////////////////////////////////////////////////////////////////////////////
	
	std::size_t buffer_id = 0;
	
	void resetBufferID()
	{
		buffer_id = 0;
	}
	
	std::string newBufferID(const std::string & prefix = sep::Buffer::ANONYM_ID)
	{
		return( sep::OSS() << prefix << sep::NamedElement::NAME_ID_SEPARATOR
						<< buffer_id++ );
	}
	
	
	////////////////////////////////////////////////////////////////////////////
	// CONNECTOR ID
	////////////////////////////////////////////////////////////////////////////
	
	std::size_t connector_id = 0;
	
	void resetConnectorID()
	{
		connector_id = 0;
	}
	
	std::string newConnectorID(const std::string & id,
			const std::string & prefix = sep::Connector::ANONYM_ID)
	{
		return( id.empty() ?
				(sep::OSS() << prefix << sep::NamedElement::NAME_ID_SEPARATOR
							<< connector_id++).str() : id );
	}
	
	////////////////////////////////////////////////////////////////////////////
	// EXPRESSION UTILS
	////////////////////////////////////////////////////////////////////////////

	sep::BF new_uminus_expr(sep::BF & arg)
	{
		if( arg.isNumeric() )
		{
			return( sep::ExpressionConstructor::uminusExpr(arg) );
		}
		return( sep::ExpressionConstructor::newCode(
				sep::OperatorManager::OPERATOR_UMINUS, arg) );
	}
	
	sep::BF new_not_expr(sep::BF & arg)
	{
		if( arg.isBoolean() )
		{
			return( sep::ExpressionConstructor::notExpr(arg) );
		}
		return( sep::ExpressionConstructor::newCode(
				sep::OperatorManager::OPERATOR_NOT, arg) );
	}	
		
} // end of @parser::members


// Appears in the public part of the parser in the h file.
@parser::declarations {/* private parser declarations section */
	
	std::string mFilename;
	
	std::size_t   noOfErrors;

}

// Appears in line with the other class member definitions in the cpp file.
@parser::definitions {
	/* BEGIN parser definitions section */
	
	////////////////////////////////////////////////////////////////////////////
	// SET LOCATION IN TRACEABLE FORM
	////////////////////////////////////////////////////////////////////////////
	
	#define SAVE_RULE_BEGIN_LOCATION  std::size_t bLine = getCurrentToken()->getLine()
	
	#define SET_RULE_LOCATION(form)   \
			sep::ParserUtil::setLocation(form, bLine, _input->LT(-1)->getLine())
	
	
	
	////////////////////////////////////////////////////////////////////////////
	// XLIA or XFSP MACRO
	////////////////////////////////////////////////////////////////////////////
	
	#define OP(op)            sep::OperatorManager::OPERATOR_##op
	
	#define NEW_EXPR(e)       sep::ExpressionConstructor::newExpr(e)
	
	#define NEW_BOOLEAN(b)    sep::ExpressionConstructor::newBoolean(b)
	#define NEW_INTEGER(i)    sep::ExpressionConstructor::newInteger(i)
	#define NEW_RATIONAL(q)   sep::ExpressionConstructor::newRational(q)
	#define NEW_FLOAT(f)      sep::ExpressionConstructor::newFloat(f)
	#define NEW_CHAR(c)       sep::ExpressionConstructor::newChar(c)
	#define NEW_STRING(s)     sep::ExpressionConstructor::newString(s)
	
	#define NEW_ID(id)        sep::ExpressionConstructor::newIdentifier(id)
	#define NEW_QID(id)       sep::ExpressionConstructor::newQualifiedIdentifier(id)
	#define NEW_QNID(id, nb)  ( (nb > 1)? NEW_QID(id) : NEW_ID(id) )
	
	
	#define NEW_INSTANCE_UFID(machine, var)  \
			sep::ExpressionConstructor::newQualifiedIdentifier(  \
				sep::OSS() << machine->getNameID() << '.' << var->getNameID() )
	
	
	#define NEW_CODE(op)               sep::ExpressionConstructor::newCode(op)
	#define NEW_CODE1(op, e)           sep::ExpressionConstructor::newCode(op, e)
	#define NEW_CODE2(op, e1, e2)      sep::ExpressionConstructor::newCode(op, e1, e2)
	#define NEW_CODE3(op, e1, e2, e3)  sep::ExpressionConstructor::newCode(op, e1, e2, e3)
	
	#define NEW_CODE_FLAT(op, e1, e2)  sep::ExpressionConstructor::newCodeFlat(op, e1, e2)
	
	#define NEW_STMT(op)               sep::StatementConstructor::newCode(op)
	#define NEW_STMT1(op, s)           sep::StatementConstructor::newCode(op, s)
	#define NEW_STMT2(op, s1, s2)      sep::StatementConstructor::newCode(op, s1, s2)
	#define NEW_STMT3(op, s1, s2, s3)  sep::StatementConstructor::newCode(op, s1, s2, s3)
	
	
	#define NEW_STMT_ASSIGN_OP(op, lv, e)  \
						NEW_STMT2(OP(ASSIGN_OP), lv, NEW_CODE1(op, e))
	
	#define NEW_STMT_ASSIGN_OP_AFTER(op, lv, e)  \
						NEW_STMT2(OP(ASSIGN_OP_AFTER), lv, NEW_CODE1(op, e))
	
	
	#define  NUM_INT(s)    std::atoi( s.c_str() )
	#define  NUM_FLOAT(s)  std::atof( s.c_str() )
		
	////////////////////////////////////////////////////////////////////////////
	// PARSER MACRO FOR SEMANTIC PREDICATE FOR KEYWORD DETECTION
	////////////////////////////////////////////////////////////////////////////
	
	#define IS_KEYWORD(kw)     ( getCurrentToken()->getText() == kw )

	
} // end of @parser::definitions


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


// MAIN RULE
formalML[ sep::WObjectManager * aWObjectManager ]
returns [ sep::System * spec = nullptr]
@init{
	mWObjectManager = aWObjectManager;
}
	: pfml=prologue_fml
	  ( s=def_system   { $spec = $s.sys;  $spec->setWObject($pfml.fmlProlog); }
	  
//	  | p=def_package  { $pack = $p.pack; $pack->setWObject($pfml.fmlProlog); }
	  )
	;


////////////////////////////////////////////////////////////////////////////////
// section PROLOGUE
////////////////////////////////////////////////////////////////////////////////

prologue_fml
returns [ sep::WObject * fmlProlog = sep::WObject::_NULL_]
@init{
	std::string attrID;
}
	: ( '@FormalML'  { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "formalml" ); }
	  | '@formalml'  { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "formalml" ); }
	  | '@xfml'      { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "xfml"     ); }
	  | '@fml'       { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "fml"      ); }
	  | '@diversity' { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "diversity"); }
	  | '@xlia'      { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "xlia"     ); }
	  | '@xfsp'      { $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "xfsp"     ); }
	  ) ?
	  {
		if( $fmlProlog == sep::WObject::_NULL_ )
		{ $fmlProlog = mWObjectManager->newWSequence(sep::WObject::_NULL_, "symbex"); }
	  }
	  LT_
	    ( 'system'   { attrID = "system";  }
	    | 'package'  { attrID = "package"; }
	    | id=ID      { attrID = $id->getText(); }
	    )
	    ( ASSIGN id=ID
		{
			$fmlProlog->append( 
					mWObjectManager->newWPropertyIdentifier(
							$fmlProlog, attrID, $id->getText() ) );
		}
	    )?
	  ( COMMA ( 'version:' )? ( FloatLiteral | ID | StringLiteral ) )*
	  GT
	  COLON
	  ( prologue_attribute[ $fmlProlog ] )?
	  ( prologue_options )?
	;


prologue_attribute
/* in */[ sep::WObject * fmlProlog ]
	: '@package'  ASSIGN  id=ID  SEMI
	{
		fmlProlog->append( mWObjectManager->newWPropertyIdentifier(
				fmlProlog, "package", $id->getText() ) );
	}

	| '@system'  ASSIGN  id=ID  SEMI
	{
		fmlProlog->append( mWObjectManager->newWPropertyIdentifier(
				fmlProlog, "system", $id->getText() ) );
	}
	;


prologue_options
	: '@options'  LCURLY
		  ( id=ID ASSIGN e=expression SEMI
		  { sep::ParserUtil::setPrologueOption($id->getText(), $e.bf); }
		  )*
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// form MODIFIER
////////////////////////////////////////////////////////////////////////////////

//modifier_property_specifier
modifier_declaration
returns [ sep::Modifier mdfr ]
	: ( 'final'         { $mdfr.setFeatureFinal();        }
//	  | 'const'         { $mdfr.setFeatureConst();        }

	  | 'static'        { $mdfr.setFeatureStatic();       }

	  | 'volatile'      { $mdfr.setFeatureVolatile();     }
	  | 'transient'     { $mdfr.setFeatureTransient();    }

	  | 'unsafe'        { $mdfr.setFeatureUnsafe();       }

	  | 'optional'      { $mdfr.setFeatureOptional();     }

	  | 'ref'           { $mdfr.setNatureReference();     }
//	  | 'macro'         { $mdfr.setNatureMacro();         }

	  | 'bind'          { $mdfr.setNatureBind();          }

	  | 'public'        { $mdfr.setVisibilityPublic();    }
//	  | 'protected'     { $mdfr.setVisibilityProtected(); }
	  | 'private'       { $mdfr.setVisibilityPrivate();   }

	  | modifier_set_direction_strict_text[ &( $mdfr ) ]
	  )+
	;


//modifier_parameter_specifier
modifier_direction
returns [ sep::Modifier mdfr ]
	: ( '->'  | 'in'  | 'input'  )  { $mdfr.setDirectionInput();  }
	| ( '<-'  | 'out' | 'output' )  { $mdfr.setDirectionOutput(); }
	| ( '<->' | 'inout'  )          { $mdfr.setDirectionInout();  }
	| ( '<='  | 'return' )          { $mdfr.setDirectionReturn(); }
	;

modifier_direction_text
returns [ sep::Modifier mdfr ]
	: ( 'in'  | 'input'  )  { $mdfr.setDirectionInput();  }
	| ( 'out' | 'output' )  { $mdfr.setDirectionOutput(); }
	| ( 'inout'  )          { $mdfr.setDirectionInout();  }
	| ( 'return' )          { $mdfr.setDirectionReturn(); }
	;

modifier_set_direction_strict_text
/*inout*/[ sep::Modifier * mdfr ]
	: 'input'    { $mdfr->setDirectionInput();  }
	| 'output'   { $mdfr->setDirectionOutput(); }
	| 'inout'    { $mdfr->setDirectionInout();  }
	| 'return'   { $mdfr->setDirectionReturn(); }
	;

modifier_direction_symbol
returns [ sep::Modifier mdfr ]
	: '->'    { $mdfr.setDirectionInput();  }
	| '<-'    { $mdfr.setDirectionOutput(); }
	| '<->'   { $mdfr.setDirectionInout();  }
	| '<='    { $mdfr.setDirectionReturn(); }
	;


//modifier_parameter_specifier
modifier_param
returns [ sep::Modifier mdfr ]
	: m=modifier_direction  { $mdfr = $m.mdfr; }

	| 'final'           { $mdfr.setFeatureFinal();    }
	| 'const'           { $mdfr.setFeatureConst();    }

	| ( '&' | 'ref' )   { $mdfr.setNatureReference(); }
	| 'macro'           { $mdfr.setNatureMacro();     }

	| 'bind'            { $mdfr.setNatureBind();      }
	;


//modifier_procedure_specifier
procedure_modifier_specifier
returns [ sep::Modifier mdfr , sep::Specifier spcfr ]
//	: ( 'final'          { $mdfr.setFeatureFinal();           }

//	  | 'volatile'       { $mdfr.setFeatureVolatile();        }
//	  | 'transient'      { $mdfr.setFeatureTransient();       }

//	  | 'model'          { $mdfr.setDesignModel();            }
//	  | 'prototype'      { $mdfr.setDesignPrototypeStatic();  }
//	  | 'instance'       { $mdfr.setDesignInstanceStatic();   }
//	  | 'dynamic'        { $mdfr.setDesignInstanceDynamic();  }

//	  | 'macro'          { $mdfr.setNatureMacro(); }

//	  | 'public'         { $mdfr.setVisibilityPublic();       }
//	  | 'protected'      { $mdfr.setVisibilityProtected();    }
//	  | 'private'        { $mdfr.setVisibilityPrivate();      }


	: ( 'timed'          { $spcfr.setFeatureTimed();          }
	  | 'timed#dense'    { $spcfr.setFeatureDenseTimed();     }
	  | 'timed#discrete' { $spcfr.setFeatureDiscreteTimed();  }

	  | 'input_enabled'  { $spcfr.setFeatureInputEnabled();   }
//	  | 'lifeline'       { $spcfr.setFeatureLifeline();       }
	  | 'unsafe'         { $mdfr.setFeatureUnsafe();          }
	  )+
	;


executable_modifier_specifier
returns [ sep::Modifier mdfr , sep::Specifier spcfr ]
//	: ( 'final'          { $mdfr.setFeatureFinal();           }

//	  | 'volatile'       { $mdfr.setFeatureVolatile();        }
//	  | 'transient'      { $mdfr.setFeatureTransient();       }

	: ( 'model'          { $spcfr.setDesignModel();           }
	  | 'prototype'      { $spcfr.setDesignPrototypeStatic(); }
//	  | 'instance'       { $spcfr.setDesignInstanceStatic();  }
	  | 'dynamic'        { $spcfr.setDesignInstanceDynamic(); }

//	  | 'macro'          { $mdfr.setNatureMacro();            }
//	  | 'bind'           { $mdfr.setNatureBind();             }

//	  | 'public'         { $mdfr.setVisibilityPublic();       }
//	  | 'protected'      { $mdfr.setVisibilityProtected();    }
//	  | 'private'        { $mdfr.setVisibilityPrivate();      }

	  | 'unsafe'         { $mdfr.setFeatureUnsafe();          }

	  | 'timed'          { $spcfr.setFeatureTimed();          }
	  | 'timed#dense'    { $spcfr.setFeatureDenseTimed();     }
	  | 'timed#discrete' { $spcfr.setFeatureDiscreteTimed();  }

	  | 'input_enabled'  { $spcfr.setFeatureInputEnabled();   }
	  | 'lifeline'       { $spcfr.setFeatureLifeline();       }
	  )+
	;

instance_modifier_specifier
returns [ sep::Modifier mdfr , sep::Specifier spcfr ]
	: ( 'final'          { $mdfr.setFeatureFinal();           }

//	  | 'volatile'       { $mdfr.setFeatureVolatile();        }
//	  | 'transient'      { $mdfr.setFeatureTransient();       }

//	  | 'model'          { $spcfr.setDesignModel();           }
//	  | 'prototype'      { $spcfr.setDesignPrototypeStatic(); }
//	  | 'instance'       { $spcfr.setDesignInstanceStatic();  }
	  | 'dynamic'        { $spcfr.setDesignInstanceDynamic(); }

//	  | 'macro'          { $mdfr.setNatureMacro();            }
//	  | 'bind'           { $mdfr.setNatureBind();             }

	  | 'public'         { $mdfr.setVisibilityPublic();       }
	  | 'protected'      { $mdfr.setVisibilityProtected();    }
	  | 'private'        { $mdfr.setVisibilityPrivate();      }

	  | 'unsafe'         { $mdfr.setFeatureUnsafe();          }

	  | 'timed'          { $spcfr.setFeatureTimed();          }
	  | 'timed#dense'    { $spcfr.setFeatureDenseTimed();     }
	  | 'timed#discrete' { $spcfr.setFeatureDiscreteTimed();  }

	  | 'input_enabled'  { $spcfr.setFeatureInputEnabled();   }
	  | 'lifeline'       { $spcfr.setFeatureLifeline();       }
	  )+
	;


//modifier_transition_specifier
modifier_transition
returns [ sep::Modifier mdfr , sep::Specifier spcfr ]
//	: ( 'final'          { $mdfr.setFeatureFinal();          }

//	  | 'volatile'       { $mdfr.setFeatureVolatile();       }
	: ( 'transient'      { $mdfr.setFeatureTransient();      }

//	  | 'unsafe'         { $mdfr.setFeatureUnsafe();         }

	  | 'timed'          { $spcfr.setFeatureTimed();         }
	  | 'timed#dense'    { $spcfr.setFeatureDenseTimed();    }
	  | 'timed#discrete' { $spcfr.setFeatureDiscreteTimed(); }
	  | 'input_enabled'  { $spcfr.setFeatureInputEnabled();  }
	  )+
	;


////////////////////////////////////////////////////////////////////////////////
// section PACKAGE
////////////////////////////////////////////////////////////////////////////////

def_package
returns [ sep::Package * pack ]
@after{
	POP_CTX;

	sep::ParserUtil::declareDefaultEndingStateIfNeed(needDefaultStateFinal,
			needDefaultStateTerminal, needDefaultStateReturn);
}
	: 'package' id=ID
		{ PUSH_CTX_CPM( $pack = new sep::Package($id->getText()) ); }

	    ( StringLiteral
		{ $pack->setUnrestrictedName($StringLiteral->getText());    }
	    )?

	  LCURLY
	  section_header[ $pack ] ?
	  section_import[ $pack ] ?

	  ( section_property[ $pack ] )*

	  ( section_composite_structure[ $pack ] )*
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// SYSTEM SPECIFCATION
////////////////////////////////////////////////////////////////////////////////

def_system
returns [ sep::System * sys ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr(sep::Specifier::COMPONENT_SYSTEM_KIND,
			sep::Specifier::MOC_COMPOSITE_STRUCTURE_KIND );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	sep::ParserUtil::declareDefaultEndingStateIfNeed(needDefaultStateFinal,
			needDefaultStateTerminal, needDefaultStateReturn);

	SET_RULE_LOCATION($sys);
}
	: ( ms=executable_modifier_specifier
	  { mdfr = $ms.mdfr; spcfr.ifnot_define( $ms.spcfr ); }
	  )?  'system'

	  ( LT_ ( 'moc:' )?  executable_specifier[ & spcfr ] GT )?
	  id=ID
	  {
		PUSH_CTX_CPM( _SYSTEM_ = $sys = new sep::System($id->getText()) );

		$sys->getwModifier().override_ifdef( mdfr );

		$sys->getwSpecifier().ifnot_define( spcfr );
	  }

	  ( StringLiteral
	  { $sys->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  LCURLY

//	  section_header_import_parameter_property[ $sys ]

	  section_header[ $sys ] ?
	  section_import[ $sys ] ?

	  ( section_parameter[ $sys ] )*

	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty($sys); }

	  ( section_property[ $sys ] )*

	  ( section_composite_structure[ $sys ] )*

	  ( section_behavior[ $sys ]
	  | section_statemachine[ $sys ]
	  )?
	  
	  // Conditional Template Code Generation for @moe
	  {  sep::TemplateFactory::genBehavior($sys); }

	  ( section_model_of_computation[ $sys ]
	  | section_model_of_interaction[ $sys ]
	  | section_model_of_execution[ $sys ]
	  )*
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// NEW [ [ FULLY ] QUALIFIED ] NAME ID
////////////////////////////////////////////////////////////////////////////////

qualifiedNameID
returns [ std::string s , std::size_t nb = 1 ]
@init{
	cpLOCATOR.clear();
	cpQNID.clear();
}
	: id=ID       { $s = $id->getText(); }
	  ( ( DOT     { cpQNID.push_back($s); $s = $s + "." ;  ++$nb; }
//	    | COLON   { $s = $s + ":" ; }
	    | COLONx2 { cpLOCATOR = $s; cpQNID.clear(); $s = $s + "::"; }
	    )
	    id=ID     { cpQNID.push_back($id->getText());  $s = $s + $id->getText(); }
	  )*
	;


integer_constant
returns [ std::size_t val ]
	: n=IntegerLiteral
	{ $val = NUM_INT($n->getText()); }

	| cid=qualifiedNameID
	{ $val = sep::ParserUtil::getIntegerConstant($cid.s, $cid.nb); }
	;


float_constant
returns [ sep::avm_float_t val ]
	: f=FloatLiteral
	{ $val = NUM_FLOAT($f->getText()); }

	| cid=qualifiedNameID
	{ $val = sep::ParserUtil::getFloatConstant($cid.s, $cid.nb); }
	;


////////////////////////////////////////////////////////////////////////////////
// section HEADER
////////////////////////////////////////////////////////////////////////////////

section_header
/* in */[ sep::Machine * container ]
	: '@header:'
	;


////////////////////////////////////////////////////////////////////////////////
// section IMPORT
////////////////////////////////////////////////////////////////////////////////

section_import [ sep::Machine * container ]
	: '@import:' ( include_package )+
	;

include_package
	: '@include'
	  ( StringLiteral  SEMI
	  | LCURLY  ( StringLiteral )+  RCURLY
	  )
	;



////////////////////////////////////////////////////////////////////////////////
// EXECUTABLE SPECIFCATION
////////////////////////////////////////////////////////////////////////////////
/*
executable_specification
/* in * [ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * machine ]
@init{
	std::size_t initialCount = 1;
	std::size_t maximalCount = AVM_NUMERIC_MAX_SIZE_T;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	SET_RULE_LOCATION($machine);
}
	: 'executable'
	  ( LT_
		( ( 'moc:' )?  executable_specifier[ &( $spcfr ) ]
	 	  ( COMMA  def_instance_count[ & initialCount , & maximalCount ] )?

		| def_instance_count[ & initialCount , & maximalCount ]
		)?
	  GT )?
	  id=ID
	  {
		PUSH_CTX_CPM( $machine = sep::Machine::newExecutable(
				container, $id->getText(), $spcfr) );

		$machine->getwModifier().override_ifdef( $mdfr );

		container->saveOwnedElement( $machine );

		$machine->getUniqInstanceSpecifier()
				->setInstanceCount(initialCount, maximalCount);
	  }

	  ( StringLiteral
	  { $machine->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  def_machine_parameters[ $machine , sep::Modifier::PROPERTY_PARAMETER_MODIFIER ] ?

	  def_machine_returns[ $machine , sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER ] ?

	  def_body_machine[ $machine ]
	;



////////////////////////////////////////////////////////////////////////////////
// FLATTENED SPECIFICATION
////////////////////////////////////////////////////////////////////////////////

executable_component [ ]
returns
	:
	;
*/

////////////////////////////////////////////////////////////////////////////////
// section PROCEDURE
////////////////////////////////////////////////////////////////////////////////

section_procedure [ sep::Machine * container ]
	: '@procedure:'
	  ( p=def_procedure[ container ] )*
	;


def_procedure [ sep::Machine * container ]
returns [ sep::Machine * procedure ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr( sep::Specifier::EXECUTABLE_PROCEDURE_MODEL_SPECIFIER );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	sep::ParserUtil::checkProcedureCompositeMocKind($procedure);

	SET_RULE_LOCATION($procedure);
}
	: ( ms=procedure_modifier_specifier
	  { mdfr.override_ifdef( $ms.mdfr ); spcfr.override_ifdef( $ms.spcfr ); }
	  )?
	  'procedure'
	  ( LT_ ( 'moc:' )?  executable_specifier[ & spcfr ]  GT )?
	  id=ID
	  {
		PUSH_CTX_CPM( $procedure = sep::Machine::newProcedure(
				container, $id->getText(), spcfr) );

		$procedure->getwModifier().override_ifdef( mdfr );

		$container->saveOwnedElement( $procedure );
	  }

	  ( StringLiteral
	  { $procedure->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  def_machine_parameters[ $procedure ] ?

	  def_machine_returns[ $procedure ,
			sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER ] ?

	  def_body_procedure[ $procedure ]
	;


def_machine_parameters [ sep::Machine * machine ]
@init{
	sep::avm_offset_t offset = 0;
	sep::Modifier mdfr = sep::Modifier::PROPERTY_PARAMETER_MODIFIER;

	sep::PropertyPart * declPropertyPart = &( $machine->getPropertyPart() );
}
	: LBRACKET  def_machine_variable_parameter_atom[ declPropertyPart , mdfr , offset ]
	  ( COMMA   def_machine_variable_parameter_atom[ declPropertyPart , mdfr , ++offset ] )*
	  RBRACKET

	| LPAREN   def_machine_variable_parameter_atom[ declPropertyPart , mdfr , offset ]
	  ( COMMA  def_machine_variable_parameter_atom[ declPropertyPart , mdfr , ++offset ] )*
	  RPAREN
	;


def_machine_variable_parameter_atom
/* in */[ sep::PropertyPart * paramDecl ,
		sep::Modifier mdfr , sep::avm_offset_t offset ]
@init{
	sep::Variable * variable;
	sep::Machine * machine = $paramDecl->getContainer()->as_ptr< sep::Machine >();
	sep::BF paramT = sep::TypeManager::UNIVERSAL;
	std::string paramID;
	sep::BF value;
}
	: ( m=modifier_param { $mdfr.override_ifdef( $m.mdfr ); } )?
	  tv=type_var { paramT = $tv.type; }
	  ( id=ID     { paramID = $id->getText(); }
	    ( iv=initial_value  { value = $iv.bf; } )?
	  )?
	  {
		$paramDecl->saveOwnedVariable( variable = new sep::Variable(
				machine, $mdfr, paramT, paramID, value ) );
	  }

	| 'bind:'
	  ( //!g4!( type_var COLON  ) =>  
		tv=type_var COLON { paramT = $tv.type; }
	    e=expression { value = $e.bf; }
	  | vid=qualifiedNameID
	  {
		value = sep::ParserUtil::getVariable($vid.s, $vid.nb);
		if( value.valid() ) { paramT = value.to_ptr< sep::Variable >()->getType(); }
	  }
	  )
	  {
		paramID = sep::OSS() << '#' << offset;
		$paramDecl->saveOwnedVariable( variable = new sep::Variable(machine,
						$mdfr.addNatureKind( sep::Modifier::NATURE_BIND_KIND ),
						paramT, paramID, value ) );

		variable->setOwnedOffset( offset );
	  }
	;


def_machine_returns
/* in */[ sep::Machine * machine , sep::Modifier mdfr ]
@init{
	sep::avm_offset_t offset = 0;
	$mdfr.setDirectionKind( sep::Modifier::DIRECTION_RETURN_KIND );
	sep::BF value;

	sep::PropertyPart * declPropertyPart = &( machine->getPropertyPart() );
}
	: ( '-->' | 'returns:' )
	  ( ( LBRACKET  def_machine_variable_return_atom[ declPropertyPart , $mdfr , offset]
	      ( COMMA   def_machine_variable_return_atom[ declPropertyPart , $mdfr , ++offset ] )*
	      RBRACKET
	    )

	  | ( LPAREN   def_machine_variable_return_atom[ declPropertyPart , $mdfr , offset]
	      ( COMMA  def_machine_variable_return_atom[ declPropertyPart , $mdfr , ++offset ] )*
	      RPAREN
	    )

	  | tv=type_var ( iv=initial_value  { value = $iv.bf; } )?
	  {
		sep::Variable * variable =
				new sep::Variable(machine, $mdfr, $tv.type, "#0", value);

		declPropertyPart->saveOwnedVariable( variable );
	  }
	  )
	;


def_machine_variable_return_atom
/* in */[ sep::PropertyPart * paramDecl ,
		sep::Modifier mdfr , sep::avm_offset_t offset ]
@init{
	sep::Variable * variable;
	sep::Machine * machine = $paramDecl->getContainer()->as_ptr< sep::Machine >();
	sep::BF paramT = sep::TypeManager::UNIVERSAL;
	std::string paramID;
	sep::BF value;
}
	: ( m=modifier_param { $mdfr.override_ifdef( $m.mdfr ); } )?
	  tv=type_var { paramT = $tv.type; }
	  ( id=ID     { paramID = $id->getText(); }
	    ( iv=initial_value  { value = $iv.bf; } )?
	  )?
	  {
		$paramDecl->saveOwnedVariable( variable =
				new sep::Variable(machine, $mdfr, paramT, paramID, value) );
	  }

	| 'bind:'
	  ( //!g4!( type_var COLON  ) =>
		tv=type_var COLON { paramT = $tv.type; }
	    e=expression { value = $e.bf; }
	  | vid=qualifiedNameID
	  {
		value = sep::ParserUtil::getVariable($vid.s, $vid.nb);
		if( value.valid() ) { paramT = value.to_ptr< sep::Variable >()->getType(); }
	  }
	  )
	  {
		paramID = sep::OSS() << '#' << offset;

		variable = new sep::Variable(machine,
				$mdfr.addNatureKind( sep::Modifier::NATURE_BIND_KIND ),
				paramT, paramID, value);

		$paramDecl->saveOwnedVariable( variable );

		variable->setOwnedOffset( offset );
	  }
	;



def_body_procedure [ sep::Machine * procedure ]
	: LCURLY
	  ( //!g4!( def_body_machine_using_section_predicat ) =>
	    def_body_procedure_section[ procedure ]

	  | def_body_procedure_simplif[ procedure ]
	  )
	  RCURLY
	;

def_body_procedure_section [ sep::Machine * procedure ]
	: section_header[ $procedure ] ?
	  section_import[ $procedure ] ?

	  ( section_parameter[ $procedure ] )*

	  ( section_property [ $procedure ] )*

	  ( section_composite_structure[ $procedure ] )*

	  ( section_behavior[ $procedure ]
	  | section_statemachine[ $procedure ]
	  )?

	  ( section_model_of_computation[ $procedure ]
	  | section_model_of_execution  [ $procedure ]
	  | section_model_of_interaction[ $procedure ]
	  )*
	;


def_body_procedure_simplif [ sep::Machine * procedure ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr;
}
	: ( { mdfr = sep::Modifier::PROPERTY_UNDEFINED_MODIFIER; }

		( m=modifier_declaration  { mdfr = $m.mdfr; } )?

	    ( decl_variable[ &( $procedure->getPropertyPart() ) , mdfr ]

	    | ads=any_def_statemachine[ $procedure , mdfr , spcfr ]

	    | def_state_activity[ $procedure ]
	    )
	  )+
	;


////////////////////////////////////////////////////////////////////////////////
// section COMPOSITE STRUCTURE
////////////////////////////////////////////////////////////////////////////////

section_composite_structure [ sep::Machine * container ]
	: section_routine[ container ]
	| section_procedure[ container ]

	| section_composite_generic[ container ]
	| section_machine_model[ container ]
	| section_machine_prototype[ container ]
	| section_machine_instance[ container ]
	;

section_composite_generic [ sep::Machine * container ]
	: ( '@composite:'  |  '@executable:'  |  '@machine:' )
	  ( m=executable_machine[ container ] )*
	;


section_machine_model [ sep::Machine * container ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr( sep::Specifier::DESIGN_MODEL_SPECIFIER );
}
	: '@model:'
	  ( m=executable_model_definiton[ container , mdfr , spcfr ] )*
	;


section_machine_prototype [ sep::Machine * container ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr( sep::Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER );
}
	: '@prototype:'
	  ( m=executable_model_definiton[ container , mdfr , spcfr ] )*
	;

section_machine_instance [ sep::Machine * container ]
	: '@instance:'
	  ( edi=executable_instance_definiton[ container ] )*
	;


executable_machine [ sep::Machine * container ]
returns [ sep::Machine * machine ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr;
}
	: ( ms=executable_modifier_specifier
	  { mdfr = $ms.mdfr; spcfr = $ms.spcfr; }
	  )?

	  ( dm=def_machine[ $container , mdfr , spcfr ]
	  { $machine = $dm.machine;  }

	  | ads=any_def_statemachine[ $container , mdfr , spcfr ]
	  { $machine = $ads.machine;  }

	  | emi=decl_instance[ $container , mdfr , spcfr ]
	  { $machine = $emi.instance; }
	  )
	;


executable_model_definiton
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * machine ]
	: ( ms=executable_modifier_specifier
	  { $mdfr.override_ifdef( $ms.mdfr );  $spcfr.override_ifdef( $ms.spcfr ); }
	  )?

	  ( dm=def_machine      [ $container , $mdfr , $spcfr ]
	  { $machine = $dm.machine;  }

	  | ads=def_statemachine[ $container , $mdfr , $spcfr ]
	  { $machine = $ads.machine; }
	  )
	;

executable_instance_definiton [ sep::Machine * container ]
returns [ sep::Machine * instance ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr( sep::Specifier::DESIGN_INSTANCE_STATIC_SPECIFIER );
}
	: ( ms=instance_modifier_specifier
	  { mdfr = $ms.mdfr; spcfr = $ms.spcfr; }
	  )?

	  emi=decl_instance[ $container , mdfr , spcfr ]
	  { $instance = $emi.instance; }
	;


////////////////////////////////////////////////////////////////////////////////
// INSTANCE MACHINE
////////////////////////////////////////////////////////////////////////////////

decl_instance
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * instance ]
@init{
	sep::BF aModel;

	std::size_t initialCount = 1;
	std::size_t maximalCount = AVM_NUMERIC_MAX_SIZE_T;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	if( aModel.is< sep::Machine >() )
	{
		POP_CTX;
	}
	SET_RULE_LOCATION($instance);
}
	: 'instance'  ( 'machine' | 'statemachine' )?
	  LT_
		( 'model:' )? mm=instance_machine_model  { aModel = $mm.model; }

		( COMMA  def_instance_count[ & initialCount , & maximalCount ] )?
	  GT  id=ID
	  {
		if( aModel.is< sep::Machine >() )
		{
			PUSH_CTX_NEW( aModel.to_ptr< sep::Machine >() );
		}

		$instance = sep::Machine::newInstance(container,
				$id->getText(), aModel, initialCount, maximalCount);

		$instance->getwModifier().override_ifdef( mdfr );

		$instance->getwSpecifier().override_ifdef(
				$spcfr.isDesignInstanceDynamic() ?
						$spcfr : $spcfr.setDesignInstanceStatic() );

		container->saveOwnedElement( $instance );
	  }

	  ( StringLiteral
	  { $instance->setUnrestrictedName($StringLiteral->getText()); }
	  )?
/*
	  decl_instance_machine_params [ instance ] ?
	  decl_instance_machine_returns[ instance ] ?

	  ( def_body_machine[ machine ] | SEMI )
*/
	  ( LPAREN
	    ( def_instance_on_new_activity[ $instance ] ) ?
	    RPAREN
	  )?

	  ( SEMI

	  | LCURLY
		( s=statement { $instance->getUniqBehaviorPart()->seqOnCreate($s.ac); } )*

		( def_instance_activity[ $instance ] )*
	    RCURLY
	  )
	;


def_instance_on_new_activity [ sep::Machine * instance ]
@init{
	std::size_t position = 0;
}
	: def_instance_on_new_activity_parameter[ $instance , position++ ]
      ( COMMA def_instance_on_new_activity_parameter[ $instance , position++ ] )*
	;

def_instance_on_new_activity_parameter
/* in */[ sep::Machine * instance , std::size_t position ]
	: //!g4!( lvalue  op_assign_param ) =>
	  lv=lvalue  oap=op_assign_param  e=expression
	  { $instance->getUniqBehaviorPart()->seqOnCreate( NEW_STMT2($oap.op, $lv.bf, $e.bf) ); }

	| e=expression
	  {
		sep::ParserUtil::appendInstanceDynamicPositionalParameter(
				$instance, $e.bf, position);
	  }
	;

op_assign_param
returns [ const sep::Operator * op ]
	: ( ASSIGN | COLON )  { $op = OP(ASSIGN);       }
	| ASSIGN_REF          { $op = OP(ASSIGN_REF);   }
	| ASSIGN_MACRO        { $op = OP(ASSIGN_MACRO); }
	;


def_instance_activity [ sep::Machine * instance ]
@init{
	sep::BehavioralPart * theBehavior = $instance->getUniqBehaviorPart();
}
	: '@create'   bs=block_statement  { theBehavior->seqOnCreate($bs.ac); }
	| '@start'    bs=block_statement  { theBehavior->seqOnStart($bs.ac);   }
/*
	| '@init'     bs=block_statement  { theBehavior->seqOnInit($bs.ac);   }

	| '@ienable'  bs=block_statement  { theBehavior->seqOnIEnable($bs.ac); }
	| '@enable'   bs=block_statement  { theBehavior->seqOnEnable ($bs.ac); }

	| '@idisable' bs=block_statement  { theBehavior->seqOnIDisable($bs.ac); }
	| '@disable'  bs=block_statement  { theBehavior->seqOnDisable ($bs.ac); }

	| '@iabort'   bs=block_statement  { theBehavior->seqOnIAbort($bs.ac); }
	| '@abort'    bs=block_statement  { theBehavior->seqOnAbort($bs.ac); }

	| '@irun'     bs=block_statement  { theBehavior->seqOnIRun($bs.ac); }
	| '@run'      bs=block_statement  { theBehavior->seqOnRun($bs.ac); }
	| '@rtc'      bs=block_statement  { theBehavior->seqOnRtc($bs.ac); }

	| '@final'    bs=block_statement  { theBehavior->seqOnFinal($bs.ac); }
*/	;


////////////////////////////////////////////////////////////////////////////////
// section BEHAVIOR | STATEMACHINE
////////////////////////////////////////////////////////////////////////////////

section_behavior [ sep::Machine * container ]
	: '@behavior:'
	  { $container->getwSpecifier().setMocCompositeStructure(); }
	  
	  ( m=executable_machine[ container ]  
	  { $container->getUniqBehaviorPart()->appendOwnedBehavior( $m.machine ); }
	  )+
	;


////////////////////////////////////////////////////////////////////////////////
// definition MACHINE
////////////////////////////////////////////////////////////////////////////////

def_instance_count
/* in */[ std::size_t * initial , std::size_t * maximal ]
@after{
	if( *($maximal) < *($initial) )
	{
		*($maximal) = *($initial);
	}
}
	: ( 'multiplicity:' | 'instance:' )?
	  ( LBRACKET
	    ( n=integer_constant  { *($initial) = $n.val; }
	      COMMA
	      ( n=integer_constant  { *($maximal) = $n.val; }
	      | ( STAR | PLUS )     { *($maximal) = AVM_NUMERIC_MAX_SIZE_T; }
	      )
	    | STAR  { *($initial) = 0; *($maximal) = AVM_NUMERIC_MAX_SIZE_T; }
	    | PLUS  { *($initial) = 1; *($maximal) = AVM_NUMERIC_MAX_SIZE_T; }
	    )
	    RBRACKET

	  | LPAREN
	    def_instance_count_atom[ $initial , $maximal ]
	    ( COMMA ?  def_instance_count_atom[ $initial , $maximal ] )*
	    RPAREN
	  )
	;

def_instance_count_atom
/* in */[ std::size_t * initial , std::size_t * maximal ]
	: 'init:' n=integer_constant  { *($initial) = $n.val; }
	| 'max:'  n=integer_constant  { *($maximal) = $n.val; }
	;


def_machine
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * machine ]
@init{
	std::size_t initialCount = 1;
	std::size_t maximalCount = AVM_NUMERIC_MAX_SIZE_T;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	SET_RULE_LOCATION($machine);
}
	: 'machine'
	  ( LT_
		( ( 'moc:' )?  executable_specifier[ &( $spcfr ) ]
	 	  ( COMMA  def_instance_count[ & initialCount , & maximalCount ] )?

		| def_instance_count[ & initialCount , & maximalCount ]
		)?
	  GT )?
	  id=ID
	  {
		PUSH_CTX_CPM( $machine = sep::Machine::newExecutable(
				container, $id->getText(), $spcfr) );

		$machine->getwModifier().override_ifdef( $mdfr );

		container->saveOwnedElement( $machine );

		$machine->getUniqInstanceSpecifier()->
				setInstanceCount(initialCount, maximalCount);
	  }

	  ( StringLiteral
	  { $machine->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  def_machine_parameters[ $machine ] ?

	  def_machine_returns[ $machine , sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER ] ?

	  def_body_machine[ $machine ]
	;

///////////////////////////////////////////////////////////////////////////////
//!g4! TO DELETE
///////////////////////////////////////////////////////////////////////////////
//def_body_machine_using_section_header_predicat
//	: '@header:'
//	;
//
//def_body_machine_using_section_import_predicat
//	: '@import:'
//	;
//
//def_body_machine_using_section_parameter_predicat
//	: '@parameter:' | '@param:'  /* deprecated */
//	| '@input:'     | '@inout:'  | '@output:'
//	| '@returns:'   | '@return:' /* deprecated */
//	;
//
//def_body_machine_using_section_property_predicat
//	: '@property:'
//	|  '@declaration:'  //deprecated
//	| '@public:'    |  '@protected:'
//	| '@private:'   |  '@local:'
//	;
//
//
// def_body_machine_using_section_predicat
// 	: def_body_machine_using_section_header_predicat
// 	| def_body_machine_using_section_import_predicat
// 	| def_body_machine_using_section_parameter_predicat
// 	| def_body_machine_using_section_property_predicat
//
// 	| '@macro:' | '@routine' | '@procedure:'
//
// 	| '@composite:'  |  '@machine:'  |  '@executable:'
// 	| '@state:'      |  '@region:'   |  '@statemachine:'
//
// 	| '@behavior:'  | '@transition:'
//
// 	// Model Of { Computation , Execution , Interaction }
// 	| '@moc:' | '@moe:' | '@com:' | '@interaction:'
// 	;
///////////////////////////////////////////////////////////////////////////////


def_body_machine [ sep::Machine * machine ]
	: LCURLY
	      //( def_body_machine_using_section_predicat ) =>
	      def_body_machine_section[ $machine ]

	    //| def_body_machine_simplif[ $machine ]
	  RCURLY
	;

def_body_machine_section [ sep::Machine * machine ]
	: section_header[ $machine ] ?
	  section_import[ $machine ] ?

	  ( section_parameter[ $machine ] )*

	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty( $machine ); }

	  ( section_property [ $machine ] )*

	  ( section_composite_structure[ $machine ] )*

	  ( section_behavior[ $machine ]
	  | section_statemachine[ $machine ]
	  )?

	  // Conditional Template Code Generation for @moe
	  {  sep::TemplateFactory::genBehavior($machine); }

	  ( section_model_of_computation[ $machine ]
	  | section_model_of_execution  [ $machine ]
	  | section_model_of_interaction[ $machine ]
	  )*
	;

def_body_machine_simplif [ sep::Machine * machine ]
@init{
	sep::PropertyPart & declPropertyPart = machine->getPropertyPart();
}
	: ( ( property_declaration[ &declPropertyPart ,
				sep::Modifier::PROPERTY_UNDEFINED_MODIFIER ]
		)*

	  | ( def_moe_primitive[ $machine ] )+
	  )
	;

////////////////////////////////////////////////////////////////////////////////
// definition STATEMACHINE
////////////////////////////////////////////////////////////////////////////////

any_def_statemachine
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * machine ]
	: ( ms=executable_modifier_specifier
	  { $mdfr.override_ifdef( $ms.mdfr ); $spcfr.override_ifdef( $ms.spcfr ); }
	  )?

	  (  dss=def_state_singleton[ $container , $mdfr , $spcfr ]
	  { $machine = $dss.state;   }

	  | ds=def_state[ $container , $mdfr , $spcfr ]
	  { $machine = $ds.state;   }

	  | sm=def_statemachine[ $container , $mdfr , $spcfr ]
	  { $machine = $sm.machine; }
	  )
	;


def_statemachine
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * machine ]
@init{
//	resetTransitionID();
	resetConnectorID();
	resetBufferID();

	std::size_t initialCount = 1;
	std::size_t maximalCount = AVM_NUMERIC_MAX_SIZE_T;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	SET_RULE_LOCATION($machine);
}
	: 'statemachine'
	  ( LT_
		( ( 'moc:' )?  executable_specifier[ &( $spcfr ) ]
	 	  ( COMMA  def_instance_count[ & initialCount , & maximalCount ] )?

		| def_instance_count[ & initialCount , & maximalCount ]
		)?
	  GT
	  )?

	  ( id=ID
		{
			if( $spcfr.isUndefined() )
			{
				$spcfr.setComponentExecutable();
			}
			PUSH_CTX_CPM( $machine = sep::Machine::newStatemachine(
					$container, $id->getText(), $spcfr) );

			$machine->getwModifier().override_ifdef( $mdfr );

			$container->saveOwnedElement( $machine );

			$machine->getUniqInstanceSpecifier()->
					setInstanceCount(initialCount, maximalCount);
		}

	  | ( LBRACKET         { $spcfr.setGroupSome(); }
	    | LBRACKET_EXCEPT  { $spcfr.setGroupExcept(); }
	    )
		{
			PUSH_CTX_CPM( $machine = sep::Machine::newStatemachine(
					$container, "[]", $spcfr/*, type*/) );

			$machine->getwModifier().override_ifdef( $mdfr );

			$container->saveOwnedElement( $machine );

			$machine->getUniqInstanceSpecifier()->
					setInstanceCount(initialCount, maximalCount);
		}

	    ( id=ID          { $machine->appendGroupId( $id->getText() ); }
	      ( COMMA id=ID  { $machine->appendGroupId( $id->getText() ); } )*

	    | STAR
		{ $machine->getwSpecifier().setGroupEvery(); }
	    )
	    RBRACKET   { $machine->setGroupId(); }
	  )

	  ( StringLiteral
	  { $machine->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  def_machine_parameters[ $machine ] ?

	  def_machine_returns[ $machine , sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER ] ?

	  def_body_statemachine[ $machine ]
	;


//!![MIGRATION]:INSTANCE
/*
decl_instance_statemachine [ sep::Machine * container ]
returns [ sep::Machine * machine ]
@init{
//	resetTransitionID();
	resetConnectorID();
	resetBufferID();

	sep::Specifier spcfr;

	sep::BF aModel;

	std::size_t initialCount = 1;
	std::size_t maximalCount = AVM_NUMERIC_MAX_SIZE_T;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	SET_RULE_LOCATION($machine);
}
	: 'statemachine'
	  LT_
		( ( 'moc:' )?  executable_specifier[ & spcfr ]  COMMA )?
		( 'model:' )?  mm=instance_machine_model  { aModel = $mm.model; }

		( COMMA  def_instance_count[ & initialCount , & maximalCount ] )?
	  GT  id=ID
	  {
		if( spcfr.isUndefined() )
		{
			spcfr.setComponentStatemachine();
		}
		PUSH_CTX_CPM( $machine = sep::Machine::newStatemachineInstance(
				container, $id->getText(), spcfr, aModel) );

		$machine->getwSpecifier().setDesignInstanceStatic();

		container->saveOwnedElement( $machine );

		$machine->getUniqInstanceSpecifier()->
				setInstanceCount(initialCount, maximalCount);
	  }

	  ( StringLiteral
	  { $machine->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  decl_instance_machine_params [ machine ] ?
	  decl_instance_machine_returns[ machine ] ?

	  ( def_body_statemachine[ machine ] | SEMI )
	;
*/

def_body_statemachine [ sep::Machine * machine ]
	: LCURLY
	  section_header[ $machine ] ?
	  section_import[ $machine ] ?

	  ( section_parameter[ $machine ] )*

	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty( $machine ); }

	  ( section_property [ $machine ] )*

	  ( section_composite_structure[ $machine ] )*

	  ( section_state_region[ $machine ]
	  | ( section_composite_region[ $machine ] )+
	  )?
	  
	  section_transition[ $machine ] ?

	  // Conditional Template Code Generation for @moe
	  {  sep::TemplateFactory::genBehavior(machine); }

	  ( section_model_of_computation[ $machine ]
	  | section_model_of_execution  [ $machine ]
	  | section_model_of_interaction[ $machine ]
	  )*
	  RCURLY
	;


section_state_region [ sep::Machine * container ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr;
}
	: ( '@state:' | '@region:' )
	  { $container->getwSpecifier().setMocStateTransitionSystem(); }

	  ( m=any_def_statemachine[ $container , mdfr , spcfr ] )+
	;

section_composite_region [ sep::Machine * container ]
@init{
	sep::Machine * regionComposititeState;
	
	std::string unrestrictedName;
	
	sep::Modifier mdfr;

	sep::Specifier spcfr;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	SET_RULE_LOCATION(regionComposititeState);
}
	: '@region(' ( 'name:' )? id=ID
	  	( sl=StringLiteral  { unrestrictedName = $sl->getText(); } )?	
	 '):'
	  {
	  	$container->getwSpecifier().setMocCompositeStructure();
	  	
		PUSH_CTX_CPM( regionComposititeState = sep::Machine::newState(
				$container, $id->getText(),
				sep::Specifier::MOC_STATE_TRANSITION_SYSTEM_KIND) );
				
		regionComposititeState->setUnrestrictedName( unrestrictedName );
				
		$container->saveOwnedElement( regionComposititeState );
	  }

	  ( m=any_def_statemachine[ regionComposititeState , mdfr , spcfr ] )+
	;


section_statemachine [ sep::Machine * container ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr;
}
	: '@statemachine:'
	  { $container->getwSpecifier().setMocStateTransitionSystem(); }

	  ( m=any_def_statemachine[ $container , mdfr , spcfr ] )+
	;



def_state
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * state = nullptr ]
@init{
	std::string sid;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	POP_CTX;

	SET_RULE_LOCATION($state);
}
	: 'state'
	  ( LT_ ( 'moc:' )?  executable_specifier[ &( $spcfr ) ]  GT
		{ sid = "$" + $spcfr.strAnyStateMoc(""); }
	  )?
	  ( id=state_id
		{
			if( $spcfr.couldBeStateMocSIMPLE() )
			{
				$spcfr.setStateMocSIMPLE();
			}

			PUSH_CTX_CPM(
					$state = sep::Machine::newState($container, $id.s, $spcfr) );

			$state->getwModifier().override_ifdef( $mdfr );

			$container->saveOwnedElement( $state );
		}

	  | ( LBRACKET         { $spcfr.setGroupSome(); }
	    | LBRACKET_EXCEPT  { $spcfr.setGroupExcept(); }
	    )
		{
			PUSH_CTX_CPM(
					$state = sep::Machine::newState($container, "[]", $spcfr) );

			$container->saveOwnedElement( $state );

			$state->getwModifier().override_ifdef( $mdfr );
		}

	    ( id=state_id          { $state->appendGroupId( $id.s ); }
	      ( COMMA id=state_id  { $state->appendGroupId( $id.s ); } )*

	    | STAR
		{ $state->getwSpecifier().setGroupEvery(); }
	    )
	    RBRACKET   { $state->setGroupId(); }
	  )?

	  {
		if( $state == nullptr )
		{
			PUSH_CTX_CPM(
					$state = sep::Machine::newState($container, sid, $spcfr) );

			$state->getwModifier().override_ifdef( $mdfr );

			$container->saveOwnedElement( $state );
		}
	  }

	  ( StringLiteral
	  { $state->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  ( def_body_state[ $state ] | SEMI )
	;


state_kw_id
returns [ std::string s ]
	: '#init'      { $s = "#init"    ; }
	| '#initial'   { $s = "#initial" ; }
	| '#start'     { $s = "#start"   ; }

	| '#dhistory'  { $s = "#dhistory"; }
	| '#shistory'  { $s = "#shistory"; }

	| '#final'
	{ $s = "#final"   ; needDefaultStateFinal.remove(_CPM_);    }

	| '#terminal'
	{ $s = "#terminal"; needDefaultStateTerminal.remove(_CPM_); }

	| '#return'
	{ $s = "#return"  ; needDefaultStateReturn.remove(_CPM_);   }
	;

state_id
returns [ std::string s ]
	: kw=state_kw_id  { $s = $kw.s; }
	| id=ID           { $s = $id->getText(); }
	| DOLLAR id=ID    { $s = "#" + $id->getText(); }
	;




def_state_singleton
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
returns [ sep::Machine * state ]
@init{
	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	$state->getwModifier().override_ifdef( $mdfr );

	POP_CTX;

	SET_RULE_LOCATION($state);
}
	: ( '#initial'
	  {
		PUSH_CTX_CPM( $state = sep::Machine::newState(
				$container, "#initial", $spcfr.setPseudostateMocINITIAL()) );

		$container->saveOwnedElement( $state );
	  }

	  | '#start'
	  {
		PUSH_CTX_CPM( $state = sep::Machine::newState(
				$container, "#start", $spcfr.setStateMocSTART()) );

		$container->saveOwnedElement( $state );
	  }

	  | '#dhistory'
	  {
		PUSH_CTX_CPM( $state = sep::Machine::newState(
				$container, "#dhistory",
				$spcfr.setPseudostateMocDEEP_HISTORY()) );

		$container->saveOwnedElement( $state );
	  }

	  | '#shistory'
	  {
		PUSH_CTX_CPM( $state = sep::Machine::newState(
				$container, "#shistory",
				$spcfr.setPseudostateMocSHALLOW_HISTORY()) );

		$container->saveOwnedElement( $state );
	  }
	  )
	  LCURLY  def_body_state_simplif[ $state ]  RCURLY

	| '#final' bs=block_statement
	{
		PUSH_CTX_CPM( $state = sep::Machine::newState(
			$container, "#final", $spcfr.setStateMocFINAL()) );

		$container->saveOwnedElement( $state );

		$state->getUniqBehaviorPart()->seqOnFinal($bs.ac);

		needDefaultStateFinal.remove($container);
	}

	| '#terminal' bs=block_statement
	{
		PUSH_CTX_CPM( $state = sep::Machine::newState(
			$container, "#terminal", $spcfr.setPseudostateMocTERMINAL()) );

		$container->saveOwnedElement( $state );

		$state->getUniqBehaviorPart()->seqOnFinal($bs.ac);

		needDefaultStateTerminal.remove($container);
	}

	| '#return' bs=block_statement
	{
		PUSH_CTX_CPM( $state = sep::Machine::newState(
			$container, "#return", $spcfr.setPseudostateMocRETURN()) );

		$container->saveOwnedElement( $state );

		$state->getUniqBehaviorPart()->seqOnFinal($bs.ac);

		needDefaultStateReturn.remove($container);
	}
	;


executable_specifier [ sep::Specifier * spcfr ]
	: ka=executable_specifier_atom[ $spcfr ]
	  ( BAND ka=executable_specifier_atom[ $spcfr ] )*
	;


executable_specifier_atom [ sep::Specifier * spcfr ]
	: id=ID  { $spcfr->setMoc( $id->getText() ); }

//	| 'simple'     { $spcfr->setStateMocSIMPLE(); }
	| 'start'      { $spcfr->setStateMocSTART();  }
	| 'final'      { $spcfr->setStateMocFINAL();  }
//	| 'sync'       { $spcfr->setStateMocSYNC();   }

//	| 'initial'    { $spcfr->setPseudostateMocINITIAL();  }
//	| 'terminal'   { $spcfr->setPseudostateMocTERMINAL(); }
	| 'return'     { $spcfr->setPseudostateMocRETURN();   }

//	| 'junction'   { $spcfr->setPseudostateMocJUNCTION(); }
	| 'choice'     { $spcfr->setPseudostateMocCHOICE();   }

	| 'fork'       { $spcfr->setPseudostateMocFORK(); }
	| 'join'       { $spcfr->setPseudostateMocJOIN(); }

//	| 'dhistory'   { $spcfr->setPseudostateMocDEEP_HISTORY();    }
//	| 'shistory'   { $spcfr->setPseudostateMocSHALLOW_HISTORY(); }

	| 'and'        { $spcfr->setMocCompositeStructure();     }
	| 'or'         { $spcfr->setMocStateTransitionSystem();  }
	| '#sts'       { $spcfr->setMocStateTransitionSystem();  }
	| '#stf'       { $spcfr->setMocStateTransitionFlow();    }
	| 'flow'       { $spcfr->setCompositeMocDataFlow();      }
	
	| '#alt'       { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionAlternative();    }
	| '#opt'       { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionOption();         }
	| '#loop'      { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionLoop();           }
	| '#break'     { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionBreak();          }
	| '#par'       { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionParallel();       }
	| '#strict'    { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionStrictSequence(); }
	| '#weak'      { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionWeakSequence();   }
	| '#seq'       { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionWeakSequence();   }
	| '#critical'  { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionCritical();       }
	| '#ignore'    { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionIgnore();         }
	| '#consider'  { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionAlternative();    }
	| '#assert'    { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionAlternative();    }
	| '#neg'       { $spcfr->setComponentInteraction().setMocCompositeInteraction().setInteractionAlternative();    }
	
	;



instance_machine_model
returns [ sep::BF model ]
	: tid=qualifiedNameID
	{
		$model = sep::ParserUtil::getExecutableMachine($tid.s, $tid.nb);
		if( $model.invalid() )
		{
			sep::ParserUtil::avm_syntax_error(
				"instance_machine_model", getCurrentToken()/*tid*/->getLine() )
					<< "unexpected ID< " << $tid.s << " >"
					<< sep::ParserUtil::SYNTAX_ERROR_EOL;
		}
	}
	;


def_body_state [ sep::Machine * state ]
	: LCURLY
	  ( //!g4!( def_body_machine_using_section_predicat ) =>
	    def_body_state_section[ $state ]

	  | def_body_state_simplif[ $state ]
	  )
	  RCURLY
	;

def_body_state_section [ sep::Machine * machine ]
	: ( section_property[ $machine ] )*

	  ( section_composite_structure[ $machine ] )*

	  ( section_state_region[ $machine ]
	  | ( section_composite_region[ $machine ] )+
	  )?

	  section_transition[ $machine ] ?

	  ( section_model_of_computation[ $machine ]
	  | section_model_of_execution  [ $machine ]
	  | section_model_of_interaction[ $machine ]
	  )*
	;

def_body_state_simplif [ sep::Machine * state ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr;
}
	: ( { mdfr = sep::Modifier::PROPERTY_UNDEFINED_MODIFIER; }

		( m=modifier_declaration  { mdfr = $m.mdfr; } )?

	    ( decl_variable[ &( $state->getPropertyPart() ) , mdfr ]

	    | ads=any_def_statemachine[ $state , mdfr , spcfr ]

	    | def_transition[ $state , mdfr , spcfr ]

	    | def_state_activity[ $state ]
	    )
	  )*
	;

section_transition [ sep::Machine * state ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr;
}
	: '@transition:'
	  ( ( m=modifier_transition  { mdfr = $m.mdfr; } )?
	    def_transition[ $state , mdfr , spcfr ]
	  )*
	;

def_transition
/* in */[ sep::Machine * state ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
@init{
	sep::Transition * trans = nullptr;
	std::string t_id;

	mProcedureCallCount = 0;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	if( (mProcedureCallCount > 0) && (trans != nullptr) )
	{
		sep::ParserUtil::inlineTransitionProcedureCall(trans, trans->getNameID());
	}

	SET_RULE_LOCATION(trans);
}
	: ( tok='@'
	  | ( tok=AT_ID  { t_id = $tok->getText(); } )
	  )
	  {
		state->getUniqBehaviorPart()->saveOutgoingTransition(
				trans = new sep::Transition((* state), newTransitionID(t_id)) );

		trans->setModifier( $mdfr );

		trans->setSpecifier( $spcfr );
	  }
	  ( LT_  moc_transition[ trans ]  GT )?

	  moe_transition[ trans ]

	| 'transition'
	  {
		state->getUniqBehaviorPart()->saveOutgoingTransition(
				trans = new sep::Transition(* state) );

		trans->setModifier( $mdfr );

		trans->setSpecifier( $spcfr );
	  }
	  ( LT_ moc_transition[ trans ] GT )?

	  ( id=ID { t_id = $id->getText(); } )?
	  { trans->fullyUpdateAllNameID( newTransitionID(t_id) ); }

	  ( StringLiteral
	  { trans->setUnrestrictedName($StringLiteral->getText()); }
	  )?

	  moe_transition[ trans ]
	;

kind_transition
returns [ sep::Transition::MOC_KIND kind ]
	: id=ID
	{
		if( ($kind = sep::Transition::toMocKind($id->getText())) ==
			sep::Transition::MOC_UNDEFINED_KIND )
		{
			sep::ParserUtil::avm_syntax_error( "kind_transition", $id.line )
					<< "unexpected ID< " << $id->getText() << " >"
					<< sep::ParserUtil::SYNTAX_ERROR_EOL;
		}
	}
//	| 'simple'   { $kind = sep::Transition::MOC_SIMPLE_KIND;   }
	| 'abort'    { $kind = sep::Transition::MOC_ABORT_KIND;    }
	| 'final'    { $kind = sep::Transition::MOC_FINAL_KIND;    }
	| 'else'     { $kind = sep::Transition::MOC_ELSE_KIND;     }
//	| 'internal' { $kind = sep::Transition::MOC_INTERNAL_KIND; }
//	| 'auto'     { $kind = sep::Transition::MOC_AUTO_KIND;     }
	| 'flow'     { $kind = sep::Transition::MOC_FLOW_KIND;     }
	;


moc_transition_attribute
returns [ sep::Transition::moc_kind_t kind ]
@init{
	$kind = sep::Transition::MOC_UNDEFINED_KIND;
}
	: kt=kind_transition { $kind = $kt.kind; }
	( BAND 'else'        { $kind = $kind | sep::Transition::MOC_ELSE_KIND; } )?
	;

moc_transition [ sep::Transition * trans ]
	: moc_transition_atom[ trans ] ( COMMA moc_transition_atom[ trans ] )*
	;

moc_transition_atom [ sep::Transition * trans ]
	: ( 'moc:' )? kt=moc_transition_attribute
	{ trans->setMocKind( $kt.kind ); }

	| ( 'prior:' )? n=integer_constant
	{ trans->setPriority( $n.val ); }

	| ( 'proba:' )? p=float_constant
	{ trans->setProbability( $p.val ); }
	;


moe_transition [ sep::Transition * trans ]
	: bs=transition_statement        { trans->setStatement($bs.ac);   }
	  ( ( '-->' )?
	    tid=target_state_id          { trans->setTarget($tid.target); }
//	    ( COMMA tid=target_state_id  { trans->appendTarget($tid.target); } )*
	  SEMI )?

	| '-->' tid=target_state_id      { trans->setTarget($tid.target); }
//	  ( COMMA tid=target_state_id    { trans->appendTarget($tid.target); } )*
	  ( bs=transition_statement      { trans->setStatement($bs.ac); }
	  | SEMI
	  )
	;

transition_statement
returns [ sep::BFCode ac ]
@init{
	const sep::Operator * op = OP(SEQUENCE);
	bool implicitSequenceOp = true;
}
@after{
	if( implicitSequenceOp && $ac.valid() && $ac->hasOneOperand()
		&& sep::OperatorManager::isSchedule(op) )
	{
		sep::BFCode singleCode = $ac->first().bfCode();
		$ac = singleCode;
	}
}
	: LCURLY  ( o=op_block { op = $o.op; implicitSequenceOp = false; } )?
		{ $ac = NEW_STMT(op); }
		( s=statement  { $ac->append($s.ac); } )*

		( transition_trigger    [ $ac ] )?
		( transition_guard      [ $ac ] )?
		( transition_timed_guard[ $ac ] )?
		( transition_effect     [ $ac ] )?
	  RCURLY
	;

transition_trigger [ sep::BFCode ac ]
	: '@trigger:' ( s=statement_com_input  { $ac->append( $s.ac ); }  )*
	;

transition_guard [ sep::BFCode ac ]
	: '@guard:'
		( s=statement_guard
		{ $ac->append( $s.ac ); }

		| e=expression
		{ $ac->append( NEW_STMT1(OP(GUARD), $e.bf) ); }

		| LBRACKET e=expression RBRACKET
		{ $ac->append( NEW_STMT1(OP(GUARD), $e.bf) ); }
		)*
	;

transition_timed_guard [ sep::BFCode ac ]
	: '@tguard:'
		( s=statement_timed_guard
		{ $ac->append( $s.ac ); }

		| e=expression
		{ $ac->append( NEW_STMT1(OP(TIMED_GUARD), $e.bf) ); }

		| LCURLY e=expression RCURLY
		{ $ac->append( NEW_STMT1(OP(TIMED_GUARD), $e.bf) ); }
		)*
	;

transition_effect [ sep::BFCode ac ]
	: '@effect:' ( s=statement  { $ac->append( $s.ac ); } )*
	;


target_state_id
returns [ sep::BF target ]
@init{
	std::string tid;
	std::size_t nb = 1;
}
@after{
	if( ($target = sep::ParserUtil::getvarMachine(tid, nb)).invalid() )
	{
		$target = NEW_QNID(tid, nb);
	}
}
	: kw=target_state_kw_id  { tid = $kw.s; }

	| u=qualifiedNameID          { tid = $u.s; nb = $u.nb; }

	| DOLLAR id=ID    { tid ="$" + $id->getText(); }
	;


target_state_kw_id
returns [ std::string s ]
	: '#init'      { $s = "#init"    ; }
	| '#initial'   { $s = "#initial" ; }
	| '#start'     { $s = "#start"   ; }

	| '#dhistory'  { $s = "#dhistory"; }
	| '#shistory'  { $s = "#shistory"; }

	| '#final'
	{ $s = "#final";
		needDefaultStateFinal.push_back(_CPM_->getContainerMachine()); }

	| '#terminal'
	{ $s = "#terminal";
		needDefaultStateTerminal.push_back(_CPM_->getContainerMachine()); }

	| '#return'
	{ $s = "#return";
		needDefaultStateReturn.push_back(_CPM_->getContainerMachine()); }
	;


def_state_activity [ sep::Machine * state ]
@init{
	sep::BehavioralPart * theBehavior = state->getUniqBehaviorPart();
}
	: '@create'   bs=block_statement  { theBehavior->seqOnCreate($bs.ac); }
	| '@init'     bs=block_statement  { theBehavior->seqOnInit($bs.ac);   }

	| '@ienable'  bs=block_statement  { theBehavior->seqOnIEnable($bs.ac); }
	| '@enable'   bs=block_statement  { theBehavior->seqOnEnable ($bs.ac); }

	| '@idisable' bs=block_statement  { theBehavior->seqOnIDisable($bs.ac); }
	| '@disable'  bs=block_statement  { theBehavior->seqOnDisable ($bs.ac); }

	| '@iabort'   bs=block_statement  { theBehavior->seqOnIAbort($bs.ac); }
	| '@abort'    bs=block_statement  { theBehavior->seqOnAbort($bs.ac); }

	| '@irun'     bs=block_statement  { theBehavior->seqOnIRun($bs.ac); }
	| '@run'      bs=block_statement  { theBehavior->seqOnRun($bs.ac); }
	| '@rtc'      bs=block_statement  { theBehavior->seqOnRtc($bs.ac); }

	| '@final'    bs=block_statement  { theBehavior->seqOnFinal($bs.ac); }
	;


////////////////////////////////////////////////////////////////////////////////
// SECTION HEADER IMPORT PARAMETER PROPERTY or DEFAULT DECLARATION
////////////////////////////////////////////////////////////////////////////////

section_header_import_parameter_property
/* in */[ sep::Machine * container ]
	: //!g4!( def_body_machine_using_section_header_predicat ) =>
	  section_header[ $container ]

	  ( section_import[ $container ] )?

	  ( section_parameter[ $container ] )?

	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty( $container ); }

	  ( section_property[ $container ] )*

	| //!g4!( def_body_machine_using_section_import_predicat ) =>
	  section_import[ $container ]

	  ( section_parameter[ $container ] )?

	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty( $container ); }

	  ( section_property[ $container ] )*

	| //!g4!( def_body_machine_using_section_parameter_predicat ) =>
	  section_parameter[ $container ]

	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty( $container ); }

	  ( section_property[ $container ] )*

	| //!g4!( def_body_machine_using_section_property_predicat ) =>
	  // Conditional Template Code Generation for @declaration
	  {  sep::TemplateFactory::genProperty( $container ); }

	  ( section_property[ $container ] )+

	| {  sep::TemplateFactory::genProperty( $container ); }
	  section_property_free_declaration[ $container ]
	;



////////////////////////////////////////////////////////////////////////////////
// section PARAMETER DECLARATION
////////////////////////////////////////////////////////////////////////////////

section_parameter [ sep::Machine * container ]
@init{
	sep::PropertyPart * declPropertyPart = &( $container->getPropertyPart() );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(declPropertyPart);
}
	: ( '@parameter:' | '@param:' /* deprecated */ )
	  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_INPUT_PARAMETER_MODIFIER  ]
	  )*

	| '@input:'  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_INPUT_PARAMETER_MODIFIER  ]
	  )*

	| '@inout:'  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_INOUT_PARAMETER_MODIFIER  ]
	  )*

	| '@output:' ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_OUTPUT_PARAMETER_MODIFIER ]
	  )*

	| ( '@returns:' | '@return:' /* deprecated */ )
	  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER ]
	  )*
	;


////////////////////////////////////////////////////////////////////////////////
// section PROPERTY DECLARATION
////////////////////////////////////////////////////////////////////////////////

section_property [ sep::Machine * container ]
@init{
	sep::PropertyPart * declPropertyPart = &( $container->getPropertyPart() );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(declPropertyPart);
}
	: ( '@property:' | '@declaration:' /* deprecated */ )
	  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_UNDEFINED_MODIFIER ]
	  )*

	| '@public:'
	  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_PUBLIC_MODIFIER ]
	  )*

	| '@protected:'
	  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_PROTECTED_MODIFIER ]
	  )*

	| ( '@private:'  |  '@local:' )
	  ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_PRIVATE_MODIFIER ]
	  )*
	;


section_property_free_declaration [ sep::Machine * container ]
@init{
	sep::PropertyPart * declPropertyPart = &( $container->getPropertyPart() );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(declPropertyPart);
}
	: ( property_declaration[ declPropertyPart ,
				sep::Modifier::PROPERTY_UNDEFINED_MODIFIER ]
	  )*
	;

////////////////////////////////////////////////////////////////////////////////
// PROPERTY ELEMENT DECLARATION
////////////////////////////////////////////////////////////////////////////////

property_declaration
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: ( m=modifier_declaration { $mdfr.override_ifdef( $m.mdfr ); } )?
	  decl_property_element[ $declPropertyPart , $mdfr ]
	;

decl_property_element
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: decl_variable[ $declPropertyPart , $mdfr ]

	| decl_port   [ $declPropertyPart , $mdfr ]
	| decl_signal [ $declPropertyPart , $mdfr ]
	| decl_buffer [ $declPropertyPart , $mdfr ]
	| decl_channel[ $declPropertyPart , $mdfr ]

	| def_type  [ $declPropertyPart , $mdfr ]
	| def_enum  [ $declPropertyPart , $mdfr ]
	| def_union [ $declPropertyPart , $mdfr ]
	| def_choice[ $declPropertyPart , $mdfr ]
	| def_struct[ $declPropertyPart , $mdfr ]

	| decl_function[ $declPropertyPart , $mdfr ]
/*	
	| decl_procedure[ $declPropertyPart , $mdfr ]

	| decl_lambda[ $declPropertyPart , $mdfr ]
*/
	;


////////////////////////////////////////////////////////////////////////////////
// declaration MACHINE PRAMETERS
////////////////////////////////////////////////////////////////////////////////

labelled_argument
returns [ std::string label, sep::BF arg ]
	: ( //!g4!( ID COLON ) =>
        id=ID COLON  { $label = $id->getText(); }
	  | 'name:'                       { $label = "name"; }
	  | 'size:'                       { $label = "size"; }
	  )
	  e=expression  { $arg = $e.bf; }
	  
	| e=expression  { $arg = $e.bf; }
	;

decl_instance_machine_params [ sep::Machine * machine ]
@init{
	sep::BFVector labelledParams(
		( $machine->getType().is< sep::Machine >() ) ? $machine->getType().
			to_ptr< sep::Machine >()->getVariableParametersCount() : 0 );

	sep::BFList positionalParams;
}
@after{
	if( labelledParams.nonempty() )
	{
		sep::ParserUtil::computeInstanceMachineParameter(
				$machine, labelledParams, positionalParams);
	}
}
	: LPAREN
	  ( lp=labelled_argument
		{
			sep::ParserUtil::appendInstanceMachineParameter($machine, $lp.label,
					labelledParams, positionalParams, $lp.arg);
		}
	    ( COMMA
	    lp=labelled_argument
		{
			sep::ParserUtil::appendInstanceMachineParameter($machine, $lp.label,
					labelledParams, positionalParams, $lp.arg);
		}
	    )*
	  )?
	  RPAREN
	;


decl_instance_machine_returns [ sep::Machine * machine ]
@init{
	sep::BFVector labelledReturns(
		( $machine->getType().is< sep::Machine >() ) ? $machine->getType().
			to_ptr< sep::Machine >()->getVariableParametersCount() : 0 );

	sep::BFList positionalReturns;
}
@after{
	if( labelledReturns.nonempty() )
	{
		sep::ParserUtil::computeInstanceMachineReturn(
				$machine, labelledReturns, positionalReturns);
	}
}
	: ( '-->' | 'returns:' )
	  ( LPAREN
	    lp=labelled_argument
		{
			sep::ParserUtil::appendInstanceMachineReturn($machine, $lp.label,
					labelledReturns, positionalReturns, $lp.arg);
		}
	    ( COMMA
	      lp=labelled_argument
	      {
			sep::ParserUtil::appendInstanceMachineReturn($machine, $lp.label,
					labelledReturns, positionalReturns, $lp.arg);
	      }
	    )*
	    RPAREN

	  | lp=labelled_argument
		{
			sep::ParserUtil::appendInstanceMachineReturn($machine, $lp.label,
					labelledReturns, positionalReturns, $lp.arg);
		}
	  )
	;



activity_machine_param_return
/* in */[ sep::BF argMachine , sep::BFCode ac ]
@init{
	sep::Machine * machine = sep::ParserUtil::getActivityMachine(argMachine);

	sep::Routine * routine = nullptr;

	std::size_t paramCount = 0;
	std::size_t returnCount = 0;
	if( machine == nullptr )
	{
		routine = nullptr;
	}
	else if( machine->getSpecifier().isDesignInstanceStatic()
			&& machine->getType().is< sep::Machine >() )
	{
		routine = &( machine->getType().to_ptr< sep::Machine >()->
			getBehavior()->getActivity( ac->getAvmOpCode() ) );
	}
	else if( ac->isnotOpCode( sep::AVM_OPCODE_INVOKE_NEW ) )
//	if( machine->isDesignPrototypeStatic() )
	{
		routine = &( machine->getBehavior()->getActivity( ac->getAvmOpCode() ) );
	}

	if( routine != nullptr )
	{
		paramCount  = routine->getPropertyPart().getVariableParametersCount();
		returnCount = routine->getPropertyPart().getVariableReturnsCount();
	}


	sep::BFVector labelledParams( paramCount );
	sep::BFList positionalParams;

	sep::BFVector labelledReturns( returnCount );
	sep::BFList positionalReturns;

	if( machine != nullptr )
	{
		PUSH_CTX_CPM( machine );
	}
}
@after{
	sep::ParserUtil::computeActivityRoutineParamReturn(argMachine, routine, $ac,
		labelledParams , positionalParams, labelledReturns, positionalReturns);

	if( machine != nullptr )
	{
		POP_CTX;
	}
}
	: LPAREN  // Parameters
	  ( lp=labelled_argument
		{
			sep::ParserUtil::appendRoutineParameters(routine, $lp.label,
					labelledParams, positionalParams, $lp.arg);
		}
	    ( COMMA
	    lp=labelled_argument
		{
			sep::ParserUtil::appendRoutineParameters(routine, $lp.label,
					labelledParams, positionalParams, $lp.arg);
		}
	    )*
	  )?
	  RPAREN

	( ( '-->' | 'returns:' )
	  ( LPAREN
	    lp=labelled_argument
		{
			sep::ParserUtil::appendRoutineReturns(routine, $lp.label,
					labelledReturns, positionalReturns, $lp.arg);
		}
	    ( COMMA
	      lp=labelled_argument
	      {
			sep::ParserUtil::appendRoutineReturns(routine, $lp.label,
					labelledReturns, positionalReturns, $lp.arg);
	      }
	    )*
	    RPAREN

	  | lp=labelled_argument
		{
			sep::ParserUtil::appendRoutineReturns(routine, $lp.label,
					labelledReturns, positionalReturns, $lp.arg);
		}
	  )
	)?

//	| 'ctx:'  LCURLY  ( sa=statement_assign { $ac->append($sa.ac); } )+  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// declaration COMMUNCATION POINT : PORT
////////////////////////////////////////////////////////////////////////////////

decl_port
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::IComPoint::ENUM_IO_NATURE nature = sep::IComPoint::IO_UNDEFINED_NATURE;
}
	: 'port'  { nature = sep::IComPoint::IO_PORT_NATURE; }
	
	  decl_port_impl[ $declPropertyPart , $mdfr, nature ]
	;

decl_port_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ,
		sep::IComPoint::ENUM_IO_NATURE nature ]
@init{
	sep::Port * port;
	sep::BF TPort;
}
	: //!g4!( ID ) =>
	  id=ID
	  {
		$declPropertyPart->appendPort( sep::BF(
				port = new sep::Port(*( $declPropertyPart ),
						$id->getText(), nature,
						$mdfr.setDirectionInoutElse() ) ) );
	  }
	  ( sl=StringLiteral
	  { port->setUnrestrictedName($sl->getText()); }
	  )?
	  ( typed_parameter_input[ &( port->getParameterPart() ) ] )?  SEMI

	| modifier_set_direction_strict_text[ &( $mdfr ) ]
	  ( id=ID
		{
			$declPropertyPart->appendPort( sep::BF(
					port = new sep::Port(*( $declPropertyPart ),
							$id->getText(), nature, $mdfr ) ) );
		}
		( sl=StringLiteral
		{ port->setUnrestrictedName($sl->getText()); }
		)?
		( typed_parameter_input[ &( port->getParameterPart() ) ] )?  SEMI

	  | LCURLY
		( id=ID
	      {
			$declPropertyPart->appendPort( sep::BF(
					port = new sep::Port(*( $declPropertyPart ),
							$id->getText(), nature, $mdfr) ) );
	      }
		  ( sl=StringLiteral
		  { port->setUnrestrictedName($sl->getText()); }
		  )?
	      ( typed_parameter_input[ &( port->getParameterPart() ) ] )?  SEMI
	 	)+
		RCURLY
	  )
	| LCURLY
	  ( //!g4!( ID ) =>
	    id=ID
		{
			$declPropertyPart->appendPort( sep::BF(
					port = new sep::Port(*( $declPropertyPart ),
							$id->getText(), nature,
							$mdfr.setDirectionInoutElse() ) ) );
			port->setModifier( $mdfr );
		}
		( sl=StringLiteral
		{ port->setUnrestrictedName($sl->getText()); }
		)?
	    ( typed_parameter_input[ &( port->getParameterPart() ) ] )?  SEMI

	  | modifier_set_direction_strict_text[ &( $mdfr ) ] id=ID
		{
			$declPropertyPart->appendPort( sep::BF(
					port = new sep::Port(*( $declPropertyPart ),
							$id->getText(), nature, $mdfr) ) );
		}
		( sl=StringLiteral
		{ port->setUnrestrictedName($sl->getText()); }
		)?
	    ( typed_parameter_input[ &( port->getParameterPart() ) ] )?  SEMI
	  )+
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// declaration COMMUNCATION POINT : MESSAGE | SIGNAL
////////////////////////////////////////////////////////////////////////////////

decl_signal
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::IComPoint::ENUM_IO_NATURE nature = sep::IComPoint::IO_UNDEFINED_NATURE;
}
	: ( 'signal'  { nature = sep::IComPoint::IO_SIGNAL_NATURE;  }
	  | 'message' { nature = sep::IComPoint::IO_MESSAGE_NATURE; }
	  )
	  decl_signal_impl[ $declPropertyPart , $mdfr, nature ]
	;

decl_signal_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ,
		sep::IComPoint::ENUM_IO_NATURE nature ]
@init{
	sep::Port * signal;
	sep::BF TPort;
}
	: //!g4!( ID ) =>
	  id=ID
	  {
		$declPropertyPart->appendSignal( sep::BF(
				signal = new sep::Signal(*( $declPropertyPart ),
						$id->getText(), nature,
						$mdfr.setDirectionInoutElse() ) ) );
	  }
	  ( sl=StringLiteral
	  { signal->setUnrestrictedName($sl->getText()); }
	  )?
	  ( typed_parameter_input[ &( signal->getParameterPart() ) ] )?  SEMI

	| modifier_set_direction_strict_text[ &( $mdfr ) ]
	  ( id=ID
		{
			$declPropertyPart->appendSignal( sep::BF(
					signal = new sep::Signal(*( $declPropertyPart ),
							$id->getText(), nature, $mdfr ) ) );
		}
	    ( sl=StringLiteral
	    { signal->setUnrestrictedName($sl->getText()); }
	    )?
		( typed_parameter_input[ &( signal->getParameterPart() ) ] )?  SEMI

	  | LCURLY
		( id=ID
	      {
			$declPropertyPart->appendSignal( sep::BF(
					signal = new sep::Signal(*( $declPropertyPart ),
							$id->getText(), nature, $mdfr) ) );
	      }
		  ( sl=StringLiteral
		  { signal->setUnrestrictedName($sl->getText()); }
		  )?
	      ( typed_parameter_input[ &( signal->getParameterPart() ) ] )?  SEMI
	 	)+
		RCURLY
	  )
	| LCURLY
	  ( //!g4!( ID ) =>
	    id=ID
		{
			$declPropertyPart->appendSignal( sep::BF(
					signal = new sep::Signal(*( $declPropertyPart ),
							$id->getText(), nature,
							$mdfr.setDirectionInoutElse() ) ) );
			signal->setModifier( $mdfr );
		}
		( sl=StringLiteral
		{ signal->setUnrestrictedName($sl->getText()); }
		)?
		( typed_parameter_input[ &( signal->getParameterPart() ) ] )?  SEMI

	  | modifier_set_direction_strict_text[ &( $mdfr ) ] id=ID
		{
			$declPropertyPart->appendSignal( sep::BF(
					signal = new sep::Signal(*( $declPropertyPart ),
							$id->getText(), nature, $mdfr) ) );
		}
		( sl=StringLiteral
		{ signal->setUnrestrictedName($sl->getText()); }
		)?
		( typed_parameter_input[ &( signal->getParameterPart() ) ] )?  SEMI
	  )+
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// declaration COMMUNCATION PARAMETER
////////////////////////////////////////////////////////////////////////////////

typed_parameter_input [ sep::PropertyPart * declParameterPart ]
@init{
	sep::avm_offset_t offset = 0;
}
	: LPAREN
		typed_parameter_atom[ declParameterPart, 
				sep::Modifier::PROPERTY_PARAMETER_MODIFIER, offset]
		( COMMA typed_parameter_atom[ declParameterPart ,
				sep::Modifier::PROPERTY_PARAMETER_MODIFIER, ++offset ] )*
	  RPAREN
	;


typed_parameter_return [ sep::PropertyPart * declParameterPart ]
@init{
	sep::avm_offset_t offset = 0;
}
	: ( LPAREN
			typed_parameter_atom[ declParameterPart, 
				sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER, offset]
			( COMMA typed_parameter_atom[ declParameterPart,
				sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER, ++offset ] )*
		RPAREN
	  | typed_parameter_atom[ declParameterPart, 
				sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER, offset]
	  )
	;


typed_parameter_atom
/* in */[ sep::PropertyPart * declParameterPart ,
			sep::Modifier mdfr , sep::avm_offset_t offset ]
@init{
	sep::Variable * variable;
	sep::BF paramT = sep::TypeManager::UNIVERSAL;
	std::string paramID;
	sep::BF value;
}
	: tv=type_var { paramT = $tv.type; }
	  ( id=ID     { paramID = $id->getText(); }
	    ( iv=initial_value  { value = $iv.bf; } )?
	  )?
	{
		variable = new sep::Variable($declParameterPart->getContainer(),
				mdfr, paramT, paramID, value);
				
		$declParameterPart->saveOwnedVariable( variable );
	}

	| 'bind:'
	  ( //!g4!( type_var COLON ) =>
	    tv=type_var COLON  { paramT = $tv.type; }
	    e=expression { value = $e.bf; }
	  | vid=qualifiedNameID
	  {
		value = sep::ParserUtil::getVariable($vid.s, $vid.nb);
		if( value.valid() )
		{ paramT = value.to_ptr< sep::Variable >()->getType(); }
	  }
	  )
	{
		paramID = sep::OSS() << '#' << offset;
		
		variable = new sep::Variable($declParameterPart->getContainer(),
				sep::Modifier::PROPERTY_PARAMETER_BIND_MODIFIER,
				paramT, paramID, value);
				
		$declParameterPart->saveOwnedVariable( variable );
				
		variable->setOwnedOffset( offset );
	}
	;

////////////////////////////////////////////////////////////////////////////////
// declaration BUFFER
////////////////////////////////////////////////////////////////////////////////

decl_buffer
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'buffer'  decl_buffer_impl[ $declPropertyPart , $mdfr ]
	;

decl_buffer_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::Buffer * buffer;

	sep::BF TBuffer;
}
	: db=def_buffer  id=ID
	{
		$declPropertyPart->appendBuffer( sep::BF(
				buffer = new sep::Buffer(*( $declPropertyPart ),
						$id->getText(), $db.kind, $db.size)) );
		buffer->setModifier( $mdfr );
	}
	  ( initial_buffer_contents[ buffer ] )?  SEMI

	| LCURLY
	  (
	    db=def_buffer  id=ID
		{
			$declPropertyPart->appendBuffer( sep::BF(
					buffer = new sep::Buffer(*( $declPropertyPart ),
							$id->getText(), $db.kind, $db.size)) );
			buffer->setModifier( $mdfr );
		}
	  )+
	  RCURLY
	;


def_buffer
returns [ sep::avm_type_specifier_kind_t kind , int size = -1 ]
	: pb=policy_buffer  { $kind = $pb.kind; }
	  ( LT_ ( 'size:' )?
	    ( n=integer_constant  { $size = $n.val; }
	    | STAR                { $size = -1; }
	    )
	    GT
	  | LBRACKET ( 'size:' )?
	    ( n=integer_constant  { $size = $n.val; }
	    | STAR                { $size = -1; }
	    )
	    RBRACKET 
	  )?
	| 'ram'  { $kind = sep::TYPE_RAM_SPECIFIER; $size = 1; }
	;


policy_buffer
returns [ sep::avm_type_specifier_kind_t kind ]
	: 'fifo'      { $kind = sep::TYPE_FIFO_SPECIFIER;           }
	| 'lifo'      { $kind = sep::TYPE_LIFO_SPECIFIER;           }
	| 'multififo' { $kind = sep::TYPE_MULTI_FIFO_SPECIFIER;     }
	| 'multilifo' { $kind = sep::TYPE_MULTI_LIFO_SPECIFIER;     }
	| 'set'       { $kind = sep::TYPE_SET_SPECIFIER;            }
	| 'bag'       { $kind = sep::TYPE_MULTISET_SPECIFIER;       }
	| 'multiset'  { $kind = sep::TYPE_MULTISET_SPECIFIER;       }
	| 'vector'    { $kind = sep::TYPE_VECTOR_SPECIFIER;         }
	| 'rvector'   { $kind = sep::TYPE_REVERSE_VECTOR_SPECIFIER; }
	;

ref_buffer[ sep::Machine * machine ]
returns [ sep::BF buf ]
	: id=qualifiedNameID
	{ $buf = sep::ParserUtil::getBuffer(machine, $id.s, $id.nb); }
	;


initial_buffer_contents[ const sep::Buffer * buffer ]
@init{
	sep::BF msg;
}
	: ASSIGN LBRACKET
	    mid=qualifiedNameID
		{/* msg = sep::ParserUtil::getMessage($mid.s, $mid.nb);
			buffer->appendMessage(msg); */}
	  ( COMMA mid=qualifiedNameID
	  )*
	  RBRACKET
	;


////////////////////////////////////////////////////////////////////////////////
// declaration CHANNEL
////////////////////////////////////////////////////////////////////////////////

decl_channel
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'channel'  decl_channel_port[ $declPropertyPart , $mdfr ]
/*	  ( //!g4!ID LCURLY  =>
        decl_channel_port[ $declPropertyPart , $mdfr ]
	  | decl_channel_var[ $declPropertyPart , $mdfr ]
	  )
*/	;


decl_channel_port
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::Channel * aChannel;

	$declPropertyPart->appendChannel( sep::BF( aChannel =
			new sep::Channel(*( $declPropertyPart ),
					"#channel#", $mdfr.setDirectionInoutElse() ) ));

}
	: ( LT_
	    com_protocol[ $declPropertyPart->getContainer()->as_ptr< sep::Machine >(),
	    			aChannel ]
	    ( COMMA com_cast[ aChannel ] )?
	    GT
	  )?

	  ( modifier_set_direction_strict_text[ &( aChannel->getwModifier() ) ] ) ?
	  id=ID  { aChannel->fullyUpdateAllNameID( $id->getText() ); }

	  LCURLY
	  (
	    m=modifier_direction  uid=qualifiedNameID SEMI
		{
			sep::BF comSignal = sep::ParserUtil::getComSignal($uid.s, $uid.nb);
			if( comSignal.valid() )
			{
				aChannel->appendSignal($m.mdfr, comSignal);
			}
		}

	  | decl_port[ &( aChannel->getParameterPart() ) ,
	  				sep::Modifier::PROPERTY_PUBLIC_MODIFIER ]
						
	  | decl_signal[ &( aChannel->getParameterPart() ) ,
					sep::Modifier::PROPERTY_PUBLIC_MODIFIER ]
	  )+
	  RCURLY
	;


decl_channel_var
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::Variable * var;
}
	: tv=type_var  id=ID
	  {
		$declPropertyPart->saveOwnedVariable( var = new sep::Variable(
				*( $declPropertyPart ), $mdfr, $tv.type, $id->getText()) );
	  }
	  ( iv=initial_value  { var->setValue($iv.bf); } )?
	  ( SEMI  |  on_write_var_routine_def[ var ] )

	| LCURLY (
	  tv=type_var  id=ID
	  {
		$declPropertyPart->saveOwnedVariable( var = new sep::Variable(
				*( $declPropertyPart) , $mdfr, $tv.type, $id->getText()) );
	  }
	  ( iv=initial_value  { var->setValue($iv.bf); } )?
	  ( SEMI  |  on_write_var_routine_def[ var ] )
	  )+  RCURLY
	;



////////////////////////////////////////////////////////////////////////////////
// declaration COMMUNCATION POINT : PORT
////////////////////////////////////////////////////////////////////////////////

decl_function
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'fun'  decl_function_impl[ $declPropertyPart , $mdfr ]
	;

decl_function_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::Function * function;
}
	: id=ID
	  {
		$declPropertyPart->appendFunction( sep::BF(
			function = new sep::Function(*( $declPropertyPart ), $id->getText()) ));
	  }
	  ( typed_parameter_input[ &( function->getParameterPart() ) ] )?
	  '->'
	  typed_parameter_return[ &( function->getParameterPart() ) ]
	  SEMI
	;



////////////////////////////////////////////////////////////////////////////////
// declaration VAR
////////////////////////////////////////////////////////////////////////////////

decl_variable
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: ( 'var'      {  $mdfr.setNatureVariable(); }
	  | 'val'      {  $mdfr.setFeatureConst();   }
	  | ( 'const'  {  $mdfr.setFeatureConst();   }
	    | 'macro'  {  $mdfr.setNatureMacro();    }
	    )+
	    ( 'var' )?
	  )
	  decl_variable_impl[ $declPropertyPart , $mdfr ]

	| decl_variable_time_clock_impl[ $declPropertyPart , $mdfr ]
	;


decl_variable_time_clock_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	$mdfr.override_ifdef( sep::Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER );
}
	: ctv=time_clock_type
	  decl_typed_variable_atom_impl[ $declPropertyPart , $mdfr , $ctv.bts ]
	;


decl_variable_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: decl_variable_atom_impl[ $declPropertyPart , $mdfr ]

	| LCURLY
	  ( decl_variable_atom_impl[ $declPropertyPart , $mdfr ] )+
	  RCURLY
	;

decl_variable_atom_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: tv=type_var  ( BAND  { mdfr.setNatureReference(); } )?
	  decl_typed_variable_atom_impl[ $declPropertyPart , $mdfr , $tv.type ]
	;

decl_typed_variable_atom_impl
/* in */[ sep::PropertyPart * declPropertyPart ,
		sep::Modifier mdfr , sep::BF type ]
@init{
	sep::Variable * var;
}
	: id=ID
	  {
		$declPropertyPart->saveOwnedVariable( var = new sep::Variable(
				*( $declPropertyPart ), $mdfr, type, $id->getText()) );
	  }

	  ( sl=StringLiteral { var->setUnrestrictedName($sl->getText()); } )?

	  ( iv=initial_value  { var->setValue($iv.bf); } )?
	  ( SEMI  |  on_write_var_routine_def[ var ] )
	;


initial_value
returns [ sep::BF bf ]
	: ASSIGN  e=expression          { $bf = $e.bf; }
	| LPAREN  e=expression  RPAREN  { $bf = $e.bf; }
	;


type_var
returns [ sep::BF type ]
	: btv=base_type_var                  { $type = $btv.type; }
	  ( dta=def_type_array[ $type , "" ] { $type = $dta.type; } )?

	| dtc=def_type_container[ "" ]       { $type = $dtc.type; }

	| dti=def_type_interval [ "" ]       { $type = $dti.type; }
	;


def_type_array
/* in */[ sep::BF baseT , std::string tid ]
returns [ sep::BF type ]
@init{
	sep::ListOfInt listOfSize;
}
	: ( dta=def_type_array_size  { listOfSize.push_back($dta.size); } )+
	{
		int szT = listOfSize.front();
		listOfSize.pop_front();

		while( listOfSize.nonempty() )
		{
			baseT = sep::BF( sep::DataType::newContainer(_CPM_,
					sep::DataType::strContainerId(sep::TYPE_ARRAY_SPECIFIER,
							baseT, listOfSize.back()),
					sep::TYPE_ARRAY_SPECIFIER, baseT, listOfSize.back()) );
			listOfSize.pop_back();
		}
		$type = sep::BF( sep::DataType::newContainer(_CPM_,
				sep::DataType::strContainerId(
						tid, sep::TYPE_ARRAY_SPECIFIER, baseT, szT),
				sep::TYPE_ARRAY_SPECIFIER, baseT, szT) );
	}
	;

def_type_array_size
returns [ int size ]
	: LBRACKET
	    ( sz=IntegerLiteral    { $size = NUM_INT($sz->getText()); }
//	    ( sz=integer_constant  { $size = $sz.val; }

		| id=qualifiedNameID
		{
			const sep::BF & constVar =
					sep::ParserUtil::getConstant($id.s, $id.nb);
			if( constVar.valid() &&
				constVar.to_ptr< sep::Variable >()->hasValue() &&
				constVar.to_ptr< sep::Variable >()->getValue().isInteger() )
			{
				$size = constVar.to_ptr< sep::Variable >()->getValue().toInteger();
			}
			else
			{
				sep::BF aType = sep::ParserUtil::getDataType($id.s, $id.nb);

				if( aType.valid() && aType.is< sep::DataType >() )
				{
					if( aType.to_ptr< sep::DataType >()->isTypedInterval() )
					{
						$size = aType.to_ptr< sep::DataType >()->getIntervalLength();

						if( $size < 0 )
						{
							sep::ParserUtil::avm_syntax_error(
								"def_type_array_size(...)" )
									<< "unexpected << interval: " << $id.s
									<< " >> as size (i.e. " << $size
									<< ") in an array typedef"
									<< sep::ParserUtil::SYNTAX_ERROR_EOL;

							$size = 0;
						}
					}
					else if( aType.to_ptr< sep::DataType >()->isTypedEnum() )
					{
						$size = aType.to_ptr< sep::DataType >()->getEnumSize();

						if( $size == 0 )
						{
							sep::ParserUtil::avm_syntax_error(
								"def_type_array_size(...)" )
									<< "unexpected << enum: " << $id.s
									<< " >> as size in an array typedef"
									<< sep::ParserUtil::SYNTAX_ERROR_EOL;
						}
					}
					else
					{
						$size = 0;

						sep::ParserUtil::avm_syntax_error(
							"def_type_array_size(...)" )
								<< "unexpected << [Qualified]NameID: " << $id.s
								<< " >> as size in an array typedef"
								<< sep::ParserUtil::SYNTAX_ERROR_EOL;
					}
				}
				else
				{
					$size = 0;

					sep::ParserUtil::avm_syntax_error(
						"def_type_array_size(...)" )
							<< "unexpected << [Qualified]NameID: " << $id.s
							<< " >> as size in an array typedef"
							<< sep::ParserUtil::SYNTAX_ERROR_EOL;
				}
			}
		}
		)
	  RBRACKET
	;


def_type_container [ std::string tid ]
returns [ sep::BF type ]
@init{
	sep::BF baseT = sep::TypeManager::UNIVERSAL;
	int szT = -1;
}
 	: sb=specifier_buffer
 	  ( LT_
	    ( ( btv=base_type_var  { baseT = $btv.type; }
	        ( COMMA  ( 'size:' )?
	          ( sz=integer_constant { szT = $sz.val; }
	          | STAR                { szT = -1; }
	          )
	        )?
	      )
	    | ( 'size:' )? sz=integer_constant  { szT = $sz.val; }
	    )
	    GT
	  )?
	{
		$type = sep::BF( sep::DataType::newContainer(_CPM_,
				sep::DataType::strContainerId(tid, $sb.kind, baseT, szT),
				$sb.kind, baseT, szT) );
	}
	;


specifier_buffer
returns [ sep::avm_type_specifier_kind_t kind ]
	: 'array'     { $kind = sep::TYPE_ARRAY_SPECIFIER;          }
	| 'vector'    { $kind = sep::TYPE_VECTOR_SPECIFIER;         }
	| 'rvector'   { $kind = sep::TYPE_REVERSE_VECTOR_SPECIFIER; }
	| 'list'      { $kind = sep::TYPE_LIST_SPECIFIER;           }
	| 'fifo'      { $kind = sep::TYPE_FIFO_SPECIFIER;           }
	| 'lifo'      { $kind = sep::TYPE_LIFO_SPECIFIER;           }
	| 'multififo' { $kind = sep::TYPE_MULTI_FIFO_SPECIFIER;     }
	| 'multilifo' { $kind = sep::TYPE_MULTI_LIFO_SPECIFIER;     }
	| 'set'       { $kind = sep::TYPE_SET_SPECIFIER;            }
	| 'bag'       { $kind = sep::TYPE_MULTISET_SPECIFIER;       }
	| 'multiset'  { $kind = sep::TYPE_MULTISET_SPECIFIER;       }
	;


def_type_interval [ std::string tid ]
returns [ sep::BF type ]
@init{
	sep::BF baseT = sep::TypeManager::INTEGER;
}
	: 'interval'  { $type = sep::TypeManager::INTEGER; }
	  LT_
	    ( pt=primitive_type { baseT = $pt.bts; } )?
	    (ll=LBRACKET | ll=RBRACKET | ll=LPAREN)
	    min=expression COMMA  max=expression
	    (rr=LBRACKET | rr=RBRACKET | rr=RPAREN)
	  GT
	{
		$type = sep::BF( sep::DataType::newInterval(_CPM_, tid, baseT,
			sep::IIntervalKind::computeKind(
				$ll->getText().at(0), $rr->getText().at(0)),
			$min.bf, $max.bf) );
	}
	;


base_type_var
returns [ sep::BF type ]
	: pt=primitive_type
	{ $type = $pt.bts; }
	| id=qualifiedNameID
	{ $type = sep::ParserUtil::getDataType($id.s, $id.nb); }
	;


primitive_type
returns [ sep::TypeSpecifier bts ]
	: ( 'boolean' | 'bool' ) { $bts = sep::TypeManager::BOOLEAN; }

	| ( 'integer' | 'int' )  { $bts = sep::TypeManager::INTEGER; }
	  ( bfs=bit_field_size
		{ $bts = sep::TypeManager::getTypeInteger( $bfs.size ); }
	  )?

	| ( 'uinteger' | 'uint' )  { $bts = sep::TypeManager::UINTEGER; }
	  ( bfs=bit_field_size
	  { $bts = sep::TypeManager::getTypeUInteger( $bfs.size ); }
	  )?

	| ( 'pos_integer' | 'pos_int' )  { $bts = sep::TypeManager::POS_INTEGER; }
	  ( bfs=bit_field_size
	  { $bts = sep::TypeManager::getTypePosInteger( $bfs.size ); }
	  )?


	| ( ( 'rational'  | 'rat'  )  { $bts = sep::TypeManager::RATIONAL; }
	  | ( 'urational' | 'urat' )  { $bts = sep::TypeManager::URATIONAL; }
	  
	  | ( 'pos_rational' | 'pos_rat' )
		{ $bts = sep::TypeManager::POS_RATIONAL; }

	  | 'float'    { $bts = sep::TypeManager::FLOAT; }
	  | 'ufloat'   { $bts = sep::TypeManager::UFLOAT; }

	  | 'double'   { $bts = sep::TypeManager::DOUBLE; }
	  | 'udouble'  { $bts = sep::TypeManager::UDOUBLE; }

	  | 'real'     { $bts = sep::TypeManager::REAL; }
	  | 'ureal'    { $bts = sep::TypeManager::UREAL; }
	  )
	  ( bfs=bit_field_size
	  {
		$bts = sep::TypeManager::newNumericTypeSpecifier(
				$bts, $bfs.size, sep::ExpressionConstant::INTEGER_ZERO);
	  }
	  )?


	| ct=time_clock_type { $bts = $ct.bts; }

	| tt=time_type { $bts = $tt.bts; }

	| 'char'    { $bts = sep::TypeManager::CHAR; }
	  ( bfs=bit_field_size
	  { $bts = sep::TypeManager::newCharacter( "char", $bfs.size ); }
	  )?

	| 'character'    { $bts = sep::TypeManager::CHARACTER; }
	  ( bfs=bit_field_size
	  { $bts = sep::TypeManager::newCharacter( "character", $bfs.size ); }
	  )?

	| 'string'  { $bts = sep::TypeManager::STRING; }
	  ( sfs=string_field_size
	  { $bts = sep::TypeManager::newString( $sfs.min , $sfs.max ); }
	  )?


	| 'operator'   { $bts = sep::TypeManager::OPERATOR;   }
	| 'avmcode'    { $bts = sep::TypeManager::AVMCODE;    }

	| 'port'       { $bts = sep::TypeManager::PORT;       }
	| 'buffer'     { $bts = sep::TypeManager::BUFFER;     }
	| 'message'    { $bts = sep::TypeManager::MESSAGE;    }
	| 'signal'     { $bts = sep::TypeManager::SIGNAL;     }
	| 'connector'  { $bts = sep::TypeManager::CONNECTOR; }

	| 'machine'    { $bts = sep::TypeManager::MACHINE;    }
	  ( LT_  id=qualifiedNameID  GT
	  {
		sep::BF machineT =
				sep::ParserUtil::getExecutableMachine($id.s, $id.nb);
	  }
	  )?

	| 'universal'  { $bts = sep::TypeManager::UNIVERSAL; }
	;


bit_field_size
returns [ int size ]
	: COLON  n=integer_constant                  { $size = $n.val; }
	| LT_  ( 'size:' )?  n=integer_constant  GT  { $size = $n.val; }
	;


string_field_size
returns [ int min=0 , int max=-1 ]
	: COLON rc=range_constant
	  { $min = $rc.min; $max = $rc.max; }

	| LT_  ( 'size:' )?  rc=range_constant  GT
	  { $min = $rc.min; $max = $rc.max; }
	;

range_constant
returns [ int min=0 , int max=-1 ]
	: n=integer_constant    { $max = $n.val; }
	  ( ( COMMA | DOTDOT )
	    n=integer_constant  { $min = $max; $max = $n.val; }
	  )?
	;

on_write_var_routine_def [ sep::Variable * var ]
	: LCURLY  ( var_routine_def[ var ] )+ RCURLY
	;


var_routine_def [ sep::Variable * var ]
@init{
	sep::Routine * onWriteRoutine = nullptr;

	sep::BehavioralPart * aBehavioralpart = var->getUniqContainerOfRoutines();

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION( onWriteRoutine );
}
	: ( '@write' | '@on_write' )
	  {
		onWriteRoutine = new sep::Routine(var, "on_write");
		var->setOnWriteRoutine(onWriteRoutine);
		if( aBehavioralpart != nullptr )
		{
			aBehavioralpart->saveAnonymousInnerRoutine(onWriteRoutine);
		}
	  }
	  ( routine_single_param[onWriteRoutine, var->getType()] )?
	  ( bs=block_statement  { onWriteRoutine->setCode($bs.ac); }
	  | '|=>' ce=conditionalExpression SEMI
	  { onWriteRoutine->setCode( NEW_STMT1(OP(GUARD), $ce.bf) ); }
	  )
	;

routine_single_param
/* in */[ sep::Routine * routine , sep::BF dftType ]
@init{
	sep::BF paramT = dftType;
	sep::BF value;
}
	: LPAREN
	  ( //!g4!( type_var ID ) =>
	    tv=type_var { paramT = $tv.type; }  id=ID
	  | id=ID
	  )
	  ( iv=initial_value  { value = $iv.bf; } )?
	  {
		sep::Variable * variable = new sep::Variable( routine,
				sep::Modifier::PROPERTY_INPUT_PARAMETER_MODIFIER,
				paramT, $id->getText(), value );
				
		routine->getPropertyPart().saveOwnedVariableParameter( variable );
	  }
	  RPAREN
	;


def_enum
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::BF superEnumType;
}
	: 'enum'  id=ID
		def_enum_impl[$declPropertyPart, $mdfr, $id->getText()]
	;

def_enum_impl
/* in */[ sep::PropertyPart * declPropertyPart ,
		sep::Modifier mdfr , std::string tid ]
@init{
	sep::Variable * var = nullptr;
	sep::DataType * enumT;

	const sep::DataType * superEnumDataType = nullptr;
}
	: LCURLY
		id=ID
		{
			
			sep::BF td( enumT = sep::DataType::newEnum(*( $declPropertyPart ), tid) );
			enumT->setModifier( $mdfr );
			$declPropertyPart->appendDataType( td );

			enumT->saveVariable( var = new sep::Variable( enumT,
					sep::Modifier::PROPERTY_UNDEFINED_MODIFIER,
					sep::TypeManager::INTEGER, $id->getText() ) );
		}
		( sl=StringLiteral { var->setUnrestrictedName($sl->getText()); } )?
		( ASSIGN e=expression  { var->setValue($e.bf); } )?
		
		( COMMA id=ID
		{
			enumT->saveVariable( var = new sep::Variable( enumT,
					sep::Modifier::PROPERTY_UNDEFINED_MODIFIER,
					sep::TypeManager::INTEGER, $id->getText() ) );
		}
		( sl=StringLiteral { var->setUnrestrictedName($sl->getText()); } )?
		( ASSIGN e=expression  { var->setValue($e.bf); } )?
		)*
//!@! TODO#ADD
//	    ( COMMA )?

	  RCURLY
	  
	| LT_ ( 'super:' )?  superId=ID  
	  	{
	  		const sep::BF & superEnumType =
	  				declPropertyPart->getSemEnumDataType($superId->getText());
			if( superEnumType.valid() )
			{
				superEnumDataType = superEnumType.to_ptr< sep::DataType >();
			}
			else
			{
				sep::ParserUtil::avm_syntax_error("def_sub_enum_impl:> "
					"with super enum ID: " + superEnumType.str() , $superId.line)
							<< "Unfound super enum datatype specifier !"
							<< sep::ParserUtil::SYNTAX_ERROR_EOL;
			}
			
			sep::BF td( enumT = sep::DataType::newEnum(
					*( $declPropertyPart ), tid, superEnumType) );
			enumT->setModifier( $mdfr );
			$declPropertyPart->appendDataType( td );
	  	}
	  	GT
	  	
	  LCURLY
	    id=ID
		{
			if( superEnumDataType != nullptr )
			{
				const sep::BF & foundSymbol =
						superEnumDataType->getEnumSymbol( $id->getText() );
			
				if( foundSymbol.valid() )
				{
					enumT->appendVariable(foundSymbol);
				}
				else
				{
					sep::ParserUtil::avm_syntax_error("def_sub_enum_impl:> "
						"enum symbol alias ID: " + $id->getText(), $id.line )
								<< "Unfound enum symbol in super enum datatype: "
								<< superEnumDataType->toString()
								<< sep::ParserUtil::SYNTAX_ERROR_EOL;
				}
			}
		}

	    ( COMMA id=ID
		{
			if( superEnumDataType != nullptr )
			{
				const sep::BF & foundSymbol =
						superEnumDataType->getEnumSymbol( $id->getText() );
			
				if( foundSymbol.valid() )
				{
					enumT->appendVariable(foundSymbol);
				}
				else
				{
					sep::ParserUtil::avm_syntax_error("def_sub_enum_impl:> "
						"enum symbol alias ID: " + $id->getText(), $id.line )
								<< "Unfound enum symbol in super enum datatype: "
								<< superEnumDataType->toString()
								<< sep::ParserUtil::SYNTAX_ERROR_EOL;
				}
			}
		}
	    )*
//!@! TODO#ADD
//	    ( COMMA )?

	  RCURLY
	;


def_struct
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: ( 'struct' | 'class' )  id=ID
	  def_class_structure_impl[$declPropertyPart, $mdfr, $id->getText()]
	;

def_class_structure_impl
/* in */[ sep::PropertyPart * declPropertyPart ,
		sep::Modifier mdfr , std::string tid ]
@init{
	sep::DataType * structT;

	sep::BF td( structT = sep::DataType::newStructure(*( $declPropertyPart ), tid) );
	structT->setModifier( $mdfr );
	$declPropertyPart->appendDataType( td );
}
	: LCURLY
		( { $mdfr = sep::Modifier::PROPERTY_UNDEFINED_MODIFIER; }

			( m=modifier_declaration  { $mdfr = $m.mdfr; } )?

		    decl_variable[ structT->getPropertyPart() , $mdfr ]
	    )+
	  RCURLY
	;


def_choice
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'choice'  id=ID
	  def_choice_impl[declPropertyPart, $mdfr, $id->getText()]
	;

def_choice_impl
/* in */[ sep::PropertyPart * declPropertyPart ,
		sep::Modifier mdfr , std::string tid ]
@init{
	sep::DataType * choiceT;

	sep::BF td( choiceT = sep::DataType::newChoice(*( $declPropertyPart ), tid) );
	choiceT->setModifier( $mdfr );
	$declPropertyPart->appendDataType( td );
}
	: LCURLY
		( { $mdfr = sep::Modifier::PROPERTY_UNDEFINED_MODIFIER; }

			( m=modifier_declaration  { $mdfr = $m.mdfr; } )?

		    decl_variable[ choiceT->getPropertyPart() , $mdfr ]
	    )+
	  RCURLY
	;


def_union
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'union'  id=ID
	  def_union_impl[$declPropertyPart , $mdfr, $id->getText()]
	;


def_union_impl
/* in */[ sep::PropertyPart * declPropertyPart ,
		sep::Modifier mdfr , std::string tid ]
@init{
	sep::DataType * unionT;

	sep::BF td(	unionT = sep::DataType::newUnion(*( $declPropertyPart ), tid) );
	unionT->setModifier( $mdfr );
	$declPropertyPart->appendDataType( td );
}
	: LCURLY
		( {$mdfr = sep::Modifier::PROPERTY_UNDEFINED_MODIFIER; }

			( m=modifier_declaration  { $mdfr = $m.mdfr; } )?

		    decl_variable[ unionT->getPropertyPart() , $mdfr ]
	    )+
	  RCURLY
	;


def_type
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'type'  def_type_impl[ $declPropertyPart , $mdfr ]
	;

def_type_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: def_type_atom_impl[ $declPropertyPart , $mdfr ]

	| LCURLY
	  ( def_type_atom_impl[ $declPropertyPart , $mdfr ] )+
	  RCURLY
	;


def_type_atom_impl
/* in */[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
@init{
	sep::DataType * aliasT;
	sep::BF type;
	bool isTypedArray = false;
}
	: id=ID
	  ( btv=base_type_var   { type = $btv.type; }
	    ( dta=def_type_array[ type , $id->getText() ]
	      { type = $dta.type; isTypedArray = true; }
	    )?
		{
			if( isTypedArray )
			{
				aliasT = type.to_ptr< sep::DataType >();
				aliasT->setModifier( $mdfr );
				$declPropertyPart->appendDataType( type );
			}
			else
			{
				sep::BF td( aliasT = sep::DataType::newAlias(
					*( $declPropertyPart ), $id->getText(), type) );
				aliasT->setModifier( $mdfr  );
				$declPropertyPart->appendDataType( td );
			}
		}
        ( def_typedef_constraint[ aliasT ] | SEMI )?

	  | dtc=def_type_container[ $id->getText() ]
	  {
	    aliasT = $dtc.type.to_ptr< sep::DataType >();
		aliasT->setModifier( $mdfr );
		$declPropertyPart->appendDataType( $dtc.type );
	  }
	  ( def_typedef_constraint[ aliasT ] | SEMI )?

	  | dti=def_type_interval[ $id->getText() ] SEMI
	  {
	    aliasT = $dti.type.to_ptr< sep::DataType >();
		aliasT->setModifier( $mdfr );
		$declPropertyPart->appendDataType( $dti.type );
	  }

	  | 'enum'
	    def_enum_impl[$declPropertyPart, $mdfr, $id->getText()]

	  | 'union'
	    def_union_impl[$declPropertyPart, $mdfr, $id->getText()]

	  | 'choice'
	    def_choice_impl[$declPropertyPart, $mdfr, $id->getText()]

	  | ( 'struct' | 'class' )
	    def_class_structure_impl[$declPropertyPart, $mdfr, $id->getText()]
	  )

	| def_enum  [ $declPropertyPart , $mdfr ]
	| def_union [ $declPropertyPart , $mdfr ]
	| def_choice[ $declPropertyPart , $mdfr ]
	| def_struct[ $declPropertyPart , $mdfr ]
	;


def_typedef_constraint[ sep::DataType * aliasT ]
@init{
	sep::Routine * onConstraintRoutine = nullptr;

	sep::BehavioralPart * aBehavioralpart = aliasT->getUniqBehaviorPart();

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION( onConstraintRoutine );
}
	: LCURLY
		'@constraint'
		{
			onConstraintRoutine = new sep::Routine(aliasT, "constraint");
			aliasT->setConstraintRoutine(onConstraintRoutine);
			aBehavioralpart->saveAnonymousInnerRoutine(onConstraintRoutine);
		}
	    ( routine_single_param[onConstraintRoutine, aliasT->getTypeSpecifier()] )?
	    ( bs=block_statement  { onConstraintRoutine->setCode( $bs.ac ); }
	    | '|=>' ce=conditionalExpression SEMI
	      { onConstraintRoutine->setCode( NEW_STMT1(OP(GUARD), $ce.bf) ); }
	    )
	  RCURLY
	;


////////////////////////////////////////////////////////////////////////////////
// TYPEDEF TIME
////////////////////////////////////////////////////////////////////////////////

time_type
returns [ sep::TypeSpecifier bts ]
@init{
	int szT = 1;
	sep::avm_type_specifier_kind_t tsk = sep::TYPE_TIME_SPECIFIER;
}
	: ( 'time'             { $bts = sep::TypeManager::TIME;            }
	
		| 'ctime'          { $bts = sep::TypeManager::CONTINUOUS_TIME; }
		| 'time#continous' { $bts = sep::TypeManager::CONTINUOUS_TIME; }
		
		| 'time#dense'     { $bts = sep::TypeManager::DENSE_TIME;      }
		
		| 'dtime'          { $bts = sep::TypeManager::DISCRETE_TIME;   }
		| 'time#discrete'  { $bts = sep::TypeManager::DISCRETE_TIME;   }
	  )
	  ( LT_      { tsk = $bts.getTypeSpecifierKind(); }
	    pt=time_type_domain           { $bts = $pt.type; }
	    ( COMMA  sz=integer_constant  { szT = $sz.val; } )?
	   GT
	   { $bts = sep::TypeManager::newClockTime(tsk, $bts, szT); }

	  | pt=time_type_domain
	  { $bts = sep::TypeManager::newClockTime(tsk, $pt.type, szT); }
	  )?
	;


time_clock_type
returns [ sep::TypeSpecifier bts ]
@init{
	int szT = 1;
}
	: 'clock'  { $bts = sep::TypeManager::CLOCK;    }
	  ( LT_
		( 'time'           { $bts = sep::TypeManager::TIME;            }
		
		| 'ctime'          { $bts = sep::TypeManager::CONTINUOUS_TIME; }
		| 'time#continous' { $bts = sep::TypeManager::CONTINUOUS_TIME; }
		
		| 'time#dense'     { $bts = sep::TypeManager::DENSE_TIME;      }
		
		| 'dtime'          { $bts = sep::TypeManager::DISCRETE_TIME;   }
		| 'time#discrete'  { $bts = sep::TypeManager::DISCRETE_TIME;   }
		
		| pt=time_type_domain { $bts = $pt.type;   }
		)
		( COMMA  sz=integer_constant  { szT = $sz.val; } )?
	   GT
	   { $bts = sep::TypeManager::newClockTime(sep::TYPE_CLOCK_SPECIFIER, $bts, szT); }

	  | ( 'time'           { $bts = sep::TypeManager::TIME;            }
	  
		| 'ctime'          { $bts = sep::TypeManager::CONTINUOUS_TIME; }
		| 'time#continous' { $bts = sep::TypeManager::CONTINUOUS_TIME; }
		
		| 'time#dense'     { $bts = sep::TypeManager::DENSE_TIME;      }
		
		| 'dtime'          { $bts = sep::TypeManager::DISCRETE_TIME;   }
		| 'time#discrete'  { $bts = sep::TypeManager::DISCRETE_TIME;   }
		
		| pt=time_type_domain { $bts = $pt.type;   }
		)
		( COMMA  sz=integer_constant  { szT = $sz.val; } )?
	   { $bts = sep::TypeManager::newClockTime(sep::TYPE_CLOCK_SPECIFIER, $bts, szT); }
	  )?
	;


time_type_domain
returns [ sep::TypeSpecifier type ]
	: ( 'integer'  |  'int' )  { $type = sep::TypeManager::INTEGER; }
	  ( LT_
	    n=integer_constant
		{ $type = sep::TypeManager::getTypeInteger( $n.val ); }
	   GT )?

	| ( 'uinteger'  |  'uint' )  { $type = sep::TypeManager::UINTEGER; }
	  ( LT_
	    n=integer_constant
		{ $type = sep::TypeManager::getTypeUInteger( $n.val); }
	   GT )?

	| ( 'rational'     | 'rat'     ) { $type = sep::TypeManager::RATIONAL;     }
	| ( 'urational'    | 'urat'    ) { $type = sep::TypeManager::URATIONAL;    }
	  
	| ( 'pos_rational' | 'pos_rat' ) { $type = sep::TypeManager::POS_RATIONAL; }

	| 'float'      { $type = sep::TypeManager::FLOAT; }
	| 'ufloat'     { $type = sep::TypeManager::UFLOAT; }

	| 'double'     { $type = sep::TypeManager::DOUBLE; }
	| 'udouble'    { $type = sep::TypeManager::UDOUBLE; }

	| 'real'       { $type = sep::TypeManager::REAL; }
	| 'ureal'      { $type = sep::TypeManager::UREAL; }
	;


////////////////////////////////////////////////////////////////////////////////
// declaration PROCEDURE , LAMBDA
////////////////////////////////////////////////////////////////////////////////
/*
decl_procedure
/* in /[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'proc'  ID decl_call_param
	  block_statement
	;

decl_lambda
/* in /[ sep::PropertyPart * declPropertyPart , sep::Modifier mdfr ]
	: 'lambda'  ID
	  COLON   decl_call_param
	  '-->'   decl_ret_value
	  block_statement
	;


decl_call_param
	: decl_call_one_param  ( COMMA decl_call_one_param )*
	;

decl_call_one_param
	: param_modifier ?  type_var  ID
	;

param_modifier
	: 'in' | 'ref' | 'out'
	;

decl_ret_value
	: type_var ( ID )?  ( COMMA type_var ( ID )? )*
	;


decl_one_ret_value
	: type_var  ( ID )?
	;
*/


////////////////////////////////////////////////////////////////////////////////
// section MOC
////////////////////////////////////////////////////////////////////////////////

section_model_of_computation [ sep::Machine * container ]
	: '@moc:'
	;


////////////////////////////////////////////////////////////////////////////////
// section ROUTINE & MACRO
////////////////////////////////////////////////////////////////////////////////

section_routine [ sep::Machine * container ]
@init{
	sep::Modifier mdfr;

	sep::Specifier spcfr( sep::Specifier::DESIGN_MODEL_KIND );
}
	: ( '@routine:'
	  | '@macro:'  { mdfr.setNatureMacro(); }
	  )
	  ( def_routine_model[ $container , mdfr , spcfr ] )*
	;

def_routine_model
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
	: ('routine'
	  | 'macro'   { $mdfr.setNatureMacro(); }
	    ( 'routine' ) ?
	  )
	  def_routine_model_impl[ $container , $mdfr , $spcfr ]
	;


def_routine_model_impl
/* in */[ sep::Machine * container ,
		sep::Modifier mdfr , sep::Specifier spcfr ]
@init{
	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION( _CPR_ );

	POP_CTX;
}
	: ID
	  {
		PUSH_CTX_CPR( sep::Routine::newDefine(
				$container, $mdfr, $spcfr, $ID->getText()) );

		$container->saveOwnedElement( _CPR_ );
	  }

	  ( def_routine_parameters[ _CPR_ ] )?
	  ( ( '-->' | 'returns:' )  def_routine_returns[ _CPR_ ] )?

	  bs=block_statement  { _CPR_->setCode($bs.ac); }
	;


def_routine_parameters [ sep::Routine * routine ]
@init{
	std::size_t offset = 0;
}
	: LPAREN
	     ( def_routine_param_atom[ routine , offset++ ]

	     ( COMMA def_routine_param_atom[ routine , offset++ ] )* )?
	  RPAREN
	;

def_routine_param_atom
/* in */[ sep::Routine * routine , std::size_t offset ]
@init{
	sep::BF variable;
	sep::Variable * param;
	sep::Machine * machine = routine->getContainerMachine();
	sep::BF paramT = sep::TypeManager::UNIVERSAL;
	sep::Modifier mdfr = sep::Modifier::PROPERTY_PARAMETER_MODIFIER;
	mdfr.addFeatureKind( sep::Modifier::FEATURE_TRANSIENT_KIND );
}
	: ( //!g4!( modifier_param ? type_var ID ) =>
	    ( m=modifier_param { mdfr.override_ifdef( $m.mdfr ); } )?
	    tv=type_var { paramT = $tv.type; }  id=ID

	  | id=ID
		{
			variable = sep::ParserUtil::getVariable($id->getText() , 1);
			if( variable.invalid() )
			{
				sep::ParserUtil::avm_syntax_error(
					"def_routine_param_atom:> " + routine->str(), $id.line )
						<< "Unfound machine param's variable < "
						<< $id->getText()
						<< " > in routine header < " << " >"
						<< sep::ParserUtil::SYNTAX_ERROR_EOL;
			}
		}
	  )
	  {
	    if( variable.valid() )
		{
			param = new sep::Variable( routine,
					sep::Modifier::PROPERTY_PARAMETER_MACRO_MODIFIER,
					variable.to_ptr< sep::Variable >()->getType(),
					$id->getText());
					
			routine->getPropertyPart().saveOwnedVariableParameter( param );
					
			param->setOwnedOffset( offset );
			param->setBinding( variable );
		}
	    else
		{
			param = new sep::Variable(routine, mdfr, $tv.type, $id->getText());
			param->setOwnedOffset( offset );

			// Only for Routine design as PROTOTYPE a.k.a. primitive routine
			if( routine->getSpecifier().isDesignPrototypeStatic() )
			{
				routine->getPropertyPart().appendVariableParameter(
					machine->getPropertyPart().saveOwnedVariable( param ) );
			}
			else
			{
				routine->getPropertyPart().saveOwnedVariableParameter( param );
			}
		}
	  }
	  ( iv=initial_value  { param->setValue($iv.bf); } )?
	;


def_routine_returns [ sep::Routine * routine ]
@init{
	sep::BF value;
	std::size_t offset = 0;
}
	: LPAREN
	     def_routine_returns_atom[ routine , offset++ ]

	     ( COMMA def_routine_returns_atom[ routine , offset++ ] )*
	  RPAREN

	| tv=type_var ( iv=initial_value  { value = $iv.bf; } )?
	{
		sep::Variable * variable = new sep::Variable( routine,
				sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER,
				$tv.type, "#0", value );
				
		routine->getPropertyPart().saveOwnedVariableReturn( variable );
				
		variable->setOwnedOffset( offset );
	}
	;


def_routine_returns_atom
/* in */[ sep::Routine * routine , std::size_t offset ]
@init{
	sep::BF variable;
	sep::Variable * param;
	sep::Machine * machine = routine->getContainerMachine();
	sep::BF paramT = sep::TypeManager::UNIVERSAL;
	sep::Modifier mdfr = sep::Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER;
}
	: ( //!g4!( modifier_param ? type_var ID ) =>
	    ( m=modifier_param { mdfr.override_ifdef( $m.mdfr ); } )?
	    tv=type_var { paramT = $tv.type; }  id=ID

	  | id=ID
		{
			variable = sep::ParserUtil::getVariable($id->getText() , 1);
			if( variable.invalid() )
			{
				sep::ParserUtil::avm_syntax_error(
					"def_routine_returns_atom:> " + routine->str(), $id.line )
						<< "Unfound machine return's variable < "
						<< $id->getText()
						<< " > in routine header < " << " >"
						<< sep::ParserUtil::SYNTAX_ERROR_EOL;
			}
		}
	  )

	  {
	    if( variable.valid() )
		{
			param = new sep::Variable( routine,
					sep::Modifier::PROPERTY_RETURN_PARAMETER_MACRO_MODIFIER,
					variable.to_ptr< sep::Variable >()->getType(),
					$id->getText());
					
			routine->getPropertyPart().saveOwnedVariableReturn( param );

			param->setOwnedOffset( offset );
			param->setBinding( variable );
		}
	    else
		{
			param = new sep::Variable(routine, mdfr, $tv.type, $id->getText());
			param->setOwnedOffset( offset );

			// Only for Routine design as PROTOTYPE a.k.a. primitive routine
			if( routine->getSpecifier().isDesignPrototypeStatic() )
			{
				routine->getPropertyPart().appendVariableReturn(
					machine->getPropertyPart().saveOwnedVariable( param ));
			}
			else
			{
				routine->getPropertyPart().saveOwnedVariableReturn( param );
			}
		}
	  }

	  ( iv=initial_value  { param->setValue($iv.bf); } )?
	;


////////////////////////////////////////////////////////////////////////////////
// section MOE
////////////////////////////////////////////////////////////////////////////////

section_model_of_execution [ sep::Machine * container ]
	: '@moe:'  ( def_moe_primitive[ $container ] )*
	;

def_moe_primitive [ sep::Machine * container ]
@init{
	sep::BehavioralPart * theBehavior = $container->getUniqBehaviorPart();

	sep::Modifier mdfr;

	sep::Specifier spcfr( sep::Specifier::DESIGN_MODEL_KIND );
}
	: '@create'       def_routine_seq[ &( theBehavior->getOnCreateRoutine()   ) ]
	| '@init'         def_routine_seq[ &( theBehavior->getOnInitRoutine()     ) ]
	| '@final'        def_routine_seq[ &( theBehavior->getOnFinalRoutine()    ) ]

	| '@start'        def_routine_seq[ &( theBehavior->getOnStartRoutine()    ) ]
	| '@stop'         def_routine_seq[ &( theBehavior->getOnStopRoutine()     ) ]

	| '@ienable'      def_routine_seq[ &( theBehavior->getOnIEnableRoutine()  ) ]
	| '@enable'       def_routine_seq[ &( theBehavior->getOnEnableRoutine()   ) ]

	| '@idisable'     def_routine_seq[ &( theBehavior->getOnIDisableRoutine() ) ]
	| '@disable'      def_routine_seq[ &( theBehavior->getOnDisableRoutine()  ) ]

	| '@iabort'       def_routine_seq[ &( theBehavior->getOnIAbortRoutine()   ) ]
	| '@abort'        def_routine_seq[ &( theBehavior->getOnAbortRoutine()    ) ]

	| '@irun'         def_routine_seq[ &( theBehavior->getOnIRunRoutine()     ) ]
	| '@run'          def_routine_seq[ &( theBehavior->getOnRunRoutine()      ) ]
	| '@rtc'          def_routine_seq[ &( theBehavior->getOnRtcRoutine()      ) ]

	| '@return'       def_routine_seq[ &( theBehavior->getOnFinalRoutine()    ) ]

	| '@concurrency'  def_routine_seq[ &( theBehavior->getOnConcurrencyRoutine() ) ]
	| '@schedule'     def_routine_seq[ &( theBehavior->getOnScheduleRoutine() ) ]
	
	| '@xschedule'    { theBehavior->setUserDefinedSchedule(); 
						$container->getwSpecifier().setFeatureUserDefinedSchedule(); }
	                  def_routine_seq[ &( theBehavior->getOnScheduleRoutine() ) ]


	| 'routine'
	  def_routine_model_impl[ $container , mdfr , spcfr ]
	;


def_routine_seq [ sep::Routine * routine ]
@init{
	PUSH_CTX_CPR( routine );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION( _CPR_ );

	POP_CTX;;
}
	: ( def_routine_parameters[ routine ] )?
	  ( ( '-->' | 'returns:' )  def_routine_returns[ routine ] )?

	  bs=block_statement  { routine->seqCode($bs.ac); }
	;


////////////////////////////////////////////////////////////////////////////////
// section COM
////////////////////////////////////////////////////////////////////////////////

section_model_of_interaction [ sep::Machine * machine ]
@init{
	sep::InteractionPart * theInteraction = machine->getUniqInteraction();

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(theInteraction);
}

	: ( '@interaction:' | '@com:' )
	  ( com_connector[ machine, theInteraction ] )*
	;

com_protocol
/* in */[ sep::Machine * machine , sep::ComProtocol * cp ]
	: 'env'       { $cp->setProtocol(sep::ComProtocol::PROTOCOL_ENVIRONMENT_KIND); }

	| 'rdv'       { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_RDV_KIND, sep::ComProtocol::PROTOCOL_UNICAST_KIND); }
	| 'multirdv'  { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_MULTIRDV_KIND, sep::ComProtocol::PROTOCOL_MULTICAST_KIND); }

	| 'flow'      { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_FLOW_KIND, sep::ComProtocol::PROTOCOL_MULTICAST_KIND); }


	| 'anycast'   { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_ANYCAST_KIND, sep::ComProtocol::PROTOCOL_ANYCAST_KIND); }

	| 'unicast'   { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_UNICAST_KIND, sep::ComProtocol::PROTOCOL_UNICAST_KIND); }

	| 'multicast' { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_MULTICAST_KIND, sep::ComProtocol::PROTOCOL_MULTICAST_KIND); }

	| 'broadcast' { $cp->setProtocolCast(sep::ComProtocol::PROTOCOL_BROADCAST_KIND, sep::ComProtocol::PROTOCOL_BROADCAST_KIND); }

	| bc=buffer_com [ machine ]
	{
		$cp->setProtocol(sep::ComProtocol::PROTOCOL_BUFFER_KIND);
		$cp->setBuffer($bc.buf);
	}
	;

com_cast[ sep::ComProtocol * cp ]
	: 'anycast'    { $cp->setCast(sep::ComProtocol::PROTOCOL_ANYCAST_KIND); }
	| 'unicast'    { $cp->setCast(sep::ComProtocol::PROTOCOL_UNICAST_KIND); }
	| 'multicast'  { $cp->setCast(sep::ComProtocol::PROTOCOL_MULTICAST_KIND); }
	| 'broadcast'  { $cp->setCast(sep::ComProtocol::PROTOCOL_BROADCAST_KIND); }
	;

buffer_com [ sep::Machine * machine ]
returns  [ sep::BF buf ]
	: 'buffer'
	  ( COLON
	    ( rb=ref_buffer[machine]  { $buf = $rb.buf; }
	    | db=def_buffer
		{
			$buf = sep::BF( new sep::Buffer(machine,
				newBufferID(), $db.kind, $db.size) );
		}
	    )

	  | LT_
	      ( rb=ref_buffer[machine]  { $buf = $rb.buf; }
	      | db=def_buffer
			{
				$buf = sep::BF( new sep::Buffer(machine,
						 newBufferID(), $db.kind, $db.size) );
			}
	      )
	    GT
	  )
	| db=def_buffer
	{
		$buf = sep::BF( new sep::Buffer(machine,
				 newBufferID(), $db.kind, $db.size) );
	}
	;


com_connector
/* in */[ sep::Machine * machine , sep::InteractionPart * anInteractionPart ]
@init{
	sep::Connector & aConnector = anInteractionPart->appendConnector();
	aConnector.updateProtocol(* anInteractionPart);
	std::string c_id;

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(aConnector);
}
	: ( 'connector' | 'connect' )
	  ( LT_
	    com_protocol[ machine, & aConnector ]
	    ( COMMA com_cast[ & aConnector ] )?
	    GT
	  )?
	  ( ID { c_id = $ID->getText(); } )?
	  { aConnector.fullyUpdateAllNameID(newConnectorID(c_id, "_#connector")); }
	  LCURLY
	  ( com_route[ machine, & aConnector ] )+
	  RCURLY


	| ( 'route' )
	  {
		aConnector.setNature( sep::IComPoint::IO_SIGNAL_NATURE );
		aConnector.fullyUpdateAllNameID(newConnectorID("", "_#route"));
	  }
	  ( LT_
	    com_protocol[ machine, & aConnector ]
	    ( COMMA com_cast[ & aConnector ] )?
	    GT
	  )?

	  ( com_route[ machine, & aConnector ]

	  | LCURLY  ( com_route[ machine, & aConnector ] )+  RCURLY

	  | LBRACKET  com_route_points[ machine , & aConnector ]  RBRACKET  SEMI
	  )
	;


com_route
/* in */[ sep::Machine * machine , sep::Connector * aConnector ]
@init{
	sep::ComRoute & comRoute = aConnector->appendComRoute(
			sep::Modifier::PROPERTY_INOUT_DIRECTION );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(comRoute);
}
	: modifier_set_direction_strict_text[ &( comRoute.getwModifier() ) ]
	  ( LT_ (
	    bc=buffer_com[ machine ]
		{
			comRoute.setProtocol(sep::ComProtocol::PROTOCOL_BUFFER_KIND);
			comRoute.setBuffer($bc.buf);
		}
	    | com_cast[ & comRoute ]
	  ) GT )?

	  ( com_port[ machine , & comRoute ]  SEMI

	  | LCURLY
	    ( com_port[ machine , & comRoute ]  SEMI )+
	    RCURLY

	  | LBRACKET
	    ( com_port[ machine , & comRoute ]
	      ( COMMA  com_port[ machine , & comRoute ] )*

	    | STAR
		{
			sep::ComPoint & comPoint = comRoute.appendAllComPoint(machine);

			SET_RULE_LOCATION(comPoint);
		}
	    )
	    RBRACKET
	    SEMI
	  )

    | com_port[ machine , & comRoute ]  SEMI
	;


com_route_points
/* in */[ sep::Machine * machine , sep::Connector * aConnector ]
@init{
	sep::ComRoute & comRoute = aConnector->appendComRoute(
			sep::Modifier::PROPERTY_INOUT_DIRECTION );

	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(comRoute);
}
	: com_port[ machine , & comRoute ]  
	  ( COMMA  com_port[ machine , & comRoute ] )*

	| STAR
    {
		sep::ComPoint & comPoint = comRoute.appendAllComPoint(machine);

		SET_RULE_LOCATION(comPoint);
    }
	;


com_port
/* in */[ sep::Machine * machine , sep::ComRoute * comRoute]
@init{
	sep::Machine * comMachine = machine;
	while( comMachine != nullptr )
	{
		if( comMachine->hasPortSignal() || (! comMachine->hasContainer()) )
		{
			break;
		}
		comMachine = comMachine->getContainerMachine();
	}

	SAVE_RULE_BEGIN_LOCATION;
}
	: //!g4!( qualifiedNameID '->' ) =>
	  m=qualifiedNameID
	  { comMachine = sep::ParserUtil::getMachine(machine, $m.s, $m.nb); }
	  
	  '->'

	  ( com_port_id[ machine , comRoute , comMachine ]

	  | LBRACKET
	    ( com_port_id[ machine , comRoute , comMachine ]

	      ( COMMA  com_port_id[ machine , comRoute , comMachine ] )*

	    | STAR
		{
			sep::ComPoint & comPoint = comRoute->appendAllComPoint(comMachine);

			SET_RULE_LOCATION(comPoint);
		}
	    )
	    RBRACKET
	  )


	| id=qualifiedNameID
	  {
		const sep::BF & comPort = sep::ParserUtil::getComPortSignal(
				comMachine, $id.s, $id.nb);
				
		sep::ComPoint & comPoint = ( comPort.valid() ) 
				? comRoute->appendComPoint(comPort.to_ptr< sep::Port >())
				: comRoute->appendComPoint(comMachine, NEW_QNID($id.s, $id.nb));
			
		SET_RULE_LOCATION(comPoint);
	  }

	;


com_port_id
/* in */[ sep::Machine * machine ,
		sep::ComRoute * comRoute , sep::Machine * comMachine ]
@init{
	SAVE_RULE_BEGIN_LOCATION;
}
	: id=qualifiedNameID
	  {
		const sep::BF & comPort = sep::ParserUtil::getComPortSignal(
				comMachine, $id.s, $id.nb);
				
		sep::ComPoint & comPoint = ( comPort.valid() ) 
			? comRoute->appendComPoint(comMachine, comPort.to_ptr< sep::Port >())
			: comRoute->appendComPoint(comMachine, NEW_QNID($id.s, $id.nb));
			
		SET_RULE_LOCATION(comPoint);
	  }
	;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// STATEMENT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

statement
returns [ sep::BFCode ac ]
	: s01=statement_assign            { $ac = $s01.ac; }
//	| s02=statement_buffer            { $ac = $s02.ac; }
	| s03=statement_com               { $ac = $s03.ac; }
	| s04=statement_constraint        { $ac = $s04.ac; }
	| s05=statement_jump              { $ac = $s05.ac; }
//	| s06=statement_time              { $ac = $s06.ac; }

	| s07=statement_activity          { $ac = $s07.ac; }
	| s08=statement_invoke_routine    { $ac = $s08.ac; }

	| s09=statement_moc               { $ac = $s09.ac; }

	| s10=statement_invoke            { $ac = $s10.ac; }
	| s11=statement_invoke_method     { $ac = $s11.ac; }

	| s12=statement_activity_new      { $ac = $s12.ac; }

	| s13=statement_ite               { $ac = $s13.ac; }
	| s14=statement_iteration         { $ac = $s14.ac; }

//	| s15=statement_lem               { $ac = $s15.ac; }

	| s16=block_statement             { $ac = $s16.ac; }

	| s17=prefix_statement            { $ac = $s17.ac; }

	| s18=statement_prompt            { $ac = $s18.ac; }

	| s19=meta_statement              { $ac = $s19.ac; }

//	| s20=quote_statement             { $ac = $s20.ac; }
	;



block_statement
returns [ sep::BFCode ac ]
@init{
	const sep::Operator * op = OP(SEQUENCE);
	bool implicitSequenceOp = true;
}
@after{
	if( implicitSequenceOp && $ac.valid() && $ac->hasOneOperand() )
	{
		sep::BFCode singleCode = $ac->first().bfCode();
		$ac = singleCode;
	}
}
	: LCURLY  ( o=op_block { op = $o.op; implicitSequenceOp = false; } )?
		{ $ac = NEW_STMT(op); }
	    (  s=statement  { $ac->append($s.ac); }  )*
	  RCURLY
	;

op_block
returns [ const sep::Operator * op ]
	: o1=op_sequence    { $op = $o1.op;   }
	| o2=op_scheduling  { $op = $o2.op;   }
	| o3=op_concurrency { $op = $o3.op;   }

	| OP_FORK          { $op = OP(FORK); }
	| OP_JOIN          { $op = OP(JOIN); }
	;

op_sequence
returns [ const sep::Operator * op ]
	: OP_SEQUENCE           { $op = OP(SEQUENCE);        }
	| OP_SEQUENCE_SIDE      { $op = OP(SEQUENCE_SIDE);   }
	| OP_SEQUENCE_WEAK      { $op = OP(SEQUENCE_WEAK);   }

	| OP_ATOMIC_SEQUENCE    { $op = OP(ATOMIC_SEQUENCE); }
	;

op_scheduling
returns [ const sep::Operator * op ]
	: OP_SCHEDULE_GT        { $op = OP(PRIOR_GT);  }
	| OP_SCHEDULE_LT        { $op = OP(PRIOR_LT);  }
	| OP_SCHEDULE_XOR       { $op = OP(EXCLUSIVE); }

	| OP_SCHEDULE_AND_THEN  { $op = OP(SCHEDULE_AND_THEN); }
	| OP_SCHEDULE_OR_ELSE   { $op = OP(SCHEDULE_OR_ELSE);  }

	| OP_NON_DETERMINISM    { $op = OP(NONDETERMINISM);    }
	;

op_concurrency
returns [ const sep::Operator * op ]
	: OP_CONCURRENCY_ASYNC            { $op = OP(ASYNCHRONOUS);           }
	| OP_CONCURRENCY_AND              { $op = OP(STRONG_SYNCHRONOUS);     }
	| OP_CONCURRENCY_OR               { $op = OP(WEAK_SYNCHRONOUS);       }
	| OP_CONCURRENCY_INTERLEAVING     { $op = OP(INTERLEAVING);           }
	| OP_CONCURRENCY_PARTIAL_ORDER    { $op = OP(PARTIAL_ORDER);          }
	| OP_CONCURRENCY_PARALLEL         { $op = OP(PARALLEL);               }
	
	| OP_CONCURRENCY_RDV_ASYNC        { $op = OP(RDV_ASYNCHRONOUS);       }
	| OP_CONCURRENCY_RDV_AND          { $op = OP(RDV_STRONG_SYNCHRONOUS); }
	| OP_CONCURRENCY_RDV_OR           { $op = OP(RDV_WEAK_SYNCHRONOUS);   }
	| OP_CONCURRENCY_RDV_INTERLEAVING { $op = OP(RDV_INTERLEAVING);       }
	| OP_CONCURRENCY_RDV_PARALLEL     { $op = OP(RDV_PARALLEL);           }
	;



op_invokable
returns [ sep::Operator * op ]
	: PLUS             { $op = OP(PLUS);         }

	| MINUS            { $op = OP(MINUS);        }

	| STAR             { $op = OP(MULT);         }
	| DIV              { $op = OP(DIV);          }
	| MOD              { $op = OP(MOD);          }

//	| POW              { $op = OP(POW);          }

	| EQUAL            { $op = OP(EQ);           }
	| NEQUAL           { $op = OP(NEQ);          }

	| SEQUAL           { $op = OP(SEQ);          }
	| NSEQUAL          { $op = OP(NSEQ);         }

	| GT               { $op = OP(GT);           }
	| GTE              { $op = OP(GTE);          }
	| LT_              { $op = OP(LT);           }
	| LTE              { $op = OP(LTE);          }

	| LNOT             { $op = OP(NOT);          }
	| LAND             { $op = OP(AND);          }
	| LAND_THEN        { $op = OP(AND_THEN);     }
	| LOR              { $op = OP(OR);           }
	| LOR_ELSE         { $op = OP(OR_ELSE);      }

	| BNOT             { $op = OP(BNOT);         }
	| BAND             { $op = OP(BAND);         }
	| BOR              { $op = OP(BOR);          }
	| BXOR             { $op = OP(BXOR);         }

	| LSHIFT           { $op = OP(LSHIFT);       }
	| RSHIFT           { $op = OP(RSHIFT);       }

	| ASSIGN           { $op = OP(ASSIGN);       }
	| ASSIGN_AFTER     { $op = OP(ASSIGN_AFTER); }
	| ASSIGN_REF       { $op = OP(ASSIGN_REF);   }
	| ASSIGN_MACRO     { $op = OP(ASSIGN_MACRO); }

	| OP_PUSH          { $op = OP(PUSH);         }
	| OP_ASSIGN_TOP    { $op = OP(ASSIGN_TOP);   }
	| OP_TOP           { $op = OP(TOP);          }
	| OP_POP           { $op = OP(POP);          }
	;

////////////////////////////////////////////////////////////////////////////////
// AVM STATEMENT
////////////////////////////////////////////////////////////////////////////////

prefix_statement
returns [ sep::BFCode ac ]
	: DOLLAR_LCURLY  a=avm_operator   { $ac = NEW_STMT($a.op);  }
	    ( ps=prefix_statement         { $ac->append($ps.ac); }
	    | e=unaryExpression           { $ac->append($e.bf);  }
	    )*
	  RCURLY
	;

prefix_expression
returns [ sep::BFCode ac ]
	: DOLLAR_LCURLY  a=avm_operator   { $ac = NEW_STMT($a.op);  }
	    ( ps=prefix_expression        { $ac->append($ps.ac); }
	    | e=unaryExpression           { $ac->append($e.bf);  }
	    )*
	  RCURLY
	;

avm_operator
returns [ const sep::Operator * op ]
	: oi=op_invokable  { $op = $oi.op; }

	| oa=op_activity   { $op = $oa.op; }

	| { ($op = sep::OperatorManager::getOp(getCurrentToken()->getText())) != nullptr }? ID
	;


////////////////////////////////////////////////////////////////////////////////
// AVM STATEMENT INVOKE
////////////////////////////////////////////////////////////////////////////////

statement_invoke_method
returns [ sep::BFCode ac ]
@init{
	sep::BF modelProcedure;
	sep::Machine * callProcedure;

	SAVE_RULE_BEGIN_LOCATION;
}
@after
{
	SET_RULE_LOCATION(callProcedure);
}
	: 'call' id=ID
	  {
		modelProcedure = sep::ParserUtil::getvarProcedure($id->getText());

		callProcedure = sep::Machine::newProcedureInstance(_CPM_,
				sep::OSS() << "call_" << ++mProcedureCallCount
						<< sep::NamedElement::NAME_ID_SEPARATOR
						<< $id->getText(), modelProcedure);

		callProcedure->getwSpecifier().setDesignInstanceStatic();

		$ac = NEW_STMT1(OP(INVOKE_METHOD), sep::BF(callProcedure));
	  }

	  decl_instance_machine_params [ callProcedure ] ?
	  decl_instance_machine_returns[ callProcedure ] ?

	  SEMI
	;


statement_invoke
returns [ sep::BFCode ac ]
	: LPAREN_INVOKE
	    ue=unaryExpression { $ac = NEW_STMT1(OP(INVOKE_METHOD), $ue.bf); }
	    ( id=ID            { $ac->append(sep::ParserUtil::getInvokable($ue.bf, $id->getText())); }
	    | 'in'             { $ac->append( INCR_BF(OP(IN)) ); }
	    | op=op_invokable  { $ac->append( INCR_BF($op.op) ); }
	    )
	    ( e=expression     { $ac->append($e.bf); } )*
	    ( 'provided:'   e=expression
	    | 'from:'       ue=unaryExpression
	    | 'to:'         ue=unaryExpression
	    | 'activity:'   o=op_activity
	    )?
	  RPAREN
	  SEMI
	;

expression_invoke
returns [ sep::BFCode ac ]
	: LPAREN_INVOKE
	    ue=unaryExpression  { $ac = NEW_STMT1(OP(INVOKE_METHOD), $ue.bf); }
	    ( id=ID            { $ac->append(sep::ParserUtil::getInvokable($e.bf, $id->getText())); }
	    | 'in'             { $ac->append( INCR_BF(OP(IN)) ); }
	    | oi=op_invokable  { $ac->append( INCR_BF($oi.op) ); }
	    )
	    ( e=expression     { $ac->append($e.bf); } )*
//	    ( 'provided:'   e=expression
//	    | 'from:'      ue=unaryExpression
//	    | 'to:'        ue=unaryExpression
//	    | 'activity:'   o=op_activity
//	    )?
	  RPAREN
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT NEW
////////////////////////////////////////////////////////////////////////////////

statement_activity_new
returns [ sep::BFCode ac ]
@init{
	sep::Machine * ptrInstance = nullptr;
	sep::BF aModel;
	
	sep::Machine * container = _CPM_;
}
@after{
	if( aModel.is< sep::Machine >() )
	{
		POP_CTX;
	}
}
	: 'new'   { $ac = NEW_STMT(OP(INVOKE_NEW)); }
	  id=qualifiedNameID
	  {
		aModel = sep::ParserUtil::getvarMachine($id.s, $id.nb);

		if( aModel.is< sep::Machine >() )
		{
			PUSH_CTX_NEW( aModel.to_ptr< sep::Machine >() );
		}

		ptrInstance = sep::Machine::newInstance(container,
				newInvokeNewInstanceNameID(container, $id.s), aModel, 1, 1);

		ptrInstance->getwSpecifier().override_ifdef(
				sep::Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER );

		 $ac->append( container->saveOwnedElement( ptrInstance ) );
	  }

	  //activity_machine_param_return[ aModel , $ac ]
	  decl_instance_dynamic_impl[ _CPM_ , ptrInstance ]

	  ( ( '-->' | 'returns:' ) e=expression )?

      SEMI
	;


decl_instance_dynamic_impl
/* in */[ sep::Machine * container , sep::Machine * ptrInstance ]
@init{
	SAVE_RULE_BEGIN_LOCATION;
}
@after{
	SET_RULE_LOCATION(ptrInstance);
}
	: ( //!g4!( LPAREN ) =>
	    LPAREN
	    ( def_instance_on_new_activity[ ptrInstance ] ) ?
	    RPAREN
	  )?

	  ( //!g4!( LCURLY ) =>
	    LCURLY
	    ( s=statement { ptrInstance->getUniqBehaviorPart()->seqOnCreate($s.ac); } )*

	    ( def_instance_activity[ ptrInstance ] )*
	    RCURLY
	  )?
	;



expression_activity_new
returns [ sep::BFCode ac ]
@init{
	sep::Machine * ptrInstance = nullptr;
	sep::BF aModel;
	
	sep::Machine * container = _CPM_;
}
@after{
	if( aModel.is< sep::Machine >() )
	{
		POP_CTX;
	}
}
	: 'new'    { $ac = NEW_STMT(OP(INVOKE_NEW)); }
	  id=qualifiedNameID
	  {
		sep::BF aModel = sep::ParserUtil::getvarMachine($id.s, $id.nb);

		if( aModel.is< sep::Machine >() )
		{
			PUSH_CTX_NEW( aModel.to_ptr< sep::Machine >() );
		}

		ptrInstance = sep::Machine::newInstance(container,
				newInvokeNewInstanceNameID(container, $id.s), aModel, 1, 1);

		ptrInstance->getwSpecifier().override_ifdef(
				sep::Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER );

		 $ac->append( container->saveOwnedElement( ptrInstance ) );
	  }

	  activity_machine_param_return[ aModel , $ac ]
//	  decl_instance_dynamic_expr_impl[ _CPM_ , ptrInstance , $ac ]

//	  { $ac->toStream(sep::AVM_OS_DEBUG); }
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT PROMPT
////////////////////////////////////////////////////////////////////////////////

statement_prompt
returns [ sep::BFCode ac ]
	: spi=statement_prompt_obs { $ac =  $spi.ac; }  // STATEMENT_PROMPT
	;

statement_prompt_obs
returns [ sep::BFCode ac ]
@init{
	sep::BF varMachine = INCR_BF(_SYSTEM_);
	sep::BF condition = sep::ExpressionConstant::BOOLEAN_TRUE;
}
	: ( '@observe' | '@obs' )

	  ( LPAREN  'ctx:'  id=qualifiedNameID  RPAREN
	  { varMachine = sep::ParserUtil::getvarMachine($id.s, $id.nb); }
	  )?

	  LCURLY
	    bs=statement_prompt_obs_com[ varMachine ]
	  RCURLY
	  (
	  ( 'provided:' e=expression
	  | LBRACKET e=expression RBRACKET
	  ) 
	  { condition = $e.bf; }
	  SEMI
	  )?

	{ $ac = NEW_STMT3(OP(OBS), varMachine, $bs.ac, condition); }
	;


statement_prompt_obs_com  [ sep::BF varMachine ]
returns [ sep::BFCode ac ]
	: sc=statement_com  { $ac = $sc.ac; }
	;


////////////////////////////////////////////////////////////////////////////////
// META STATEMENT
////////////////////////////////////////////////////////////////////////////////

meta_statement
returns [ sep::BFCode ac ]
	: ( '@informal'  { $ac = NEW_STMT(OP(INFORMAL)); }
	  | '@trace'     { $ac = NEW_STMT(OP(TRACE));    }
	  | '@debug'     { $ac = NEW_STMT(OP(DEBUG));    }
	  | '@comment'   { $ac = NEW_STMT(OP(COMMENT));  }
	  )
		LCURLY  
	    	( ( s=statement   { $ac->append($s.ac); } )+
	    	| ( e=expression  { $ac->append($e.bf); } )+
	    	)
	  	RCURLY
//	| '@expression' id=StringLiteral { $ac = NEW_STMT(OP(DEBUG));    }
//	| '@statement'  id=StringLiteral { $ac = NEW_STMT(OP(DEBUG));    }
	
/* TODO#ADD
	// meta_eval
	| LBRACKET_BAR
	    e=expression  { $ac = NEW_STMT1(OP(META_EVAL), $e.bf); }
	  BAR_RBRACKET

	// meta_run
	| LBRACKET_LCURLY
	    s=statement   { $ac = NEW_STMT1(OP(META_RUN), $s.ac); }
	  RCURLY_RBRACKET
*/
	;

/* TODO#ADD
quote_statement
returns [ sep::BFCode ac ]
@init{
	const sep::Operator * op = OP(SEQUENCE);
}
	: PERCENT_LCURLY  ( o=op_block { op = $o.op; } ) ?  { $ac = NEW_STMT(op); }
	    ( s=statement  { $ac->append($s.ac); }  )+
	  RCURLY_PERCENT
	 { $ac = NEW_STMT1(OP(QUOTE), $ac); }
	;
*/


////////////////////////////////////////////////////////////////////////////////
// STATEMENT ASSIGN
////////////////////////////////////////////////////////////////////////////////

statement_assign
returns [ sep::BFCode ac ]
	// lvalue := expression
	: lv=lvalue
	( ( ASSIGN | ASSIGN_AFTER )  e=expression  SEMI
	  { $ac = NEW_STMT2(OP(ASSIGN), $lv.bf, $e.bf); }

	| ASSIGN_REF  rlv=lvalue  SEMI
	{ $ac = NEW_STMT2(OP(ASSIGN_REF), $lv.bf, $rlv.bf); }

	| ASSIGN_MACRO  e=expression  SEMI
	{ $ac = NEW_STMT2(OP(ASSIGN_MACRO), $lv.bf, $e.bf); }


	| ( PLUS_ASSIGN | PLUS_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf, $e.bf); }

	| ( MINUS_ASSIGN | MINUS_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(MINUS), $lv.bf, $e.bf); }

	| ( STAR_ASSIGN | STAR_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(MULT), $lv.bf, $e.bf); }

	| ( DIV_ASSIGN | DIV_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(DIV), $lv.bf, $e.bf); }

	| ( MOD_ASSIGN | MOD_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(MOD), $lv.bf, $e.bf); }


	| ( LAND_ASSIGN | LAND_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(AND), $lv.bf, $e.bf); }

	| ( LOR_ASSIGN | LOR_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(OR), $lv.bf, $e.bf); }


	| ( BAND_ASSIGN | BAND_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(BAND), $lv.bf, $e.bf); }

	| ( BOR_ASSIGN | BOR_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(BOR), $lv.bf, $e.bf); }

	| ( BXOR_ASSIGN | BXOR_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(BXOR), $lv.bf, $e.bf); }


	| ( LSHIFT_ASSIGN | LSHIFT_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(LSHIFT), $lv.bf, $e.bf); }

	| ( RSHIFT_ASSIGN | RSHIFT_ASSIGN_AFTER )  e=expression  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(RSHIFT), $lv.bf, $e.bf); }


	// queue <=< expression ( <=< expression )*
	// fifo <=< a <=< b <=< c
	// soit :>  fifo:a:b:c
	| OP_PUSH  e=expression
	{ $ac = NEW_STMT2(OP(PUSH), $lv.bf, $e.bf); }
	  ( OP_PUSH  e=expression  { $ac->append($e.bf); } )*
	  SEMI

	// queue ^=< expression
	// fifo:a ^=< b
	// soit :>  fifo:b
	| OP_ASSIGN_TOP  e=expression  SEMI
	{ $ac = NEW_STMT2(OP(ASSIGN_TOP), $lv.bf, $e.bf); }

	// queue ^=> lvalue
	// fifo:a ^=> b
	// soit :>  fifo:a  et  lvalue = a
	| OP_TOP  v=lvalue  SEMI
	{ $ac = NEW_STMT2(OP(TOP), $lv.bf, $v.bf); }

	// queue >=> lvalue ( >=> lvalue )*
	// fifo::a::b::c >=> lvalue1 >=> lvalue2 >=> lvalue3
	// soit :>  fifo  et  lvalue1 = c , lvalue2 = b , lvalue3 = a
	| OP_POP      { $ac = NEW_STMT1(OP(POP), $lv.bf); }
	  ( v=lvalue  { $ac->append($v.bf); } )*
	  SEMI

	// lvalue ++
	| INCR  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_ONE); }

	// lvalue --
	| DECR  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_MINUS_ONE); }
	)

//	| 'pop'  lv=lvalue  SEMI
//	{ $ac = NEW_STMT1(OP(POP), $lv.bf); }

//	| 'newfresh'  lv=lvalue  SEMI
//	{ $ac = NEW_STMT1(OP(ASSIGN_NEWFRESH), $lv.bf); }

	// ++ lvalue
	| INCR  lv=lvalue  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_ONE); }

	// -- lvalue
	| DECR  lv=lvalue  SEMI
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_MINUS_ONE); }
	;


lvalue
returns [ sep::BF bf ]
@init{
	sep::UniFormIdentifier * ufi = new sep::UniFormIdentifier(false);
	sep::BF bfUfi( ufi ); // for automatic destruction of << UFI >> if need

	std::size_t countID = 1;
	bool isnotEXPR = true;

	SAVE_RULE_BEGIN_LOCATION;
}
	: ( COLONx2 { ufi->setAbsolute(); } )?
	  id=ID
	  {
		if( ($bf = sep::ParserUtil::getvar($id->getText(), 1)).valid() )
		{
			ufi->appendFieldVariable($bf);
		}
		else if( ($bf = sep::ParserUtil::getvarMachine(
				$id->getText(), 1)).valid() )
		{
			ufi->appendFieldMachine($bf);
		}
		else
		{
			ufi->appendField($id->getText());
		}

		$bf = bfUfi;
	  }

	  ( ( DOT id=ID
		{ ufi->appendField($id->getText());  ++countID; } )

	  | ( LBRACKET  e=expression  RBRACKET
		{ ufi->appendIndex($e.bf); isnotEXPR = false; } )
	  )*
	{
		if( isnotEXPR )
		{
			if( countID == 1 )
			{
				$bf = ufi->first();
			}
			else if( ($bf = sep::ParserUtil::getvar(
					ufi->str(), countID)).invalid() )
			{
				$bf = bfUfi;
				SET_RULE_LOCATION(ufi);
			}
		}
	}
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT BUFFER
////////////////////////////////////////////////////////////////////////////////

//statement_buffer
//returns [ sep::BFCode ac ]
//	: 'clear'  id=qualifiedNameID  SEMI
//	{ $ac = NEW_STMT1(OP(CLEAR), getvarBuffer($id.s, $id.nb)); }
//
//	| 'push'  id=qualifiedNameID
//    { $ac = NEW_STMT1(OP(PUSH), getvarBuffer($id.s, $id.nb)); }
//	   parameters[ ac ] ?  SEMI
//
//	| 'pop'   id=qualifiedNameID
//    { $ac = NEW_STMT1(OP(POP), getvarBuffer($id.s, $id.nb)); }
//	  parameters[ ac ] ?  SEMI
//
//	| 'top'   id=qualifiedNameID
//    { $ac = NEW_STMT1(OP(TOP), getvarBuffer($id.s, $id.nb)); }
//	  parameters[ ac ] ?  SEMI
//	;

//expression_buffer
//returns [ sep::BFCode ac ]
//	: 'empty'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(EMPTY), $e.bf); }
//
//	| 'nonempty'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(NONEMPTY), $e.bf); }
//
//	| 'singleton'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(SINGLETON), $e.bf); }
//
//	| 'populated'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(POPULATED), $e.bf); }
//
//	| 'full'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(FULL), $e.bf); }
//
//	| 'size'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(SIZE), $e.bf); }
//
//	| 'pop'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(POP), $e.bf); }
//
//	| 'top'  e=unaryExpression
//	{ $ac = NEW_STMT1(OP(TOP), $e.bf); }
//	;

parameters [ sep::BFCode ac ]
	: LPAREN  e=expression  { $ac->append($e.bf); }
	  ( COMMA e=expression  { $ac->append($e.bf); }  )*
	  RPAREN
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT COM
////////////////////////////////////////////////////////////////////////////////

statement_com
returns [ sep::BFCode ac ]
	: si=statement_com_input   { $ac = $si.ac; }
	| so=statement_com_output  { $ac = $so.ac; }
	;

statement_com_input
returns [ sep::BFCode ac ]
@init{
	sep::BF varPortSignal;
	sep::Port * port = nullptr;
	const sep::Operator * op = nullptr;
}
	: ( tok='input'        { op = OP(INPUT);        }
	  | tok='input#save'   { op = OP(INPUT_SAVE);   }
	  | tok='input#var'    { op = OP(INPUT_VAR);    }
	  | tok='input#flow'   { op = OP(INPUT_FLOW);   }
	  | tok='input#env'    { op = OP(INPUT_ENV);    }
	  | tok='input#buffer' { op = OP(INPUT_BUFFER); }
	  | tok='input#rdv'    { op = OP(INPUT_RDV);    }
	  ) id=qualifiedNameID
	  {
		$ac = NEW_STMT1( op,
			varPortSignal = sep::ParserUtil::getvarPortSignal($id.s, $id.nb) );
		if( varPortSignal.is< sep::Port >() )
		{ port = varPortSignal.to_ptr< sep::Port >(); }
		else if( varPortSignal.invalid() )
		{
			sep::ParserUtil::avm_syntax_error(
				"statement_com_input:> ", $tok.line )
					<< "Unfound port/signal or variable < " << $id.s
					<< " > in machine < " << str_header( _CPM_ ) << " >"
					<< sep::ParserUtil::SYNTAX_ERROR_EOL;
		}
	  }
	  parameters_port[ port , $ac ] ?
	  ( '<--'
	    ( 'env'  { $ac->setOperator( OP(INPUT_ENV) ); }
	    | me=expression
		{
			sep::BFCode inputFrom = NEW_STMT2(OP(INPUT_FROM), $ac->first(), $me.bf);

			inputFrom->getOperands().insert(
					inputFrom->end(), ++($ac->begin()), $ac->end() );
					
			$ac = inputFrom;
		}
	    )
	    ( '<-' id=qualifiedNameID
		{ $ac->append(sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }
	    )?
	  )?
	  ( ( '<==' | 'via' ) id=qualifiedNameID
	  { sep::ParserUtil::updateSignalRoutingChannel(
			sep::Modifier::DIRECTION_INPUT_KIND, $ac, $id.s, $id.nb); }
	  )?
	  SEMI
	;

statement_com_output
returns [ sep::BFCode ac ]
@init{
	sep::BF varPortSignal;
	sep::Port * port = nullptr;
	const sep::Operator * op = nullptr;
}
	: ( tok='output'        { op = OP(OUTPUT);        }
	  | tok='output#var'    { op = OP(OUTPUT_VAR);    }
	  | tok='output#flow'   { op = OP(OUTPUT_FLOW);   }
	  | tok='output#env'    { op = OP(OUTPUT_ENV);    }
	  | tok='output#buffer' { op = OP(OUTPUT_BUFFER); }
	  | tok='output#rdv'    { op = OP(OUTPUT_RDV);    }
	  ) id=qualifiedNameID
	  {
		$ac = NEW_STMT1( op,
			varPortSignal = sep::ParserUtil::getvarPortSignal($id.s, $id.nb) );
		if( varPortSignal.is< sep::Port >() )
		{ port = varPortSignal.to_ptr< sep::Port >(); }
		else if( varPortSignal.invalid() )
		{
			sep::ParserUtil::avm_syntax_error(
				"statement_com_output:>", $tok.line )
					<< "Unfound port/signal or variable < " << $id.s
					<< " > in machine < " << str_header( _CPM_ ) << " >"
					<< sep::ParserUtil::SYNTAX_ERROR_EOL;
		}
	  }
	  parameters_port[ port , $ac ] ?
	  ( '-->'
	    ( 'env'  { $ac->setOperator( OP(OUTPUT_ENV) ); }
	    | me=expression
		  {
			sep::BFCode outputTo = NEW_STMT2(OP(OUTPUT_TO), $ac->first(), $me.bf);

			outputTo->getOperands().insert(
					outputTo->end(), ++($ac->begin()), $ac->end() );
					
			$ac = outputTo;
		  }
	    )
	    ( '->' id=qualifiedNameID
		{ $ac->append(sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }
	    )?
	  )?
	  ( ( '==>' | 'via' ) id=qualifiedNameID
	  { sep::ParserUtil::updateSignalRoutingChannel(
			sep::Modifier::DIRECTION_OUTPUT_KIND, $ac, $id.s, $id.nb); }
	  )?
	  SEMI
	;


parameters_port
/* in */[ sep::Port * port , sep::BFCode ac ]
@init{
	sep::BFVector labelledParams(
			(port != nullptr) ? port->getParametersCount() : 0 );

	sep::BFList positionalParams;
}
@after{
	sep::ParserUtil::computePortParameter(
			port, $ac, labelledParams, positionalParams);
}
	: LPAREN
	    lp=labelled_argument
		{
			sep::ParserUtil::appendPortParameter(port, $lp.label,
					labelledParams, positionalParams, $lp.arg);
		}
	  ( COMMA  lp=labelled_argument
		{
			sep::ParserUtil::appendPortParameter(port, $lp.label,
					labelledParams, positionalParams, $lp.arg);
		}
	    )*
	  RPAREN
	;



expression_com
returns [ sep::BFCode ac ]
	: 'present'  id=qualifiedNameID
	{ $ac = NEW_STMT1(OP(PRESENT),
		sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }

	| 'absent'  id=qualifiedNameID
	{ $ac = NEW_STMT1(OP(ABSENT),
		sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }
	;

////////////////////////////////////////////////////////////////////////////////
// STATEMENT GUARD
////////////////////////////////////////////////////////////////////////////////

statement_constraint
returns [ sep::BFCode ac ]
	: sg=statement_guard        { $ac = $sg.ac; }
	| st=statement_timed_guard  { $ac = $st.ac; }
	| sc=statement_checksat     { $ac = $sc.ac; }
	;


statement_guard
returns [ sep::BFCode ac ]
	: 'guard'  e=expression  SEMI
	{ $ac = NEW_STMT1(OP(GUARD), $e.bf); }

	| 'event'  e=expression  SEMI
	{ $ac = NEW_STMT1(OP(EVENT), $e.bf); }
	;

statement_timed_guard
returns [ sep::BFCode ac ]
	: 'tguard'  e=expression  SEMI
	{ $ac = NEW_STMT1(OP(TIMED_GUARD), $e.bf); }
	;

statement_checksat
returns [ sep::BFCode ac ]
@init{
	std::string solverID;
}
	: 'checksat'
	  ( LT_  ( id=StringLiteral | id=ID )  GT    { solverID = $id->getText(); }
	  | 'solver:'  ( id=StringLiteral | id=ID )  { solverID = $id->getText(); }
	  )?
	  e=expression  SEMI
	{
		if( solverID.empty() )
		{
			$ac = NEW_STMT1( OP(CHECK_SAT), $e.bf );
		}
		else
		{
			$ac = NEW_STMT2( OP(CHECK_SAT), NEW_STRING(solverID), $e.bf );
		}
	}
	;


expression_checksat
returns [ sep::BFCode ac ]
@init{
	std::string solverID;
}
	: 'checksat'
	  ( LT_  ( id=StringLiteral | id=ID )  GT    { solverID = $id->getText(); }
	  | 'solver:'  ( id=StringLiteral | id=ID )  { solverID = $id->getText(); }
	  )?
	  e=expression
	{
		if( solverID.empty() )
		{
			$ac = NEW_STMT1( OP(CHECK_SAT), $e.bf);
		}
		else
		{
			$ac = NEW_STMT2( OP(CHECK_SAT), NEW_STRING(solverID), $e.bf );
		}
	}
	;

expression_quantifier
returns [ sep::BFCode ac ]
@init{
	sep::BFCode code;
	
	sep::PropertyPart boundVariables(_CPM_, "bound#vars");
	
	PUSH_CTX_LOCAL( & boundVariables );
}
@after{
	POP_CTX;
}
	: ( 'forall' { code = NEW_CODE( OP(FORALL) ); }
	  | 'exists' { code = NEW_CODE( OP(EXISTS) ); } 
	  )
	  LT_  ( id=ID  COLON  tv=type_var )
	  { code->append( boundVariables.saveOwnedVariable(
	  			new sep::Variable( _CPM_,
	  					sep::Modifier::PROPERTY_QUANTIFIER_PARAMETER_MODIFIER,
	  					$tv.type, $id->getText() ) )); 
	  }
	  ( COMMA id=ID  COLON  tv=type_var
	  { code->append( boundVariables.saveOwnedVariable(
	  			new sep::Variable( _CPM_,
			  			sep::Modifier::PROPERTY_QUANTIFIER_PARAMETER_MODIFIER,
			  			$tv.type, $id->getText() ) )); 
	  }
	  )*
	  GT
	  e=expression
	{
		code->append( $e.bf );
		$ac = code;
	}
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT IF THEN [ ELSEIF ] [ ELSE ]
////////////////////////////////////////////////////////////////////////////////

statement_ite
returns [ sep::BFCode ac ]
@init{
	sep::BFCode elseifCode;
	sep::BFCode code;
}
	: 'if'  e=expression  bs=block_statement
	  { code = $ac = NEW_STMT2(OP(IF), $e.bf, $bs.ac); }
	  ( ( 'elseif' | 'else' 'if' )  e=expression  bs=block_statement
		{
			code->setOperator(OP(IFE));
			code->append(elseifCode = NEW_STMT2(OP(IF), $e.bf, $bs.ac));
			code = elseifCode;
		}
	  )*
	  ( 'else'  bs=block_statement
		{
			if( $bs.ac->hasOperand() )
			{
				code->setOperator(OP(IFE)); code->append($bs.ac);
			}
		}
	  )?
	;

expression_ite
returns [ sep::BFCode ac ]
@init{
	sep::BFCode elseifExpr;
	sep::BFCode expr;
}
	: 'if'  c=expression  LCURLY  e=expression  RCURLY
	  { expr = $ac = NEW_STMT2(OP(IF), $c.bf, $e.bf); }
	  ( ( 'elseif' | 'else' 'if' ) c=expression  LCURLY  e=expression  RCURLY
		{
			expr->setOperator(OP(IFE));
			expr->append(elseifExpr = NEW_STMT2(OP(IF), $c.bf, $e.bf));
			expr = elseifExpr;
		}
	  )*
	  ( 'else'  LCURLY  e=expression  RCURLY
		{ expr->setOperator(OP(IFE)); expr->append($e.bf); }
	  )?
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT WHERE  PROVIDED
////////////////////////////////////////////////////////////////////////////////

//statement_where
//returns [ sep::BFCode ac ]
//	: 'where'  e=expression  bs=block_statement
//	  { $ac = NEW_STMT2(OP(WHERE), $e.bf, $bs.ac); }
//	  ( 'provided'  e=expression    { $ac->append($e.bf); } )?
//	  ( 'else'  bs=block_statement  { $ac->append($bs.ac); }
//	  )?
//	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT ITERATION
////////////////////////////////////////////////////////////////////////////////

statement_iteration
returns [ sep::BFCode ac ]
	: 'for'
	  ( isa=for_assign_header  SEMI  e=expression  SEMI  sai=for_assign_header
		{ $ac = NEW_STMT3(OP(FOR), $isa.ac, $e.bf, $sai.ac); }
	  |
	    LPAREN
	      isa=for_assign_header  SEMI  e=expression  SEMI  sai=for_assign_header
	    RPAREN
		{ $ac = NEW_STMT3(OP(FOR), $isa.ac, $e.bf, $sai.ac); }
	  |
	    lv=lvalue  COLON  e=expression
		{ $ac = NEW_STMT2(OP(FOREACH), $lv.bf, $e.bf); }
	  |
	    LPAREN  lv=lvalue  COLON  e=expression  RPAREN
		{ $ac = NEW_STMT2(OP(FOREACH), $lv.bf, $e.bf); }
	  )
	  sa=block_statement  { $ac->append($sa.ac); }

	| 'while'  e=expression  bs=block_statement
	{ $ac = NEW_STMT2(OP(WHILE_DO), $e.bf, $bs.ac); }

	| 'do'  bs=block_statement  'while'  e=expression  SEMI
	{ $ac = NEW_STMT2(OP(DO_WHILE), $bs.ac, $e.bf); }
	;


for_assign_header
returns [ sep::BFCode ac ]
	// lvalue := expression
	: lv=lvalue
	( ASSIGN  e=expression
	{ $ac = NEW_STMT2(OP(ASSIGN), $lv.bf, $e.bf); }

	// ++ lvalue
	// lvalue ++
	| INCR
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_ONE); }

	// lvalue --
	| DECR
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_MINUS_ONE); }
	)

	| INCR  lv=lvalue
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		 sep::ExpressionConstant::INTEGER_ONE); }

	// -- lvalue
	| DECR  lv=lvalue
	{ $ac = NEW_STMT_ASSIGN_OP(OP(PLUS), $lv.bf,
		sep::ExpressionConstant::INTEGER_MINUS_ONE); }
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT JUMP
////////////////////////////////////////////////////////////////////////////////

statement_jump
returns [ sep::BFCode ac ]
	: 'break'         { $ac = NEW_STMT(OP(BREAK)); }
	  ( e=expression  { $ac->append( $e.bf ); } )?
	  SEMI

	| 'continue'      { $ac = NEW_STMT(OP(CONTINUE)); }
	  ( e=expression  { $ac->append( $e.bf ); } )?
	  SEMI

	| 'return'        { $ac = NEW_STMT(OP(RETURN)); }
	  ( e=expression  { $ac->append( $e.bf ); }
	    ( COMMA e=expression  { $ac->append( $e.bf ); } )*
	  )?
	  SEMI

	| 'exit'          { $ac = NEW_STMT(OP(EXIT)); }
	  ( e=expression  { $ac->append( $e.bf ); } )?
	  SEMI
	;

////////////////////////////////////////////////////////////////////////////////
// STATEMENT LAMBDA
////////////////////////////////////////////////////////////////////////////////

expression_lambda
returns [ sep::BFCode ac ]
	: 'lambda'  { $ac = NEW_CODE( OP(LAMBDA) ); }
	  ( id=ID   { $ac->append( NEW_ID($id->getText()) ); } )*
	  '->' e=expression  { $ac->append( $e.bf ); }
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT STATUS
////////////////////////////////////////////////////////////////////////////////

expression_status
returns [ sep::BFCode ac ]
	: 'status#was'    o=op_activity  id=qualifiedNameID
	{ $ac = NEW_STMT2(OP(STATUS_WAS), INCR_BF($o.op),
			sep::ParserUtil::getvarMachine($id.s, $id.nb)); }

	| 'status#is'     o=op_activity  id=qualifiedNameID
	{ $ac = NEW_STMT2(OP(STATUS_IS), INCR_BF($o.op),
			sep::ParserUtil::getvarMachine($id.s, $id.nb)); }

	| 'status#being'  o=op_activity  id=qualifiedNameID
	{ $ac = NEW_STMT2(OP(STATUS_BEING), INCR_BF($o.op),
			sep::ParserUtil::getvarMachine($id.s, $id.nb)); }

	| 'status#will'   o=op_activity  id=qualifiedNameID
	{ $ac = NEW_STMT2(OP(STATUS_WILL), INCR_BF($o.op),
			sep::ParserUtil::getvarMachine($id.s, $id.nb)); }

	| 'changed'     lv=lvalue
	{ $ac = NEW_STMT1(OP(CHANGED), $lv.bf); }

	| 'changed#to'  lv=lvalue
	{ $ac = NEW_STMT1(OP(CHANGED_TO), $lv.bf); }
	;

op_activity
returns [ sep::Operator * op ]
	: 'init'     { $op = OP(INIT);            }
	| 'final'    { $op = OP(FINAL);           }
	| 'destroy'  { $op = OP(DESTROY);         }
	| 'start'    { $op = OP(START);           }
	| 'restart'  { $op = OP(RESTART);         }
	| 'stop'     { $op = OP(STOP);            }
	| 'ienable'  { $op = OP(IENABLE_INVOKE);  }
	| 'enable'   { $op = OP(ENABLE_INVOKE);   }
	| 'idisable' { $op = OP(IDISABLE_INVOKE); }
	| 'disable'  { $op = OP(DISABLE_INVOKE);  }
	| 'iabort'   { $op = OP(IABORT_INVOKE);   }
	| 'abort'    { $op = OP(ABORT_INVOKE);    }
	| 'run'      { $op = OP(RUN);             }
	| 'rtc'      { $op = OP(RTC);             }
	| 'schedule' { $op = OP(SCHEDULE_INVOKE); }
	| 'suspend'  { $op = OP(SUSPEND);         }
	| 'resume'   { $op = OP(RESUME);          }
	| 'wait'     { $op = OP(WAIT);            }
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT ACTIVITY
////////////////////////////////////////////////////////////////////////////////

statement_activity
returns [ sep::BFCode ac ]
@init{
	sep::BF flowTarget;
	sep::BF machine;
}
	: o=op_activity  { $ac = NEW_STMT($o.op); }
	  ( id=qualifiedNameID
		{ $ac->append(machine =
			sep::ParserUtil::getvarMachine($id.s, $id.nb)); }

	  | ( '$self' | 'self' )  
		{ machine = sep::ExecutableLib::MACHINE_SELF; }
		( ( ( LPAREN id=qualifiedNameID RPAREN )
		  | ( LT_ id=qualifiedNameID GT )
		  )
		{ machine = NEW_CODE1(OP(SELF),
				sep::ParserUtil::getSelfExecutableMachine($id.s)); }
		)?
		{ $ac->append(machine); }
	  | ( '$this' | 'this' ) 
	  	{ $ac->append(machine = sep::ExecutableLib::MACHINE_THIS); }

	  | '$parent' { $ac->append(machine = sep::ExecutableLib::MACHINE_PARENT); }
	  | '$super'  { $ac->append(machine = sep::ExecutableLib::MACHINE_PARENT); }
	  
	  | '$system' { $ac->append(machine = sep::ExecutableLib::MACHINE_SYSTEM); }
	  )?
	  
//	  ( e=expression { $ac->append($e.bf); } )?
	  
	  activity_machine_param_return[ machine , $ac ] ?
	  SEMI
	/*
	| 'wait'  expression  SEMI
	{ $ac = NEW_STMT(OP(WAIT)); }
	*/

//	| 'goto'  id=qualifiedNameID
//	  { $ac = NEW_STMT1(OP(GOTO),
//		flowTarget = sep::ParserUtil::getvarMachine($id.s, $id.nb)); }
	| 'goto'   e=expression 
	  { $ac = NEW_STMT1(OP(GOTO),  $e.bf); flowTarget = $e.bf; }
		
	  ( fs=statement_init_flow[flowTarget]  { $ac->append($fs.ac); }
	  | SEMI
	  )

	| 'join'  e=expression  SEMI
	{ $ac = NEW_STMT1(OP(JOIN), $e.bf); }

	;


statement_init_flow [ sep::BF flowTarget ]
returns [ sep::BFCode ac ]
@init{
	if( flowTarget.is< sep::Machine >() )
	{
		PUSH_CTX_CPM( flowTarget.to_ptr< sep::Machine >() );
	}
}
@after{
	if( flowTarget.is< sep::Machine >() )
	{
		POP_CTX;
	}
}
	: 'flow' bs=block_statement   { $ac = $bs.ac; }
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT ROUTINE INVOKATION
////////////////////////////////////////////////////////////////////////////////

statement_invoke_routine
returns [ sep::BFCode ac ]
@init{
	sep::Routine * invokeRoutine = nullptr;
}
	: id=ID
	  {
		invokeRoutine = sep::Routine::newInvoke( _CPRMS_, $id->getText());

		invokeRoutine->setModel(
				sep::ParserUtil::getvarRoutine($id->getText()) );
	  }

	  invoke_routine_params[ invokeRoutine ]
      ( invoke_routine_returns[ invokeRoutine ] )?
      SEMI

      { $ac = sep::Routine::invokeRoutineStatement(invokeRoutine); }
	;


invoke_routine_params [ sep::Routine * invokeRoutine ]
	: LPAREN
	  ( lp=labelled_argument
		{
			invokeRoutine->getPropertyPart().appendVariableParameter($lp.label, $lp.arg);
		}
	    ( COMMA
	    lp=labelled_argument
		{
			invokeRoutine->getPropertyPart().appendVariableParameter($lp.label, $lp.arg);
		}
	    )*
	  )?
	  RPAREN
	;


invoke_routine_returns [ sep::Routine * invokeRoutine ]
	: ( '-->' | 'returns:' )
	  ( LPAREN
	    lp=labelled_argument
		{
			invokeRoutine->getPropertyPart().appendVariableReturn($lp.label, $lp.arg);
		}
	    ( COMMA
	      lp=labelled_argument
	      {
			invokeRoutine->getPropertyPart().appendVariableReturn($lp.label, $lp.arg);
	      }
	    )*
	    RPAREN

	  | lp=labelled_argument
		{
			invokeRoutine->getPropertyPart().appendVariableReturn($lp.label, $lp.arg);
		}
	  )
	;


////////////////////////////////////////////////////////////////////////////////
// STATEMENT LEM
////////////////////////////////////////////////////////////////////////////////
/*
statement_lem
returns [ sep::BFCode ac ]
	: 'when'  { $ac = NEW_STMT(OP(LEM_WHEN)); }
	  ( e=expression      { $ac->append($e.bf); }  )?
	  bs=block_statement  { $ac->append($bs.ac); }
	  ( e=expression      { $ac->append($e.bf); }  )?
	  SEMI

	| 'in'  id=qualifiedNameID
	  { $ac = NEW_STMT1(OP(LEM_INPUT),
		sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }
	  ( 'provided'  e=expression  { $ac->append($e.bf); }  )?
	  SEMI

	| id=qualifiedNameID  LEM_TRANSFERT  id2=qualifiedNameID  SEMI
	{ $ac = NEW_STMT2(OP(LEM_OUTPUT),
		sep::ParserUtil::getvarPortSignal($id.s, $id.nb),
		sep::ParserUtil::getvarPortSignal($id2.s, $id2.nb)); }
	;

expression_lem
returns [ sep::BFCode ac ]
	: 'touch'  id=qualifiedNameID
	{ $ac = NEW_STMT1(OP(LEM_TOUCH),
		sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }

	| 'in'  id=qualifiedNameID
	{ $ac = NEW_STMT1(OP(LEM_INPUT),
		sep::ParserUtil::getvarPortSignal($id.s, $id.nb)); }
	  ( 'provided'  e=expression  { $ac->append($e.bf); }  )?
	;
*/

////////////////////////////////////////////////////////////////////////////////
// STATEMENT MOC
////////////////////////////////////////////////////////////////////////////////

statement_moc
returns [ sep::BFCode ac ]
	: 'step_mark'  StringLiteral  SEMI
	{
		$ac = NEW_STMT1(OP(STEP_MARK),
			NEW_STRING($StringLiteral->getText()));
	}
	;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// EXPRESSION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

expression
returns [ sep::BF bf ]
	: ce=conditionalExpression  { $bf = $ce.bf; }

	( ASSIGN  e=expression
	{ $bf = NEW_CODE2(OP(ASSIGN), $bf, $e.bf); }

	| ASSIGN_MACRO  e=expression
	{ $bf = NEW_CODE2(OP(ASSIGN_MACRO), $bf, $e.bf); }

	| ASSIGN_AFTER  e=expression
	{ $bf = NEW_CODE2(OP(ASSIGN_AFTER), $bf, $e.bf); }

	| PLUS_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(PLUS), $bf, $e.bf); }

	| PLUS_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(PLUS), $bf, $e.bf); }

	| MINUS_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(MINUS), $bf, $e.bf); }

	| MINUS_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(MINUS), $bf, $e.bf); }

	| STAR_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(MULT), $bf, $e.bf); }

	| STAR_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(MULT), $bf, $e.bf); }

	| DIV_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(DIV), $bf, $e.bf); }

	| DIV_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(DIV), $bf, $e.bf); }

	| MOD_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(MOD), $bf, $e.bf); }

	| MOD_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(MOD), $bf, $e.bf); }

	| LAND_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(AND), $bf, $e.bf); }

	| LAND_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(AND), $bf, $e.bf); }

	| LOR_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(OR), $bf, $e.bf); }

	| LOR_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(OR), $bf, $e.bf); }

	| BAND_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(BAND), $bf, $e.bf); }

	| BAND_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(BAND), $bf, $e.bf); }

	| BOR_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(BOR), $bf, $e.bf); }

	| BOR_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(BOR), $bf, $e.bf); }

	| BXOR_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(BXOR), $bf, $e.bf); }

	| BXOR_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(BXOR), $bf, $e.bf); }

	| LSHIFT_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(LSHIFT), $bf, $e.bf); }

	| LSHIFT_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(LSHIFT), $bf, $e.bf); }

	| RSHIFT_ASSIGN  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(RSHIFT), $bf, $e.bf); }

	| RSHIFT_ASSIGN_AFTER  e=expression
	{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(RSHIFT), $bf, $e.bf); }

	| OP_PUSH  e=expression
	{ $bf = NEW_CODE2(OP(PUSH), $bf, $e.bf); }

	| OP_ASSIGN_TOP  e=expression
	{ $bf = NEW_CODE2(OP(ASSIGN_TOP), $bf, $e.bf); }

	| OP_POP  e=expression
	{ $bf = NEW_CODE2(OP(POP), $bf, $e.bf); }

//	| LEM_TRANSFERT  e=expression
//	{ $bf = NEW_CODE2(OP(LEM_OUTPUT), $bf, $e.bf); }
	)?
	;


conditionalExpression
returns [ sep::BF bf ]
	: e=scheduleExpression  { $bf = $e.bf; }
	  ( QUESTION  th=expression  COLON  el=expression
	  { $bf = NEW_CODE3(OP(IFE), $bf, $th.bf, $el.bf); }
	  )?
	;

scheduleExpression
returns [ sep::BF bf ]
@init{
	const sep::Operator * op;
}
	: e=conditionalOrExpression  { $bf = $e.bf; }
	  ( ( os=op_sequence         { op = $os.op; }
	    | oh=op_scheduling       { op = $oh.op; }
		| oc=op_concurrency      { op = $oc.op; }
		)
	    e=conditionalOrExpression  { $bf = NEW_CODE_FLAT(op, $bf, $e.bf); }
	  )*
	;

conditionalOrExpression
returns [ sep::BF bf ]
	: e=conditionalImpliesExpression  { $bf = $e.bf; }
	  ( LOR e=conditionalImpliesExpression
	  { $bf = NEW_CODE_FLAT(OP(OR), $bf, $e.bf); }
	  )*
	;

conditionalImpliesExpression
returns [ sep::BF bf ]
	: e=conditionalAndExpression  { $bf = $e.bf; }
	  ( LIMPLIES e=conditionalAndExpression
	  { $bf = NEW_CODE_FLAT(OP(IMPLIES), $bf, $e.bf); }
	  )*
	;


conditionalAndExpression
returns [ sep::BF bf ]
	: e=bitwiseOrExpression  { $bf = $e.bf; }
	  ( LAND e=bitwiseOrExpression
	  { $bf = NEW_CODE_FLAT(OP(AND), $bf, $e.bf); }
	  )*
	;

bitwiseOrExpression
returns [ sep::BF bf ]
	: e=bitwiseXorExpression  { $bf = $e.bf; }
	  ( BOR e=bitwiseXorExpression
	  { $bf = NEW_CODE_FLAT(OP(BOR), $bf, $e.bf); }
	  )*
	;

bitwiseXorExpression
returns [ sep::BF bf ]
	: e=bitwiseAndExpression  { $bf = $e.bf; }
	  ( BXOR e=bitwiseAndExpression
	  { $bf = NEW_CODE_FLAT(OP(BXOR), $bf, $e.bf); }
	  )*
	;

bitwiseAndExpression
returns [ sep::BF bf ]
	: e=equalityExpression  { $bf = $e.bf; }
	  ( BAND e=equalityExpression
	  { $bf = NEW_CODE_FLAT(OP(BAND), $bf, $e.bf); }
	  )*
	;

equalityExpression
returns [ sep::BF bf ]
@init{
	sep::BFCode eqExpr;
	sep::BF rhs;
}
	: e=relationalExpression  { $bf = $e.bf; }
	  ( eq=equalOp e=relationalExpression
	  { eqExpr = NEW_CODE2($eq.op, $bf, $e.bf); }
	    ( eq=equalOp e=relationalExpression
		{
			/*if( eqExpr.getOperator() == $eq.op )
			{
				eqExpr.append( $e.bf );
			}
			else*/ if( eqExpr.getOperator() == OP(AND) )
			{
				eqExpr.append( NEW_CODE2($eq.op, rhs, $e.bf) );
			}
			else
			{
				eqExpr = NEW_CODE2(OP(AND), eqExpr, NEW_CODE2($eq.op, rhs, $e.bf));
			}

			rhs = $e.bf;
		}
	    )*
	  { $bf = eqExpr; }
	  )?
	;

equalOp
returns [ const sep::Operator * op ]
	: EQUAL   { $op = OP(EQ);   }
	| NEQUAL  { $op = OP(NEQ);  }
	| SEQUAL  { $op = OP(SEQ);  }
	| NSEQUAL { $op = OP(NSEQ); }
	;


relationalExpression
returns [ sep::BF bf ]
@init{
	sep::BFCode relExpr;
	sep::BF rhs;
}
	: e=shiftExpression  { $bf = $e.bf; }
	  ( r=relationalOp e=shiftExpression
	  { relExpr = NEW_CODE2($r.op, $bf, rhs = $e.bf); }
	    ( r=relationalOp e=shiftExpression
		{
			/*if( relExpr.getOperator() == $r.op )
			{
				relExpr.append( $e.bf );
			}
			else*/ if( relExpr.getOperator() == OP(AND) )
			{
				relExpr.append( NEW_CODE2($r.op, rhs, $e.bf) );
			}
			else
			{
				relExpr = NEW_CODE2(OP(AND), relExpr, NEW_CODE2($r.op, rhs, $e.bf));
			}

			rhs = $e.bf;
		}
	    )*
	  { $bf = relExpr; }
	  )?
	;

relationalOp
returns [ const sep::Operator * op ]
	: LTE  { $op = OP(LTE); }
	| GTE  { $op = OP(GTE); }
	| LT_  { $op = OP(LT); }
	| GT   { $op = OP(GT); }

	| 'in'       { $op = OP(IN); }
//	| 'notin'    { $op = OP(NOTIN); }
//	| 'contains' { $op = OP(CONTAINS); }
//
//	| 'subset'   { $op = OP(SUBSET); }
//
//	| 'starts_with' { $op = OP(STARTS_WITH); }
//	| 'ends_with'   { $op = OP(ENDS_WITH); }
	;

shiftExpression
returns [ sep::BF bf ]
	: e=additiveExpression  { $bf = $e.bf; }
	  ( s=shiftOp e=additiveExpression
	  { $bf = NEW_CODE2($s.op, $bf, $e.bf); }
	  )*
	;


shiftOp
returns [ const sep::Operator * op ]
	: LSHIFT  { $op = OP(LSHIFT); }
	| RSHIFT  { $op = OP(RSHIFT); }
	;


additiveExpression
returns [ sep::BF bf ]
@init{
	const sep::Operator * op = nullptr;
}
	: e=multiplicativeExpression  { $bf = $e.bf; }
	  ( ( PLUS  { op = OP(PLUS);  }
	    | MINUS { op = OP(MINUS); }
	    )
	    e=multiplicativeExpression
		{
			if( op == OP(MINUS) )
			{
				$bf = NEW_CODE_FLAT(OP(PLUS), $bf, new_uminus_expr($e.bf));
			}
			else
			{
				$bf = NEW_CODE_FLAT(op, $bf, $e.bf);
			}
		}
	  )*
	;

multiplicativeExpression
returns [ sep::BF bf ]
@init{
	const sep::Operator * op = nullptr;
}
	: e=unaryExpression  { $bf = $e.bf; }
	  ( ( STAR { op = OP(MULT); }
	    | DIV  { op = OP(DIV); }
	    | MOD  { op = OP(MOD); }
	    )
	    e=unaryExpression
		{ $bf = NEW_CODE_FLAT(op, $bf, $e.bf); }
	  )*
	;

/**
 * NOTE: for '+' and '-', if the next token is int or long interal, then it's not a unary expression.
 *       it's a literal with signed value. INTLTERAL AND LONG LITERAL are added here for this.
 */
unaryExpression
returns [ sep::BF bf ]
	: PLUS  e=unaryExpression
	{ $bf = $e.bf; }

	| MINUS e=unaryExpression
	{ $bf = new_uminus_expr($e.bf); }

	| INCR  e=unaryExpression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(PLUS),
		$e.bf, sep::ExpressionConstant::INTEGER_ONE); }
	| DECR  e=unaryExpression
	{ $bf = NEW_STMT_ASSIGN_OP(OP(PLUS), $e.bf,
		sep::ExpressionConstant::INTEGER_MINUS_ONE); }

	| LNOT e=unaryExpression
	{ $bf = new_not_expr($e.bf); }

	| BNOT e=unaryExpression
	{ $bf = NEW_CODE1(OP(BNOT), $e.bf); }

	| OP_POP   e=unaryExpression
	{ $bf = NEW_CODE1(OP(POP), $e.bf); }

	| OP_TOP   e=unaryExpression
	{ $bf = NEW_CODE1(OP(TOP), $e.bf); }

//	| 'newfresh'  e=unaryExpression
//	{ $bf = NEW_CODE1(OP(ASSIGN_NEWFRESH), $e.bf); }

	| pe=prefix_expression           { $bf = $pe.ac; }

	| ei=expression_invoke           { $bf = $ei.ac; }

	| ea=expression_activity_new     { $bf = $ea.ac; }

//	| eb=expression_buffer           { $bf = $eb.ac; }
	| ec=expression_com              { $bf = $ec.ac; }
	| ek=expression_checksat         { $bf = $ek.ac; }
	| eq=expression_quantifier       { $bf = $eq.ac; }
	| et=expression_ite              { $bf = $et.ac; }
	| el=expression_lambda           { $bf = $el.ac; }
//	| es=expression_status           { $bf = $es.ac; }
//	| et=expression_time             { $bf = $et.ac; }

//	| em=expression_lem              { $bf = $em.ac; }

	| ce=ctorExpression              { $bf = $ce.ctor; }

	| p=primary                      { $bf = $p.bf; }
	  ( INCR
		{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(PLUS), $p.bf,
			sep::ExpressionConstant::INTEGER_ONE); }
	  | DECR
		{ $bf = NEW_STMT_ASSIGN_OP_AFTER(OP(PLUS), $p.bf,
			sep::ExpressionConstant::INTEGER_MINUS_ONE); }
	  )?

	| l=literal                      { $bf = $l.bf; }

	| qe=quote_expression            { $bf = $qe.ac; }

	| me=meta_eval_expression        { $bf = $me.ac; }

	| LPAREN  le=expression  RPAREN  { $bf = $le.bf; }

	| co=collection_of_expression    { $bf = $co.bf; }
	;


ctorExpression
returns [ sep::BFCode ctor ]
	: 'ctor' LT_  tv=type_var  GT  LPAREN  e=expression  RPAREN
	{ $ctor = NEW_CODE2(OP(CTOR), $tv.type, $e.bf); }
	;


/*
quote_expression
returns [ sep::BFCode ac ]
@init{
	const sep::Operator * op = OP(SEQUENCE);
}
	: PERCENT_LCURLY  ( o=op_block { op = $o.op; } ) ?  { $ac = NEW_STMT(op); }
	    ( s=statement   { $ac->append($s.ac); }  )*
	    ( e=expression  { $ac->append($e.bf); }  )
	  RCURLY_PERCENT
	 { $ac = NEW_STMT1(OP(QUOTE), $ac); }
	;
*/


quote_expression
returns [ sep::BFCode ac ]
	: PERCENT_LCURLY  e=expression  RCURLY_PERCENT
	 { $ac = NEW_STMT1(OP(QUOTE), $e.bf); }
	;

meta_eval_expression
returns [ sep::BFCode ac ]
	: LBRACKET_BAR  e=expression  BAR_RBRACKET
	 { $ac = NEW_STMT1(OP(META_EVAL), $e.bf); }
	;



/**
 * have to use scope here, parameter passing isn't well supported in antlr.
 *
primary
returns [ sep::BF bf ]
@init{
	sep::UniFormIdentifier * ufi = new sep::UniFormIdentifier(false);
	sep::BF bfUfi( ufi );// for automatic destruction of << UFI >> if need

	std::size_t countID = 1;
	bool isnotEXPR  = true;
	bool hasnoPARAM = true;

	SAVE_RULE_BEGIN_LOCATION;
}
	: //( ( id=ID { ufi->setLocator($id->getText()); } )?
	  //  COLONx2 { ufi->setAbsolute(); } )?
	  id=ID
	  {
		if( ($bf = sep::ParserUtil::getObjectByNameID($id->getText())).valid() )
		{
			ufi->appendField($bf);
		}
		else
		{
			ufi->appendField($id->getText());
		}

		$bf = bfUfi;
	  }

	  ( ( DOT id=ID
		{ ufi->appendField($id->getText());  ++countID; } )

	  | ( LBRACKET  e=expression  RBRACKET
		{ ufi->appendIndex($e.bf);  isnotEXPR = false; }
	    )

	  | LPAREN            { ufi->last().addScheme(sep::UFI_SCHEME_INVOKABLE); }
	    ( e=expression    { ufi->appendFieldParameter($e.bf);  hasnoPARAM = false; }
	      ( COMMA
	        e=expression  { ufi->appendFieldParameter($e.bf);  hasnoPARAM = false; }
	      )*
	    )?
	    RPAREN
	  )*
	{
		if( countID == 1 )
		{
			$bf = ufi->first();
		}
		else if( isnotEXPR && hasnoPARAM )
		{
			if( ($bf = sep::ParserUtil::getvar(
					ufi->str(), countID)).invalid() )
			{
				$bf = bfUfi;
				SET_RULE_LOCATION(ufi);
			}
		}
		else if( ufi->singleton() )
		{
			$bf = ufi->first();
		}
	}
	;
*/


primary
returns [ sep::BF bf ]
	: id=ID
	  ( //!g4!( LPAREN ) =>
	    pi=primary_invoke[ $id->getText() ]
		{ $bf = $pi.bf; }

	  | //!g4!( DOT | LBRACKET ) =>
	    pu=primary_ufid[ $id->getText() ]
		{ $bf = $pu.bf; }
	  | //!g4!( COLONx2 ) =>
	    p=primary_ufi[ $id->getText() ]
		{ $bf = $p.bf; }
	  | //!g4!( COLONx2 ) =>
	  	p=primary_ufi[ $id->getText() ]
		{ $bf = $p.bf; }
	  )?
	  {
		if( $bf.invalid() )
		{
			if( ($bf = sep::ParserUtil::getObjectByNameID(
					$id->getText())).invalid() )
			{
				$bf = NEW_ID( $id->getText());
			}
		}
	  }

	| p=primary_ufi[ "" ]  { $bf = $p.bf; }
	;


primary_ufid [ std::string mainId ]
returns [ sep::BF bf ]
@init{
	sep::UniFormIdentifier * ufi = new sep::UniFormIdentifier(false);
	sep::BF bfUfi( ufi );// for automatic destruction of << UFI >> if need

	if( ($bf = sep::ParserUtil::getObjectByNameID(mainId)).valid() )
	{
		ufi->appendField( $bf );
	}
	else
	{
		ufi->appendField( mainId );
	}

	$bf = bfUfi;

	std::size_t countID = 1;
	bool isnotEXPR  = true;

	SAVE_RULE_BEGIN_LOCATION;
}
	: ( ( DOT id=ID
		{ ufi->appendField( $id->getText() );  ++countID; } )

	  | ( LBRACKET  e=expression  RBRACKET
		{ ufi->appendIndex( $e.bf );  isnotEXPR = false; }
	    )
	  )+
	{
		if( isnotEXPR )
		{
			if( ($bf = sep::ParserUtil::getvar(ufi->str(), countID)).invalid() )
			{
				$bf = bfUfi;
				SET_RULE_LOCATION( ufi );
			}
		}
	}
	;



primary_ufi [ std::string locatorId ]
returns [ sep::BF bf ]
@init{
	sep::UniFormIdentifier * ufi =
			new sep::UniFormIdentifier(not locatorId.empty());
	sep::BF bfUfi( ufi );// for automatic destruction of << UFI >> if need

	if( not locatorId.empty() )
	{
		ufi->setLocator( locatorId );
	}

	$bf = bfUfi;

	std::size_t countID = 1;
	bool isnotEXPR  = true;

	SAVE_RULE_BEGIN_LOCATION;
}
	: COLONx2 id=ID
	  {
		if( ($bf = sep::ParserUtil::getObjectByNameID($id->getText())).valid() )
		{
			ufi->appendField( $bf );
		}
		else
		{
			ufi->appendField( $id->getText() );
		}
	  }

	  ( ( DOT id=ID
		{ ufi->appendField( $id->getText() );  ++countID; } )

	  | ( LBRACKET  e=expression  RBRACKET
		{ ufi->appendIndex( $e.bf );  isnotEXPR = false; }
	    )
	  )+
	{
		if( isnotEXPR )
		{
			if( ($bf = sep::ParserUtil::getvar(ufi->str(), countID)).invalid() )
			{
				$bf = bfUfi;
				SET_RULE_LOCATION( ufi );
			}
		}
	}
	;


primary_invoke [ std::string mainId ]
returns [ sep::BF bf ]
@init{
	sep::Routine * invokeRoutine = sep::Routine::newInvoke( _CPRMS_, mainId);

	invokeRoutine->setModel( sep::ParserUtil::getvarRoutine(mainId) );

	SAVE_RULE_BEGIN_LOCATION;
}
@after
{
	SET_RULE_LOCATION( invokeRoutine );
}
	: LPAREN
	  ( lp=labelled_argument
		{
			invokeRoutine->getPropertyPart().appendVariableParameter($lp.label, $lp.arg);
		}
	    ( COMMA
	    lp=labelled_argument
		{
			invokeRoutine->getPropertyPart().appendVariableParameter($lp.label, $lp.arg);
		}
	    )*
	  )?
	  RPAREN

	  { $bf = sep::Routine::invokeRoutineExpression(invokeRoutine); }
	;


literal
returns [ sep::BF bf ]
	: IntegerLiteral  { $bf = NEW_INTEGER($IntegerLiteral->getText());   }
	| RationalLiteral { $bf = NEW_RATIONAL($RationalLiteral->getText()); }
	| FloatLiteral    { $bf = NEW_FLOAT($FloatLiteral->getText());       }

	| CharLiteral     { $bf = NEW_CHAR($CharLiteral->getText().at(0));     }
	| StringLiteral   { $bf = NEW_STRING($StringLiteral->getText()); }

	| 'true'   { $bf = NEW_BOOLEAN(true);  }
	| 'false'  { $bf = NEW_BOOLEAN(false); }

	| '$time'  { $bf = sep::ParserUtil::getVarTime();      }
	| '$delay' { $bf = sep::ParserUtil::getVarDeltaTime(); }
	| '$delta' { $bf = sep::ParserUtil::getVarDeltaTime(); }
	
	| ( '$self' | 'self' )  
	  { $bf = sep::ExecutableLib::MACHINE_SELF; }
	  ( ( ( LPAREN id=qualifiedNameID RPAREN )
	  | ( LT_ id=qualifiedNameID GT )
	  )
	  { $bf = NEW_CODE1(OP(SELF),
			sep::ParserUtil::getSelfExecutableMachine($id.s));   }
	  )?
	
	| ( '$this' | 'this' ) { $bf = sep::ExecutableLib::MACHINE_THIS;        }

	| ( '$env'  | 'env'  ) { $bf = sep::ExecutableLib::MACHINE_ENVIRONMENT; }

	| '$parent'     { $bf = sep::ExecutableLib::MACHINE_PARENT;    }
	| '$super'      { $bf = sep::ExecutableLib::MACHINE_PARENT;    }
	
	| '$system'     { $bf = sep::ExecutableLib::MACHINE_SYSTEM;    }

	| '$null' LT_
	   ( 'machine'  { $bf = sep::ExecutableLib::MACHINE_NULL;      }
	   | 'channel'  { $bf = sep::ExecutableLib::CHANNEL_NIL;       }
	   | 'port'     { $bf = sep::ExecutableLib::PORT_NIL;          }
	   | 'signal'   { $bf = sep::ExecutableLib::PORT_NIL;          }
	   | 'message'  { $bf = sep::ExecutableLib::PORT_NIL;          }
	   | 'buffer'   { $bf = sep::ExecutableLib::BUFFER_NIL;        }
	   ) GT

	| '$any'        { $bf = sep::ExecutableLib::ANY_VALUE;         }
	| '$default'    { $bf = sep::ExecutableLib::DEFAULT_VALUE;     }
	| '$optional'   { $bf = sep::ExecutableLib::OPTIONAL_VALUE;    }
	| '$omit'       { $bf = sep::ExecutableLib::OMIT_VALUE;        }
	| '$none'       { $bf = sep::ExecutableLib::NONE_VALUE;        }
	| '$any$none'   { $bf = sep::ExecutableLib::ANY_OR_NONE_VALUE; }
	;



collection_of_expression
returns [ sep::BF bf ]
@init{
	sep::BFVector values;
}
	: LCURLY
	    e=expression          { values.append($e.bf); }
	    ( COMMA e=expression  { values.append($e.bf); } )*
	  RCURLY
	  {  $bf = sep::BuiltinArray::create(values); }

	| LBRACKET
	    e=expression          { values.append($e.bf); }
	    ( COMMA e=expression  { values.append($e.bf); } )*
	  RBRACKET
	  { $bf = sep::BuiltinArray::create(values); }
	;


////////////////////////////////////////////////////////////////////////////////
///// KEYWORD XLIA or XFSP
////////////////////////////////////////////////////////////////////////////////
/*
kw_start     : { IS_KEYWORD( "start"    ) }?  ID;

kw_in        : { IS_KEYWORD( "in"       ) }?  ID;

kw_input     : { IS_KEYWORD( "input"    ) }?  ID;
kw_output    : { IS_KEYWORD( "output"   ) }?  ID;

kw_wait      : { IS_KEYWORD( "wait"     ) }?  ID;
*/


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// LEXER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


OP_ATOMIC_SEQUENCE              : '|§|'  ;

OP_SEQUENCE                     : '|;|'  ;
OP_SEQUENCE_SIDE                : '|.|'  | '|/;|' ;
OP_SEQUENCE_WEAK                : '|;;|' ;

OP_SCHEDULE_GT                  : '|>|'   ;
OP_SCHEDULE_LT                  : '|<|'   ;
OP_SCHEDULE_XOR                 : '|xor|' ;

OP_SCHEDULE_AND_THEN            : '|and#then|' ;
OP_SCHEDULE_OR_ELSE             : '|or#else|'  ;


OP_NON_DETERMINISM              : '|/\\|' | '|indet|' ;

OP_CONCURRENCY_ASYNC            : '|a|'   | '|async|' ;

OP_CONCURRENCY_AND              : '|and|' | '|strong_sync|';
OP_CONCURRENCY_OR               : '|or|'  | '|weak_sync|'  ;

OP_CONCURRENCY_INTERLEAVING     : '|i|'   | '|<>|' | '|interleaving|'  ;
OP_CONCURRENCY_PARTIAL_ORDER    : '|~|'   | '|><|' | '|partial-order|' ;

OP_CONCURRENCY_PARALLEL         : '|,|'   | '|parallel|' ;

OP_FORK                         : '|fork|'  ;
OP_JOIN                         : '|join|'  ;


OP_CONCURRENCY_RDV_ASYNC        : '||a||'   ;
OP_CONCURRENCY_RDV_AND          : '||and||' ;
OP_CONCURRENCY_RDV_OR           : '||or||'  ;
OP_CONCURRENCY_RDV_INTERLEAVING : '||i||'   ;
OP_CONCURRENCY_RDV_PARTIAL_ORDER: '||~||'   ;
OP_CONCURRENCY_RDV_PARALLEL     : '||,||'   ;

//LEM_TRANSFERT                 : '->'  ;

ASSIGN                          : '='   | ':=' ;
ASSIGN_AFTER                    : '=:'  ;
ASSIGN_REF                      : '<-'  ;
ASSIGN_MACRO                    : '::=' ;

OP_PUSH                         : '<=<' ;
OP_ASSIGN_TOP                   : '^=<' ;
OP_TOP                          : '^=>' ;
OP_POP                          : '>=>' ;

LPAREN                          : '('   ;
RPAREN                          : ')'   ;
LCURLY                          : '{'   ;
RCURLY                          : '}'   ;
LBRACKET                        : '['   ;
RBRACKET                        : ']'   ;

LBRACKET_EXCEPT                 : '[^'  ;

LPAREN_INVOKE                   : '(:'  ;
LCURLY_INVOKE                   : '{:'  ;

PERCENT_LPAREN_INVOKE           : '%(:'  ;

PERCENT_LPAREN                  : '%('  ;
RPAREN_PERCENT                  : ')%'  ;


STATEMENT_PROMPT                : ':>'  ;

DOLLAR_LCURLY                   : '${'  ;
RCURLY_DOLLAR                   : '}$'  ;

PERCENT_LCURLY                  : '%{'  ;
RCURLY_PERCENT                  : '}%'  ;

LBRACKET_BAR                    : '[|'  ;
BAR_RBRACKET                    : '|]'  ;

LBRACKET_LCURLY                 : '[{'  ;
RCURLY_RBRACKET                 : '}]'  ;

COLON                           : ':'   ;
COMMA                           : ','   ;
QUESTION                        : '?'   ;
SEMI                            : ';'   ;

DIESE                           : '#'   ;
DOLLAR                          : '$'   ;

DOT                             : '.'   ;
DOTDOT                          : '..'  ;
COLONx2                         : '::'  ;


LAND                            : '&&'  | 'and' ;
LAND_THEN                       : 'and#then'    ;
LAND_ASSIGN                     : '&&=' | '&&:=';
LAND_ASSIGN_AFTER               : '&&=:';

LNOT                            : '!'   | 'not' ;

LOR                             : '||'  | 'or'  ;
LOR_ELSE                        : 'or#else'     ;
LOR_ASSIGN                      : '||=' | '||:=';
LOR_ASSIGN_AFTER                : '||=:';
LXOR                            : 'xor' ;

LIMPLIES                        : '=>'  ;

EQUAL                           : '=='  ;
NEQUAL                          : '!='  ;

SEQUAL                          : '===' ;
NSEQUAL                         : '=!=' | '=/=' ;

LTE                             : '<='  ;
LT_                             : '<'   ;
GTE                             : '>='  ;
GT                              : '>'   ;


PLUS                            : '+'   ;
PLUS_ASSIGN                     : '+='  | '+:=' ;
PLUS_ASSIGN_AFTER               : '+=:' ;
INCR                            : '++'  ;

MINUS                           : '-'   ;
MINUS_ASSIGN                    : '-='  | '-:=' ;
MINUS_ASSIGN_AFTER              : '-=:' ;
DECR                            : '--'  ;

STAR                            : '*'   ;
STAR_ASSIGN                     : '*='  | '*:=' ;
STAR_ASSIGN_AFTER               : '*=:' ;
DIV                             : '/'   ;
DIV_ASSIGN                      : '/='  | '/:=' ;
DIV_ASSIGN_AFTER                : '/=:' ;
MOD                             : '%'   ;
MOD_ASSIGN                      : '%='  | '%:=' ;
MOD_ASSIGN_AFTER                : '%=:' ;

//POW                           : "**" ;

RSHIFT                          : '>>'  ;
RSHIFT_ASSIGN                   : '>>=' | '>>:=';
RSHIFT_ASSIGN_AFTER             : '>>=:';
LSHIFT                          : '<<'  ;
LSHIFT_ASSIGN                   : '<<=' | '<<:=';
LSHIFT_ASSIGN_AFTER             : '<<=:';

BAND                            : '&'   ;
BAND_ASSIGN                     : '&='  | '&:=' ;
BAND_ASSIGN_AFTER               : '&=:' ;
BNOT                            : '~'   ;
BOR                             : '|'   ;
BOR_ASSIGN                      : '|='  | '|:=' ;
BOR_ASSIGN_AFTER                : '|=:' ;
BXOR                            : '^'   ;
BXOR_ASSIGN                     : '^='  | '^:=' ;
BXOR_ASSIGN_AFTER               : '^=:' ;


ID
	: ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'#')*
	;


AT_ID
	: '@' ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'#'|'$')*
	{ setText( getText().substr(1) ); }
	;


StringLiteral
	: '"'  ( ESC_SEQUENCE | ~('\\'|'"') )*  '"'
	{ 
		if( getText().size() < 3 )   { setText( "" ); }
		else { setText( getText().substr(1, getText().length() - 2) ); }
	}
	;

CharLiteral
	: '\''  ( ESC_SEQUENCE | ~('\''|'\\') )  '\''
	{ setText( std::string( 1 , getText().at(1) ) ); }
	;


FloatLiteral
	: FractionalConstant DecimalExponent? FloatingSuffix?
	| DecimalDigits DecimalExponent DecimalDigits?
	;

RationalLiteral : IntegerLiteral  DIV  Integer;

IntegerLiteral  : Integer IntSuffix?;

// fragments
fragment FloatingSuffix : 'f' | 'l' | 'F' | 'L';
fragment IntSuffix       : 'L'|'u'|'U'|'Lu'|'LU'|'uL'|'UL' ;

fragment Integer         : Decimal | Binary | Octal | Hexadecimal ;
fragment Decimal         : '0' | '1'..'9' (DecimalDigit | '_')* ;

fragment Binary          : ('0b' | '0B') ('0' | '1' | '_')+ ;
fragment Octal           : '0' (OctalDigit | '_')+ ;
fragment Hexadecimal     : ('0x' | '0X') (HexDigit | '_')+;

fragment DecimalDigit    : '0'..'9' ;
fragment OctalDigit      : '0'..'7' ;
fragment HexDigit        : ('0'..'9'|'a'..'f'|'A'..'F') ;

fragment DecimalExponent : ('e'|'E') ('+'|'-')? DecimalDigits;
fragment DecimalDigits   : ( '0'..'9' | '_')+ ;

fragment FractionalConstant
	: DecimalDigits? '.' DecimalDigits
	| DecimalDigits '.'
	;


fragment
EXPONENT
	: ('e'|'E')  ('+'|'-')?  ('0'..'9')+
	;

fragment
HEX_DIGIT
	: ('0'..'9' | 'a'..'f' | 'A'..'F')
	;

fragment
ESC_SEQUENCE
	: '\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')
	| UNICODE_ESCAPE
	| OCTAL_ESCAPE
	;

fragment
OCTAL_ESCAPE
	: '\\' ('0'..'3')  ('0'..'7')  ('0'..'7')
	| '\\' ('0'..'7')  ('0'..'7')
	| '\\' ('0'..'7')
	;

fragment
UNICODE_ESCAPE
	: '\\' 'u' HEX_DIGIT  HEX_DIGIT  HEX_DIGIT  HEX_DIGIT
	;


WHITESPACE
	: [ \t]+              -> skip;

NEWLINE
	: ('\r' '\n'? | '\n') -> skip;

BLOCKCOMMENT
	: '/*' .*? '*/'       -> skip;

LINECOMMENT
	: '//' ~ [\r\n]*      -> skip;

/* end CPP */

