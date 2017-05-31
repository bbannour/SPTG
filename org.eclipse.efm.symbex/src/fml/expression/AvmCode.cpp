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
 ******************************************************************************/
#include "AvmCode.h"

#include <fml/common/BehavioralElement.h>
#include <fml/common/ObjectElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/BaseCompiledForm.h>
#include <fml/executable/BaseInstanceForm.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/builtin/BuiltinForm.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>


namespace sep
{


/**
 * DEFAULT NULL
 */
BFCode BFCode::REF_NULL;


/**
 * COMPARISON
 * OPERATOR
 */
int AvmCode::compare(const AvmCode & other) const
{
	if( this == &other )
	{
		return( 0 );
	}
	else if( sameOperator( other ) )
	{
		int  cmpResult = 0;

		AvmCode::const_iterator it = begin();
		AvmCode::const_iterator endIt = end();

		AvmCode::const_iterator itOther = other.begin();
		AvmCode::const_iterator endOther = other.end();

		for( ; (it != endIt) && (itOther != endOther) ; ++it , ++itOther )
		{
			cmpResult = (*it).compare( *itOther );
			if( cmpResult != 0  )
			{
				return( cmpResult );
			}
		}

		return( (size() == other.size()) ? 0 :
				((size() < other.size()) ? -1 : 1) );
	}
	else
	{
		return( (getAvmOpCode() < other.getAvmOpCode()) ? -1 : 1 );
	}
}

bool AvmCode::isEQ(const AvmCode & other) const
{
	if( this == &other )
	{
		return( true );
	}
	else if( sameOperator( other ) && (size() == other.size()) )
	{
		AvmCode::const_iterator it = begin();
		AvmCode::const_iterator endIt = end();
		AvmCode::const_iterator itOther = other.begin();
		for(  ; it != endIt ; ++it , ++itOther )
		{
			if( not (*it).isEQ( *itOther ) )
			{
				return( false );
			}
		}
		return( true );
	}
	else
	{
		return( false );
	}
}


/**
 * AvmCode::toStream
 * Serialization
 */
OutStream & AvmCode::toDebug(OutStream & out) const
{
AVM_IF_DEBUG_NOT_FLAG_AND( BYTECODE , hasInstruction() )

	AVM_DEBUG_ENABLE_FLAG( BYTECODE )

	toStreamWithBytecode( out << TAB << "$" ) << EOL_FLUSH;

	AVM_DEBUG_DISABLE_FLAG( BYTECODE )

AVM_ELSE

	toStream(out);

AVM_ENDIF_DEBUG_NOT_FLAG_AND( BYTECODE )

	return( out );
}


void AvmCode::toStreamPrefix(OutStream & out, const BF & arg)
{
	if( arg.invalid() )
	{
		out << TAB << "null<avmcode::arg>" << EOL;
	}

	else if( arg.is< BuiltinForm >() )
	{
		out << TAB << arg.to_ptr< BuiltinForm >()->str() << EOL;
	}

	else if( arg.is< Operator >() )
	{
		out << TAB << arg.to_ptr< Operator >()->standardSymbol();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< Routine >() )
	{
		arg.to_ptr< Routine >()->toStreamInvoke(out);
	}

	else if( arg.is< PropertyElement >() )
	{
		out << TAB << "&"
			<< arg.to_ptr< PropertyElement >()->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< BaseInstanceForm >() )
	{
		out << TAB
			<< arg.to_ptr< BaseInstanceForm >()->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< BehavioralElement >() )
	{
		out << TAB << "&"
			<< arg.to_ptr< BehavioralElement >()->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( WObjectManager::is( arg ) )
	{
		out << TAB << "&"
			<< WObjectManager::from( arg )->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< RuntimeID >() )
	{
		out << TAB << arg.bfRID().str() << EOL;
	}

	else if( arg.is_exactly< AvmProgram >() )
	{
		AvmProgram * aProg = arg.to_ptr< AvmProgram >();
		if( aProg->isAnonym() )
		{
			aProg->toStream(out);
		}
		else
		{
			out << TAB << aProg->getFullyQualifiedNameID();
			arg.AVM_DEBUG_REF_COUNTER(out);
			out << EOL;
		}
	}
	else if( arg.is< BaseAvmProgram >() )
	{
		out << TAB
			<< arg.to_ptr< BaseAvmProgram >()->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< BaseTypeSpecifier >() )
	{
		out << TAB
			<< arg.to_ptr< BaseTypeSpecifier >()->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< ObjectElement >() )
	{
		out << TAB << "&"
			<< arg.to_ptr< ObjectElement >()->getFullyQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< BuiltinArray >() )
	{
		arg.to_ptr< BuiltinArray >()->toStream(out);
	}

	else if ( arg.is< AvmCode >() )
	{
		arg.to_ptr< AvmCode >()->toStreamPrefix(out);
	}

	else
	{
		out << arg;
	}

	out << std::flush;
}


OutStream & AvmCode::toStreamWithBytecode(OutStream & out) const
{
	out << "{ " << strOperator() << " "
		<< mInstruction->getMainBytecode().strCode()
		<< EOL_INCR_INDENT;

	if( nonempty() )
	{
		const_iterator it = begin();
		const_iterator itEnd = end();
		for( avm_size_t argOffset = 0 ; it != itEnd ; ++it , ++argOffset )
		{
			out << TAB << "$( " << mInstruction->at(argOffset).strCode();

			if( (*it).is< AvmCode >() )
			{
				out << " ";

				if( (*it).to_ptr< AvmCode >()->hasInstruction() )
				{
					(*it).to_ptr< AvmCode >()->toStreamWithBytecode(out);
				}
				else
				{
					(*it).to_ptr< AvmCode >()->toStreamPrefix(
							out << IGNORE_FIRST_TAB, false );
				}
			}
			else
			{
				ScopeNewIndent asni(out, AVM_STR_INDENT);

				toStreamPrefix( out , (*it) );
			}
			out << " )" << EOL;
		}
	}

	out << DECR_INDENT_TAB << "}" << std::flush;

	return( out );
}


OutStream & AvmCode::toStreamRoutine(OutStream & out) const
{
AVM_IF_DEBUG_FLAG( BYTECODE )

	if( hasInstruction() )
	{
		toStreamWithBytecode( out << "$" ) << EOL_FLUSH;
	}
	else if( OperatorManager::isSchedule(mOperator) )
	{
		out << " " << strOperator() << EOL;

		AvmCode::const_iterator it = begin();
		AvmCode::const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			toStreamPrefix(out, (*it));
		}
	}
	else
	{
		toStreamPrefix( out << EOL );
	}

	return( out );

AVM_ENDIF_DEBUG_FLAG( BYTECODE )

	if( OperatorManager::isSchedule(mOperator) )
	{
		out << " " << strOperator() << EOL;

		AvmCode::const_iterator it = begin();
		AvmCode::const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			prettyPrinter(out, (*it));
		}
	}
	else
	{
		prettyPrinter( out << EOL );
	}

	return( out );
}


void AvmCode::toStreamPrefix(OutStream & out, bool printEOL) const
{
AVM_IF_DEBUG_FLAG_AND( BYTECODE , hasInstruction() )

	toStreamWithBytecode( out << TAB << "$" ) << EOL_FLUSH;

AVM_ELSE_IF( hasOperator() )

	std::string strOperatorStd = strOperator();

	out << TAB << "${" << strOperatorStd;

	if( OperatorManager::isSchedule( mOperator ) ||
		OperatorManager::isConditionnal( mOperator ) )
	{
		out << EOL_INCR_INDENT;
		for( const_iterator it = begin() ; it != end() ; ++it )
		{
			toStreamPrefix(out, (*it));
		}
		out << DECR_INDENT_TAB <<  "}" << std::flush;
	}

	else if( OperatorManager::isActivity( mOperator )
			&& populated()
			&& second().is< AvmCode >()
			&& StatementTypeChecker::isAssign( second() ) )
	{
		const_iterator it = begin();
		toStreamPrefix( (out << AVM_STR_INDENT), (*it) );
		out << END_INDENT << EOL_INCR_INDENT;
		for( ++it ; it != end() ; ++it )
		{
			toStreamPrefix(out, (*it));
		}
		out << DECR_INDENT_TAB <<  "}" << std::flush;
	}

	else //if( OperatorManager::isUfiOrCtor( mOperator ) )
	{
		out << AVM_STR_INDENT;
		for( const_iterator it = begin() ; it != end() ; ++it )
		{
			toStreamPrefix(out, (*it));
		}
		out << END_INDENT <<  " }" << std::flush;
	}

	if( printEOL )
	{
		out << EOL_FLUSH;
	}

	return;

AVM_ELSE_IF( nonempty() )

	out << TAB << "{" << EOL_INCR_INDENT;
	for( const_iterator it = begin() ; it != end() ; ++it )
	{
		toStreamPrefix(out, (*it));
	}
	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;

AVM_ENDIF_DEBUG_FLAG_AND( BYTECODE )
}



void AvmCode::prettyPrinter(OutStream & out, bool isStatement) const
{
//	switch( mOperator->getFixNotation() )
//	{
//		case NOTATION_FUNCTION:
//		case NOTATION_INFIX:
//		case NOTATION_PREFIX:
//		case NOTATION_SUFFIX:
//		default:
//	}

	switch( mOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_NULL:

		// AVM NOP STATEMENT
		case AVM_OPCODE_NOP:

		case AVM_OPCODE_FAILED:
		case AVM_OPCODE_THROW:

		// AVM META STATEMENT
		case AVM_OPCODE_INFORMAL:

		case AVM_OPCODE_TRACE:

		case AVM_OPCODE_DEBUG:

		case AVM_OPCODE_COMMENT:

		case AVM_OPCODE_QUOTE:

		case AVM_OPCODE_META_EVAL:
		case AVM_OPCODE_META_RUN:
		{
			prettyPrinterBasicStatement( out , isStatement );

			break;
		}

		// AVM UFI STATEMENT
		case AVM_OPCODE_UFI:
		{
			prettyPrinterDefault( out , false );

			break;
		}

		// AVM FORM CONSTRUCTOR STATEMENT
		case AVM_OPCODE_CTOR:
		{
			out << TAB << "ctor<" << AVM_STR_INDENT;

			prettyPrinter( out , first() , false );

			out << " >(";

			prettyPrinter( out , second() , false );

			out << " )" << END_INDENT_EOL;

			break;
		}

		// AVM FORM REGEX STATEMENT
		case AVM_OPCODE_REGEX:
		{
			prettyPrinterDefault( out , false );

			break;
		}

		// AVM MACHINE MANAGING
		case AVM_OPCODE_CONTEXT_SWITCHER:
		{
			out << TAB << "ctx<" << AVM_STR_INDENT;

			prettyPrinter( out , first() , false );

			out << TAB << "> " << END_INDENT << IGNORE_FIRST_TAB;

			prettyPrinter( out , second() , isStatement );

			break;
		}

		case AVM_OPCODE_INIT:
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		case AVM_OPCODE_STOP:

		case AVM_OPCODE_WAIT:

		case AVM_OPCODE_SUSPEND:
		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_SET:
		case AVM_OPCODE_DISABLE_CHILD:
		case AVM_OPCODE_DISABLE_SELF:
		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		case AVM_OPCODE_ABORT_SET:
		case AVM_OPCODE_ABORT_CHILD:
		case AVM_OPCODE_ABORT_SELF:
		case AVM_OPCODE_ABORT_SELVES:

		case AVM_OPCODE_HISTORY_CLEAR:
		case AVM_OPCODE_DEEP_HISTORY_INVOKE:
		case AVM_OPCODE_SHALLOW_HISTORY_INVOKE:

		case AVM_OPCODE_IRUN:
		case AVM_OPCODE_RUN:
		case AVM_OPCODE_RTC:

		case AVM_OPCODE_SCHEDULE_INVOKE:
		case AVM_OPCODE_SCHEDULE_GET:
		case AVM_OPCODE_SCHEDULE_IN:
		case AVM_OPCODE_SCHEDULE_SET:

		case AVM_OPCODE_DEFER_INVOKE:
		case AVM_OPCODE_DEFER_GET:
		case AVM_OPCODE_DEFER_SET:

		case AVM_OPCODE_GOTO:
		{
			prettyPrinterBasicStatement( out , isStatement );

			break;
		}

		case AVM_OPCODE_FORK:
		case AVM_OPCODE_JOIN:

		case AVM_OPCODE_INPUT_ENABLED:

		case AVM_OPCODE_RDV:

		case AVM_OPCODE_SYNCHRONIZE:
		{
			prettyPrinterDefault( out , isStatement );

			break;
		}

		case AVM_OPCODE_INVOKE_NEW:

		case AVM_OPCODE_INVOKE_ROUTINE:

		case AVM_OPCODE_INVOKE_TRANSITION:

		case AVM_OPCODE_INVOKE_METHOD:
		case AVM_OPCODE_INVOKE_PROGRAM:
		case AVM_OPCODE_INVOKE_FUNCTION:

		case AVM_OPCODE_INVOKE_LAMBDA_APPLY:
		case AVM_OPCODE_INVOKE_LAMBDA_LET:
		{
			prettyPrinterBasicStatement( out , isStatement );

			break;
		}

		// AVM MACHINE STATUS
		case AVM_OPCODE_STATUS_WAS:
		case AVM_OPCODE_STATUS_IS:
		case AVM_OPCODE_STATUS_BEING:
		case AVM_OPCODE_STATUS_WILL:

		case AVM_OPCODE_CHANGED:
		case AVM_OPCODE_CHANGED_TO:
		{
			prettyPrinterDefault( out , isStatement );

			break;
		}


		// AVM PROGRAM SCHEDULING
		case AVM_OPCODE_ASYNCHRONOUS:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:

		case AVM_OPCODE_INTERLEAVING:
		case AVM_OPCODE_PARTIAL_ORDER_REDUCTION:

		case AVM_OPCODE_PARALLEL:

		// Optimized version of concurrency for RDV synchronization
		case AVM_OPCODE_RDV_ASYNCHRONOUS:
		case AVM_OPCODE_RDV_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_RDV_WEAK_SYNCHRONOUS:

		case AVM_OPCODE_RDV_INTERLEAVING:
		case AVM_OPCODE_RDV_PARTIAL_ORDER_REDUCTION:

		case AVM_OPCODE_RDV_PARALLEL:

		case AVM_OPCODE_EXCLUSIVE:

		case AVM_OPCODE_NONDETERMINISM:

		case AVM_OPCODE_PRIOR_GT:
		case AVM_OPCODE_PRIOR_LT:

		case AVM_OPCODE_SCHEDULE_AND_THEN:
		case AVM_OPCODE_SCHEDULE_OR_ELSE:

		case AVM_OPCODE_ATOMIC_SEQUENCE:

		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_SIDE:
		case AVM_OPCODE_SEQUENCE_WEAK:

		case AVM_OPCODE_PRODUCT:

		// AVM BUFFER MANAGING
		case AVM_OPCODE_UPDATE_BUFFER:
		{
			prettyPrinterBlockStatement( out , isStatement );

			break;
		}

		// LAMBDA STATEMENT
		case AVM_OPCODE_APPLY:

		case AVM_OPCODE_LAMBDA:

		// FUNCTIONB STATEMENT
		case AVM_OPCODE_FUN:


		// LET STATEMENT
		case AVM_OPCODE_LET:
		{
			prettyPrinterDefault( out , isStatement );

			break;
		}

		// LOOKUP STATEMENT
		case AVM_OPCODE_LOOKUP_INT_EXT:
		case AVM_OPCODE_LOOKUP_INT:
		case AVM_OPCODE_LOOKUP_NEAREST:
		case AVM_OPCODE_LOOKUP_BELOW:
		case AVM_OPCODE_LOOKUP_ABOVE:
		case AVM_OPCODE_LOOKUP2D_INT_EXT:
		{
			prettyPrinterFunctional( out );

			break;
		}

		// AVM PRIMITIVE STATEMENT
		case AVM_OPCODE_ASSIGN:
		case AVM_OPCODE_ASSIGN_AFTER:
		case AVM_OPCODE_ASSIGN_OP:
		case AVM_OPCODE_ASSIGN_OP_AFTER:
		case AVM_OPCODE_ASSIGN_REF:
		case AVM_OPCODE_ASSIGN_MACRO:
		{
			out << TAB << AVM_STR_INDENT;

			AvmCode::const_iterator it = begin();
			AvmCode::const_iterator endIt = end();

			prettyPrinter(out, (*it), false);

			BaseTypeSpecifier * aType = (*it).is< InstanceOfData >() ?
				(*it).to_ptr< InstanceOfData >()->getTypeSpecifier() : NULL;

			for( ++it ; it != endIt ; ++it )
			{
				out << TAB << strOperator();

				prettyPrinter(out, (*it), aType);
			}

			( isStatement ? (out << ";") : out ) << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_ASSIGN_NEWFRESH:
		case AVM_OPCODE_ASSIGN_RESET:
		{
			prettyPrinterFunctional( out );

			break;
		}

		case AVM_OPCODE_GUARD:
		case AVM_OPCODE_TIMED_GUARD:

		case AVM_OPCODE_EVENT:

		case AVM_OPCODE_CHECK_SAT:
		{
			prettyPrinterBasicStatement( out , isStatement );

			break;
		}

		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_FROM:

		case AVM_OPCODE_INPUT_SAVE:

		// Optimized version of INPUT
		case AVM_OPCODE_INPUT_ENV:
		case AVM_OPCODE_INPUT_VAR:
		case AVM_OPCODE_INPUT_FLOW:
		case AVM_OPCODE_INPUT_BUFFER:
		case AVM_OPCODE_INPUT_RDV:
		case AVM_OPCODE_INPUT_MULTI_RDV:
		case AVM_OPCODE_INPUT_BROADCAST:
		case AVM_OPCODE_INPUT_DELEGATE:

		case AVM_OPCODE_OUTPUT:
		case AVM_OPCODE_OUTPUT_TO:
		// Optimized version of OUTPUT
		case AVM_OPCODE_OUTPUT_ENV:
		case AVM_OPCODE_OUTPUT_VAR:
		case AVM_OPCODE_OUTPUT_FLOW:
		case AVM_OPCODE_OUTPUT_BUFFER:
		case AVM_OPCODE_OUTPUT_RDV:
		case AVM_OPCODE_OUTPUT_MULTI_RDV:
		case AVM_OPCODE_OUTPUT_BROADCAST:
		case AVM_OPCODE_OUTPUT_DELEGATE:
		{
			out << TAB << strOperator() << " " << AVM_NO_INDENT;

			prettyPrinter(out, first(), false);

			if( populated() )
			{
				AvmCode::const_iterator it = begin();
				AvmCode::const_iterator endIt = end();

				out << "(";

				prettyPrinter(out, *(++it), false);

				for( ++it ; it != endIt ; ++it )
				{
					out << ", ";
					prettyPrinter(out, (*it), false);
				}

				out << ")";
			}

			out << ";" << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_PRESENT:
		case AVM_OPCODE_ABSENT:
		{
			out << TAB << strOperator() << " " << AVM_NO_INDENT;

			prettyPrinter(out, first(), false);

			if( populated() )
			{
				AvmCode::const_iterator it = begin();
				AvmCode::const_iterator endIt = end();

				out << "(";

				prettyPrinter(out, *(++it), false);

				for( ++it ; it != endIt ; ++it )
				{
					out << ", ";
					prettyPrinter(out, (*it), false);
				}

				out << ")";
			}

			( isStatement ? (out << ";") : out ) << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_IF:
		{
			out << TAB << "if";

			prettyPrinterCondition( out , first() );

			prettyPrinterBlock( out << EOL , second() );

			break;
		}
		case AVM_OPCODE_IFE:
		{
			out << TAB << "if";

			prettyPrinterCondition( out , first() );

			prettyPrinterBlock( out << EOL , second() );

			out << TAB << "else" << EOL;

			prettyPrinterBlock( out , third() );

			break;
		}

		case AVM_OPCODE_WHERE:
		{
			out << TAB << "where";

			prettyPrinterCondition( out , first() );

			prettyPrinterBlock( out << EOL , second() );

			break;
		}
		case AVM_OPCODE_WHERE_ELSE:
		{
			prettyPrinterCondition( out << TAB << "where" , first() );

			prettyPrinterBlock( out << EOL , second() );

			prettyPrinterBlock( out << TAB << "else" << EOL , third() );

			break;
		}

		case AVM_OPCODE_FOR:
		{
			out << TAB << "for( " << AVM_NO_INDENT;

			prettyPrinter( out , first() , false );
			out << " ; ";
			prettyPrinter( out , second() , false );
			out << " ; ";
			prettyPrinter( out , third() , false );

			out << " )" << END_INDENT_EOL;

			prettyPrinterBlock( out , fourth() );

			break;
		}

		case AVM_OPCODE_FOREACH:
		{
			out << TAB << "for( " << AVM_NO_INDENT;

			prettyPrinter( out , first() , false );
			out << " : ";
			prettyPrinter( out , second() , false );

			out << " )" << END_INDENT_EOL;

			prettyPrinterBlock( out , third() );

			break;
		}

		case AVM_OPCODE_WHILE_DO:
		{
			prettyPrinterCondition( out << TAB << "while" , first() );

			prettyPrinterBlock( out << EOL , second() );

			break;
		}
		case AVM_OPCODE_DO_WHILE:
		{
			prettyPrinterBlock( out << TAB << "do" << EOL , first() );

			prettyPrinterCondition( out << TAB << "while" , second() );

			out << ";" << EOL;

			break;
		}

		case AVM_OPCODE_BREAK:
		case AVM_OPCODE_CONTINUE:
		case AVM_OPCODE_RETURN:
		case AVM_OPCODE_EXIT:
		{
			prettyPrinterBasicStatement( out , isStatement );

			break;
		}

		case AVM_OPCODE_STEP_MARK:

		// AVM QUANTIFIER EXPRESSION
		case AVM_OPCODE_EXIST:
		case AVM_OPCODE_FORALL:
		{
			prettyPrinterPrefix( out );

			break;
		}

		// AVM PREDICAT EXPRESSION
		case AVM_OPCODE_NOT:

		case AVM_OPCODE_AND:
		case AVM_OPCODE_AND_THEN:

		case AVM_OPCODE_NAND:

		case AVM_OPCODE_XAND:

		case AVM_OPCODE_OR:
		case AVM_OPCODE_OR_ELSE:

		case AVM_OPCODE_NOR:

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_XNOR:

		// AVM INTEGER BIT A BIT OPERATOR
		case AVM_OPCODE_BNOT:

		case AVM_OPCODE_BAND:
		case AVM_OPCODE_BOR:
		case AVM_OPCODE_BXOR:

		case AVM_OPCODE_LSHIFT:
		case AVM_OPCODE_RSHIFT:

		// AVM COMPARISON EXPRESSION

		case AVM_OPCODE_EQ:
		case AVM_OPCODE_NEQ:

		case AVM_OPCODE_SEQ:
		case AVM_OPCODE_NSEQ:

		case AVM_OPCODE_LT:
		case AVM_OPCODE_LTE:
		case AVM_OPCODE_GT:
		case AVM_OPCODE_GTE:

		// AVM ARITHMETIC EXPRESSION

		case AVM_OPCODE_PLUS:
		case AVM_OPCODE_MINUS:
		case AVM_OPCODE_UMINUS:

		case AVM_OPCODE_MULT:
		case AVM_OPCODE_POW:

		case AVM_OPCODE_DIV:
		case AVM_OPCODE_MOD:
		{
			prettyPrinterInfix( out );

			break;
		}

		// AVM MATHEMATICAL FUNCTION
		case AVM_OPCODE_MIN:
		case AVM_OPCODE_MAX:

		// RANDOM
		case AVM_OPCODE_RANDOM:

		// ROUNDING
		case AVM_OPCODE_ABS:

		case AVM_OPCODE_CEIL:
		case AVM_OPCODE_FLOOR:
		case AVM_OPCODE_ROUND:
		case AVM_OPCODE_TRUNCATE:

		// EXP - LOG
		case AVM_OPCODE_SQRT:

		case AVM_OPCODE_EXP:
		case AVM_OPCODE_LN:
		case AVM_OPCODE_LOG:

		// TRIGONOMETRIC
		case AVM_OPCODE_SIN:
		case AVM_OPCODE_COS:
		case AVM_OPCODE_TAN:

		case AVM_OPCODE_SINH:
		case AVM_OPCODE_COSH:
		case AVM_OPCODE_TANH:

		case AVM_OPCODE_ASIN:
		case AVM_OPCODE_ACOS:
		case AVM_OPCODE_ATAN:
		case AVM_OPCODE_ATAN2:

		case AVM_OPCODE_ASINH:
		case AVM_OPCODE_ACOSH:
		case AVM_OPCODE_ATANH:
		{
			prettyPrinterFunctional( out );

			break;
		}

		// AVM STRING / CONTAINER OPERATOR
		case AVM_OPCODE_CONTAINS:

		case AVM_OPCODE_IN:
		case AVM_OPCODE_NOTIN:

		case AVM_OPCODE_SUBSET:
		case AVM_OPCODE_SUBSETEQ:

		case AVM_OPCODE_INTERSECT:

		case AVM_OPCODE_STARTS_WITH:
		case AVM_OPCODE_ENDS_WITH:

		case AVM_OPCODE_CONCAT:
		{
			prettyPrinterInfix( out );

			break;
		}

		case AVM_OPCODE_APPEND:

		case AVM_OPCODE_REMOVE:
		case AVM_OPCODE_CLEAR:

		case AVM_OPCODE_RESIZE:

		case AVM_OPCODE_SELECT:

		case AVM_OPCODE_PUSH:
		case AVM_OPCODE_ASSIGN_TOP:
		case AVM_OPCODE_TOP:
		case AVM_OPCODE_POP:
		case AVM_OPCODE_POP_FROM:

		case AVM_OPCODE_EMPTY:
		case AVM_OPCODE_NONEMPTY:
		case AVM_OPCODE_SINGLETON:
		case AVM_OPCODE_POPULATED:
		case AVM_OPCODE_FULL:

		case AVM_OPCODE_SIZE:
		{
			prettyPrinterFunctional( out );

			break;
		}

		// CTL* , IOLTL STATEMENT
		case AVM_OPCODE_NECESSARILY:
		case AVM_OPCODE_POSSIBLY:

		case AVM_OPCODE_GLOBALLY:
		case AVM_OPCODE_EVENTUALLY:

		case AVM_OPCODE_NEXT:
		{
			prettyPrinterPrefix( out );

			break;
		}

		case AVM_OPCODE_UNTIL:
		case AVM_OPCODE_UNLESS:
		case AVM_OPCODE_RELEASES:

		case AVM_OPCODE_AND_T:
		case AVM_OPCODE_OR_T:
		case AVM_OPCODE_NOT_T:
		case AVM_OPCODE_IMP_T:
		{
			prettyPrinterInfix( out );

			break;
		}

		case AVM_OPCODE_OBS:
		{
			prettyPrinterPrefix( out );

			break;
		}

		default:
		{
			toStreamPrefix( out );

			break;
		}
	}

	out << std::flush;
}


void AvmCode::prettyPrinterBasicStatement(
		OutStream & out, bool isStatement) const
{
	out << TAB << ( isStatement ? "" : "(" ) << strOperator()
		<< AVM_STR_INDENT;

	AvmCode::const_iterator it = begin();
	AvmCode::const_iterator endIt = end();
	for( ; it != endIt ; ++it )
	{
		prettyPrinter(out, (*it), false);
	}

	out << ( isStatement ? ";" : ")" ) << END_INDENT_EOL;
}


void AvmCode::prettyPrinterBlockStatement(
		OutStream & out, bool isStatement) const
{
	out << TAB << "{ " << strOperator() << EOL_INCR_INDENT;

	AvmCode::const_iterator it = begin();
	AvmCode::const_iterator endIt = end();
	for( ; it != endIt ; ++it )
	{
		prettyPrinter(out, (*it), isStatement);
	}

	out << DECR_INDENT_TAB << "}"  << EOL;
}


void AvmCode::prettyPrinterDefault(OutStream & out, bool isStatement) const
{
	out << TAB << "${ " << strOperator() << EOL_INCR_INDENT;

	AvmCode::const_iterator it = begin();
	AvmCode::const_iterator endIt = end();
	for( ; it != endIt ; ++it )
	{
		prettyPrinter(out, (*it), isStatement);
	}

	out << DECR_INDENT_TAB << "}" << EOL;
}


void AvmCode::prettyPrinterFunctional(OutStream & out) const
{
	out << TAB << strOperator() << "(" << AVM_NO_INDENT;

	if( singleton() )
	{
		prettyPrinter(out, first(), false);
	}
	else if( populated() )
	{
		AvmCode::const_iterator it = begin();
		AvmCode::const_iterator endIt = end();

		prettyPrinter(out, (*it), false);

		for( ++it ; it != endIt ; ++it )
		{
			out << ", ";
			prettyPrinter(out, (*it), false);
		}
	}

	out << ")" << END_INDENT_EOL;
}


void AvmCode::prettyPrinterInfix(OutStream & out) const
{
	out << TAB << "(" << AVM_NO_INDENT;

	if( singleton() )
	{
		out << strOperator() << " ";

		prettyPrinter(out, first(), false);
	}
	else if( populated() )
	{
		AvmCode::const_iterator it = begin();
		AvmCode::const_iterator endIt = end();

		prettyPrinter(out, (*it), false);

		for( ++it ; it != endIt ; ++it )
		{
			out << " " << strOperator() << " ";

			prettyPrinter(out, (*it), false);
		}
	}

	out << ")" << END_INDENT_EOL;
}


void AvmCode::prettyPrinterPrefix(OutStream & out) const
{
	out << TAB << "(" << strOperator() << AVM_STR_INDENT;

	AvmCode::const_iterator it = begin();
	AvmCode::const_iterator endIt = end();
	for( ; it != endIt ; ++it )
	{
		prettyPrinter(out, (*it), false);
	}

	out << ")" << END_INDENT_EOL;
}


void AvmCode::prettyPrinterSuffix(OutStream & out) const
{
	out << TAB << "(" << AVM_RTS_INDENT;

	AvmCode::const_iterator it = begin();
	AvmCode::const_iterator endIt = end();
	for( ; it != endIt ; ++it )
	{
		prettyPrinter(out, (*it), false);
	}

	out << strOperator() << ")" << END_INDENT_EOL;
}


void AvmCode::prettyPrinter(OutStream & out, const BF & arg, bool isStatement)
{
	if( arg.invalid() )
	{
		out << TAB << "null<avmcode::arg>" << EOL;
	}

	else if( arg.is< AvmCode >() )
	{
		arg.to_ptr< AvmCode >()->prettyPrinter(out, isStatement);
	}
	else if( arg.is< BuiltinForm >() )
	{
		out << TAB << arg.to_ptr< BuiltinForm >()->str() << EOL;
	}

	else if( arg.is< Operator >() )
	{
		out << TAB << arg.to_ptr< Operator >()->standardSymbol();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< Routine >() )
	{
		arg.to_ptr< Routine >()->toStreamInvoke(out);
	}

	else if( arg.is< PropertyElement >() )
	{
		out << TAB << "&"
			<< arg.to_ptr< PropertyElement >()->getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< BaseInstanceForm >() )
	{
		out << TAB //<< "&"
				<< arg.to_ptr< BaseInstanceForm >()->getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< BehavioralElement >() )
	{
		out << TAB << "&"
			<< arg.to_ptr< BehavioralElement >()->getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( WObjectManager::is( arg ) )
	{
		out << TAB << "&"
			<< WObjectManager::from( arg )->getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< UniFormIdentifier >() )
	{
		out << TAB << arg.to_ptr< UniFormIdentifier >()->str() << EOL;
	}

	else if( arg.is< RuntimeID >() )
	{
		out << TAB << arg.bfRID().str() << EOL;
	}

	else if( arg.is_exactly< AvmProgram >() )
	{
		AvmProgram * aProg = arg.to_ptr< AvmProgram >();
		if( aProg->isAnonym() )
		{
			aProg->toStream(out);
		}
		else
		{
			out << TAB << aProg->getQualifiedNameID();
			arg.AVM_DEBUG_REF_COUNTER(out);
			out << EOL;
		}
	}

	else if( arg.is< BaseTypeSpecifier >() )
	{
		out << TAB << arg.to_ptr< BaseTypeSpecifier >()->strT();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< ObjectElement >() )
	{
		out << TAB << "&"
			<< arg.to_ptr< ObjectElement >()->getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< BuiltinArray >() )
	{
		arg.to_ptr< BuiltinArray >()->toStream(out);
	}

	else
	{
		arg.toStream( out );
	}
}


void AvmCode::prettyPrinter(OutStream & out,
		const BF & arg, BaseTypeSpecifier * aType)
{
	if( aType != NULL )
	{
		aType->formatStream(out, arg);
	}
	else
	{
		prettyPrinter(out, arg, false);
	}
}


void AvmCode::prettyPrinterCondition(OutStream & out, const BF & arg)
{
	out << AVM_STR_INDENT;

	if( arg.is< AvmCode >() )
	{
		arg.to_ptr< AvmCode >()->prettyPrinter( out , false );
	}
	else
	{
		prettyPrinter(out << "( ", arg, false);
		out << " )";
	}

	out << END_INDENT;
}


void AvmCode::prettyPrinterBlock(OutStream & out, const BF & arg)
{
	if( arg.is< AvmCode >() )
	{
		if( OperatorManager::isSchedule(arg.to_ptr< AvmCode >()->mOperator) )
		{
			arg.to_ptr< AvmCode >()->prettyPrinter( out, true );
		}
		else
		{
			out << TAB << "{" << EOL_INCR_INDENT;
			arg.to_ptr< AvmCode >()->prettyPrinter( out, true );
			out << DECR_INDENT_TAB << "}" << EOL;
		}
	}
	else
	{
		out << TAB << "{" << EOL_INCR_INDENT;
		prettyPrinter(out, arg, true);
		out << DECR_INDENT_TAB << "}" << EOL;
	}
}


}
