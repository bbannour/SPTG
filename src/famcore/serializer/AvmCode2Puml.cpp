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
#include "AvmCode2Puml.h"

#include <fml/builtin/BuiltinForm.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/infrastructure/Routine.h>

#include <fml/operator/OperatorManager.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>


namespace sep
{

OutStream & AvmCode2Puml::toStream(OutStream & out, const AvmCode & aCode)
{
	if( OperatorManager::isSchedule(aCode.getOperator()) )
	{
		if( not aCode.isOpCode(AVM_OPCODE_SEQUENCE) )
		{
			out << " " << aCode.strOperator();
		}
		out << EOL;

		for( const auto & itOperand : aCode.getOperands() )
		{
			prettyPrinter(out, itOperand);
		}
	}
	else
	{
		prettyPrinter(out << EOL, aCode);
	}

	return( out );
}



void AvmCode2Puml::prettyPrinter(OutStream & out, const AvmCode & aCode, bool isStatement)
{
//	switch( aCode.getOperator()->getFixNotation() )
//	{
//		case NOTATION_FUNCTION:
//		case NOTATION_INFIX:
//		case NOTATION_PREFIX:
//		case NOTATION_SUFFIX:
//		default:
//	}

	switch( aCode.getOperator()->getOptimizedOpCode() )
	{
		case AVM_OPCODE_NULL:

		// AVM NOP STATEMENT
		case AVM_OPCODE_NOP:

		case AVM_OPCODE_FAILED:
		case AVM_OPCODE_THROW:

		// AVM META STATEMENT
		case AVM_OPCODE_INFORMAL:

		case AVM_OPCODE_COMMENT:

		case AVM_OPCODE_QUOTE:

		case AVM_OPCODE_META_EVAL:
		case AVM_OPCODE_META_RUN:
		{
			prettyPrinterBasicStatement(out, aCode, isStatement);

			break;
		}

		case AVM_OPCODE_TRACE:
		case AVM_OPCODE_DEBUG:
		{
			out << TAB << aCode.strOperator() << AVM_STR_INDENT;

			for( const auto & itOperand : aCode.getOperands() )
			{
				prettyPrinter(out, itOperand, false);
			}

			out << " }" << END_INDENT_EOL;

			break;
		}

		// AVM UFI STATEMENT
		case AVM_OPCODE_UFI:
		{
			prettyPrinterDefault(out, aCode, false);

			break;
		}

		// AVM FORM CONSTRUCTOR STATEMENT
		case AVM_OPCODE_CTOR:
		{
			out << TAB << "ctor<" << AVM_STR_INDENT;

			prettyPrinter(out, aCode[0], false );

			out << " >(";

			prettyPrinter(out, aCode[1], false );

			out << " )" << END_INDENT_EOL;

			break;
		}

		// AVM FORM REGEX STATEMENT
		case AVM_OPCODE_REGEX:
		{
			prettyPrinterDefault(out, aCode, false);

			break;
		}

		// AVM MACHINE MANAGING
		case AVM_OPCODE_CONTEXT_SWITCHER:
		{
			out << TAB << "ctx<" << AVM_STR_INDENT;

			prettyPrinter(out, aCode[0], false);

			out << TAB << "> " << END_INDENT << IGNORE_FIRST_TAB;

			prettyPrinter(out , aCode[1] , isStatement);

			break;
		}

		case AVM_OPCODE_PROCESS_STATE_GET:
		case AVM_OPCODE_PROCESS_STATE_SET:

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
			prettyPrinterBasicStatement(out, aCode, isStatement);

			break;
		}

		case AVM_OPCODE_FORK:
		case AVM_OPCODE_JOIN:

		case AVM_OPCODE_INPUT_ENABLED:

		case AVM_OPCODE_RDV:

		case AVM_OPCODE_SYNCHRONIZE:
		{
			prettyPrinterDefault(out, aCode, isStatement);

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
			prettyPrinterBasicStatement(out, aCode, isStatement);

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
			prettyPrinterDefault(out, aCode , isStatement);

			break;
		}


		// AVM PROGRAM SCHEDULING
		case AVM_OPCODE_ASYNCHRONOUS:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:

		case AVM_OPCODE_INTERLEAVING:
		case AVM_OPCODE_PARTIAL_ORDER:

		case AVM_OPCODE_PARALLEL:

		// Optimized version of concurrency for RDV synchronization
		case AVM_OPCODE_RDV_ASYNCHRONOUS:
		case AVM_OPCODE_RDV_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_RDV_WEAK_SYNCHRONOUS:

		case AVM_OPCODE_RDV_INTERLEAVING:
		case AVM_OPCODE_RDV_PARTIAL_ORDER:

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
			prettyPrinterBlockStatement(out, aCode , isStatement);

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
			prettyPrinterDefault(out, aCode, isStatement);

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
			prettyPrinterFunctional(out, aCode);

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

			AvmCode::const_iterator itOperand = aCode.begin();
			AvmCode::const_iterator endOperand = aCode.end();

			prettyPrinter(out << IGNORE_FIRST_TAB, (*itOperand), false);

			const BaseTypeSpecifier & aType = (*itOperand).is< InstanceOfData >()
					? (*itOperand).to< InstanceOfData >().getTypeSpecifier()
					: BaseTypeSpecifier::nullref();

			for( ++itOperand ; itOperand != endOperand ; ++itOperand )
			{
				out << TAB << aCode.strOperator();

				prettyPrinter(out, (*itOperand), aType);
			}

			( isStatement ? (out << " $ks(\";\")") : out ) << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_ASSIGN_NEWFRESH:
		case AVM_OPCODE_ASSIGN_RESET:
		{
			prettyPrinterFunctional(out, aCode);

			break;
		}

		case AVM_OPCODE_GUARD:
		case AVM_OPCODE_TIMED_GUARD:

		case AVM_OPCODE_EVENT:

		case AVM_OPCODE_CHECK_SAT:
		{
			prettyPrinterBasicStatement(out, aCode , isStatement);

			break;
		}

		case AVM_OPCODE_INPUT:
		case AVM_OPCODE_INPUT_FROM:

		case AVM_OPCODE_INPUT_SAVE:

		// Optimized version of INPUT
		case AVM_OPCODE_INPUT_VAR:
		case AVM_OPCODE_INPUT_FLOW:
		case AVM_OPCODE_INPUT_BUFFER:
		case AVM_OPCODE_INPUT_RDV:
		case AVM_OPCODE_INPUT_MULTI_RDV:
		case AVM_OPCODE_INPUT_BROADCAST:
		case AVM_OPCODE_INPUT_DELEGATE:

		case AVM_OPCODE_OUTPUT:
		// Optimized version of OUTPUT
		case AVM_OPCODE_OUTPUT_VAR:
		case AVM_OPCODE_OUTPUT_FLOW:
		case AVM_OPCODE_OUTPUT_BUFFER:
		case AVM_OPCODE_OUTPUT_RDV:
		case AVM_OPCODE_OUTPUT_MULTI_RDV:
		case AVM_OPCODE_OUTPUT_BROADCAST:
		case AVM_OPCODE_OUTPUT_DELEGATE:
		{
			out << TAB << "$kw(\"" << aCode.strOperator() << "\") " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[0], false);

			if( aCode.hasManyOperands() )
			{
				AvmCode::const_iterator itOperand = aCode.begin();
				AvmCode::const_iterator endOperand = aCode.end();

				out << "(";

				prettyPrinter(out, *(++itOperand), false);

				for( ++itOperand ; itOperand != endOperand ; ++itOperand )
				{
					out << ", ";
					prettyPrinter(out, (*itOperand), false);
				}

				out << ")";
			}

			out << " $ks(\";\")" << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_OUTPUT_TO:
		{
			out << TAB << aCode.strOperator() << " " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[0], false);

			if( aCode.getOperands().size() > 2 )
			{
				AvmCode::const_iterator itOperand = aCode.begin();
				AvmCode::const_iterator endOperand = aCode.end();

				++itOperand;
				++itOperand;

				out << "(";

				prettyPrinter(out, *itOperand, false);

				for( ++itOperand ; itOperand != endOperand ; ++itOperand )
				{
					out << ", ";
					prettyPrinter(out, (*itOperand), false);
				}

				out << ")";
			}

			out << " --> ";
			prettyPrinter(out, aCode[1], false);

			out << " $ks(\";\")" << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_INPUT_ENV:
		{
			out << TAB << OperatorManager::OPERATOR_INPUT->standardSymbol()
				<< " " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[0], false);

			if( aCode.hasManyOperands() )
			{
				AvmCode::const_iterator itOperand = aCode.begin();
				AvmCode::const_iterator endOperand = aCode.end();

				out << "(";

				prettyPrinter(out, *(++itOperand), false);

				for( ++itOperand ; itOperand != endOperand ; ++itOperand )
				{
					out << ", ";
					prettyPrinter(out, (*itOperand), false);
				}

				out << ") --> $env";
			}

			out << " $ks(\";\")" << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_OUTPUT_ENV:
		{
			out << TAB << OperatorManager::OPERATOR_OUTPUT->standardSymbol()
				<< " " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[0], false);

			if( aCode.hasManyOperands() )
			{
				AvmCode::const_iterator itOperand = aCode.begin();
				AvmCode::const_iterator endOperand = aCode.end();

				out << "(";

				prettyPrinter(out, *(++itOperand), false);

				for( ++itOperand ; itOperand != endOperand ; ++itOperand )
				{
					out << ", ";
					prettyPrinter(out, (*itOperand), false);
				}

				out << ") <-- $env";
			}

			out << " $ks(\";\")" << END_INDENT_EOL;

			break;
		}


		case AVM_OPCODE_PRESENT:
		case AVM_OPCODE_ABSENT:
		{
			out << TAB << aCode.strOperator() << " " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[0], false);

			if( aCode.hasManyOperands() )
			{
				AvmCode::const_iterator itOperand = aCode.begin();
				AvmCode::const_iterator endOperand = aCode.end();

				out << "(";

				prettyPrinter(out, *(++itOperand), false);

				for( ++itOperand ; itOperand != endOperand ; ++itOperand )
				{
					out << ", ";
					prettyPrinter(out, (*itOperand), false);
				}

				out << ")";
			}

			( isStatement ? (out << " $ks(\";\")") : out ) << END_INDENT_EOL;

			break;
		}

		case AVM_OPCODE_IF:
		{
			out << TAB << "if";

			prettyPrinterCondition( out , aCode[0] );

			prettyPrinterBlock( out << EOL , aCode[1] );

			break;
		}
		case AVM_OPCODE_IFE:
		{
			out << TAB << "if";

			prettyPrinterCondition( out , aCode[0] );

			prettyPrinterBlock( out << EOL , aCode[1] );

			out << TAB << "else" << EOL;

			prettyPrinterBlock( out , aCode[2] );

			break;
		}

		case AVM_OPCODE_WHERE:
		{
			out << TAB << "where";

			prettyPrinterCondition( out , aCode[0] );

			prettyPrinterBlock( out << EOL , aCode[1] );

			break;
		}
		case AVM_OPCODE_WHERE_ELSE:
		{
			prettyPrinterCondition( out << TAB << "where" , aCode[0] );

			prettyPrinterBlock( out << EOL , aCode[1] );

			prettyPrinterBlock( out << TAB << "else" << EOL , aCode[2] );

			break;
		}

		case AVM_OPCODE_FOR:
		{
			out << TAB << "for( " << AVM_NO_INDENT;

			prettyPrinter( out , aCode[0] , false );
			out << " ; ";
			prettyPrinter( out , aCode[1] , false );
			out << " ; ";
			prettyPrinter( out , aCode[2] , false );

			out << " )" << END_INDENT_EOL;

			prettyPrinterBlock( out , aCode[3] );

			break;
		}

		case AVM_OPCODE_FOREACH:
		{
			out << TAB << "for( " << AVM_NO_INDENT;

			prettyPrinter( out , aCode[0] , false );
			out << " : ";
			prettyPrinter( out , aCode[1] , false );

			out << " )" << END_INDENT_EOL;

			prettyPrinterBlock( out , aCode[2] );

			break;
		}

		case AVM_OPCODE_WHILE_DO:
		{
			prettyPrinterCondition( out << TAB << "while" , aCode[0] );

			prettyPrinterBlock( out << EOL , aCode[1] );

			break;
		}
		case AVM_OPCODE_DO_WHILE:
		{
			prettyPrinterBlock( out << TAB << "do" << EOL , aCode[0] );

			prettyPrinterCondition( out << TAB << "while" , aCode[1] );

			out << " $ks(\";\")" << EOL;

			break;
		}

		case AVM_OPCODE_BREAK:
		case AVM_OPCODE_CONTINUE:
		case AVM_OPCODE_RETURN:
		case AVM_OPCODE_EXIT:
		{
			prettyPrinterBasicStatement(out, aCode, isStatement);

			break;
		}

		case AVM_OPCODE_STEP_MARK:

		// AVM QUANTIFIER EXPRESSION
		case AVM_OPCODE_EXISTS:
		case AVM_OPCODE_FORALL:
		{
			out << TAB << ( (aCode.getOperator()->getAvmOpCode() == AVM_OPCODE_FORALL)
					? "forall" : "exists" ) << "< ";// << AVM_TAB_INDENT;// << AVM_STR_INDENT;

			std::size_t endVarOfsset = aCode.getOperands().size() - 1;
			for( std::size_t offset = 0 ; offset < endVarOfsset ; ++offset )
			{
				if( offset > 0 )
				{
					out << " , " << WRAP_TAB2;
				}
				if( aCode[offset].is< Variable >() )
				{
					const Variable & boundVariable =
							aCode[offset].to< Variable >();

					std::string strType = boundVariable.strTypeSpecifier();

					if( boundVariable.hasTypeSpecifier() )
					{
						const BaseTypeSpecifier & typSeSpecifier =
								boundVariable.getTypeSpecifier();
						if( (typSeSpecifier.hasTypedTime() || typSeSpecifier.hasTypedClock())
							&& typSeSpecifier.is< ContainerTypeSpecifier >() )
						{
							const BaseTypeSpecifier & domainType = typSeSpecifier.to<
									ContainerTypeSpecifier >().getContentsTypeSpecifier();
							strType = domainType.strT();
						}
					}
//					out << "$param(\"" << boundVariable.getNameID() << "\")" << " : " << strType;
					out << boundVariable.getNameID() << " : " << strType;
				}
				else if( aCode[offset].is< InstanceOfData >() )
				{
					const InstanceOfData & boundVariable =
							aCode[offset].to< InstanceOfData >();
					const BaseTypeSpecifier & typSeSpecifier =
							boundVariable.getTypeSpecifier();

					std::string strType = typSeSpecifier.strT();
					if( (typSeSpecifier.hasTypedTime() || typSeSpecifier.hasTypedClock())
						&& typSeSpecifier.is< ContainerTypeSpecifier >() )
					{
						const BaseTypeSpecifier & domainType = typSeSpecifier.to<
								ContainerTypeSpecifier >().getContentsTypeSpecifier();
						strType = domainType.strT();
					}
//					out << "$param(\"" << boundVariable.getNameID() << "\")" << " : " << strType;
					out << boundVariable.getNameID() << " : " << strType;
				}
			}

			out << " >" << IGNORE_FIRST_TAB;

			if( aCode[ endVarOfsset ].is< AvmCode >() )
			{
				prettyPrinter( out , aCode[ endVarOfsset ] , false );
			}
			else
			{
				out << "( ";
				prettyPrinter( out , aCode[ endVarOfsset ] , false );
				out << " )";
			}

//			out << END_INDENT_EOL;
			break;
		}

		// AVM PREDICAT EXPRESSION
		case AVM_OPCODE_AND:
		case AVM_OPCODE_OR:
		{
			prettyPrinterInfix(out, aCode, true, true);

			break;
		}

		case AVM_OPCODE_NOT:

//		case AVM_OPCODE_AND:
		case AVM_OPCODE_AND_THEN:

		case AVM_OPCODE_NAND:

		case AVM_OPCODE_XAND:

//		case AVM_OPCODE_OR:
		case AVM_OPCODE_OR_ELSE:

		case AVM_OPCODE_NOR:

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_XNOR:

		case AVM_OPCODE_IMPLIES:

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
			prettyPrinterInfix(out, aCode);

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
			prettyPrinterFunctional(out, aCode);

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
			prettyPrinterInfix(out, aCode);

			break;
		}

		case AVM_OPCODE_PUSH:
		{
			prettyPrinterInfix(out, aCode, false);

			break;
		}

		case AVM_OPCODE_APPEND:

		case AVM_OPCODE_REMOVE:
		case AVM_OPCODE_CLEAR:

		case AVM_OPCODE_RESIZE:

		case AVM_OPCODE_SELECT:

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
			prettyPrinterFunctional(out, aCode);

			break;
		}

		// CTL* , IOLTL STATEMENT
		case AVM_OPCODE_NECESSARILY:
		case AVM_OPCODE_POSSIBLY:

		case AVM_OPCODE_GLOBALLY:
		case AVM_OPCODE_EVENTUALLY:

		case AVM_OPCODE_NEXT:
		{
			prettyPrinterPrefix(out, aCode);

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
			prettyPrinterInfix(out, aCode);

			break;
		}

		case AVM_OPCODE_OBS:
		{
			out << TAB << aCode.strOperator() << "( ctx: " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[0], false);

			out << " ) {" << END_INDENT_EOL << INCR_INDENT;

			prettyPrinter(out, aCode[1], true);

			out << DECR_INDENT << TAB << "} [ " << AVM_NO_INDENT;

			prettyPrinter(out, aCode[2], false);

			out << " ];" << END_INDENT_EOL;

			break;
		}

		default:
		{
			aCode.toStreamPrefix( out );

			break;
		}
	}

	out << std::flush;
}


void AvmCode2Puml::prettyPrinterBasicStatement(OutStream & out,
		const AvmCode & aCode, bool isStatement)
{
	out << TAB << ( isStatement ? "$kw(\"" : "($kop(\"" ) << aCode.strOperator() << "\")"
		<< AVM_STR_INDENT;

	for( const auto & itOperand : aCode.getOperands() )
	{
		prettyPrinter(out, itOperand, false);
	}

	out << ( isStatement ? " $ks(\";\")" : ")" ) << END_INDENT_EOL;
}


void AvmCode2Puml::prettyPrinterBlockStatement(OutStream & out,
		const AvmCode & aCode, bool isStatement)
{
	out << TAB << "{";
	if( not aCode.isOpCode(AVM_OPCODE_SEQUENCE) )
	{
		out << " $kop(\"" << aCode.strOperator() << "\")";
	}
	out << EOL_INCR_INDENT;

	for( const auto & itOperand : aCode.getOperands() )
	{
		prettyPrinter(out, itOperand, isStatement);
	}

	out << DECR_INDENT_TAB << "}"  << EOL;
}


void AvmCode2Puml::prettyPrinterDefault(OutStream & out, const AvmCode & aCode, bool isStatement)
{
	out << TAB << "${ " << aCode.strOperator() << EOL_INCR_INDENT;

	for( const auto & itOperand : aCode.getOperands() )
	{
		prettyPrinter(out, itOperand, isStatement);
	}

	out << DECR_INDENT_TAB << "}" << EOL;
}


void AvmCode2Puml::prettyPrinterFunctional(OutStream & out, const AvmCode & aCode, bool isExpression)
{
	out << TAB << aCode.strOperator() << "(" << AVM_NO_INDENT;

	if( aCode.hasOneOperand() )
	{
		prettyPrinter(out, aCode[0], false);
	}
	else if( aCode.hasManyOperands() )
	{
		AvmCode::const_iterator itOperand = aCode.begin();
		AvmCode::const_iterator endOperand = aCode.end();

		prettyPrinter(out, (*itOperand), false);

		for( ++itOperand ; itOperand != endOperand ; ++itOperand )
		{
			out << ", ";
			prettyPrinter(out, (*itOperand), false);
		}
	}

	out << ( isExpression ? ")" : ");" ) << END_INDENT_EOL;
}


void AvmCode2Puml::prettyPrinterInfix(OutStream & out,
		const AvmCode & aCode, bool isExpression, bool isWrap)
{
	out << TAB << ( isExpression ? "(" : "" ) << AVM_NO_INDENT;

	if( aCode.hasOneOperand() )
	{
		out << "$kop(\"" << aCode.strOperator() << "\") ";

		prettyPrinter(out, aCode[0], false);
	}
	else if( aCode.hasManyOperands() )
	{
		AvmCode::const_iterator itOperand = aCode.begin();
		AvmCode::const_iterator endOperand = aCode.end();

		prettyPrinter(out, (*itOperand), false);

		for( ++itOperand ; itOperand != endOperand ; ++itOperand )
		{
			if( isWrap )
			{
				out << WRAP_TAB2;
			}
			out << " $kop(\"" << aCode.strOperator() << "\") ";

			prettyPrinter(out, (*itOperand), false);
		}
	}

	out << ( isExpression ? ")" : " $ks(\";\")" ) << END_INDENT_EOL;
}


void AvmCode2Puml::prettyPrinterPrefix(OutStream & out, const AvmCode & aCode, bool isExpression)
{
	out << TAB << ( isExpression ? "(" : "" ) << aCode.strOperator()
		<< AVM_STR_INDENT;

	for( const auto & itOperand : aCode.getOperands() )
	{
		prettyPrinter(out, itOperand, false);
	}

	out << (isExpression ? ")" : " $ks(\";\")") << END_INDENT_EOL;
}


void AvmCode2Puml::prettyPrinterSuffix(OutStream & out, const AvmCode & aCode, bool isExpression)
{
	out << TAB << (isExpression ? "(" : "") << AVM_RTS_INDENT;

	for( const auto & itOperand : aCode.getOperands() )
	{
		prettyPrinter(out, itOperand, false);
	}

	out << aCode.strOperator() << ( isExpression ? ")" : " $ks(\";\")" ) << END_INDENT_EOL;
}


void AvmCode2Puml::prettyPrinter(OutStream & out, const BF & arg, bool isStatement)
{
	if( arg.invalid() )
	{
		out << TAB << "null<AvmCode2Puml::arg>" << EOL;
	}

	else if( arg.is< AvmCode >() )
	{
		prettyPrinter(out, arg.to< AvmCode >(), isStatement);
	}
	else if( arg.is< BuiltinForm >() )
	{
		out << TAB << arg.to< BuiltinForm >().str() << EOL;
	}

	else if( arg.is< Operator >() )
	{
		out << TAB << arg.to< Operator >().standardSymbol();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< Routine >() )
	{
		arg.to< Routine >().toStreamInvoke(out);
	}

	else if( arg.is< Variable >() )
	{
		if( AvmCode::EXPRESSION_PRETTY_PRINTER_BASED_FQN )
		{
			out << TAB << VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
				<< arg.to< PropertyElement >().getQualifiedNameID();
			arg.AVM_DEBUG_REF_COUNTER(out);
			out << EOL;
		}
//		else if( arg.to< Variable >().getNameID().starts_with("#")
//				|| arg.to< Variable >().getNameID().starts_with("$")
//				|| ((arg.to< Variable >().getNameID() != "TM" )
//					&& (! arg.to< Variable >().getTypeSpecifier().hasTypedClock())) )
//		{
//			out << TAB << "$param(\"" << arg.to< PropertyElement >().getNameID() << "\")" << EOL;
//		}
		else //if( EXPRESSION_PRETTY_PRINTER_BASED_NAME )
		{
			out << TAB << arg.to< PropertyElement >().getNameID() << EOL;
		}
	}
	else if( arg.is< PropertyElement >() )
	{
//		out << TAB << VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
//			<< arg.to< PropertyElement >().getQualifiedNameID();
//		arg.AVM_DEBUG_REF_COUNTER(out);
//		out << EOL;
//!@2024
		if( AvmCode::EXPRESSION_PRETTY_PRINTER_BASED_FQN )
		{
			out << TAB << VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
				<< arg.to< PropertyElement >().getQualifiedNameID();
			arg.AVM_DEBUG_REF_COUNTER(out);
			out << EOL;
		}
		else //if( EXPRESSION_PRETTY_PRINTER_BASED_NAME )
		{
			out << TAB << arg.to< PropertyElement >().getNameID() << EOL;
		}
	}
	else if( arg.is< InstanceOfData >() )
	{
		if( AvmCode::EXPRESSION_PRETTY_PRINTER_BASED_FQN )
		{
			out << TAB //<< VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
				<< arg.to< InstanceOfData >().getQualifiedNameID();
		}
//		else if( arg.to< InstanceOfData >().getNameID().starts_with("#")
//			|| arg.to< InstanceOfData >().getNameID().starts_with("$")
//			|| (! arg.to< InstanceOfData >().getTypeSpecifier().hasTypedClock()) )
//		{
//			out << TAB << "$param(\"" << arg.to< InstanceOfData >().getNameID() << "\")" << EOL;
//		}
		else //if( EXPRESSION_PRETTY_PRINTER_BASED_NAME )
		{
			out << TAB << arg.to< InstanceOfData >().getNameID();
		}

		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< BaseInstanceForm >() )
	{
		if( AvmCode::EXPRESSION_PRETTY_PRINTER_BASED_FQN )
		{
			out << TAB //<< VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
				<< arg.to< BaseInstanceForm >().getQualifiedNameID();
		}
		else //if( EXPRESSION_PRETTY_PRINTER_BASED_NAME )
		{
			out << TAB << arg.to< BaseInstanceForm >().getNameID();
		}

		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}
	else if( arg.is< BehavioralElement >() )
	{
		out << TAB << VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
			<< arg.to< BehavioralElement >().getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( WObjectManager::is( arg ) )
	{
		out << TAB << VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
			<< WObjectManager::from( arg )->getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< UniFormIdentifier >() )
	{
		out << TAB << arg.to< UniFormIdentifier >().str() << EOL;
	}

	else if( arg.is< RuntimeID >() )
	{
		out << TAB << arg.bfRID().str() << EOL;
	}

	else if( arg.is_exactly< AvmProgram >() )
	{
		const AvmProgram & aProg = arg.to< AvmProgram >();
		if( aProg.isAnonym() )
		{
			aProg.toStream(out);
		}
		else
		{
			out << TAB << aProg.getQualifiedNameID();
			arg.AVM_DEBUG_REF_COUNTER(out);
			out << EOL;
		}
	}

	else if( arg.is< BaseTypeSpecifier >() )
	{
		out << TAB << arg.to< BaseTypeSpecifier >().strT();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< ObjectElement >() )
	{
		out << TAB << VALUE_IF_DEBUG_FLAG( ALL_NAME_ID , "&" , "" )
			<< arg.to< ObjectElement >().getQualifiedNameID();
		arg.AVM_DEBUG_REF_COUNTER(out);
		out << EOL;
	}

	else if( arg.is< BuiltinArray >() )
	{
		arg.to< BuiltinArray >().toStream(out);
	}

	else
	{
		arg.toStream( out );
	}
}


void AvmCode2Puml::prettyPrinter(OutStream & out,
		const BF & arg, const BaseTypeSpecifier & aType)
{
	if( aType.isnotNullref() )
	{
		aType.formatStream(out << TAB, arg);
		out << EOL;
	}
	else
	{
		prettyPrinter(out, arg, false);
	}
}


void AvmCode2Puml::prettyPrinterCondition(OutStream & out, const BF & arg)
{
	out << AVM_STR_INDENT;

	if( arg.is< AvmCode >() )
	{
		prettyPrinter(out, arg.to< AvmCode >(), false);
	}
	else
	{
		prettyPrinter(out << "( ", arg, false);
		out << " )";
	}

	out << END_INDENT;
}


void AvmCode2Puml::prettyPrinterBlock(OutStream & out, const BF & arg)
{
	if( arg.is< AvmCode >() )
	{
		if( OperatorManager::isSchedule(arg.to< AvmCode >().getOperator()) )
		{
			prettyPrinter(out, arg.to< AvmCode >(), true );
		}
		else
		{
			out << TAB << "{" << EOL_INCR_INDENT;
			prettyPrinter(out, arg.to< AvmCode >(), true);
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
