/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 juin 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "OperatorLib.h"

#include <fml/expression/AvmCode.h>


namespace sep
{


/**
 * TEST
 */
bool OperatorLib::isPropositional(AVM_OPCODE opcode)
{
	switch( opcode )
	{
		/*
		 ***********************************************************************
		 * AVM PROPOSITIONAL EXPRESSION
		 ***********************************************************************
		 */
		case AVM_OPCODE_NOT:

		case AVM_OPCODE_AND:
		case AVM_OPCODE_NAND:

		case AVM_OPCODE_XAND:

		case AVM_OPCODE_OR:
		case AVM_OPCODE_NOR:

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_XNOR:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}



std::string OperatorLib::to_string(FIX_NOTATION fix)
{
	switch( fix )
	{
		case NOTATION_INFIX    : return( "infix"     );
		case NOTATION_PREFIX   : return( "prefix"    );
		case NOTATION_SUFFIX   : return( "suffix"    );
		case NOTATION_FUNCTION : return( "function"  );
		case NOTATION_STATEMENT: return( "statement" );

		default: return( "fix#unknown" );
	}
}

FIX_NOTATION OperatorLib::to_fix(
		const std::string & fix, FIX_NOTATION defaultFix)
{
	if( fix == "infix"     )  return( NOTATION_INFIX     );
	if( fix == "prefix"    )  return( NOTATION_PREFIX    );
	if( fix == "suffix"    )  return( NOTATION_SUFFIX    );
	if( fix == "function"  )  return( NOTATION_FUNCTION  );
	if( fix == "statement" )  return( NOTATION_STATEMENT );

	return( defaultFix );
}


std::string OperatorLib::to_string(AVM_OPCODE opcode,
			ENUM_PRINT_OPERATOR_FORMAT printFormat)
{
	switch( opcode )
	{
		case AVM_OPCODE_ASSIGN:        return( ":="  );
		case AVM_OPCODE_ASSIGN_AFTER:  return( "=:"  );
		case AVM_OPCODE_ASSIGN_MACRO:  return( "::=" );

		case AVM_OPCODE_EQ:      return( "=" );

		case AVM_OPCODE_NEQ:     return( "!="  );
		case AVM_OPCODE_SEQ:     return( "===" );
		case AVM_OPCODE_NSEQ:    return( "=/=" );

		case AVM_OPCODE_BAND:    return( "&" );
		case AVM_OPCODE_BOR:     return( "|" );
		case AVM_OPCODE_BXOR:    return( "^" );
		case AVM_OPCODE_BNOT:    return( "~" );

		case AVM_OPCODE_PLUS :   return( "+" );
		case AVM_OPCODE_MINUS:   return( "-" );
		case AVM_OPCODE_UMINUS:  return( "-" );
		case AVM_OPCODE_MOD:     return( "%" );
		case AVM_OPCODE_MULT:    return( "*" );
		case AVM_OPCODE_DIV:     return( "/" );
		case AVM_OPCODE_POW:     return( "^" );

		case AVM_OPCODE_LT:      return( "<"  );
		case AVM_OPCODE_LTE:     return( "<=" );
		case AVM_OPCODE_GT:      return( ">"  );
		case AVM_OPCODE_GTE:     return( ">=" );

		case AVM_OPCODE_NOT:     return( "not" );
		case AVM_OPCODE_AND:     return( "and" );
		case AVM_OPCODE_OR :     return( "or"  );
		case AVM_OPCODE_XOR:     return( "xor" );

		case AVM_OPCODE_SEQUENCE        :  return( "|;|"     );
		case AVM_OPCODE_ATOMIC_SEQUENCE :  return( "|§|"     );
		case AVM_OPCODE_SEQUENCE_WEAK   :  return( "|;;|"    );

		case AVM_OPCODE_INTERLEAVING    :  return( "|i|"     );

		case AVM_OPCODE_PRIOR_GT        :  return( "|<|"     );

		case AVM_OPCODE_REGEX           :  return( "|regex|" );

		default:  return( "opcode#unknown" );
	}
}


AVM_OPCODE OperatorLib::toOpcode(
		const std::string & op, AVM_OPCODE defaultOpcode)
{
	if( op == "NOT" )  return( AVM_OPCODE_NOT );
	if( op == "AND" )  return( AVM_OPCODE_AND );
	if( op == "OR"  )  return( AVM_OPCODE_OR  );
	if( op == "XOR" )  return( AVM_OPCODE_XOR );

	if( op == "|;|"  )  return( AVM_OPCODE_SEQUENCE );
	if( op == "|§|"  )  return( AVM_OPCODE_ATOMIC_SEQUENCE );
	if( op == "|;;|" )  return( AVM_OPCODE_SEQUENCE_WEAK );

	if( op == "|i|"  )  return( AVM_OPCODE_INTERLEAVING );

	if( op == "|<|"  )  return( AVM_OPCODE_PRIOR_GT );

	if( op == "|regex|"  )  return( AVM_OPCODE_REGEX );

	return( defaultOpcode );
}



////////////////////////////////////////////////////////////////////////////////
// OperatorFamily
////////////////////////////////////////////////////////////////////////////////

IStatementFamily::avm_opcode_family
IStatementFamily::computeStatementFamily(AVM_OPCODE opcode)
{
	switch( opcode )
	{
//		case AVM_OPCODE_IF               :
//		case AVM_OPCODE_IFE              :
//
//		case AVM_OPCODE_WHERE            :
//		case AVM_OPCODE_WHERE_ELSE       :
//
//		case AVM_OPCODE_FOR              :
//		case AVM_OPCODE_FOREACH          :
//		case AVM_OPCODE_WHILE_DO         :
//		case AVM_OPCODE_DO_WHILE         :

		case AVM_OPCODE_GUARD            :
		case AVM_OPCODE_TIMED_GUARD      :
		case AVM_OPCODE_EVENT            :
		case AVM_OPCODE_CHECK_SAT        :
			return( AVM_STATEMENT_GUARD_FAMILY );


		case AVM_OPCODE_INPUT            :
		case AVM_OPCODE_INPUT_FROM       :
			return AVM_STATEMENT_INPUT_FAMILY;

		case AVM_OPCODE_INPUT_ENV        :
			return AVM_STATEMENT_INPUT_ENV_FAMILY;

		case AVM_OPCODE_INPUT_RDV        :
			return AVM_STATEMENT_INPUT_SYNC_FAMILY;

		case AVM_OPCODE_INPUT_MULTI_RDV  :
			return AVM_STATEMENT_INPUT_SYNC_FAMILY;

		case AVM_OPCODE_INPUT_BUFFER     :
			return AVM_STATEMENT_INPUT_ASYNC_FAMILY;
		case AVM_OPCODE_INPUT_BROADCAST  :
			return AVM_STATEMENT_INPUT_ASYNC_FAMILY;


		case AVM_OPCODE_OUTPUT           :
		case AVM_OPCODE_OUTPUT_TO        :
			return AVM_STATEMENT_OUTPUT_FAMILY;

		case AVM_OPCODE_OUTPUT_ENV       :
			return AVM_STATEMENT_OUTPUT_ENV_FAMILY;

		case AVM_OPCODE_OUTPUT_RDV       :
			return AVM_STATEMENT_OUTPUT_SYNC_FAMILY;

		case AVM_OPCODE_OUTPUT_MULTI_RDV :
			return AVM_STATEMENT_OUTPUT_SYNC_FAMILY;

		case AVM_OPCODE_OUTPUT_BUFFER    :
			return AVM_STATEMENT_OUTPUT_ASYNC_FAMILY;

		case AVM_OPCODE_OUTPUT_BROADCAST :
			return AVM_STATEMENT_OUTPUT_ASYNC_FAMILY;

		case AVM_OPCODE_ASSIGN           :
		case AVM_OPCODE_ASSIGN_AFTER     :
		case AVM_OPCODE_ASSIGN_OP        :
		case AVM_OPCODE_ASSIGN_OP_AFTER  :
		case AVM_OPCODE_ASSIGN_REF       :
		case AVM_OPCODE_ASSIGN_MACRO     :
		case AVM_OPCODE_ASSIGN_NEWFRESH  :
		case AVM_OPCODE_ASSIGN_RESET     :
			return AVM_STATEMENT_BASIC_FAMILY;

		default: return AVM_STATEMENT_UNDEFINED_FAMILY;
	}
}


IStatementFamily::avm_opcode_family
IStatementFamily::computeStatementFamily(AvmCode * aCode)
{
	avm_opcode_family opcodeFamily =
			computeStatementFamily( aCode->getOptimizedOpCode() );

	AvmCode::iterator it = aCode->begin();
	AvmCode::iterator itEnd = aCode->end();
	for( ; it != itEnd ; ++it )
	{
		if( (*it).is< AvmCode >() )
		{
			opcodeFamily = opcodeFamily |
					computeStatementFamily( (*it).to_ptr< AvmCode >() );
		}
	}

	return( opcodeFamily );
}


std::string IStatementFamily::strStatementFamily(avm_opcode_family mask) const
{
	std::ostringstream ossFamily;

	const std::string SEPARATOR = " | ";
	std::string sep = "";

	avm_opcode_family opcodeFamily = theStatementFamily & mask;

	if( opcodeFamily == AVM_STATEMENT_UNDEFINED_FAMILY )
	{
		return( "<?opcode>" );
	}

	if( (opcodeFamily & AVM_STATEMENT_BASIC_FAMILY) != 0 )
	{
		ossFamily << sep << "basic"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_GUARD_FAMILY) != 0 )
	{
		ossFamily << sep << "guard"; sep = SEPARATOR;
	}

	if( (opcodeFamily & AVM_STATEMENT_INPUT_FAMILY) != 0 )
	{
		ossFamily << sep << "input"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_INPUT_ENV_FAMILY) != 0 )
	{
		ossFamily << sep << "input#env"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_INPUT_SYNC_FAMILY) != 0 )
	{
		ossFamily << sep << "input#sync"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_INPUT_ASYNC_FAMILY) != 0 )
	{
		ossFamily << sep << "input#async"; sep = SEPARATOR;
	}

	if( (opcodeFamily & AVM_STATEMENT_OUTPUT_FAMILY) != 0 )
	{
		ossFamily << sep << "output"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_OUTPUT_ENV_FAMILY) != 0 )
	{
		ossFamily << sep << "output#env"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_OUTPUT_SYNC_FAMILY) != 0 )
	{
		ossFamily << sep << "output#sync"; sep = SEPARATOR;
	}
	if( (opcodeFamily & AVM_STATEMENT_OUTPUT_ASYNC_FAMILY) != 0 )
	{
		ossFamily << sep << "output#async"; sep = SEPARATOR;
	}


	return( ossFamily.str() );
}


}
