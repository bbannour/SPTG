/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 févr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Z3_C_Solver.h"

/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_Z3_C_ )

#include <fstream>
#include <memory>

#include <util/avm_vfs.h>

#include <fml/expression/AvmCode.h>
#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfData.h>

#include <fml/type/TypeManager.h>

#include <fml/workflow/WObject.h>

#include <z3_api.h>


namespace sep
{

/*
 *******************************************************************************
 * ID
 *******************************************************************************
 */
std::string Z3Solver::ID = "Z3";

std::string Z3Solver::DESCRIPTION = R""""(Z3
	High-performance Theorem Prover 
	https://github.com/Z3Prover/z3)"""";

std::uint64_t Z3Solver::SOLVER_SESSION_ID = 1;


/**
   \brief Display a symbol in the given output stream.
 */
static void display_symbol(OutStream & os, Z3_context ctx, Z3_symbol s)
{
	switch (Z3_get_symbol_kind(ctx, s)) {
		case Z3_INT_SYMBOL:
			os << "$" << Z3_get_symbol_int(ctx, s);
			break;
		case Z3_STRING_SYMBOL:
			os << Z3_get_symbol_string(ctx, s);
			break;
		default:
			AVM_OS_FATAL_ERROR_EXIT
					<< "unreachable code was reached !!!"
					<< SEND_EXIT;
			break;
	}
}

/**
   \brief Display the given type.
 */
static void display_sort(OutStream & os, Z3_context ctx, Z3_sort ty)
{
	switch (Z3_get_sort_kind(ctx, ty)) {
		case Z3_UNINTERPRETED_SORT:
			display_symbol(os, ctx, Z3_get_sort_name(ctx, ty));
			break;
		case Z3_BOOL_SORT:
			os << "bool";
			break;
		case Z3_INT_SORT:
			os << "int";
			break;
		case Z3_REAL_SORT:
			os << "real";
			break;
		case Z3_BV_SORT:
			os << "bv" << Z3_get_bv_sort_size(ctx, ty);
			break;
		case Z3_ARRAY_SORT:
			os << "[";
			display_sort(os, ctx, Z3_get_array_sort_domain(ctx, ty));
			os << "->";
			display_sort(os, ctx, Z3_get_array_sort_range(ctx, ty));
			os << "]";
			break;
		case Z3_DATATYPE_SORT:
			if (Z3_get_datatype_sort_num_constructors(ctx, ty) != 1)
			{
				os << Z3_sort_to_string(ctx,ty);
				break;
			}
			{
				unsigned num_fields = Z3_get_tuple_sort_num_fields(ctx, ty);
				unsigned i;
				os << "(";
				for (i = 0; i < num_fields; i++) {
					Z3_func_decl field = Z3_get_tuple_sort_field_decl(ctx, ty, i);
					if (i > 0) {
						os << ", ";
					}
					display_sort(os, ctx, Z3_get_range(ctx, field));
				}
				os << ")";
				break;
			}
		default:
			os << "unknown[";
			display_symbol(os, ctx, Z3_get_sort_name(ctx, ty));
			os << "]";
			break;
	}
}

/**
   \brief Custom ast pretty printer.

   This function demonstrates how to use the API to navigate terms.
 */
static void display_ast(OutStream & os, Z3_context ctx, Z3_ast v)
{
	switch (Z3_get_ast_kind(ctx, v)) {
		case Z3_NUMERAL_AST: {
			Z3_sort t;
			os << Z3_get_numeral_string(ctx, v);
			t = Z3_get_sort(ctx, v);
			os << ":";
			display_sort(os, ctx, t);
			break;
		}
		case Z3_APP_AST: {
			Z3_app app = Z3_to_app(ctx, v);
			unsigned num_fields = Z3_get_app_num_args(ctx, app);
			Z3_func_decl d = Z3_get_app_decl(ctx, app);
			os << Z3_func_decl_to_string(ctx, d);
			if (num_fields > 0) {
				os << "[";
				display_ast(os, ctx, Z3_get_app_arg(ctx, app, 0));
				for (unsigned i = 1; i < num_fields; i++) {
					os << ", ";
					display_ast(os, ctx, Z3_get_app_arg(ctx, app, i));
				}
				os << "]";
			}
			break;
		}
		case Z3_QUANTIFIER_AST: {
			os << "quantifier";
			break;
		}
		default: {
			os << "#unknown";
			break;
		}
	}
}

/**
   \brief Custom function interpretations pretty printer.
 */
//void display_function_interpretations(OutStream & out, Z3_context c, Z3_model m)
//{
//    unsigned num_functions, i;
//
//    out << "function interpretations:" << EOL;
//
//    num_functions = Z3_model_get_num_funcs(c, m);
//    for (i = 0; i < num_functions; i++) {
//        Z3_func_decl fdecl;
//        Z3_symbol name;
//        Z3_ast func_else;
//        unsigned num_entries = 0, j;
//        Z3_func_interp_opt finterp;
//
//        fdecl = Z3_model_get_func_decl(c, m, i);
//        finterp = Z3_model_get_func_interp(c, m, fdecl);
//        Z3_func_interp_inc_ref(c, finterp);
//        name = Z3_get_decl_name(c, fdecl);
//        display_symbol(out, c, name);
//        out << " = {";
//        if (finterp)
//          num_entries = Z3_func_interp_get_num_entries(c, finterp);
//        for (j = 0; j < num_entries; j++) {
//            unsigned num_args, k;
//            Z3_func_entry fentry = Z3_func_interp_get_entry(c, finterp, j);
//	    Z3_func_entry_inc_ref(c, fentry);
//            if (j > 0) {
//                out << ", ";
//            }
//            num_args = Z3_func_entry_get_num_args(c, fentry);
//            out << "(";
//            for (k = 0; k < num_args; k++) {
//                if (k > 0) {
//                    out << ", ";
//                }
//                display_ast(out, c, Z3_func_entry_get_arg(c, fentry, k));
//            }
//            out << "|->";
//            display_ast(out, c, Z3_func_entry_get_value(c, fentry));
//            out << ")";
//	    Z3_func_entry_dec_ref(c, fentry);
//        }
//        if (num_entries > 0) {
//            out << ", ";
//        }
//        out << "(else|->";
//        func_else = Z3_func_interp_get_else(c, finterp);
//        display_ast(out, c, func_else);
//        out << ")}\n";
//	Z3_func_interp_dec_ref(c, finterp);
//    }
//}


/**
   \brief Custom model pretty printer.
 */
//static void display_model(OutStream & out, Z3_context c, Z3_model m)
//{
//    unsigned num_constants;
//    unsigned i;
//
//    if (!m) return;
//
//    num_constants = Z3_model_get_num_consts(c, m);
//    for (i = 0; i < num_constants; i++) {
//        Z3_symbol name;
//        Z3_func_decl cnst = Z3_model_get_const_decl(c, m, i);
//        Z3_ast a, v;
//        bool ok;
//        name = Z3_get_decl_name(c, cnst);
//        display_symbol(out, c, name);
//        out << " = ";
//        a = Z3_mk_app(c, cnst, 0, 0);
//        v = a;
//        ok = Z3_model_eval(c, m, a, 1, &v);
//        display_ast(out, c, v);
//        out << EOL;
//    }
//    display_function_interpretations(out, c, m);
//}




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * CONSTRUCTOR
 * Default
 */
Z3Solver::Z3Solver(bool forceUniqueID)
: base_this_type(nullptr, nullptr),
CONFIG ( nullptr ),
CONTEXT( nullptr ),
SOLVER ( nullptr )
{
	mLogFolderLocation = VFS::ProjectDebugPath + "/z3_c/";

	this->enableForceUniqueID(forceUniqueID);
}


/**
 * CONFIGURE
 */
bool Z3Solver::configure(const WObject * wfFilterObject)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	std::string logFolderLocation = VFS::ProjectDebugPath + "/z3_c/";

	if ( not VFS::checkWritingFolder(logFolderLocation, false) )
	{
		AVM_OS_LOG << " Z3Solver::configure :> Error: The folder "
				<< "`" << logFolderLocation	<< "' "
				<< "---> doesn't exist or is not writable !!!"
				<< std::endl << std::endl;

		return( false );
	}

AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( true );
}



/**
 * CREATE - DESTROY
 * ValidityChecker
 */

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_error_code e)
{
	AVM_OS_EXIT( FAILED )
			<< "Z3Solver:> Incorrect use of the solver, error code << "
			<< e << " >>"
			<< SEND_EXIT;
}

bool Z3Solver::createChecker()
{
	CONFIG = Z3_mk_config();

	Z3_set_param_value(CONFIG, "MODEL", "true");

	CONTEXT = Z3_mk_context(CONFIG);

//	Z3_set_error_handler(CONTEXT, error_handler);

	SOLVER  = Z3_mk_solver(CONTEXT);
	Z3_solver_inc_ref(CONTEXT, SOLVER);


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< "log_" << SOLVER_SESSION_ID << ".z3" );
	Z3_open_log( fileLocation.c_str() );

	if( not Z3_open_log( fileLocation.c_str() ) )
	{
		AVM_OS_LOG << " Z3Solver::createChecker :> Failed to open the log file "
				<< "`" << fileLocation	<< "' !!!"
				<< std::endl << std::endl;
		return( false );
	}

	Z3_set_ast_print_mode(CONTEXT, Z3_PRINT_SMTLIB2_COMPLIANT);

AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


	SMT_TYPE_BOOL      = Z3_mk_bool_sort(CONTEXT);

	SMT_TYPE_ENUM      = Z3_mk_int_sort(CONTEXT);

	SMT_TYPE_UINTEGER  = Z3_mk_int_sort(CONTEXT);
	SMT_TYPE_INTEGER   = Z3_mk_int_sort(CONTEXT);

	SMT_TYPE_URATIONAL = Z3_mk_real_sort(CONTEXT);
	SMT_TYPE_RATIONAL  = Z3_mk_real_sort(CONTEXT);

	SMT_TYPE_UREAL     = Z3_mk_real_sort(CONTEXT);
	SMT_TYPE_REAL      = Z3_mk_real_sort(CONTEXT);

	SMT_CST_BOOL_TRUE  = Z3_mk_true(CONTEXT);
	SMT_CST_BOOL_FALSE = Z3_mk_false(CONTEXT);

	SMT_CST_INT_ZERO   = Z3_mk_int(CONTEXT, 0, SMT_TYPE_INTEGER);
	SMT_CST_INT_ONE    = Z3_mk_int(CONTEXT, 1, SMT_TYPE_INTEGER);

	resetTable();

	return( true );
}


bool Z3Solver::destroyChecker()
{
	resetTable();

	SMT_TYPE_BOOL      = nullptr;

	SMT_TYPE_ENUM      = nullptr;

	SMT_TYPE_UINTEGER  = nullptr;
	SMT_TYPE_INTEGER   = nullptr;

	SMT_TYPE_BV32      = nullptr;
	SMT_TYPE_BV64      = nullptr;

	SMT_TYPE_URATIONAL = nullptr;
	SMT_TYPE_RATIONAL  = nullptr;

	SMT_TYPE_UREAL     = nullptr;
	SMT_TYPE_REAL      = nullptr;

	SMT_TYPE_NUMBER    = nullptr;

	SMT_TYPE_STRING    = nullptr;

	SMT_CST_BOOL_TRUE  = nullptr;
	SMT_CST_BOOL_FALSE = nullptr;

	SMT_CST_INT_ZERO   = nullptr;
	SMT_CST_INT_ONE    = nullptr;

	Z3_close_log();

	if( SOLVER != nullptr )
	{
		Z3_solver_dec_ref(CONTEXT, SOLVER);

		SOLVER = nullptr;
	}

	if( CONTEXT != nullptr )
	{
		Z3_del_context(CONTEXT);

		CONTEXT = nullptr;
	}

	if( CONFIG != nullptr )
	{
		Z3_del_config(CONFIG);
		CONFIG = nullptr;
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	++SOLVER_SESSION_ID;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( true );
}

bool Z3Solver::resetTable()
{
	base_this_type::resetTable();

	mTableOfParameterDecl.push_back( nullptr );

	mTableOfParameterExpr.push_back( nullptr );

	mBitsetOfConstrainedParameter.push_back( false );
	mBitsetOfPositiveParameter.push_back( false );
	mBitsetOfStrictlyPositiveParameter.push_back( false );

	return( true );
}



/**
 * PROVER
 */
bool Z3Solver::isSubSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	return( true );
}

bool Z3Solver::isEqualSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	return( true );
}

SolverDef::SATISFIABILITY_RING Z3Solver::isSatisfiable(const BF & aCondition)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	createChecker();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Solver::isSatisfiable(...) :"
			<< SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_sat(aCondition);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	Z3_ast z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">" << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "\t";
		display_ast(AVM_OS_TRACE, CONTEXT, z3Condition);
		AVM_OS_TRACE << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH

	AVM_OS_TRACE << "\t" << Z3_ast_to_string(CONTEXT, z3Condition) << std::endl;

	if( mBitsetOfConstrainedParameter.anyTrue() )
	{
		AVM_OS_TRACE << "REQUIRED ASSERTION : " << mBitsetOfConstrainedParameter
				<< " for CONSTRAINED type" << std::endl;
	}
	if( mBitsetOfPositiveParameter.anyTrue() )
	{
		AVM_OS_TRACE << "REQUIRED ASSERTION : " << mBitsetOfPositiveParameter
				<< " for POSITIVE type" << std::endl;
	}
	if( mBitsetOfStrictlyPositiveParameter.anyTrue() )
	{
		AVM_OS_TRACE << "REQUIRED ASSERTION : "
				<< mBitsetOfStrictlyPositiveParameter
				<< " for STRICTLY POSITIVE type" << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
	AVM_OS_TRACE << "Z3::CONTEXT :" << SOLVER_SESSION_ID << ">" << std::endl
			<< std::string( Z3_solver_to_string(CONTEXT, SOLVER) ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

	if( z3Condition != nullptr )
	{
		if( mBitsetOfConstrainedParameter.anyTrue() )
		{
			appendPossitiveAssertion();
		}


		Z3_solver_assert(CONTEXT, SOLVER, z3Condition);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
	dbg_smt(SOLVER);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

		switch( Z3_solver_check(CONTEXT, SOLVER) )
		{
			case Z3_L_TRUE:
			{
				satisfiability = SolverDef::SATISFIABLE;
				break;
			}

			case Z3_L_FALSE:
			{
				satisfiability = SolverDef::UNSATISFIABLE;
				break;
			}

			case Z3_L_UNDEF:
			{
				satisfiability = SolverDef::UNKNOWN_SAT;
				break;
			}

			default:
			{
				satisfiability = SolverDef::ABORT_SAT;
				break;
			}
		}
	}

	destroyChecker();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "result :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( satisfiability );
}


/**
 * SOLVER
 */
bool Z3Solver::solveImpl(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	createChecker();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Solver::solve(...) :"
			<< SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_model(aCondition, dataVector, valuesVector);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	Z3_ast z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">" << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "\t";
		display_ast(AVM_OS_TRACE, CONTEXT, z3Condition);
		AVM_OS_TRACE << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH

	AVM_OS_TRACE << "\t" << Z3_ast_to_string(CONTEXT, z3Condition) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
	AVM_OS_TRACE << "Z3::CONTEXT :" << SOLVER_SESSION_ID << ">" << std::endl
			<< std::string( Z3_solver_to_string(CONTEXT, SOLVER) ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

	if( z3Condition != nullptr )
	{
		Z3_solver_assert(CONTEXT, SOLVER, z3Condition);

		switch( Z3_solver_check(CONTEXT, SOLVER) )
		{
			case Z3_L_TRUE:
			{
				satisfiability = SolverDef::SATISFIABLE;

				Z3_model model = Z3_solver_get_model(CONTEXT, SOLVER);
				if( model != nullptr )
				{
					Z3_model_inc_ref(CONTEXT, model);
				}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Model sat:" << SOLVER_SESSION_ID << ">" << std::endl
			<< Z3_model_to_string(CONTEXT, model) << std::endl;

	dbg_smt(SOLVER, true);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

				unsigned num_constants = Z3_model_get_num_consts(CONTEXT, model);
				for( unsigned index = 0 ; index < num_constants ; ++index )
				{
					Z3_func_decl model_const =
							Z3_model_get_const_decl(CONTEXT, model, index);

					Z3_symbol symbol = Z3_get_decl_name(CONTEXT, model_const);

					int offset = mTableOfParameterDecl.find(symbol);
					if( offset >= 0 )
					{
						dataVector.append( mTableOfParameterInstance[offset] );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	display_symbol(AVM_OS_TRACE, CONTEXT, symbol);
	AVM_OS_TRACE << " := ";
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

						Z3_ast app = Z3_mk_app(CONTEXT, model_const, 0, 0);

						Z3_ast value = app;

						bool ok = Z3_model_eval(
								CONTEXT, model, app, true, &value);

						if( ok )
						{
							BF bfVal = to_baseform(model, value);

							valuesVector.append( bfVal.valid() ?
									bfVal : dataVector.back() );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	display_ast(AVM_OS_TRACE, CONTEXT, value);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
						}
						else
						{
							valuesVector.append( BF::REF_NULL );

							AVM_OS_FATAL_ERROR_EXIT
									<< "Z3Solver::solve :> "
										"failed to Z3_model_eval << "
									<< Z3_ast_to_string(CONTEXT, app)
									<< " >> !!!"
									<< SEND_EXIT;
						}
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::solve :> "
								"unfound parameter instance for Z3 symbol << "
								<< Z3_get_symbol_string(CONTEXT, symbol)
								<< " >> !!!"
								<< SEND_EXIT;
					}
				}

				if( model != nullptr )
				{
					Z3_model_dec_ref(CONTEXT, model);
				}

				break;
			}

			case Z3_L_FALSE:
			{
				satisfiability = SolverDef::UNSATISFIABLE;
				break;
			}

			case Z3_L_UNDEF:
			{
				satisfiability = SolverDef::UNKNOWN_SAT;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
				AVM_OS_TRACE << "Z3Model undef:" << SOLVER_SESSION_ID << ">"
						<< std::endl
						<< std::string( Z3_solver_to_string(CONTEXT, SOLVER) )
						<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

				break;
			}

			default:
			{
				satisfiability = SolverDef::ABORT_SAT;
				break;
			}
		}
	}

	destroyChecker();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "solve :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( satisfiability == SolverDef::SATISFIABLE );
}



/**
 * TOOLS
 */

Z3_sort Z3Solver::getZ3Type(const ITypeSpecifier & bts) const
{
	if( bts.isTypedBoolean() )
	{
		return( SMT_TYPE_BOOL );
	}
	else if( bts.isTypedEnum() )
	{
		return( SMT_TYPE_ENUM );
		// TODO Attention : il faudrait rajouter les contraintes
		// d'intervalle pour le type énuméré
	}
	else if( bts.weaklyTypedUInteger() )
	{
		return( SMT_TYPE_UINTEGER );
	}
	else if( bts.weaklyTypedInteger() )
	{
		return( SMT_TYPE_INTEGER );
	}

	else if( bts.weaklyTypedURational() )
	{
		return( SMT_TYPE_URATIONAL );
	}
	else if( bts.weaklyTypedRational() )
	{
		return( SMT_TYPE_RATIONAL );
	}

	else if( bts.weaklyTypedUReal() )
	{
		return( SMT_TYPE_UREAL );
	}
	else if( bts.weaklyTypedReal() )
	{
		return( SMT_TYPE_REAL );
	}

	else if( bts.isTypedMachine() )
	{
		// TODO:> Consolidation après TEST
		return( SMT_TYPE_INTEGER );
	}

	return( SMT_TYPE_REAL );
}


Z3_ast Z3Solver::getParameterExpr(const BF & bfParameter)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bfParameter.to< InstanceOfData >() );

	if( aParameter.getMark() == 0 )
	{
		aParameter.setMark( mTableOfParameterInstance.size() );
		mTableOfParameterInstance.append( bfParameter );

		mTableOfParameterDecl.push_back( Z3_mk_string_symbol( CONTEXT,
				uniqParameterID( aParameter).c_str() ) );

		const BaseTypeSpecifier & paramTypeSpecifier =
				aParameter.referedTypeSpecifier();

		mTableOfParameterExpr.push_back( Z3_mk_const( CONTEXT,
				mTableOfParameterDecl.last(), getZ3Type(paramTypeSpecifier)) );

		mBitsetOfConstrainedParameter.push_back(
				paramTypeSpecifier.couldGenerateConstraint() );

		mBitsetOfPositiveParameter.push_back(
				paramTypeSpecifier.isTypedPositiveNumber() );

		mBitsetOfStrictlyPositiveParameter.push_back(
				paramTypeSpecifier.isTypedStrictlyPositiveNumber() );
	}

	return( mTableOfParameterExpr.at( aParameter.getMark() ) );
}


Z3_ast Z3Solver::getBoundParameterExpr(
		const BF & bfParameter, ARGS & boundVarConstraints)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bfParameter.to< InstanceOfData >() );

	aParameter.setMark( mTableOfParameterInstance.size() );
	mTableOfParameterInstance.append( bfParameter );

	mTableOfParameterDecl.push_back( Z3_mk_string_symbol( CONTEXT,
			uniqParameterID( aParameter ).c_str() ) );

	const BaseTypeSpecifier & paramTypeSpecifier =
			aParameter.referedTypeSpecifier();

	Z3_ast paramExpr = Z3_mk_const( CONTEXT, // Z3_mk_bound(
			mTableOfParameterDecl.last(), getZ3Type(paramTypeSpecifier));

	mTableOfParameterExpr.push_back( paramExpr );

	mBitsetOfStrictlyPositiveParameter.push_back( false );
	mBitsetOfPositiveParameter.push_back( false );
	mBitsetOfConstrainedParameter.push_back( false );

	if( paramTypeSpecifier.isTypedStrictlyPositiveNumber() )
	{
		boundVarConstraints.next(
				Z3_mk_gt(CONTEXT, paramExpr, SMT_CST_INT_ZERO) );
	}
	else if( paramTypeSpecifier.isTypedPositiveNumber() )
	{
		boundVarConstraints.next(
				Z3_mk_ge(CONTEXT, paramExpr, SMT_CST_INT_ZERO) );
	}
	else
	{
		boundVarConstraints.next( SMT_CST_BOOL_TRUE );
	}

	return( mTableOfParameterExpr.at( aParameter.getMark() ) );
}


Z3_ast Z3Solver::getVariableExpr(InstanceOfData * aVar, std::size_t varID)
{
	if( mTableOfVariableExpr.size() <= varID )
	{
		mTableOfVariableDecl.push_back( Z3_mk_string_symbol( CONTEXT,
				uniqVariableID( *aVar, varID ).c_str() ) );

		mTableOfVariableExpr.push_back( Z3_mk_const( CONTEXT,
				mTableOfVariableDecl.last(),
				getZ3Type(aVar->getTypeSpecifier()) ) );
	}

	return( mTableOfVariableExpr.at( varID ) );
}


void Z3Solver::appendPossitiveAssertion()
{
	std::size_t endOffset = mBitsetOfConstrainedParameter.size();
	for( std::size_t offset = 1 ; offset < endOffset ; ++offset )
	{
		if( mBitsetOfStrictlyPositiveParameter[offset] )
		{
			Z3_solver_assert(CONTEXT, SOLVER, Z3_mk_gt(
					CONTEXT, mTableOfParameterExpr[offset], SMT_CST_INT_ZERO ));
		}
		else if( mBitsetOfPositiveParameter[offset] )
		{
			Z3_solver_assert(CONTEXT, SOLVER, Z3_mk_ge(
					CONTEXT, mTableOfParameterExpr[offset], SMT_CST_INT_ZERO ));
		}
	}
}


Z3_ast Z3Solver::safe_from_baseform(const BF & exprForm)
{
	Z3_ast e = nullptr;

	try
	{
		if( (e = from_baseform(exprForm)) == nullptr )
		{
			AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
					<< "\tZ3Solver::safe_from_baseform< unknown::error :"
					<< SOLVER_SESSION_ID << ">" << std::endl
					<< REPEAT("--------", 10) << std::endl
					<< "\tFailed to CONVERT sep::fml::expression to Z3::Expr:>" << std::endl
					<< "\t  " << exprForm.str() << std::endl
					<< REPEAT("********", 10) << std::endl;

			destroyChecker();
		}
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tZ3Solver::safe_from_baseform< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\tFailed to CONVERT sep::fml::expression to Z3::Expr:>" << std::endl
				<< "\t  " << exprForm.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();
	}

	return( e );
}



Z3_ast Z3Solver::from_baseform(const BF & exprForm)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( exprForm ) << "expression !!!"
			<< SEND_EXIT;

	switch( exprForm.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = exprForm.to< AvmCode >();

			switch( aCode.getAvmOpCode() )
			{
				// COMPARISON OPERATION
				case AVM_OPCODE_EQ:
				{
					return( Z3_mk_eq( CONTEXT,
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_NEQ:
				{
					return( Z3_mk_not( CONTEXT, Z3_mk_eq( CONTEXT,
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) ) );

//					ARGS arg( 2 );
//
//					arg.next( from_baseform(aCode.first()) );
//					arg.next( from_baseform(aCode.second()) );
//
//					return( Z3_mk_distinct(CONTEXT, 2, arg->table) );
				}

				case AVM_OPCODE_LT:
				{
					return( Z3_mk_lt( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_LTE:
				{
					return( Z3_mk_le( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_GT:
				{
					return( Z3_mk_gt( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_GTE:
				{
					return( Z3_mk_ge( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}


				case AVM_OPCODE_CONTAINS:
				{
					const BuiltinCollection & aCollection =
							aCode.first().to< BuiltinCollection >();

					if( aCollection.singleton() )
					{
						return( Z3_mk_eq( CONTEXT,
								from_baseform(aCollection.at(0)),
								from_baseform(aCode.second())) );
					}
					else if( aCollection.populated() )
					{
						ARGS arg( aCollection.size() );
						const BF & elt = aCode.second();

						for( std::size_t offset = 0 ; arg.hasNext() ; ++offset )
						{
							arg.next( Z3_mk_eq( CONTEXT,
									from_baseform(elt),
									from_baseform(aCollection.at(offset)) ) );
						}

						return( Z3_mk_or(CONTEXT, arg->count, arg->table) );
					}
					else
					{
						return( SMT_CST_BOOL_FALSE );
					}
				}


				// LOGICAL OPERATION
				case AVM_OPCODE_NOT:
				{
					return( Z3_mk_not( CONTEXT, from_baseform(aCode.first())) );
				}

				case AVM_OPCODE_AND:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_and(CONTEXT, arg->count, arg->table) );
				}

				case AVM_OPCODE_NAND:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_not( CONTEXT,
							Z3_mk_and(CONTEXT, arg->count, arg->table) ) );
				}

//				case AVM_OPCODE_XAND:
//				{
//					ARGS arg( 2 );
//
//					arg.next( Z3_mk_not( CONTEXT,
//							from_baseform(aCode.first())) );
//					arg.next( from_baseform(aCode.second()) );
//
//					return( Z3_mk_and(CONTEXT, arg->table, 2) );
//
//					return( mVC->orExpr(
//							mVC->andExpr(from_baseform(aCode.first()),
//									from_baseform(aCode.second())),
//							mVC->andExpr(mVC->notExpr(from_baseform(aCode.first())),
//									mVC->notExpr(from_baseform(aCode.second()))) ) );
//				}


				case AVM_OPCODE_OR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_or(CONTEXT, arg->count, arg->table) );
				}

				case AVM_OPCODE_NOR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_not( CONTEXT,
							Z3_mk_or(CONTEXT, arg->count, arg->table) ) );
				}

//				case AVM_OPCODE_BAND:
//				{
//					return( Z3_mk_bv_and( CONTEXT,
//							from_baseform(aCode.first()),
//							from_baseform(aCode.second()) ) );
//				}
//
//				case AVM_OPCODE_BOR:
//				{
//					return( Z3_mk_bv_or( CONTEXT,
//							from_baseform(aCode.first()),
//							from_baseform(aCode.second()) ) );
//				}
//
//				case AVM_OPCODE_LSHIFT:
//				{
//					if( aCode.second().isInteger() )
//					{
//						return( Z3_mk_bv_shift_left0( CONTEXT,
//								from_baseform(aCode.first()),
//								aCode.second().toInteger()) );
//
//					}
//					else
//					{
//						AVM_OS_FATAL_ERROR_EXIT
//								<< "Unexpected second argument for "
//									"newFixedLeftShiftExpr !!!\n"
//								<< aCode.toString( AVM_TAB1_INDENT )
//								<< SEND_EXIT;
//
//						return( nullptr );
//					}
//				}
//
//				case AVM_OPCODE_RSHIFT:
//				{
//					if( aCode.second().isInteger() )
//					{
//						return( Z3_mk_bv_shift_right0( CONTEXT,
//								from_baseform(aCode.first()),
//								aCode.second().toInteger()) );
//
//					}
//					else
//					{
//						AVM_OS_FATAL_ERROR_EXIT
//								<< "Unexpected second argument for "
//									"newFixedRightShiftExpr !!!\n"
//								<< aCode.toString( AVM_TAB1_INDENT )
//								<< SEND_EXIT;
//
//						return( nullptr );
//					}
//				}

				case AVM_OPCODE_XOR:
				{
					return( Z3_mk_xor( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_XNOR:
				{
					return( Z3_mk_not( CONTEXT, Z3_mk_xor( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) ) );
				}

				case AVM_OPCODE_IMPLIES:
				{
					return( Z3_mk_implies( CONTEXT,
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_EXISTS:
				{
					std::size_t boundVarCount = aCode.size()  - 1;

					Z3_app arg[ boundVarCount ];

					ARGS boundVarConstraints( aCode.size() );

					for (std::size_t offset = 0; offset < boundVarCount; ++offset)
					{
						arg[ offset ] = (Z3_app) getBoundParameterExpr(
								aCode[ offset ], boundVarConstraints );
					}

					boundVarConstraints.next(
							from_baseform(aCode[ boundVarCount ]) );

					return( Z3_mk_exists_const(CONTEXT,
							0, boundVarCount, arg, 0, 0,
							Z3_mk_and(CONTEXT, boundVarConstraints->count,
									boundVarConstraints->table) ));
				}

				case AVM_OPCODE_FORALL:
				{
					std::size_t boundVarCount = aCode.size()  - 1;

					Z3_app arg[ boundVarCount ];

					ARGS boundVarConstraints( boundVarCount );

					for (std::size_t offset = 0; offset < boundVarCount; ++offset)
					{
						arg[ offset ] = (Z3_app) getBoundParameterExpr(
								aCode[ offset ], boundVarConstraints );
					}

					Z3_ast forallCondition =
							(boundVarCount == 1) ? boundVarConstraints[0]
							: Z3_mk_and(CONTEXT, boundVarCount,
									boundVarConstraints->table);

					forallCondition = Z3_mk_implies( CONTEXT, forallCondition,
							from_baseform(aCode[ boundVarCount ]) );

					return( Z3_mk_forall_const(CONTEXT,
			        		0, boundVarCount, arg, 0, 0, forallCondition) );
				}


				// ARITHMETIC OPERATION
				case AVM_OPCODE_PLUS:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_add(CONTEXT, arg->count, arg->table) );
				}

				case AVM_OPCODE_UMINUS:
				{
					return( Z3_mk_unary_minus(CONTEXT,
							from_baseform(aCode.first())) );
				}

				case AVM_OPCODE_MINUS:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_sub(CONTEXT, arg->count, arg->table) );
				}

				case AVM_OPCODE_MULT:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( Z3_mk_mul(CONTEXT, arg->count, arg->table) );
				}

				case AVM_OPCODE_DIV:
				{
					return( Z3_mk_div( CONTEXT,
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_POW:
				{
					if( ExpressionFactory::isPosInteger(aCode.second()) )
					{
//						return( Z3_mk_power( CONTEXT,
//								from_baseform(aCode.first()),
//								from_baseform(aCode.second()) ) );

						avm_uinteger_t power =
								ExpressionFactory::toUInteger(aCode.second());

						ARGS arg( power );

						arg.next( from_baseform(aCode.first()) );

						while( arg.hasNext() )
						{
							arg.next( arg[ 0 ] );
						}

						return( Z3_mk_mul(CONTEXT, arg->count, arg->table) );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::from_baseform:> Unsupported "
								"expression Operator << AVM_OPCODE_POW >> !!!"
								<< SEND_EXIT;

						return( nullptr );
					}
				}

				case AVM_OPCODE_MOD:
				{
					return( Z3_mk_mod( CONTEXT,
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}


				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Z3Solver::from_baseform:> Unexpected "
								"OBJECT KIND for execution !!!\n"
							<< aCode.toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return( nullptr );
				}
			}

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			return( getParameterExpr( exprForm ) );
		}

		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( exprForm.to< Boolean >().getValue() ?
					SMT_CST_BOOL_TRUE : SMT_CST_BOOL_FALSE );
		}


		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( Z3_mk_int64(CONTEXT,
					exprForm.to< Integer >().toInteger(),
					SMT_TYPE_INTEGER) );

//			return( Z3_mk_numeral(CONTEXT,
//					exprForm.to< Integer >().str().c_str(),
//					SMT_TYPE_INTEGER) );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( Z3_mk_real(CONTEXT,
					exprForm.to< Rational >().toNumerator(),
					exprForm.to< Rational >().toDenominator() ) );

//			return( Z3_mk_numeral( CONTEXT,
//					exprForm.to< Rational >().str().c_str(),
//					SMT_TYPE_REAL) );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( Z3_mk_numeral(CONTEXT,
					exprForm.to< Float >().str().c_str(),
					SMT_TYPE_REAL) );
		}


		case FORM_RUNTIME_ID_KIND:
		{
			return( Z3_mk_int(CONTEXT,
					exprForm.bfRID().getRid(), SMT_TYPE_INTEGER) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Z3Solver::from_baseform:> Unexpected OBJECT KIND << "
					<< exprForm.classKindName() << " >> as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			return( nullptr );
		}
	}

	AVM_OS_FATAL_ERROR_EXIT
			<< "Z3Solver::from_baseform ERROR !!!"
			<< SEND_EXIT;

	return( nullptr );
}


BF Z3Solver::to_baseform(Z3_model model, Z3_ast z3Form)
{
	switch( Z3_get_ast_kind(CONTEXT, z3Form) )
	{
		case Z3_NUMERAL_AST:
		{
			Z3_sort type = Z3_get_sort(CONTEXT, z3Form);

			switch( Z3_get_sort_kind(CONTEXT, type) )
			{
				case Z3_BOOL_SORT:
				{
					switch( Z3_get_bool_value(CONTEXT, z3Form) )
					{
						case Z3_L_TRUE:
						{
							return( ExpressionConstructor::newBoolean( true ) );
						}
						case Z3_L_FALSE:
						{
							return( ExpressionConstructor::newBoolean( false ) );
						}
						case Z3_L_UNDEF:
						default:
						{
							return( ExpressionConstructor::newBoolean(
									Z3_get_numeral_string(CONTEXT, z3Form)) );
						}
					}
				}
				case Z3_INT_SORT:
				{
					{
						int val;
						if( Z3_get_numeral_int(CONTEXT, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newInteger(
									static_cast< avm_integer_t >( val ) ) );
						}
					}
					{
						unsigned val;
						if( Z3_get_numeral_uint(CONTEXT, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newUInteger(
									static_cast< avm_uinteger_t >( val ) ) );
						}
					}
					{
						int64_t val;
						if( Z3_get_numeral_int64(CONTEXT, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newInteger(
									static_cast< avm_integer_t >( val ) ) );
						}
					}
					{
						uint64_t val;
						if( Z3_get_numeral_uint64(CONTEXT, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newUInteger(
									static_cast< avm_uinteger_t >( val ) ) );
						}
					}

					return( ExpressionConstructor::newInteger(
							Z3_get_numeral_string(CONTEXT, z3Form)) );
				}
				case Z3_REAL_SORT:
				{
					int64_t num;
					int64_t den;
					if( Z3_get_numeral_rational_int64(CONTEXT, z3Form, &num, &den) == Z3_L_TRUE )
					{
						return( ExpressionConstructor::newRational(
								static_cast< avm_integer_t >( num ),
								static_cast< avm_integer_t >( den ) ) );
					}

					return( ExpressionConstructor::newFloat(
							Z3_get_numeral_string(CONTEXT, z3Form)) );
				}
				case Z3_UNINTERPRETED_SORT:
				case Z3_BV_SORT:
				case Z3_ARRAY_SORT:
				case Z3_DATATYPE_SORT:
				default:
				{
					return( ExpressionConstructor::newString(
							Z3_get_numeral_string(CONTEXT, z3Form)) );

					break;
				}
			}

			break;
		}
		case Z3_APP_AST:
		{
			Z3_app app = Z3_to_app(CONTEXT, z3Form);

			if( Z3_get_app_num_args(CONTEXT, app) == 0 )
			{
				Z3_func_decl func_decl = Z3_get_app_decl(CONTEXT, app);

				std::string val = Z3_func_decl_to_string(CONTEXT, func_decl);
				if( val == "(define true bool)" )
				{
					return( ExpressionConstructor::newBoolean( true ) );
				}
				else if( val == "(define false bool)" )
				{
					return( ExpressionConstructor::newBoolean( false ) );
				}

//				z3Form = Z3_model_get_const_interp(CONTEXT, model, func_decl);
//
//				return( to_baseform(model, z3Form) );

			}

			break;
		}
		case Z3_QUANTIFIER_AST:
		{
			break;
		}
		default:
		{
			break;
		}
	}

	return( BF::REF_NULL );
}


/**
 * Using file API
 */

SolverDef::SATISFIABILITY_RING Z3Solver::smt_check_sat(const BF & aCondition)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "z3_c_check_sat_"  << SOLVER_SESSION_ID  << ".z3";
	OutStream osFile;
	if ( osFile.open(fileLocation, std::ios_base::out) )
	{
		osFile << ";; z3 " << fileLocation << std::endl;

		if( not to_smt(osFile, aCondition) )
		{
			return( SolverDef::UNKNOWN_SAT );
		}

		// AST SERIALIZATION
//		Z3_ast z3Condition = from_baseform(aCondition);
//		osFile << std::endl << std::endl << "(assert ";
//		display_ast(osFile, CONTEXT, z3Condition);
//		osFile << ")" << std::endl << "(check-sat)" << std::endl;
	}
	else
	{
		return( SolverDef::ABORT_SAT );
	}


	return( satisfiability );
}

bool Z3Solver::smt_check_model(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	BFVector paramVector;

	StringOutStream ossCondition("", "\t", "");
	to_smt(ossCondition, aCondition, paramVector);

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "z3_c_get_model_" << SOLVER_SESSION_ID << ".log";
	OutStream osFile;
	if ( osFile.open(fileLocation, std::ios_base::out) )
	{
		osFile << ";; z3 " << fileLocation << std::endl;
//		osFile << "(echo \"" << aCondition.str() << "\")" << std::endl;

		std::size_t paramCount = paramVector.size();
		for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
		{
			const InstanceOfData & aParam =
					paramVector[ offset ].to< InstanceOfData >();

			osFile << "(declare-const " << uniqParameterID(aParam)
					<< " " << strTypeSmt2(aParam) << ")" << std::endl;
		}

		osFile << "(assert " << ossCondition.str() << ")" << std::endl;

		osFile << "(get-model)" << std::endl;

		// AST SERIALIZATION
		Z3_ast z3Condition = from_baseform(aCondition);
		osFile << std::endl << std::endl << "(assert ";
		display_ast(osFile, CONTEXT, z3Condition);
		osFile << ")" << std::endl << std::endl << "(get-model)" << std::endl;
	}
	else
	{
		return( false );
	}

	return( true );
}



SolverDef::SATISFIABILITY_RING Z3Solver::from_smt_sat(const BF & aCondition)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;


	return( satisfiability );
}

bool Z3Solver::from_smt_model(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	return( true );
}


bool Z3Solver::to_smt(OutStream & os, const BF & aCondition,
		bool enableModelProduction, bool enableChecksat) const
{
	BFVector paramVector;

	StringOutStream ossCondition( os.INDENT );

	to_smt(ossCondition, aCondition, paramVector);

//	BF fullCondition = completeUsingDataTypeConstraint(aCondition, paramVector)


//	os << ";; Getting info" << std::endl
//		<< "(get-info :name)"    << std::endl
//		<< "(get-info :version)" << std::endl;

//	os << "(echo \"" << aCondition.str() << "\")" << std::endl;

	std::size_t paramCount = paramVector.size();
	for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
	{
		if( paramVector[ offset ].is< InstanceOfData >() )
		{
			const InstanceOfData & aParam =
					paramVector[ offset ].to< InstanceOfData >();

			os << "(declare-const " << uniqParameterID(aParam)
					<< " " << strTypeSmt2(aParam) << ")" << EOL;
			if( aParam.getTypeSpecifier().isTypedStrictlyPositiveNumber() )
			{
				os << "(assert (< 0 " << uniqParameterID(aParam) <<"))" << EOL;
			}
			else if( aParam.getTypeSpecifier().isTypedPositiveNumber() )
			{
				os << "(assert (<= 0 " << uniqParameterID(aParam) <<"))" << EOL;
			}
		}
		else if( paramVector[ offset ].is< Variable >() )
		{
			const Variable & aVariable = paramVector[ offset ].to< Variable >();

			std::string varType;
			bool isTypedStrictlyPositive = false;
			bool isTypedPositive = false;
			if( aVariable.hasTypeSpecifier())
			{
				varType = strTypeSmt2(aVariable.getTypeSpecifier());
				isTypedStrictlyPositive =
						aVariable.getTypeSpecifier().isTypedStrictlyPositiveNumber();
				isTypedPositive =
						aVariable.getTypeSpecifier().isTypedPositiveNumber();
			}
			else if( aVariable.hasDataType() )
			{
				varType = strTypeSmt2(aVariable.getDataType());
				isTypedStrictlyPositive =
						aVariable.getDataType().isTypedStrictlyPositiveNumber();
				isTypedPositive =
						aVariable.getDataType().isTypedPositiveNumber();
			}
			else
			{
				varType = "<unknown-type>";
			}

			os << "(declare-const " << uniqVariableID(aVariable)
					<< " " << varType << ")" << EOL;
			if( isTypedStrictlyPositive )
			{
				os << "(assert (< 0 " << uniqVariableID(aVariable) <<"))" << EOL;
			}
			else if( isTypedPositive )
			{
				os << "(assert (<= 0 " << uniqVariableID(aVariable) <<"))" << EOL;
			}
		}
		else
		{
			os << TAB << "(" << paramVector[ offset ].str() << ")" << EOL;
		}
	}

	os << "(assert " << ossCondition.str() << ")" << EOL2;

	if( enableChecksat )
	{
		os << "(check-sat)" << EOL;
	}
	if( enableModelProduction )
	{
		os << "(get-model)" << EOL;
	}

	return( true );
}

bool Z3Solver::to_smtlib(OutStream & os, const BF & aCondition)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aCondition )
			<< "conditional expression !!!"
			<< SEND_EXIT;

	createChecker();

	Z3_ast z3_expr = from_baseform(aCondition);

	os << Z3_ast_to_string(CONTEXT, z3_expr);

	destroyChecker();

	return( true );
}


bool Z3Solver::to_smt(OutStream & os,
		const BF & aCondition, BFVector & dataVector) const
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aCondition )
			<< "conditional expression !!!"
			<< SEND_EXIT;

	bool hasQuantifier = false;

	os << TAB;

	switch( aCondition.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aCondition.to< AvmCode >();

			os << '(';
			std::string eoe = "";

			switch( aCode.getAvmOpCode() )
			{
				case AVM_OPCODE_EQ:
				{
					os << "=";
					break;
				}
				case AVM_OPCODE_AND:
				{
					os << "and";
					break;
				}
				case AVM_OPCODE_OR:
				{
					os << "or";
					break;
				}
				case AVM_OPCODE_NOT:
				{
					os << "not";
					break;
				}

				case AVM_OPCODE_NEQ:
				{
					os << "not (=";
					eoe = ")";
					break;
				}

				case AVM_OPCODE_IFE:
				{
					os << "ite";
					break;
				}

				case AVM_OPCODE_IF:
				{
					os << "if";
					break;
				}

				case AVM_OPCODE_CONTAINS:
				{
					os << "contains";
					break;
				}

				case AVM_OPCODE_EXISTS:
				{
					os << "exists";
					hasQuantifier = true;
					break;
				}
				case AVM_OPCODE_FORALL:
				{
					os << "forall";
					hasQuantifier = true;
					break;
				}

				default:
				{
					os << aCode.getOperator()->strSMT();
					break;

				}
			}

			if( hasQuantifier )
			{
				BFList boundVars;

				OSS typeConstraint;

				os << " (" << EOL;
				auto endOperand = aCode.end();
				auto itOperand = aCode.begin();
				uint16_t termCount = 0;
				for( ; (itOperand + 1) != endOperand ; ++itOperand )
				{
					boundVars.append(*itOperand);

					if( (*itOperand).is< InstanceOfData >() )
					{
						const InstanceOfData & aParam =
								(*itOperand).to< InstanceOfData >();

						os << TAB2 << "(" << uniqParameterID(aParam)
							<< " " << strTypeSmt2(aParam) << ")" << EOL;

						if( aParam.getTypeSpecifier().isTypedStrictlyPositiveNumber() )
						{
							++termCount;
							typeConstraint << "(< 0 "
									<< uniqParameterID(aParam) <<") ";
						}
						else if( aParam.getTypeSpecifier().isTypedPositiveNumber() )
						{
							++termCount;
							typeConstraint << "(<= 0 "
									<< uniqParameterID(aParam) <<") ";
						}
					}
					else if( (*itOperand).is< Variable >() )
					{
						const Variable & aVariable = (*itOperand).to< Variable >();

						std::string varType;
						if( aVariable.hasTypeSpecifier())
						{
							varType = strTypeSmt2(aVariable.getTypeSpecifier());

							if( aVariable.getTypeSpecifier().isTypedPositiveNumber() )
							{
								++termCount;
								typeConstraint << "(<= 0 "
										<< uniqVariableID(aVariable) <<") ";
							}
						}
						else if( aVariable.hasDataType() )
						{
							varType = strTypeSmt2(aVariable.getDataType());

							if( aVariable.getDataType().isTypedStrictlyPositiveNumber() )
							{
								++termCount;
								typeConstraint << "(< 0 "
										<< uniqVariableID(aVariable) <<") ";
							}
						}
						else
						{
							varType = "<unknown-type>";
						}

						os << TAB2 << "(" << uniqVariableID(aVariable)
							<< " " << varType << ")" << EOL;

//						if( aVariable.getDataType().isTypedStrictlyPositiveNumber() )
//						{
//							++termCount;
//							typeConstraint << "(< 0 "
//									<< uniqVariableID(aVariable) <<") ";
//						}
//						else if( aVariable.getTypeSpecifier().isTypedPositiveNumber() )
//						{
//							++termCount;
//							typeConstraint << "(<= 0 "
//									<< uniqVariableID(aVariable) <<") ";
//						}
					}
					else
					{
						os << TAB2 << "(" << (*itOperand).str() << ")" << EOL;
					}
				}
				os << TAB2 << ")" << EOL;

				BFVector occursVars;

				if( termCount > 0 )
				{
					std::string strConstraint = typeConstraint.str();

					if( aCode.getAvmOpCode() == AVM_OPCODE_EXISTS )
					{
//						os << TAB2 << "(and" << EOL_TAB3 << strConstraint << EOL
						os << TAB2 << "(and " << strConstraint << EOL
							<< INCR2_INDENT;
						to_smt(os, *itOperand, occursVars);
						os << DECR2_INDENT << TAB2 << ")" << EOL_TAB;
					}
					else if( termCount > 2 )
					{
						os << TAB2 << "(=> (and" << strConstraint << ")" << EOL
							<< INCR2_INDENT;
						to_smt(os, *itOperand, occursVars);
						os << DECR2_INDENT << TAB2 << ")" << EOL_TAB;
					}
					else
					{
						os << TAB2 << "(=> " << strConstraint << EOL
							<< INCR2_INDENT;
						to_smt(os, *itOperand, occursVars);
						os << DECR2_INDENT << TAB2 << ")" << EOL_TAB;
					}
				}
				else
				{
					to_smt(os, *itOperand, occursVars);
				}

				occursVars.remove(boundVars);
				dataVector.add_unique(occursVars);
			}
			else if( ExpressionTypeChecker::isPropositional(aCode) )
			{
				os << EOL << INCR_INDENT;
				for( const auto & itOperand : aCode.getOperands() )
				{
					hasQuantifier = to_smt(os, itOperand, dataVector)
								|| hasQuantifier;
				}
				os << DECR_INDENT << TAB;
			}
			else
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					os << AVM_STR_INDENT;
					to_smt(os, itOperand, dataVector);
					os << END_INDENT;
				}
			}

			os << eoe << ')';

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			dataVector.add_unique( aCondition );
			os << uniqParameterID( aCondition.to< InstanceOfData >() );

			break;
		}

		case FORM_XFSP_VARIABLE_KIND:
		{
			dataVector.add_unique( aCondition );
			os << uniqVariableID( aCondition.to< Variable >() );

			break;
		}

		case FORM_ARRAY_BF_KIND:
		{
			os << '{';
			const ArrayBF & arrayArg =  aCondition.to< ArrayBF >();
			for( std::size_t idx = 0 ; idx < arrayArg.size() ; ++idx )
			{
				os << " ";
				hasQuantifier = to_smt(os, arrayArg.at(idx), dataVector)
							|| hasQuantifier;
			}

			os << TAB << " }";

			break;
		}

		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		{
			os << aCondition.str();

			break;
		}

		default:
		{
			if( aCondition.is< BuiltinContainer >() )
			{
				os << '{';
				const BuiltinContainer & aCollection =
						aCondition.to< BuiltinContainer >();
				for( std::size_t idx = 0 ; idx < aCollection.size() ; ++idx )
				{
					os << " ";
					hasQuantifier = to_smt(os, aCollection.at(idx), dataVector)
								|| hasQuantifier;
				}

				os << TAB << " }";
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Z3Solver::to_smt:> Unexpected OBJECT KIND << "
					<< aCondition.classKindName() << " >> as expression << "
						<< aCondition.str() << " >> !!!"
						<< SEND_EXIT;

				os << aCondition.str();
			}

			break;
		}
	}

	os << EOL;

	return hasQuantifier;
}



void Z3Solver::dbg_smt(const Z3_solver & z3Solver, bool produceModelOption) const
{
	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< ( produceModelOption ? "z3_c_get_model_" : "z3_c_check_sat_" )
			<< SOLVER_SESSION_ID << ".smt2" );

	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
		osFile << ";; z3 " << fileLocation << std::endl;
		osFile << ";; Getting info" << std::endl
				<< "(get-info :name)"    << std::endl
				<< "(get-info :version)" << std::endl;

		Z3_set_ast_print_mode(CONTEXT, Z3_PRINT_SMTLIB2_COMPLIANT);

		Z3_ast_vector assertions = Z3_solver_get_assertions(CONTEXT, SOLVER);

		unsigned num_assumptions = Z3_ast_vector_size(CONTEXT, assertions);

		// for auto destruction
		std::unique_ptr< Z3_ast[] > assumptions( new Z3_ast[num_assumptions] );

        for (unsigned i = 0; i < num_assumptions; i++)
        {
        	assumptions[i] = Z3_ast_vector_get(CONTEXT, assertions, i);
        }

		Z3_ast formula = 0;
		if (num_assumptions > 0) {
			--num_assumptions;
			formula = assumptions[num_assumptions];
		}
		else
		{
			formula = Z3_mk_true(CONTEXT);
		}

//		osFile << Z3_ast_vector_to_string(CONTEXT, assertions) << std::endl << std::endl
//				<< "formula: " << Z3_ast_to_string(CONTEXT, formula) << std::endl << std::endl;

		std::string strSMT = Z3_benchmark_to_smtlib_string(CONTEXT, "", "",
				"unknown", "", num_assumptions, assumptions.get(), formula);

		osFile << ";; Getting values or models" << std::endl
				<< "(set-option :produce-models true)" << std::endl
//				<< "; Getting assignments" << std::endl
//				<< "(set-option :produce-assignments true)" << std::endl
//				<< "; Logic" << std::endl
//				<< "(set-logic ALL)" << std::endl
				<< std::endl

				<< strSMT << std::endl

				<< "(get-model)" << std::endl
//				<< "(get-assignment)"
				<< std::endl;

		osFile.close();
	}
}



} /* namespace sep */


#endif /* _AVM_SOLVER_Z3_C_ */

