/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Yices2Solver.h"

/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_YICES_V2_ )


#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

#include <cstdint>
#include <fstream>

#include <gmp.h>
// contains #define __GMP_H__  using by YICES

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */

#include <yices.h>

#include <util/avm_vfs.h>

#include <fml/expression/AvmCode.h>
#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
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


namespace sep
{


#define SOLVER_CREATE_CHECKER  \
		do { \
			yices_init(); \
			CFG = yices_new_config(); \
			CTX = yices_new_context(CFG); \
			createChecker(); \
		} while( false )


#define SOLVER_DESTROY_CHECKER  \
		do { \
			destroyChecker(); \
			yices_free_context(CTX); CTX = nullptr; \
			yices_free_config(CFG);  CFG = nullptr; \
			yices_exit(); \
		} while( false )



/*
 *******************************************************************************
 * ID
 *******************************************************************************
 */
std::string Yices2Solver::ID = "YICES2";

std::string Yices2Solver::DESCRIPTION = "Yices 2 "
		"'Solver for Satisfiability Modulo Theories (SMT) problems, "
		"Copyright 2014 SRI International, "
		"GPL 3 License'";

std::uint64_t Yices2Solver::SOLVER_SESSION_ID = 1;


/**
 * CONSTRUCTOR
 * Default
 */
Yices2Solver::Yices2Solver()
: base_this_type(NULL_TYPE, NULL_TERM),
CFG( nullptr ),
CTX( nullptr )
{
	mLogFolderLocation = VFS::ProjectDebugPath + "/yices2/";
}


/**
 * DESTRUCTOR
 */
Yices2Solver::~Yices2Solver()
{
//	yices_free_config( CONFIG );
	CFG = nullptr;

//	yices_free_context( CTX );
	CTX = nullptr;

//	yices_exit();
}


static void yices_dump_context(context_t * ctx)
{

}

static int yicesl_set_output_file(const char * file_name)
{
	return 0;
}

static int yicesl_enable_log_file(const char * file_name)
{
	return 0;
}



/**
 * CONFIGURE
 */
bool Yices2Solver::configure(const WObject * wfFilterObject)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	std::string logFolderLocation = VFS::ProjectDebugPath + "/yices2/";

	if ( not VFS::checkWritingFolder(logFolderLocation, true) )
	{
		AVM_OS_LOG << " Yices1Solver::createChecker :> Error: The folder "
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

bool Yices2Solver::createChecker()
{
//	if( CTX != nullptr )
//	{
//		yices_reset_context(CTX);
//
//		return( true );
//	}
//	else
//	{
//		yices_init();
//		CONFIG = yices_new_config();
//
//		CTX = yices_new_context(CONFIG);
//		CTX = yices_new_context(nullptr);
//	}


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "yices_log_" << SOLVER_SESSION_ID << ".ys";
	yicesl_enable_log_file( fileLocation.c_str() );

	fileLocation = OSS() << mLogFolderLocation
			<< "yices_out_" << SOLVER_SESSION_ID << ".ys";
	yicesl_set_output_file( fileLocation.c_str() );

AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


	SMT_TYPE_BOOL      = yices_bool_type();

	SMT_TYPE_UINTEGER  = yices_int_type();
	SMT_TYPE_INTEGER   = yices_int_type();

	SMT_TYPE_URATIONAL = yices_real_type();
	SMT_TYPE_RATIONAL  = yices_real_type();

	SMT_TYPE_UREAL     = yices_real_type();
	SMT_TYPE_REAL      = yices_real_type();

//	SMT_TYPE_BV8    = yices_bvtype(8);
//	SMT_TYPE_BV16   = yices_bvtype(16);
//	SMT_TYPE_BV32   = yices_bvtype(32);
//	SMT_TYPE_BV64   = yices_bvtype(64);
//	SMT_TYPE_BV128  = yices_bvtype(128);
//	SMT_TYPE_BV256  = yices_bvtype(256);
//	SMT_TYPE_BV512  = yices_bvtype(512);
//	SMT_TYPE_BV1024 = yices_bvtype(1024);
//
//	if( yices_set_type_name(SMT_TYPE_BV8,    "bv8_t"    ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV16,   "bv16_t"   ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV32,   "bv32_t"   ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV64,   "bv64_t"   ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV128,  "bv128_t"  ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV256,  "bv256_t"  ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV512,  "bv512_t"  ) != 0 ) return false;
//	if( yices_set_type_name(SMT_TYPE_BV1024, "bv1024_t" ) != 0 ) return false;


	SMT_CST_BOOL_TRUE  = yices_true();
	SMT_CST_BOOL_FALSE = yices_false();

	SMT_CST_INT_ZERO = yices_zero();
	SMT_CST_INT_ONE  = yices_int32(1);

	resetTable();

	return( true );
}



bool Yices2Solver::destroyChecker()
{
	resetTable();

	SMT_TYPE_BOOL      = NULL_TYPE;

	SMT_TYPE_UINTEGER  = NULL_TYPE;
	SMT_TYPE_INTEGER   = NULL_TYPE;

	SMT_TYPE_BV32      = NULL_TYPE;
	SMT_TYPE_BV64      = NULL_TYPE;

	SMT_TYPE_URATIONAL = NULL_TYPE;
	SMT_TYPE_RATIONAL  = NULL_TYPE;

	SMT_TYPE_UREAL     = NULL_TYPE;
	SMT_TYPE_REAL      = NULL_TYPE;

	SMT_TYPE_NUMBER    = NULL_TYPE;

	SMT_TYPE_STRING    = NULL_TYPE;

	SMT_CST_BOOL_TRUE  = NULL_TERM;
	SMT_CST_BOOL_FALSE = NULL_TERM;

	SMT_CST_INT_ZERO   = NULL_TERM;
	SMT_CST_INT_ONE    = NULL_TERM;

//	yices_reset_context(CTX);
//	yices_free_context( CTX );
//	CTX = nullptr;

//	yices_free_config( CONFIG );
//	CONFIG = nullptr;

//	yices_exit();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	++SOLVER_SESSION_ID;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( true );
}


bool Yices2Solver::resetTable()
{
	base_this_type::resetTable();

	mTableOfParameterDecl.push_back( NULL_TERM );

	mTableOfParameterExpr.push_back( NULL_TERM );

	mBitsetOfConstrainedParameter.push_back( false );
	mBitsetOfPositiveParameter.push_back( false );
	mBitsetOfStrictlyPositiveParameter.push_back( false );

	return( true );
}



/**
 * PROVER
 */
bool Yices2Solver::isSubSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	return( true );
}

bool Yices2Solver::isEqualSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	return( true );
}

SolverDef::SATISFIABILITY_RING Yices2Solver::isSatisfiable(const BF & aCondition)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	SOLVER_CREATE_CHECKER;

	BFVector paramVector;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Yices2Solver::isSatisfiable(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_sat(aCondition, paramVector);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	term_t yicesCondition = from_baseform(aCondition);


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Yices2Condition :" << SOLVER_SESSION_ID << ">" << std::endl;
	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "\t";
		yices_dump_context(CTX);
		AVM_OS_TRACE << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
//	AVM_OS_TRACE << "\t" << yices2_term_to_string(CTX, z3Condition) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )


	if( yicesCondition != NULL_TERM )
	{
		yices_assert_formula(CTX, yicesCondition);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )	// trace to file
	dbg_smt(yicesCondition, nullptr, paramVector, false);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

		switch( yices_check_context(CTX, nullptr) )
		{
			case STATUS_SAT:
			{
				satisfiability = SolverDef::SATISFIABLE;
				break;
			}

			case STATUS_UNSAT:
			{
				satisfiability = SolverDef::UNSATISFIABLE;
				break;
			}

			case STATUS_UNKNOWN:
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


	SOLVER_DESTROY_CHECKER;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "result :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( satisfiability );
}


/**
 * SOLVER
 */
bool Yices2Solver::solveImpl(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	SOLVER_CREATE_CHECKER;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Yices2Solver::solve(...) "
			":" << SOLVER_SESSION_ID << ">";
	AVM_OS_TRACE << "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_model(aCondition, dataVector, valuesVector);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	term_t yicesCondition =  from_baseform(aCondition);


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Yices2Condition :" << SOLVER_SESSION_ID << ">" << std::endl;
	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "\t";
		yices_dump_context(CTX);
		AVM_OS_TRACE << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH

//	AVM_OS_TRACE << "\t" << yices2_term_to_string(CTX, yicesCondition) << std::endl;

AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )


	if( yicesCondition != NULL_TERM )
	{
		yices_assert_formula(CTX, yicesCondition);

		switch( yices_check_context(CTX, nullptr) )
		{
			case STATUS_SAT:
			{
				satisfiability = SolverDef::SATISFIABLE;

				model_t * model = yices_get_model(CTX, 1);

				AVM_OS_ASSERT_FATAL_ERROR_EXIT( model != nullptr )
						<< "Yices2Solver::solve:> Failed to obten a model with "
						"<< yices_get_model >> !!!"
						<< SEND_EXIT;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "YICES2Model sat:" << SOLVER_SESSION_ID << ">" << std::endl;

//	FILE * model_stream = freopen(
//			( OSS() << mLogFolderLocation << "yices_check_model_"
//					<< SOLVER_SESSION_ID << ".log" ).c_str(), "w", stdout);
//
//	FILE * model_stream = fopen(
//			( OSS() << mLogFolderLocation << "yices_check_model_"
//					<< SOLVER_SESSION_ID << ".log" ).c_str(), "w");
//
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( model_stream != nullptr )
//			<< "Yices2Solver::solve:> Failed to open a FILE for "
//			"<< yices_print_model >> !!!"
//			<< SEND_EXIT;
//
//	AVM_OS_TRACE << "voir :>" << mLogFolderLocation
//			<< "yices_check_model_" << SOLVER_SESSION_ID  ".log"
//			<< std::endl;
//
//	STREAMBUF_SAVE_REDIRECT( AVM_OS_COUT , AVM_OS_TRACE );
//	yices_print_model(model_stream, model);
//	STREAMBUF_RESTORE( AVM_OS_COUT );
//
//	fclose( model_stream );

				AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )	// trace to file
	dbg_smt(yicesCondition, model, dataVector, true);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


				std::size_t paramCount = mTableOfParameterDecl.size();
				for( std::size_t offset = 1 ; offset < paramCount ; offset++ )
				{
					dataVector.append( mTableOfParameterInstance[ offset ] );

					BF bfVal = to_baseform(model, mTableOfParameterDecl[ offset ],
							mTableOfParameterInstance.rawAt( offset )->
							getTypeSpecifier());

					valuesVector.append( bfVal.valid() ? bfVal : dataVector.back() );
				}

				yices_free_model( model );

				break;
			}

			case STATUS_UNSAT:
			{
				satisfiability = SolverDef::UNSATISFIABLE;
				break;
			}

			case STATUS_UNKNOWN:
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

	SOLVER_DESTROY_CHECKER;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "solve :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( satisfiability == SolverDef::SATISFIABLE );
}



/**
 * TOOLS
 */

type_t Yices2Solver::getYicesType(const BaseTypeSpecifier & bts)
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

	return( NULL_TYPE );
}


term_t Yices2Solver::getParameterExpr(const BF & bfParameter)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bfParameter.to< InstanceOfData >() );

	if( aParameter.getMark() == 0 )
	{
		aParameter.setMark( mTableOfParameterInstance.size() );
		mTableOfParameterInstance.append( bfParameter );

		const BaseTypeSpecifier & paramTypeSpecifier =
				aParameter.referedTypeSpecifier();

		term_t yicesParam = yices_new_variable(getYicesType(paramTypeSpecifier));

		if( yices_set_term_name( yicesParam,
				uniqParameterID( aParameter ).c_str() ) != 0 )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Yices2Solver::getParameterExpr:> yices_set_term_name( "
					<< yicesParam << " , "<< aParameter.getFullyQualifiedNameID()
					<< " ) != 0 !!!"
					<< SEND_EXIT;
		}

		mTableOfParameterDecl.push_back( yicesParam );

		mTableOfParameterExpr.push_back( yicesParam );

		mBitsetOfConstrainedParameter.push_back(
				paramTypeSpecifier.couldGenerateConstraint() );

		mBitsetOfPositiveParameter.push_back(
				paramTypeSpecifier.isTypedPositiveNumber() );

		mBitsetOfStrictlyPositiveParameter.push_back(
				paramTypeSpecifier.isTypedStrictlyPositiveNumber() );
	}

	return( mTableOfParameterExpr.at( aParameter.getMark() ) );
}




term_t Yices2Solver::getVariableExpr(InstanceOfData * aVar, std::size_t varID)
{
	if( mTableOfVariableExpr.size() <= varID )
	{
		term_t yicesVar = yices_new_variable(
				getYicesType(aVar->getTypeSpecifier()));
		if( yices_set_term_name( yicesVar,
				uniqVariableID( *aVar, varID ).c_str() ) != 0 )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Yices2Solver::getVariableExpr:> yices_set_term_name( "
					<< yicesVar << " , "<< aVar->getFullyQualifiedNameID()
					<< " ) != 0 !!!"
					<< SEND_EXIT;
		}

		mTableOfVariableDecl.push_back( yicesVar );

		mTableOfVariableExpr.push_back( yicesVar );
	}

	return( mTableOfVariableExpr.at( varID ) );
}



term_t Yices2Solver::getBoundParameterExpr(const BF & bfParameter)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bfParameter.to< InstanceOfData >() );

	aParameter.setMark( mTableOfParameterInstance.size() );
	mTableOfParameterInstance.append( bfParameter );

	const BaseTypeSpecifier & paramTypeSpecifier =
			aParameter.referedTypeSpecifier();

	term_t yicesParam = yices_new_variable(getYicesType(paramTypeSpecifier));

	if( yices_set_term_name( yicesParam,
			uniqParameterID( aParameter ).c_str() ) != 0 )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Yices2Solver::getBoundParameterExpr:> yices_set_term_name( "
				<< yicesParam << " , "<< aParameter.getFullyQualifiedNameID()
				<< " ) != 0 !!!"
				<< SEND_EXIT;
	}

	mTableOfParameterDecl.push_back( yicesParam );

	mTableOfParameterExpr.push_back( yicesParam );

	mBitsetOfConstrainedParameter.push_back(
			paramTypeSpecifier.couldGenerateConstraint() );

	mBitsetOfPositiveParameter.push_back(
			paramTypeSpecifier.isTypedPositiveNumber() );

	mBitsetOfStrictlyPositiveParameter.push_back(
			paramTypeSpecifier.isTypedStrictlyPositiveNumber() );

	return( mTableOfParameterExpr.at( aParameter.getMark() ) );
}


term_t Yices2Solver::safe_from_baseform(const BF & exprForm)
{
	term_t e = NULL_TERM;

	try
	{
		if( (e = from_baseform(exprForm)) == NULL_TERM )
		{
			AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
					<< "\tYices2Solver::safe_from_baseform< unknown::error :"
					<< SOLVER_SESSION_ID << ">" << std::endl
					<< REPEAT("--------", 10) << std::endl
					<< "\tFailed to CONVERT sep::fml::expression to YICES2::Expr:>" << std::endl
					<< "\t  " << exprForm.str() << std::endl
					<< REPEAT("********", 10) << std::endl;

			destroyChecker();
		}
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tYices2Solver::safe_from_baseform< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\tFailed to CONVERT sep::fml::expression to YICES1::Expr:>" << std::endl
				<< "\t  " << exprForm.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();
	}

	return( e );
}



term_t Yices2Solver::from_baseform(const BF & exprForm)
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
					return( yices_eq(
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_NEQ:
				{
					return( yices_neq(
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_LT:
				{
					return( yices_arith_lt_atom(
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_LTE:
				{
					return( yices_arith_leq_atom(
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_GT:
				{
					return( yices_arith_gt_atom(
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}

				case AVM_OPCODE_GTE:
				{
					return( yices_arith_geq_atom(
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) ) );
				}


				case AVM_OPCODE_CONTAINS:
				{
					const BuiltinCollection & aCollection =
							aCode.first().to< BuiltinCollection >();

					if( aCollection.singleton() )
					{
						return( yices_eq(
							from_baseform(aCollection.at(0)),
							from_baseform(aCode.second()) ) );
					}
					else if( aCollection.populated() )
					{
						ARGS arg( aCollection.size() );
						for( std::size_t offset = 0 ; arg.hasNext() ; ++offset )
						{
							arg.next( yices_eq(
								from_baseform(aCollection.at(offset)),
								from_baseform(aCode.second()) ));
						}

						return( yices_or(arg->count, arg->table) );
					}
					else
					{
						return( SMT_CST_BOOL_FALSE );
					}
				}


				// LOGICAL OPERATION
				case AVM_OPCODE_NOT:
				{
					return( yices_not( from_baseform(aCode.first())) );
				}

				case AVM_OPCODE_AND:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_and(arg->count, arg->table) );
				}

				case AVM_OPCODE_NAND:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_not( yices_and(arg->count, arg->table) ) );
				}

//				case AVM_OPCODE_XAND:
//				{
//					ARGS arg( 2 );
//
//					arg.next( yices_not( from_baseform(aCode.first())) );
//
//					arg.next( from_baseform(aCode.second(),
//							TypeManager::BOOLEAN) );
//
//					return( yices_and(arg->table, 2) );
//
//					return( mVC->orExpr(
//							mVC->andExpr(
//									from_baseform(aCode.first(),
//											TypeManager::BOOLEAN),
//									from_baseform(aCode.second(),
//											TypeManager::BOOLEAN)),
//							mVC->andExpr(
//									mVC->notExpr(from_baseform(aCode.first(),
//											TypeManager::BOOLEAN)),
//									mVC->notExpr(from_baseform(aCode.second(),
//											TypeManager::BOOLEAN))) ) );
//				}


				case AVM_OPCODE_OR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_or(arg->count, arg->table) );
				}

				case AVM_OPCODE_NOR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_not( yices_or(arg->count, arg->table) ) );
				}

				case AVM_OPCODE_XOR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_xor(arg->count, arg->table) );
				}

				case AVM_OPCODE_XNOR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_not( yices_xor(arg->count, arg->table) ) );
				}

				case AVM_OPCODE_IMPLIES:
				{
					return( yices_implies(
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}


				case AVM_OPCODE_EXISTS:
				{
					ARGS arg( aCode.size()  - 1 );

					for (std::size_t offset = 0; offset < arg->count; ++offset)
					{
						arg.next( getBoundParameterExpr(aCode[ offset ]) );
					}

					term_t formula = from_baseform(aCode.last());

					return( yices_exists(arg->count, arg->table, formula) );
				}

				case AVM_OPCODE_FORALL:
				{
					ARGS arg( aCode.size()  - 1 );

					for (std::size_t offset = 0; offset < arg->count; ++offset)
					{
						arg.next( getBoundParameterExpr(aCode[ offset ]) );
					}

					term_t formula = from_baseform(aCode.last());

					return( yices_forall(arg->count, arg->table, formula) );
				}
				// BITWISE OPERATION
				case AVM_OPCODE_BAND:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_bvand(arg->count, arg->table) );
				}

				case AVM_OPCODE_BOR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( yices_bvor(arg->count, arg->table) );
				}

				case AVM_OPCODE_LSHIFT:
				{
					if( aCode.second().isInteger() )
					{
						return( yices_bvshl(
								from_baseform(aCode.first()),
								from_baseform(aCode.second())) );

					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Yices2Solver::from_baseform:> "
									"Unexpected second argument for "
									"newFixedLeftShiftExpr !!!\n"
								<< aCode.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return( NULL_TERM );
					}
				}

				case AVM_OPCODE_RSHIFT:
				{
					if( aCode.second().isInteger() )
					{
						return( yices_bvashr(
								from_baseform(aCode.first()),
								from_baseform(aCode.second())) );

					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Yices2Solver::from_baseform:> "
									"Unexpected second argument for "
									"newFixedRightShiftExpr !!!\n"
								<< aCode.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return( NULL_TERM );
					}
				}


				// ARITHMETIC OPERATION
				case AVM_OPCODE_PLUS:
				{
					AvmCode::const_iterator itOperand = aCode.begin();
					term_t term_yices = from_baseform(*itOperand);

					AvmCode::const_iterator endOperand = aCode.end();
					for( ++itOperand ; itOperand != endOperand ; ++itOperand )
					{
						term_yices = yices_add(term_yices,
								from_baseform(*itOperand));
					}

					return( term_yices );
				}

				case AVM_OPCODE_UMINUS:
				{
					return( yices_neg(from_baseform(aCode.first())) );
				}

				case AVM_OPCODE_MINUS:
				{
					AvmCode::const_iterator itOperand = aCode.begin();
					term_t term_yices = from_baseform(*itOperand);

					AvmCode::const_iterator endOperand = aCode.end();
					for( ++itOperand ; itOperand != endOperand ; ++itOperand )
					{
						term_yices = yices_sub(term_yices,
								from_baseform(*itOperand));
					}

					return( term_yices );
				}

				case AVM_OPCODE_MULT:
				{
					AvmCode::const_iterator itOperand = aCode.begin();
					term_t term_yices = from_baseform(*itOperand);

					AvmCode::const_iterator endOperand = aCode.end();
					for( ++itOperand ; itOperand != endOperand ; ++itOperand )
					{
						term_yices = yices_mul(term_yices,
								from_baseform(*itOperand));
					}

					return( term_yices );
				}

				case AVM_OPCODE_DIV:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported expression Operator "
								"<< AVM_OPCODE_DIV >> !!!"
							<< SEND_EXIT;

					return( NULL_TERM );
				}

				case AVM_OPCODE_POW:
				{
					if( ExpressionFactory::isUInteger(aCode.second()) )
					{
						avm_uinteger_t power =
								ExpressionFactory::toUInteger(aCode.second());

						term_t term_yices = from_baseform(aCode.first());

						for( ; power > 0 ; --power )
						{
							term_yices = yices_mul(term_yices, term_yices);
						}

						return( term_yices );

//						return( yices_power(from_baseform(aCode.first()),
//								ExpressionFactory::toUInteger(aCode.second())) );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Yices2Solver::from_baseform:> "
									"Unsupported expression Operator "
									"<< AVM_OPCODE_POW >> !!!"
								<< SEND_EXIT;

						return( NULL_TERM );
					}
				}

//				case AVM_OPCODE_MOD:

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Yices2Solver::from_baseform:> "
								"Unsupported expression !!!\n"
							<< aCode.toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return( NULL_TERM );
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
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

			return( yices_mpz( exprForm.to<
					Integer >().getValue().get_mpz_t() ) );

#else

			return( yices_int64(exprForm.to< Integer >().toInt64()) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */

//			return( yices_mk_num_from_string(CTX,
//					exprForm.to< Integer >().str().c_str()) );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

			return( yices_mpq( exprForm.to<
					Rational >().getValue().get_mpq_t() ) );

#else

			return( yices_rational64(
					exprForm.to< Rational >().toNumerator(),
					exprForm.to< Rational >().toDenominator()) );

//			return( yices_parse_rational(
//					exprForm.to< Rational >().str() ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

			mpq_class mpq( exprForm.to< Float >().getValue() );

			return( yices_mpq( mpq.get_mpq_t() ) );

#else

			return( yices_parse_float(
					exprForm.to< Float >().str().c_str()) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
		}


		case FORM_RUNTIME_ID_KIND:
		{
			return( yices_int64(exprForm.bfRID().getRid()) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Yices2Solver::from_baseform:> "
						"Unexpected BASEFORM KIND << " << exprForm.classKindName()
					<< " >> as expression << " << exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			return( NULL_TERM );
		}
	}

	return( NULL_TERM );
}


BF Yices2Solver::to_baseform(model_t * model, term_t param,
		const BaseTypeSpecifier & bts)
{
	if( bts.isTypedBoolean() )
	{
		int32_t val;
		if( yices_get_bool_value(model, param, &val) == NO_ERROR )
		{
			return( ExpressionConstructor::newBoolean( val != 0 ) );
		}
		else
		{
			return( BF::REF_NULL );
		}
	}

	else if( bts.weaklyTypedInteger() )
	{
		{
			int32_t val;
			if( yices_get_int32_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newInteger(
						static_cast< avm_integer_t >( val ) ) );
			}
		}
		{
			int64_t val;
			if( yices_get_int64_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newInteger(
						static_cast< avm_integer_t >( val ) ) );
			}
		}
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )
		{
			mpz_t val;
			if( yices_get_mpz_value(model, param, val) == NO_ERROR )
			{
				BF bfValue = ExpressionConstructor::newInteger(val);

				mpz_clear(val);

				return( bfValue );
			}
			else
			{
//				mpz_clear(val);
			}
		}
#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
	}
	else if( bts.weaklyTypedRational() )
	{
		{
			int32_t  num;
			uint32_t den;
			if( yices_get_rational32_value(model, param, &num, &den) == NO_ERROR )
			{
				return( ExpressionConstructor::newRational(
						static_cast< avm_integer_t  >( num ),
						static_cast< avm_uinteger_t >( den ) ) );
			}
		}
		{
			int64_t  num;
			uint64_t den;
			if( yices_get_rational64_value(model, param, &num, &den) == NO_ERROR )
			{
				return( ExpressionConstructor::newRational(
						static_cast< avm_integer_t >( num ),
						static_cast< avm_uinteger_t >( den )) );
			}
		}

		{
			int32_t val;
			if( yices_get_int32_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newRational(
						static_cast< avm_integer_t >( val ) ) );
			}
		}
		{
			int64_t val;
			if( yices_get_int64_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newRational(
						static_cast< avm_integer_t >( val ) ) );
			}
		}
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )
		{
			mpq_t val;
			if( yices_get_mpq_value(model, param, val) == NO_ERROR )
			{
				BF bfValue = ExpressionConstructor::newRational(val);

				mpq_clear(val);

				return( bfValue );
			}
			else
			{
				mpq_clear(val);
			}
		}
#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
	}

	else if( bts.weaklyTypedReal() )
	{
		{
			double val;
			if( yices_get_double_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newFloat(
						static_cast< avm_float_t >( val ) ) );
			}
		}

		{
			int32_t val;
			if( yices_get_int32_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newFloat(
						static_cast< avm_integer_t >( val ) ) );
			}
		}
		{
			int64_t val;
			if( yices_get_int64_value(model, param, &val) == NO_ERROR )
			{
				return( ExpressionConstructor::newFloat(
						static_cast< avm_integer_t >( val ) ) );
			}
		}

		{
			int32_t  num;
			uint32_t den;
			if( yices_get_rational32_value(model, param, &num, &den) == NO_ERROR )
			{
				return( ExpressionConstructor::newRational(
						static_cast< avm_integer_t  >( num ),
						static_cast< avm_uinteger_t >( den ) ) );
			}
		}
		{
			int64_t  num;
			uint64_t den;
			if( yices_get_rational64_value(model, param, &num, &den) == NO_ERROR )
			{
				return( ExpressionConstructor::newRational(
						static_cast< avm_integer_t >( num ),
						static_cast< avm_integer_t >( den ) ) );
			}
		}
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )
		{
			mpq_t val;
			if( yices_get_mpq_value(model, param, val) == NO_ERROR )
			{
				BF bfValue = ExpressionConstructor::newRational(val);

				mpq_clear(val);

				return( bfValue );
			}
			else
			{
				mpq_clear(val);
			}
		}
#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
	}

	return( BF::REF_NULL );
}


/**
 * Using file API
 */
#define YICES_VAR_TYPE_SEPARATOR  "::"

SolverDef::SATISFIABILITY_RING Yices2Solver::smt_check_sat(
		const BF & aCondition, BFVector & paramVector)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	StringOutStream ossCondition("", "\t", "");
	bool hasQuantifier = to_smt(ossCondition, aCondition, paramVector);

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "yices_check_sat_" << SOLVER_SESSION_ID << ".ys";
	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
//		osFile << "(set-verbosity! 0)" << std::endl;
//		osFile << "(set-option :verbosity 0)" << std::endl;
//		osFile << "(set-arith-only! true)" << std::endl;
//		osFile << "(set-nested-rec-limit! 50)" << std::endl;

		if( hasQuantifier )
		{
			osFile << ";; yices --mode=ef --verbosity=5 "
					<< fileLocation << std::endl;
		}
		else
		{
//			osFile << ";; yices --logic=QF_LRA --verbosity=5 "
			osFile << ";; yices --arith-solver=auto --verbosity=5 "
					<< fileLocation << std::endl;
		}

		std::size_t paramCount = paramVector.size();
		for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
		{
			const InstanceOfData & aParam =
					paramVector[ offset ].to< InstanceOfData >();

			osFile << "(define " << uniqParameterID(aParam)
					<< YICES_VAR_TYPE_SEPARATOR << strTypeSmt2(aParam)
					<< ")" << std::endl;

			if( aParam.getTypeSpecifier().isTypedStrictlyPositiveNumber() )
			{
				osFile << "(assert (< 0 " << uniqParameterID(aParam)
						<<"))" << std::endl;
			}
			else if( aParam.getTypeSpecifier().isTypedPositiveNumber() )
			{
				osFile << "(assert (<= 0 " << uniqParameterID(aParam)
						<<"))" << std::endl;
			}
		}

		osFile << "(assert " << ossCondition.str() << ")" << std::endl;

		if( hasQuantifier )
		{
			osFile << "(ef-solve)" << std::endl
					<< "(show-model)" << std::endl;
		}
		else
		{
			osFile << "(check)" << std::endl;
		}

		osFile.close();
	}
	else
	{
		return( SolverDef::ABORT_SAT );
	}

	return( satisfiability );
}

bool Yices2Solver::smt_check_model(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	BFVector paramVector;

	StringOutStream ossCondition("", "\t", "");
	bool hasQuantifier = to_smt(ossCondition, aCondition, paramVector);

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "yices_check_sat_" << SOLVER_SESSION_ID << ".ys";
	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
//		osFile << "(set-verbosity! 0)" << std::endl;
//		osFile << "(set-arith-only! true)" << std::endl;
//		osFile << "(set-nested-rec-limit! 50)" << std::endl;

//		osFile << "(set-evidence! true)" << std::endl;

		if( hasQuantifier )
		{
			osFile << ";; yices --mode=ef --verbosity=5 "
					<< fileLocation << std::endl;
		}
		else
		{
//			osFile << ";; yices --logic=QF_LRA --verbosity=5 "
			osFile << ";; yices --arith-solver=auto --verbosity=5 "
						<< fileLocation << std::endl;
		}

		std::size_t paramCount = paramVector.size();
		for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
		{
			const InstanceOfData & aParam =
					paramVector[ offset ].to< InstanceOfData >();

			osFile << "(define " << uniqParameterID(aParam)
					<< YICES_VAR_TYPE_SEPARATOR << strTypeSmt2(aParam)
					<< ")" << std::endl;
		}

		osFile 	<< "(assert " << ossCondition.str() << ")" << std::endl;

		if( hasQuantifier )
		{
			osFile << "(ef-solve)" << std::endl
					<< "(show-model)" << std::endl;
		}
		else
		{
			osFile << "(check)" << std::endl;
		}

		osFile.close();
	}
	else
	{
		return( false );
	}

	return( true );
}


SolverDef::SATISFIABILITY_RING Yices2Solver::from_smt_sat(const BF & aCondition)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;


	return( satisfiability );
}

bool Yices2Solver::from_smt_model(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	return( true );
}


std::string Yices2Solver::strTypeSmt2(const ITypeSpecifier & aTypedElement) const
{
	if( aTypedElement.isTypedBoolean() )
	{
		return yices_type_to_string(SMT_TYPE_BOOL, 128, UINT32_MAX, 0);  //"bool";
	}
	else if( aTypedElement.isTypedEnum() )
	{
		return yices_type_to_string(SMT_TYPE_INTEGER, 128, UINT32_MAX, 0); //"int";
	}
	else if( aTypedElement.isTypedUInteger() )
	{
		return yices_type_to_string(SMT_TYPE_UINTEGER, 128, UINT32_MAX, 0); //"int";
	}
	else if( aTypedElement.weaklyTypedInteger() )
	{
		return yices_type_to_string(SMT_TYPE_INTEGER, 128, UINT32_MAX, 0); //"int";
	}
	else if( aTypedElement.isTypedRational() )
	{
		return yices_type_to_string(SMT_TYPE_RATIONAL, 128, UINT32_MAX, 0); //"int";
	}
	else if( aTypedElement.isTypedURational() )
	{
		return yices_type_to_string(SMT_TYPE_URATIONAL, 128, UINT32_MAX, 0); //"int";
	}
	else if( aTypedElement.weaklyTypedRational() )
	{
		return yices_type_to_string(SMT_TYPE_RATIONAL, 128, UINT32_MAX, 0); //"int";
	}
	else if( aTypedElement.weaklyTypedReal() )
	{
		return yices_type_to_string(SMT_TYPE_REAL, 128, UINT32_MAX, 0); //"int";
	}
	else
	{
		return "Unknown";
	}
}

bool Yices2Solver::to_smt(OutStream & os,
		const BF & aCondition, bool enableModelProduction) const
{
	BFVector paramVector;

	StringOutStream ossCondition("", "\t", "");
	bool hasQuantifier = to_smt(ossCondition, aCondition, paramVector);

//	os << "(set-verbosity! 0)" << std::endl;
//	os << "(set-option :verbosity 0)" << std::endl;
//	os << "(set-arith-only! true)" << std::endl;
//	os << "(set-nested-rec-limit! 50)" << std::endl;

	std::size_t paramCount = paramVector.size();
	for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
	{
		const InstanceOfData & aParam =
				paramVector[ offset ].to< InstanceOfData >();

		os << "(define " << uniqParameterID(aParam)
				<< YICES_VAR_TYPE_SEPARATOR << strTypeSmt2(aParam)
				<< ")" << std::endl;

		if( aParam.getTypeSpecifier().isTypedStrictlyPositiveNumber() )
		{
			os << "(assert (< 0 " << uniqParameterID(aParam)
					<<"))" << std::endl;
		}
		else if( aParam.getTypeSpecifier().isTypedPositiveNumber() )
		{
			os << "(assert (<= 0 " << uniqParameterID(aParam)
					<<"))" << std::endl;
		}
	}

	os << "(assert " << ossCondition.str() << ")" << std::endl;

	if( hasQuantifier )
	{
		os << "(ef-solve)" << std::endl
				<< "(show-model)" << std::endl;
	}
	else
	{
		os << "(check)" << std::endl;
	}

	return( hasQuantifier );
}

bool Yices2Solver::to_smt(OutStream & os,
		const BF & aCondition, BFVector & dataVector) const
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aCondition )
			<< " conditional expression !!!"
			<< SEND_EXIT;

	bool hasQuantifier = false;

	os << TAB;

	switch( aCondition.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = aCondition.to< AvmCode >();

			os << '(';

			switch( aCode.getAvmOpCode() )
			{
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

				case AVM_OPCODE_EQ:
				{
					os << "=";
					break;
				}
				case AVM_OPCODE_NEQ:
				{
					os << "/=";
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

				case AVM_OPCODE_POW:
				{
					if( ExpressionFactory::isUInteger(aCode.second()) )
					{
						avm_uinteger_t power =
								ExpressionFactory::toUInteger(aCode.second());

						AvmCode::const_iterator itOperand = aCode.begin();
						AvmCode::const_iterator endOperand = aCode.end();

						os << "* ";
						hasQuantifier = to_smt(os, *itOperand, dataVector)
									|| hasQuantifier;

						for( ; power > 0 ; --power )
						{
							os << " ";
							hasQuantifier = to_smt(os, *itOperand, dataVector)
										|| hasQuantifier;
						}

						itOperand = endOperand;
					}
					else
					{
						os << aCode.getOperator()->strSMT();
					}

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

				os << " (" << std::endl;
				auto endOperand = aCode.end();
				auto itOperand = aCode.begin();
				for( ; (itOperand + 1) != endOperand ; ++itOperand )
				{
					boundVars.append(*itOperand);

					const InstanceOfData & aParam =
							(*itOperand).to< InstanceOfData >();

					os << "\t" << uniqParameterID(aParam)
						<< YICES_VAR_TYPE_SEPARATOR << strTypeSmt2(aParam)
						<< std::endl;
				}
				os << " ) ";

				to_smt(os, *itOperand, dataVector);

				dataVector.remove(boundVars);
			}
			else
			{
				for( const auto & itOperand : aCode.getOperands() )
				{
					os << " ";
					hasQuantifier = to_smt(os, itOperand, dataVector)
								|| hasQuantifier;
				}
			}

			os << ')';

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			dataVector.add_unique( aCondition );
			os << uniqParameterID( aCondition.to< InstanceOfData >() );

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
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected BASEFORM KIND as expression << "
					<< aCondition.str() << " >> !!!"
					<< SEND_EXIT;

			os << aCondition.str();

			break;
		}
	}

	os << EOL;

	return hasQuantifier;
}


void Yices2Solver::dbg_smt(term_t aTerm, model_t * aModel,
		BFVector & paramVector, bool produceModelOption) const
{
//	AVM_OS_TRACE << "z3::solver::to_smt2(...) --> "
//			<< ( produceModelOption ? "Get Model" : "isSatifiable" ) << std::endl;
//			<< Yices2Solver.to_smt2() << std::endl;


	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< ( produceModelOption ? "yices_get_model_" : "yices_check_sat_" )
			<< SOLVER_SESSION_ID << ".smt2" );

//	FILE * osFile = std::fopen(fileLocation.c_str(), "w");
//	if( osFile != nullptr )
//	{
//		std::fprintf(osFile,
//				"; Getting info\n(get-info :name)\n(get-info :version)\n");
//
//		if( produceModelOption )
//		{
//			std::fprintf(osFile, "; Getting values or models\n(set-option :produce-models true)\n");
////			std::fprintf(osFile, "; Getting assignments\n(set-option :produce-assignments true)\n");
////			std::fprintf(osFile, "; Logic\n(set-logic ALL)\n");
//
//			yices_print_model(osFile, aModel);
//
//			std::fprintf(osFile, "\n(get-model)\n\n");
//		}
//		else
//		{
////			std::fprintf(osFile, "; Logic\n(set-logic ALL)\n");
//
//		}
//
//		std::fclose( osFile );
//	}

	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
		osFile << ";; yices-smt2 " << fileLocation << std::endl;
		osFile << ";; Getting info" << std::endl
				<< "(get-info :name)"    << std::endl
				<< "(get-info :version)" << std::endl;

		for( const auto & itParam : paramVector)
		{
			const InstanceOfData & aParam = itParam.to< InstanceOfData >();
			osFile << "(declare-fun " << uniqParameterID(aParam)
					<< " () " << SatSolver::strTypeSmt2(aParam)
					<< ")" << std::endl;
		}

		if( produceModelOption )
		{
			osFile << ";; Getting values or models" << std::endl
					<< "(set-option :produce-models true)" << std::endl
//					<< "; Getting assignments" << std::endl
//					<< "(set-option :produce-assignments true)" << std::endl
//					<< ";; Logic" << std::endl
//					<< "(set-logic ALL)" << std::endl
					<< std::endl;

			osFile << "(assert "
					<< yices_term_to_string(aTerm, 128, UINT32_MAX, 0)
					<< ")" << std::endl;

			osFile << yices_model_to_string(aModel, 128, UINT32_MAX, 0) << std::endl;

			osFile << "(get-model)" << std::endl
//					<< "(get-assignment)"
					<< std::endl;
		}
		else
		{
//			osFile << "; Logic" << std::endl
//					<< "(set-logic ALL)" << std::endl;

			osFile << "(assert "
					<< yices_term_to_string(aTerm, 128, UINT32_MAX, 0)
					<< ")" << std::endl;

			osFile << "(check-sat)" << std::endl;
		}

		osFile.close();
	}

}


} /* namespace sep */


#endif /* _AVM_SOLVER_YICES_V2_ */
