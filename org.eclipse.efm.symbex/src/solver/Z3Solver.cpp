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

#include "Z3Solver.h"

/*
 * Here because "SolverDef.h" could define this macro
 */
#if( defined( _AVM_SOLVER_Z3_ ) and (not defined( _AVM_SOLVER_Z3_C_ )) )

#include <fstream>

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

std::string Z3Solver::DESCRIPTION = "Z3 "
		"'High-performance Theorem Prover at Microsoft Research, MIT License'";

std::uint64_t Z3Solver::SOLVER_SESSION_ID = 1;


/**
 * CONSTRUCTOR
 * Default
 */
Z3Solver::Z3Solver()
: base_this_type( ),
CONFIG ( nullptr ),
CONTEXT( nullptr )
{
	mLogFolderLocation = VFS::ProjectDebugPath + "/z3_cpp/";
}


/**
 * CONFIGURE
 */
bool Z3Solver::configure(const WObject * wfFilterObject)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

		std::string logFolderLocation = VFS::ProjectDebugPath + "/z3_cpp/";

	if ( not VFS::checkWritingFolder(logFolderLocation, true) )
	{
		AVM_OS_LOG << " Z3Solver::createChecker :> Error: The folder "
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
bool Z3Solver::createChecker(z3::config & config, z3::context & context)
{
	CONFIG = & config;

	CONFIG->set("MODEL", "true");

	CONTEXT = & context;

//	SMT_CST_BOOL_TRUE  = CONTEXT->bool_val(true);
//	SMT_CST_BOOL_FALSE = CONTEXT->bool_val(false);

	resetTable();

	return( true );
}

#define	SMT_CST_BOOL_TRUE   CONTEXT->bool_val( true )
#define	SMT_CST_BOOL_FALSE  CONTEXT->bool_val( false )

#define	SMT_CST_INT_ZERO  CONTEXT->int_val( 0 )


bool Z3Solver::destroyChecker()
{
	resetTable();

	CONFIG = nullptr;

	CONTEXT = nullptr;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	++SOLVER_SESSION_ID;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( true );
}

bool Z3Solver::resetTable()
{
	base_this_type::resetTable();

	mTableOfParameterDecl.push_back( z3::symbol(*CONTEXT, 0) );

	mTableOfParameterExpr.push_back( z3::expr(*CONTEXT) );

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

	z3::config config;
	z3::context context;
	createChecker(config, context);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Solver::isSatisfiable(...) :"
			<< SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_sat(aCondition);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	z3::expr z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << z3Condition << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "Z3::CONTEXT :" << SOLVER_SESSION_ID << ">"
				<< std::endl << context << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH

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

	//if( z3Condition != nullptr )
	{
		z3::solver z3Solver(*CONTEXT);

		if( mBitsetOfConstrainedParameter.anyTrue() )
		{
			appendPossitiveAssertion( z3Solver );
		}

		z3Solver.add( z3Condition );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )	// trace to file
	dbg_smt(z3Solver);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


		switch( z3Solver.check() )
		{
			case z3::sat:
			{
				satisfiability = SolverDef::SATISFIABLE;
				break;
			}

			case z3::unsat:
			{
				satisfiability = SolverDef::UNSATISFIABLE;
				break;
			}

			case z3::unknown:
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

	z3::config config;
	z3::context context;
	createChecker(config, context);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Solver::solve(...) :"
			<< SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_model(aCondition, dataVector, valuesVector);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	z3::expr z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << z3Condition << std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "Z3::CONTEXT :" << SOLVER_SESSION_ID << ">"
				<< std::endl << context << std::endl;
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	//if( z3Condition != nullptr )
	{
		z3::solver z3Solver(*CONTEXT);

		z3Solver.add( z3Condition );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )	// trace to file
	dbg_smt(z3Solver, true);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

		switch( z3Solver.check() )
		{
			case z3::sat:
			{
				satisfiability = SolverDef::SATISFIABLE;

				z3::model z3Model = z3Solver.get_model();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Model sat:" << SOLVER_SESSION_ID << ">"
			<< std::endl << z3Model << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

				unsigned num_constants = z3Model.num_consts();
				for( unsigned i = 0 ; i < num_constants ; i++ )
				{
					z3::func_decl paramDecl = z3Model.get_const_decl(i);

					z3::symbol paramSymbol = z3Model.get_const_decl(i).name();

					z3::expr value = z3Model.get_const_interp(paramDecl);

					int offset = mTableOfParameterDecl.find(paramSymbol);
					if( offset >= 0 )
					{
						dataVector.append( mTableOfParameterInstance[offset] );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << paramSymbol << " := ";
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

						BF bfVal = to_baseform( z3Model, value);

						valuesVector.append( bfVal.valid() ?
								bfVal : dataVector.back() );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << value << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::solve :> unfound "
									"parameter instance for Z3 symbol << "
								<< paramSymbol << " >> !!!"
								<< SEND_EXIT;
					}
				}


				break;
							break;
			}

			case z3::unsat:
			{
				satisfiability = SolverDef::UNSATISFIABLE;
				break;
			}

			case z3::unknown:
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
	AVM_OS_TRACE << "solve :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( satisfiability == SolverDef::SATISFIABLE );
}



/**
 * TOOLS
 */
z3::sort Z3Solver::getZ3Type(const BaseTypeSpecifier & bts)
{
	if( bts.isTypedBoolean() )
	{
		return( CONTEXT->bool_sort() );
	}

	else if( bts.isTypedEnum() )
	{
		return( CONTEXT->int_sort() );
		// TODO Attention : il faudrait rajouter les contraintes
		// d'intervalle pour le type énuméré
	}
	else if( bts.weaklyTypedInteger() )
	{
		return( CONTEXT->int_sort() );
	}

	else if( bts.weaklyTypedReal() )
	{
		return( CONTEXT->real_sort() );
	}

	return( CONTEXT->real_sort() );
}


z3::expr Z3Solver::getParameterExpr(const BF & bParameter)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bParameter.to< InstanceOfData >() );

	if( aParameter.getMark() == 0 )
	{
		aParameter.setMark( mTableOfParameterInstance.size() );
		mTableOfParameterInstance.append( bParameter );

		mTableOfParameterDecl.push_back( CONTEXT->str_symbol(
				uniqParameterID( aParameter ).c_str() ) );

		const BaseTypeSpecifier & paramTypeSpecifier =
				aParameter.referedTypeSpecifier();

		mTableOfParameterExpr.push_back(
				CONTEXT->constant(mTableOfParameterDecl.last(),
						getZ3Type(paramTypeSpecifier)) );

		mBitsetOfConstrainedParameter.push_back(
				paramTypeSpecifier.couldGenerateConstraint() );

		mBitsetOfPositiveParameter.push_back(
				paramTypeSpecifier.isTypedPositiveNumber() );

		mBitsetOfStrictlyPositiveParameter.push_back(
				paramTypeSpecifier.isTypedStrictlyPositiveNumber() );
	}

	return( mTableOfParameterExpr.at( aParameter.getMark() ) );
}


z3::expr Z3Solver::getBoundParameterExpr(const BF & bParameter, z3::expr & z3And)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bParameter.to< InstanceOfData >() );

	aParameter.setMark( mTableOfParameterInstance.size() );
	mTableOfParameterInstance.append( bParameter );

	mTableOfParameterDecl.push_back( CONTEXT->str_symbol(
			uniqParameterID( aParameter ).c_str() ) );

	const BaseTypeSpecifier & paramTypeSpecifier =
			aParameter.referedTypeSpecifier();

	z3::expr paramExpr = CONTEXT->constant(
			mTableOfParameterDecl.last(), getZ3Type(paramTypeSpecifier));

	mTableOfParameterExpr.push_back( paramExpr );

	mBitsetOfStrictlyPositiveParameter.push_back( false );
	mBitsetOfPositiveParameter.push_back( false );
	mBitsetOfConstrainedParameter.push_back( false );

	if( paramTypeSpecifier.isTypedStrictlyPositiveNumber() )
	{
		z3And = z3And && (paramExpr > SMT_CST_INT_ZERO);
	}
	else if( paramTypeSpecifier.isTypedPositiveNumber() )
	{
		z3And = z3And && (paramExpr >= SMT_CST_INT_ZERO);
	}

	return( mTableOfParameterExpr.at( aParameter.getMark() ) );
}


z3::expr Z3Solver::getVariableExpr(InstanceOfData * aVar, std::size_t varID)
{
	if( mTableOfVariableExpr.size() <= varID )
	{
		mTableOfVariableDecl.push_back( CONTEXT->str_symbol(
				uniqVariableID( *aVar, varID ).c_str() ) );

		mTableOfVariableExpr.push_back(
				CONTEXT->constant(mTableOfVariableDecl.last(),
						getZ3Type(aVar->getTypeSpecifier())) );
		}

	return( mTableOfVariableExpr.at( varID ) );
}


void Z3Solver::appendPossitiveAssertion(z3::solver & z3Solver)
{
	std::size_t endOffset = mBitsetOfConstrainedParameter.size();
	for( std::size_t offset = 1 ; offset < endOffset ; ++offset )
	{
		if( mBitsetOfStrictlyPositiveParameter[offset] )
		{
			z3Solver.add( mTableOfParameterExpr[offset] > SMT_CST_INT_ZERO );
		}
		else if( mBitsetOfPositiveParameter[offset] )
		{
			z3Solver.add( mTableOfParameterExpr[offset] >= SMT_CST_INT_ZERO );
		}
	}
}


z3::expr Z3Solver::safe_from_baseform(const BF & exprForm)
{
	z3::expr e(*CONTEXT);

	try
	{
		e = from_baseform(exprForm);

		destroyChecker();
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tZ3Solver::safe_from_baseform< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\tFailed to CONVERT sep::fml::expression to Z3::Expr:>"
				<< std::endl
				<< "\t  " << exprForm.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();
	}

	return( e );
}


z3::expr Z3Solver::from_baseform(const BF & exprForm)
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
					return( from_baseform(aCode.first()) ==
							from_baseform(aCode.second()) );
				}

				case AVM_OPCODE_NEQ:
				{
					return( from_baseform(aCode.first()) !=
							from_baseform(aCode.second()) );

//					ARGS arg( 2 );
//
//					arg.next( from_baseform(aCode.first()) );
//					arg.next( from_baseform(aCode.second()) );
//
//					return( Z3_mk_distinct(CONTEXT, 2, arg->table) );
				}

				case AVM_OPCODE_LT:
				{
					return( from_baseform(aCode.first()) <
							from_baseform(aCode.second()) );
				}

				case AVM_OPCODE_LTE:
				{
					return( from_baseform(aCode.first()) <=
							from_baseform(aCode.second()) );
				}

				case AVM_OPCODE_GT:
				{
					return( from_baseform(aCode.first()) >
							from_baseform(aCode.second()) );
				}

				case AVM_OPCODE_GTE:
				{
					return( from_baseform(aCode.first()) >=
							from_baseform(aCode.second()) );
				}


				case AVM_OPCODE_CONTAINS:
				{
					BuiltinCollection * aCollection =
							aCode.first().to_ptr< BuiltinCollection >();

					if( aCollection->singleton() )
					{
						return( from_baseform(aCollection->at(0))
								== from_baseform(aCode.second()) );
					}
					else if( aCollection->populated() )
					{
						std::size_t colSize = aCollection->size();
						const BF & elt = aCode.second();

						z3::expr z3Or = ( from_baseform(elt) ==
								from_baseform(aCollection->at(0)) );

						for( std::size_t offset = 1 ; offset < colSize ; ++offset )
						{
							z3Or = z3Or || (from_baseform(elt) ==
								from_baseform(aCollection->at(offset)));
						}

						return( z3Or );
					}
					else
					{
						return( CONTEXT->bool_val(false) );
					}
				}


				// LOGICAL OPERATION
				case AVM_OPCODE_NOT:
				{
					return( not from_baseform(aCode.first()) );
				}

				case AVM_OPCODE_AND:
				{
					z3::expr z3And =
							from_baseform(aCode.first()) &&
							from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3And = z3And && from_baseform(aCode.at(offset));
					}

					return( z3And );
				}

				case AVM_OPCODE_NAND:
				{
					z3::expr z3And =
							from_baseform(aCode.first()) &&
							from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3And = z3And && from_baseform(aCode.at(offset));
					}

					return( not z3And );
				}

//				case AVM_OPCODE_XAND:

				case AVM_OPCODE_OR:
				{
					z3::expr z3Or =
							from_baseform(aCode.first()) ||
							from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3Or = z3Or || from_baseform(aCode.at(offset));
					}

					return( z3Or );
				}

				case AVM_OPCODE_NOR:
				{
					z3::expr z3Or =
						from_baseform(aCode.first()) ||
						from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3Or = z3Or || from_baseform(aCode.at(offset));
					}

					return( not z3Or );
				}


				// BITWISE OPERATION
//				case AVM_OPCODE_BAND:
//				case AVM_OPCODE_BOR:
//				case AVM_OPCODE_LSHIFT:
//				case AVM_OPCODE_RSHIFT:

				case AVM_OPCODE_XOR:
				{
					z3::expr arg0 = from_baseform(aCode.first());

					z3::expr arg1 = from_baseform(aCode.second());

					return( (arg0 && (! arg1)) || ((! arg0) && arg1) );
				}

//				case AVM_OPCODE_XNOR:

				case AVM_OPCODE_IMPLIES:
				{
					return( z3::implies(
							from_baseform(aCode.first()) ,
							from_baseform(aCode.second()) ) );
				}


				case AVM_OPCODE_EXISTS:
				{
					std::size_t boundVarCount = aCode.size()  - 1;

					z3::expr_vector arg( *CONTEXT );

					z3::expr z3Constraint = SMT_CST_BOOL_TRUE;

					for (std::size_t offset = 0; offset < boundVarCount; ++offset)
					{
						arg.push_back(
								getBoundParameterExpr(
										aCode[ offset ], z3Constraint) );
					}

					z3Constraint = z3Constraint &&
							from_baseform(aCode[ boundVarCount ]);

					return( z3::exists(arg, z3Constraint) );
				}

				case AVM_OPCODE_FORALL:
				{
					std::size_t boundVarCount = aCode.size()  - 1;

					z3::expr_vector arg( *CONTEXT );

					z3::expr z3Constraint = SMT_CST_BOOL_TRUE;

					for (std::size_t offset = 0; offset < boundVarCount; ++offset)
					{
						arg.push_back(
								getBoundParameterExpr(
										aCode[ offset ], z3Constraint) );
					}

					z3Constraint = z3::implies( z3Constraint,
							from_baseform(aCode[ boundVarCount ]) );

					return( z3::forall(arg, z3Constraint) );
				}


				// ARITHMETIC OPERATION
				case AVM_OPCODE_PLUS:
				{
					z3::expr z3Plus =
							from_baseform(aCode.first()) +
							from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3Plus = z3Plus + from_baseform(aCode.at(offset));
					}

					return( z3Plus );
				}

				case AVM_OPCODE_UMINUS:
				{
					return( - from_baseform(aCode.first()) );
				}

				case AVM_OPCODE_MINUS:
				{
					z3::expr z3Minus =
							from_baseform(aCode.first()) -
							from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3Minus = z3Minus - from_baseform(aCode.at(offset));
					}

					return( z3Minus );
				}

				case AVM_OPCODE_MULT:
				{
					z3::expr z3Mult =
							from_baseform(aCode.first()) *
							from_baseform(aCode.second());

					for( std::size_t offset = 2 ; offset < aCode.size() ; ++offset )
					{
						z3Mult = z3Mult * from_baseform(aCode.at(offset));
					}

					return( z3Mult );
				}

				case AVM_OPCODE_DIV:
				{
					return( from_baseform(aCode.first()) /
							from_baseform(aCode.second()) );
				}

				case AVM_OPCODE_POW:
				{

//					if( ExpressionFactory::isInt32(aCode.second()) )
//					{
//						return( std::pw(
//								from_baseform(aCode.first()),
//								from_baseform(aCode.second()) ) );
//					}
//					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::from_baseform:> "
									"Unsupported expression Operator "
									"<< AVM_OPCODE_POW >> !!!"
								<< SEND_EXIT;

						return( z3::expr(*CONTEXT) );
					}
				}

//				case AVM_OPCODE_MOD:

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Z3Solver::from_baseform:> "
								"Unexpected expression !!!\n"
							<< aCode.toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return( z3::expr(*CONTEXT) );
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
			return( CONTEXT->bool_val(
					exprForm.to< Boolean >().getValue() ) );
		}

		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( CONTEXT->int_val( static_cast< int64_t >(
					exprForm.to< Integer >().toInteger() ) ) );

//			return( CONTEXT->int_val( exprForm.to< Integer >().str().c_str() ) );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( CONTEXT->real_val(
					exprForm.to< Rational >().toNumerator(),
					exprForm.to< Rational >().toDenominator() ) );

//			return( CONTEXT->real_val( exprForm.to< Rational >().str().c_str() ) );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( CONTEXT->real_val(
					exprForm.to< Float >().str().c_str() ) );
		}


		case FORM_RUNTIME_ID_KIND:
		{
			return( CONTEXT->int_val( exprForm.bfRID().getRid() ) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Z3Solver::from_baseform:> Unexpected OBJECT KIND << "
					<< exprForm.classKindName() << " >> as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			return( z3::expr(*CONTEXT) );
		}
	}

	AVM_OS_FATAL_ERROR_EXIT
			<< "Z3Solver::from_baseform ERROR !!!"
			<< SEND_EXIT;

	return( z3::expr(*CONTEXT) );
}


BF Z3Solver::to_baseform(z3::model z3Model, z3::expr z3Form)
{
	std::ostringstream oss;
	oss << z3Form;

	if( z3Form.is_bool() )
	{
		return( ExpressionConstructor::newBoolean( oss.str() ) );
	}
	else if( z3Form.is_int() )
	{
		return( ExpressionConstructor::newInteger( oss.str() ) );
	}
	else if( z3Form.is_real() )
	{
		return( ExpressionConstructor::newFloat( oss.str() ) );
	}

	return( BF::REF_NULL );
}


/**
 * Using file API
 */
SolverDef::SATISFIABILITY_RING Z3Solver::smt_check_sat(const BF & aCondition)
{
	SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

	BFVector paramVector;

	StringOutStream ossCondition("", "\t", "");
	to_smt(ossCondition, aCondition, paramVector);

	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< "z3_cpp_check_sat_" << SOLVER_SESSION_ID << ".log" );
	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
//		osFile << "(echo \"" << aCondition.str() << "\")" << std::endl;

		InstanceOfData * aParam;

		std::size_t paramCount = paramVector.size();
		for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
		{
			aParam = paramVector[ offset ].to_ptr< InstanceOfData >();

			osFile << "(declare-const " << aParam->getFullyQualifiedNameID()
					<< " ";
			if( aParam->isTypedBoolean() )
			{
				osFile << "Bool";
			}
			else if( aParam->isTypedEnum() )
			{
				osFile << "Int";
			}
			else if( aParam->weaklyTypedInteger() )
			{
				osFile << "Int";
			}
			else if( aParam->weaklyTypedReal() )
			{
				osFile << "Real";
			}
			else
			{
				osFile << "Unknown";
			}
			osFile << ")" << std::endl;
		}

		osFile << ";;(assert " << ossCondition.str() << ")" << std::endl;

		// AST SERIALIZATION
		z3::expr z3Condition = from_baseform(aCondition);
		osFile << std::endl << std::endl
				<< "(assert "    << z3Condition << ")" << std::endl << std::endl;

		osFile << "(check-sat)" << std::endl;

		osFile.close();
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

	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< "z3_cpp_get_model_" << SOLVER_SESSION_ID << ".log");
	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
//		osFile << "(echo \"" << aCondition.str() << "\")" << std::endl;

		InstanceOfData * aParam;

		std::size_t paramCount = paramVector.size();
		for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
		{
			aParam = paramVector[ offset ].to_ptr< InstanceOfData >();

			osFile << "(declare-const " << aParam->getFullyQualifiedNameID()
					<< " ";
			if( aParam->isTypedBoolean() )
			{
				osFile << "Bool";
			}
			else if( aParam->isTypedEnum() )
			{
				osFile << "Int";
			}
			else if( aParam->weaklyTypedInteger() )
			{
				osFile << "Int";
			}
			else if( aParam->weaklyTypedReal() )
			{
				osFile << "Real";
			}
			else
			{
				osFile << "Unknown";
			}
			osFile << ")" << std::endl;
		}

		osFile << ";;(assert " << ossCondition.str() << ")" << std::endl;

		// AST SERIALIZATION
		z3::expr z3Condition = from_baseform(aCondition);
		osFile << std::endl << std::endl
				<< "(assert "    << z3Condition << ")" << std::endl << std::endl;

		osFile << "(get-model)" << std::endl;

		osFile.close();
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



bool Z3Solver::to_smt(OutStream & os,
		const BF & exprForm, BFVector & dataVector) const
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( exprForm ) << "expression !!!"
			<< SEND_EXIT;

	bool hasQuantifier = false;

	os << TAB;

	switch( exprForm.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & aCode = exprForm.to< AvmCode >();

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
					os << "(not";
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

				auto endOperand = aCode.end();
				auto itOperand = aCode.begin();
				for( ; (itOperand + 1) != endOperand ; ++itOperand )
				{
					boundVars.append(*itOperand);

					os << " " << (*itOperand).to<
							InstanceOfData >().getFullyQualifiedNameID();
				}

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

			os << eoe << ')';

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			dataVector.add_unique( exprForm );

			os << exprForm.to< InstanceOfData >().getFullyQualifiedNameID();

			break;
		}

		case FORM_ARRAY_BF_KIND:
		{
			os << '{';
			ArrayBF * arrayArg =  exprForm.to_ptr< ArrayBF >();
			for( std::size_t idx = 0 ; idx < arrayArg->size() ; ++idx )
			{
				os << " ";
				hasQuantifier = to_smt(os, arrayArg->at(idx), dataVector)
							|| hasQuantifier;
			}

			os << " }";

			break;
		}

		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		{
			os << exprForm.str();

			break;
		}

		default:
		{
			if( exprForm.is< BuiltinContainer >() )
			{
				os << '{';
				BuiltinContainer * aCollection =
						exprForm.to_ptr< BuiltinContainer >();
				for( std::size_t idx = 0 ; idx < aCollection->size() ; ++idx )
				{
					os << " ";
					hasQuantifier = to_smt(os, aCollection->at(idx), dataVector)
								|| hasQuantifier;
				}

				os << " }";
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Z3Solver::to_smt:> Unexpected OBJECT KIND << "
						<< exprForm.classKindName() << " >> as expression << "
						<< exprForm.str() << " >> !!!"
						<< SEND_EXIT;

				os << exprForm.str();
			}

			break;
		}
	}

	os << EOL;

	return hasQuantifier;
}


void Z3Solver::dbg_smt(z3::solver & z3Solver, bool produceModelOption) const
{
	AVM_OS_TRACE << "z3::solver::to_smt2(...) --> "
			<< ( produceModelOption ? "Get Model" : "isSatifiable" ) << std::endl
			<< z3Solver.to_smt2() << std::endl;


	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< ( produceModelOption ? "z3_cpp_get_model_" : "z3_cpp_check_sat_" )
			<< SOLVER_SESSION_ID << ".smt2" );

	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
		osFile << ";; yices-smt2 " << fileLocation << std::endl;
		osFile << ";; Getting info" << std::endl
				<< "(get-info :name)"    << std::endl
				<< "(get-info :version)" << std::endl;

		if( produceModelOption )
		{
			osFile << ";; Getting values or models" << std::endl
					<< "(set-option :produce-models true)" << std::endl
//					<< "; Getting assignments" << std::endl
//					<< "(set-option :produce-assignments true)" << std::endl
//					<< "; Logic" << std::endl
//					<< "(set-logic ALL)" << std::endl
					<< std::endl;

			osFile << z3Solver.to_smt2() << std::endl;

			osFile << "(get-model)" << std::endl
//					<< "(get-assignment)"
					<< std::endl;
		}
		else
		{
//			osFile << ";; Logic" << std::endl
//					<< "(set-logic ALL)" << std::endl;

			osFile << z3Solver.to_smt2() << std::endl;
		}

		osFile.close();
	}
}


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
void display_function_interpretations(OutStream & out, Z3_context c, Z3_model m)
{
    unsigned num_functions, i;

    out << "function interpretations:" << std::endl;

    num_functions = Z3_model_get_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
        Z3_func_decl fdecl;
        Z3_symbol name;
        Z3_ast func_else;
        unsigned num_entries = 0, j;
        Z3_func_interp_opt finterp;

        fdecl = Z3_model_get_func_decl(c, m, i);
        finterp = Z3_model_get_func_interp(c, m, fdecl);
	Z3_func_interp_inc_ref(c, finterp);
        name = Z3_get_decl_name(c, fdecl);
        display_symbol(out, c, name);
        out << " = {";
        if (finterp)
          num_entries = Z3_func_interp_get_num_entries(c, finterp);
        for (j = 0; j < num_entries; j++) {
            unsigned num_args, k;
            Z3_func_entry fentry = Z3_func_interp_get_entry(c, finterp, j);
	    Z3_func_entry_inc_ref(c, fentry);
            if (j > 0) {
                out << ", ";
            }
            num_args = Z3_func_entry_get_num_args(c, fentry);
            out << "(";
            for (k = 0; k < num_args; k++) {
                if (k > 0) {
                    out << ", ";
                }
                display_ast(out, c, Z3_func_entry_get_arg(c, fentry, k));
            }
            out << "|->";
            display_ast(out, c, Z3_func_entry_get_value(c, fentry));
            out << ")";
	    Z3_func_entry_dec_ref(c, fentry);
        }
        if (num_entries > 0) {
            out << ", ";
        }
        out << "(else|->";
        func_else = Z3_func_interp_get_else(c, finterp);
        display_ast(out, c, func_else);
        out << ")}\n";
	Z3_func_interp_dec_ref(c, finterp);
    }
}


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
//        Z3_bool ok;
//        name = Z3_get_decl_name(c, cnst);
//        display_symbol(out, c, name);
//        out << " = ";
//        a = Z3_mk_app(c, cnst, 0, 0);
//        v = a;
//        ok = Z3_model_eval(c, m, a, 1, &v);
//        display_ast(out, c, v);
//        out << std::endl;
//    }
//    display_function_interpretations(out, c, m);
//}


} /* namespace sep */


#endif /* _AVM_SOLVER_Z3_ */


