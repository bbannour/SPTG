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
#if defined( _AVM_SOLVER_Z3_ )


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

#include <fstream>


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

avm_uint64_t Z3Solver::SOLVER_SESSION_ID = 0;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


#if defined( _AVM_SOLVER_Z3_CPP_ )


/**
 * CREATE - DESTROY
 * ValidityChecker
 */


bool Z3Solver::createChecker(z3::config & cfg, z3::context & ctx)
{
	CFG = & cfg;

	CFG->set("MODEL", "true");

	CTX = & ctx;


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	++SOLVER_SESSION_ID;
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		mLogFolderLocation = OSS << VFS::ProjectLogPath << "/z3/";

		if ( not VFS::checkWritingFolder(mLogFolderLocation) )
		{
			AVM_OS_LOG << " Z3Solver::createChecker :> Error: The folder "
					<< "`" << mLogFolderLocation	<< "' "
					<< "---> doesn't exist or is not writable !!!"
					<< std::endl << std::endl;
			return( false );
		}
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	SMT_CST_BOOL_TRUE  = CTX->bool_val(true);
	SMT_CST_BOOL_FALSE = CTX->bool_val(false);

	resetTable();

	return( true );
}


bool Z3Solver::destroyChecker()
{
	resetTable();

	CFG = NULL;

	CTX = NULL;

	return( true );
}

bool Z3Solver::resetTable()
{
	base_this_type::resetTable();

	mTableOfParameterDecl.append( z3::symbol(*CTX, 0) );

	mTableOfParameterExpr.append( z3::expr(*CTX) );

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

	z3::config cfg;
	z3::context ctx;
	createChecker(cfg, ctx);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Solver::isSatisfiable(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		smt_check_sat(aCondition);
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	z3::expr z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << z3Condition << std::endl;
AVM_IF_DEBUG_LEVEL_GTE_HIGH
	AVM_OS_TRACE << "Z3::CTX :" << SOLVER_SESSION_ID << ">" << std::endl
			<< ctx << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	//if( z3Condition != NULL )
	{
		z3::solver z3Solver(*CTX);

		z3Solver.add( z3Condition );

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

	z3::config cfg;
	z3::context ctx;
	createChecker(cfg, ctx);

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
	AVM_OS_TRACE << "Z3::CTX :" << SOLVER_SESSION_ID << ">" << std::endl
			<< ctx << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	z3::solver z3Solver(*CTX);

	z3Solver.add( z3Condition );

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

	//if( z3Condition != NULL )
	{
		z3::solver z3Solver(*CTX);

		z3Solver.add( z3Condition );

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
z3::sort Z3Solver::getZ3Type(BaseTypeSpecifier * bts)
{
	if( bts->isTypedBoolean() )
	{
		return( CTX->bool_sort() );
	}

	else if( bts->isTypedEnum() )
	{
		return( CTX->int_sort() );
		// TODO Attention : il faudrait rajouter les contraintes
		// d'intervalle pour le type énuméré
	}
	else if( bts->weaklyTypedInteger() )
	{
		return( CTX->int_sort() );
	}

	else if( bts->weaklyTypedReal() )
	{
		return( CTX->real_sort() );
	}

	return( CTX->real_sort() );
}


z3::expr Z3Solver::getParameterExpr(const BF & bfParameter)
{
	InstanceOfData * aParameter = bfParameter.to_ptr< InstanceOfData >();

	if( aParameter->getMark() == 0 )
	{
		aParameter->setMark( mTableOfParameterInstance.size() );
		mTableOfParameterInstance.append( bfParameter );

		mTableOfParameterDecl.push_back(
				CTX->str_symbol(aParameter->getNameID().c_str()) );

		mTableOfParameterExpr.push_back(
				CTX->constant(mTableOfParameterDecl.last(),
						getZ3Type(aParameter->referedTypeSpecifier())) );
	}

	return( mTableOfParameterExpr.at( aParameter->getMark() ) );
}




z3::expr Z3Solver::getVariableExpr(InstanceOfData * aVar, std::size_t varID)
{
	if( mTableOfVariableExpr.size() <= varID )
	{
		mTableOfVariableDecl.push_back(
				CTX->str_symbol(aVar->getNameID().c_str()) );

		mTableOfVariableExpr.push_back(
				CTX->constant(mTableOfVariableDecl.last(),
						getZ3Type(aVar->getTypeSpecifier())) );
		}

	return( mTableOfVariableExpr.at( varID ) );
}


z3::expr Z3Solver::safe_from_baseform(const BF & exprForm,
		BaseTypeSpecifier * typeSpecifier)
{
	z3::expr e(*CTX);

	try
	{
		e = from_baseform(exprForm, typeSpecifier);

		destroyChecker();
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tZ3Solver::safe_from_baseform< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\tFailed to CONVERT sep::fml::expression to Z3::Expr:>" << std::endl
				<< "\t  " << exprForm.str(" ") << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();
	}

	return( e );
}


z3::expr Z3Solver::from_baseform(const BF & exprForm,
		BaseTypeSpecifier * typeSpecifier)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( exprForm ) << "expression !!!"
			<< SEND_EXIT;


	switch( exprForm.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode * aCode = exprForm.to_ptr< AvmCode >();

			typeSpecifier = TypeManager::UNIVERSAL;

			switch( aCode->getAvmOpCode() )
			{
				// COMPARISON OPERATION
				case AVM_OPCODE_EQ:
				{
					return( from_baseform(aCode->first() , typeSpecifier) ==
							from_baseform(aCode->second(), typeSpecifier) );
				}

				case AVM_OPCODE_NEQ:
				{
					return( from_baseform(aCode->first() , typeSpecifier) !=
							from_baseform(aCode->second(), typeSpecifier) );

//					ARGS arg( 2 );
//
//					arg.next( from_baseform(aCode->first() , typeSpecifier) );
//					arg.next( from_baseform(aCode->second(), typeSpecifier) );
//
//					return( Z3_mk_distinct(CTX, 2, arg->table) );
				}

				case AVM_OPCODE_LT:
				{
					return( from_baseform(aCode->first() , typeSpecifier) <
							from_baseform(aCode->second(), typeSpecifier) );
				}

				case AVM_OPCODE_LTE:
				{
					return( from_baseform(aCode->first() , typeSpecifier) <=
							from_baseform(aCode->second(), typeSpecifier) );
				}

				case AVM_OPCODE_GT:
				{
					return( from_baseform(aCode->first() , typeSpecifier) >
							from_baseform(aCode->second(), typeSpecifier) );
				}

				case AVM_OPCODE_GTE:
				{
					return( from_baseform(aCode->first() , typeSpecifier) >=
							from_baseform(aCode->second(), typeSpecifier) );
				}


				case AVM_OPCODE_CONTAINS:
				{
					BuiltinCollection * aCollection =
							aCode->first().to_ptr< BuiltinCollection >();

					if( aCollection->singleton() )
					{
						return( from_baseform(aCollection->at(0), typeSpecifier) ==
								from_baseform(aCode->second(), typeSpecifier) );
					}
					else if( aCollection->populated() )
					{
						std::size_t colSize = aCollection->size();
						const BF & elt = aCode->second();

						z3::expr z3Or = ( from_baseform(elt, typeSpecifier) ==
								from_baseform(aCollection->at(0), typeSpecifier) );

						for( std::size_t offset = 1 ; offset < colSize ; ++offset )
						{
							z3Or = z3Or || (from_baseform(elt, typeSpecifier) ==
								from_baseform(aCollection->at(offset), typeSpecifier));
						}

						return( z3Or );
					}
					else
					{
						return( ((typeSpecifier != NULL) &&
								typeSpecifier->isTypedBoolean()) ?
										CTX->bool_val(false) : CTX->int_val(0) );
					}
				}


				// LOGICAL OPERATION
				case AVM_OPCODE_NOT:
				{
					return( not from_baseform(
							aCode->first(), TypeManager::BOOLEAN) );
				}

				case AVM_OPCODE_AND:
				{
					z3::expr z3And =
							from_baseform(aCode->first(), TypeManager::BOOLEAN) &&
							from_baseform(aCode->second(), TypeManager::BOOLEAN);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3And = z3And && from_baseform(
								aCode->at(offset), TypeManager::BOOLEAN);
					}

					return( z3And );
				}

				case AVM_OPCODE_NAND:
				{
					z3::expr z3And =
							from_baseform(aCode->first(), TypeManager::BOOLEAN) &&
							from_baseform(aCode->second(), TypeManager::BOOLEAN);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3And = z3And && from_baseform(
								aCode->at(offset), TypeManager::BOOLEAN);
					}

					return( not z3And );
				}

//				case AVM_OPCODE_XAND:

				case AVM_OPCODE_OR:
				{
					z3::expr z3Or =
							from_baseform(aCode->first(), TypeManager::BOOLEAN) ||
							from_baseform(aCode->second(), TypeManager::BOOLEAN);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3Or = z3Or || from_baseform(
								aCode->at(offset), TypeManager::BOOLEAN);
					}

					return( z3Or );
				}

				case AVM_OPCODE_NOR:
				{
					z3::expr z3Or =
						from_baseform(aCode->first(), TypeManager::BOOLEAN) ||
						from_baseform(aCode->second(), TypeManager::BOOLEAN);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3Or = z3Or || from_baseform(
								aCode->at(offset), TypeManager::BOOLEAN);
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
					z3::expr arg0 = from_baseform(
							aCode->first(), TypeManager::BOOLEAN);

					z3::expr arg1 = from_baseform(
							aCode->second(), TypeManager::BOOLEAN);

					return( (arg0 && (! arg1)) || ((! arg0) && arg1) );
				}

//				case AVM_OPCODE_XNOR:


				// ARITHMETIC OPERATION
				case AVM_OPCODE_PLUS:
				{
					z3::expr z3Plus =
							from_baseform(aCode->first(), typeSpecifier) +
							from_baseform(aCode->second(), typeSpecifier);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3Plus = z3Plus +
								from_baseform(aCode->at(offset), typeSpecifier);
					}

					return( z3Plus );
				}

				case AVM_OPCODE_UMINUS:
				{
					return( - from_baseform(aCode->first(), typeSpecifier) );
				}

				case AVM_OPCODE_MINUS:
				{
					z3::expr z3Minus =
							from_baseform(aCode->first(), typeSpecifier) -
							from_baseform(aCode->second(), typeSpecifier);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3Minus = z3Minus -
								from_baseform(aCode->at(offset), typeSpecifier);
					}

					return( z3Minus );
				}

				case AVM_OPCODE_MULT:
				{
					z3::expr z3Mult =
							from_baseform(aCode->first(), typeSpecifier) *
							from_baseform(aCode->second(), typeSpecifier);

					for( std::size_t offset = 2 ; offset < aCode->size() ; ++offset )
					{
						z3Mult = z3Mult *
								from_baseform(aCode->at(offset), typeSpecifier);
					}

					return( z3Mult );
				}

				case AVM_OPCODE_DIV:
				{
					return( from_baseform(aCode->first() , typeSpecifier) /
							from_baseform(aCode->second(), typeSpecifier) );
				}

				case AVM_OPCODE_POW:
				{

//					if( ExpressionFactory::isInt32(aCode->second()) )
//					{
//						return( std::pw(
//								from_baseform(aCode->first() , typeSpecifier),
//								from_baseform(aCode->second() , typeSpecifier) ) );
//					}
//					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::from_baseform:> "
									"Unsupported expression Operator "
									"<< AVM_OPCODE_POW >> !!!"
								<< SEND_EXIT;

						return( z3::expr(*CTX) );
					}
				}

//				case AVM_OPCODE_MOD:

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Z3Solver::from_baseform:> "
								"Unexpected expression !!!\n"
							<< aCode->toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return( z3::expr(*CTX) );
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
			return( CTX->bool_val(
					exprForm.to_ptr< Boolean >()->getValue() ) );
		}

		case FORM_BUILTIN_INTEGER_KIND:
		{
			if( (typeSpecifier != NULL) && typeSpecifier->isTypedBoolean() )
			{
//				return( CTX->bool_val(
//						not exprForm.to_ptr< Integer >()->isZero() ) );

				return( exprForm.to_ptr< Integer >()->isZero() ?
						SMT_CST_BOOL_FALSE : SMT_CST_BOOL_TRUE );
			}
			else
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

				return( CTX->int_val( static_cast< __int64 >(
						exprForm.to_ptr< Integer >()->toInteger() ) ) );

#else

				return( CTX->int_val( static_cast< __int64 >(
						exprForm.to_ptr< Integer >()->toInteger() ) ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}

//			return( CTX->int_val( exprForm.to_ptr< Integer >()->str().c_str() ) );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			if( (typeSpecifier != NULL) && typeSpecifier->isTypedBoolean() )
			{
//				return( CTX->bool_val(
//						not exprForm.to_ptr< Rational >()->isZero() ) );

				return( exprForm.to_ptr< Rational >()->isZero() ?
						SMT_CST_BOOL_FALSE : SMT_CST_BOOL_TRUE );
			}
			else
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

				return( CTX->real_val(
						exprForm.to_ptr< Rational >()->toNumerator(),
						exprForm.to_ptr< Rational >()->toDenominator() ) );

#else

				return( CTX->real_val(
						exprForm.to_ptr< Rational >()->toNumerator(),
						exprForm.to_ptr< Rational >()->toDenominator() ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}

//			return( CTX->real_val( exprForm.to_ptr< Rational >()->str().c_str() ) );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			if( (typeSpecifier != NULL) && typeSpecifier->isTypedBoolean() )
			{
//				return( CTX->bool_val(
//						not exprForm.to_ptr< Float >()->isZero() ) );

				return( exprForm.to_ptr< Float >()->isZero() ?
						SMT_CST_BOOL_FALSE : SMT_CST_BOOL_TRUE );
			}
			else
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

				return( CTX->real_val(
						exprForm.to_ptr< Float >()->str().c_str() ) );

#else

				return( CTX->real_val(
						exprForm.to_ptr< Float >()->str().c_str() ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}
		}


		case FORM_RUNTIME_ID_KIND:
		{
			return( CTX->int_val( exprForm.bfRID().getRid() ) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Z3Solver::from_baseform:> Unexpected BASEFORM KIND << "
					<< exprForm.classKindName() << " >> as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			return( z3::expr(*CTX) );
		}
	}

	AVM_OS_FATAL_ERROR_EXIT
			<< "Z3Solver::from_baseform ERROR !!!"
			<< SEND_EXIT;

	return( z3::expr(*CTX) );
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

	std::string fileLocation = OSS << mLogFolderLocation,
			<< "z3_check_sat_" << SOLVER_SESSION_ID << ".smt";
	std::ofstream osFile;
	osFile.open(fileLocation.c_str(), std::ios_base::out);
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
			else if( aParam->weaklyTypedInteger() ||
					aParam->isTypedEnum() )
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

		osFile << "(assert " << ossCondition.str() << ")" << std::endl;

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

	std::string fileLocation = OSS << mLogFolderLocation
			<< "z3_check_sat_" << SOLVER_SESSION_ID << ".smt";
	std::ofstream osFile;
	osFile.open(fileLocation.c_str(), std::ios_base::out);
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
			else if( aParam->weaklyTypedInteger() ||
					aParam->isTypedEnum() )
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

		osFile << "(assert " << ossCondition.str() << ")" << std::endl;

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



void Z3Solver::to_smt(OutStream & os,
		const BF & exprForm, BFVector & dataVector) const
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( exprForm ) << "expression !!!"
			<< SEND_EXIT;

	os << TAB;

	switch( exprForm.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode * aCode = exprForm.to_ptr< AvmCode >();

			os << '(';
			std::string eoe = "";

			switch( aCode->getAvmOpCode() )
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

				default:
				{
					os << aCode->getOperator()->strSMT();
					break;

				}
			}

			AvmCode::iterator it = aCode->begin();
			AvmCode::iterator endIt = aCode->end();
			for( ; it != endIt ; ++it )
			{
				os << " ";
				to_smt(os, *it, dataVector);
			}

			os << eoe << ')';

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			dataVector.add_union( exprForm );
			os << exprForm.to_ptr< InstanceOfData >()->getFullyQualifiedNameID();

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
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected BASEFORM KIND as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			os << exprForm.str();

			break;
		}
	}

	os << EOL;
}


#else /* NOT _AVM_SOLVER_Z3_CPP_ ==> _AVM_SOLVER_Z3_C << default >> */

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



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
static void display_function_interpretations(
		OutStream & os, Z3_context ctx, Z3_model model)
{
	unsigned num_functions, i;

	os << "function interpretations:" << std::endl;

	num_functions = Z3_get_model_num_funcs(ctx, model);
	for (i = 0; i < num_functions; i++) {
		Z3_func_decl fdecl;
		Z3_symbol name;
		Z3_ast func_else;
		unsigned num_entries, j;

		fdecl = Z3_get_model_func_decl(ctx, model, i);
		name = Z3_get_decl_name(ctx, fdecl);
		display_symbol(os, ctx, name);
		os << " = {";
		num_entries = Z3_get_model_func_num_entries(ctx, model, i);
		for (j = 0; j < num_entries; j++) {
			unsigned num_args, k;
			if (j > 0) {
				os << ", ";
			}
			num_args = Z3_get_model_func_entry_num_args(ctx, model, i, j);
			os << "(";
			for (k = 0; k < num_args; k++) {
				if (k > 0) {
					os << ", ";
				}
				display_ast(os, ctx, Z3_get_model_func_entry_arg(ctx, model, i, j, k));
			}
			os << "|->";
			display_ast(os, ctx, Z3_get_model_func_entry_value(ctx, model, i, j));
			os << ")";
		}
		if (num_entries > 0) {
			os << ", ";
		}
		os << "(else|->";
		func_else = Z3_get_model_func_else(ctx, model, i);
		display_ast(os, ctx, func_else);
		os << ")}" << std::endl;
	}
}

/**
   \brief Custom model pretty printer.
 */
static void display_model(OutStream & os, Z3_context ctx, Z3_model model)
{
	unsigned num_constants;
	unsigned i;

	num_constants = Z3_get_model_num_constants(ctx, model);
	for (i = 0; i < num_constants; i++) {
		Z3_symbol name;
		Z3_func_decl cnst = Z3_get_model_constant(ctx, model, i);
		Z3_ast a, v;
		name = Z3_get_decl_name(ctx, cnst);
		display_symbol(os, ctx, name);
		os << " = ";
		a = Z3_mk_app(ctx, cnst, 0, 0);
		v = a;
		Z3_bool ok = Z3_eval(ctx, model, a, &v);
		if( ok == Z3_TRUE )
		{
			display_ast(os, ctx, v);
			os << std::endl;
		}
	}
	display_function_interpretations(os, ctx, model);
}





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



/**
 * CONFIGURE
 */
bool Z3Solver::configure(
		Configuration & aConfiguration, WObject * wfFilterObject,
		ListOfPairMachineData & listOfSelectedVariable)
{
	if( not base_this_type::configure(
		aConfiguration, wfFilterObject, listOfSelectedVariable) )
	{
		return( false );
	}

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
	CFG = Z3_mk_config();

	Z3_set_param_value(CFG, "MODEL", "true");

	CTX = Z3_mk_context(CFG);

//	Z3_set_error_handler(error_handler);


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	++SOLVER_SESSION_ID;
AVM_IF_DEBUG_LEVEL_GTE_HIGH
	mLogFolderLocation = OSS() << VFS::ProjectLogPath << "/z3/";

	if ( not VFS::checkWritingFolder(mLogFolderLocation) )
	{
		AVM_OS_LOG << " Z3Solver::createChecker :> Error: The folder "
				<< "`" << mLogFolderLocation	<< "' "
				<< "---> doesn't exist or is not writable !!!"
				<< std::endl << std::endl;
		return( false );
	}

//	std::string fileLocation = OSS << mLogFolderLocation
//			<< "z3_log_" << SOLVER_SESSION_ID << ".z3";
//	Z3_open_log( fileLocation.c_str() );
//
//	fileLocation = OSS << mLogFolderLocation
//			<< "z3_trace_" << SOLVER_SESSION_ID << ".z3";
//	Z3_trace_to_file( CTX , fileLocation.c_str() );
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )


	SMT_TYPE_BOOL = Z3_mk_bool_sort(CTX);
	SMT_TYPE_INT  = Z3_mk_int_sort(CTX);
	SMT_TYPE_REAL = Z3_mk_real_sort(CTX);

	SMT_CST_BOOL_TRUE  = Z3_mk_true(CTX);
	SMT_CST_BOOL_FALSE = Z3_mk_false(CTX);

	SMT_CST_INT_ZERO = Z3_mk_int(CTX, 0, SMT_TYPE_INT);
	SMT_CST_INT_ONE  = Z3_mk_int(CTX, 1, SMT_TYPE_INT);

	resetTable();

	return( true );
}


bool Z3Solver::destroyChecker()
{
	resetTable();

	SMT_TYPE_BOOL  = NULL;
	SMT_TYPE_INT   = NULL;
	SMT_TYPE_BV32  = NULL;
	SMT_TYPE_BV64  = NULL;
	SMT_TYPE_REAL  = NULL;

	SMT_CST_BOOL_TRUE   = NULL;
	SMT_CST_BOOL_FALSE  = NULL;

	SMT_CST_INT_ZERO	= NULL;
	SMT_CST_INT_ONE	 = NULL;

//	Z3_close_log();
//	Z3_trace_off( CTX );

	if( CFG != NULL )
	{
		Z3_del_config(CFG);
		CFG = NULL;
	}

	if( CTX != NULL )
	{
		Z3_del_context(CTX);

		CTX = NULL;
	}

	return( true );
}

bool Z3Solver::resetTable()
{
	base_this_type::resetTable();

	mTableOfParameterDecl.append( NULL );

	mTableOfParameterExpr.append( NULL );

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
	AVM_OS_TRACE << "Z3Solver::isSatisfiable(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		smt_check_sat(aCondition);
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	Z3_ast z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">"
			<< std::endl;
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "\t";
		display_ast(AVM_OS_TRACE, CTX, z3Condition);
		AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
	AVM_OS_TRACE << "\t" << Z3_ast_to_string(CTX, z3Condition) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
	AVM_OS_TRACE << "Z3::CTX :" << SOLVER_SESSION_ID << ">" << std::endl
			<< Z3_context_to_string(CTX) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

	if( z3Condition != NULL )
	{
		Z3_assert_cnstr(CTX, z3Condition);

		switch( Z3_check(CTX) )
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
	AVM_OS_TRACE << "Z3Solver::solve(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
	smt_check_model(aCondition, dataVector, valuesVector);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	Z3_ast z3Condition = from_baseform(aCondition);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Condition :" << SOLVER_SESSION_ID << ">"
			<< std::endl;
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << "\t";
		display_ast(AVM_OS_TRACE, CTX, z3Condition);
		AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
	AVM_OS_TRACE << "\t" << Z3_ast_to_string(CTX, z3Condition) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
	AVM_OS_TRACE << "Z3::CTX :" << SOLVER_SESSION_ID << ">" << std::endl
			<< Z3_context_to_string(CTX) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

	if( z3Condition != NULL )
	{
		Z3_assert_cnstr(CTX, z3Condition);

		Z3_model model = NULL;

		switch( Z3_check_and_get_model(CTX, &model) )
		{
			case Z3_L_TRUE:
			{
				satisfiability = SolverDef::SATISFIABLE;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "Z3Model sat:" << SOLVER_SESSION_ID << ">" << std::endl
			<< Z3_model_to_string(CTX, model) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

				unsigned num_constants = Z3_get_model_num_constants(CTX, model);
				for( unsigned i = 0 ; i < num_constants ; i++ )
				{
					Z3_func_decl cnst = Z3_get_model_constant(CTX, model, i);

					Z3_symbol symbol = Z3_get_decl_name(CTX, cnst);

					int offset = mTableOfParameterDecl.find(symbol);
					if( offset >= 0 )
					{
						dataVector.append( mTableOfParameterInstance[offset] );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	display_symbol(AVM_OS_TRACE, CTX, symbol);
	AVM_OS_TRACE << " := ";
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

						Z3_ast app = Z3_mk_app(CTX, cnst, 0, 0);

						Z3_ast value = app;

						Z3_bool ok = Z3_eval(CTX, model, app, &value);

						switch( ok )
						{
							case Z3_L_TRUE:
							{
								BF bfVal = to_baseform(model, value);

								valuesVector.append( bfVal.valid() ?
										bfVal : dataVector.back() );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	display_ast(AVM_OS_TRACE, CTX, value);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
								break;
							}
							case Z3_L_FALSE:
							case Z3_L_UNDEF:
							default:
							{
								valuesVector.append( BF::REF_NULL );

								AVM_OS_FATAL_ERROR_EXIT
										<< "Z3Solver::solve :> "
											"failed to Z3_eval << "
										<< Z3_ast_to_string(CTX, app)
										<< " >> !!!"
										<< SEND_EXIT;

								break;
							}
						}
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::solve :> "
								"unfound parameter instance for Z3 symbol << "
								<< Z3_get_symbol_string(CTX, symbol)
								<< " >> !!!"
								<< SEND_EXIT;
					}
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
						<< std::endl;
				AVM_OS_TRACE << Z3_model_to_string(CTX, model) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

				break;
			}

			default:
			{
				satisfiability = SolverDef::ABORT_SAT;
				break;
			}
		}

		if( model != NULL )
		{
			Z3_del_model(CTX, model);
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

Z3_sort Z3Solver::getZ3Type(BaseTypeSpecifier * bts)
{
	if( bts->isTypedBoolean() )
	{
		return( SMT_TYPE_BOOL );
	}
	else if( bts->isTypedEnum() )
	{
		return( SMT_TYPE_INT );
		// TODO Attention : il faudrait rajouter les contraintes
		// d'intervalle pour le type énuméré
	}
	else if( bts->weaklyTypedInteger() )
	{
		return( SMT_TYPE_INT );
	}
	else if( bts->weaklyTypedReal() )
	{
		return( SMT_TYPE_REAL );
	}

	else if( bts->isTypedMachine() )
	{
		// TODO:> Consolidation après TEST
		return( SMT_TYPE_INT );
	}

	return( SMT_TYPE_REAL );
}


Z3_ast Z3Solver::getParameterExpr(const BF & bfParameter)
{
	InstanceOfData * aParameter = bfParameter.to_ptr< InstanceOfData >();

	if( aParameter->getMark() == 0 )
	{
		aParameter->setMark( mTableOfParameterInstance.size() );
		mTableOfParameterInstance.append( bfParameter );

		mTableOfParameterDecl.push_back( Z3_mk_string_symbol( CTX,
//				( OSS << "P_" << aParameter->getMark() ).c_str() ) );
				aParameter->getNameID().c_str() ) );

		mTableOfParameterExpr.push_back( Z3_mk_const( CTX,
				mTableOfParameterDecl.last(),
				getZ3Type(aParameter->referedTypeSpecifier())) );
	}

	return( mTableOfParameterExpr.at( aParameter->getMark() ) );
}




Z3_ast Z3Solver::getVariableExpr(InstanceOfData * aVar, std::size_t varID)
{
	if( mTableOfVariableExpr.size() <= varID )
	{
		mTableOfVariableDecl.push_back( Z3_mk_string_symbol( CTX,
//				( OSS << "V_" << varID ).c_str() ) );
				aVar->getNameID().c_str() ) );

		mTableOfVariableExpr.push_back( Z3_mk_const( CTX,
				mTableOfVariableDecl.last(),
				getZ3Type(aVar->getTypeSpecifier()) ) );
	}

	return( mTableOfVariableExpr.at( varID ) );
}



Z3_ast Z3Solver::safe_from_baseform(const BF & exprForm,
		BaseTypeSpecifier * typeSpecifier)
{
	Z3_ast e = NULL;

	try
	{
		if( (e = from_baseform(exprForm, typeSpecifier)) == NULL )
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



Z3_ast Z3Solver::from_baseform(const BF & exprForm,
		BaseTypeSpecifier * typeSpecifier)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( exprForm ) << "expression !!!"
			<< SEND_EXIT;

	switch( exprForm.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode * aCode = exprForm.to_ptr< AvmCode >();

			typeSpecifier = TypeManager::UNIVERSAL;

			switch( aCode->getAvmOpCode() )
			{
				// COMPARISON OPERATION
				case AVM_OPCODE_EQ:
				{
					return( Z3_mk_eq( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}

				case AVM_OPCODE_NEQ:
				{
					return( Z3_mk_not( CTX, Z3_mk_eq( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) ) );

//					ARGS arg( 2 );
//
//					arg.next( from_baseform(aCode->first() , typeSpecifier) );
//					arg.next( from_baseform(aCode->second(), typeSpecifier) );
//
//					return( Z3_mk_distinct(CTX, 2, arg->table) );
				}

				case AVM_OPCODE_LT:
				{
					return( Z3_mk_lt( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}

				case AVM_OPCODE_LTE:
				{
					return( Z3_mk_le( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}

				case AVM_OPCODE_GT:
				{
					return( Z3_mk_gt( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}

				case AVM_OPCODE_GTE:
				{
					return( Z3_mk_ge( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}


				// LOGICAL OPERATION
				case AVM_OPCODE_NOT:
				{
					return( Z3_mk_not( CTX,
							from_baseform(aCode->first() , typeSpecifier)) );
				}

				case AVM_OPCODE_AND:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_and(CTX, arg->count, arg->table) );
				}

				case AVM_OPCODE_NAND:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_not( CTX, Z3_mk_and(CTX, arg->count, arg->table) ) );
				}

//				case AVM_OPCODE_XAND:
//				{
//					ARGS arg( 2 );
//
//					arg.next( Z3_mk_not( CTX,
//							from_baseform(aCode->first() , typeSpecifier)) );
//					arg.next( from_baseform(aCode->second(), typeSpecifier) );
//
//					return( Z3_mk_and(CTX, arg->table, 2) );
//
//					return( mVC->orExpr(
//							mVC->andExpr(from_baseform(aCode->first(), typeSpecifier),
//									from_baseform(aCode->second(), typeSpecifier)),
//							mVC->andExpr(mVC->notExpr(from_baseform(aCode->first(), typeSpecifier)),
//									mVC->notExpr(from_baseform(aCode->second(), typeSpecifier))) ) );
//				}


				case AVM_OPCODE_OR:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_or(CTX, arg->count, arg->table) );
				}

				case AVM_OPCODE_NOR:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_not( CTX, Z3_mk_or(CTX, arg->count, arg->table) ) );
				}

//				case AVM_OPCODE_BAND:
//				{
//					return( Z3_mk_bv_and( CTX,
//							from_baseform(aCode->first(), typeSpecifier),
//							from_baseform(aCode->second(), typeSpecifier) ) );
//				}
//
//				case AVM_OPCODE_BOR:
//				{
//					return( Z3_mk_bv_or( CTX,
//							from_baseform(aCode->first(), typeSpecifier),
//							from_baseform(aCode->second(), typeSpecifier) ) );
//				}
//
//				case AVM_OPCODE_LSHIFT:
//				{
//					if( aCode->second().isInteger() )
//					{
//						return( Z3_mk_bv_shift_left0( CTX,
//								from_baseform(aCode->first(), typeSpecifier),
//								aCode->second().toInteger()) );
//
//					}
//					else
//					{
//						AVM_OS_FATAL_ERROR_EXIT
//								<< "Unexpected second argument for "
//									"newFixedLeftShiftExpr !!!\n"
//								<< aCode->toString( AVM_TAB1_INDENT )
//								<< SEND_EXIT;
//
//						return( NULL );
//					}
//				}
//
//				case AVM_OPCODE_RSHIFT:
//				{
//					if( aCode->second().isInteger() )
//					{
//						return( Z3_mk_bv_shift_right0( CTX,
//								from_baseform(aCode->first(), typeSpecifier),
//								aCode->second().toInteger()) );
//
//					}
//					else
//					{
//						AVM_OS_FATAL_ERROR_EXIT
//								<< "Unexpected second argument for "
//									"newFixedRightShiftExpr !!!\n"
//								<< aCode->toString( AVM_TAB1_INDENT )
//								<< SEND_EXIT;
//
//						return( NULL );
//					}
//				}

				case AVM_OPCODE_XOR:
				{
					return( Z3_mk_xor( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}

				case AVM_OPCODE_XNOR:
				{
					return( Z3_mk_not( CTX, Z3_mk_xor( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) ) );
				}


				// ARITHMETIC OPERATION
				case AVM_OPCODE_PLUS:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_add(CTX, arg->count, arg->table) );
				}

				case AVM_OPCODE_UMINUS:
				{
					return( Z3_mk_unary_minus(CTX,
							from_baseform(aCode->first(), typeSpecifier)) );
				}

				case AVM_OPCODE_MINUS:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_sub(CTX, arg->count, arg->table) );
				}

				case AVM_OPCODE_MULT:
				{
					ARGS arg( aCode->size() );

					AvmCode::iterator it = aCode->begin();
					for( ; arg.hasNext() ; ++it )
					{
						arg.next( from_baseform(*it, typeSpecifier) );
					}

					return( Z3_mk_mul(CTX, arg->count, arg->table) );
				}

				case AVM_OPCODE_DIV:
				{
					return( Z3_mk_div( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}

				case AVM_OPCODE_POW:
				{
					if( ExpressionFactory::isPosInteger(aCode->second()) )
					{
//						return( Z3_mk_power( CTX,
//								from_baseform(aCode->first() , typeSpecifier),
//								from_baseform(aCode->second(), typeSpecifier) ) );

						avm_uinteger_t power =
								ExpressionFactory::toUInteger(aCode->second());

						ARGS arg( power );

						arg.next( from_baseform(aCode->first()) );

						while( arg.hasNext() )
						{
							arg.next( arg[ 0 ] );
						}

						return( Z3_mk_mul(CTX, arg->count, arg->table) );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Z3Solver::from_baseform:> Unsupported "
								"expression Operator << AVM_OPCODE_POW >> !!!"
								<< SEND_EXIT;

						return( NULL );
					}
				}

				case AVM_OPCODE_MOD:
				{
					return( Z3_mk_mod( CTX,
							from_baseform(aCode->first() , typeSpecifier),
							from_baseform(aCode->second(), typeSpecifier) ) );
				}


				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Z3Solver::from_baseform:> Unexpected "
								"BASEFORM KIND for execution !!!\n"
							<< aCode->toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return( NULL );
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
			if( exprForm.to_ptr< Boolean >()->getValue() )
			{
				return( ((typeSpecifier != NULL) && typeSpecifier->isTypedBoolean()) ?
						SMT_CST_BOOL_TRUE : SMT_CST_INT_ONE );
			}
			else
			{
				return( ((typeSpecifier != NULL) && typeSpecifier->isTypedBoolean()) ?
						SMT_CST_BOOL_FALSE : SMT_CST_INT_ZERO );
			}
		}


		case FORM_BUILTIN_INTEGER_KIND:
		{
			if( (typeSpecifier != NULL) && typeSpecifier->isTypedBoolean() )
			{
				return( exprForm.to_ptr< Integer >()->isZero() ?
						SMT_CST_BOOL_FALSE : SMT_CST_BOOL_TRUE );
			}
			else
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

				return( Z3_mk_int64(CTX,
						exprForm.to_ptr< Integer >()->toInteger(),
						SMT_TYPE_INT) );

#else

				return( Z3_mk_int64(CTX,
						exprForm.to_ptr< Integer >()->toInteger(),
						SMT_TYPE_INT) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}

//			return( Z3_mk_numeral(CTX,
//					exprForm.to_ptr< Integer >()->str().c_str(),
//					SMT_TYPE_INT) );
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			if( (typeSpecifier != NULL) && typeSpecifier->isTypedBoolean() )
			{
				return( exprForm.to_ptr< Rational >()->isZero() ?
						SMT_CST_BOOL_FALSE : SMT_CST_BOOL_TRUE );
			}
			else
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

				return( Z3_mk_real(CTX,
						exprForm.to_ptr< Rational >()->toNumerator(),
						exprForm.to_ptr< Rational >()->toDenominator() ) );

#else

				return( Z3_mk_real(CTX,
						exprForm.to_ptr< Rational >()->toNumerator(),
						exprForm.to_ptr< Rational >()->toDenominator() ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}

//			return( Z3_mk_numeral( CTX,
//					exprForm.to_ptr< Rational >()->str().c_str(),
//					SMT_TYPE_REAL) );
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			if( (typeSpecifier != NULL) && typeSpecifier->isTypedBoolean() )
			{
				return( exprForm.to_ptr< Float >()->isZero() ?
						SMT_CST_BOOL_FALSE : SMT_CST_BOOL_TRUE );
			}
			else
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

				return( Z3_mk_numeral(CTX,
						exprForm.to_ptr< Float >()->str().c_str(),
						SMT_TYPE_REAL) );

#else

				return( Z3_mk_numeral(CTX,
						exprForm.to_ptr< Float >()->str().c_str(),
						SMT_TYPE_REAL) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}
		}


		case FORM_RUNTIME_ID_KIND:
		{
			return( Z3_mk_int(CTX, exprForm.bfRID().getRid(), SMT_TYPE_INT) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Z3Solver::from_baseform:> Unexpected BASEFORM KIND << "
					<< exprForm.classKindName() << " >> as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			return( NULL );
		}
	}

	AVM_OS_FATAL_ERROR_EXIT
			<< "Z3Solver::from_baseform ERROR !!!"
			<< SEND_EXIT;

	return( NULL );
}


BF Z3Solver::to_baseform(Z3_model model, Z3_ast z3Form)
{
	switch( Z3_get_ast_kind(CTX, z3Form) )
	{
		case Z3_NUMERAL_AST:
		{
			Z3_sort type = Z3_get_sort(CTX, z3Form);

			switch( Z3_get_sort_kind(CTX, type) )
			{
				case Z3_BOOL_SORT:
				{
					switch( Z3_get_bool_value(CTX, z3Form) )
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
									Z3_get_numeral_string(CTX, z3Form)) );
						}
					}
				}
				case Z3_INT_SORT:
				{
					{
						int val;
						if( Z3_get_numeral_int(CTX, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newInteger(
									static_cast< avm_integer_t >( val ) ) );
						}
					}
					{
						unsigned val;
						if( Z3_get_numeral_uint(CTX, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newUInteger(
									static_cast< avm_uinteger_t >( val ) ) );
						}
					}
					{
						__int64 val;
						if( Z3_get_numeral_int64(CTX, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newInteger(
									static_cast< avm_integer_t >( val ) ) );
						}
					}
					{
						unsigned __int64 val;
						if( Z3_get_numeral_uint64(CTX, z3Form, &val) == Z3_L_TRUE )
						{
							return( ExpressionConstructor::newUInteger(
									static_cast< avm_uinteger_t >( val ) ) );
						}
					}

					return( ExpressionConstructor::newInteger(
							Z3_get_numeral_string(CTX, z3Form)) );
				}
				case Z3_REAL_SORT:
				{
					__int64 num;
					__int64 den;
					if( Z3_get_numeral_rational_int64(CTX, z3Form, &num, &den) == Z3_L_TRUE )
					{
						return( ExpressionConstructor::newRational(
								static_cast< avm_integer_t >( num ),
								static_cast< avm_integer_t >( den ) ) );
					}

					return( ExpressionConstructor::newFloat(
							Z3_get_numeral_string(CTX, z3Form)) );
				}
				case Z3_UNINTERPRETED_SORT:
				case Z3_BV_SORT:
				case Z3_ARRAY_SORT:
				case Z3_DATATYPE_SORT:
				default:
				{
					return( ExpressionConstructor::newString(
							Z3_get_numeral_string(CTX, z3Form)) );

					break;
				}
			}

			break;
		}
		case Z3_APP_AST:
		{
			Z3_app app = Z3_to_app(CTX, z3Form);

			if( Z3_get_app_num_args(CTX, app) == 0 )
			{
				Z3_func_decl func_decl = Z3_get_app_decl(CTX, app);

				std::string val = Z3_func_decl_to_string(CTX, func_decl);
				if( val == "(define true bool)" )
				{
					return( ExpressionConstructor::newBoolean( true ) );
				}
				else if( val == "(define false bool)" )
				{
					return( ExpressionConstructor::newBoolean( false ) );
				}

//				z3Form = Z3_model_get_const_interp(CTX, model, func_decl);
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

	BFVector paramVector;

	StringOutStream ossCondition("", "\t", "");
	to_smt(ossCondition, aCondition, paramVector);

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "z3_check_sat_"  << SOLVER_SESSION_ID  << ".smt";
	std::ofstream osFile;
	osFile.open(fileLocation.c_str(), std::ios_base::out);
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
			else if( aParam->weaklyTypedInteger() || aParam->isTypedEnum() )
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

		osFile << "(assert " << ossCondition.str() << ")" << std::endl;

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

	std::string fileLocation = OSS() << mLogFolderLocation
			<< "z3_check_sat_" << SOLVER_SESSION_ID << ".smt";
	std::ofstream osFile;
	osFile.open(fileLocation.c_str(), std::ios_base::out);
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
			else if( aParam->weaklyTypedInteger() || aParam->isTypedEnum() )
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

		osFile << "(assert " << ossCondition.str() << ")" << std::endl;

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



void Z3Solver::to_smt(OutStream & os,
		const BF & exprForm, BFVector & dataVector) const
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( exprForm ) << "expression !!!"
			<< SEND_EXIT;

	os << TAB;

	switch( exprForm.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode * aCode = exprForm.to_ptr< AvmCode >();

			os << '(';
			std::string eoe = "";

			switch( aCode->getAvmOpCode() )
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

				default:
				{
					os << aCode->getOperator()->strSMT();
					break;

				}
			}

			AvmCode::iterator it = aCode->begin();
			AvmCode::iterator endIt = aCode->end();
			for( ; it != endIt ; ++it )
			{
				os << " ";
				to_smt(os, *it, dataVector);
			}

			os << eoe << ')';

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			dataVector.add_union( exprForm );
			os << exprForm.to_ptr< InstanceOfData >()->getFullyQualifiedNameID();

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
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected BASEFORM KIND as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			os << exprForm.str();

			break;
		}
	}

	os << EOL;
}

#endif /* _AVM_SOLVER_Z3_CPP_ */

} /* namespace sep */


#endif /* _AVM_SOLVER_Z3_ */

