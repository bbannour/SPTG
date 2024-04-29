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

#include "CVC5Solver.h"

/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_CVC5_ )


#include <util/avm_vfs.h>

#include <fml/expression/AvmCode.h>
#include <fml/builtin/Boolean.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/builtin/Character.h>
#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/numeric/Float.h>
#include <fml/builtin/Identifier.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>
#include <fml/builtin/String.h>

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


/*
 *******************************************************************************
 * ID
 *******************************************************************************
 */
std::string CVC5Solver::ID = "CVC5";

std::string CVC5Solver::DESCRIPTION = "CVC5 "
		"'Cooperating Validity Checker 5, Efficient Automatic Theorem Prover "
		"for Satisfiability Modulo Theories problems, BSD License'";

std::uint64_t CVC5Solver::SOLVER_SESSION_ID = 1;


//For automatic destroy of these CVC5 object using assignment
cvc5::Term CVC5Solver::CVC5_EXPR_NULL;
cvc5::Sort CVC5Solver::CVC5_TYPE_NULL;


/**
 * CONSTRUCTOR
 * Default
 */
CVC5Solver::CVC5Solver(bool produce_models_flag)
: base_this_type(CVC5_TYPE_NULL, CVC5_EXPR_NULL),
mParamPrefix( "P_" ),
mSmtEngine( )
{
	mLogFolderLocation = VFS::ProjectDebugPath + "/cvc5/";

	SMT_TYPE_BOOL      = mSmtEngine.getBooleanSort();

	SMT_TYPE_ENUM      = mSmtEngine.getIntegerSort();

	SMT_TYPE_UINTEGER  = mSmtEngine.getIntegerSort();
	SMT_TYPE_INTEGER   = mSmtEngine.getIntegerSort();

	SMT_TYPE_BV32      = mSmtEngine.mkBitVectorSort(32);
	SMT_TYPE_BV64      = mSmtEngine.mkBitVectorSort(64);

	SMT_TYPE_URATIONAL = mSmtEngine.getRealSort();
	SMT_TYPE_RATIONAL  = mSmtEngine.getRealSort();

	SMT_TYPE_UREAL     = mSmtEngine.getRealSort();
	SMT_TYPE_REAL      = mSmtEngine.getRealSort();

	SMT_TYPE_NUMBER    = mSmtEngine.getRealSort();

	SMT_TYPE_STRING    = mSmtEngine.getStringSort();

	SMT_CST_BOOL_TRUE  = mSmtEngine.mkBoolean(true);
	SMT_CST_BOOL_FALSE = mSmtEngine.mkBoolean(false);

	SMT_CST_INT_ZERO   = mSmtEngine.mkInteger(0);
	SMT_CST_INT_ONE    = mSmtEngine.mkInteger(1);

//	// Set the logic : LINEAR ARITHMETIC
//	mSmtEngine.setLogic("QF_LIRA");
//	// Set the logic : BIT VECTOR
//	mSmtEngine.setLogic("QF_BV");

	// Produce Models
	mSmtEngine.setOption("produce-models", (produce_models_flag ? "true" : "false"));

	// Enable Multiple Queries
	mSmtEngine.setOption("incremental", "true");
	//Disable dagifying the output
	mSmtEngine.setOption("default-dag-thresh", 0);
	// Set the output-language to CVC's
	mSmtEngine.setOption("output-language", "cvc5");
}


/**
 * DESTRUCTOR
 */
CVC5Solver::~CVC5Solver()
{
	SMT_TYPE_BOOL      = CVC5_TYPE_NULL;

	SMT_TYPE_ENUM      = CVC5_TYPE_NULL;

	SMT_TYPE_UINTEGER  = CVC5_TYPE_NULL;
	SMT_TYPE_INTEGER   = CVC5_TYPE_NULL;

	SMT_TYPE_BV32      = CVC5_TYPE_NULL;
	SMT_TYPE_BV64      = CVC5_TYPE_NULL;

	SMT_TYPE_URATIONAL = CVC5_TYPE_NULL;
	SMT_TYPE_RATIONAL  = CVC5_TYPE_NULL;

	SMT_TYPE_UREAL     = CVC5_TYPE_NULL;
	SMT_TYPE_REAL      = CVC5_TYPE_NULL;

	SMT_TYPE_NUMBER    = CVC5_TYPE_NULL;

	SMT_TYPE_STRING    = CVC5_TYPE_NULL;

	SMT_CST_BOOL_TRUE  = CVC5_EXPR_NULL;
	SMT_CST_BOOL_FALSE = CVC5_EXPR_NULL;

	SMT_CST_INT_ZERO   = CVC5_EXPR_NULL;
	SMT_CST_INT_ONE    = CVC5_EXPR_NULL;
}


/**
 * CONFIGURE
 */
bool CVC5Solver::configure(const WObject * wfFilterObject)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	std::string logFolderLocation = VFS::ProjectDebugPath + "/cvc5/";

	if ( not VFS::checkWritingFolder(logFolderLocation, true) )
	{
		AVM_OS_LOG << " CVC5Solver::createChecker :> Error: The folder "
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

bool CVC5Solver::createChecker()
{
//	// Set the logic : LINEAR ARITHMETIC
//	mSmtEngine.setLogic("QF_LIRA");
//	// Set the logic : BIT VECTOR
//	mSmtEngine.setLogic("QF_BV");

//	// Produce Models
//	mSmtEngine.setOption("produce-models", false);
//
//	// Enable Multiple Queries
//	mSmtEngine.setOption("incremental", true);
//	//Disable dagifying the output
//	mSmtEngine.setOption("default-dag-thresh", 0);
//	// Set the output-language to CVC's
//	mSmtEngine.setOption("output-language", "cvc5");


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

		std::string logFileLocation = ( OSS() << mLogFolderLocation
				<< "log_" << SOLVER_SESSION_ID << ".cvc5" );

		mSmtEngine.setOption("dump-to", logFileLocation);

		mSmtEngine.setOption("dump", "raw-benchmark");

//		mSmtEngine.setOption("dump", "declarations");
//		mSmtEngine.setOption("dump", "assertions");

		mSmtEngine.setOption("output-lang", "smt2.6.1");

AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


//	SMT_TYPE_BOOL      = mSmtEngine.getBooleanSort();
//
//	SMT_TYPE_ENUM      = mSmtEngine.getIntegerSort();
//
//	SMT_TYPE_UINTEGER  = mSmtEngine.getIntegerSort();
//	SMT_TYPE_INTEGER   = mSmtEngine.getIntegerSort();
//
//	SMT_TYPE_BV32      = mSmtEngine.mkBitVectorSort(32);
//	SMT_TYPE_BV64      = mSmtEngine.mkBitVectorSort(64);
//
//	SMT_TYPE_URATIONAL = mSmtEngine.getRealSort();
//	SMT_TYPE_RATIONAL  = mSmtEngine.getRealSort();
//
//	SMT_TYPE_UREAL     = mSmtEngine.getRealSort();
//	SMT_TYPE_REAL      = mSmtEngine.getRealSort();
//
//	SMT_TYPE_NUMBER    = mSmtEngine.getRealSort();
//
//	SMT_TYPE_STRING    = mSmtEngine.getStringSort();
//
//	SMT_CST_BOOL_TRUE  = mSmtEngine.mkBoolean(true);
//	SMT_CST_BOOL_FALSE = mSmtEngine.mkBoolean(false);
//
//	SMT_CST_INT_ZERO   = mSmtEngine.mkInteger(0);
//	SMT_CST_INT_ONE    = mSmtEngine.mkInteger(1);

	resetTable();

	return( true );
}

bool CVC5Solver::destroyChecker()
{
	resetTable();

//	SMT_TYPE_BOOL      = CVC5_TYPE_NULL;
//
//	SMT_TYPE_ENUM      = CVC5_TYPE_NULL;
//
//	SMT_TYPE_UINTEGER  = CVC5_TYPE_NULL;
//	SMT_TYPE_INTEGER   = CVC5_TYPE_NULL;
//
//	SMT_TYPE_BV32      = CVC5_TYPE_NULL;
//	SMT_TYPE_BV64      = CVC5_TYPE_NULL;
//
//	SMT_TYPE_URATIONAL = CVC5_TYPE_NULL;
//	SMT_TYPE_RATIONAL  = CVC5_TYPE_NULL;
//
//	SMT_TYPE_UREAL     = CVC5_TYPE_NULL;
//	SMT_TYPE_REAL      = CVC5_TYPE_NULL;
//
//	SMT_TYPE_NUMBER    = CVC5_TYPE_NULL;
//
//	SMT_TYPE_STRING    = CVC5_TYPE_NULL;
//
//	SMT_CST_BOOL_TRUE  = CVC5_EXPR_NULL;
//	SMT_CST_BOOL_FALSE = CVC5_EXPR_NULL;
//
//	SMT_CST_INT_ZERO   = CVC5_EXPR_NULL;
//	SMT_CST_INT_ONE    = CVC5_EXPR_NULL;
//

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	++SOLVER_SESSION_ID;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( true );
}

bool CVC5Solver::resetTable()
{
	base_this_type::resetTable();

	mTableOfParameterExpr.push_back( CVC5_EXPR_NULL );

	mBitsetOfConstrainedParameter.push_back( false );
	mBitsetOfPositiveParameter.push_back( false );
	mBitsetOfStrictlyPositiveParameter.push_back( false );

	return( true );
}


/**
 * PROVER
 */
//bool CVC5Solver::isSubSet(
//		const ExecutionContext & newEC, const ExecutionContext & oldEC)
//{
//	try
//	{
//		createChecker();
//
//		cvc5::Term newFormula;
//		cvc5::Term oldFormula;
//
//		// On construit la formule newFormula =
//		// garde_newEC AND
//		// x1 = e1 AND ---- AND xn = en
//		//
//		// et la formule oldFormula =
//		// garde_oldEC AND
//		// x1 = e'1 AND ---- AND xn = e'n AND
//		// e1 = e'1 AND ---- AND en = e'n
//		//
//		edToExprWithVarEquality(newEC.getExecutionData(), newFormula,
//				oldEC.getExecutionData(), oldFormula);
//
//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	oldEC.writeTraceBeforeExec(AVM_OS_TRACE << TAB);
//	AVM_OS_TRACE << TAB << "Expr: " << oldFormula << std::endl;
//
//	newEC.writeTraceBeforeExec(AVM_OS_TRACE << TAB);
//	AVM_OS_TRACE << TAB << "Expr: " << newFormula << std::endl;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
//
//		// ASSERT de newFormula
//		//
//		mSmtEngine.assertFormula(newFormula);
//
//		// CHECKSAT de oldFormula
//		//
//		// A la place de CHECKSAT on utilise NOT QUERY(NOT oldFormula)
//		//
//		cvc5::Result result = mSmtEngine.query( oldFormula.notExpr() );
//
//		newFormula = CVC5_EXPR_NULL;
//		oldFormula = CVC5_EXPR_NULL;
//		destroyChecker();
//
//		// Si not result alors la formule oldFormula est satisfiable
//		return( result != cvc5::Result::VALID );
//	}
//	catch( const std::exception & ex )
//	{
//		AVM_OS_TRACE << TAB << "*** Exception caught in CVC5Solver::isSubSet: \n"
//				<< ex.what() << std::endl;
//	}
//
//	return( false );
//}


//bool CVC5Solver::isSubSet(
//		const ExecutionContext & newEC, const ExecutionContext & oldEC)
//{
//	try
//	{
//		createChecker();
//
//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << std::endl << "new EC: " << newEC.getIdNumber() << std::endl
//			<< std::endl << "old EC: " << oldEC.getIdNumber() << std::endl;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
//
//		// On construit la formule newFormula :
//		// garde_newEC AND
//		// x1 = e1 AND ---- AND xn = en
//		//
//		// et la formule oldFormula :
//		// garde_oldEC AND
//		// x1 = e'1 AND ---- AND xn = e'n AND
//		// e1 = e'1 AND ---- AND en = e'n
//		//
//		cvc5::Term newFormula;
//		cvc5::Term oldFormula;
//		edToExprWithVarEquality(newEC.getExecutionData(),
//				newFormula, oldEC.getExecutionData(), oldFormula);
//
//		if( oldFormula != SMT_CST_BOOL_FALSE )
//		{
//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	oldEC.writeTraceBeforeExec(AVM_OS_TRACE << TAB);
//	AVM_OS_TRACE << TAB << "!!!!!!!!!!!!!!! old Expr: " << oldFormula << std::endl;
//
//	newEC.writeTraceBeforeExec(AVM_OS_TRACE << TAB);
//	AVM_OS_TRACE << TAB << "!!!!!!!!!!!!!!! new Expr: " << newFormula << std::endl;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
//
//			cvc5::Term implyFormula;
//			if( not mTableOfParameterExprForOldFormula.empty() )
//			{
//				// On construit la formule itexists
//				// mTableOfParameterExprForOldFormula oldFormula
//				cvc5::Term itExistsFormula = mSmtEngine.mkTerm(
//						cvc5::Kind::EXISTS,
//						mSmtEngine.mkTerm(cvc5::Kind::VARIABLE_LIST,
//								mTableOfParameterExprForOldFormula),
//						oldFormula);
//
//				// On construit la formule newFormula => itExistsFormula
//				//
//				implyFormula = mSmtEngine.mkTerm(
//						cvc5::Kind::IMPLIES, newFormula, itExistsFormula);
//			}
//			else
//			{
//				// On construit la formule newFormula => oldFormula
//				//
//				implyFormula = mSmtEngine.mkTerm(
//						cvc5::Kind::IMPLIES, newFormula, oldFormula);
//			}

//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << implyFormula;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
//
//			// On construit la formule forall
//			// mTableOfParameterExprForNewFormula implyFormula
//			Vector< cvc5::Term > forAllParameterAndVariableList;
//			forAllParameterAndVariableList.append(mTableOfVariableExpr);
//			forAllParameterAndVariableList.append(
//					mTableOfParameterExprForNewFormula);
//			cvc5::Term forAllFormula = mSmtEngine.mkTerm(cvc5::Kind::FORALL,
//					mSmtEngine.mkTerm(cvc5::Kind::VARIABLE_LIST,
//							forAllParameterAndVariableList),
//					implyFormula);
//			AVM_OS_TRACE << TAB << "--> forAllFormula : ";
//			AVM_OS_TRACE << forAllFormula;
//
//			// QUERY de forAllFormula
//			//
//			cvc5::Result result = mSmtEngine.query( forAllFormula );
//
//			newFormula = CVC5_EXPR_NULL;
//			oldFormula = CVC5_EXPR_NULL;
//			destroyChecker();
//
//			return( result == cvc5::Result::VALID );
//		}
//		else
//		{
//			AVM_OS_TRACE << TAB << "--> cas  oldFormula à false " << std::endl;
//			return( false );
//		}
//	}
//	catch( const std::exception & ex )
//	{
//		AVM_OS_TRACE << TAB << "*** Exception caught in CVC5Solver::isSubSet: \n"
//				<< ex.what() << std::endl;
//	}
//
//	return( false );
//}



bool CVC5Solver::isSubSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	try
	{
		createChecker();

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << std::endl << "new EC: " << newEC.getIdNumber() << std::endl
			<< std::endl << "old EC: " << oldEC.getIdNumber() << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

		// On construit la formule newFormula :
		// garde_newEC AND
		// x1 = e1 AND ---- AND xn = en
		//
		// la formule oldFormula :
		// garde_oldEC AND
		// x1 = e'1 AND ---- AND xn = e'n
		//
		// et la formule equFormula qui établie l'égalité des mémoires symboliques
		// e1 = e'1 AND ---- AND en = e'n
		//
		cvc5::Term newFormula;
		cvc5::Term oldFormula;
		cvc5::Term equFormula;
		edToExprWithVarEquality(newEC.getExecutionData(), newFormula,
								oldEC.getExecutionData(), oldFormula,
								equFormula);

		bool bResult = false;

		if( oldFormula != SMT_CST_BOOL_FALSE )
		{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	oldEC.traceDefault(AVM_OS_TRACE << TAB);
	AVM_OS_TRACE << TAB << "!!!!!!!!!!!!!!! old Expr: " << oldFormula << std::endl;

	newEC.traceDefault(AVM_OS_TRACE << TAB);
	AVM_OS_TRACE << TAB << "!!!!!!!!!!!!!!! new Expr: " << newFormula << std::endl;

//	newEC.writeTraceBeforeExec(AVM_OS_TRACE << TAB);
//	AVM_OS_TRACE << TAB << "!!!!!!!!!!!!!!! equ Expr: " << equFormula << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

			// Déclaration des variables de mTableOfVariableExpr et
			// et des paramètres de mTableOfParameterExpr
			//

			// ASSERT de newFormula
			//
			mSmtEngine.assertFormula(newFormula);

			// ASSERT de equFormula
			//
//			mSmtEngine.assertFormula(equFormula);

			// CHECKSAT de NOT oldFormula
			//
			// A la place on utilise NOT QUERY(oldFormula)
			//



//			cvc5::Result toto = mSmtEngine.query( oldFormula );
			cvc5::Result toto = mSmtEngine.checkSatAssuming( oldFormula );

// !!!!!!!!!!!!!!! 271009 : ESSAI AFA temporaire !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//			cvc5::Result toto = mSmtEngine.query(
//					mSmtEngine.mkTerm(cvc5::Kind::NOT, oldFormula) );
//			if(toto == cvc5::SATISFIABLE)
//			{
//				int i = 1;
//			}
//			if(toto == cvc5::INVALID)
//			{
//				int i = 2;
//			}

//			bool result = ( toto == cvc5::Result::VALID );
			bool result = toto.isSat();

			bResult = ( not result );
		}
		else
		{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "--> cas  oldFormula à false " << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
		}

		newFormula = CVC5_EXPR_NULL;
		oldFormula = CVC5_EXPR_NULL;
		equFormula = CVC5_EXPR_NULL;
		destroyChecker();

		return( bResult );
	}
	catch( const std::exception  & ex )
	{
		AVM_OS_TRACE << TAB << "*** Exception caught in CVC5Solver::isSubSet: \n"
				<< ex.what() << std::endl;

		destroyChecker();
	}

	return( false );
}


void CVC5Solver::edToExprWithVarEquality(const ExecutionData & newED,
		cvc5::Term & newFormula, const ExecutionData & oldED,
		cvc5::Term & oldFormula, cvc5::Term & equFormula)
{
//	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mSmtEngine ) << "ValidityChecker !!!"
//			<< SEND_EXIT;

	std::vector< cvc5::Term > newFormulaList;
	std::vector< cvc5::Term > oldFormulaList;
	std::vector< cvc5::Term > equFormulaList;

	resetTable();

	// compile PCs
	cvc5::Term aPC;

//	m_pTableOfParameterExpr = &mTableOfParameterExprForNewFormula;
	newFormulaList.push_back( aPC =
			safe_from_baseform(newED.getPathCondition()) );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << std::endl << "new PC: " << aPC << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

//	m_pTableOfParameterExpr = nullptr;
	oldFormulaList.push_back( aPC =
			safe_from_baseform(oldED.getPathCondition()) );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << "old PC: " << aPC << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	InstanceOfData * aVar = nullptr;

	// compile DATAs
	std::ostringstream oss;

	avm_offset_t varID = 1;
	for( const auto & itPairMachineData : getSelectedVariable() )
	{
		if( itPairMachineData.second().nonempty() )
		{
			const RuntimeForm & newRF = newED.getRuntime(
					itPairMachineData.first() );
			const RuntimeForm & oldRF = oldED.getRuntime(
					itPairMachineData.first() );

			for( const auto & itVar : itPairMachineData.second() )
			{
				//??? TABLEAUX
				aVar = newRF.rawVariable(itVar->getOffset());
				
				const BaseTypeSpecifier & varTypeSpecifier = aVar->getTypeSpecifier();

				oss.str("");
				oss << "V_" << varID;

//				m_pTableOfParameterExpr = &mTableOfParameterExprForNewFormula;
				cvc5::Term newValue = safe_from_baseform(newRF.getData(itVar));
//				m_pTableOfParameterExpr = nullptr;
				cvc5::Term oldValue = safe_from_baseform(oldRF.getData(itVar));

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << varTypeSpecifier.strT() << "  "
			<< itVar->getNameID() << " --> " << oss.str()
			<< std::endl << "\told: " << oldValue << "\tnew: " << newValue;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )


				if( varTypeSpecifier.isTypedBoolean() )
				{
					const BF & newElement = newRF.getData(itVar);
					const BF & oldElement = oldRF.getData(itVar);
					if( newElement.isBoolean() && oldElement.isBoolean() )
					{
						// On rajoute l'équivalence entre la nouvelle valeur
						// symbolique et l'ancienne
//						equFormulaList.push_back( mSmtEnginemkExpr(
//								cvc5::Kind::EQUAL, newValue, oldValue) );
						oldFormulaList.push_back(
								(newElement.toBoolean() == oldElement.toBoolean()) ?
										SMT_CST_BOOL_TRUE : SMT_CST_BOOL_FALSE );

						if( newElement.toBoolean() != oldElement.toBoolean() )
						{
							oldFormula = SMT_CST_BOOL_FALSE;
							resetTable();
							return;
						}
					}
					else
					{
						cvc5::Term varExpr =
								mSmtEngine.mkVar(SMT_TYPE_BOOL, oss.str());
						mTableOfVariableExpr.push_back( varExpr );

						newFormulaList.push_back( mSmtEngine.mkTerm(
								cvc5::Kind::EQUAL, { varExpr, newValue } ));
						oldFormulaList.push_back( mSmtEngine.mkTerm(
								cvc5::Kind::EQUAL, { varExpr, oldValue } ));
					}
				}
				else if( varTypeSpecifier.weaklyTypedInteger()
						|| varTypeSpecifier.isTypedEnum()
						|| varTypeSpecifier.isTypedMachine() )
				{
					const BF & newElement = newRF.getData(itVar);
					const BF & oldElement = oldRF.getData(itVar);
					if ( newElement.isNumeric() && oldElement.isNumeric() )
					{
						// On rajoute l'égalité entre la nouvelle valeur
						// symbolique et l'ancienne
//						equFormulaList.push_back( mSmtEngine.mkTerm(
//								cvc5::Kind::EQUAL, newValue, oldValue) );

						oldFormulaList.push_back(
								(ExpressionComparer::isEQ(newElement, oldElement)) ?
								SMT_CST_BOOL_TRUE : SMT_CST_BOOL_FALSE  );

						if( ExpressionComparer::isNEQ(newElement, oldElement) )
						{
							oldFormula = SMT_CST_BOOL_FALSE;
							resetTable();
							return;
						}
					}
					else
					{
						cvc5::Term varExpr =
								mSmtEngine.mkVar(SMT_TYPE_INTEGER, oss.str());
						mTableOfVariableExpr.push_back( varExpr );

						newFormulaList.push_back( mSmtEngine.mkTerm(
								cvc5::Kind::EQUAL, { varExpr, newValue } ));

						oldFormulaList.push_back( mSmtEngine.mkTerm(
								cvc5::Kind::EQUAL, { varExpr, oldValue } ));
					}
				}
				else if( varTypeSpecifier.weaklyTypedReal() )
				{
					const BF & newElement = newRF.getData(itVar);
					const BF & oldElement = oldRF.getData(itVar);
					if ( newElement.isNumeric() && oldElement.isNumeric() )
					{
						// On rajoute l'égalité entre la nouvelle valeur
						// symbolique et l'ancienne
//						equFormulaList.push_back( mSmtEngine.mkTerm(
//								cvc5::Kind::EQUAL, newValue, oldValue) );

						oldFormulaList.push_back(
								(ExpressionComparer::isEQ(newElement, oldElement)) ?
								SMT_CST_BOOL_TRUE : SMT_CST_BOOL_FALSE  );

						if( ExpressionComparer::isNEQ(newElement, oldElement) )
						{
							oldFormula = SMT_CST_BOOL_FALSE;
							resetTable();
							return;
						}
					}
					else
					{
						cvc5::Term varExpr =
								mSmtEngine.mkVar(SMT_TYPE_REAL, oss.str());
						mTableOfVariableExpr.push_back( varExpr );

						newFormulaList.push_back( mSmtEngine.mkTerm(
								cvc5::Kind::EQUAL, { varExpr, newValue } ));

						oldFormulaList.push_back( mSmtEngine.mkTerm(
								cvc5::Kind::EQUAL, { varExpr, oldValue } ));
					}
				}
				else
				{
					AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
							<< aVar->getFullyQualifiedNameID() << " as : " << oss.str() << " : "
							<< varTypeSpecifier.getFullyQualifiedNameID() << ">> !!!"
							<< SEND_ALERT;

					cvc5::Term varExpr =
							mSmtEngine.mkVar(SMT_TYPE_REAL, oss.str());
					mTableOfVariableExpr.push_back( varExpr );

					newFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, newValue } ));

					oldFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, oldValue } ));
				}
			}
		}
	}

	for( const auto & itParam : mTableOfParameterExpr )
	{
		if( not mTableOfParameterExprForNewFormula.contains( itParam ) )
		{
			mTableOfParameterExprForOldFormula.append( itParam );
		}
	}

//	oldFormula = mSmtEngine.simplify(
//			mSmtEngine.mkTerm(cvc5::Kind::AND, oldFormulaList) );
//
//	newFormula = mSmtEngine.simplify(
//			mSmtEngine.mkTerm(cvc5::Kind::AND, newFormulaList) );

// Temporaire pour trace : remplacer ensuite par les 2 égalités précédentes
	cvc5::Term oldFormulAvantSimplfy =
			mSmtEngine.mkTerm(cvc5::Kind::AND, oldFormulaList);

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << std::endl << "oldFormula avant simplify : "
			<< oldFormulAvantSimplfy << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	oldFormula = mSmtEngine.simplify( oldFormulAvantSimplfy );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << "oldFormula après simplify : "
			<< oldFormula << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )


	cvc5::Term newFormulAvantSimplfy =
			mSmtEngine.mkTerm(cvc5::Kind::AND, newFormulaList);

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << std::endl << "newFormula avant simplify : "
			<< newFormulAvantSimplfy << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	newFormula = mSmtEngine.simplify( newFormulAvantSimplfy );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << "newFormula après simplify : "
			<< newFormula << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

//	cvc5::Term equFormulAvantSimplfy = mSmtEngine.mkTerm(cvc5::Kind::AND, equFormulaList);
//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << std::endl << "equFormula avant simplify : ";
//			<< equFormulAvantSimplfy << std::endl;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
//	equFormula = mSmtEngine.simplify( equFormulAvantSimplfy );

	resetTable();
}



bool CVC5Solver::isEqualSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	try
	{
		createChecker();

		cvc5::Term newFormula;
		cvc5::Term oldFormula;

		edToExpr(newEC.getExecutionData(), newFormula,
				oldEC.getExecutionData(), oldFormula);

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	oldEC.traceDefault(AVM_OS_TRACE << TAB);
	AVM_OS_TRACE << TAB << "Expr: " << oldFormula << std::endl;

	newEC.traceDefault(AVM_OS_TRACE << TAB);
	AVM_OS_TRACE << TAB << "Expr: " << newFormula << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

//		cvc5::Term equalTest = mSmtEngine.mkTerm(cvc5::Kind::FORALL,
//			mSmtEngine.mkTerm(cvc5::Kind::VARIABLE_LIST, mTableOfVariableExpr),
//			mSmtEngine.mkTerm(cvc5::Kind::EXISTS,
//				mSmtEngine.mkTerm(cvc5::Kind::VARIABLE_LIST, mTableOfParameterExpr),
//				mSmtEngine.mkTerm(cvc5::Kind::EQUAL, { oldFormula, newFormula } )));
//
//		cvc5::Term equalTest = mSmtEngine.mkTerm(cvc5::Kind::EXISTS,
//				mTableOfParameterExpr,
//				mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
//						{ oldFormula, newFormula } ));

		cvc5::Term equalTest = mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
				{ oldFormula, newFormula } );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "isSubSet Expr: " << equalTest << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

//		cvc5::Result result = mSmtEngine.query(equalTest);
		cvc5::Result result = mSmtEngine.checkSatAssuming(equalTest);

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "\nisEqual result : "
			<< TAB << (result.isSat() ? "true" : "false")
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

		newFormula = CVC5_EXPR_NULL;
		oldFormula = CVC5_EXPR_NULL;
		destroyChecker();

		return( result.isSat() );
	}
	catch( const std::exception & ex )
	{
		AVM_OS_TRACE << TAB << "*** Exception caught in CVC5Solver::isEqualSet: \n"
				<< ex.what() << std::endl;

		destroyChecker();
	}

	return( false );
}


SolverDef::SATISFIABILITY_RING CVC5Solver::isSatisfiable(const BF & aCondition)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "CVC5Solver::isSatisfiable(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
//	smt_check_sat(aCondition);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	if( aCondition.isBoolean() )
	{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "is satisfiable : " << aCondition.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

		return( aCondition.toBoolean() ?
				SolverDef::SATISFIABLE : SolverDef::UNSATISFIABLE );
	}

	else if( aCondition.isFloat() )
	{
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "is satisfiable : " << aCondition.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

		return( ( aCondition.toFloat() != 0 ) ?
				SolverDef::SATISFIABLE : SolverDef::UNSATISFIABLE );
	}

	try
	{
		createChecker();

		// compile Formula
		cvc5::Term aFormula = safe_from_baseform( aCondition );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "CVC5Condition :" << SOLVER_SESSION_ID << ">" << std::endl;

	dbg_smt(aFormula);

	AVM_OS_TRACE << "\t" << aFormula << std::endl;

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

//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )	// trace to file
//	AVM_OS_TRACE << "z3::solver::to_smt2(...)" << std::endl
//			<< z3Solver.to_smt2() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


		// ATTENTION : lorsque CVC5 répond UNKNOWN,
		// on considère que la garde est SATISFIABLE
		SolverDef::SATISFIABILITY_RING satisfiability = SolverDef::SATISFIABLE;

		if( mBitsetOfConstrainedParameter.allFalse()
				|| appendPossitiveAssertion() )
		{
			cvc5::Result result = mSmtEngine.checkSatAssuming( aFormula );

			if( result.isSat() )
			{
				satisfiability = SolverDef::SATISFIABLE;
			}
			else if( result.isUnsat() )
			{
				satisfiability = SolverDef::UNSATISFIABLE;
			}
			else if( result.isUnknown() )
			{
				satisfiability = SolverDef::UNKNOWN_SAT;
			}

			else //if( result.isAbort() )
			{
				satisfiability = SolverDef::ABORT_SAT;
			}
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "result :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

		aFormula = CVC5_EXPR_NULL;
		destroyChecker();

		return( satisfiability );
	}
	catch ( const std::exception & ex )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tCVC5Solver::isSatisfiable< std::exception :"
				<< SOLVER_SESSION_ID << ">\n\t" << ex.what() << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\t  " << aCondition.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();

		return( SolverDef::UNKNOWN_SAT );
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tCVC5Solver::isSatisfiable< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\t  " << aCondition.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();

		return( SolverDef::UNKNOWN_SAT );
	}

	return( SolverDef::UNKNOWN_SAT );
}



/**
 * SOLVER
 */
bool CVC5Solver::solveImpl(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "CVC5Solver::solve(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;

	// trace to file
//	smt_check_sat(aCondition);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	try
	{
		// Produce Models option --> true
		createChecker( );

		resetTable();

		// compile Formula
		cvc5::Term aFormula = safe_from_baseform( aCondition );


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "CVC5Condition :" << SOLVER_SESSION_ID << ">" << std::endl;

	dbg_smt(aFormula, true);

	AVM_OS_TRACE << "\t" << aFormula << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )


		cvc5::Result result = mSmtEngine.checkSatAssuming( aFormula );

		if( result.isSat() )
		{
//			cvc5::Model * concreteModel = mSmtEngine.getModel();

			for( std::size_t i = 1 ; i < mTableOfParameterInstance.size() ; ++i )
			{
				dataVector.append( mTableOfParameterInstance[i] );

				const cvc5::Term & var = mTableOfParameterExpr[i];
				cvc5::Term val = mSmtEngine.getValue(var);

				if( val == SMT_CST_BOOL_TRUE )
				{
					valuesVector.append( ExpressionConstant::BOOLEAN_TRUE );
				}
				else if( val == SMT_CST_BOOL_FALSE )
				{
					valuesVector.append( ExpressionConstant::BOOLEAN_FALSE );
				}
				else if( val.getKind() == cvc5::Kind::CONST_INTEGER )
				{
					valuesVector.append( ExpressionConstructor::newInteger(val.toString()) );
				}
				else if( val.getKind() == cvc5::Kind::CONST_RATIONAL )
				{
					valuesVector.append(
							ExpressionConstructor::newRational(val.toString()) );
				}
				else
				{
					valuesVector.append( dataVector.back() );
				}

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << mTableOfParameterInstance.rawAt( i )->getFullyQualifiedNameID()
			<< " --> " << var << " = " << val << std::endl;
//	AVM_OS_COUT<< mTableOfParameterInstance.rawAt( i )->getFullyQualifiedNameID()
//			<< " --> " << var << " = " << val << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
			}
		}

		aFormula = CVC5_EXPR_NULL;
		destroyChecker();

		return( result.isSat() );
	}
	catch ( const std::exception & ex )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tCVC5Solver::solve< std::exception :"
				<< SOLVER_SESSION_ID << ">\n\t" << ex.what() << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\t  " << aCondition.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();

		return( false );
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tCVC5Solver::solve< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\t  " << aCondition.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();

		return( false );
	}

	return( false );
}


/**
 * TOOLS
 */

void CVC5Solver::edToExpr(
		const ExecutionData & newED, cvc5::Term & newFormula,
		const ExecutionData & oldED, cvc5::Term & oldFormula)
{
//	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mSmtEngine ) << "ValidityChecker !!!"
//			<< SEND_EXIT;

	resetTable();

	// compile PCs
	cvc5::Term aPC;
	std::vector< cvc5::Term > newFormulaList;
	newFormulaList.push_back( aPC = safe_from_baseform(newED.getPathCondition()) );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << std::endl << "new PC: " << aPC << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	std::vector< cvc5::Term > oldFormulaList;
	oldFormulaList.push_back( aPC = safe_from_baseform(oldED.getPathCondition()) );

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << "old PC: " << aPC << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	InstanceOfData * aVar = nullptr;

	// compile DATAs
	std::ostringstream oss;

	avm_offset_t varID = 1;
	for( const auto & itPairMachineData : getSelectedVariable() )
	{
		if( itPairMachineData.second().nonempty() )
		{
			const RuntimeForm & newRF = newED.getRuntime(
					itPairMachineData.first() );
			const RuntimeForm & oldRF = oldED.getRuntime(
					itPairMachineData.first() );

			for( const auto & itVar : itPairMachineData.second() )
			{
				//??? TABLEAUX
				aVar = newRF.rawVariable(itVar->getOffset());
				
				const BaseTypeSpecifier & varTypeSpecifier = aVar->getTypeSpecifier();

				oss.str("");
				oss << "V_" << varID;

				cvc5::Term newValue = safe_from_baseform(newRF.getData(itVar));
				cvc5::Term oldValue = safe_from_baseform(oldRF.getData(itVar));

				if( varTypeSpecifier.isTypedBoolean() )
				{
					cvc5::Term varExpr =
							mSmtEngine.mkVar(SMT_TYPE_BOOL, oss.str());
					mTableOfVariableExpr.push_back( varExpr );
					newFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, newValue } ));
					oldFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL,{ varExpr, oldValue } ));
				}
				else if( varTypeSpecifier.isTypedEnum() )
				{
					cvc5::Term varExpr =
							mSmtEngine.mkVar(SMT_TYPE_ENUM, oss.str());
					mTableOfVariableExpr.push_back( varExpr );
					newFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, newValue } ));
					oldFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, oldValue } ));
				}
				else if( varTypeSpecifier.weaklyTypedInteger() )
				{
					cvc5::Term varExpr =
							mSmtEngine.mkVar(SMT_TYPE_INTEGER, oss.str());
					mTableOfVariableExpr.push_back( varExpr );
					newFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, newValue } ));
					oldFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, oldValue } ));
				}
				else if( varTypeSpecifier.weaklyTypedReal() )
				{
					cvc5::Term varExpr =
							mSmtEngine.mkVar(SMT_TYPE_REAL, oss.str());
					mTableOfVariableExpr.push_back( varExpr );
					newFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, newValue } ));
					oldFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, oldValue } ));
				}
				else
				{
					AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
							<< aVar->getFullyQualifiedNameID() << " as : " << oss.str() << " : "
							<< varTypeSpecifier.getFullyQualifiedNameID() << ">> !!!"
							<< SEND_ALERT;

					cvc5::Term varExpr = mSmtEngine.mkVar(SMT_TYPE_REAL, oss.str());
					mTableOfVariableExpr.push_back( varExpr );
					newFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, newValue } ));
					oldFormulaList.push_back( mSmtEngine.mkTerm(
							cvc5::Kind::EQUAL, { varExpr, oldValue } ));
				}
			}
		}
	}

	oldFormula = mSmtEngine.simplify(
			mSmtEngine.mkTerm(cvc5::Kind::AND, oldFormulaList) );

	newFormula = mSmtEngine.simplify(
			mSmtEngine.mkTerm(cvc5::Kind::AND, newFormulaList) );


	resetTable();
}


/*
cvc5::Term CVC5Solver::edToExpr(const ExecutionData & anED)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mSmtEngine ) << "ValidityChecker !!!"
			<< SEND_EXIT;

//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << TAB << "edToExpr ED: \n";
//	anED.toStreamData(AVM_OS_TRACE, "\t");
//	AVM_OS_TRACE << std::flush;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	resetTable();

	// compile PC
	cvc5::Term pcExpr = mSmtEngine.simplify(safe_from_baseform(anED.getPathCondition()));
AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "\nPC: " << pcExpr << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )
	mSmtEngine.assertFormula( pcExpr );

	std::vector< cvc5::Term > aFormulaList;
	InstanceOfData * aVar = nullptr;
	ListOfInstanceOfData::iterator itVar;

	// compile DATA
	for( const auto & itPairMachineData : getSelectedVariable() )
	{
		if( itPairMachineData.second().nonempty() )
		{
			itVar = itPairMachineData.begin();
			RuntimeForm * aRF = anED.get(itVar);

			for( ; itVar != itPairMachineData.end() ; ++itVar )
			{
				aVar = aRF.refExecutable().getBasicVariable(itVar->getOffset());
				
				const BaseTypeSpecifier & varTypeSpecifier = aVar->getTypeSpecifier();

				if( varTypeSpecifier.isTypedBoolean() )
				{
					aFormulaList.push_back(
							safe_from_baseform(aRF.getData(itVar)) );
				}
				else if( varTypeSpecifier.weaklyTypedInteger()
						|| varTypeSpecifier.isTypedEnum() )
				{
					aFormulaList.push_back(
							safe_from_baseform(aRF.getData(itVar)) );
				}
				else if( varTypeSpecifier.weaklyTypedReal() )
				{
					aFormulaList.push_back(
							safe_from_baseform(aRF.getData(itVar)) );
				}
				else
				{
					AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
							<< aVar->getFullyQualifiedNameID() " : "
							<< varTypeSpecifier.getFullyQualifiedNameID() << ">> !!!"
							<< SEND_ALERT;

					aFormulaList.push_back(
							safe_from_baseform(aRF.getData(itVar)) );
				}
			}
		}
	}

	cvc5::Term edExpr =  mSmtEngine.mkTerm(cvc5::Kind::TUPLE, aFormulaList);

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "Expr: ";
	AVM_OS_TRACE << edExpr << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	resetTable();

	return( edExpr );
}

*/


cvc5::Term CVC5Solver::edToExpr(const ExecutionData & anED)
{
//	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mSmtEngine ) << "ValidityChecker !!!"
//			<< SEND_EXIT;

//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << TAB << "edToExpr ED: \n";
//	anED.toStreamData(AVM_OS_TRACE, "\t");
//	AVM_OS_TRACE << std::flush;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	resetTable();

	std::vector< cvc5::Term > aFormulaList;

	// compile PC
	aFormulaList.push_back( safe_from_baseform(anED.getPathCondition()) );

	// compile DATA
	avm_offset_t varID = 0;
	for( const auto & itPairMachineData : getSelectedVariable() )
	{
		if( itPairMachineData.second().nonempty() )
		{
			const RuntimeForm & aRF = anED.getRuntime(
					itPairMachineData.first() );

			for( const auto & itVar : itPairMachineData.second() )
			{
				//??? TABLEAUX
				InstanceOfData * aVar = aRF.rawVariable(itVar->getOffset());

				const BaseTypeSpecifier & varTypeSpecifier = aVar->getTypeSpecifier();

				if( varTypeSpecifier.isTypedBoolean() )
				{
					aFormulaList.push_back( mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
							{ getVariableExpr(aVar, SMT_TYPE_BOOL, varID),
							safe_from_baseform(aRF.getData(itVar)) }) );
				}
				else if( varTypeSpecifier.isTypedEnum() )
				{
					aFormulaList.push_back( mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
							{ getVariableExpr(aVar, SMT_TYPE_ENUM, varID),
							safe_from_baseform(aRF.getData(itVar)) }) );
				}
				else if( varTypeSpecifier.weaklyTypedInteger() )
				{
					aFormulaList.push_back( mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
							{ getVariableExpr(aVar, SMT_TYPE_INTEGER, varID),
							safe_from_baseform(aRF.getData(itVar)) }) );
				}
				else if( varTypeSpecifier.weaklyTypedReal() )
				{
					aFormulaList.push_back( mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
							{ getVariableExpr(aVar, SMT_TYPE_REAL, varID),
							safe_from_baseform(aRF.getData(itVar)) }) );
				}
				else
				{
					AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
							<< aVar->getFullyQualifiedNameID() << " : "
							<< varTypeSpecifier.getFullyQualifiedNameID() << ">> !!!"
							<< SEND_ALERT;

					aFormulaList.push_back( mSmtEngine.mkTerm(cvc5::Kind::EQUAL,
							{ getVariableExpr(aVar, SMT_TYPE_REAL, varID),
							safe_from_baseform(aRF.getData(itVar)) }) );
				}
			}
		}
	}

	cvc5::Term edExpr = mSmtEngine.mkTerm(cvc5::Kind::EXISTS,
			{ mSmtEngine.mkTerm(
					cvc5::Kind::VARIABLE_LIST, mTableOfParameterExpr),
			mSmtEngine.simplify(
					mSmtEngine.mkTerm(cvc5::Kind::AND, aFormulaList)) });

AVM_IF_DEBUG_FLAG( SMT_SOLVING )
	AVM_OS_TRACE << TAB << "Expr: ";
	AVM_OS_TRACE << edExpr << std::endl;
AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

	resetTable();

	return( edExpr );
}


cvc5::Term & CVC5Solver::getParameterExpr(const BF & bfParameter)
{
	InstanceOfData & aParameter = const_cast< InstanceOfData & >(
			bfParameter.to< InstanceOfData >() );

	if( aParameter.getMark() == 0 )
	{
		const BaseTypeSpecifier & paramTypeSpecifier =
				aParameter.referedTypeSpecifier();

		cvc5::Sort paramType;

		if( paramTypeSpecifier.isTypedBoolean() )
		{
			paramType = SMT_TYPE_BOOL;
		}
		else if( paramTypeSpecifier.weaklyTypedUInteger() )
		{
			if( SolverDef::DEFAULT_SOLVER_KIND ==
					SolverDef::SOLVER_CVC5_BV32_KIND )
			{
				paramType = SMT_TYPE_BV32;
			}
			else
//			if( SolverDef::DEFAULT_SOLVER_KIND == SolverDef::SOLVER_CVC5_KIND )
			{
				paramType = SMT_TYPE_UINTEGER;
			}
		}
		else if( paramTypeSpecifier.weaklyTypedInteger() )
		{
			if( SolverDef::DEFAULT_SOLVER_KIND ==
					SolverDef::SOLVER_CVC5_BV32_KIND )
			{
				paramType = SMT_TYPE_BV32;
			}
			else
//			if( SolverDef::DEFAULT_SOLVER_KIND == SolverDef::SOLVER_CVC5_KIND )
			{
				paramType = SMT_TYPE_INTEGER;
			}
//			else
//			{
//				AVM_OS_FATAL_ERROR_EXIT
//						<< "SolverDef::DEFAULT_SOLVER_KIND <> "
//							"CVC5_INT and <> CVC5_BV32 !!!\n"
//						<< SEND_EXIT;
//
//				paramType = SMT_TYPE_INTEGER;
//			}
		}

		else if( paramTypeSpecifier.weaklyTypedURational() )
		{
			paramType = SMT_TYPE_URATIONAL;
		}
		else if( paramTypeSpecifier.weaklyTypedRational() )
		{
			paramType = SMT_TYPE_RATIONAL;
		}

		else if( paramTypeSpecifier.weaklyTypedUReal() )
		{
			paramType = SMT_TYPE_UREAL;
		}
		else if( paramTypeSpecifier.weaklyTypedReal() )
		{
			paramType = SMT_TYPE_REAL;
		}

		else if( paramTypeSpecifier.isTypedString() )
		{
			paramType = SMT_TYPE_STRING;
		}
		else if( paramTypeSpecifier.isTypedEnum() )
		{
			paramType = SMT_TYPE_ENUM;
			// TODO Attention : il faudrait rajouter les contraintes
			// d'intervalle pour le type énuméré
		}
		else if( paramTypeSpecifier.isTypedMachine() )
		{
			// TODO:> Consolidation après TEST
			paramType = SMT_TYPE_INTEGER;
		}
		else
		{
			AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
					<< aParameter.getFullyQualifiedNameID() << " : "
					<< paramTypeSpecifier.getFullyQualifiedNameID() << ">> !!!"
					<< SEND_ALERT;

			paramType = SMT_TYPE_REAL;
		}


		cvc5::Term paramExpr = mSmtEngine.mkVar(
				paramType, uniqParameterID( aParameter ));

//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << TAB  << mParamPrefix << mTableOfParameterInstance.size()
//			<< " <- " << aParameter.getFullyQualifiedNameID() << std::endl;
//	AVM_OS_TRACE << std::flush;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

		aParameter.setMark( mTableOfParameterInstance.size() );

		mTableOfParameterInstance.push_back( bfParameter );

		mTableOfParameterExpr.push_back( paramExpr );

		mBitsetOfConstrainedParameter.push_back(
				paramTypeSpecifier.couldGenerateConstraint() );

		mBitsetOfPositiveParameter.push_back(
				paramTypeSpecifier.isTypedPositiveNumber() );

		mBitsetOfStrictlyPositiveParameter.push_back(
				paramTypeSpecifier.isTypedStrictlyPositiveNumber() );

//		if( m_pTableOfParameterExpr != nullptr )
//		{
//			m_pTableOfParameterExpr->append(paramExpr);
//		}
	}

	return( mTableOfParameterExpr[ aParameter.getMark() ] );
}



cvc5::Term & CVC5Solver::getBoundParameterExpr(
		const BF & bfParameter, ARGS & boundVarConstraints)
{
	InstanceOfData & aBoundParameter = const_cast< InstanceOfData & >(
			bfParameter.to< InstanceOfData >() );

//	if( aBoundParameter.getMark() == 0 )
	{
		const BaseTypeSpecifier & paramTypeSpecifier =
				aBoundParameter.referedTypeSpecifier();

		cvc5::Sort paramType;

		if( paramTypeSpecifier.isTypedBoolean() )
		{
			paramType = SMT_TYPE_BOOL;
		}
		else if( paramTypeSpecifier.weaklyTypedUInteger() )
		{
			if( SolverDef::DEFAULT_SOLVER_KIND ==
					SolverDef::SOLVER_CVC5_BV32_KIND )
			{
				paramType = SMT_TYPE_BV32;
			}
			else
//			if( SolverDef::DEFAULT_SOLVER_KIND == SolverDef::SOLVER_CVC5_KIND )
			{
				paramType = SMT_TYPE_UINTEGER;
			}
		}
		else if( paramTypeSpecifier.weaklyTypedInteger() )
		{
			if( SolverDef::DEFAULT_SOLVER_KIND ==
					SolverDef::SOLVER_CVC5_BV32_KIND )
			{
				paramType = SMT_TYPE_BV32;
			}
			else
//			if( SolverDef::DEFAULT_SOLVER_KIND == SolverDef::SOLVER_CVC5_KIND )
			{
				paramType = SMT_TYPE_INTEGER;
			}
//			else
//			{
//				AVM_OS_FATAL_ERROR_EXIT
//						<< "SolverDef::DEFAULT_SOLVER_KIND <> "
//							"CVC5_INT and <> CVC5_BV32 !!!\n"
//						<< SEND_EXIT;
//
//				paramType = SMT_TYPE_INTEGER;
//			}
		}

		else if( paramTypeSpecifier.weaklyTypedURational() )
		{
			paramType = SMT_TYPE_URATIONAL;
		}
		else if( paramTypeSpecifier.weaklyTypedRational() )
		{
			paramType = SMT_TYPE_RATIONAL;
		}

		else if( paramTypeSpecifier.weaklyTypedUReal() )
		{
			paramType = SMT_TYPE_UREAL;
		}
		else if( paramTypeSpecifier.weaklyTypedReal() )
		{
			paramType = SMT_TYPE_REAL;
		}

		else if( paramTypeSpecifier.isTypedString() )
		{
			paramType = SMT_TYPE_STRING;
		}
		else if( paramTypeSpecifier.isTypedEnum() )
		{
			paramType = SMT_TYPE_ENUM;
			// TODO Attention : il faudrait rajouter les contraintes
			// d'intervalle pour le type énuméré
		}
		else if( paramTypeSpecifier.isTypedMachine() )
		{
			// TODO:> Consolidation après TEST
			paramType = SMT_TYPE_INTEGER;
		}
		else
		{
			AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
					<< aBoundParameter.getFullyQualifiedNameID() << " : "
					<< paramTypeSpecifier.getFullyQualifiedNameID() << ">> !!!"
					<< SEND_ALERT;

			paramType = SMT_TYPE_REAL;
		}


		cvc5::Term paramExpr = mSmtEngine.mkTerm(cvc5::Kind::VARIABLE_LIST,
				{ mSmtEngine.mkVar(paramType, aBoundParameter.getNameID()) });

//AVM_IF_DEBUG_FLAG( SMT_SOLVING )
//	AVM_OS_TRACE << TAB  << mParamPrefix << mTableOfParameterInstance.size()
//			<< " <- " << aBoundParameter.getFullyQualifiedNameID() << std::endl;
//	AVM_OS_TRACE << std::flush;
//AVM_ENDIF_DEBUG_FLAG( SMT_SOLVING )

		aBoundParameter.setMark( mTableOfParameterInstance.size() );

		mTableOfParameterInstance.push_back( bfParameter );

		mTableOfParameterExpr.push_back( paramExpr );

		mBitsetOfStrictlyPositiveParameter.push_back( false );
		mBitsetOfPositiveParameter.push_back( false );
		mBitsetOfConstrainedParameter.push_back( false );

		if( paramTypeSpecifier.isTypedStrictlyPositiveNumber() )
		{
			boundVarConstraints.next( mSmtEngine.mkTerm(
					cvc5::Kind::GT, { paramExpr, SMT_CST_INT_ZERO }) );
		}
		else if( paramTypeSpecifier.isTypedPositiveNumber() )
		{
			boundVarConstraints.next( mSmtEngine.mkTerm(
					cvc5::Kind::GEQ, { paramExpr, SMT_CST_INT_ZERO }) );
		}
		else
		{
			boundVarConstraints.next( SMT_CST_BOOL_TRUE );
		}

//		if( m_pTableOfParameterExpr != nullptr )
//		{
//			m_pTableOfParameterExpr->append(paramExpr);
//		}
	}

	return( mTableOfParameterExpr[ aBoundParameter.getMark() ] );
}



cvc5::Term & CVC5Solver::getVariableExpr(InstanceOfData * aVar,
		cvc5::Sort varType, avm_offset_t varID)
{
	if( mTableOfVariableExpr.size() <= varID )
	{
		mTableOfVariableExpr.push_back(
				mSmtEngine.mkVar( varType, uniqVariableID( *aVar, varID ) ) );
	}

	return( mTableOfVariableExpr.at(varID) );
}



bool CVC5Solver::appendPossitiveAssertion()
{
	std::size_t endOffset = mBitsetOfConstrainedParameter.size();
	for( std::size_t offset = 1 ; offset < endOffset ; ++offset )
	{
		if( mBitsetOfStrictlyPositiveParameter[offset] )
		{
			cvc5::Result result = mSmtEngine.checkSatAssuming(
					mSmtEngine.mkTerm(cvc5::Kind::GT,
						{ mTableOfParameterExpr[offset], SMT_CST_INT_ZERO}) );
			if( result.isUnsat() )
			{
				return( false );
			}
		}
		else if( mBitsetOfPositiveParameter[offset] )
		{
			cvc5::Result result = mSmtEngine.checkSatAssuming(
					mSmtEngine.mkTerm(cvc5::Kind::GEQ,
						{ mTableOfParameterExpr[offset], SMT_CST_INT_ZERO }) );
			if( result.isUnsat() )
			{
				return( false );
			}
		}
	}

	return( true );
}


cvc5::Term CVC5Solver::safe_from_baseform(const BF & exprForm)
{
	try
	{
		return( from_baseform(exprForm) );
	}
	catch ( const std::exception & ex )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tCVC5Solver::safe_from_baseform< std::exception :"
				<< SOLVER_SESSION_ID << ">\n\t" << ex.what() << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\tFailed to CONVERT sep::fml::expression to cvc5::Term:>" << std::endl
				<< "\t  " << exprForm.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();

		return( SMT_CST_INT_ZERO );
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << REPEAT("********", 10) << std::endl
				<< "\tCVC5Solver::safe_from_baseform< unknown::exception :"
				<< SOLVER_SESSION_ID << ">" << std::endl
				<< REPEAT("--------", 10) << std::endl
				<< "\tFailed to CONVERT sep::fml::expression to cvc5::Term:>" << std::endl
				<< "\t  " << exprForm.str() << std::endl
				<< REPEAT("********", 10) << std::endl;

		destroyChecker();

		return( SMT_CST_INT_ZERO );
	}

	return( SMT_CST_INT_ZERO );
}

cvc5::Term CVC5Solver::from_baseform(const BF & exprForm)
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
					return( mSmtEngine.mkTerm(cvc5::Kind::EQUAL, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}

				case AVM_OPCODE_NEQ:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::DISTINCT, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}

				case AVM_OPCODE_LT:
				{
					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_SLT, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::LT, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
				}

				case AVM_OPCODE_LTE:
				{
					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						cvc5::Term leftMember;
						cvc5::Term rightMember;
						BFVector rightList;
						BFVector leftList;

						if( aCode.first().is< AvmCode >() &&
							( aCode.first().to< AvmCode >().
									isOpCode( AVM_OPCODE_PLUS ) ) )
						{
							for( const auto & itOperand :
								aCode.first().to< AvmCode >().getOperands() )
							{
								if( itOperand.is< AvmCode >() &&
									( itOperand.to< AvmCode >().
											isOpCode( AVM_OPCODE_UMINUS ) ) )
								{
									rightList.append(
											itOperand.to< AvmCode >().first() );
								}
								else if( itOperand.isInteger() &&
										( itOperand.toInteger() < 0 ) )
								{
									rightList.append( ExpressionConstructor::
											newInteger(- itOperand.toInteger()) );
								}
								else
								{
									leftList.append( itOperand );
								}
							}
						}
						else if( not ( aCode.first().isInteger() &&
									 ( aCode.first().toInteger() == 0 ) ) )
						{
							leftList.append( aCode.first() );
						}

						if( aCode.second().is< AvmCode >() &&
							( aCode.second().to< AvmCode >().
									isOpCode( AVM_OPCODE_PLUS ) ) )
						{
							for( const auto & itOperand :
								aCode.second().to< AvmCode >().getOperands() )
							{
								if( itOperand.is< AvmCode >() &&
									( itOperand.to< AvmCode >().
											isOpCode( AVM_OPCODE_UMINUS ) ) )
								{
									leftList.append(
											itOperand.to< AvmCode >().first() );
								}
								else if( itOperand.isInteger() &&
										( itOperand.toInteger() < 0 ) )
								{
									leftList.append( ExpressionConstructor::
										newInteger(- itOperand.toInteger()) );
								}
								else
								{
									rightList.append( itOperand );
								}
							}
						}
						else if( not ( aCode.second().isInteger() &&
									 ( aCode.second().toInteger() == 0 ) ) )
						{
							rightList.append( aCode.second() );
						}

						if( leftList.empty() )
						{
							leftMember = from_baseform(
									ExpressionConstant::INTEGER_ZERO);
						}
						else if( leftList.singleton() )
						{
							leftMember = from_baseform(leftList[0]);
						}
						else
						{
							// leftMember = BVPLUS des elements de leftList
							leftMember = from_baseform( leftList[0] );
							for (std::size_t i = 1 ; i < leftList.size() ; i ++)
							{
								leftMember =  mSmtEngine.mkTerm(
										cvc5::Kind::BITVECTOR_ADD, {
												leftMember,
												from_baseform(leftList[i]) });
							}
						}

						if( rightList.empty() )
						{
							rightMember = from_baseform(
									ExpressionConstant::INTEGER_ZERO);
						}
						else if( rightList.singleton() )
						{
							rightMember = from_baseform(rightList[0]);
						}
						else
						{
							// rightMember = BVPLUS des elements de rightList
							rightMember = from_baseform( rightList[0] );
							for (std::size_t i = 1 ; i < rightList.size() ; i ++)
							{
								rightMember =  mSmtEngine.mkTerm(
										cvc5::Kind::BITVECTOR_ADD,  {
												rightMember,
												from_baseform(rightList[i]) });
							}
						}

						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_SLE, {
								leftMember, rightMember }) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::LEQ, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
				}

				case AVM_OPCODE_GT:
				{
					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_SGT, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::GT, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
				}

				case AVM_OPCODE_GTE:
				{
					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_SGE, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::GEQ, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
				}


				case AVM_OPCODE_CONTAINS:
				{
					const BuiltinCollection & aCollection =
							aCode.first().to< BuiltinCollection >();

					if( aCollection.singleton() )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::EQUAL, {
								from_baseform(aCollection.at(0)),
								from_baseform(aCode.second()) }) );
					}
					else if( aCollection.populated() )
					{
						ARGS arg( aCollection.size() );
						const BF & elt = aCode.second();

						for( std::size_t offset = 0 ; arg.hasNext() ; ++offset )
						{

							arg.next( mSmtEngine.mkTerm(cvc5::Kind::EQUAL, {
									from_baseform(aCollection.at(offset)),
									from_baseform(elt) }) );
						}

						return( mSmtEngine.mkTerm(cvc5::Kind::OR, arg->table) );
					}
					else
					{
						return( SMT_CST_BOOL_FALSE );
					}
				}


				// LOGICAL OPERATION
				case AVM_OPCODE_NOT:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::NOT, {
							from_baseform(aCode.first()) }) );
				}

				case AVM_OPCODE_AND:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( mSmtEngine.mkTerm(cvc5::Kind::AND, arg->table) );
				}

				case AVM_OPCODE_NAND:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::NOT, {
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
									from_baseform(aCode.first()),
									from_baseform(aCode.second())
							})
					}) );
				}

				case AVM_OPCODE_XAND:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::OR, {
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
									from_baseform(aCode.first()),
									from_baseform(aCode.second())
							}),
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
									mSmtEngine.mkTerm(cvc5::Kind::NOT, {
											from_baseform(aCode.first()) }),
									mSmtEngine.mkTerm(cvc5::Kind::NOT, {
											from_baseform(aCode.second()) })
							})
					}) );
				}


				case AVM_OPCODE_OR:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					return( mSmtEngine.mkTerm(cvc5::Kind::OR, arg->table) );
				}

				case AVM_OPCODE_NOR:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::NOT, {
							mSmtEngine.mkTerm(cvc5::Kind::OR, {
									from_baseform(aCode.first()),
									from_baseform(aCode.second())
							})
					}) );
				}

				case AVM_OPCODE_IMPLIES:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::IMPLIES, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}


				// QUANTIFED LOGICAL OPERATION
				case AVM_OPCODE_EXISTS:
				{
					std::size_t boundVarCount = aCode.size()  - 1;

					ARGS boundVars( boundVarCount );

					ARGS boundVarConstraints( aCode.size() );

					for (std::size_t offset = 0; offset < boundVarCount; ++offset)
					{
						boundVars.next(
								getBoundParameterExpr(aCode[ offset ],
										boundVarConstraints) );
					}

					cvc5::Term boundVarList = mSmtEngine.mkTerm(
							cvc5::Kind::VARIABLE_LIST, boundVars->table);

					boundVarConstraints.next(
							from_baseform(aCode[ boundVarCount ]) );

					return( mSmtEngine.mkTerm( cvc5::Kind::EXISTS, {
							boundVarList,
							mSmtEngine.mkTerm(cvc5::Kind::AND,
									boundVarConstraints->table)
					}) );

				}

				case AVM_OPCODE_FORALL:
				{
					std::size_t boundVarCount = aCode.size()  - 1;

					ARGS boundVars( boundVarCount );

					ARGS boundVarConstraints( boundVarCount );

					for (std::size_t offset = 0; offset < boundVarCount; ++offset)
					{
						boundVars.next(
								getBoundParameterExpr(aCode[ offset ],
										boundVarConstraints) );
					}

					cvc5::Term boundVarList = mSmtEngine.mkTerm(
							cvc5::Kind::VARIABLE_LIST, boundVars->table);

					cvc5::Term forallCondition =
							(boundVarCount == 1) ? boundVarConstraints[0]
							: mSmtEngine.mkTerm(cvc5::Kind::AND,
									boundVarConstraints->table);

					forallCondition = mSmtEngine.mkTerm(cvc5::Kind::IMPLIES, {
							forallCondition,
							from_baseform(aCode[ boundVarCount ]) });

					return( mSmtEngine.mkTerm(cvc5::Kind::FORALL, {
							boundVarList, forallCondition }) );
				}


				// BITWISE OPERATION
				case AVM_OPCODE_BAND:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_AND, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}

				case AVM_OPCODE_BOR:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_OR, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}

				case AVM_OPCODE_LSHIFT:
				{
					if( aCode.second().isInteger() )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_SHL, {
								from_baseform(aCode.first()),
								mSmtEngine.mkInteger(
										aCode.second().toInteger() ) }) );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Unexpected second argument for "
									"newFixedLeftShiftExpr !!!\n"
								<< aCode.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						break;
					}
				}

				case AVM_OPCODE_RSHIFT:
				{
					if( aCode.second().isInteger() )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_ASHR, {
								from_baseform(aCode.first()),
								mSmtEngine.mkInteger(
										aCode.second().toInteger() ) }) );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Unexpected second argument for "
									"newFixedRightShiftExpr !!!\n"
								<< aCode.toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						break;
					}
				}

				case AVM_OPCODE_XOR:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::OR, {
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
								from_baseform(aCode.first()),
								mSmtEngine.mkTerm(cvc5::Kind::NOT, {
											from_baseform(aCode.second()) })
							}),
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
								mSmtEngine.mkTerm(cvc5::Kind::NOT, {
									from_baseform(aCode.first()) }),
								from_baseform(aCode.second())
							})
					}) );
				}

				case AVM_OPCODE_XNOR:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::OR, {
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second())
							}),
							mSmtEngine.mkTerm(cvc5::Kind::AND, {
								mSmtEngine.mkTerm(cvc5::Kind::NOT, {
									from_baseform(aCode.first()) }),
								mSmtEngine.mkTerm(cvc5::Kind::NOT, {
											from_baseform(aCode.second()) })
							})
					}) );
				}


				// ARITHMETIC OPERATION
				case AVM_OPCODE_PLUS:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						return( mSmtEngine.mkTerm(
								cvc5::Kind::BITVECTOR_ADD, arg->table) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(
								cvc5::Kind::ADD, arg->table) );
					}
				}

				case AVM_OPCODE_UMINUS:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::NEG, {
							from_baseform(aCode.first()) }) );
				}

				case AVM_OPCODE_MINUS:
				{
					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::BITVECTOR_SUB, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(cvc5::Kind::SUB, {
								from_baseform(aCode.first()),
								from_baseform(aCode.second()) }) );
					}
				}

				case AVM_OPCODE_MULT:
				{
					ARGS arg( aCode.size() );

					for( const auto & itOperand : aCode.getOperands() )
					{
						arg.next( from_baseform(itOperand) );
					}

					if( SolverDef::DEFAULT_SOLVER_KIND ==
							SolverDef::SOLVER_CVC5_BV32_KIND )
					{
						return( mSmtEngine.mkTerm(
									cvc5::Kind::BITVECTOR_MULT, arg->table) );
					}
					else
//						if( SolverDef::DEFAULT_SOLVER_KIND ==
//								SolverDef::SOLVER_CVC5_KIND )
					{
						return( mSmtEngine.mkTerm(
								cvc5::Kind::MULT, arg->table) );
					}
				}

				case AVM_OPCODE_DIV:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::DIVISION, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}

				case AVM_OPCODE_POW:
				{
					return( mSmtEngine.mkTerm(cvc5::Kind::POW, {
							from_baseform(aCode.first()),
							from_baseform(aCode.second()) }) );
				}

//				case AVM_OPCODE_MOD:

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "CVC5Solver::from_baseform:> "
								"Unsupported expression !!!\n"
							<< aCode.toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					break;
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
			if( SolverDef::DEFAULT_SOLVER_KIND ==
					SolverDef::SOLVER_CVC5_BV32_KIND )
			{
				return( mSmtEngine.mkBitVector( 32,
						exprForm.to< Integer >().toInteger() ) );
			}
			else
//				if( SolverDef::DEFAULT_SOLVER_KIND == SolverDef::SOLVER_CVC5_KIND )
			{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

//				return( mSmtEngine.mkInteger(
//						exprForm.to< Integer >().getValue() ) );
				return( mSmtEngine.mkInteger( exprForm.to< Integer >().toInteger() ) );

#else

				return( mSmtEngine.mkInteger( exprForm.to< Integer >().str()) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
			}
//			else
//			{
//			AVM_OS_FATAL_ERROR_EXIT
//					<< "SolverDef::DEFAULT_SOLVER_KIND <> "
//						"CVC5_INT and <> CVC5_BV32 !!!\n"
//					<< SEND_EXIT;
//
//				return( mSmtEngine.mkConst( cvc5::Rational(
//						exprForm.to< Integer >().getValue() ) ) );
//			}
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

//			return( mSmtEngine.mkReal(
//					exprForm.to< Rational >().getValue() ) );

			return( mSmtEngine.mkReal( exprForm.to< Rational >().str() ) );

#else

			return( mSmtEngine.mkReal( exprForm.to< Rational >().str() ) );

//			return( mSmtEngine.mkConst( cvc5::Rational(
//					exprForm.to< Rational >().getNumerator(),
//					exprForm.to< Rational >().getDenominator()) ) );
//
//			return( mSmtEngine.mkConst( cvc5::Rational(
//					exprForm.to< Rational >().strNumerator(),
//					exprForm.to< Rational >().strDenominator()) ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_  */
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
#if defined( _AVM_BUILTIN_NUMERIC_GMP_ )

//			return( mSmtEngine.mkReal( mpq_class(
//					exprForm.to< Float >().getValue() ) ) );

			return( mSmtEngine.mkReal( exprForm.to< Float >().str() ) );

#else

			return( mSmtEngine.mkReal( exprForm.to< Float >().str() ) );

#endif /* _AVM_BUILTIN_NUMERIC_GMP_ */
		}


		case FORM_RUNTIME_ID_KIND:
		{
			return( mSmtEngine.mkInteger( exprForm.bfRID().getRid() ) );
		}


		case FORM_BUILTIN_CHARACTER_KIND:
		{
			AVM_OS_ERROR_ALERT << "Unexpected a CHAR as expression << "
					<< exprForm.to< Character >().getValue()
					<< " >> !!!"
					<< SEND_ALERT;

			return( mSmtEngine.mkString(
					exprForm.to< Character >().str() ) );
		}

		case FORM_BUILTIN_STRING_KIND:
		{
			return( mSmtEngine.mkString(
					exprForm.to< String >().getValue() ) );
		}

		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected a STRING | UFI as expression << "
					<< exprForm.to< String >().getValue() << " >> !!!"
					<< SEND_EXIT;

			break;
//			return( mSmtEngine.mkString(
//					exprForm.to< String >().getValue() ) );
		}

		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected a IDENTIFIER as expression << "
					<< exprForm.to< Identifier >().getValue()
					<< " >> !!!"
					<< SEND_EXIT;

			break;
//			return( mSmtEngine.mkString(
//					exprForm.to< Identifier >().getValue() ) );
		}

		case FORM_OPERATOR_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected an OPERATOR as expression << "
					<< exprForm.to< Operator >().standardSymbol()
					<< " >> !!!"
					<< SEND_EXIT;

			break;
//			return( mSmtEngine.mkString(
//					exprForm.to< Operator >().standardSymbol() ) );
		}


		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_PORT_KIND:

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "CVC5Solver::from_baseform:> Unexpected OBJECT KIND << "
					<< exprForm.classKindName() << " >> as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			break;
//			return( mSmtEngine.mkString(
//					exprForm.to< BaseInstanceForm >().getFullyQualifiedNameID() ) );
		}
	}

	AVM_OS_FATAL_ERROR_EXIT
			<< "CVC5Solver::from_baseform ERROR !!!"
			<< SEND_EXIT;

	return( SMT_CST_INT_ZERO );
}


void CVC5Solver::dbg_smt(const cvc5::Term & aFormula, bool produceModelOption) const
{
//	aFormula.printAst(AVM_OS_TRACE << "\t");
	AVM_OS_TRACE << "\t" << aFormula.toString() << std::endl;

	std::string fileLocation = ( OSS() << mLogFolderLocation
			<< ( produceModelOption ? "cvc4_get_model_" : "cvc4_check_sat_" )
			<< SOLVER_SESSION_ID << ".smt2" );

	std::ofstream osFile;
	osFile.open(fileLocation, std::ios_base::out);
	if ( osFile.good() )
	{
		osFile << "; Getting info" << std::endl
				<< "(get-info :name)"    << std::endl
				<< "(get-info :version)" << std::endl;

		if( produceModelOption )
		{
			osFile << "; Getting values or models" << std::endl
					<< "(set-option :produce-models true)" << std::endl
//					<< "; Getting assignments" << std::endl
//					<< "(set-option :produce-assignments true)" << std::endl
					<< "; Logic" << std::endl
					<< "(set-logic ALL)" << std::endl
					<< std::endl;

//			aFormula.printAst(osFile << "\t");
			osFile << "\t" << aFormula;

			osFile << std::endl << std::endl
					<< "(get-model)" << std::endl
//					<< "(get-assignment)"
					<< std::endl;
		}
		else
		{
			osFile << std::endl;

//			aFormula.printAst(osFile << "\t");
			osFile << "\t" << aFormula.toString()
					<< std::endl << std::endl
					<< "CHECKSAT;" << std::endl;
		}

		osFile.close();
	}
}




} /* namespace sep */


#endif /* _AVM_SOLVER_CVC5_ */
