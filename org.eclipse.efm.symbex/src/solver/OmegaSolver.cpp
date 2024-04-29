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

#include "OmegaSolver.h"

/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_OMEGA_ )


#include <common/BF.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>
#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/expression/ExpressionSimplifier.h>
#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{

/*
 ***************************************************************************
 * ID
 ***************************************************************************
 */
std::string OmegaSolver::ID = "OMEGA";

std::string OmegaSolver::DESCRIPTION = "OMEGA 'Solver of quantifier-free "
		"problems in Presburger Arithmetic at CS.UMD.EDU, version 2.1'";

std::uint64_t OmegaSolver::SOLVER_SESSION_ID = 1;



/**
 * CONFIGURE
 */
bool OmegaSolver::configure(
		Configuration & aConfiguration, const WObject * wfFilterObject,
		ListOfPairMachineData & listOfSelectedVariable)
{
	if( not SatSolver::configure(
		aConfiguration, wfFilterObject, listOfSelectedVariable) )
	{
		return( mConfigFlag = false );
	}

	setSelectedVariable(
			aConfiguration.getMainExecutionData(),
			listOfSelectedVariable );

	return( mConfigFlag = true );
}


/**
 * RESET VARIABLE or PARAMETER
 */
void OmegaSolver::resetVariableTable()
{
	getSelectedVariable().clear();

	// Attention Omega compte de 1 à n
	mTableOfVariableInstance.clear();
	mTableOfVariableInstance.append( nullptr );

	mTableOfVar4ParamInstance.clear();
}


void OmegaSolver::resetParameterTable()
{
	// Initialisation du tableau des parametres
	mTableOfVariableID.clear();

	for( const auto & itParamInstance : mTableOfParameterInstance )
	{
		itParamInstance->setMark(0);
	}
	mTableOfParameterInstance.clear();

	// Attention: Omega compte de 1 à n
	mTableOfParameterID.clear();
	omega::Variable_ID sentinelID;
	mTableOfParameterID.push_back(sentinelID);
}


/**
 * SET VARIABLE or PARAMETER
 */
void OmegaSolver::setSelectedVariable(const ExecutionData & anED)
{
	resetVariableTable();

	TableOfInstanceOfData::const_raw_iterator itVar;
	TableOfInstanceOfData::const_raw_iterator endVar;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != endRF ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( itRID.refExecutable().hasVariable() ||
			itRID.refExecutable().hasBuffer() )
		{
			PairMachineData tmpListOfOffset( itRID );

			itVar = itRID.refExecutable().getBasicVariables().begin();
			endVar = itRID.refExecutable().getBasicVariables().end();
			for( ; itVar != endVar ; ++itVar )
			{
				tmpListOfOffset.second().append( (itVar) );

				mTableOfVariableInstance.append( (itVar) );

//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
//	AVM_OS_TRACE << TAB << "Omega Relation variable : "
//			<< str_header( *itVar ) << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
			}

			if( tmpListOfOffset.second().nonempty() )
			{
				getSelectedVariable().append(tmpListOfOffset);
			}
		}
	}
}


void OmegaSolver::setSelectedVariable(const ExecutionData & anED,
		ListOfPairMachineData & listOfSelectedVariable)
{
	resetVariableTable();

	SatSolver::setSelectedVariable(listOfSelectedVariable);

	for( const auto & itPairMachineData : listOfSelectedVariable )
	{
		if( itPairMachineData.second().nonempty() )
		{

			for( const auto & itVar : itPairMachineData.second() )
			{
				mTableOfVariableInstance.append( itVar );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
	AVM_OS_TRACE << TAB << "Omega Relation variable : "
			<< str_header( itVar ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
			}
		}
	}
}


void OmegaSolver::setSelectedVariable(const ExecutionData & anED,
		ListOfInstanceOfData & aLisOfAdditionnalVar)
{
	setSelectedVariable(anED);

	mTableOfVar4ParamInstance.append(aLisOfAdditionnalVar);
}



/**
 * PROVER
 */
bool OmegaSolver::isSubSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	oldEC.traceDefault(AVM_OS_TRACE << TAB);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	// Creation de la relation Omega
	// Attention: Omega compte de 1 à n
	omega::Relation oldRelation( mTableOfVariableInstance.size() - 1 );
	toRelation(oldEC.getExecutionData(), oldRelation);


	if( ((& newEC) != mCacheForNewEC) || isCurrentPathScope() )
	{
		mCacheForNewEC = (& newEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		newEC.traceDefault(AVM_OS_TRACE << TAB);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		// Creation de la relation Omega
		// Attention: Omega compte de 1 à n
		omega::Relation newRelation( mTableOfVariableInstance.size() - 1 );
		toRelation(newEC.getExecutionData(), newRelation);

		mCacheForNewRelation = newRelation;


		return( isSubSet(newRelation, oldRelation) );
	}
	else
	{
		omega::Relation newRelation = mCacheForNewRelation;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
		AVM_OS_TRACE << TAB << "ED cpy : "
				<< newRelation.print_with_subs_to_string() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )

		return( isSubSet(newRelation, oldRelation) );
	}
}


bool OmegaSolver::isEqualSet(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	oldEC.traceDefault(AVM_OS_TRACE << TAB);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	// Creation de la relation Omega
	// Attention: Omega compte de 1 à n
	omega::Relation oldRelation( mTableOfVariableInstance.size() - 1 );
	toRelation(oldEC.getExecutionData(), oldRelation);


	if( (& newEC) != mCacheForNewEC )
	{
		mCacheForNewEC = (& newEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		newEC.traceDefault(AVM_OS_TRACE << TAB);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		// Creation de la relation Omega
		// Attention: Omega compte de 1 à n
		omega::Relation newRelation( mTableOfVariableInstance.size() - 1 );
		toRelation(newEC.getExecutionData(), newRelation);

		mCacheForNewRelation = newRelation;


		return( isEqualSet(newRelation, oldRelation) );
	}
	else
	{
		omega::Relation newRelation = mCacheForNewRelation;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		AVM_OS_TRACE << TAB << "ED cpy : "
				<< newRelation.print_with_subs_to_string() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

		return( isEqualSet(newRelation, oldRelation) );
	}
}


bool OmegaSolver::isEmptyIntersection(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	oldEC.traceDefault(AVM_OS_TRACE << TAB);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	// Creation de la relation Omega
	// Attention: Omega compte de 1 à n
	omega::Relation oldRelation( mTableOfVariableInstance.size() - 1 +
			mTableOfVar4ParamInstance.size() );
	setParameterUple(oldRelation);
	toRelation(oldEC.getExecutionData(), oldRelation);


	if( (& newEC) != mCacheForNewEC )
	{
		mCacheForNewEC = (& newEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		newEC.traceDefault(AVM_OS_TRACE << TAB);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		// Creation de la relation Omega
		// Attention: Omega compte de 1 à n
		omega::Relation newRelation( mTableOfVariableInstance.size() - 1 +
				mTableOfVar4ParamInstance.size() );
		setParameterUple(newRelation);
		toRelation(newEC.getExecutionData(), newRelation);

		mCacheForNewRelation = newRelation;


		return( isEmptyIntersection(newRelation, oldRelation) );
	}
	else
	{
		omega::Relation newRelation = mCacheForNewRelation;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
		AVM_OS_TRACE << TAB << "ED cpy : "
				<< newRelation.print_with_subs_to_string() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

		return( isEmptyIntersection(newRelation, oldRelation) );
	}
}



SolverDef::SATISFIABILITY_RING OmegaSolver::isSatisfiable(const BF & aCondition)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "OmegaSolver::isSatisfiable(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	BF valCondition = ExpressionSimplifier::simplif( aCondition );

	// Initialisation du tableau des parametres
	mTableOfVariableID.clear();
	mTableOfParameterInstance.clear();

	// Attention: Omega compte de 1 à n
	mTableOfParameterID.clear();
	omega::Variable_ID sentinelID;
	mTableOfParameterID.push_back(sentinelID);

	omega::Relation aRelation(0);

	// Creation du quantificateur Exist associe aux parametres
	registerExistQuantifier = aRelation.add_and()->add_exists();
	omega::F_And * andRootNode = registerExistQuantifier->add_and();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
//	AVM_OS_COUT << "aCondition : " << aCondition->str() << std::flush;
	AVM_OS_TRACE << "v::isSatisfiable(...) "
				":" << SOLVER_SESSION_ID << ">" << std::endl;
	AVM_OS_TRACE << TAB << aCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	toConjonction(andRootNode, valCondition);

	// Simplification de la Relation
	aRelation.finalize();

	aRelation.simplify(2,4);


//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
//	AVM_OS_TRACE << TAB << "the Relation : "
//			<< newRelation.print_with_subs_to_string() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )


	SolverDef::SATISFIABILITY_RING satisfiability =
			aRelation.is_satisfiable() ?
					SolverDef::SATISFIABLE : SolverDef::UNSATISFIABLE;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "result :" << SOLVER_SESSION_ID << "> "
			<< SolverDef::strSatisfiability(satisfiability) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	aRelation = omega::Relation::Null();

	resetParameterTable();

	return( satisfiability );
}


/**
 * TOOLS
 */
bool OmegaSolver::isSubSet(omega::Relation & Rel1, omega::Relation & Rel2)
{
	return( Must_Be_Subset(Rel1, Rel2) );
}

bool OmegaSolver::isEqualSet(omega::Relation & Rel1, omega::Relation & Rel2)
{
	return( Must_Be_Subset(copy(Rel1), copy(Rel2)) && Must_Be_Subset(Rel2, Rel1) );
}


bool OmegaSolver::isEmptyIntersection(omega::Relation & Rel1, omega::Relation & Rel2)
{
	omega::Relation interRelation = Intersection(Rel2, Rel1);

	bool isEmpty = (! interRelation.is_satisfiable() );

	interRelation = omega::Relation::Null();

	return( isEmpty );
}


bool OmegaSolver::setParameterUple(omega::Relation & aRelation)
{
	std::ostringstream oss;

	VectorOfInstanceOfData::const_iterator it = mTableOfVar4ParamInstance.begin();
	VectorOfInstanceOfData::const_iterator itEnd = mTableOfVar4ParamInstance.end();
	avm_offset_t paramOffset = 1;
	for( ; it != itEnd ; ++it , ++paramOffset )
	{
		oss.str("");
		oss << "VP_" << paramOffset;


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << TAB <<  oss.str() << " << " << (*it)->getFullyQualifiedNameID()
			<< " >> --> is a Symbolic Parameter" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

		(*it)->setOffset(mTableOfParameterID.size());
		mTableOfParameterInstance.push_back( (*it) );

		omega::Variable_ID aVarID = aRelation.set_var(paramOffset);
		mTableOfParameterID.push_back( aVarID );
		aRelation.name_set_var(paramOffset, oss.str().c_str());
	}

	return( true );
}

bool OmegaSolver::toRelation(
		const ExecutionData & anED, omega::Relation & aRelation)
{
	// Creation du quantificateur Exist associe aux parametres
	registerExistQuantifier = aRelation.add_and()->add_exists();
	omega::F_And * andRootNode = registerExistQuantifier->add_and();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << TAB << "aPC : " << anED.getPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	toConjonction(andRootNode, anED.getPathCondition());

	std::ostringstream oss;

	ListOfPairMachineData::const_iterator itPairMachineData = getSelectedVariable().begin();
	ListOfPairMachineData::const_iterator endPairMachineData = getSelectedVariable().end();
	avm_offset_t varOffset = mTableOfVar4ParamInstance.size() + 1;
	for( ; itPairMachineData != endPairMachineData ; ++itPairMachineData )
	{
		if( (*itPairMachineData).second().nonempty() )
		{
			ListOfInstanceOfData::const_iterator itVar = (*itPairMachineData).second().begin();
			ListOfInstanceOfData::const_iterator endVar = (*itPairMachineData).second().end();

			const RuntimeForm & aRF = anED.getRuntime( (*itPairMachineData).first() );

			for( ; itVar != endVar ; ++itVar , ++varOffset )
			{
				oss.str("");
				oss << "V_" << varOffset;


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
//	AVM_OS_COUT <<  oss.str() << " <-- " << aRF.getData(*itVar).str() << std::endl;
	AVM_OS_TRACE << TAB <<  oss.str() << " <-- "
			<< aRF.getData(*itVar).str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


				omega::Variable_ID aVarID = aRelation.set_var(varOffset);
				mTableOfVariableID.push_back(aVarID);
				aRelation.name_set_var(varOffset, oss.str().c_str());

				omega::EQ_Handle eqNode = andRootNode->add_EQ();
				eqNode.update_coef(aVarID, -1);

				if( (*itVar)->isTypedBoolean() )
				{
					if( aRF.getData(*itVar).isEqualTrue() )
					{
						eqNode.update_const( 1 );
					}
					else if( aRF.getData(*itVar).isEqualFalse() )
					{
						eqNode.update_const( 0 );
					}
					else
					{
						eqNode.update_coef(aVarID, 1);
					}
				}
				else
				{
					toConstraint(eqNode, 1, aRF.getData(*itVar));
				}
			}
		}
	}

	// Simplification de la Relation
	aRelation.finalize();


//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
//	AVM_OS_COUT << "FINALIZE : ";
//	aRelation.prefix_print(); AVM_OS_COUT << std::flush;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )


	aRelation.simplify(2,4);


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )
//	AVM_OS_COUT << "SIMPLIF  : " << std::endl
//			<< "ED : " << aRelation.print_with_subs_to_string() << std::endl;
	AVM_OS_TRACE << TAB << "ED : "
			<< aRelation.print_with_subs_to_string() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SMT_SOLVING )


	resetParameterTable();

	return( true );
}


omega::Variable_ID OmegaSolver::getParameterID(InstanceOfData * aParameter)
{
	if( aParameter->getMark() == 0 )
	{
//		if( aParameter->isTypedBoolean() )
//		{
//		}
//		else if( aParameter->isTypedInteger() )
//		{
//		}
//		else if( aParameter->isTypedRational() )
//		{
//		}
//		else if( aParameter->isTypedFloat() )
//		{
//		}
//		else if( aParameter->isTypedReal() )
//		{
//		}
//		else
//		{
//			AVM_OS_ERROR_ALERT << "Unexpected an instance type << "
//					<< aParameter->getFullyQualifiedNameID() << " : " << paramFormType->getFullyQualifiedNameID()
//					<< ">> !!!"
//					<< SEND_ALERT;
//		}

		aParameter->setMark(mTableOfParameterID.size());
		mTableOfParameterInstance.push_back(aParameter);

		std::ostringstream oss;
		oss.str("");
		oss << "P_" << mTableOfParameterID.size();


//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
//	AVM_OS_COUT << "\t" << oss.str() << " <- " << aParameter->getFullyQualifiedNameID() << std::endl;
//	AVM_OS_TRACE << TAB  << oss.str() << " <- " << aParameter->getFullyQualifiedNameID() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

		mTableOfParameterID.push_back(
				registerExistQuantifier->declare( oss.str().c_str() ) );
	}

	//return( mTableOfParameterID[ aParameter->getMark() ] );

	omega::Variable_ID varID = mTableOfParameterID[ aParameter->getMark() ];


//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
//	AVM_OS_TRACE << TAB << "varID: ";
//	const char * c = varID->char_name();
//	while( isalnum(*c) ) { AVM_OS_TRACE << *c; ++c; }
//	AVM_OS_TRACE << TAB << " <- " << str_header( aParameter ) << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	return( varID );
}


void OmegaSolver::toConjonction(omega::F_And * andNode, const BF & exprForm)
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
				case AVM_OPCODE_EQ: // - first + second == 0
				{
					BFCode exprCond;
					avm_integer_t exprInt;

					if( aCode.first().is< AvmCode >() )
					{
						exprCond = aCode.first().bfCode();

						if( aCode.second().isInteger() )
						{
							exprInt = aCode.second().toInteger();
						}
					}
					else if( aCode.first().isInteger() )
					{
						exprInt = aCode.first().toInteger();

						if( aCode.second().is< AvmCode >() )
						{
							exprCond = aCode.second().bfCode();
						}
					}

					if( exprCond.valid() )
					{
						switch( exprCond->getAvmOpCode() )
						{
							case AVM_OPCODE_EQ:
							case AVM_OPCODE_NEQ:
							case AVM_OPCODE_LT:
							case AVM_OPCODE_LTE:
							case AVM_OPCODE_GT:
							case AVM_OPCODE_GTE:
							case AVM_OPCODE_NOT:
							case AVM_OPCODE_AND:
							case AVM_OPCODE_NAND:
							case AVM_OPCODE_XAND:
							case AVM_OPCODE_OR:
							case AVM_OPCODE_NOR:
							case AVM_OPCODE_XOR:
							case AVM_OPCODE_XNOR:
							{
								omega::F_And * andEQ = andNode;

								if( exprInt == 0 )
								{
									andEQ = andNode->add_not()->add_and();
								}

								toConjonction(andEQ, exprCond);

								return;
							}

							default:
							{
								break;
							}
						}
					}
					else
					{
						omega::EQ_Handle eqNode = andNode->add_EQ();
						toConstraint(eqNode, -1, aCode.first());
						toConstraint(eqNode,  1, aCode.second());
					}

					break;
				}


				case AVM_OPCODE_NEQ: // NOT( - first + second == 0 )
				{
					BFCode exprCond;
					avm_integer_t exprInt;

					if( aCode.first().is< AvmCode >() )
					{
						exprCond = aCode.first().bfCode();

						if( aCode.second().isInteger() )
						{
							exprInt = aCode.second().toInteger();
						}
					}
					else if( aCode.first().isInteger() )
					{
						exprInt = aCode.first().toInteger();

						if( aCode.second().is< AvmCode >() )
						{
							exprCond = aCode.second().bfCode();
						}
					}

					if( exprCond.valid() )
					{
						switch( exprCond->getAvmOpCode() )
						{
							case AVM_OPCODE_EQ:
							case AVM_OPCODE_NEQ:
							case AVM_OPCODE_LT:
							case AVM_OPCODE_LTE:
							case AVM_OPCODE_GT:
							case AVM_OPCODE_GTE:
							case AVM_OPCODE_NOT:
							case AVM_OPCODE_AND:
							case AVM_OPCODE_NAND:
							case AVM_OPCODE_XAND:
							case AVM_OPCODE_OR:
							case AVM_OPCODE_NOR:
							case AVM_OPCODE_XOR:
							case AVM_OPCODE_XNOR:
							{
								omega::F_And * andEQ = andNode;

								if( exprInt != 0 )
								{
									andEQ = andNode->add_not()->add_and();
								}

								toConjonction(andEQ, exprCond);

								return;
							}

							default:
							{
								break;
							}
						}
					}
					else
					{
						omega::EQ_Handle eqNode =
								andNode->add_not()->add_and()->add_EQ();

						toConstraint(eqNode, -1, aCode.first());
						toConstraint(eqNode,  1, aCode.second());
					}

					break;
				}



				case AVM_OPCODE_LT: // - first + second - 1 >= 0
				{
					omega::GEQ_Handle geqNode = andNode->add_GEQ();
					toConstraint(geqNode, -1, aCode.first());
					toConstraint(geqNode,  1, aCode.second());
					geqNode.update_const(-1);

					break;
				}

				case AVM_OPCODE_LTE: // - first + second >= 0
				{
					omega::GEQ_Handle geqNode = andNode->add_GEQ();
					toConstraint(geqNode, -1, aCode.first());
					toConstraint(geqNode,  1, aCode.second());

					break;
				}

				case AVM_OPCODE_GT: // first - second - 1 >= 0
				{
					omega::GEQ_Handle geqNode = andNode->add_GEQ();
					toConstraint(geqNode,  1, aCode.first());
					toConstraint(geqNode, -1, aCode.second());
					geqNode.update_const(-1);

					break;
				}

				case AVM_OPCODE_GTE:  // first - second >= 0
				{
					BFCode exprCond;
					avm_integer_t exprInt;

					if( aCode.first().is< AvmCode >() )
					{
						exprCond = aCode.first().bfCode();

						if( aCode.second().isInteger() )
						{
							exprInt = aCode.second().toInteger();
						}
					}
					else if( aCode.first().isInteger() )
					{
						exprInt = aCode.first().toInteger();

						if( aCode.second().is< AvmCode >() )
						{
							exprCond = aCode.second().bfCode();
						}
					}

					if( exprCond.valid() )
					{
						switch( exprCond->getAvmOpCode() )
						{
							case AVM_OPCODE_EQ:
							case AVM_OPCODE_NEQ:
							case AVM_OPCODE_LT:
							case AVM_OPCODE_LTE:
							case AVM_OPCODE_GT:
							case AVM_OPCODE_GTE:
							case AVM_OPCODE_NOT:
							case AVM_OPCODE_AND:
							case AVM_OPCODE_NAND:
							case AVM_OPCODE_XAND:
							case AVM_OPCODE_OR:
							case AVM_OPCODE_NOR:
							case AVM_OPCODE_XOR:
							case AVM_OPCODE_XNOR:
							{
								omega::F_And * andEQ = andNode;

								if( exprInt < 1 )
								{
									andEQ = andNode->add_not()->add_and();
								}

								toConjonction(andEQ, exprCond);

								return;
							}

							default:
							{
								break;
							}
						}
					}
					else
					{
						omega::GEQ_Handle geqNode = andNode->add_GEQ();
						toConstraint(geqNode,  1, aCode.first());
						toConstraint(geqNode, -1, aCode.second());
					}

					break;
				}


				case AVM_OPCODE_CONTAINS:
				{
					BuiltinCollection * aCollection =
							aCode.first().to_ptr< BuiltinCollection >();

					if( aCollection->singleton() )
					{
						omega::EQ_Handle eqNode = andNode->add_EQ();
						toConstraint(eqNode, -1, aCollection->at(0));
						toConstraint(eqNode,  1, aCode.second());
					}
					else if( aCollection->populated() )
					{
						omega::F_Or * orNode = andNode->add_or();

						std::size_t colSize = aCollection->size();
						for( std::size_t offset = 0 ; offset < colSize ; ++offset )
						{
							omega::EQ_Handle eqNode = orNode->add_and()->add_EQ();
							toConstraint(eqNode, -1, aCollection->at(offset));
							toConstraint(eqNode,  1, aCode.second());
						}
					}
					else
					{
						andNode->add_EQ().update_const(
							exprForm.to< Boolean >().getValue() ? 0 : 1 );
					}
					break;
				}


				case AVM_OPCODE_NOT:
				{
					if( aCode.first().is< InstanceOfData >() ) // arg0 == 0
					{
						andNode->add_EQ().update_coef(getParameterID(
								aCode.first().to_ptr< InstanceOfData >()), 1);
					}
					else  // NOT( arg0 )
					{
						toConjonction(andNode->add_not()->add_and(), aCode.first());
					}

					break;
				}

				case AVM_OPCODE_AND: // AND args
				{
					for( const auto & itOperand : aCode.getOperands() )
					{
						toConjonction(andNode, itOperand);
					}

					break;
				}

				case AVM_OPCODE_NAND: // NAND first second
				{
					omega::F_And * nandNode = andNode->add_not()->add_and();
					toConjonction(nandNode, aCode.first());
					toConjonction(nandNode, aCode.second());

					break;
				}


				case AVM_OPCODE_XAND:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported boolean expression << XAND >> !!!"
							<< SEND_EXIT;

					break;
				}


				case AVM_OPCODE_OR: // OR args
				{
					omega::F_Or * orNode = andNode->add_or();
					for( const auto & itOperand : aCode.getOperands() )
					{
						toConjonction(orNode->add_and(), itOperand);
					}

					break;
				}

				case AVM_OPCODE_NOR: // NOR first second
				{
					omega::F_And * norNode = andNode->add_not()->add_or()->add_and();
					toConjonction(norNode, aCode.first());
					toConjonction(norNode, aCode.second());

					break;
				}


				case AVM_OPCODE_XOR:
				case AVM_OPCODE_XNOR:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported boolean expression "
								"<< XOR | XNOR >> !!!"
							<< SEND_EXIT;

					break;
				}


				case AVM_OPCODE_PLUS:
				case AVM_OPCODE_UMINUS:
				case AVM_OPCODE_MINUS:
				case AVM_OPCODE_MULT:
				case AVM_OPCODE_DIV:
				case AVM_OPCODE_POW:
				case AVM_OPCODE_MOD:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected arithmetic expression Operator !!!"
							<< SEND_EXIT;
					break;
				}


				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected BASEFORM KIND for execution !!!\n"
							<< aCode.toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;
					break;
				}
			}

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
//			andNode->add_not()->add_and()->add_EQ().update_coef(
//					getParameterID( exprForm.to_ptr< InstanceOfData >() ) );

			omega::EQ_Handle eqNode = andNode->add_and()->add_EQ();
			eqNode.update_coef( getParameterID(exprForm.to_ptr< InstanceOfData >()), 1);
			eqNode.update_const(-1);

			break;
		}


		case FORM_BUILTIN_BOOLEAN_KIND: // true <=> (0 == 0) ; false <=> (1 == 0)
		{
			andNode->add_EQ().update_const(
					exprForm.to< Boolean >().getValue() ? 0 : 1 );

			break;
		}

		case FORM_BUILTIN_INTEGER_KIND:
		{
			andNode->add_EQ().update_const(
					exprForm.to< Integer >().isZero() ? 0 : 1 );

			break;
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			andNode->add_EQ().update_const(
					exprForm.to< Rational >().isZero() ? 0 : 1 );

			break;
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			andNode->add_EQ().update_const(
				exprForm.to< Float >().isZero() ? 0 : 1  );

			break;
		}

		case FORM_BUILTIN_CHARACTER_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unsupported built-in Character !!!"
					<< SEND_EXIT;

			break;
		}

		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unsupported built-in String "
						"< STRING | UFI | IDENTIFIER > or Operator !!!"
					<< SEND_EXIT;

			break;
		}

		case FORM_OPERATOR_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unsupported Operator expression !!!"
					<< SEND_EXIT;

			break;
		}


		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_PORT_KIND:

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected BASEFORM KIND as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			break;
		}
	}
}


void OmegaSolver::toConstraint(omega::Constraint_Handle & constraintNode,
		int coefficient, const BF & exprForm)
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
				case AVM_OPCODE_PLUS:
				{
					for( const auto & itOperand : aCode.getOperands() )
					{
						toConstraint(constraintNode, coefficient, itOperand);
					}

					break;
				}

				case AVM_OPCODE_UMINUS:
				{
					toConstraint(constraintNode, - coefficient, aCode.first());

					break;
				}

				case AVM_OPCODE_MINUS:
				{
					toConstraint(constraintNode,   coefficient, aCode.first());
					toConstraint(constraintNode, - coefficient, aCode.second());

					break;
				}

				case AVM_OPCODE_MULT:
				{
					if( aCode.size() == 2 )
					{
						if( aCode.first().isInteger() )
						{
							coefficient = coefficient * aCode.first().toInteger();
							toConstraint(constraintNode, coefficient, aCode.second());
						}
						else if( aCode.second().isInteger() )
						{
							coefficient = coefficient * aCode.second().toInteger();
							toConstraint(constraintNode, coefficient, aCode.first());
						}
						else
						{
							AVM_OS_FATAL_ERROR_EXIT
									<< "Unsupported non linear multiplication !!!"
									<< SEND_EXIT;
						}
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "Unsupported non binary multiplication !!!"
								<< SEND_EXIT;
					}

					break;
				}

				case AVM_OPCODE_DIV:
				case AVM_OPCODE_POW:
				case AVM_OPCODE_MOD:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unsupported arithmetic expression Operator "
								"<< DIV | EXP | MOD >> !!!"
							<< SEND_EXIT;

					break;
				}

				case AVM_OPCODE_EQ:
				case AVM_OPCODE_NEQ:
				case AVM_OPCODE_LT:
				case AVM_OPCODE_LTE:
				case AVM_OPCODE_GT:
				case AVM_OPCODE_GTE:
				case AVM_OPCODE_NOT:
				case AVM_OPCODE_AND:
				case AVM_OPCODE_NAND:
				case AVM_OPCODE_XAND:
				case AVM_OPCODE_OR:
				case AVM_OPCODE_NOR:
				case AVM_OPCODE_XOR:
				case AVM_OPCODE_XNOR:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected boolean expression Operator << "
							<< aCode.str() << " >> !!!"
							<< SEND_EXIT;

					break;
				}
				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected BASEFORM KIND for execution\n"
							<< aCode.toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;
					break;
				}
			}

			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			constraintNode.update_coef(
					getParameterID(exprForm.to_ptr< InstanceOfData >()),
					coefficient );

			break;
		}


		case FORM_BUILTIN_BOOLEAN_KIND:  // true <=> 1 ; false <=> 0
		{
			constraintNode.update_const(
					( exprForm.to< Boolean >().getValue() ) ? 1 : 0 );

			break;
		}

		case FORM_BUILTIN_INTEGER_KIND:
		{
			constraintNode.update_const(
					coefficient * exprForm.to< Integer >().toInteger() );

			break;
		}

		case FORM_BUILTIN_RATIONAL_KIND:
		{
			AVM_OS_WARNING_ALERT << "Unsupported builtin Rational !!!"
					<< SEND_ALERT;

			if( exprForm.to< Rational >().isInteger() )
			{
				constraintNode.update_const(
					coefficient * exprForm.to< Rational >().toInteger() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unsupported built-in Rational !!!"
						<< SEND_EXIT;
			}

			break;
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			AVM_OS_WARNING_ALERT << "Unsupported built-in Float !!!"
					<< SEND_ALERT;

			if( exprForm.to< Float >().isInteger() )
			{
				constraintNode.update_const(
						coefficient * exprForm.to< Float >().toInteger() );
			}
			else
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unsupported built-in Float !!!"
						<< SEND_EXIT;
			}

			break;
		}


		case FORM_RUNTIME_ID_KIND:
		{
			constraintNode.update_const(
					coefficient * exprForm.bfRID().getRid() );

			break;
		}


		case FORM_BUILTIN_CHARACTER_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unsupported built-in Character !!!"
					<< SEND_EXIT;

			break;
		}

		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unsupported built-in String "
						"< STRING | UFI | IDENTIFIER > or Operator !!!"
					<< SEND_EXIT;

			break;
		}

		case FORM_OPERATOR_KIND:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unsupported Operator expression !!!"
					<< SEND_EXIT;

			break;
		}


		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_PORT_KIND:

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected BASEFORM KIND as expression << "
					<< exprForm.str() << " >> !!!"
					<< SEND_EXIT;

			break;
		}
	}
}


/**
 * SOLVER
 */
bool OmegaSolver::solveImpl(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )
	AVM_OS_TRACE << "OmegaSolver::solve(...) "
			":" << SOLVER_SESSION_ID << ">" << std::endl
			<< "\t" << aCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SMT_SOLVING )

	// !!!! NE FAIT RIEN POUR L'INSTANT

	return(false);
}


}


#endif /* _AVM_SOLVER_OMEGA_ */
