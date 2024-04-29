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
#include "SatSolver.h"


#include <util/avm_vfs.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionFactory.h>

#include <fml/workflow/WObject.h>


namespace sep
{

class Configuration;


bool SatSolver::configure(
		Configuration & aConfiguration, const WObject * wfFilterObject,
		ListOfPairMachineData & listOfSelectedVariable)
{
	mListOfSelectedVariable = listOfSelectedVariable;

	if( mListOfSelectedVariable.empty() )
	{
		AVM_OS_WARNING_ALERT
				<< "Unexpected in SatSolver, for redundancy detection, "
					"an empty selected variable list !!!"
				<< SEND_ALERT;

		return( mConfigFlag = true );
	}


AVM_IF_DEBUG_FLAG2( CONFIGURING , SOLVING )
	AVM_OS_TRACE << std::endl
			<< "Listes des variables utilisées pour la redondance" << std::endl;

	std::size_t varCount = 0;
	ListOfInstanceOfData::const_iterator itVar;
	ListOfInstanceOfData::const_iterator endVar;

	ListOfPairMachineData::const_iterator itPairMachineData =
			mListOfSelectedVariable.begin();
	ListOfPairMachineData::const_iterator endPairMachineData =
			mListOfSelectedVariable.end();
	for( ; itPairMachineData != endPairMachineData ; ++itPairMachineData )
	{
		AVM_OS_TRACE << "\t" << "Machine:> "
				<< (*itPairMachineData).first().getFullyQualifiedNameID() << std::endl;

		if( (*itPairMachineData).second().nonempty() )
		{
			itVar = (*itPairMachineData).second().begin();
			endVar = (*itPairMachineData).second().end();
			for( ; itVar != endVar ; ++itVar , ++varCount )
			{
				AVM_OS_TRACE << "\t\t" << str_header( *itVar ) << std::endl;
			}
		}
	}

	AVM_OS_TRACE << "Total:> " << varCount << std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( CONFIGURING , SOLVING )

	return( mConfigFlag = true );
}



/**
 * SOLVER
 * an empty << dataVector >> compute by the solver
 * an empty << valuesVector >> compute by the solver
 */
bool SatSolver::solve(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	BF fullCondition = completeUsingDataTypeConstraint(aCondition, dataVector);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << "SatSolver::solve(...) :>" << std::endl
			<< "\tcondition:> " << aCondition.str() << std::endl
			<< "\tfull cond:> " << fullCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

	if( fullCondition.isEqualTrue() )
	{
		return( true );
	}
	else if( fullCondition.isEqualFalse() )
	{
		return( false );
	}

	return( solveImpl(fullCondition, dataVector, valuesVector) );
}


BF SatSolver::completeUsingDataTypeConstraint(
		const BF & aCondition, BFVector & dataVector) const
{
	BF allCondition = aCondition;
	BF typeConstraint;

	BFVector paramsVars( dataVector );
	BFList boundVars;
	ExpressionFactory::collectsFreeVariable(aCondition, boundVars, paramsVars);

	BFVector::raw_iterator< InstanceOfData > itParam = paramsVars.begin();
	BFVector::raw_iterator< InstanceOfData > endParam = paramsVars.end();
	for( ; itParam != endParam ; ++itParam )
	{
		typeConstraint = (itParam)->getTypeSpecifier().genConstraint( *itParam );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )
		AVM_OS_TRACE << "completeUsingDataTypeConstraint:> "
				<< str_header( *itParam ) << std::endl
				<< "\tconstraint:> " << typeConstraint.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )

		if( typeConstraint.isEqualFalse() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE );
		}
		else if( typeConstraint.isNotEqualTrue() )
		{
			allCondition = ExpressionConstructor::andExpr(
					allCondition, typeConstraint);
		}
	}

	return( allCondition );
}


////////////////////////////////////////////////////////////////////////////////
// SMT2 for DEBUG
////////////////////////////////////////////////////////////////////////////////

std::string SatSolver::strTypeSmt2(const ITypeSpecifier & aTypedElement) const
{
	if( aTypedElement.isTypedBoolean() )
	{
		return "Bool";
	}
	else if( aTypedElement.isTypedEnum() )
	{
		return "Int";
	}
	else if( aTypedElement.isTypedUInteger() )
	{
		return "Int";
	}
	else if( aTypedElement.weaklyTypedInteger() )
	{
		return "Int";
	}
	else if( aTypedElement.weaklyTypedReal() )
	{
		return "Real";
	}
	else
	{
		return "Unknown";
	}
}


bool SatSolver::to_smt(OutStream & os,
		const BF & aCondition, bool enableModelProduction) const
{
	BFVector paramVector;

	StringOutStream ossCondition("", "\t", "");

	to_smt(ossCondition, aCondition, paramVector);

	os << ";; Getting info" << std::endl
		<< "(get-info :name)"    << std::endl
		<< "(get-info :version)" << std::endl;

	//	osFile << "(echo \"" << aCondition.str() << "\")" << std::endl;

	std::size_t paramCount = paramVector.size();
	for( std::size_t offset = 0 ; offset < paramCount ; offset++ )
	{
		const InstanceOfData & aParam =
				paramVector[ offset ].to< InstanceOfData >();

		os << "(declare-const " << uniqParameterID(aParam)
				<< " " << strTypeSmt2(aParam) << ")" << std::endl;
		if( aParam.getTypeSpecifier().isTypedStrictlyPositiveNumber() )
		{
			os << "(assert (< 0 " << uniqParameterID(aParam) <<"))" << std::endl;
		}
		else if( aParam.getTypeSpecifier().isTypedPositiveNumber() )
		{
			os << "(assert (<= 0 " << uniqParameterID(aParam) <<"))" << std::endl;
		}
	}

	os << "(assert " << ossCondition.str() << ")" << std::endl
		<< std::endl
		<< "(check-sat)" << std::endl;
	if( enableModelProduction )
	{
		os << "(get-model)" << std::endl;
	}

	return( true );
}


bool SatSolver::to_smt(OutStream & os,
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

				os << "(" << std::endl;
				auto endOperand = aCode.end();
				auto itOperand = aCode.begin();
				for( ; (itOperand + 1) != endOperand ; ++itOperand )
				{
					boundVars.append(*itOperand);

					if( (*itOperand).is< InstanceOfData >() )
					{
						const InstanceOfData & aParam =
								(*itOperand).to< InstanceOfData >();

						os << "\t(" << uniqParameterID(aParam)
							<< " " << strTypeSmt2(aParam) << ")" << std::endl;

						if( aParam.getTypeSpecifier().isTypedStrictlyPositiveNumber() )
						{
							typeConstraint << "(< 0 "
									<< uniqParameterID(aParam) <<") ";
						}
						else if( aParam.getTypeSpecifier().isTypedPositiveNumber() )
						{
							typeConstraint << "(<= 0 "
									<< uniqParameterID(aParam) <<") ";
						}
					}
					else if( (*itOperand).is< Variable >() )
					{
						const Variable & aVariable = (*itOperand).to< Variable >();

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
								<< " " << varType << ")" << std::endl;
						if( isTypedStrictlyPositive )
						{
							os << "(assert (< 0 " << uniqVariableID(aVariable) <<"))" << std::endl;
						}
						else if( isTypedPositive )
						{
							os << "(assert (<= 0 " << uniqVariableID(aVariable) <<"))" << std::endl;
						}
					}
					else
					{
						os << "\t(" << (*itOperand).str() << ")" << std::endl;
					}
				}
				std::string strConstraint = typeConstraint.str();
				if( strConstraint.size() > 0 )
				{
					os << "\t; (and " << strConstraint << ")" << std::endl;
				}
				os << "\t)" << std::endl << "\t";

				to_smt(os, *itOperand, dataVector);

				os << eoe << ')' << std::endl;

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

				os << eoe << ')';
			}

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

			os << " }";

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

				os << " }";
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


}
