/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_TESTCASE_UTILS_H_
#define AVM_TESTCASE_UTILS_H_

#include <common/BF.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/infrastructure/Variable.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{

class Machine;


class AvmTestCaseUtils
{

private:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTestCaseUtils()
	{

	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTestCaseUtils()
	{
		//!! NOTHING
	}


public:

	////////////////////////////////////////////////////////////////////////////
	// TEST CASE UTILS
	////////////////////////////////////////////////////////////////////////////

	static void getTestPurposeTrace(const ExecutionContext & tpEC,
			ExecutionContext::VectorOfConstPtr & testPurposeTrace);

	static void getParameters(const ExecutionContext & tpTargetEC,
			InstanceOfData::Table & testPurposeParameters);

	static void getInitialVariablesOfParameters(const ExecutionContext & tpEC,
			Machine & tcMachine, Variable::Table & initParamVariables);

	static void getComPortVariableArguments(
			const Machine & tcMachine, const BFCode & comTrace,
			BF & tcPort, Variable::Table & varArgs, bool addUnique = true);

	static void comParametersFromEC(
			const ExecutionContext & tpEC, InstanceOfData::Table & comParams);

	static BFCode tpTrace_to_tcStatement(
			const Machine & tcMachine, const BFCode & comTrace);

//	static void getComPortParametertsArguments(
//			const Machine & tcMachine, const BFCode & comTrace,
//			BF & tcPort, AvmCode::OperandCollectionT & paramArgs);
//
//	static BFCode tpTrace_to_tcIncFailStatement(
//			const Machine & tcMachine, const BFCode & comTrace);


	/////////////////////////////////////////
	// Substitution
	/////////////////////////////////////////

	static BF substitution(const BF & anExpression,
			const BF & oldTerm, const BF & newTerm);

//	static BF substitution(const ExecutionData & varTC_subst_mParamTP_ED,
//			const BF & anExpression, const BF & oldTerm, const BF & newTerm);

	/////////////////////////////////////////
	// Fresh variables of EC
	/////////////////////////////////////////

	static const BF & newfreshDurationVarOfEC(
			const ExecutionContext & anEC, const Machine & tcMachine);
	static const BF & newfreshDurationVarFromEC(
			const ExecutionContext & tpEC, const Machine & tcMachine);

	static void newfreshDurationVarsOfEC(const ExecutionContext & anEC,
			const Machine & tcMachine, Variable::Table & tcVars);
	static void newfreshDurationVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars);

	static void newfreshInputVarsOfEC(const ExecutionContext & anEC,
			const Machine & tcMachine, Variable::Table & tcVars);
	static void newfreshInputVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars);

	static void newfreshOutputVarsOfEC(const ExecutionContext & anEC,
			const Machine & tcMachine, Variable::Table & tcVars);
	static void newfreshOutputVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars);

	static void newfreshInoutVarsOfEC(const ExecutionContext & anEC,
			const Machine & tcMachine, Variable::Table & tcVars);
	static void newfreshInoutVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars);


	/////////////////////////////////////////
	// Fresh variables of trace to EC
	/////////////////////////////////////////

	static inline void newfreshTraceDurationVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars)
	{
		const ExecutionContext * pEC = & tpEC;
		while( pEC != nullptr )
		{
			newfreshDurationVarsFromEC(*pEC, tcMachine, tcVars);
			pEC = pEC->getContainer();
		}
	}

	static inline void newfreshTraceInputVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars)
	{
		const ExecutionContext * pEC = & tpEC;
		while( pEC != nullptr )
		{
			newfreshInputVarsFromEC(*pEC, tcMachine, tcVars);
			pEC = pEC->getContainer();
		}
	}

	static inline void newfreshTraceOutputVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars)
	{
		const ExecutionContext * pEC = & tpEC;
		while( pEC != nullptr )
		{
			newfreshOutputVarsFromEC(*pEC, tcMachine, tcVars);
			pEC = pEC->getContainer();
		}
	}

	static inline void newfreshTraceInoutVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars)
	{
		const ExecutionContext * pEC = & tpEC;
		while( pEC != nullptr )
		{
			newfreshInoutVarsFromEC(*pEC, tcMachine, tcVars);

			pEC = pEC->getContainer();
		}
	}

	static inline void newfreshTraceVarsFromEC(const ExecutionContext & tpEC,
			const Machine & tcMachine, Variable::Table & tcVars)
	{
		const ExecutionContext * pEC = & tpEC;
		while( pEC != nullptr )
		{
			newfreshDurationVarsFromEC(*pEC, tcMachine, tcVars);
			newfreshInoutVarsFromEC(*pEC, tcMachine, tcVars);

			pEC = pEC->getContainer();
		}
	}

	/////////////////////////////////////////
	// Newfresh parameters of EC
	/////////////////////////////////////////

	static void getInitialParameters(const ExecutionContext & tpEC,
			InstanceOfData::Table & initParamVariables);

	static const BF & newfreshDurationParamOfEC(const ExecutionContext & anEC);
	static const BF & newfreshDurationParamFromEC(const ExecutionContext & tpEC);

	static void newfreshDurationParamsOfEC(const ExecutionContext & anEC,
			InstanceOfData::Table & freshParameters);
	static void newfreshDurationParamsFromEC(const ExecutionContext & tpEC,
			InstanceOfData::Table & freshParameters);

	static void newfreshOutputParamsOfEC(const ExecutionContext & anEC,
			InstanceOfData::Table & freshParameters);
	static void newfreshOutputParamsFromEC(const ExecutionContext & tpEC,
			InstanceOfData::Table & freshParameters);


	static void newfreshInoutParamsOfEC(const ExecutionContext & anEC,
			InstanceOfData::Table & freshParameters);
	static void newfreshInoutParamsFromEC(const ExecutionContext & tpEC,
			InstanceOfData::Table & freshParameters);

	static void newfreshTraceParamsFromEC(const ExecutionContext & tpEC,
			InstanceOfData::Table & tcInoutParams,
			InstanceOfData::Table & tcClockParams);

	////////////////////////////////////////////////////////////////////////////
	// CONDITION / GUARD SIMPLIFICATION
	////////////////////////////////////////////////////////////////////////////

	static BF existsExpr(const AvmCode::OperandCollectionT & boundVars,
			const BF & formula, bool enableSimplification);

	static BF forallExpr(const AvmCode::OperandCollectionT & boundVars,
			const BF & formula, bool enableSimplification);


	static bool containseParameter(const BF & condition, const BF & aParameter);

	static bool containsSomeParameter(const BF & condition,
			const std::vector<BF> & newfreshParamsAtHeight);

	static bool containsSomeParameter(
			AvmCode::OperandCollectionT & guardClauses,
			const std::vector<BF> & newfreshParamsAtHeight);

};


} /* namespace sep */

#endif /* AVM_TESTCASE_UTILS_H_ */
