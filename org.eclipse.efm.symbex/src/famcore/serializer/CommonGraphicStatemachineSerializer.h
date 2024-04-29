/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 October 2018
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_SERIALIZER_COMMON_GRAPHIC_STATEMACHINE_SERIALIZER_H_
#define FAM_SERIALIZER_COMMON_GRAPHIC_STATEMACHINE_SERIALIZER_H_


#include <string>


namespace sep
{

class OutStream;
class AvmSerializerProcessor;
class Machine;
class SymbexValueCSS;
class System;
class Transition;


class CommonGraphicStatemachineSerializer
{

protected:
	/**
	 * STATIC
	 */
	static std::string FILE_HEADER;
	static std::string FILE_FOOTER;

	static std::string ERROR_MESSAGE;

	/**
	 * ATTRIBUTE
	 */
	const SymbexValueCSS * pMultiValueArrayCSS;
	const SymbexValueCSS * pMultiValueParamsCSS;
	const SymbexValueCSS * pMultiValueStructCSS;

	bool mMachineFlag;
	bool mMachineInstanceFlag;
	bool mMachineModelFlag;
	bool mMachinePrototypeFlag;

	bool mProcedureFlag;
	bool mProgramFlag;
	bool mRoutineFlag;

	bool mStatemachineFlag;

	bool mStatemachineDisableFlag;
	bool mStatemachineEnableFlag;

	bool mTransitionFlag;
	bool mTransitionPriorityFlag;

	bool mStatementFlag;
	bool mStatementAssignFlag;

	bool mStatementComFlag;
	bool mStatementComEnvFlag;

	bool mStatementInputFlag;
	bool mStatementInputEnvFlag;

	bool mStatementOuputFlag;
	bool mStatementOuputEnvFlag;

	bool mStatementGuardFlag;
	bool mStatementTestFlag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CommonGraphicStatemachineSerializer()
	: pMultiValueArrayCSS( nullptr ),
	pMultiValueParamsCSS ( nullptr ),
	pMultiValueStructCSS ( nullptr ),

	mMachineFlag( true ),

	mMachineInstanceFlag( true ),
	mMachineModelFlag( true ),
	mMachinePrototypeFlag( true ),

	mProcedureFlag( true ),
	mProgramFlag( true ),
	mRoutineFlag( true ),
	mStatemachineFlag( true ),

	mStatemachineDisableFlag( true ),
	mStatemachineEnableFlag( true ),

	mTransitionFlag( true ),
	mTransitionPriorityFlag( false ),

	mStatementFlag( true ),
	mStatementAssignFlag( false ),

	mStatementComFlag( true ),
	mStatementComEnvFlag( true ),

	mStatementInputFlag( false ),
	mStatementInputEnvFlag( false ),

	mStatementOuputFlag( false ),
	mStatementOuputEnvFlag( false ),

	mStatementGuardFlag( false ),
	mStatementTestFlag( false )
	{
		//!! NOTHING
	}

	CommonGraphicStatemachineSerializer(const SymbexValueCSS & vac,
			const SymbexValueCSS & vpc, const SymbexValueCSS & vsc)
	: pMultiValueArrayCSS( & vac ),
	pMultiValueParamsCSS ( & vpc ),
	pMultiValueStructCSS ( & vsc ),

	mMachineFlag( true ),

	mMachineInstanceFlag( true ),
	mMachineModelFlag( true ),
	mMachinePrototypeFlag( true ),

	mProcedureFlag( true ),
	mProgramFlag( true ),
	mRoutineFlag( true ),
	mStatemachineFlag( true ),

	mStatemachineDisableFlag( true ),
	mStatemachineEnableFlag( true ),

	mTransitionFlag( true ),
	mTransitionPriorityFlag( false ),

	mStatementFlag( true ),
	mStatementAssignFlag( false ),

	mStatementComFlag( true ),
	mStatementComEnvFlag( true ),

	mStatementInputFlag( false ),
	mStatementInputEnvFlag( false ),

	mStatementOuputFlag( false ),
	mStatementOuputEnvFlag( false ),

	mStatementGuardFlag( false ),
	mStatementTestFlag( false )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~CommonGraphicStatemachineSerializer()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API
	////////////////////////////////////////////////////////////////////////////

	void format(OutStream & out, const System & aSystem);

	void formatSystem(OutStream & out, const System & aSystem);

	void formatMachine(OutStream & out, const Machine & aMachine);


	void formatMachineModelInterface(
			OutStream & out, const Machine & aMachine);

	void formatMachineCall(
			OutStream & out, const Machine & aMachine);

	void formatStatemachineCall(
			OutStream & out, const Machine & aMachine);

	void formatCompositeStructure(
			OutStream & out, const Machine & aMachine);
	void formatStateTransitionStructure(
			OutStream & out, const Machine & aMachine);

	void formatMachineDefault(
			OutStream & out, const Machine & aMachine);


	void formatMachineSimpleState(
			OutStream & out, const Machine & aMachine);

	void formatMachinePseudoState(
			OutStream & out, const Machine & aMachine);

	void formatTransition(
			OutStream & out, const Transition & aTransition);

};


} /* namespace sep */

#endif /* FAM_SERIALIZER_COMMON_GRAPHIC_STATEMACHINE_SERIALIZER_H_ */
