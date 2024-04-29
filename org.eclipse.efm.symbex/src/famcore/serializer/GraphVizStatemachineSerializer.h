/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_SERIALIZER_GRAPHVIZSTATEMACHINESERIALIZER_H_
#define FAM_SERIALIZER_GRAPHVIZSTATEMACHINESERIALIZER_H_

#include  <famcore/serializer/Serializer.h>


namespace sep
{

class OutStream;
class AvmSerializerProcessor;
class Machine;
class System;
class Transition;


class GraphVizStatemachineSerializer :
		public AutoRegisteredSerializerProcessorUnit< GraphVizStatemachineSerializer >
{

	AVM_DECLARE_CLONABLE_CLASS( GraphVizStatemachineSerializer )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"serializer#model#graphviz",
			"GraphVizStatemachineSerializer")
	// end registration


protected:
	/**
	 * STATIC
	 */
	static std::string ERROR_MESSAGE;


	/**
	 * ATTRIBUTE
	 */
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
	GraphVizStatemachineSerializer(
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: RegisteredSerializerProcessorUnit(aManager, wfParameterObject,
			AVM_PRE_PROCESSING_STAGE, DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR),

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

	mStatementFlag( false ),
	mStatementAssignFlag( false ),

	mStatementComFlag( true ),
	mStatementComEnvFlag( false ),

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
	virtual ~GraphVizStatemachineSerializer()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl() override;

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & out) const override;

	/**
	 * PRE-POST PROCESSING API
	 */
	virtual bool preprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT FORMAT API
	////////////////////////////////////////////////////////////////////////////

	static void format(SymbexControllerUnitManager & aManager,
			OutStream & out, const System & aSystem);


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API
	////////////////////////////////////////////////////////////////////////////

	void dotFormat(OutStream & out, const System & aSystem);

	void dotFormatSystem(OutStream & out, const System & aSystem);

	void dotFormatMachine(OutStream & out, const Machine & aMachine);


	void dotFormatMachineModelInterface(
			OutStream & out, const Machine & aMachine);

	void dotFormatMachineCall(
			OutStream & out, const Machine & aMachine);

	void dotFormatStatemachineCall(
			OutStream & out, const Machine & aMachine);

	void dotFormatCompositeStructure(
			OutStream & out, const Machine & aMachine);
	void dotFormatStateTransitionStructure(
			OutStream & out, const Machine & aMachine);

	void dotFormatMachineDefault(
			OutStream & out, const Machine & aMachine);


	void dotFormatMachineSimpleState(
			OutStream & out, const Machine & aMachine);

	void dotFormatMachinePseudoState(
			OutStream & out, const Machine & aMachine);

	void dotFormatTransition(
			OutStream & out, const Transition & aTransition);

};


} /* namespace sep */

#endif /* FAM_SERIALIZER_GRAPHVIZSTATEMACHINESERIALIZER_H_ */
