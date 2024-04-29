/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef MACHINECOVERAGEFILTER_H_
#define MACHINECOVERAGEFILTER_H_

#include <famcore/api/BaseCoverageFilter.h>

#include <collection/Bitset.h>
#include <collection/Typedef.h>

#include <fml/expression/AvmCode.h>


namespace sep
{


class RuntimeForm;
class RuntimeID;


typedef Vector< RuntimeForm * > VectorOfRuntimeForm;



class MachineCoverageFilter :
		public AutoRegisteredCoverageProcessorUnit< MachineCoverageFilter >
{

	AVM_DECLARE_CLONABLE_CLASS( MachineCoverageFilter )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"coverage#machine",
			"avm::processor.MACHINE_COVERAGE",
			"avm::core.filter.MACHINE_COVERAGE" )
	// end registration


protected:
	/**
	 * ATTRIBUTES
	 */
	std::string mScope;

	bool mStrictFlag;

	// Table des flag de couverture de transition pour chaque INSTANCE de machine
	ArrayOfBitset * mExecutableCoverageTable;
	ArrayOfBitset * mMachineCoverageTable;

	// Local Variables
	ExecutionContext::child_iterator itEC;
	ExecutionContext::child_iterator itEndEC;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MachineCoverageFilter(SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: RegisteredCoverageProcessorUnit(aManager, wfParameterObject,
			AVM_PREPOST_FILTERING_STAGE, PRECEDENCE_OF_MACHINE_COVERAGE),
	mScope(),
	mStrictFlag( false ),
	mExecutableCoverageTable( nullptr ),
	mMachineCoverageTable( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~MachineCoverageFilter();


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl() override;


	void configureExecutableCoverageTableFlag(bool value);
	void configureExecutableCoverageTableFlag(
			const ExecutableForm & anExecutable, bool value);

	void configureInstanceCoverageTableFlag();
	void configureInstanceCoverageTableFlag(bool value);
	void configureInstanceCoverageTableFlag(
			const ExecutionData & anED, const RuntimeID & aRID, bool value);

	void configureMachineCoverageTableFlag(
			const List< RuntimeID > & listOfMachine, bool value);


	/**
	 * PRE-PROCESS
	 */
	virtual bool preprocess() override;


	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const override;


	/**
	 * postEval Filter
	 */
	virtual bool postfilter(ExecutionContext & anEC) override;


	void setCoverage(ExecutionContext * anEC, avm_offset_t rid);

	void checkMachine(ExecutionContext * anEC);
	void checkMachine(ExecutionContext * anEC, const BF & aFiredCode);

	void checkMachineAfter(ExecutionContext * anEC);

};



}

#endif /* MACHINECOVERAGEFILTER_H_ */
