/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_API_COMPOSITE_CONTROLLER_UNIT_H_
#define FAM_API_COMPOSITE_CONTROLLER_UNIT_H_

#include  <famcore/api/AbstractProcessorUnit.h>
#include <collection/List.h>


namespace sep
{

class ExecutionContext;
class IProcessorUnitRegistration;
class Operator;
class SymbexControllerUnitManager;


class CompositeControllerUnit :
		public AbstractProcessorUnit ,
		public List< AbstractProcessorUnit * >
{

	AVM_DECLARE_CLONABLE_CLASS( CompositeControllerUnit )


private:
	/**
	 * PROCESSOR FACTORY
	 * for instantiation reason
	 * AbstractProcessorUnit::REGISTER_TOOL() is a pure virtual method
	 */
	virtual IProcessorUnitRegistration & REGISTER_TOOL() const override;


protected:
	/**
	 * TYPEDEF
	 */
	typedef List< AbstractProcessorUnit * > ListOfControllerUnits;

	typedef ListOfControllerUnits::iterator        iterator;
	typedef ListOfControllerUnits::const_iterator  const_iterator;

	/**
	 * ATTRIBUTE
	 */
	const Operator * theOperator;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	iterator processorIt;
	iterator processorItEnd;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompositeControllerUnit(
			SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject = nullptr);

	/**
	 * DESTRUCTOR
	 */
	virtual ~CompositeControllerUnit()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE  API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool configure() override
	{
		return true;
	}

	inline virtual bool configureImpl() override
	{
		return true;
	}

	bool configureControllerUnits();


	////////////////////////////////////////////////////////////////////////////
	// REGISTER FOMAL ANALYSIS MODULE a.k.a. CONTROLLER UNIT  API
	////////////////////////////////////////////////////////////////////////////

	inline void addControllerUnit(AbstractProcessorUnit * aProcessor)
	{
		ListOfControllerUnits::add_unique(aProcessor);
	}

	inline void appendControllerUnit(AbstractProcessorUnit * aProcessor)
	{
		ListOfControllerUnits::append(aProcessor);
	}


	AbstractProcessorUnit * getControllerUnit(
			const IProcessorUnitRegistration & aRegisterTool);

	AbstractProcessorUnit * getControllerUnit(
			const WObject * wfProcessorObject);

	AbstractProcessorUnit * getControllerUnit(
			const std::string & aFullyQualifiedNameID);


	bool registerPreprocessor(AbstractProcessorUnit * aFAM);

	bool registerPostprocessor(AbstractProcessorUnit * aFAM);

	bool registerPrefilter(AbstractProcessorUnit * aFAM);

	bool registerPostfilter(AbstractProcessorUnit * aFAM);


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool initImpl() override;

	virtual bool exitImpl() override;


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) PROCESS  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess() override;

	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FILTERING  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize() override;

	virtual bool filteringFinalize() override;


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) FILTER  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool prefilter() override;

	// Due to [-Woverloaded-virtual=]
	using AbstractProcessorUnit::prefilter;

	virtual bool postfilter() override;

	// Due to [-Woverloaded-virtual=]
	using AbstractProcessorUnit::postfilter;


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API :> RELEASE
	////////////////////////////////////////////////////////////////////////////

	inline virtual void handleRequestRelease(AbstractProcessorUnit * aRequestor)
	{
		ListOfControllerUnits::remove( aRequestor );
	}

	// Due to [-Woverloaded-virtual=]
	using AbstractProcessorUnit::handleRequestRelease;


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void report(OutStream & os) const override
	{
		//!! NOTHING
	}

	// Due to [-Woverloaded-virtual=]
	using AbstractProcessorUnit::report;


	////////////////////////////////////////////////////////////////////////////
	// UNIT TEST API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void tddUnitReport(OutStream & os) const override
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void tddRegressionReport(OutStream & os) const override
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	void toStream(OutStream & os) const override
	{
		toStream(os, "");
	}

	void toStream(OutStream & os, const std::string & header) const;

};


} /* namespace sep */

#endif /* FAM_API_COMPOSITE_CONTROLLER_UNIT_H_ */
