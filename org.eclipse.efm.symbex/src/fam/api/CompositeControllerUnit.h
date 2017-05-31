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

#include <fam/api/AbstractProcessorUnit.h>
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
	virtual IProcessorUnitRegistration & REGISTER_TOOL() const;


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
	Operator * theOperator;

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
			WObject * wfParameterObject = NULL);

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

	inline virtual bool configure()
	{
		return true;
	}

	inline virtual bool configureImpl()
	{
		return true;
	}

	bool configureControllerUnits();


	////////////////////////////////////////////////////////////////////////////
	// REGISTER FOMAL ANALYSIS MODULE a.k.a. CONTROLLER UNIT  API
	////////////////////////////////////////////////////////////////////////////

	inline void addControllerUnit(AbstractProcessorUnit * aProcessor)
	{
		ListOfControllerUnits::add_union(aProcessor);
	}

	inline void appendControllerUnit(AbstractProcessorUnit * aProcessor)
	{
		ListOfControllerUnits::append(aProcessor);
	}


	AbstractProcessorUnit * getControllerUnit(
			const IProcessorUnitRegistration & aRegisterTool);

	AbstractProcessorUnit * getControllerUnit(WObject * wfProcessorObject);

	AbstractProcessorUnit * getControllerUnit(
			const std::string & aFullyQualifiedNameID);


	bool registerPreprocessor(AbstractProcessorUnit * aFAM);

	bool registerPostprocessor(AbstractProcessorUnit * aFAM);

	bool registerPrefilter(AbstractProcessorUnit * aFAM);

	bool registerPostfilter(AbstractProcessorUnit * aFAM);


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool initImpl();

	virtual bool exitImpl();


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) PROCESS  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool preprocess();

	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// FILTERING  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize();

	virtual bool filteringFinalize();


	////////////////////////////////////////////////////////////////////////////
	// ( PRE / POST ) FILTER  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool prefilter();

	virtual bool postfilter();


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API :> RELEASE
	////////////////////////////////////////////////////////////////////////////

	inline void handleRequestRelease(AbstractProcessorUnit * aRequestor)
	{
		ListOfControllerUnits::remove( aRequestor );
	}


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void report(OutStream & os) const
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// UNIT TEST API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void tddUnitReport(OutStream & os) const
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void tddRegressionReport(OutStream & os) const
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	void toStream(OutStream & os) const
	{
		toStream(os, "");
	}

	void toStream(OutStream & os, const std::string & header) const;

};


} /* namespace sep */

#endif /* FAM_API_COMPOSITE_CONTROLLER_UNIT_H_ */
