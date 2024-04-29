/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 01 oct. 2019
 *
 * Contributors:
 *  Jose Escobedo   (CEA LIST) jose.escobedo@cea.fr
 *  Mathilde Arnaud (CEA LIST) mathilde.arnaud@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAMSC_TESTING_OFFLINETESTHELPER_H_
#define FAMSC_TESTING_OFFLINETESTHELPER_H_

#include <string>


namespace sep
{

class BF;

class OfflineTestProcessor;

class TraceFactory;
class TraceSequence;

class OfflineTestHelper
{

protected:
	/**
	 * ATTRIBUTES
	 */
	const OfflineTestProcessor & mProcessorUnit;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	OfflineTestHelper(const OfflineTestProcessor & aProcessorUnit)
	: mProcessorUnit( aProcessorUnit )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~OfflineTestHelper()
	{
		//!! NOTHING
	}

	/*
	 * Parse FAM Configuration
	 * Utils
	 */
	bool parseMergedTrace(const std::string & filePath,
			TraceSequence & aTrace, const BF & theTimeVar);

	bool parseMergedTrace(
			TraceFactory & aTraceFactory, const std::string & filePath,
			TraceSequence & aMergeTrace, const BF & theTimeVar);

	bool parseMergedTrace(TraceFactory & aTraceFactory,
			const std::string &format, const std::string & filePath,
			TraceSequence & aMergeTrace, const BF & theTimeVar);

	bool parseTestPurpose(
			const std::string & filePath, TraceSequence & testPurpose);


	/*
	 * Input/Output Trace
	 * Utils
	 */
	bool hasIOTrace(const BF & anElement);

	/*
	 * Test Purpose
	 * Utils
	 */
	bool testPurposeContainsElement(
			TraceSequence & aTestPurpose, const BF & anElement);

	/*
	 * Local Observable
	 * Utils
	 */
	void makeLocalObs(TraceSequence & anObs,
			TraceSequence & aTrace, bool timedFlag);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	void printTrace(const TraceSequence & aTrace,
			const std::string & title = "The (local) trace:",
			const std::string & tab = "\t");

};




} /* namespace sep */
#endif /* FAMSC_TESTING_OFFLINETESTHELPER_H_ */
