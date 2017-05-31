/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 févr. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASICTRACEPARSER_H_
#define BASICTRACEPARSER_H_

#include <util/avm_string.h>
#include <common/BF.h>

#include <fstream>


namespace sep
{


class Configuration;
class ITypeSpecifier;
class InstanceOfPort;
class TracePoint;
class TraceSequence;


class BasicTraceParser
{


protected:
	/**
	 * ATTRIBUTE
	 */
	const Configuration & mConfiguration;

	BF bfVarTime;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	BF  bfTP;
	TracePoint * aTracePoint;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BasicTraceParser(const Configuration & aConfiguration)
	: mConfiguration( aConfiguration ),
	bfVarTime( ),
	bfTP( ),
	aTracePoint( NULL )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BasicTraceParser()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// BASIC PARSER API
	////////////////////////////////////////////////////////////////////////////

	bool parseBasicTrace(TraceSequence & aTraceElement,
			std::ifstream & inFile, const BF & aVarTime);

	bool parseBasicTraceDuration(TraceSequence & aTraceElement,
			const std::string & inLine, const BF & aVarTime);

	bool parseBasicTraceSignal(
			TraceSequence & aTraceElement, const std::string & inLine);

	bool parseBasicTraceStructure(
			TraceSequence & aTraceElement, const std::string & inLine);

	bool parseBasicTraceSignalParameters(TracePoint * aTracePoint,
			InstanceOfPort * port, const std::string & anExpr);

	BF parseBasicTraceSignalParameter(const ITypeSpecifier & aTypeSpecifier,
			const std::string & anExpr);

// TODO : temporary, the format should be defined properly or fixed
	bool parseBasicXliaTrace(TraceSequence & aTraceElement,
			std::ifstream & inFile, const BF & aVarTime);

	bool parseBasicXliaTraceDuration(TraceSequence & aTraceElement,
			const std::string & inLine, const BF & aVarTime);

	bool parseBasicXliaTraceSignal(
			TraceSequence & aTraceElement, const std::string & inLine);
};


} /* namespace sep */

#endif /* BASICTRACEPARSER_H_ */
