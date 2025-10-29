/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TTCNTITANTRACEFORMATTER_H_
#define TTCNTITANTRACEFORMATTER_H_

#include "TTCNBaseTraceFormatter.h"

#include <fml/type/BaseTypeSpecifier.h>

#include <printer/OutStream.h>

#include <util/avm_numeric.h>


namespace sep
{


class AvmTraceGenerator;

class BF;

class ExecutionData;

class InstanceOfData;

class TraceManager;
class TracePoint;
class TraceSequence;


class TTCNTitanTraceFormatter final :  public TTCNBaseTraceFormatter
{

public:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::string & DEFAULT_ENVIRONMENT_CHANNEL;

	static const std::string & DEFAULT_TESTCASES_STARTING_WRAPPER;

	static const std::string & DEFAULT_TESTCASES_ENDING_WRAPPER;

	static const std::string & DEFAULT_TESTCASES_STARTING_ENDING_IMPL;


	static const std::string & DEFAULT_TESTCASES_SENDING_WRAPPER;

	static const std::string & DEFAULT_TESTCASES_SENDING_IMPL;


	static const std::string & DEFAULT_TESTCASES_RECEIVING_WRAPPER;

	static const std::string & DEFAULT_TESTCASES_RECEIVING_IMPL;


	static const std::string & DEFAULT_ADAPTATION_UTILS_IMPL;



protected:
	/**
	 * ATTRIBUTES
	 */
	std::string mDeclarationsModuleName;
	std::string mTemplatesModuleName;
	std::string mAdaptationModuleName;
	std::string mTestcasesModuleName;
	std::string mControlModuleName;

	std::string mTestcasesStartingWrapper;
	std::string mTestcasesEndingWrapper;
	std::string mTestcasesSendingWrapper;
	std::string mTestcasesReceivingWrapper;

	std::string mAdaptationUtilsImpl;
	std::string mAdaptationStartingEndingImpl;
	std::string mAdaptationSendingImpl;
	std::string mAdaptationReceivingImpl;

	bool mUseMessageTemplateWithParameters;
	bool mUseMessageFunctionWithParameters;

	StringOutStream outModuleDeclaration;
	StringOutStream outModuleTemplate;
	StringOutStream outModuleAdaptation;
	StringOutStream outModuleTestsAndControl;
	StringOutStream outModuleControlPart;


	StringOutStream channelsDeclaration;

	SetOfString setofAdaptationPortFunction;

	StringOutStream ossTemplateList;
	StringOutStream ossAdaptationList;
	StringOutStream ossTestcaseList;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TTCNTitanTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: TTCNBaseTraceFormatter( aTraceGenerator ),
	mDeclarationsModuleName( "TTCN_Declarations" ),
	mTemplatesModuleName( "TTCN_Templates" ),
	mAdaptationModuleName( "TTCN_Adaptation" ),
	mTestcasesModuleName( "TTCN_TestsAndControl" ),
	mControlModuleName( "TTCN_ControlPart" ),

	mTestcasesStartingWrapper ( DEFAULT_TESTCASES_STARTING_WRAPPER  ),
	mTestcasesEndingWrapper   ( DEFAULT_TESTCASES_ENDING_WRAPPER    ),
	mTestcasesSendingWrapper  ( DEFAULT_TESTCASES_SENDING_WRAPPER   ),
	mTestcasesReceivingWrapper( DEFAULT_TESTCASES_RECEIVING_WRAPPER ),

	mAdaptationUtilsImpl( DEFAULT_ADAPTATION_UTILS_IMPL ),

	mAdaptationStartingEndingImpl( DEFAULT_TESTCASES_STARTING_ENDING_IMPL ),
	mAdaptationSendingImpl( DEFAULT_TESTCASES_SENDING_IMPL ),
	mAdaptationReceivingImpl( DEFAULT_TESTCASES_RECEIVING_IMPL ),

	mUseMessageTemplateWithParameters( false ),
	mUseMessageFunctionWithParameters( false ),

	outModuleDeclaration( AVM_TAB1_INDENT ),
	outModuleTemplate( AVM_TAB1_INDENT ),
	outModuleAdaptation( AVM_TAB1_INDENT ),
	outModuleTestsAndControl( AVM_TAB1_INDENT ),
	outModuleControlPart( AVM_TAB1_INDENT ),

	channelsDeclaration( AVM_TAB1_INDENT ),

	setofAdaptationPortFunction( ),

	ossTemplateList( AVM_TAB1_INDENT ),
	ossAdaptationList( AVM_TAB1_INDENT ),
	ossTestcaseList( AVM_TAB1_INDENT )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TTCNTitanTraceFormatter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl(const WObject * wfParameterObject) override;


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API

	////////////////////////////////////////////////////////////////////////////

	virtual void format(TraceManager & aTraceManager) override;

	virtual void formatTraceManager(const TraceManager & aTraceManager) override;

	virtual void formatTracePointImpl(const TracePoint & aTracePoint) override;

	void formatModuleDeclarationsHeader(OutStream & out);
	void formatModuleDeclarationsEnd(OutStream & out);

	void formatModuleTemplatesHeader(OutStream & out);
	void formatModuleTemplatesEnd(OutStream & out);

	void formatModuleAdaptationHeader(OutStream & out);
	void formatModuleAdaptationEnd(OutStream & out);


	void formatModuleTestsAndControlHeader(OutStream & out);
	void formatModuleTestsAndControlEnd(OutStream & out);

	void formatModuleTestsAndControlTestcaseHeader(
			OutStream & out, const std::string & testcaseName);
	void formatModuleTestsAndControlTestcaseEnd(OutStream & out);

	void formatModuleControlPartHeader(OutStream & out);
	void formatModuleControlPartEnd(OutStream & out);
	void formatModuleControlPartBody(
			OutStream & out, const std::string & testcaseName);

	virtual void formatTestcase(
			StringOutStream & outTemplateMessageParameterName,
			StringOutStream & outTemplateParameters,
			const TracePoint & aTracePoint) override;

};


} /* namespace sep */

#endif /* TTCNTITANTRACEFORMATTER_H_ */
