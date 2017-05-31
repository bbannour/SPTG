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

#include "AbstractTraceFormatter.h"

#include <collection/List.h>


namespace sep
{


class AvmTraceGenerator;

class BF;
class BaseTypeSpecifier;

class ExecutionData;

class TraceManager;
class TracePoint;
class TraceSequence;


class TTCNTitanTraceFormatter  :  public AbstractTraceFormatter
{

protected:
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
	 * TYPEDEF
	 */
	typedef List< BaseTypeSpecifier * > ListOfBaseTypeSpecifier;

	typedef List< std::string >  ListOfString;


	/**
	 * ATTRIBUTES
	 */
	TraceSequence * aTraceElement;
	int traceNumber;
	int linkNumber;

	std::string systemName;

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


// !!! Modif AFA - 23/05/2016 !!!
//	ListOfInstanceOfPort listOfTreatedSignal;
	ListOfString listOfTreatedSignalName;

	ListOfBaseTypeSpecifier listOfTreatedType;

	std::ostringstream module_TTCN_Declarations;
	std::ostringstream module_TTCN_Templates;
	std::ostringstream module_TTCN_Adaptation;
	std::ostringstream module_TTCN_TestsAndControl;
	std::ostringstream module_TTCN_ControlPart;

	std::ostringstream newTypesDeclaration;

	std::ostringstream recordsDeclaration;

	std::ostringstream portsDeclaration;

	std::ostringstream channelsDefinition;
	std::ostringstream channelsDeclaration;
	ListOfString ListOfChannelName;

	ListOfString listOfAdaptationPortFunction;

	std::ostringstream ossTemplateList;
	std::ostringstream ossAdaptationList;
	std::ostringstream ossTestcaseList;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TTCNTitanTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: AbstractTraceFormatter( aTraceGenerator ),
	aTraceElement( NULL ),
	traceNumber( 1 ),
	linkNumber( 0 ),

	systemName( ),

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


// !!! Modif AFA - 23/05/2016 !!!
//	listOfTreatedSignal( ),
	listOfTreatedType( ),

	module_TTCN_Declarations( ),
	module_TTCN_Templates( ),
	module_TTCN_Adaptation( ),
	module_TTCN_TestsAndControl( ),
	module_TTCN_ControlPart( ),

	newTypesDeclaration( ),

	recordsDeclaration( ),

	portsDeclaration( ),
	channelsDefinition( ),
	channelsDeclaration( ),

	listOfAdaptationPortFunction( ),

	ossTemplateList( ),
	ossAdaptationList( ),
	ossTestcaseList( )
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

	bool configureImpl(WObject * wfParameterObject);

	bool configureFormatter(
			WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);


	////////////////////////////////////////////////////////////////////////////
	// FORMAT API

	////////////////////////////////////////////////////////////////////////////

	void format(TraceManager & aTraceManager);

	void format_impl(TraceManager & aTraceManager);


	void formatHeader_TTCN_Declarations(std::ostream & os);
	void formatEnd_TTCN_Declarations(std::ostream & os);
	void format_TTCN_Declarations(TraceSequence * aTraceElt);
	void format_TTCN_Declarations(TracePoint * aTracePoint);
	void format_TTCN_Declarations(TracePoint * aTracePoint,
			BaseTypeSpecifier * aTS, std::string typeName);

	void format_TTCN_DeclarationsChannels();

	void formatHeader_TTCN_Templates(std::ostream & os);
	void formatEnd_TTCN_Templates(std::ostream & os);
	void format_TTCN_Templates(
			const BF & value, BaseTypeSpecifier * aTS,
			std::string typeName, avm_size_t anOffset,
			const std::string & TAB, const std::string & CHAR);

	void formatHeader_TTCN_Adaptation(std::ostream & os);
	void formatEnd_TTCN_Adaptation(std::ostream & os);


	void formatHeader_TTCN_TestsAndControl(std::ostream & os);
	void formatEnd_TTCN_TestsAndControl(std::ostream & os);

	void formatHeader_TTCN_TestsAndControl_testcase(std::ostream & os);
	void formatEnd_TTCN_TestsAndControl_testcase(std::ostream & os);

	void formatHeader_TTCN_ControlPart(std::ostream & os);
	void formatEnd_TTCN_ControlPart(std::ostream & os);
	void format_TTCN_ControlPart_execute(std::ostream & os);

	void format_TTCN_Trace(TraceSequence * aTraceElt);
	void format_TTCN_Trace(TracePoint * aTracePoint);

};


} /* namespace sep */

#endif /* TTCNTITANTRACEFORMATTER_H_ */
