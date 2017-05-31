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
 *  Alain Faivre (CEA LIST) alain.faivre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TTCNTRACEFORMATTER_H_
#define TTCNTRACEFORMATTER_H_

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


class TTCNTraceFormatter  :  public AbstractTraceFormatter
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef List< BaseTypeSpecifier * > ListOfBaseTypeSpecifier;

	typedef List< std::string >  ListOfString;


	/**
	 * ATTRIBUTES
	 */
	bool isSDLFlag;

	TraceSequence * aTraceElement;
	int traceNumber;
	int linkNumber;

	std::string systemName;

// !!! Modif AFA - 23/05/2016 !!!
//	ListOfInstanceOfPort listOfTreatedSignal;
	ListOfString listOfTreatedSignalName;

	ListOfBaseTypeSpecifier listOfTreatedType;

	std::ostringstream module_TTCN_Declarations;
	std::ostringstream module_TTCN_Templates;
	std::ostringstream module_TTCN_TestsAndControl;
	std::ostringstream module_TTCN_ControlPart;

	std::ostringstream newTypesDeclaration;

	std::ostringstream recordsDeclaration;

	std::ostringstream portsDeclaration;

	std::ostringstream channelsDefinition;
	std::ostringstream channelsDeclaration;
	ListOfString ListOfChannelName;

	std::ostringstream templateList;

	std::ostringstream ossTestcaseList;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TTCNTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: AbstractTraceFormatter( aTraceGenerator ),
	isSDLFlag( true ),
	aTraceElement( NULL ),
	traceNumber( 1 ),
	linkNumber( 0 ),

	systemName( ),

// !!! Modif AFA - 23/05/2016 !!!
//	listOfTreatedSignal( ),
	listOfTreatedType( ),

	module_TTCN_Templates( ),
	module_TTCN_TestsAndControl( ),
	module_TTCN_ControlPart( ),

	newTypesDeclaration( ),

	recordsDeclaration( ),

	portsDeclaration( ),
	channelsDefinition( ),
	channelsDeclaration( ),

	templateList( ),

	ossTestcaseList( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TTCNTraceFormatter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configureImpl(WObject * wfParameterObject);


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


	void formatHeader_TTCN_TestsAndControl(std::ostream & os);
	void formatEnd_TTCN_TestsAndControl(std::ostream & os);

	void formatHeader_TTCN_TestsAndControl_testcase(std::ostream & os);
	void formatEnd_TTCN_TestsAndControl_testcase(std::ostream & os);

	void formatHeader_TTCN_ControlPart(std::ostream & os);
	void formatEnd_TTCN_ControlPart(std::ostream & os);
	void format_TTCN_ControlPart_execute(std::ostream & os);

	void format_TTCN_Templates(TraceSequence * aTraceElt);
	void format_TTCN_Templates(TracePoint * aTracePoint);

};


} /* namespace sep */

#endif /* TTCNTRACEFORMATTER_H_ */
