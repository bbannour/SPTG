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

#include "TTCNBaseTraceFormatter.h"

#include <printer/OutStream.h>

#include <util/avm_numeric.h>


namespace sep
{


class AvmTraceGenerator;

class BF;
class BaseTypeSpecifier;

class ExecutionData;

class TraceManager;
class TracePoint;


class TTCNTraceFormatter  :  public TTCNBaseTraceFormatter
{

protected:
	/**
	 * ATTRIBUTES
	 */
	bool isSDLFlag;

	bool mUseTemplateWithParameters;
	bool mUseFuctionWithParameters;

	StringOutStream outModuleDeclaration;
	StringOutStream outModuleTemplate;
	StringOutStream outModuleTestsAndControl;
	StringOutStream outModuleControlPart;

	StringOutStream portsDeclaration;

	StringOutStream channelsDeclaration;

	StringOutStream templateList;

	StringOutStream ossTestcaseList;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TTCNTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: TTCNBaseTraceFormatter( aTraceGenerator ),
	isSDLFlag( true ),

	mUseTemplateWithParameters( false ),
	mUseFuctionWithParameters( false ),

	outModuleDeclaration( AVM_TAB1_INDENT ),
	outModuleTemplate( AVM_TAB1_INDENT ),
	outModuleTestsAndControl( AVM_TAB1_INDENT ),
	outModuleControlPart( AVM_TAB1_INDENT ),

	portsDeclaration( AVM_TAB1_INDENT ),
	channelsDeclaration( AVM_TAB1_INDENT ),

	templateList( AVM_TAB1_INDENT ),

	ossTestcaseList( AVM_TAB1_INDENT )
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
	void format_TTCN_Templates(
			const BF & value, const BaseTypeSpecifier & aTS,
			const std::string & aParamName, std::size_t anOffset);

	void formatModuleTestsAndControlHeader(OutStream & out);
	void formatModuleTestsAndControlEnd(OutStream & out);

	void formatModuleTestsAndControlTestcaseHeader(
			OutStream & out, const std::string & testcaseName);
	void formatModuleTestsAndControlTestcaseEnd(OutStream & out);

	void formatModuleControlPartHeader(OutStream & out);
	void formatModuleControlPartEnd(OutStream & out);
	void formatModuleControlPartBody(
			OutStream & out, const std::string & testcaseName);

	void format_TTCN_Templates(const TracePoint & aTracePoint);


	virtual void formatTestcase(StringOutStream & outTemplateName,
			StringOutStream & outTemplateParameters,
			const TracePoint & aTracePoint) override;

};


} /* namespace sep */

#endif /* TTCNTRACEFORMATTER_H_ */
