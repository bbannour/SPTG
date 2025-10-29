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

#ifndef FAM_TRACE_TTCNBASETRACEFORMATTER_H_
#define FAM_TRACE_TTCNBASETRACEFORMATTER_H_

#include "AbstractTraceFormatter.h"

#include <collection/BFContainer.h>
#include <collection/Set.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <util/avm_numeric.h>

#include <map>


namespace sep
{

class AvmTraceGenerator;

class BF;

class ExecutionContext;

class InstanceOfData;

class TraceManager;
class TracePoint;
class TraceSequence;

class WObject;


class TTCNBaseTraceFormatter :  public AbstractTraceFormatter
{

public:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::string & DATA_TYPE_NAME_FORMAT;


	static const std::string & PORT_TYPE_NAME_FORMAT;

	static const std::string & PORT_INSTANCE_NAME_FORMAT;


	static const std::string & MESSAGE_TYPE_NAME_FORMAT;


	static const std::string & TEMPLATE_VALUE_NAME_FORMAT;


	static const std::string & TEMPLATE_FUNCTION_NAME_FORMAT;

	static const std::string & TEMPLATE_PARAMETRIZED_NAME_FORMAT;


	static const std::string & TESTCASE_NAME_FORMAT;



protected:
	/**
	 * TYPEDEF
	 */
	typedef Set< std::string >                 SetOfString;
	typedef Set< std::string >::const_iterator SetStringIterator;

	typedef Set< const InstanceOfPort * >                 SetOfChannel;
	typedef Set< const InstanceOfPort * >::const_iterator SetOfChannelIterator;


	/**
	 * ATTRIBUTES
	 */
	std::string mDataTypeNameFormat;

	std::string mPortTypeNameFormat;
	std::string mPortInstanceNameFormat;

	std::string mMessageTypeNameFormat;

	std::string mTemplateValueNameFormat;

	std::string mTemplateFunctionNameFormat;
	std::string mTemplateParametrizedNameFormat;

	std::string mTestcaseNameFormat;

	std::string mSystemNameID;

	const TracePoint * mCurrentTracePoint;
	const TraceSequence * mCurrentTraceSequence;

	std::string mTemplatesPortMessageAnonymParameterPrefix;
	std::string mTemplatesPortMessageArgumentParameterPrefix;

	SetOfString setofTracePointObjectName;

	Set< const ExecutionContext * > setofExecutionContext4CoverageInfo;
	BFList mCoverageInfoTraceabilitySequence;

	Set< const BaseTypeSpecifier * > setofTreatedType;
	SetOfString setofTreatedTypeName;
	std::map< std::string , std::string > mapofTreatedTypeName;

	SetOfChannel setofCommunicationgChannel;

	StringOutStream outDeclarationTypedefBuffer;

	StringOutStream outPortInstanceDeclarationBuffer;

	StringOutStream outPortInstanceMappingToSystemBuffer;
	StringOutStream outPortInstanceUnmappingToSystemBuffer;

	StringOutStream outChannelDefinitionBuffer;

	StringOutStream outDeclarationMessageRecordBuffer;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TTCNBaseTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: AbstractTraceFormatter( aTraceGenerator ),
	mDataTypeNameFormat( DATA_TYPE_NAME_FORMAT ),

	mPortTypeNameFormat( PORT_TYPE_NAME_FORMAT ),
	mPortInstanceNameFormat( PORT_INSTANCE_NAME_FORMAT ),

	mMessageTypeNameFormat( MESSAGE_TYPE_NAME_FORMAT ),

	mTemplateValueNameFormat( TEMPLATE_VALUE_NAME_FORMAT ),

	mTemplateFunctionNameFormat( TEMPLATE_FUNCTION_NAME_FORMAT ),
	mTemplateParametrizedNameFormat( TEMPLATE_PARAMETRIZED_NAME_FORMAT ),

	mTestcaseNameFormat( TESTCASE_NAME_FORMAT ),

	mSystemNameID( ),

	mCurrentTracePoint( nullptr ),
	mCurrentTraceSequence( nullptr ),

	mTemplatesPortMessageAnonymParameterPrefix( "param" ),
	mTemplatesPortMessageArgumentParameterPrefix( "p" ),

	setofTracePointObjectName( ),

	setofExecutionContext4CoverageInfo( ),
	mCoverageInfoTraceabilitySequence( ),

	setofTreatedType( ),
	setofTreatedTypeName( ),
	mapofTreatedTypeName( ),
	setofCommunicationgChannel( ),

	outDeclarationTypedefBuffer( AVM_TAB1_INDENT ),
	outPortInstanceDeclarationBuffer( AVM_TAB1_INDENT ),

	outPortInstanceMappingToSystemBuffer( AVM_TAB1_INDENT ),
	outPortInstanceUnmappingToSystemBuffer( AVM_TAB1_INDENT ),

	outChannelDefinitionBuffer( AVM_TAB1_INDENT ),

	outDeclarationMessageRecordBuffer( AVM_TAB1_INDENT )

	{
		//!! NOTHING

	}
	virtual ~TTCNBaseTraceFormatter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl(const WObject * wfParameterObject) override;

	bool configureFormatter(
			const WObject * FORMAT, std::string & formatPattern,
			const std::string & id, bool isRegex = false);


	/**
	 * FORMAT TTCN-3 API
	 */
	inline virtual void formatHeader(OutStream & os) override
	{
		//!! NOTHING
	}

	inline virtual void formatTrace(
			OutStream & os, const TraceSequence & aTraceElt) override
	{
		//!! NOTHING
	}

	inline virtual void formatFooter(OutStream & os) override
	{
		//!! NOTHING
	}


	virtual void formatTraceManager(const TraceManager  & aTraceManager) = 0;

	virtual void formatTraceSequence(const TraceSequence & aTraceSequence);

	virtual void formatTracePoint(const TracePoint & aTracePoint);

	virtual void formatTracePointImpl(const TracePoint & aTracePoint) = 0;

	/**
	 * COVERAGE TRACEABILITY
	 */
	void collectTraceCoverageInfo(const TracePoint & aTracePoint);

	void formatTestcaseCoverageInfo(OutStream & out);


	/**
	 * COMMON UTILS
	 */
	std::string ttcnTypename(const BaseTypeSpecifier & aTS);


	OutStream & dataTypeName(OutStream & out,
			const std::string & aTypename) const;

	inline std::string dataTypeName(const std::string & aTypename) const
	{
		StringOutStream outName;

		dataTypeName(outName, aTypename);

		return( outName.str() );
	}

	OutStream & dataTypeName(OutStream & out,
			const BaseTypeSpecifier & aTS) const;

	inline std::string dataTypeName(const BaseTypeSpecifier & aTS) const
	{
		StringOutStream outName;

		dataTypeName(outName, aTS);

		return( outName.str() );
	}


	OutStream & portTypeName(
			OutStream & out, const InstanceOfPort & aPort) const;

	inline std::string portTypeName(const InstanceOfPort & aPort) const
	{
		StringOutStream outName;

		portTypeName(outName, aPort);

		return( outName.str() );
	}

	OutStream & portInstanceName(
			OutStream & out, const InstanceOfPort & aPort) const;

	inline std::string portInstanceName(const InstanceOfPort & aPort) const
	{
		StringOutStream outName;

		portInstanceName(outName, aPort);

		return( outName.str() );
	}


	OutStream & messageTypeName(
			OutStream & out, const InstanceOfPort & aPort) const;

	inline std::string messageTypeName(const InstanceOfPort & aPort) const
	{
		StringOutStream outName;

		messageTypeName(outName, aPort);

		return( outName.str() );
	}


	OutStream & formatTemplateValueName(
			OutStream & out, const TracePoint & aTracePoint) const;

	inline std::string formatTemplateValueName(
			const TracePoint & aTracePoint) const
	{
		StringOutStream outName;

		formatTemplateValueName(outName, aTracePoint);

		return( outName.str() );
	}


	OutStream & formatTemplateParametrizedName(
			OutStream & out, const TracePoint & aTracePoint)const;

	inline std::string formatTemplateParametrizedName(
			const TracePoint & aTracePoint) const
	{
		StringOutStream outName;

		formatTemplateParametrizedName(outName, aTracePoint);

		return( outName.str() );
	}


	OutStream & formatTemplateFunctionName(
			OutStream & out, const TracePoint & aTracePoint) const;

	inline std::string formatTemplateFunctionName(
			const TracePoint & aTracePoint) const
	{
		StringOutStream outName;

		formatTemplateFunctionName(outName, aTracePoint);

		return( outName.str() );
	}


	OutStream & formatTestcaseName(
			OutStream & out, const TraceSequence & aTraceSequence) const;

	inline std::string formatTestcaseName(
			const TraceSequence & aTraceSequence) const
	{
		StringOutStream outName;

		formatTestcaseName(outName, aTraceSequence);

		return( outName.str() );
	}


	/**
	 * USED TYPE DEFINITION
	 */
	void formatDeclarationTypedef(
			OutStream & out, const TracePoint & aTracePoint,
			const BaseTypeSpecifier & aTS, const std::string & typeName);

	inline void formatDeclarationTypedef(OutStream & out,
			const TracePoint & aTracePoint, const BaseTypeSpecifier & aTS)
	{
		return( formatDeclarationTypedef(out, aTracePoint, aTS, aTS.strT()) );
	}

	/**
	 * COMMUNICATING CHANNEL DECLARATIONS
	 */
	void formatDeclarationChannels();

	void collectDeclarationCommunicatingChannel(const TracePoint & aTracePoint);

	/**
	 * COMMUNICATING MESSAGE-RECORD DECLARATIONS
	 */
	void formatDeclaration(const TracePoint & aTracePoint);

	void formatDeclarationCommunicatingMessage(OutStream & out,
			OutStream & outTypedefBuffer, const TracePoint & aTracePoint);

	void formatDeclarationConstant(
			OutStream & out, const TracePoint & aTracePoint,
			const InstanceOfData & paramConstant);


	/**
	 * MESSAGE TEMPLATE WITHOUT PARAMETERS
	 */
	void formatTemplateWithoutParameters(
			OutStream & out, const TracePoint & aTracePoint);

	void formatTemplateWithoutParameters(OutStream & out,
			const BF & value, const BaseTypeSpecifier & aTS,
			const std::string & aParamName, std::size_t anOffset);

	void formatTestcaseWithTemplateWithoutParameters(OutStream & out,
			const TracePoint & aTracePoint, bool isFirstTime4Object);


	/**
	 * MESSAGE TEMPLATE / FUNCTION WITH PARAMETERS
	 */
	void formatTestcaseWithTemplateWithParameters(OutStream & out,
			const TracePoint & aTracePoint, bool isFirstTime4Object);

	/**
	 * MESSAGE TEMPLATE / FUNCTION WITH PARAMETERS
	 */
	void formatTestcaseWithTemplateFunctionWithParameters(OutStream & out,
			const TracePoint & aTracePoint, bool isFirstTime4Object);


	/**
	 * MESSAGE TEMPLATE / FUNCTION PARAMETERS VALUE
	 */
	void formatTemplatesParametersValue(OutStream & out,
			const BaseTypeSpecifier & aTS,
			const BF & value, std::size_t anOffset);


	virtual void formatTestcase(StringOutStream & outTemplateName,
			StringOutStream & outTemplateParameters,
			const TracePoint & aTracePoint) = 0;


};

} /* namespace sep */

#endif /* FAM_TRACE_TTCNBASETRACEFORMATTER_H_ */
