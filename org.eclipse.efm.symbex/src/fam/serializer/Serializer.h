/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_SERIALIZER_SERIALIZER_H_
#define FAM_SERIALIZER_SERIALIZER_H_

#include <fam/api/AbstractProcessorUnit.h>

#include <printer/OutStream.h>


namespace sep
{

class Serializer :  public AbstractProcessorUnit
{

protected:
	/**
	 * ATTRIBUTE
	 */
	static const avm_size_t  mDefaultLineWrapWidth = 42;

	WrapData mWrapData;

	bool mInfoAllFlags;
	bool mDataSelectionModifiedFlags;

	SymbexValueCSS mMultiValueArrayCSS;
	SymbexValueCSS mMultiValueParamsCSS;
	SymbexValueCSS mMultiValueStructCSS;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Serializer(SymbexControllerUnitManager & aManager, WObject * wfParameterObject,
			avm_computing_process_stage_t requiredStage,
			const avm_uint8_t * aPrecedence/* = DEFAULT_PRECEDENCE_OF_PROCESSOR*/)
	: AbstractProcessorUnit(aManager, wfParameterObject, requiredStage, aPrecedence),
	mWrapData( mDefaultLineWrapWidth , 0 , 4 ,"\n" ),

	mInfoAllFlags( true ),
	mDataSelectionModifiedFlags( true ),

	mMultiValueArrayCSS ( DEFAULT_SYMBEX_VALUE_ARRAY_CSS  ),
	mMultiValueParamsCSS( DEFAULT_SYMBEX_VALUE_PARAMS_CSS ),
	mMultiValueStructCSS( DEFAULT_SYMBEX_VALUE_STRUCT_CSS )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Serializer()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	bool configureImpl();

};


////////////////////////////////////////////////////////////////////////////////
// PROCESSOR UNIT AUTO REGISTRATION FACTORY
// for automatic registration in the processor repository
////////////////////////////////////////////////////////////////////////////////

template< class ProcessorT >
class AutoRegisteredSerializerProcessorUnit :  public  Serializer
{

public:
	/**
	 * TYPDEDEF
	 */
	typedef AutoRegisteredSerializerProcessorUnit< ProcessorT >
				RegisteredSerializerProcessorUnit;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AutoRegisteredSerializerProcessorUnit(SymbexControllerUnitManager & aManager,
			WObject * wfParameterObject, avm_computing_process_stage_t requiredStage,
			const avm_uint8_t * aPrecedence/* = DEFAULT_PRECEDENCE_OF_PROCESSOR*/)
	: Serializer(aManager, wfParameterObject, requiredStage, aPrecedence)
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AutoRegisteredSerializerProcessorUnit()
	{
		// Force Instanciate
		(void) & AUTO_REGISTER_TOOL;
	}


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 */
	static struct AutoRegisterProcessorFactory  :
			public ProcessorUnitRegistrationImpl< ProcessorT >
	{
		AutoRegisterProcessorFactory()
		: ProcessorUnitRegistrationImpl< ProcessorT >(
				ProcessorT::QNID() , ProcessorT::QNID1() ,
				ProcessorT::QNID2(), ProcessorT::QNID3() )
		{
			//!! NOTHING
		}

	}  AUTO_REGISTER_TOOL;
	// end registration


	/**
	 * API
	 */
	inline const IProcessorUnitRegistration & REGISTER_TOOL() const
	{
		return( AUTO_REGISTER_TOOL );
	}

	inline bool isRegisterTool(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( AUTO_REGISTER_TOOL.isEquals( aRegisterTool ) );
	}

};


template< class ProcessorT > typename
AutoRegisteredSerializerProcessorUnit< ProcessorT >::AutoRegisterProcessorFactory
AutoRegisteredSerializerProcessorUnit< ProcessorT >::AUTO_REGISTER_TOOL;


} /* namespace sep */

#endif /* FAM_SERIALIZER_SERIALIZER_H_ */
