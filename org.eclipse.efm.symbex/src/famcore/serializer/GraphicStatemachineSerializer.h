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

#ifndef FAM_SERIALIZER_GRAPHICSTATEMACHINESERIALIZER_H_
#define FAM_SERIALIZER_GRAPHICSTATEMACHINESERIALIZER_H_

#include  <famcore/serializer/Serializer.h>
#include  <famcore/serializer/CommonGraphicStatemachineSerializer.h>


namespace sep
{

class OutStream;
class AvmSerializerProcessor;
class Machine;
class System;
class Transition;


class GraphicStatemachineSerializer :
		public AutoRegisteredSerializerProcessorUnit< GraphicStatemachineSerializer >,
		public CommonGraphicStatemachineSerializer
{

	AVM_DECLARE_CLONABLE_CLASS( GraphicStatemachineSerializer )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"serializer#statemachine#graphic",
			"serializer#model#graphic",
			"GraphicStatemachineSerializer")
	// end registration


protected:


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	GraphicStatemachineSerializer(
			SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject)
	: RegisteredSerializerProcessorUnit(aManager, wfParameterObject,
			AVM_PRE_PROCESSING_STAGE, DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR),
	CommonGraphicStatemachineSerializer(
			mMultiValueArrayCSS, mMultiValueParamsCSS, mMultiValueStructCSS)
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~GraphicStatemachineSerializer()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl() override;

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & out) const override;

	/**
	 * PRE-POST PROCESSING API
	 */
	virtual bool preprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// DEFAULT FORMAT API
	////////////////////////////////////////////////////////////////////////////

	static void sformat(SymbexControllerUnitManager & aManager,
			OutStream & out, const System & aSystem);

};


} /* namespace sep */

#endif /* FAM_SERIALIZER_GRAPHICSTATEMACHINESERIALIZER_H_ */
