/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 juil. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_CONNECTOR_END_H_
#define FML_INFRASTRUCTURE_CONNECTOR_END_H_

#include <common/Element.h>
#include <fml/infrastructure/ComProtocol.h>
#include <fml/common/TraceableElement.h>

#include <common/AvmPointer.h>
#include <common/BF.h>

#include <fml/common/ObjectElement.h>

#include <fml/lib/AvmLang.h>
#include <fml/lib/IComPoint.h>


namespace sep
{

class Machine;
class Port;


class ComPoint :
		public Element,
		public ComProtocol,
		public TraceableElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ComPoint )
{

	AVM_DECLARE_CLONABLE_CLASS( ComPoint )


protected:
	/**
	 * ATTRIBUTES
	 */
	Machine * mMachine;
	Port    * mPort;

	BF mMachinePortQualifiedNameID;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ComPoint()
	: Element( CLASS_KIND_T( ComPoint ) ),
	ComProtocol( PROTOCOL_UNDEFINED_KIND ),
	TraceableElement( ),
	mMachine( NULL ),
	mPort( NULL ),
	mMachinePortQualifiedNameID( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ComPoint()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mMachine
	 */
	inline Machine * getMachine()
	{
		return( mMachine );
	}

	inline bool hasMachine()
	{
		return( mMachine != NULL );
	}

	inline void setMachine(Machine * aMachine)
	{
		mMachine = aMachine;
	}


	/**
	 * GETTER - SETTER
	 * mPort
	 */
	inline Port * getPort() const
	{
		return( mPort );
	}

	inline bool hasPort()
	{
		return( mPort != NULL );
	}


	/**
	 * SETTER
	 * mMachine
	 * mPort
	 */
	inline void setMachinePort(Machine * aMachine, Port * aPort)
	{
		mMachine = aMachine;

		mPort = aPort;
	}


	/**
	 * GETTER - SETTER
	 * mMachinePortQualifiedNameID
	 */
	inline BF & getMachinePortQualifiedNameID()
	{
		return( mMachinePortQualifiedNameID );
	}

	inline bool hasMachinePortQualifiedNameID()
	{
		return( mMachinePortQualifiedNameID.valid() );
	}

	inline void setMachinePort(const BF & bf)
	{
		mMachinePortQualifiedNameID = bf;
	}


	inline bool isMachineAllPort()
	{
		return( mMachinePortQualifiedNameID == XLIA_SYNTAX::ID_ALL );
	}

	inline void setMachineAllSignal(Machine * aMachine)
	{
		mMachine = aMachine;
		mMachinePortQualifiedNameID = XLIA_SYNTAX::ID_ALL;
	}


	/**
	 * Serialization
	 */
	inline virtual std::string str() const
	{
		StringOutStream oss( AVM_NO_INDENT );

		toStream( oss );

		return( oss.str() );
	}

	void toStream(OutStream & out) const;

};


} /* namespace sep */

#endif /* FML_INFRASTRUCTURE_CONNECTOR_END_H_ */
