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

#ifndef FML_INFRASTRUCTURE_COMPOINT_END_H_
#define FML_INFRASTRUCTURE_COMPOINT_END_H_

#include <common/Element.h>
#include <fml/infrastructure/ComProtocol.h>
#include <fml/common/TraceableElement.h>

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
	mMachine( nullptr ),
	mPort( nullptr ),
	mMachinePortQualifiedNameID( )
	{
		//!! NOTHING
	}

	ComPoint(Machine * aMachine, Port * aPort)
	: Element( CLASS_KIND_T( ComPoint ) ),
	ComProtocol( PROTOCOL_UNDEFINED_KIND ),
	TraceableElement( ),
	mMachine( aMachine ),
	mPort( aPort ),
	mMachinePortQualifiedNameID( )
	{
		//!! NOTHING
	}

	ComPoint(Machine * aMachine, const BF & aPortQualifiedNameID)
	: Element( CLASS_KIND_T( ComPoint ) ),
	ComProtocol( PROTOCOL_UNDEFINED_KIND ),
	TraceableElement( ),
	mMachine( aMachine ),
	mPort( nullptr ),
	mMachinePortQualifiedNameID( aPortQualifiedNameID )
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
	inline const Machine & getMachine() const
	{
		return( * mMachine );
	}

	inline bool hasMachine() const
	{
		return( mMachine != nullptr );
	}

	inline void setMachine(Machine * aMachine)
	{
		mMachine = aMachine;
	}

	/**
	 * GETTER - SETTER
	 * mPort
	 */
	inline const Port & getPort() const
	{
		return( * mPort );
	}

	inline bool hasPort() const
	{
		return( mPort != nullptr );
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
	inline const BF & getMachinePortQualifiedNameID() const
	{
		return( mMachinePortQualifiedNameID );
	}

	inline bool hasMachinePortQualifiedNameID() const
	{
		return( mMachinePortQualifiedNameID.valid() );
	}

	inline void setMachinePortID(const BF & bf)
	{
		mMachinePortQualifiedNameID = bf;
	}


	inline bool isMachineAllPort() const
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
	inline virtual std::string str() const override
	{
		StringOutStream oss( AVM_NO_INDENT );

		toStream( oss );

		return( oss.str() );
	}

	virtual void toStream(OutStream & out) const override;

};


} /* namespace sep */

#endif /* FML_INFRASTRUCTURE_COMPOINT_END_H_ */
