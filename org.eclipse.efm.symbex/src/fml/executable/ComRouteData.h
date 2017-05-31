/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 oct. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMROUTEDATA_H_
#define COMROUTEDATA_H_

#include <common/AvmPointer.h>

#include <collection/Typedef.h>

#include <fml/lib/IComPoint.h>

#include <fml/executable/BaseCompiledForm.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/Connector.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 * TYPEDEF
 * Pair
 * InstanceOfMachine
 * InstanceOfPort
 */
typedef Pair< InstanceOfMachine * , InstanceOfPort * >  PairMachinePort;

DEFINE_LIST_PTR( PairMachinePort )

DEFINE_VECTOR_PTR( PairMachinePort )


class ComRouteData :
		public BaseCompiledForm,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ComRouteData )
{

	AVM_DECLARE_CLONABLE_CLASS( ComRouteData )


protected:
	/*
	 * ATTRIBUTES
	 */
	// The list of OUTPUT Port
	VectorOfPairMachinePort mMachinePorts;

	ComProtocol::PROTOCOL_KIND mCast;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ComRouteData(const Connector * aConnector,
			Modifier::DIRECTION_KIND ioDirection)
	: BaseCompiledForm( CLASS_KIND_T( ComRouteData ) , NULL, aConnector ),
	mMachinePorts( ),
	mCast( ComProtocol::PROTOCOL_UNDEFINED_KIND )
	{
		getwModifier().setDirectionKind( ioDirection );
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ComRouteData(const ComRouteData & aCRD)
	: BaseCompiledForm( aCRD ),
	mMachinePorts( aCRD.mMachinePorts ),
	mCast( aCRD.mCast )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ComRouteData()
	{
		//!! NOTHING
	}


	/**
	 * SETTER
	 * mUFI
	 * mID
	 */
	virtual void updateFullyQualifiedNameID()
	{
		if( hasAstElement() )
		{
			std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();

			std::string::size_type pos =
					aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
			if( pos != std::string::npos )
			{
				setFullyQualifiedNameID(
						"com" + aFullyQualifiedNameID.substr(pos) );
			}
			else
			{
				setFullyQualifiedNameID( aFullyQualifiedNameID );
			}
		}
		else
		{
			setFullyQualifiedNameID("");
		}

		updateNameID();
	}


	/**
	 * GETTER - SETTER
	 * mCast
	 */
	inline ComProtocol::PROTOCOL_KIND getCast() const
	{
		return( mCast );
	}

	inline bool hasCast() const
	{
		return( mCast != ComProtocol::PROTOCOL_UNDEFINED_KIND );
	}

	inline void setCast(ComProtocol::PROTOCOL_KIND aCast)
	{
		mCast = aCast;
	}


	/**
	 * GETTER - SETTER
	 * mMachinePorts
	 */
	inline VectorOfPairMachinePort & getMachinePorts()
	{
		return( mMachinePorts );
	}

	inline const VectorOfPairMachinePort & getMachinePorts() const
	{
		return( mMachinePorts );
	}

	inline bool hasMachinePorts() const
	{
		return( mMachinePorts.nonempty() );
	}

	inline void appendMachinePort(PairMachinePort & aMachinePort)
	{
		mMachinePorts.append(&aMachinePort);
	}

	inline void appendMachinePort(
			InstanceOfMachine * aMachine, InstanceOfPort * aPort)
	{
		mMachinePorts.append(new PairMachinePort(aMachine, aPort));
	}


	/**
	 * Serialization
	 */
	inline void strHeader(OutStream & out) const
	{
		out << str_indent( this );
	}

	void toStream(OutStream & out) const;

};


} /* namespace sep */

#endif /* COMROUTEDATA_H_ */
