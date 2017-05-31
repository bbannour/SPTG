/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef INSTANCEOFCONNECT_H_
#define INSTANCEOFCONNECT_H_

#include <common/AvmPointer.h>

#include <fml/executable/BaseInstanceForm.h>

#include <collection/Typedef.h>

#include <fml/lib/IComPoint.h>

#include <fml/executable/ComRouteData.h>

#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/Connector.h>


namespace sep
{


class BaseAvmProgram;
class Connector;


class InstanceOfConnect :
		public BaseInstanceForm ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceOfConnect )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceOfConnect )


protected:
	/*
	 * ATTRIBUTES
	 */
	// The Transfert Flag
	bool mTransfertFlag;

	// The Message IDentifier
	avm_size_t mMID;

	// global ComRoute protocol & cast
	ComProtocol::PROTOCOL_KIND mProtocol;
	ComProtocol::PROTOCOL_KIND mCast;

	ComRouteData mOutputComRouteData;
	ComRouteData mInputComRouteData;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfConnect(BaseAvmProgram * aContainer, const Connector * aConnector,
			avm_offset_t anOffset, ComProtocol::PROTOCOL_KIND aProtocol,
			ComProtocol::PROTOCOL_KIND aCast);


	/**
	 * CONSTRUCTOR
	 * copy
	 */
	InstanceOfConnect(const InstanceOfConnect & aConnect)
	: BaseInstanceForm( aConnect ),
	mTransfertFlag( aConnect.mTransfertFlag ),

	mMID( aConnect.mMID ),

	mProtocol( aConnect.mProtocol ),
	mCast( aConnect.mCast ),

	mOutputComRouteData( aConnect.mOutputComRouteData ),
	mInputComRouteData( aConnect.mInputComRouteData )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfConnect(BaseAvmProgram * aContainer, InstanceOfConnect * aTarget,
			VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfConnect ),
			aContainer, aTarget, aRelativeMachinePath),
	mTransfertFlag( aTarget->mTransfertFlag ),

	mMID( aTarget->mMID ),

	mProtocol( aTarget->mProtocol ),
	mCast( aTarget->mCast ),

	mOutputComRouteData( aTarget->mOutputComRouteData ),
	mInputComRouteData( aTarget->mInputComRouteData )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceOfConnect()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled COnnector
	 */
	inline const Connector * getAstConnector() const
	{
		return( getAstElement()->as< Connector >() );
	}


	/**
	 * GETTER - SETTER
	 * mMID
	 */
	inline avm_size_t getMID() const
	{
		return( mMID );
	}

	inline void setMID(avm_size_t mid)
	{
		mMID = mid;
	}


	/**
	 * GETTER - SETTER
	 * mProtocol
	 */
	inline ComProtocol::PROTOCOL_KIND getProtocol() const
	{
		return( mProtocol );
	}

	inline bool hasProtocol() const
	{
		return( mProtocol != ComProtocol::PROTOCOL_UNDEFINED_KIND );
	}

	inline void setProtocol(ComProtocol::PROTOCOL_KIND aProtocol)
	{
		mProtocol = aProtocol;
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

	inline void setProtocolCast(ComProtocol::PROTOCOL_KIND aProtocol,
			ComProtocol::PROTOCOL_KIND aCast)
	{
		mProtocol = aProtocol;
		mCast = aCast;
	}


	/**
	 * GETTER - SETTER
	 * mOutputComRouteData
	 */
	inline ComRouteData & getOutputComRouteData()
	{
		return( mOutputComRouteData );
	}

	inline const ComRouteData & getOutputComRouteData() const
	{
		return( mOutputComRouteData );
	}

	inline bool hasOutputComRouteData() const
	{
		return( mOutputComRouteData.hasMachinePorts() );
	}

	inline void appendOutputComRouteData(PairMachinePort & aMachinePort)
	{
		mOutputComRouteData.appendMachinePort(aMachinePort);
	}

	/**
	 * GETTER - SETTER
	 * mInputComRouteData
	 */
	inline ComRouteData & getInputComRouteData()
	{
		return( mInputComRouteData );
	}

	inline const ComRouteData & getInputComRouteData() const
	{
		return( mInputComRouteData );
	}

	inline bool hasInputComRouteData() const
	{
		return( mInputComRouteData.hasMachinePorts() );
	}

	inline void appendInputComRouteData(PairMachinePort & aMachinePort)
	{
		mInputComRouteData.appendMachinePort(aMachinePort);
	}


	/**
	 * Serialization
	 */
	void strHeader(OutStream & out) const;

	void toStream(OutStream & out) const;

};


}

#endif /* INSTANCEOFCONNECT_H_ */
