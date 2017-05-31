/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef ROUTINGDATA_H_
#define ROUTINGDATA_H_

#include <base/SmartPointer.h>
#include <common/Element.h>

#include <collection/Pair.h>
#include <collection/Vector.h>

#include <fml/lib/IComPoint.h>

#include <fml/executable/InstanceOfBuffer.h>

#include <fml/infrastructure/ComProtocol.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


class InstanceOfConnect;
class InstanceOfMachine;
class InstanceOfPort;

class RoutingData;


class RoutingDataElement :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RoutingDataElement )
{

	friend class RoutingData;

	AVM_DECLARE_CLONABLE_CLASS( RoutingDataElement )

public:
	typedef Pair < InstanceOfMachine * , InstanceOfPort * >  PairMachinePort;


protected:
	/*
	 * ATTRIBUTES
	 */
	// The Message Identifier
	avm_size_t mMID;

	// global protocol
	ComProtocol::PROTOCOL_KIND mProtocol;

	// The connector instance
	InstanceOfConnect * mConnect;

	// The concerned MACHINE and the PORT
	PairMachinePort mMachinePort;

	// list of local protocol and buffer
	ListOfInstanceOfBuffer mBufferInstance;

	// The runtime machine RID for RID access optimization
	RuntimeID mRuntimeRID;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RoutingDataElement(avm_size_t mid, InstanceOfMachine * aMachine,
			InstanceOfPort * aPort, ComProtocol::PROTOCOL_KIND aProtocol)
	: Element( CLASS_KIND_T( RoutingData ) ),
	mMID( mid ),
	mProtocol( aProtocol ),
	mConnect( NULL ),
	mMachinePort(aMachine, aPort),
	mBufferInstance( ),
	mRuntimeRID( )
	{
		//!! NOTHING
	}

	RoutingDataElement(InstanceOfConnect * aConnector,
			InstanceOfMachine * aMachine, InstanceOfPort * aPort);


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	explicit RoutingDataElement(const RoutingDataElement & anElement)
	: Element( anElement ),
	mMID( anElement.mMID ),
	mProtocol( anElement.mProtocol ),
	mConnect( anElement.mConnect ),
	mMachinePort( anElement.mMachinePort ),
	mBufferInstance( anElement.mBufferInstance ),
	mRuntimeRID( anElement.mRuntimeRID )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RoutingDataElement()
	{
		//!! NOTHING
	}

	/**
	 * GETTER
	 * mMachinePort
	 */
	inline InstanceOfMachine * getMachine() const
	{
		return( mMachinePort.first() );
	}

	inline InstanceOfPort * getPort() const
	{
		return( mMachinePort.second() );
	}

	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;

};


class RoutingData :
		public SmartPointer< RoutingDataElement , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RoutingData )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< RoutingDataElement ,
						DestroyElementPolicy >  base_this_type;

	typedef Pair < InstanceOfMachine * , InstanceOfPort * >  PairMachinePort;


public:
	/*
	 * STATIC ATTRIBUTES
	 */
	static RoutingData _NULL_;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RoutingData()
	: base_this_type( )
	{
		//!! NOTHING
	}

	RoutingData(avm_size_t mid, InstanceOfMachine * aMachine,
			InstanceOfPort * aPort, ComProtocol::PROTOCOL_KIND aProtocol)
	: base_this_type( new RoutingDataElement(mid, aMachine, aPort, aProtocol) )
	{
		//!! NOTHING
	}

	RoutingData(InstanceOfConnect * aConnector,
			InstanceOfMachine * aMachine, InstanceOfPort * aPort)
	: base_this_type( new RoutingDataElement(aConnector, aMachine, aPort) )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	RoutingData(const RoutingData & anElement)
	: base_this_type( anElement )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~RoutingData()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mMID
	 */
	inline avm_size_t getMID() const
	{
		return( base_this_type::mPTR->mMID );
	}

	inline void setMID(avm_size_t mid) const
	{
		base_this_type::mPTR->mMID = mid;
	}


	/**
	 * GETTER - SETTER
	 * mProtocol
	 */
	inline ComProtocol::PROTOCOL_KIND getProtocol() const
	{
		return( base_this_type::mPTR->mProtocol );
	}

	inline bool isProtocolENV() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_ENVIRONMENT_KIND );
	}

	inline bool isnotProtocolENV() const
	{
		return( base_this_type::mPTR->mProtocol
				!= ComProtocol::PROTOCOL_ENVIRONMENT_KIND );
	}

	inline bool isProtocolBUFFER() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_BUFFER_KIND );
	}

	inline bool isProtocolRDV() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_RDV_KIND );
	}

	inline bool isProtocolMULTI_RDV() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_MULTIRDV_KIND );
	}

	inline bool isProtocolANYCAST() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_ANYCAST_KIND );
	}

	inline void setProtocol(ComProtocol::PROTOCOL_KIND aProtocol) const
	{
		base_this_type::mPTR->mProtocol = aProtocol;
	}


	/**
	 * GETTER - SETTER
	 * mConnect
	 */
	inline InstanceOfConnect * getConnect() const
	{
		return( base_this_type::mPTR->mConnect );
	}

	inline bool hasConnect() const
	{
		return( base_this_type::mPTR->mConnect != NULL );
	}

	inline void setConnect(InstanceOfConnect * anConnect) const
	{
		base_this_type::mPTR->mConnect = anConnect;
	}


	/**
	 * GETTER
	 * mMachinePort
	 */
	inline PairMachinePort & getMachinePort() const
	{
		return( base_this_type::mPTR->mMachinePort );
	}

	inline InstanceOfMachine * getMachine() const
	{
		return( base_this_type::mPTR->mMachinePort.first() );
	}

	inline InstanceOfPort * getPort() const
	{
		return( base_this_type::mPTR->mMachinePort.second() );
	}


	/**
	 * GETTER - SETTER
	 * tableOfBufferOffset
	 */
	inline ListOfInstanceOfBuffer & getBufferInstance()
	{
		return( base_this_type::mPTR->mBufferInstance );
	}

	inline const ListOfInstanceOfBuffer & getBufferInstance() const
	{
		return( base_this_type::mPTR->mBufferInstance );
	}

	inline void appendBuffer(InstanceOfBuffer * aBuffer)
	{
		getBufferInstance().push_back(aBuffer);
	}


	/**
	 * GETTER - SETTER
	 * mRuntimeRID
	 */
	inline const RuntimeID & getRuntimeRID() const
	{
		return( base_this_type::mPTR->mRuntimeRID );
	}

	inline bool hasRuntimeRID() const
	{
		return( base_this_type::mPTR->mRuntimeRID.valid() );
	}

	inline void setRuntimeRID(const RuntimeID & aRID) const
	{
		base_this_type::mPTR->mRuntimeRID = aRID;
	}


	/**
	 * Serialization
	 */
	virtual std::string str() const;

	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		if( base_this_type::mPTR != NULL )
		{
			StringOutStream oss(indent);

			base_this_type::mPTR->toStream( oss );

			return( oss.str() );
		}
		else
		{
			return( indent.TABS + "RoutingData<null>" + indent.EOL);
		}
	}

	inline void toStream(OutStream & os) const
	{
		if( base_this_type::mPTR != NULL )
		{
			base_this_type::mPTR->toStream(os);
		}
		else
		{
			os << "RoutingData<null>" << std::flush;
		}
	}

};


/**
 * TYPE DEFINITION
 * TABLE of ROUTING DATA
 */
typedef  Vector< RoutingData >  TableOfRoutingData;


}

#endif /*ROUTINGDATA_H_*/
