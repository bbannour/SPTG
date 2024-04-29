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
#include <collection/List.h>
#include <collection/Vector.h>

#include <fml/lib/IComPoint.h>

#include <fml/executable/InstanceOfBuffer.h>

#include <fml/infrastructure/ComProtocol.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


class InstanceOfConnector;
class InstanceOfMachine;
class InstanceOfPort;

class RoutingData;


/**
 * TYPEDEF
 * Pair
 * InstanceOfMachine
 * InstanceOfPort
 */
typedef Pair< const InstanceOfMachine & ,
			const InstanceOfPort & >  PairMachinePort;

typedef Vector< PairMachinePort * > VectorOfPairMachinePort;



class RoutingDataElement : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RoutingDataElement )
{

	friend class RoutingData;

	AVM_DECLARE_CLONABLE_CLASS( RoutingDataElement )

protected:
	/*
	 * ATTRIBUTES
	 */
	// The Message Identifier
	std::size_t mMID;

	// global protocol
	ComProtocol::PROTOCOL_KIND mProtocol;

	// The connector instance
	const InstanceOfConnector & mConnector;

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
	RoutingDataElement(std::size_t mid, const InstanceOfMachine & aMachine,
			const InstanceOfPort & aPort, ComProtocol::PROTOCOL_KIND aProtocol);

	RoutingDataElement(const InstanceOfConnector & aConnector,
			const InstanceOfMachine & aMachine, const InstanceOfPort & aPort);


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	explicit RoutingDataElement(const RoutingDataElement & anElement)
	: Element( anElement ),
	mMID( anElement.mMID ),

	mProtocol( anElement.mProtocol ),
	mConnector( anElement.mConnector ),
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
	inline const InstanceOfMachine & getMachine() const
	{
		return( mMachinePort.first() );
	}

	inline const InstanceOfPort & getPort() const
	{
		return( mMachinePort.second() );
	}

	/**
	 * Serialization
	 */
	virtual void toStreamPrefix(OutStream & out) const;

	inline virtual void toStream(OutStream & out) const override
	{
		toStreamPrefix( out );

		out << TAB << "}" << EOL_FLUSH;
	}

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

protected:
/**
 * ATTRIBUTES
 */
	List< RoutingData >  mManyCastRoutingData;

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
	: base_this_type( ),
	mManyCastRoutingData( )
	{
		//!! NOTHING
	}

	RoutingData(std::size_t mid, const InstanceOfMachine & aMachine,
			const InstanceOfPort & aPort, ComProtocol::PROTOCOL_KIND aProtocol)
	: base_this_type( new RoutingDataElement(mid, aMachine, aPort, aProtocol) ),
	mManyCastRoutingData( )
	{
		//!! NOTHING
	}

	RoutingData(const InstanceOfConnector & aConnector,
			const InstanceOfMachine & aMachine, const InstanceOfPort & aPort)
	: base_this_type( new RoutingDataElement(aConnector, aMachine, aPort) ),
	mManyCastRoutingData( )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	RoutingData(const RoutingData & anElement)
	: base_this_type( anElement ),
	mManyCastRoutingData( anElement.mManyCastRoutingData )
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
	inline std::size_t getMID() const
	{
		return( base_this_type::mPTR->mMID );
	}

	inline void setMID(std::size_t mid) const
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

	inline bool isProtocolBROADCAST() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_BROADCAST_KIND );
	}

	inline bool isProtocolMULTICAST() const
	{
		return( base_this_type::mPTR->mProtocol
				== ComProtocol::PROTOCOL_MULTICAST_KIND );
	}

	inline bool isMultiRoutingProtocol() const
	{
		switch( base_this_type::mPTR->mProtocol )
		{
			case ComProtocol::PROTOCOL_BUFFER_KIND:
			case ComProtocol::PROTOCOL_BROADCAST_KIND:
			case ComProtocol::PROTOCOL_MULTICAST_KIND:
			case ComProtocol::PROTOCOL_UNICAST_KIND:
			case ComProtocol::PROTOCOL_ANYCAST_KIND:
			{
				return( true );
			}

			case ComProtocol::PROTOCOL_RDV_KIND:
			case ComProtocol::PROTOCOL_MULTIRDV_KIND:

			case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
			case ComProtocol::PROTOCOL_TRANSFERT_KIND:
			case ComProtocol::PROTOCOL_UNDEFINED_KIND:
			default:
			{
				return( false );
			}
		}
	}


	inline void setProtocol(ComProtocol::PROTOCOL_KIND aProtocol) const
	{
		base_this_type::mPTR->mProtocol = aProtocol;
	}


	/**
	 * GETTER - SETTER
	 * mManyCastRoutingData
	 */
	inline const List< RoutingData > & getManyCastRoutingData() const
	{
		return( mManyCastRoutingData );
	}

	inline bool hasManyCastRoutingData() const
	{
		return( mManyCastRoutingData.nonempty() );
	}


	inline void appendManyCastRoutingData(const RoutingData & aRoutingData)
	{
		mManyCastRoutingData.append(aRoutingData);
	}


	/**
	 * GETTER - SETTER
	 * mConnector
	 */
	inline const InstanceOfConnector & getConnector() const
	{
		return( base_this_type::mPTR->mConnector );
	}


	/**
	 * GETTER
	 * mMachinePort
	 */
	inline PairMachinePort & getMachinePort() const
	{
		return( base_this_type::mPTR->mMachinePort );
	}

	inline const InstanceOfMachine & getMachine() const
	{
		return( base_this_type::mPTR->mMachinePort.first() );
	}

	inline const InstanceOfPort & getPort() const
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

	inline const bool hasBufferInstance() const
	{
		return( base_this_type::mPTR->mBufferInstance.nonempty() );
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
		if( base_this_type::mPTR != nullptr )
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

	void toStream(OutStream & out) const;

};


/**
 * TYPE DEFINITION
 * TABLE of ROUTING DATA
 */
typedef  Vector< RoutingData >  TableOfRoutingData;


}

#endif /*ROUTINGDATA_H_*/
