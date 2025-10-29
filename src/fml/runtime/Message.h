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
#ifndef MESSAGE_H_
#define MESSAGE_H_

#include <base/SmartPointer.h>
#include <common/Element.h>

#include <collection/BFContainer.h>
#include <collection/List.h>
#include <collection/Vector.h>

#include <common/BF.h>

#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/RoutingData.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{

class Message;

/**
 * TYPEDEF
 */
typedef List< std::size_t >  ListOfSizeT;


class MessageElement final : public Element,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( MessageElement )
{

	friend class Message;

	AVM_DECLARE_CLONABLE_CLASS( MessageElement )

protected:
	/*
	 * ATTRIBUTES
	 */
	RoutingData mRoutingData;

	// RID of sender
	RuntimeID mSenderRID;

	// RID of Receiver
	RuntimeID mReceiverRID;

	// The port
	BF mPort;

	// The parameters
	BFVector mParameters;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MessageElement(const RuntimeID & aSenderRID, const BF & aPort,
			const RuntimeID & aReceiverRID = RuntimeID::nullref())
	: Element( CLASS_KIND_T( Message ) ),
	mRoutingData( ),
	mSenderRID( aSenderRID ),
	mReceiverRID( aReceiverRID ),
	mPort( aPort ),
	mParameters( )
	{
		//!! NOTHING
	}

	MessageElement(const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, InstanceOfPort * aPort)
	: Element( CLASS_KIND_T( Message ) ),
	mRoutingData( ),
	mSenderRID( aSenderRID ),
	mReceiverRID( aReceiverRID ),
	mPort( INCR_BF( aPort ) ),
	mParameters( )
	{
		//!! NOTHING
	}

	MessageElement(const RoutingData & aRoutingData, const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, const BF & aPort)
	: Element( CLASS_KIND_T( Message ) ),
	mRoutingData( aRoutingData ),
	mSenderRID( aSenderRID ),
	mReceiverRID( aReceiverRID ),
	mPort( aPort ),
	mParameters( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	MessageElement(const MessageElement & anElement)
	: Element( anElement ),
	mRoutingData( anElement.mRoutingData ),
	mSenderRID( anElement.mSenderRID ),
	mReceiverRID( anElement.mReceiverRID ),
	mPort( anElement.mPort ),
	mParameters( anElement.mParameters )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~MessageElement()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * The Message Identifier
	 *
	 */
	inline std::size_t getMID() const
	{
		return( mRoutingData.valid() ? mRoutingData.getMID() : 0 );
	}



	/**
	 * Serialization
	 */
	virtual std::string str() const override;

	virtual void toStream(OutStream & out) const override;

	virtual void toStreamValue(OutStream & out) const;

};

class Message final :
		public SmartPointer< MessageElement , DestroyElementPolicy >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Message )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef SmartPointer< MessageElement ,
						DestroyElementPolicy >  base_this_type;

public:
	/**
	 * TYPEDEF
	 */
	typedef BFVector::const_iterator  const_iterator;

	typedef MessageElement *          pointer_t;


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static Message & nullref()
	{
		static Message _NULL_;

		return( _NULL_ );
	}


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Message()
	: base_this_type( )
	{
		//!! NOTHING
	}

	Message(const RuntimeID & aSenderRID, const BF & aPort,
			const RuntimeID & aReceiverRID = RuntimeID::nullref())
	: base_this_type( new MessageElement(aSenderRID, aPort, aReceiverRID) )
	{
		//!! NOTHING
	}

	Message(const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, InstanceOfPort * aPort)
	: base_this_type( new MessageElement(aSenderRID, aReceiverRID, aPort) )
	{
		//!! NOTHING
	}

	Message(const RoutingData & aRoutingData, const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, const BF & aPort)
	: base_this_type( new MessageElement(aRoutingData, aSenderRID, aReceiverRID, aPort) )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Message(const Message & anElement)
	: base_this_type( anElement )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Message()
	{
		//!! NOTHING
	}


	/**
	 * operator=
	 */
	inline Message & operator=(const BF & other)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( other.is< Message >() )
				<< "Invalid Assignment Cast of an inherit BF Class !!"
				<< SEND_EXIT;

		if( base_this_type::mPTR != other.raw_pointer() )
		{
			release_acquire(
					static_cast< MessageElement * >( other.raw_pointer() ) );
		}
		return( *this );
	}

	/**
	 * Comparison
	 * operator==
	 */
	bool equals(const Message & aMessage) const;


	/**
	 * GETTER - SETTER
	 * mParameters
	 */
	inline const_iterator beginParameters() const
	{
		return( base_this_type::mPTR->mParameters.begin() );
	}

	inline const_iterator endParameters() const
	{
		return( base_this_type::mPTR->mParameters.end() );
	}


	inline void appendParameters(const BFVector & aParameter)
	{
		base_this_type::mPTR->mParameters.append( aParameter );
	}

	inline const BFVector & getParameters() const
	{
		return( base_this_type::mPTR->mParameters );
	}

	inline bool hasParameter() const
	{
		return( base_this_type::mPTR->mParameters.nonempty() );
	}

	inline std::size_t size() const
	{
		return( base_this_type::mPTR->mParameters.size() );
	}


	inline void appendParameter(const BF & aParameter)
	{
		base_this_type::mPTR->mParameters.append( aParameter );
	}

	inline const BF & getParameter(std::size_t offset) const
	{
		return( base_this_type::mPTR->mParameters.get( offset ) );
	}



	/**
	 * GETTER - SETTER
	 * The Message Identifier
	 *
	 */
	inline std::size_t getMID() const
	{
		return( base_this_type::mPTR->getMID() );
	}


	inline bool isMID(std::size_t mid) const
	{
		return( getMID() == mid );
	}

	inline bool isMID(const ListOfSizeT & ieMids) const
	{
		return( ieMids.contains( getMID() ) );
	}


	/**
	 * GETTER - SETTER
	 * mRoutingData
	 */
	inline const RoutingData & getRoutingData() const
	{
		return( base_this_type::mPTR->mRoutingData );
	}

	inline bool hasRoutingData() const
	{
		return( base_this_type::mPTR->mRoutingData.valid() );
	}

	inline void setRoutingData(const RoutingData & aRoutingData) const
	{
		base_this_type::mPTR->mRoutingData = aRoutingData;
	}


	/**
	 * GETTER - SETTER
	 * mSenderRID
	 */
	inline const RuntimeID & getSenderRID() const
	{
		return( base_this_type::mPTR->mSenderRID );
	}

	inline InstanceOfMachine * getSenderMachine() const
	{
		return( base_this_type::mPTR->mSenderRID.getInstance() );
	}

	inline RuntimeID getLifelineSenderRID() const
	{
		return( base_this_type::mPTR->mSenderRID.getLifeline() );
	}


	// The RID of the Machine where the port is declared
	inline RuntimeID getMainSenderRID() const
	{
		return( hasPort()
				? base_this_type::mPTR->mSenderRID.getCommunicator( getPort() )
				: RuntimeID::nullref() );
	}

	// The instance of Machine where the port is declared
	inline InstanceOfMachine * getMainSenderMachine() const
	{
		return( getMainSenderRID().getInstance() );
	}


	inline bool hasSenderRID() const
	{
		return( base_this_type::mPTR->mSenderRID.valid() );
	}


	// return TRUE for all ancestor of the concrete sender RID
	inline bool isSender(const RuntimeID & aRID) const
	{
		return( base_this_type::mPTR->mSenderRID.hasAsAncestor(aRID) );
				// DON'T DO THIS VERIFICATION
//				|| aRID.hasAsAncestor(base_this_type::mPTR->mSenderRID) );
	}


	// return TRUE for all ancestor of the concrete sender RID
	inline bool isSenderMachine(const InstanceOfMachine & anInstance) const
	{
		return( base_this_type::mPTR->mSenderRID.hasAsAncestor(anInstance) );
	}

	inline bool needSender(const RuntimeID & aRID) const
	{
		return( base_this_type::mPTR->mSenderRID.invalid()
				|| isSender(aRID) );
	}


	inline void setSenderRID(const RuntimeID & aRID)
	{
		base_this_type::mPTR->mSenderRID = aRID;
	}


	/**
	 * GETTER - SETTER
	 * mReceiverRID
	 */
	inline const RuntimeID & getReceiverRID() const
	{
		return( base_this_type::mPTR->mReceiverRID );
	}

	inline InstanceOfMachine * getReceiverMachine() const
	{
		return( base_this_type::mPTR->mReceiverRID.getInstance() );
	}

	inline RuntimeID getLifelineReceiverRID() const
	{
		return( base_this_type::mPTR->mReceiverRID.getLifeline() );
	}


	inline bool hasReceiverRID() const
	{
		return( base_this_type::mPTR->mReceiverRID.valid() );
	}


	// return TRUE for all ancestor of the concrete sender RID
	inline bool isReceiver(const RuntimeID & aRID) const
	{
		return( base_this_type::mPTR->mReceiverRID.invalid()
				|| aRID.invalid()
				|| aRID.hasAsAncestor( base_this_type::mPTR->mReceiverRID ) );
				// DON'T DO THIS VERIFICATION
//				|| base_this_type::mPTR->mReceiverRID.hasAsAncestor( aRID ) );
	}


	// return TRUE for all ancestor of the concrete sender RID
	inline bool isReceiverMachine(const InstanceOfMachine & anInstance) const
	{
		return( base_this_type::mPTR->mReceiverRID.hasAsAncestor(anInstance) );
	}

	inline bool needReceiver(const RuntimeID & aRID)
	{
		return( base_this_type::mPTR->mReceiverRID.invalid()
				|| isReceiver(aRID) );
	}

	inline void setReceiverRID(const RuntimeID & aRID) const
	{
		base_this_type::mPTR->mReceiverRID = aRID;
	}


	/**
	 * GETTER - SETTER
	 * mPort
	 */
	inline const BF & bfPort() const
	{
		return( base_this_type::mPTR->mPort );
	}

	inline const InstanceOfPort & getPort() const
	{
		return( base_this_type::mPTR->mPort.as< InstanceOfPort >() );
	}

	inline InstanceOfPort * ptrPort() const
	{
		return( base_this_type::mPTR->mPort.as_ptr< InstanceOfPort >() );
	}

	inline bool hasPort() const
	{
		return( base_this_type::mPTR->mPort.valid() );
	}


	inline bool isSignal(InstanceOfPort * aSignal) const
	{
		return( base_this_type::mPTR->mPort.isTEQ( aSignal ) );
	}

	inline bool isSignal(const ListOfInstanceOfPort & ieSignals) const
	{
		return( ieSignals.contains(
				base_this_type::mPTR->mPort.as_ptr< InstanceOfPort >() ) );
	}


	inline void setPort(const BF & aPort)
	{
		base_this_type::mPTR->mPort = aPort;
	}


	/**
	 * TEST
	 * isCompatible
	 */
	// case of Receiver only
	inline bool isCompatible(const RuntimeID & aReceiverRID) const
	{
		return( isReceiver(aReceiverRID) );
	}

	// case of MID & Receiver
	inline bool isCompatible(std::size_t mid,
			const RuntimeID & aReceiverRID) const
	{
		return( isMID(mid) && isReceiver(aReceiverRID) );
	}


	// case of Signal & Receiver
	inline bool isCompatible(InstanceOfPort * aSignal,
			const RuntimeID & aReceiverRID) const
	{
		return( isSignal(aSignal) && isReceiver(aReceiverRID) );
	}


	// case of list< MID >
	inline bool isCompatible(const ListOfSizeT & ieMids) const
	{
		return( isMID(ieMids) );
	}

	inline bool isCompatible(const ListOfSizeT & ieMids,
			const RuntimeID & aReceiverRID) const
	{
		return( isReceiver(aReceiverRID) && isMID(ieMids) );
	}


	// case of list< Signal >
	inline bool isCompatible(const ListOfInstanceOfPort & ieSignals) const
	{
		return( isSignal(ieSignals) );
	}

	inline bool isCompatible(const ListOfInstanceOfPort & ieSignals,
			const RuntimeID & aReceiverRID) const
	{
		return( isReceiver(aReceiverRID) && isSignal(ieSignals) );
	}



	/**
	 * Serialization
	 */
	inline std::string str() const
	{
		return( (base_this_type::mPTR != nullptr) ?
				base_this_type::mPTR->str() : "Message<null>" );
	}

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
			return( indent.TABS + "Message<null>" + indent.EOL);
		}
	}

	inline void toStream(OutStream & out) const
	{
		if( base_this_type::mPTR != nullptr )
		{
			base_this_type::mPTR->toStream(out);
		}
		else
		{
			out << "Message<null>" << std::flush;
		}
	}

	inline void toStreamValue(OutStream & out) const
	{
		if( base_this_type::mPTR != nullptr )
		{
			base_this_type::mPTR->toStreamValue(out);
		}
		else
		{
			out << "Message<null>" << std::flush;
		}
	}

	void toFscn(OutStream & out) const;

};



/**
 * TYPE DEFINITION
 * TABLE of ROUTER
 */
typedef  List< Message   >  ListOfMessage;

typedef  Vector< Message >  TableOfMessage;


} /* namespace sep */

#endif /*MESSAGE_H_*/
