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
#include <fml/runtime/RuntimeID.h>


namespace sep
{

class Message;

/**
 * TYPEDEF
 */
typedef List< avm_size_t >  ListOfSizeT;


class MessageElement :
		public Element,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( MessageElement )
{

	friend class Message;

	AVM_DECLARE_CLONABLE_CLASS( MessageElement )

protected:
	/*
	 * ATTRIBUTES
	 */
	// The Message Identifier
	avm_size_t mMID;

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
	MessageElement(const RuntimeID & aSenderRID, const BF & aPort)
	: Element( CLASS_KIND_T( Message ) ),
	mMID( 0 ),
	mSenderRID( aSenderRID ),
	mReceiverRID( ),
	mPort( aPort ),
	mParameters( )
	{
		//!! NOTHING
	}

	MessageElement(avm_size_t aMID,
			const RuntimeID & aSenderRID, const BF & aPort)
	: Element( CLASS_KIND_T( Message ) ),
	mMID( aMID ),
	mSenderRID( aSenderRID ),
	mReceiverRID( ),
	mPort( aPort ),
	mParameters( )
	{
		//!! NOTHING
	}

	MessageElement(const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, const BF & aPort)
	: Element( CLASS_KIND_T( Message ) ),
	mMID( 0 ),
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
	mMID( 0 ),
	mSenderRID( aSenderRID ),
	mReceiverRID( aReceiverRID ),
	mPort( INCR_BF( aPort ) ),
	mParameters( )
	{
		//!! NOTHING
	}

	MessageElement(avm_size_t aMID, const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, const BF & aPort)
	: Element( CLASS_KIND_T( Message ) ),
	mMID( aMID ),
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
	mMID( anElement.mMID ),
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
	 * Serialization
	 */
	virtual std::string str() const;

	virtual void toStream(OutStream & os) const;

};

class Message :
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

	/*
	 * STATIC ATTRIBUTES
	 */
	static Message _NULL_;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Message()
	: base_this_type( )
	{
		//!! NOTHING
	}

	Message(const RuntimeID & aSenderRID, const BF & aPort)
	: base_this_type( new MessageElement(aSenderRID, aPort) )
	{
		//!! NOTHING
	}

	Message(avm_size_t aMID, const RuntimeID & aSenderRID, const BF & aPort)
	: base_this_type( new MessageElement(aMID, aSenderRID, aPort) )
	{
		//!! NOTHING
	}

	Message(const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, const BF & aPort)
	: base_this_type( new MessageElement(aSenderRID, aReceiverRID, aPort) )
	{
		//!! NOTHING
	}

	Message(const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, InstanceOfPort * aPort)
	: base_this_type( new MessageElement(aSenderRID, aReceiverRID, aPort) )
	{
		//!! NOTHING
	}

	Message(avm_size_t aMID, const RuntimeID & aSenderRID,
			const RuntimeID & aReceiverRID, const BF & aPort)
	: base_this_type( new MessageElement(aMID, aSenderRID, aReceiverRID, aPort) )
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

	inline avm_size_t size() const
	{
		return( base_this_type::mPTR->mParameters.size() );
	}


	inline void appendParameter(const BF & aParameter)
	{
		base_this_type::mPTR->mParameters.append( aParameter );
	}

	inline const BF & getParameter(avm_size_t offset) const
	{
		return( base_this_type::mPTR->mParameters.get( offset ) );
	}



	/**
	 * GETTER - SETTER
	 * mMID
	 */
	inline avm_size_t getMID() const
	{
		return( base_this_type::mPTR->mMID );
	}


	inline bool isMID(avm_size_t mid) const
	{
		return( base_this_type::mPTR->mMID == mid );
	}

	inline bool isMID(const ListOfSizeT & ieMids) const
	{
		return( ieMids.contains(base_this_type::mPTR->mMID) );
	}

	inline void setMID(avm_size_t mid) const
	{
		base_this_type::mPTR->mMID = mid;
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


	// The RID of the Machine where the port is declared
	inline RuntimeID getMainSenderRID() const
	{
		return( hasPort()
				? base_this_type::mPTR->mSenderRID.getCommunicator( getPort() )
				: RuntimeID::REF_NULL );
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
	inline bool isSenderMachine(InstanceOfMachine * anInstance) const
	{
		return( base_this_type::mPTR->mSenderRID.hasAsAncestor(anInstance) );
	}

	inline bool needSender(const RuntimeID & aRID)
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
	inline bool isReceiverMachine(InstanceOfMachine * anInstance) const
	{
		return( base_this_type::mPTR->mReceiverRID.hasAsAncestor(anInstance) );
	}

	inline bool needReceiver(const RuntimeID & aRID)
	{
		return( base_this_type::mPTR->mReceiverRID.invalid()
				|| isReceiver(aRID) );
	}

	inline void setReceiverRID(const RuntimeID & aRID)
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

	inline InstanceOfPort * getPort() const
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

	// case of MID
	inline bool isCompatible(avm_size_t mid) const
	{
		return( isMID(mid) );
	}

	inline bool isCompatible(avm_size_t mid,
			const RuntimeID & aReceiverRID) const
	{
		return( isMID(mid) && isReceiver(aReceiverRID) );
	}


	// case of Signal
	inline bool isCompatible(InstanceOfPort * aSignal) const
	{
		return( isSignal(aSignal));
	}

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
	inline virtual std::string str() const
	{
		return( (base_this_type::mPTR != NULL) ?
				base_this_type::mPTR->str() : "Message<null>" );
	}

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
			return( indent.TABS + "Message<null>" + indent.EOL);
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
			os << "Message<null>" << std::flush;
		}
	}

	void toFscn(OutStream & os) const;

};



/**
 * TYPE DEFINITION
 * TABLE of ROUTER
 */
typedef  List< Message   >  ListOfMessage;

typedef  Vector< Message >  TableOfMessage;


} /* namespace sep */

#endif /*MESSAGE_H_*/
