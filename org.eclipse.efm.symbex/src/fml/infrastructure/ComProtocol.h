/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef COMPROTOCOL_H_
#define COMPROTOCOL_H_


#include <fml/lib/IComPoint.h>

#include <fml/infrastructure/Buffer.h>


namespace sep
{

class ComProtocol
{

public:
	/**
	 * ENUM TYPEDEF
	 */
	enum PROTOCOL_KIND
	{
		PROTOCOL_ENVIRONMENT_KIND,

		PROTOCOL_TRANSFERT_KIND,

		PROTOCOL_BUFFER_KIND,

		PROTOCOL_RDV_KIND,
		PROTOCOL_MULTIRDV_KIND,

		PROTOCOL_FLOW_KIND,

		PROTOCOL_BROADCAST_KIND,

		PROTOCOL_MULTICAST_KIND,
		PROTOCOL_UNICAST_KIND,

		PROTOCOL_ANYCAST_KIND,

		PROTOCOL_UNDEFINED_KIND
	};


protected:
	/**
	 * ATTRIBUTES
	 */
	IComPoint::ENUM_IO_NATURE mComPointNature;

	PROTOCOL_KIND mProtocol;
	PROTOCOL_KIND mCast;

	Buffer * mBuffer;

	BF mBufferUfid;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ComProtocol(PROTOCOL_KIND aProtocol,
			IComPoint::ENUM_IO_NATURE aNature = IComPoint::IO_PORT_NATURE)
	: mComPointNature( aNature ),
	mProtocol( aProtocol ),
	mCast( to_cast(aProtocol) ),
	mBuffer( NULL ),
	mBufferUfid( )
	{
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ComProtocol()
	{
	}


	/**
	 * GETTER - TESTER - SETTER
	 * mComPointNature
	 */
	inline IComPoint::ENUM_IO_NATURE getNature() const
	{
		return( mComPointNature );
	}


	inline bool isPort() const
	{
		return( mComPointNature == IComPoint::IO_PORT_NATURE );
	}

	inline bool isSignal() const
	{
		return( mComPointNature == IComPoint::IO_SIGNAL_NATURE );
	}


	inline void setNature(IComPoint::ENUM_IO_NATURE aNature)
	{
		mComPointNature = aNature;
	}

	/**
	 * GETTER - SETTER
	 * mProtocol
	 */
	inline PROTOCOL_KIND getProtocol() const
	{
		return( mProtocol );
	}

	inline bool hasProtocol() const
	{
		return( mProtocol != PROTOCOL_UNDEFINED_KIND );
	}

	inline void setProtocol(PROTOCOL_KIND aProtocol)
	{
		mProtocol = aProtocol;
	}


	/**
	 * GETTER - SETTER
	 * mCast
	 */
	inline PROTOCOL_KIND getCast() const
	{
		return( mCast );
	}

	inline bool hasCast() const
	{
		return( mCast != PROTOCOL_UNDEFINED_KIND );
	}

	inline void setCast(PROTOCOL_KIND aCast)
	{
		mCast = aCast;
	}


	/**
	 * GETTER - SETTER
	 * mProtocol
	 * mCast
	 */
	inline void setProtocolCast(PROTOCOL_KIND aProtocol,
			PROTOCOL_KIND aCast)
	{
		mProtocol = aProtocol;
		mCast = aCast;
	}


	/**
	 * GETTER - SETTER
	 * mBuffer
	 */
	inline Buffer * getBuffer() const
	{
		return( mBuffer );
	}

	inline bool hasBuffer() const
	{
		return( mBuffer != NULL );
	}

	inline void setBuffer(const BF & aBuffer)
	{
		if( aBuffer.is< Buffer >() )
		{
			mBuffer = aBuffer.to_ptr< Buffer >();
			mBufferUfid = aBuffer;
		}
		else
		{
			mBufferUfid = aBuffer;
		}
	}


	/**
	 * GETTER - SETTER
	 * mBufferUfid
	 */
	inline BF & getBufferUfid()
	{
		return( mBufferUfid );
	}

	inline const BF & getBufferUfid() const
	{
		return( mBufferUfid );
	}

	inline bool hasBufferUfid() const
	{
		return( mBufferUfid.valid() );
	}

	inline std::string strBufferUfid() const
	{
		return( mBufferUfid.str() );
	}

	/**
	 * Update
	 */
	inline void update(ComProtocol * cp)
	{
		mProtocol   = cp->mProtocol;
		mCast       = cp->mCast;
		mBuffer     = cp->mBuffer;
		mBufferUfid = cp->mBufferUfid;
	}


	/**
	 * Serialization
	 */
	static PROTOCOL_KIND to_cast(PROTOCOL_KIND protocol);

	static std::string to_string(PROTOCOL_KIND protocol);


	static std::string strProtocol(PROTOCOL_KIND aProtocol);

	static std::string strProtocol(
			PROTOCOL_KIND aProtocol, PROTOCOL_KIND aCast);

	static std::string strCast(PROTOCOL_KIND aCast);


	inline std::string strProtocolCast(bool mustBeDefined = false) const
	{
		StringOutStream oss( AVM_NO_INDENT );

		toStreamProtocolCast( oss );

		return( oss.str() );
	}

	OutStream & toStreamProtocolCast(
			OutStream & out, bool mustBeDefined = false) const;

};


}

#endif /* COMPROTOCOL_H_ */
