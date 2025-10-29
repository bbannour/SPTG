/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ICOMPOINT_H_
#define ICOMPOINT_H_

#include <string>

#include <util/avm_numeric.h>


namespace sep
{

////////////////////////////////////////////////////////////////////////////////
// COMMUNICATION POINT : KIND & DIRECTION
////////////////////////////////////////////////////////////////////////////////

class IComPoint
{

public:
	/**
	 * ComPoint NATURE
	 */
	typedef std::uint8_t         ENUM_IO_NATURE;

	enum
	{
		IO_CHANNEL_NATURE       = 0x001,

		IO_MESSAGE_NATURE       = 0x002,

		IO_PORT_NATURE          = 0x004,

		IO_SIGNAL_NATURE        = 0x008,


		IO_MASK_ALL_NATURE      = 0x0FF,

		IO_UNDEFINED_NATURE     = 0x000
	};


	/**
	 * DESTRUCTOR
	 */
	virtual ~IComPoint()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// NATURE
	////////////////////////////////////////////////////////////////////////////
	/**
	 * STATIC
	 */
	static ENUM_IO_NATURE to_nature(const std::string & id);

	static std::string str_nature(ENUM_IO_NATURE nature,
			ENUM_IO_NATURE mask = IO_MASK_ALL_NATURE);

	static std::string SEPARATOR;

	/**
	 * API
	 */
	virtual ENUM_IO_NATURE getComPointNature() const = 0;

//	ENUM_IO_NATURE getComPointNature() const
//	{
//		return( mNature );
//	}


	inline bool isPort() const
	{
		return( getComPointNature() == IO_PORT_NATURE );
	}

	inline bool isSignal() const
	{
		return( getComPointNature() == IO_SIGNAL_NATURE );
	}

	inline bool isChannel() const
	{
		return( getComPointNature() == IO_CHANNEL_NATURE );
	}

	inline bool isMessage() const
	{
		return( getComPointNature() == IO_MESSAGE_NATURE );
	}

	inline std::string strComPointNature() const
	{
		return( IComPoint::str_nature( getComPointNature() ) );
	}

};


} /* namespace sep */

#endif /* ICOMPOINT_H_ */
