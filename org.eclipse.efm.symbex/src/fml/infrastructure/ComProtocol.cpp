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

#include "ComProtocol.h"

#include <util/avm_string.h>

namespace sep
{

ComProtocol::PROTOCOL_KIND ComProtocol::to_cast(PROTOCOL_KIND protocol)
{
	switch( protocol )
	{
		case PROTOCOL_ENVIRONMENT_KIND : return( PROTOCOL_UNDEFINED_KIND );

		case PROTOCOL_TRANSFERT_KIND   : return( PROTOCOL_UNDEFINED_KIND );

		case PROTOCOL_BUFFER_KIND      : return( PROTOCOL_UNDEFINED_KIND );

		case PROTOCOL_RDV_KIND         : return( PROTOCOL_UNICAST_KIND );
		case PROTOCOL_MULTIRDV_KIND    : return( PROTOCOL_MULTICAST_KIND );

		case PROTOCOL_FLOW_KIND        : return( PROTOCOL_UNDEFINED_KIND );

		case PROTOCOL_BROADCAST_KIND   : return( protocol );
		case PROTOCOL_MULTICAST_KIND   : return( protocol );
		case PROTOCOL_UNICAST_KIND     : return( protocol );
		case PROTOCOL_ANYCAST_KIND     : return( protocol );

		case PROTOCOL_UNDEFINED_KIND   : return( protocol );

		default                        : return( PROTOCOL_UNDEFINED_KIND );
	}
}

std::string ComProtocol::to_string(PROTOCOL_KIND protocol)
{
	switch( protocol )
	{
		case PROTOCOL_ENVIRONMENT_KIND : return( "env" );

		case PROTOCOL_TRANSFERT_KIND   : return( "transfert" );

		case PROTOCOL_BUFFER_KIND      : return( "buffer" );

		case PROTOCOL_RDV_KIND         : return( "rdv" );
		case PROTOCOL_MULTIRDV_KIND    : return( "multirdv" );

		case PROTOCOL_FLOW_KIND        : return( "flow" );

		case PROTOCOL_BROADCAST_KIND   : return( "broadcast" );

		case PROTOCOL_MULTICAST_KIND   : return( "multicast" );
		case PROTOCOL_UNICAST_KIND     : return( "unicast" );
		case PROTOCOL_ANYCAST_KIND     : return( "anycast" );

		case PROTOCOL_UNDEFINED_KIND   : return( "undefined<protocol#kind>" );

		default                        : return( "unknown<protocol#kind>" );
	}
}


std::string ComProtocol::strProtocol(
		PROTOCOL_KIND aProtocol, PROTOCOL_KIND aCast)
{
	switch ( aProtocol )
	{
		case PROTOCOL_ENVIRONMENT_KIND:
		{
			return( "env" );
		}

		case PROTOCOL_BUFFER_KIND:
		{
			return( OSS() << "buffer , " << ComProtocol::strCast(aCast) );
		}

		case PROTOCOL_RDV_KIND:
		{
			return( OSS() << "rdv , " << ComProtocol::strCast(aCast) );
		}
		case PROTOCOL_MULTIRDV_KIND:
		{
			return( OSS() << "multirdv , " << ComProtocol::strCast(aCast) );
		}

		case PROTOCOL_FLOW_KIND:
		{
			return( OSS() << "flow , " << ComProtocol::strCast(aCast) );
		}

		case PROTOCOL_UNDEFINED_KIND:
		{
			return( OSS() << "undefined<protocol#kind> , "
					<< ComProtocol::strCast(aCast) );
		}

		default :
		{
			return( OSS() << "unexpected<"
					<< to_string(aProtocol) << " , "
					<< to_string(aCast) << ">" );
		}
	}
}


std::string ComProtocol::strProtocol(PROTOCOL_KIND aProtocol)
{
	switch ( aProtocol )
	{
		case PROTOCOL_ENVIRONMENT_KIND:
		{
			return( "env" );
		}

		case PROTOCOL_BUFFER_KIND:
		{
			return( "buffer" );
		}

		case PROTOCOL_RDV_KIND:
		{
			return( "rdv" );
		}
		case PROTOCOL_MULTIRDV_KIND:
		{
			return( "multirdv" );
		}

		case PROTOCOL_FLOW_KIND:
		{
			return( "flow" );
		}


		case PROTOCOL_ANYCAST_KIND:
		{
			return( "anycast" );
		}
		case PROTOCOL_UNICAST_KIND:
		{
			return( "unicast" );
		}
		case PROTOCOL_BROADCAST_KIND:
		{
			return( "broadcast" );
		}
		case PROTOCOL_MULTICAST_KIND:
		{
			return( "multicast" );
		}
		case PROTOCOL_UNDEFINED_KIND:
		{
			return( "undefined<protocol#kind>" );
		}

		default :
		{
			return( OSS() << "unexpected<"
					<< to_string(aProtocol) << ">" );
		}
	}
}


std::string ComProtocol::strCast(PROTOCOL_KIND aCast)
{
	switch ( aCast )
	{
		case PROTOCOL_UNICAST_KIND:
		{
			return( "unicast" );
		}

		case PROTOCOL_ANYCAST_KIND:
		{
			return( "anycast" );
		}

		case PROTOCOL_BROADCAST_KIND:
		{
			return( "broadcast" );
		}
		case PROTOCOL_MULTICAST_KIND:
		{
			return( "multicast" );
		}

		case PROTOCOL_UNDEFINED_KIND:
		{
			return( "undefined<cast#kind>" );
		}

		default :
		{
			return( OSS() << "unexpected<"
					<< to_string(aCast) << ">" );
		}
	}
}


OutStream & ComProtocol::toStreamProtocolCast(
		OutStream & out, bool mustBeDefined) const
{
	if( mProtocol == PROTOCOL_UNDEFINED_KIND )
	{
		if( (mCast != PROTOCOL_UNDEFINED_KIND) || mustBeDefined )
		{
			out << "< " << ComProtocol::strCast(mCast) << " >";
		}
	}
	else
	{
		out << "< ";

		switch ( mProtocol )
		{
			case PROTOCOL_ENVIRONMENT_KIND:
			{
				out << "env";

				break;
			}

			case PROTOCOL_BUFFER_KIND:
			{
				out << "buffer";

				if( mBuffer != NULL )
				{
					out << ": ";
					if( mBuffer->isAnonymID() )
					{
						out << Buffer::str(mBuffer->getPolicySpecifierKind(),
								mBuffer->getSize());
					}
					else
					{
						out << mBuffer->getNameID();
					}
				}
				else if( mBufferUfid.valid() )
				{
					out << ": " << mBufferUfid.str();
				}
				else
				{
					out << " , " << ComProtocol::strCast(mCast);
				}

				break;
			}

			case PROTOCOL_RDV_KIND:
			{
				out << "rdv" << " , " << ComProtocol::strCast(mCast);

				break;
			}
			case PROTOCOL_MULTIRDV_KIND:
			{
				out << "multirdv" << " , " << ComProtocol::strCast(mCast);

				break;
			}

			case PROTOCOL_FLOW_KIND:
			{
				out << "flow" << " , " << ComProtocol::strCast(mCast);

				break;
			}

			case PROTOCOL_UNDEFINED_KIND:
			{
				out << "undefined<protocol#kind>" << " , "
					<< ComProtocol::strCast(mCast);

				break;
			}

			default :
			{
				out << "unexpected<" << to_string(mProtocol)
					<< " , " << to_string(mCast) << ">";

				break;
			}
		}

		out << " >";
	}

	return( out );
}


}
