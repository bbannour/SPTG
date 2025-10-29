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

#include <string>


namespace sep
{


/**
 * Serialization
 * Deserialization
 */
ComProtocol::PROTOCOL_KIND ComProtocol::to_protocol(const std::string & strProtocol)
{
	std::string lowerProtocol = strProtocol;
	StringTools::tolower( lowerProtocol );


	if( lowerProtocol == "env"         ) return PROTOCOL_ENVIRONMENT_KIND;
	if( lowerProtocol == "environment" ) return PROTOCOL_ENVIRONMENT_KIND;

	if( lowerProtocol == "transfert"   ) return PROTOCOL_TRANSFERT_KIND;

	if( lowerProtocol == "buffer"      ) return PROTOCOL_BUFFER_KIND;

	if( lowerProtocol == "rdv"         ) return PROTOCOL_RDV_KIND;
	if( lowerProtocol == "multirdv"    ) return PROTOCOL_MULTIRDV_KIND;

	if( lowerProtocol == "flow"        ) return PROTOCOL_FLOW_KIND;

	if( lowerProtocol == "broadcast"   ) return PROTOCOL_BROADCAST_KIND;

	if( lowerProtocol == "multicast"   ) return PROTOCOL_MULTICAST_KIND;
	if( lowerProtocol == "unicast"     ) return PROTOCOL_UNICAST_KIND;
	if( lowerProtocol == "anycast"     ) return PROTOCOL_ANYCAST_KIND;

	return PROTOCOL_UNDEFINED_KIND;
}

ComProtocol::PROTOCOL_KIND ComProtocol::to_cast(const std::string & strCast)
{
	std::string lowerCast = strCast;
	StringTools::tolower( lowerCast );

	if( lowerCast == "broadcast"     ) return PROTOCOL_BROADCAST_KIND;

	if( lowerCast == "multicast"     ) return PROTOCOL_MULTICAST_KIND;
	if( lowerCast == "unicast"       ) return PROTOCOL_UNICAST_KIND;
	if( lowerCast == "anycast"       ) return PROTOCOL_ANYCAST_KIND;

	return PROTOCOL_UNDEFINED_KIND;
}


avm_type_specifier_kind_t ComProtocol::to_policy(const std::string & strPolicy)
{
	std::string lowerPolicy = strPolicy;
	StringTools::tolower( lowerPolicy );

	if( lowerPolicy == "fifo"      ) return TYPE_FIFO_SPECIFIER;
	if( lowerPolicy == "lifo"      ) return TYPE_LIFO_SPECIFIER;

	if( lowerPolicy == "multififo" ) return TYPE_MULTI_FIFO_SPECIFIER;
	if( lowerPolicy == "multilifo" ) return TYPE_MULTI_LIFO_SPECIFIER;

	if( lowerPolicy == "ram"       ) return TYPE_RAM_SPECIFIER;

	if( lowerPolicy == "set"       ) return TYPE_SET_SPECIFIER;
	if( lowerPolicy == "bag"       ) return TYPE_MULTISET_SPECIFIER;
	if( lowerPolicy == "multiset"  ) return TYPE_MULTISET_SPECIFIER;

	return TYPE_UNDEFINED_SPECIFIER;
}

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

		case PROTOCOL_MULTICAST_KIND:
		{
			StringOutStream OSS;

			OSS << "multicast";
			if( aProtocol != aCast )
			{
				OSS << " , " << ComProtocol::strCast(aCast);
			}

			return( OSS.str() );
		}

		case PROTOCOL_BROADCAST_KIND:
		{
			StringOutStream OSS;

			OSS << "broadcast";
			if( aProtocol != aCast )
			{
				OSS << " , " << ComProtocol::strCast(aCast);
			}

			return( OSS.str() );
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

				if( mBuffer != nullptr )
				{
					out << ": ";
					if( mBuffer->isAnonymID() )
					{
						out << Buffer::str(mBuffer->getPolicySpecifierKind(),
								mBuffer->realCapacity());
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

			case PROTOCOL_MULTICAST_KIND:
			{
				out << "multicast";
				if( mProtocol != mCast )
				{
					out << " , " << ComProtocol::strCast(mCast);
				}

				break;
			}

			case PROTOCOL_BROADCAST_KIND:
			{
				out << "broadcast";
				if( mProtocol != mCast )
				{
					out << " , " << ComProtocol::strCast(mCast);
				}

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
