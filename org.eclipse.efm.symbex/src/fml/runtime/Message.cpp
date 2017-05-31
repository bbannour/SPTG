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
#include "Message.h"

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>


namespace sep
{


/*
 * STATIC ATTRIBUTES
 */
Message Message::_NULL_;


/**
 * Comparison
 * operator==
 */
bool Message::equals(const Message & aMessage) const
{
	if( (this == &aMessage)
		|| base_this_type::operator ==( aMessage ) )
	{
		return( true );
	}
	else if( this->invalid() || aMessage.invalid() )
	{
		return( false );
	}
	else if( (this->getMID() == aMessage.getMID())
			&& (getPort() == aMessage.getPort())
			&& (getSenderRID() == aMessage.getSenderRID())
			&& (getReceiverRID() == aMessage.getReceiverRID()) )
	{
		if( hasParameter() )
		{
			Message::const_iterator itOther = aMessage.beginParameters();
			Message::const_iterator it = beginParameters();
			Message::const_iterator endIt = endParameters();
			for( ; it != endIt ; ++it )
			{
				// Syntaxic equality between arguments ?
				if( (*it) != (*itOther) )
				{
					return( false );
				}
			}
		}

		return( true );
	}

	return( false );
}


/**
 * Serialization
 */
std::string MessageElement::str() const
{
	StringOutStream oss;

	oss << "message< mid:" << mMID << ", ";
	if( mPort.is< InstanceOfPort >() )
	{
		InstanceOfPort * aPort = mPort.to_ptr< InstanceOfPort >();
		oss << aPort->strComPointNature() << ": "
			<< aPort->getFullyQualifiedNameID();
	}
	else
	{
		oss << "port: null<port>";
	}

	if( mSenderRID.valid() )
	{
		oss << ", sender: " << mSenderRID.strUniqId();
	}
	if( mReceiverRID.valid() )
	{
		oss << ", receiver: " << mReceiverRID.strUniqId();
	}
	oss << " >[";

	if( mParameters.nonempty() )
	{
		oss << AVM_STR_INDENT;

		Message::const_iterator it = mParameters.begin();
		Message::const_iterator endIt = mParameters.end();

		it->toStream(oss);

		for( ++it ; it != endIt ; ++it )
		{
			oss << " , ";
			it->toStream(oss);
		}
		oss << END_INDENT;
	}

	oss << " ]";

	return( oss.str() );
}


void MessageElement::toStream(OutStream & os) const
{
	if( os.preferablySTR() )
	{
		os << TAB << str() << EOL_FLUSH;
		return;
	}

	os << TAB << "message< mid#" << mMID << " > ";
	if( mSenderRID.valid() )
	{
		os << mSenderRID.strUniqId()<< "->";
	}
	os << (mPort.is< InstanceOfPort >()
			? mPort.to_ptr< InstanceOfPort >()->getFullyQualifiedNameID()
			: "null<port>");

	if( mParameters.nonempty() )
	{
		os << " {";

		AVM_DEBUG_REF_COUNTER(os);
		os << EOL;

		if( mReceiverRID.valid() )
		{
			os << TAB2 << "receiver = "
					<< mReceiverRID.strUniqId() << ";" << EOL;
		}


AVM_IF_DEBUG_LEVEL_GT_MEDIUM
		os << TAB << "param" << EOL_INCR_INDENT;

		Message::const_iterator it = mParameters.begin();
		Message::const_iterator endIt = mParameters.end();
		for( ; it != endIt ; ++it )
		{
			it->toStream(os);
		}
		os << DECR_INDENT;

AVM_ELSE

		os << TAB2 << "param = [" << AVM_STR_INDENT;

		Message::const_iterator it = mParameters.begin();
		Message::const_iterator endIt = mParameters.end();
		for( ; it != endIt ; ++it )
		{
			os << " ,";
			it->toStream(os);
		}
		os << END_INDENT << " ];" << EOL;
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

		os << TAB << "}" << EOL_FLUSH;
	}
	else
	{
		os << ";";
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}
}

void Message::toFscn(OutStream & os) const
{
	RuntimeID aRID = getSenderRID();

	for( ; aRID.hasPRID() ; aRID = aRID.getPRID() )
	{
		if( aRID.getExecutable()->hasPort() )
		{
			break;
		}
	}

	if( hasPort() )
	{
		int pointpos = getPort()->getFullyQualifiedNameID().rfind('.',
				getPort()->getFullyQualifiedNameID().size());
//		os << TAB2 << ":pid#" << rid.getRid() << ":"
//				<< getPort()->getFullyQualifiedNameID().substr(
//					rid->getInstance()->getFullyQualifiedNameID().size() + 1);
		os << TAB2 << ":pid#" << aRID.getRid() << ":"
				<< getPort()->getFullyQualifiedNameID().substr(pointpos + 1);
	}
	else
	{
		os << TAB2 << ":pid#" << aRID.getRid() << ":_";
	}

	if( hasParameter() )
	{
		os << "(" << AVM_NO_INDENT;

		Message::const_iterator it = beginParameters();
		Message::const_iterator endIt = endParameters();

		it->toStream(os);

		for( ++it ; it != endIt ; ++it )
		{
			os << " , ";
			it->toStream(os);
		}

		os << ")";

AVM_IF_DEBUG_ENABLED_AND( base_this_type::mPTR->mReceiverRID.valid() )
	os << " /* --> " << base_this_type::mPTR->mReceiverRID.strUniqId() << "*/";
AVM_ENDIF_DEBUG_ENABLED_AND

		os << ";" << END_INDENT_EOL;
	}
	else
	{
AVM_IF_DEBUG_ENABLED_AND( base_this_type::mPTR->mReceiverRID.valid() )
	os << " /* --> " << base_this_type::mPTR->mReceiverRID.strUniqId() << "*/";
AVM_ENDIF_DEBUG_ENABLED_AND

		os << ";" << EOL_FLUSH;
	}
}




}
