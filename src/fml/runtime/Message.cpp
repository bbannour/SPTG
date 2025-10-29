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
			&& getPort().isTEQ( aMessage.getPort() )
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

	oss << "message< mid:" << getMID() << ", ";
	if( mPort.is< InstanceOfPort >() )
	{
		const InstanceOfPort & aPort = mPort.to< InstanceOfPort >();

		oss << aPort.strComPointNature() << ": "
			<< aPort.getFullyQualifiedNameID();
	}
	else
	{
		oss << "port: $null<port>";
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
			oss << " , " << it->str();
		}
		oss << END_INDENT;
	}

	oss << " ]";

	return( oss.str() );
}


void MessageElement::toStream(OutStream & out) const
{
	if( out.preferablySTR() )
	{
		out << TAB << str() << EOL_FLUSH;
		return;
	}

	out << TAB << "message< mid#" << getMID() << " > ";
	if( mSenderRID.valid() )
	{
		out << mSenderRID.strUniqId()<< "->";
	}
	out << (mPort.is< InstanceOfPort >()
			? mPort.to< InstanceOfPort >().getFullyQualifiedNameID()
			: "$null<port>");

	if( mParameters.nonempty() )
	{
		out << " {";

		AVM_DEBUG_REF_COUNTER(out);
		out << EOL;

		if( mReceiverRID.valid() )
		{
			out << TAB2 << "receiver = "
					<< mReceiverRID.strUniqId() << ";" << EOL;
		}


AVM_IF_DEBUG_LEVEL_GT_MEDIUM
		out << TAB << "@param:" << EOL_INCR_INDENT;

		Message::const_iterator it = mParameters.begin();
		Message::const_iterator endIt = mParameters.end();
		for( ; it != endIt ; ++it )
		{
			it->toStream(out);
		}
		out << DECR_INDENT;

AVM_ELSE

		out << TAB2 << "param = [" << AVM_STR_INDENT;

		Message::const_iterator it = mParameters.begin();
		Message::const_iterator endIt = mParameters.end();

		it->toStream(out);
		for( ++it ; it != endIt ; ++it )
		{
			out << " ,";
			it->toStream(out);
		}
		out << END_INDENT << " ];" << EOL;
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

		out << TAB << "}" << EOL_FLUSH;
	}
	else
	{
		out << ";";
		AVM_DEBUG_REF_COUNTER(out);
		out << EOL_FLUSH;
	}
}


void MessageElement::toStreamValue(OutStream & out) const
{
	out << TAB;
	if( mPort.is< InstanceOfPort >() )
	{
		const InstanceOfPort & aPort = mPort.to< InstanceOfPort >();

		out << aPort.getNameID();

		if( mParameters.nonempty() )
		{
			out << AVM_STR_INDENT << "( ";

			Message::const_iterator itParam = mParameters.begin();
			Message::const_iterator endParam = mParameters.end();

			std::size_t offset = 1;
			std::size_t endOffset = aPort.getParameterCount();

			aPort.getParameterType(0).formatStream(out, *itParam);

			for( ++itParam ; (offset < endOffset) && (itParam != endParam) ;
					++itParam , ++offset )
			{
				out << " , ";
				aPort.getParameterType(offset).formatStream(out, *itParam);
			}

			for( ; itParam != endParam ; ++itParam )
			{
				out << " , " << itParam->str();
			}


			out << " )" << END_INDENT;
		}
	}
	else
	{
		out << TAB << "mid:" << getMID();

		if( mParameters.nonempty() )
		{
			out << AVM_STR_INDENT << "( ";

			Message::const_iterator itParam = mParameters.begin();
			Message::const_iterator endParam = mParameters.end();

			out << itParam->str();

			for( ++itParam ; itParam != endParam ; ++itParam )
			{
				out << " , " << itParam->str();
			}

			out << " )" << END_INDENT;
		}

	}

	if( mReceiverRID.valid() )
	{
		out << " --> " << mReceiverRID.strUniqId();
	}

	out << EOL_FLUSH;
}


void Message::toFscn(OutStream & out) const
{
	RuntimeID aRID = getSenderRID();

	for( ; aRID.hasPRID() ; aRID = aRID.getPRID() )
	{
		if( aRID.refExecutable().hasPort() )
		{
			break;
		}
	}

	if( hasPort() )
	{
		int dotPosition = getPort().getFullyQualifiedNameID().rfind('.',
				getPort().getFullyQualifiedNameID().size());
//		out << TAB2 << ":" << rid.strPid() << ":"
//			<< getPort().getFullyQualifiedNameID().substr(
//					rid->getInstance()->getFullyQualifiedNameID().size() + 1);
		out << TAB2 << ":" << aRID.strPid() << ":"
			<< getPort().getFullyQualifiedNameID().substr(dotPosition + 1);
	}
	else
	{
		out << TAB2 << ":" << aRID.strPid() << ":_";
	}

	if( hasParameter() )
	{
		out << "(" << AVM_NO_INDENT;

		Message::const_iterator it = beginParameters();
		Message::const_iterator endIt = endParameters();

		it->toStream(out);

		for( ++it ; it != endIt ; ++it )
		{
			out << " , ";
			it->toStream(out);
		}

		out << ")";

AVM_IF_DEBUG_ENABLED_AND( base_this_type::mPTR->mReceiverRID.valid() )
	out << " /* --> " << base_this_type::mPTR->mReceiverRID.strUniqId() << "*/";
AVM_ENDIF_DEBUG_ENABLED_AND

		out << ";" << END_INDENT_EOL;
	}
	else
	{
AVM_IF_DEBUG_ENABLED_AND( base_this_type::mPTR->mReceiverRID.valid() )
	out << " /* --> " << base_this_type::mPTR->mReceiverRID.strUniqId() << "*/";
AVM_ENDIF_DEBUG_ENABLED_AND

		out << ";" << EOL_FLUSH;
	}
}




}
