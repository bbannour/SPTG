/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 janv. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmBufferPrimitive.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/executable/InstanceOfBuffer.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/runtime/Message.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER APPEND
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_APPEND::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		// get the optional port parameter
		Message aMsg;
		if( ENV.mARG->at(1).is< Message >() )
		{
			aMsg = ENV.mARG->at(1);
		}
		else
		{
			BF aPort;
			if( ENV.mARG->at(1).is< InstanceOfPort >() )
			{
				aPort = ENV.mARG->at(1);
				ENV.mARG->begin(2);
			}
			else
			{
				ENV.mARG->begin(1);
			}
			aMsg = Message(ENV.mARG->outED.getRID(), aPort);

			// get other parameters
			for( ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				aMsg.appendParameter( ENV.mARG->current() );
			}

AVM_IF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to append in buffer" << std::endl;
	aMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
		}

		// append the message in the buffer
		if( ENV.mARG->at(0).to< BaseBufferForm >().push(aMsg) )
		{
			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}
	}

	else if( ENV.mARG->at(0).is< BuiltinContainer >() )
	{
		BuiltinContainer * bc = ENV.mARG->at(0).to_ptr< BuiltinContainer >();

		bool isAppend = false;
		for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
		{
			if( bc->add( ENV.mARG->current() ) )
			{
				isAppend = true;
			}
			else
			{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << APPEND >> : "
			<<  ENV.mARG->outED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
	AVM_OS_TRACE << "\t" << "<capacity:" << bc->capacity()
			<< "> " << bc->str() << " <=< "
			<< ENV.mARG->current().str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

				break;
			}
		}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << bc->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

		if( isAppend )
		{
			ENV.appendOutput( ENV.mARG->outED );
			return( true );
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER REMOVE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_REMOVE::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		BaseBufferForm * bbf = ENV.mARG->at(0).to_ptr< BaseBufferForm >();

		if( ENV.mARG->at(1).is< InstanceOfPort >() )
		{
AVM_IF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to remove in buffer:>"
			<< std::endl << TAB2 << "buffer: " << str_header( bbf->getInstance() )
			<< std::endl << TAB2 << "port  : "
			<< str_header( ENV.mARG->at(1).to< InstanceOfPort >() )
			<< std::endl << TAB2 << "buffer:av>" << bbf->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG2( BUFFER , COMMUNICATION )

			bbf->remove( ENV.mARG->at(1).to_ptr< InstanceOfPort >() );

AVM_IF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
	AVM_OS_TRACE << TAB2 << "buffer:ap>" << bbf->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG2( BUFFER , COMMUNICATION )

		}

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	else if( ENV.mARG->at(0).is< BuiltinContainer >() )
	{
		BuiltinContainer * bc = ENV.mARG->at(0).to_ptr< BuiltinContainer >();

		for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
		{
			bc->remove( ENV.mARG->current() );
		}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << bc->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER CLEAR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_CLEAR::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.mARG->at(0).to< BaseBufferForm >().clear();
	}

	else if( ENV.mARG->at(0).is< BuiltinContainer >() )
	{
		ENV.mARG->at(0).to< BuiltinContainer >().clear();
	}

	ENV.appendOutput( ENV.mARG->outED );

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER RESIZE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_RESIZE::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.mARG->at(0).to< BaseBufferForm >().resize(
				ENV.mARG->at(1).toInteger());
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.mARG->at(0).to< BuiltinCollection >().resize(
				ENV.mARG->at(1).toInteger());
	}

	ENV.appendOutput( ENV.mARG->outED );

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER PUSH
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_PUSH::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		// get the optional port parameter
		Message aMsg;
		if( ENV.mARG->at(1).is< Message >() )
		{
			aMsg = ENV.mARG->at(1);
		}
		else
		{
			BF aPort;
			if( ENV.mARG->at(1).is< InstanceOfPort >() )
			{
				aPort = ENV.mARG->at(1);
				ENV.mARG->begin(2);
			}
			else
			{
				ENV.mARG->begin(1);
			}
			aMsg = Message(ENV.mARG->outED.getRID(), aPort);

			// get other parameters
			for( ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				aMsg.appendParameter( ENV.mARG->current() );
			}

AVM_IF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to append in buffer" << std::endl;
	aMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
		}

		// append the message in the buffer
		if( ENV.mARG->at(0).to< BaseBufferForm >().push(aMsg) )
		{
			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}
	}

	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		BuiltinQueue * queue = ENV.mARG->at(0).to_ptr< BuiltinQueue >();
		if( queue != nullptr )
		{
			bool isAppend = false;
			for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				if( queue->push( ENV.mARG->current() ) )
				{
					isAppend = true;
				}
				else
				{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << PUSH >> : "
			<<  ENV.mARG->outED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
	AVM_OS_TRACE << "\t" << "<capacity:" << queue->capacity()
			<< "> " << queue->str() << " <=< "
			<< ENV.mARG->current().str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

					break;
				}
			}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

			if( isAppend )
			{
				ENV.appendOutput( ENV.mARG->outED );
				return( true );
			}
		}
		else
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << PUSH >> : "
			<<  ENV.mARG->outED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
	AVM_OS_TRACE << "\t" << "Unfound queue for << "
			<< ENV.mARG->at(0).str() << " >>" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}
	}

	else if( ENV.mARG->at(0).is< BuiltinContainer >() )
	{
		BuiltinContainer * bc = ENV.mARG->at(0).to_ptr< BuiltinContainer >();

		bool isAppend = false;
		for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
		{
			if( bc->add( ENV.mARG->current() ) )
			{
				isAppend = true;
			}
			else
			{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << PUSH >> : "
			<<  ENV.mARG->outED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
	AVM_OS_TRACE << "\t" << "<capacity:" << bc->capacity()
			<< "> " << bc->str() << " <=< "
			<< ENV.mARG->current().str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

				break;
			}
		}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << bc->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

		if( isAppend )
		{
			ENV.appendOutput( ENV.mARG->outED );
			return( true );
		}
	}

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER ASSIGN_TOP
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_ASSIGN_TOP::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		// get the optional port parameter
		Message aMsg;
		if( ENV.mARG->at(1).is< Message >() )
		{
			aMsg = ENV.mARG->at(1);
		}
		else
		{
			BF aPort;
			if( ENV.mARG->at(1).is< InstanceOfPort >() )
			{
				aPort = ENV.mARG->at(1);
				ENV.mARG->begin(2);
			}
			else
			{
				ENV.mARG->begin(1);
			}
			aMsg = Message(ENV.mARG->outED.getRID(), aPort);

			// get other parameters
			for( ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				aMsg.appendParameter( ENV.mARG->current() );
			}

AVM_IF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to assign#top in buffer" << std::endl;
	aMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
		}

		// append the message in the buffer
		if( ENV.mARG->at(0).to< BaseBufferForm >().top( aMsg) )
		{
			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}
	}
	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		BuiltinQueue * queue = ENV.mARG->at(0).to_ptr< BuiltinQueue >();
		if( queue->nonempty() )
		{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:queue> " << queue->str() << std::endl
			<< "rvalue:> " << ENV.mARG->at(1).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

			if( queue->top( ENV.mARG->at(1) ) )
			{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "queue> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

				ENV.appendOutput( ENV.mARG->outED );

				return( true );
			}
		}
	}

	return( false );
}


bool AvmPrimitive_ASSIGN_TOP::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		// get the optional port parameter
		Message aMsg;
		if( ENV.mARG->at(1).is< Message >() )
		{
			aMsg = ENV.mARG->at(1);
		}
		else
		{
			BF aPort;
			if( ENV.mARG->at(1).is< InstanceOfPort >() )
			{
				aPort = ENV.mARG->at(1);
			}
			aMsg = Message(ENV.mARG->outED.getRID(), aPort);

			// get other parameters
			for( ENV.mARG->begin(2) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				aMsg.appendParameter( ENV.mARG->current() );
			}

AVM_IF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
	AVM_OS_TRACE << TAB << "Output Message to assign#top in buffer" << std::endl;
	aMsg.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG2( BUFFER , COMMUNICATION )
		}

		// append the message in the buffer
		if( ENV.mARG->at(0).to< BaseBufferForm >().top( aMsg) )
		{
			ENV.outVAL = aMsg;

			return( true );
		}
	}
	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		BuiltinQueue * queue = ENV.mARG->at(0).to_ptr< BuiltinQueue >();
		if( (queue != nullptr) && queue->nonempty() )
		{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:queue> " << queue->str() << std::endl
			<< "rvalue:> " << ENV.mARG->at(1).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

			if( queue->top( ENV.mARG->at(1) ) )
			{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "queue> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

				ENV.outVAL = ENV.mARG->at(1);

				return( true );
			}
		}
		else if( queue == nullptr )
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << ASSING#TOP >> : "
			<<  ENV.inED.getRID().strUniqId() << " |=> "
			<< ENV.inCODE->str() << std::endl;
	AVM_OS_TRACE << "\t" << "Unfound builtin queue for << "
			<< ENV.mARG->at(0).str() << " >>" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}
	}

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER TOP
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_TOP::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		Message aMsg = ENV.mARG->at(0).to< BaseBufferForm >().top();

		if( aMsg.valid() && (ENV.mARG->count > 1) )
		{
			if( ENV.mARG->at(1).is< InstanceOfData >() &&
					ENV.mARG->at(1).to< InstanceOfData >().isTypedMessage() )
			{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:msg> " << aMsg.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

				if( not ENV.setRvalue(ENV.mARG->outED,
						ENV.mARG->at(1).to< InstanceOfData >(), aMsg) )
				{
					return( false );
				}
			}
			else
			{
				// We have to ignore the << Buffer >>
				Message::const_iterator itValue = aMsg.beginParameters();
				Message::const_iterator endValue = aMsg.endParameters();
				ENV.mARG->begin(1);
				for( ; ENV.mARG->hasNext() && (itValue != endValue) ;
						ENV.mARG->next() , ++itValue )
				{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> " << ENV.mARG->current().str() << std::endl
			<< "rvalue:> " << (*itValue).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

					if( not ENV.setRvalue(ENV.mARG->outED,
							ENV.mARG->current().to< InstanceOfData >(),
							(*itValue)) )
					{
						return( false );
					}
				}
			}

			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}

		return( aMsg.valid() );
	}
	else //if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		BuiltinQueue * queue = ENV.mARG->at(0).to_ptr< BuiltinQueue >();
		if( ENV.mARG->count > 1 )
		{
			BF popValue;
			for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				popValue = queue->top();

				if( popValue.invalid() )
				{
					return( false );
				}
				else
				{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << popValue.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

					if( not ENV.setRvalue(ENV.mARG->outED,
							ENV.mARG->current().to< InstanceOfData >(),
							popValue) )
					{
						return( false );
					}
				}
			}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:queue> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}
	}

	return( false );
}


bool AvmPrimitive_TOP::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ENV.mARG->at(0).to< BaseBufferForm >().top();
	}

	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
//		AVM_OS_TRACE << "queue->top :> " << ENV.mARG->at(0).str()
//				<< " = " << ENV.getWritableQueue(ENV.mARG->outED,
//						ENV.mARG->at(0)).str() << std::endl;

		ENV.outVAL = ENV.mARG->at(0).to< BuiltinQueue >().top();
	}

	return( ENV.outVAL.valid() );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER POP
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_POP::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		Message aMsg = ENV.mARG->at(0).to< BaseBufferForm >().pop();

		if( aMsg.valid() && (ENV.mARG->count > 1) )
		{
			if( ENV.mARG->at(1).is< InstanceOfData >() &&
					ENV.mARG->at(1).to< InstanceOfData >().isTypedMessage() )
			{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:msg> " << aMsg.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

				if( not ENV.setRvalue(ENV.mARG->outED,
						ENV.mARG->at(1).to< InstanceOfData >(), aMsg) )
				{
					return( false );
				}
			}
			else
			{
				// We have to ignore the << Buffer >>
				Message::const_iterator itValue = aMsg.beginParameters();
				Message::const_iterator endValue = aMsg.endParameters();
				ENV.mARG->begin(1);
				for( ; ENV.mARG->hasNext() && (itValue != endValue) ;
						ENV.mARG->next() , ++itValue )
				{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> " << ENV.mARG->current().str() << std::endl
			<< "rvalue:> " << (*itValue).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

					if( not ENV.setRvalue(ENV.mARG->outED,
							ENV.mARG->current().to< InstanceOfData >(),
							(*itValue)) )
					{
						return( false );
					}
				}
			}

			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}

		return( aMsg.valid() );
	}

	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		BuiltinQueue * queue = ENV.mARG->at(0).to_ptr< BuiltinQueue >();
		if( ENV.mARG->count == 1 )
		{
			queue->pop();
		}
		else //if( ENV.mARG->count > 1 )
		{
			BF popValue;
			for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				popValue = queue->pop();

				if( popValue.invalid() )
				{
					return( false );
				}
				else
				{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->current().to_ptr< InstanceOfData >() )
			<< std::endl
			<< "rvalue:> " << popValue.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

					if( not ENV.setRvalue(ENV.mARG->outED,
							ENV.mARG->current().to< InstanceOfData >(),
							popValue) )
					{
						return( false );
					}
				}
			}
		}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:queue> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	else if( ENV.mARG->at(0).is< BuiltinContainer >() )
	{
		BuiltinContainer * bc = ENV.mARG->at(0).to_ptr< BuiltinContainer >();

		if( bc->nonempty() )
		{
			BF popValue = bc->pop_first();

			if( popValue.valid()
				&& ENV.setRvalue(ENV.mARG->outED,
						ENV.mARG->at(1).to< InstanceOfData >(), popValue) )
			{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->at(1).to_ptr< InstanceOfData >() )
			<< std::endl
			<< "pop$rvalue:> " << popValue.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

				ENV.appendOutput( ENV.mARG->outED );

				return( true );
			}
		}
	}

	return( false );
}


bool AvmPrimitive_POP::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ENV.mARG->at(0).to< BaseBufferForm >().pop();
	}

	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		ENV.outVAL = ENV.mARG->at(0).to< BuiltinQueue >().pop();
	}

	else if( ENV.mARG->at(0).is< BuiltinContainer >() )
	{
		ENV.outVAL = ENV.mARG->at(0).to< BuiltinContainer >().pop();
	}

	return( ENV.outVAL.valid() );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER POP FROM
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_POP_FROM::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		Message aMsg = ENV.mARG->at(0).to< BaseBufferForm >().pop();

		if( aMsg.valid() && (ENV.mARG->count > 1) )
		{
			if( ENV.mARG->at(1).is< InstanceOfData >() &&
					ENV.mARG->at(1).to< InstanceOfData >().isTypedMessage() )
			{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:msg> " << aMsg.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

				if( not ENV.setRvalue(ENV.mARG->outED,
						ENV.mARG->at(1).to< InstanceOfData >(), aMsg) )
				{
					return( false );
				}
			}
			else
			{
				// We have to ignore the << Buffer >>
				Message::const_iterator itValue = aMsg.beginParameters();
				Message::const_iterator endValue = aMsg.endParameters();
				ENV.mARG->begin(1);
				for( ; ENV.mARG->hasNext() && (itValue != endValue) ;
						ENV.mARG->next() , ++itValue )
				{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> " << ENV.mARG->current().str() << std::endl
			<< "rvalue:> " << (*itValue).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

					if( not ENV.setRvalue(ENV.mARG->outED,
							ENV.mARG->current().to< InstanceOfData >(),
							(*itValue)) )
					{
						return( false );
					}
				}
			}

			ENV.appendOutput( ENV.mARG->outED );

			return( true );
		}

		return( aMsg.valid() );
	}
	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
		BuiltinQueue * queue = ENV.mARG->at(0).to_ptr< BuiltinQueue >();
		if( ENV.mARG->count == 1 )
		{
			queue->pop();
		}
		else //if( ENV.mARG->count > 1 )
		{
			BF popValue;
			for( ENV.mARG->begin(1) ; ENV.mARG->hasNext() ; ENV.mARG->next() )
			{
				popValue = queue->pop();

				if( popValue.invalid() )
				{
					return( false );
				}
				else
				{
AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:> " << popValue.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

					if( not ENV.setRvalue(ENV.mARG->outED,
							ENV.mARG->current().to< InstanceOfData >(),
							popValue) )
					{
						return( false );
					}
				}
			}
		}

AVM_IF_DEBUG_FLAG( ASSIGNMENT )
	AVM_OS_TRACE << "rvalue:queue> " << queue->str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( ASSIGNMENT )

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_POP_FROM::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ENV.mARG->at(0).to< BaseBufferForm >().pop();
	}

	else if( ENV.mARG->at(0).is< BuiltinQueue >() )
	{
//		AVM_OS_TRACE << "queue :> " << ENV.mARG->at(0).str() << std::endl;

		ENV.outVAL = ENV.mARG->at(0).to< BuiltinQueue >().pop();

//		AVM_OS_TRACE << "queue->pop :> " << ENV.mARG->at(0).str() << std::endl;
	}

	return( ENV.outVAL.valid() );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER EMPTY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_EMPTY::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BaseBufferForm >().empty() );
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BuiltinCollection >().empty() );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER NONEMPTY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_NONEMPTY::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BaseBufferForm >().nonempty() );
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BuiltinCollection >().nonempty() );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER SINGLETON
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_SINGLETON::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BaseBufferForm >().singleton() );
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BuiltinCollection >().singleton() );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER POPULATED
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_POPULATED::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BaseBufferForm >().populated() );
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BuiltinCollection >().populated() );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER FULL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_FULL::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BaseBufferForm >().full() );
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BuiltinCollection >().full() );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER SIZE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_SIZE::seval(EvaluationEnvironment & ENV)
{
	if( ENV.mARG->at(0).is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newInteger(
				ENV.mARG->at(0).to< BaseBufferForm >().size() );
	}

	else if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newInteger(
				ENV.mARG->at(0).to< BuiltinCollection >().size() );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER CONTAINS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_CONTAINS::seval(EvaluationEnvironment & ENV)
{
	/*if( container.is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(0).to< BaseBufferForm >().
						contains( ENV.mARG->at(1) ) );
	}

	else*/ if( ENV.mARG->at(0).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean( ENV.mARG->at(0).
				to< BuiltinCollection >().contains( ENV.mARG->at(1) ) );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(0).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER IN
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_IN::seval(EvaluationEnvironment & ENV)
{
	/*if( container.is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				ENV.mARG->at(1).to< BaseBufferForm >().
						contains( ENV.mARG->at(0) ) );
	}

	else*/ if( ENV.mARG->at(1).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean( ENV.mARG->at(1).
				to< BuiltinCollection >().contains( ENV.mARG->at(0) ) );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(1).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BUFFER NOTIN
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_NOTIN::seval(EvaluationEnvironment & ENV)
{
	/*if( container.is< BaseBufferForm >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean(
				! ENV.mARG->at(1).to< BaseBufferForm >().
						contains( ENV.mARG->at(0) ) );
	}

	else*/ if( ENV.mARG->at(1).is< BuiltinCollection >() )
	{
		ENV.outVAL = ExpressionConstructor::newBoolean( not ENV.mARG->at(1).
				to< BuiltinCollection >().contains( ENV.mARG->at(0) ) );
	}

	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected a NON-BUILTIN-COLLECTION for the value << "
				<< ENV.mARG->at(1).str() << " >> !!!"
				<< SEND_EXIT;

		return( false );
	}

	return( true );
}




}
