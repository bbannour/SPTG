/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "StatementFactory.h"

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableLib.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


/**
 * COLLECT
 * [state]machine
 */
void StatementFactory::collectRunMachine(ExecutableForm * anExecutableForm,
		const BF & aStatement, ListOfInstanceOfMachine & listOfMachine)
{
	switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode* aCode = aStatement.to_ptr< AvmCode >();

			switch( aCode->getAvmOpCode() )
			{
				case AVM_OPCODE_RUN:

//				case AVM_OPCODE_RESUME:
//				case AVM_OPCODE_RESTART:
				case AVM_OPCODE_START:
				{
					if( aCode->first().is< InstanceOfMachine >() )
					{
						listOfMachine.add_union(
								aCode->first().to_ptr< InstanceOfMachine >() );
					}
					break;
				}

				default:
				{
					AvmCode::iterator it = aCode->begin();
					AvmCode::iterator itEnd = aCode->end();
					for( ; it != itEnd ; ++it )
					{
						collectRunMachine(anExecutableForm, (*it), listOfMachine);
					}

					break;
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_union( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}


void StatementFactory::collectActivityMachine(
		ExecutableForm * anExecutableForm, AVM_OPCODE opCode,
		const BF & aStatement, ListOfInstanceOfMachine & listOfMachine)
{
	switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode* aCode = aStatement.to_ptr< AvmCode >();

			if( aCode->isOpCode(opCode) )
			{
				if( aCode->first().is< InstanceOfMachine >() )
				{
					listOfMachine.add_union(
							aCode->first().to_ptr< InstanceOfMachine >() );
				}
			}
			else
			{
				AvmCode::iterator it = aCode->begin();
				AvmCode::iterator itEnd = aCode->end();
				for( ; it != itEnd ; ++it )
				{
					collectActivityMachine(
							anExecutableForm, opCode, (*it), listOfMachine);
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_union( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}


void StatementFactory::collectActivityMachine(ExecutableForm * anExecutableForm,
		AVM_OPCODE opCode1, AVM_OPCODE opCode2,
		const BF & aStatement, ListOfInstanceOfMachine & listOfMachine)
{
	switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode* aCode = aStatement.to_ptr< AvmCode >();

			if( aCode->isOpCode(opCode1) || aCode->isOpCode(opCode2) )
			{
				if( aCode->first().is< InstanceOfMachine >() )
				{
					listOfMachine.add_union(
							aCode->first().to_ptr< InstanceOfMachine >() );
				}
			}
			else
			{
				AvmCode::iterator it = aCode->begin();
				AvmCode::iterator itEnd = aCode->end();
				for( ; it != itEnd ; ++it )
				{
					collectActivityMachine(anExecutableForm,
							opCode1, opCode2, (*it), listOfMachine);
				}
			}

			break;
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
//			listOfMachine.add_union( aStatement.to_ptr< InstanceOfMachine >() );

			break;
		}

		default:
		{
			break;
		}
	}
}


/**
 * COLLECT
 * Transition
 */
void StatementFactory::collectInvokeTransition(ExecutableForm * anExecutableForm,
		const BF & aStatement, ListOfAvmTransition & listOfTransition)
{
	switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode* aCode = aStatement.to_ptr< AvmCode >();

			switch( aCode->getAvmOpCode() )
			{
				case AVM_OPCODE_INVOKE_TRANSITION:
				{
					if( aCode->first().is< AvmTransition >() )
					{
						listOfTransition.add_union(
								aCode->first().to_ptr< AvmTransition >() );
					}
					break;
				}

				case AVM_OPCODE_SCHEDULE_INVOKE:
				{
					if( aCode->empty() )
					{
						collectInvokeTransition(anExecutableForm,
								anExecutableForm->getOnSchedule(),
								listOfTransition );
					}
					break;
				}

				default:
				{
					AvmCode::iterator it = aCode->begin();
					AvmCode::iterator itEnd = aCode->end();
					for( ; it != itEnd ; ++it )
					{
						collectInvokeTransition(
								anExecutableForm, (*it), listOfTransition);
					}

					break;
				}
			}

			break;
		}


		case FORM_AVMTRANSITION_KIND:
		{
//			listOfTransition.add_union( aStatement.to_ptr< AvmTransition >() );

			break;
		}


		default:
		{
			break;
		}
	}
}



/**
 * COLLECT
 * RID
 */
void StatementFactory::collectRID(const BF & aStatement,
		List< RuntimeID > & listOfRID)
{
	switch( aStatement.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode::iterator it = aStatement.to_ptr< AvmCode >()->begin();
			AvmCode::iterator itEnd = aStatement.to_ptr< AvmCode >()->end();
			for( ; it != itEnd ; ++it )
			{
				collectRID((*it), listOfRID);
			}

			break;
		}

		case FORM_RUNTIME_ID_KIND:
		{
			listOfRID.add_union( aStatement.bfRID() );

			break;
		}

		default:
		{
			break;
		}
	}
}



/**
 * CONTAINS
 * Activity on RID
 */
bool StatementFactory::containsOperationOnRID(AvmCode * aCode,
		const AVM_OPCODE opActivity, const RuntimeID & aRID)
{
	if( aCode->nonempty() )
	{
		AvmCode::iterator it = aCode->begin();

		if( aCode->isOpCode(opActivity) && ((aRID == (*it))
				/*|| aCode->contains(aRID)*/) )
		{
			return( true );
		}

		AvmCode::iterator itEnd = aCode->end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).is< AvmCode >() && containsOperationOnRID(
					(*it).to_ptr< AvmCode >(), opActivity, aRID) )
			{
				return( true );
			}
		}
	}

	return( false );
}


/**
 * get activity
 * ExecutableForm
 * or
 * RuntimeID
 */
ExecutableForm * StatementFactory::getActivityTargetExecutable(
		AvmProgram * anAvmProgram, AvmCode * aCode)
{
//		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aCode )	<< "AvmCode !!!"
//				<< SEND_EXIT;

	if( aCode->empty() )
	{
		return( anAvmProgram->getExecutable() );
	}
	else // if( aCode->singleton() )
	{
		if( aCode->first() == ExecutableLib::MACHINE_SELF )
		{
			return( anAvmProgram->getExecutable() );
		}
		else if( aCode->first().is< InstanceOfMachine >() )
		{
			return( aCode->first().to_ptr< InstanceOfMachine >()
					->getExecutable() );
		}
		else if( aCode->first().is< RuntimeID >() )
		{
			return( aCode->first().as_bf< RuntimeID >().getExecutable() );
		}
	}

	return( NULL );
}


const RuntimeID & StatementFactory::getActivityTargetRID(
		const ExecutionData & anED, const RuntimeID & aRID, AvmCode * aCode)
{
	if( aCode->empty() )
	{
		return( aRID );
	}
	else // if( aCode->singleton() )
	{
		if( aCode->first() == ExecutableLib::MACHINE_SELF )
		{
			return( aRID );
		}
		else if( aCode->first().is< RuntimeID >() )
		{
			return( aCode->first().as_bf< RuntimeID >() );
		}
		else if( aCode->first().is< InstanceOfMachine >() )
		{
			return( anED.getRuntimeID(
					aCode->first().to_ptr< InstanceOfMachine >()) );
		}
	}

	return( RuntimeID::REF_NULL );
}



}
