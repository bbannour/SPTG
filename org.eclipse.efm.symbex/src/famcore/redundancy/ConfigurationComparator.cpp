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
#include "ConfigurationComparator.h"

#include  <famcore/redundancy/RedundancyFilter.h>

#include <fml/executable/ExecutableQuery.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfRuntimeFormState.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{


bool BaseConfigurationComparator::equals(
		const ExecutionData & firstED, const BF & firstSchedule,
		const ExecutionData & sndED  , const BF & sndSchedule)
{
	return( firstED.getRuntimeFormStateTable()->
			equalsState( sndED.getRuntimeFormStateTable() ) );
}

/*!ALTERNATIVE!*
bool BaseConfigurationComparator::equals2(
		const ExecutionData & firstED, const BF & firstSchedule,
		const ExecutionData & sndED  , const BF & sndSchedule)
{
	if( firstSchedule.valid() && sndSchedule.valid() )
	{
//		AVM_OS_TRACE << "Compare :" << std::endl;
//		AVM_OS_TRACE << "\t" << firstSchedule->str() << std::endl;
//		AVM_OS_TRACE << "\t" << sndSchedule->str() << std::endl;

		if( firstSchedule == sndSchedule )
		{
			if( firstSchedule.is< RuntimeID >() )
			{
				return( equals(
						firstED, firstED.getRuntime(
								firstSchedule.bfRID() ).getOnSchedule(),
						sndED, sndED.getRuntime(
								sndSchedule.bfRID() ).getOnSchedule()) );
			}
			else if( firstSchedule.is< AvmCode >() )
			{
				for( const auto & itArg :
						firstSchedule.to< AvmCode >().getOperands() )
				{
					if( not equals(firstED, itArg, sndED, itArg) )
					{
						return( false );
					}
				}
				return( true );
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "Unexpected Schedule Element Type << "
						<< firstSchedule.str() << " >> !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
		else if( firstSchedule.classKind() == sndSchedule.classKind() )
		{
			if( firstSchedule.is< RuntimeID >() )
			{
				return( (firstSchedule == sndSchedule)&& equals(
						firstED, firstED.getRuntime(
								firstSchedule.bfRID() ).getOnSchedule(),
						sndED, sndED.getRuntime(
								sndSchedule.bfRID() ).getOnSchedule()) );
			}
			else if( firstSchedule.is< AvmCode >() )
			{
				const AvmCode & firstCode = firstSchedule.to< AvmCode >();
				const AvmCode & sndCode = sndSchedule.to< AvmCode >();

				if( (firstCode.sameOperator( sndCode )) &&
					(firstCode.size() == sndCode.size()) )
				{
					auto itOperandFirst = firstCode.begin();
					auto itOperandSnd = sndCode.begin();
					for(  ; itOperandFirst != firstCode.end() ;
							++itOperandFirst , ++itOperandSnd )
					{
						if( not equals(firstED,
								*itOperandFirst, sndED, *itOperandSnd) )
						{
							return( false );
						}
					}
					return( true );
				}

				return( false );
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "Unexpected Schedule Element Type!!!!!"
						<< SEND_EXIT;

				return( false );
			}
		}
		else
		{
			return( false );
		}
	}
	else
	{
		return( firstSchedule == sndSchedule );
	}
}
*!ALTERNATIVE!*/


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ALL CONFIGURATION COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AllConfigurationComparator::equals(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	if( ((& newEC) == (& oldEC)) || newEC.edTEQ( oldEC ) )
	{
		return( true );
	}

	if( newEC.getExecutionData().getTableOfRuntime().size() !=
			oldEC.getExecutionData().getTableOfRuntime().size() )
	{
		return( false );
	}


	return( equals(newEC.getExecutionData(),
			newEC.getExecutionData().getOnSchedule(),
			oldEC.getExecutionData(),
			oldEC.getExecutionData().getOnSchedule() ) );

//	return( strStateConf(newEC.getExecutionData()) ==
//			strStateConf(oldEC.getExecutionData()) );
}



bool AllConfigurationComparator::equals(
		const ExecutionData & firstED, const BF & firstSchedule,
		const ExecutionData & sndED, const BF & sndSchedule)
{
	return( firstED.getRuntimeFormStateTable()->
			equalsState( sndED.getRuntimeFormStateTable() ) );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// DETAILS CONFIGURATION COMPARATOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool DetailConfigurationComparator::configure(const WObject * wfParameterObject)
{
	const WObject * theDETAILS = Query::getRegexWSequence(wfParameterObject,
			OR_WID2("control_state", "CONTROL_STATE"), wfParameterObject);

	if( theDETAILS != WObject::_NULL_ )
	{
		const ExecutionData & theED = mConfiguration.getMainExecutionData();

		ExecutableForm * anExecutable = nullptr;

		ListOfExecutableForm listOfExecutable;
		ListOfInstanceOfMachine listOfInstance;

		ExecutableQuery XQuery( mConfiguration );

		WObject::const_iterator itWfO = theDETAILS->owned_begin();
		WObject::const_iterator endWfO = theDETAILS->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				const std::string & kind = (*itWfO)->getNameID();
				const std::string & qnid = (*itWfO)->toStringValue();

				if( (kind == "model") || (kind == "form") )
				{
					anExecutable = XQuery.getExecutable(
							qnid ).to_ptr< ExecutableForm >();
					if( anExecutable != nullptr )
					{
						listOfExecutable.append(anExecutable);
					}
					else
					{
						AVM_OS_WARN << "Unfound the machine "<< kind << " << "
								<< qnid << " >> as processor parameter:> "
								<< wfParameterObject->strHeader()
								<< std::endl;
					}
				}
				else if( kind == "instance" )
				{
					const BF & anInstance = XQuery.getMachine(
							Specifier::DESIGN_INSTANCE_KIND, qnid );
					if( anInstance.valid() )
					{
						listOfInstance.append(
								anInstance.to_ptr< InstanceOfMachine >());
					}
					else
					{
						AVM_OS_WARN << "Unfound the machine " << kind << " << "
								<< qnid << " >> as processor parameter:> "
								<< wfParameterObject->strHeader()
								<< std::endl;
					}
				}
				else
				{
					AVM_OS_WARN << "Unexpected attribute << "
							<< (*itWfO)->str()
							<< " >> as processor parameter:> "
							<< wfParameterObject->strHeader()
							<< std::endl;
				}
			}
		}

		computeIgnoreMachine(theED, listOfExecutable, listOfInstance);

	}
	else
	{
		AVM_OS_WARN << "Unfound section << DETAILS >> as state scope parameter";
	}

	return( true );

}


void DetailConfigurationComparator::appendFamilyMachine(
		const ExecutionData & anED, const RuntimeID & aRID)
{
	if( aRID.invalid() )
	{
		return;
	}

	mListOfIgnoreMachine.append(aRID);

	const RuntimeForm & aRF = anED.getRuntime(aRID);
	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator it = aRF.beginChild();
		TableOfRuntimeID::const_iterator endIt = aRF.endChild();
		for( ; it != endIt ; ++it )
		{
			appendFamilyMachine( anED , anED.getRuntime(*it).getRID() );
		}
	}
}


void DetailConfigurationComparator::computeIgnoreMachine(
		const ExecutionData & anED, ListOfExecutableForm & listOfExecutable,
		ListOfInstanceOfMachine & listOfInstance)
{
	for( const auto & itMachine : listOfInstance )
	{
		appendFamilyMachine( anED ,  anED.getRuntimeID(* itMachine) );
	}
}



bool DetailConfigurationComparator::equals(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	if( restrictedRunnableElementTrace(newEC.getRunnableElementTrace()) )
	{
		return( false );
	}
	else
	{
		return( newEC.getExecutionData().getRuntimeFormStateTable()->equalsState(
				oldEC.getExecutionData().getRuntimeFormStateTable() ) );
	}
}


bool DetailConfigurationComparator::restrictedRunnableElementTrace(const BF & form)
{
	if( form.is< ExecutionConfiguration >() )
	{
		ExecutionConfiguration * aConf = form.to_ptr< ExecutionConfiguration >();

		return( mListOfIgnoreMachine.contains(aConf->getRuntimeID()) );
	}

	else if( form.is< AvmCode >() )
	{
		for( const auto & itCode : form.to< AvmCode >().getOperands() )
		{
			if( not restrictedRunnableElementTrace(itCode) )
			{
				return( false );
			}
		}

		return( true );
	}

	else
	{
		return( true );
	}
}


}
