/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 mars 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "RuntimeQuery.h"

#include <fml/executable/ExecutableQuery.h>

#include <fml/workflow/UniFormIdentifier.h>
#include <fml/workflow/WObject.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// STATIC TOOLS
// Used during configuration step
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * SEARCH
 * Symbol
 * !UNUSED!
 *
const BF & RuntimeQuery::searchSymbol(WObject * aWProperty)
{
	const std::string & kind = aWProperty->getNameID();
	const std::string & qnid = aWProperty->toStringValue();

	ExecutableQuery XQuery( mConfiguration );

	if( (kind == "variable") || (kind == "var") )
	{
		const BF & aSymbol = XQuery.getDataByQualifiedNameID( qnid );
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}

	else if( (kind == "model") || (kind == "form") )
	{
		const BF & aSymbol = XQuery.searchMachine(
				Specifier::DESIGN_MODEL_KIND, qnid);
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}

	else if( kind == "instance" )
	{
		const BF & aSymbol = XQuery.searchMachine(
				Specifier::DESIGN_INSTANCE_KIND, qnid );
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}

	else if( kind == "executable" )
	{
		const BF & anExecutable = XQuery.getExecutableByQualifiedNameID( qnid );
		if( anExecutable.valid() )
		{
			return( anExecutable );
		}
	}

	else if( kind == "transition" )
	{
		const BF & aSymbol = XQuery.getTransitionByQualifiedNameID( qnid );
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}
	else if( kind == "routine" )
	{
		const BF & aSymbol = XQuery.getProgramByQualifiedNameID(
				qnid, Specifier::SCOPE_ROUTINE_KIND );
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}
	else if( kind == "program" )
	{
		const BF & aSymbol = XQuery.getProgramByQualifiedNameID(
				qnid, Specifier::SCOPE_UNDEFINED_KIND );
//				qnid, Specifier::SCOPE_PROGRAM_KIND   );
		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}

	else
	{
		AVM_OS_WARN << "Unexpected attribute << " << aWProperty->str()
				<< " >> as coverage processor parameter";
	}

	return( BF::REF_NULL );
}

avm_size_t RuntimeQuery::searchSymbol(
		WObject * aWProperty, BFList & listofSymbol )
{
	avm_size_t count = 0;

	const std::string & kind = aWProperty->getNameID();
	const std::string & qnid = aWProperty->toStringValue();

	ExecutableQuery XQuery( mConfiguration );

	if( (kind == "variable") || (kind == "var") )
	{
		count += XQuery.getDataByQualifiedNameID(qnid, listofSymbol);
	}

	else if( (kind == "model") || (kind == "form") )
	{
		//!!Symbol
//		count += searchMachine(aSystem, Specifier::DESIGN_MODEL_KIND,
//				qnid, listofSymbol );
	}

	else if( kind == "instance" )
	{
		//!!Symbol
//		count += searchMachine(aSystem, Specifier::DESIGN_INSTANCE_KIND,
//				qnid, listofSymbol );
	}

	else if( kind == "executable" )
	{
		count += XQuery.getExecutableByQualifiedNameID(qnid, listofSymbol);
	}

	else if( kind == "transition" )
	{
		count += XQuery.getTransitionByQualifiedNameID(qnid, listofSymbol );
	}

	else if( kind == "routine" )
	{
		count += XQuery.getProgramByQualifiedNameID(qnid,
				Specifier::SCOPE_ROUTINE_KIND, listofSymbol);
	}

	else if( kind == "program" )
	{
		count += XQuery.getProgramByQualifiedNameID(
				qnid, Specifier::SCOPE_UNDEFINED_KIND, listofSymbol );
//				qnid, Specifier::SCOPE_PROGRAM_KIND  , listofSymbol )
	}

	else
	{
		AVM_OS_WARN << "Unexpected attribute << " << aWProperty->str()
				<< " >> as coverage processor parameter";
	}

	return( count );
}
*
* !UNUSED!
*/

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// RUNTIME TOOLS
// Used during execution< processing / filtering > step
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * SEARCH
 * Variable
 */
BF RuntimeQuery::searchVariable(const ExecutionData & anED,
		const RuntimeID & ctxRID, const std::string & aFullyQualifiedNameID) const
{
	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::
		reverse_iterator it = anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::
		reverse_iterator itEnd = anED.getLocalRuntimes()->rend();
		for(  ; it != itEnd ; ++it )
		{
			const BF & anInstance = (*it).getProgram()->getAllData().
					getByFQNameID( aFullyQualifiedNameID );
			if( anInstance.valid() )
			{
				return( anInstance );
			}
		}
	}


	UniFormIdentifier anUFI(aFullyQualifiedNameID);

	std::ostringstream osUFI;

	UniFormIdentifier::iterator it = anUFI.begin();
	UniFormIdentifier::iterator itEnd = anUFI.end();

	// recherche de la machine PRINCIPALE (ROOT)
	osUFI << "inst::" << (*it).str();

	const RuntimeID & theSystemRID = anED.getSystemRID();
	RuntimeID theMachineID = theSystemRID;

	for( ++it ; (it != itEnd) ; ++it )
	{
		if( theMachineID.getInstance()->fqnEquals( osUFI.str() ) )
		{
			break;
		}
		osUFI << "." << (*it).str();
	}

	if( it != itEnd )
	{
		VectorOfInstanceOfMachine aliasPath;

		RuntimeID rid = theMachineID;

		// comme c'est la spec RID
//		aliasPath.append( theMachineID.getInstance() );

		// recherche de la machine FEUILLE
		for( ; it != itEnd ; ++it)
		{
			osUFI << "." << (*it).str();
			rid = anED.getRuntime(rid).getChild( osUFI.str() );
			if( rid.valid() )
			{
				theMachineID = rid;
				aliasPath.append( theMachineID.getInstance() );
			}
			else
			{
				break;
			}
		}

		if( (it == itEnd) && (theMachineID == theSystemRID) )
		{
			--it;
		}

		if( it != itEnd )
		{
			ExecutableForm * anExecutable = theMachineID.getExecutable();
			osUFI.str( "" );
			osUFI << "inst::"                    // "exec::".size() == 6
					<< anExecutable->getFullyQualifiedNameID().substr( 6 );


			for( ; it != itEnd ; ++it)
			{
				osUFI << "." << (*it).str();
			}


			// The ORIGINAL INSTANCE
			InstanceOfData * anInstance =
					anExecutable->getAllData().rawByFQNameID( osUFI.str() );

			if( anInstance != NULL )
			{
				anInstance = anExecutable->getConstData().rawByFQNameID(
						osUFI.str() );
			}

			if( anInstance != NULL )
			{
				if( aliasPath.nonempty() )
				{
					anInstance = new InstanceOfData(
							theSystemRID.getExecutable(),
							anInstance, aliasPath );

					anInstance->setCreatorContainerRID( theMachineID );
					anInstance->setRuntimeContainerRID( theMachineID );

					return( BF( anInstance ) );
				}

//				AVM_OS_TRACE << TAB << "Searching " << anUFI->str() << std::endl;
//				AVM_OS_TRACE << TAB << "Found " << std::endl;
//				anInstance->serialize(AVM_OS_TRACE << TAB);
//				AVM_OS_TRACE << std::flush;
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & RuntimeQuery::searchVariable(const ExecutionData & anED,
		const RuntimeID & ctxRID, const ObjectElement * astElement) const
{
	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::
		reverse_iterator it = anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::
		reverse_iterator itEnd = anED.getLocalRuntimes()->rend();
		for(  ; it != itEnd ; ++it )
		{
			const BF & anInstance =
				(*it).getProgram()->getAllData().getByAstElement(astElement);
			if( anInstance.valid() )
			{
				return( anInstance );
			}
		}
	}

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF)
	{
		const BF & anInstance =
			(*itRF)->getExecutable()->getAllData().getByAstElement(astElement);
		if( anInstance.valid() )
		{
			return( anInstance );
		}
	}

	return( BF::REF_NULL );
}



BF RuntimeQuery::searchVariable(const ExecutionData & anED,
		const RuntimeID & ctxRID, const BF & aSymbolicParameter) const
{
	if( aSymbolicParameter.is< InstanceOfData >() )
	{
		InstanceOfData * aParamInstance =
				aSymbolicParameter.to_ptr< InstanceOfData >();

		RuntimeID aRID = aParamInstance->hasCreatorContainerRID() ?
				aParamInstance->getCreatorContainerRID() : ctxRID;

		const BF & foundVariable = aRID.getExecutable()->getymbolByAstElement(
				aParamInstance->getAstElement(), TYPE_UNIVERSAL_SPECIFIER);

		if( foundVariable.valid() )
		{
			return( foundVariable );
		}
		else
		{
			const BF & foundVariable = searchVariable(
					anED, ctxRID, aParamInstance->getAstElement() );

			if( foundVariable.valid() )
			{
				return( foundVariable );
			}
			else
			{
				const BF & foundVariable = searchVariable(anED, ctxRID,
						aParamInstance->getAstFullyQualifiedNameID() );

				if( foundVariable.valid() )
				{
					return( foundVariable );
				}
			}
		}
	}

	return( searchVariable(anED, ctxRID, aSymbolicParameter.str()) );
}


/**
 * SEARCH
 * Symbol
 * !UNUSED!
 *
BF RuntimeQuery::searchSymbol(TableOfSymbol & aliasTable,
		const ExecutionData & anED, UniFormIdentifier * anUFI)
{
	std::ostringstream osUFI;

	std::string aFullyQualifiedNameID = anUFI->str();

	{
		const BF & foundInstance =
				aliasTable.getByFQNameID( aFullyQualifiedNameID );
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}


	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::
		reverse_iterator it = anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::
		reverse_iterator itEnd = anED.getLocalRuntimes()->rend();
		for(  ; it != itEnd ; ++it )
		{
			const BF & anInstance = (*it).getProgram()->getAllData().
					getByFQNameID( aFullyQualifiedNameID );
			if( anInstance.valid() )
			{
				return( anInstance );
			}
		}
	}


	UniFormIdentifier::iterator it = anUFI->begin();
	UniFormIdentifier::iterator itEnd = anUFI->end();

	// recherche de la machine PRINCIPALE (ROOT)
	osUFI << "inst::" << (*it).str();

	const RuntimeID & theSystemRID = anED.getSystemRID();
	RuntimeID theMachineID = theSystemRID;

	for( ++it ; (it != itEnd) ; ++it )
	{
		if( theMachineID.getInstance()->fqnEquals( osUFI.str() ) )
		{
			break;
		}
		osUFI << "." << (*it).str();
	}

	if( it != itEnd )
	{
		VectorOfInstanceOfMachine aliasPath;

		RuntimeID aRID = theMachineID;

		// comme c'est la spec RID
//		aliasPath.append( theMachineID.getInstance() );

		// recherche de la machine FEUILLE
		for( ; it != itEnd ; ++it)
		{
			osUFI << "." << (*it).str();
			aRID = anED.getRuntime(aRID).getChild( osUFI.str() );
			if( aRID.valid() )
			{
				theMachineID = aRID;
				aliasPath.append( theMachineID.getInstance() );
			}
			else
			{
				break;
			}
		}

		if( (it == itEnd) && (theMachineID == theSystemRID) )
		{
			--it;
		}

		if( it != itEnd )
		{
			ExecutableForm * anExecutable = theMachineID.getExecutable();
			osUFI.str( "inst::" );
			osUFI << anExecutable->getFullyQualifiedNameID().substr( 6 );
			// 6 == "exec::".size()

			for( ; it != itEnd ; ++it)
			{
				osUFI << "." << (*it).str();
			}


			// The ORIGINAL INSTANCE
			BF anInstance = anExecutable->getAllData().
					getByFQNameID( osUFI.str() );

			if( anInstance.invalid() )
			{
				anInstance = anExecutable->getConstData().
						getByFQNameID( osUFI.str() );
			}
			if( anInstance.invalid() )
			{
				anInstance = anExecutable->getPort().
						getByFQNameID( osUFI.str() );
			}
			if( anInstance.invalid() )
			{
				anInstance = anExecutable->getBuffer().
						getByFQNameID( osUFI.str() );
			}
			if( anInstance.invalid() )
			{
				anInstance = anExecutable->getConnect().
						getByFQNameID( osUFI.str() );
			}

			if( anInstance.valid() )
			{

//				AVM_OS_TRACE << TAB << "Searching " << anUFI->str() << std::endl
//						<< TAB << "Found " << std::endl;
//				anInstance.toStream(AVM_OS_TRACE << TAB);
//				AVM_OS_TRACE << std::flush;

				if( aliasPath.nonempty() )
				{
					BaseInstanceForm * newInstance = NULL;

					switch ( anInstance.classKind() )
					{
						case FORM_INSTANCE_DATA_KIND:
						{
							newInstance = new InstanceOfData(
									theSystemRID.getExecutable(),
									anInstance.to_ptr< InstanceOfData >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );
							aliasTable.save( newInstance );

							break;
						}

						case FORM_INSTANCE_MACHINE_KIND:
						{
							newInstance = new InstanceOfMachine(
									theSystemRID.getExecutable(),
									anInstance.to_ptr< InstanceOfMachine >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						case FORM_INSTANCE_PORT_KIND:
						{
							newInstance = new InstanceOfPort(
									theSystemRID.getExecutable(),
									anInstance.to_ptr< InstanceOfPort >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						case FORM_INSTANCE_BUFFER_KIND:
						{
							newInstance = new InstanceOfBuffer(
									theSystemRID.getExecutable(),
									anInstance.to_ptr< InstanceOfBuffer >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						case FORM_INSTANCE_CONNECTOR_KIND:
						{
							newInstance = new InstanceOfConnect(
									theSystemRID.getExecutable(),
									anInstance.to_ptr< InstanceOfConnect >(),
									aliasPath);
							newInstance->setCreatorContainerRID( theMachineID );
							newInstance->setRuntimeContainerRID( theMachineID );

							return( aliasTable.save( newInstance ) );
						}

						default :
						{
							return( BF::REF_NULL );
						}
					}
				}
			}

			return( anInstance );
		}

		else if( aliasPath.nonempty() )
		{
			return( BF(	sep::incrReferenceCount(aliasPath.last()) ) );
		}

		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Unfound leaf machine : << " << osUFI.str()
					<< " >> container of << " << aFullyQualifiedNameID << " >>"
					<< SEND_EXIT;
		}
	}

	return( BF::REF_NULL );
}

const BF & RuntimeQuery::searchSymbol(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const ObjectElement * astElement)
{
	{
		const BF & foundInstance = aliasTable.getByAstElement(astElement);
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::
		reverse_iterator it = anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::
		reverse_iterator itEnd = anED.getLocalRuntimes()->rend();
		for(  ; it != itEnd ; ++it )
		{
			const BF & anInstance =
					(*it).getProgram()->getAllData().getByAstElement(astElement);
			if( anInstance.valid() )
			{
				return( anInstance );
			}
		}
	}

	{
		ExecutableQuery XQuery( mConfiguration );

		const BF & foundInstance = XQuery.getInstanceByAstElement(astElement);

		return( foundInstance );
	}
}


const BF & RuntimeQuery::searchSymbol(TableOfSymbol & aliasTable,
		const ExecutionData & anED, const BF & aBaseInstance)
{
	if( aliasTable.contains(aBaseInstance) )
	{
		return( aBaseInstance );
	}

	if( anED.hasLocalRuntimeStack() )
	{
		StackOfLocalRuntime::
		reverse_iterator it = anED.getLocalRuntimes()->rbegin();
		StackOfLocalRuntime::
		reverse_iterator itEnd = anED.getLocalRuntimes()->rend();
		for( ; it != itEnd ; ++it )
		{
			if( (*it).getProgram()->containsData( aBaseInstance ) )
			{
				return( aBaseInstance );
			}
		}
	}

	const RuntimeID & theSystemRID = anED.getSystemRID();

	VectorOfInstanceOfMachine aliasPath;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != endRF ; ++itRF)
	{
		itRID = (*itRF)->getRID();

		switch ( aBaseInstance.classKind() )
		{
			case FORM_INSTANCE_DATA_KIND:
			{
				if( itRID.getExecutable()->containsData(
						aBaseInstance.to_ptr< InstanceOfData >()) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfData * newInstance = new InstanceOfData(
						theSystemRID.getExecutable(),
						aBaseInstance.to_ptr< InstanceOfData >(), aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}

				break;
			}

			case FORM_INSTANCE_MACHINE_KIND:
			{
				if( itRID.getExecutable()->
						getInstanceStatic().contains(aBaseInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfMachine * newInstance = new InstanceOfMachine(
							theSystemRID.getExecutable(),
							aBaseInstance.to_ptr< InstanceOfMachine >(),
							aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			case FORM_INSTANCE_PORT_KIND:
			{
				if( itRID.getExecutable()->getPort().contains(aBaseInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfPort * newInstance = new InstanceOfPort(
							theSystemRID.getExecutable(),
							aBaseInstance.to_ptr< InstanceOfPort >(), aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			case FORM_INSTANCE_BUFFER_KIND:
			{
				InstanceOfBuffer * bufferInstance =
						aBaseInstance.to_ptr< InstanceOfBuffer >();

				if( itRID.getExecutable()->getBuffer().contains(bufferInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfBuffer * newInstance = new InstanceOfBuffer(
							theSystemRID.getExecutable(),
							bufferInstance, aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			case FORM_INSTANCE_CONNECTOR_KIND:
			{
				InstanceOfConnect * connectInstance =
						aBaseInstance.to_ptr< InstanceOfConnect >();

				if( itRID.getExecutable()->getConnect().contains(connectInstance) )
				{
					aliasPath.append( itRID.getInstance() );

					InstanceOfConnect * newInstance = new InstanceOfConnect(
							theSystemRID.getExecutable(),
							connectInstance, aliasPath );
					newInstance->setCreatorContainerRID( itRID );
					newInstance->setRuntimeContainerRID( itRID );

					aliasTable.save( newInstance );
				}
				break;
			}

			default :
			{
				break;
			}
		}
	}

	return( aBaseInstance );
}
*
* !UNUSED!
*/



////////////////////////////////////////////////////////////////////////////////
// LIFELINE API
////////////////////////////////////////////////////////////////////////////////

void RuntimeQuery::getSystemLifelines(Vector< RuntimeID > & lifelines) const
{
	const RuntimeForm & systemRF =
			mConfiguration.getMainExecutionData().getSystemRuntime();

	if( systemRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = systemRF.beginChild();
		TableOfRuntimeID::const_iterator endRID = systemRF.endChild();
		for( ; itRID != endRID ; ++itRID)
		{
			lifelines.append( *itRID );
		}
	}
}


const RuntimeID & RuntimeQuery::getRuntineByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	TableOfRuntimeT::const_iterator itRF =
			mConfiguration.getMainExecutionData().getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF =
			mConfiguration.getMainExecutionData().getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF)
	{
		if( NamedElement::fqnEndsWith(
				(*itRF)->getFullyQualifiedNameID(),aQualifiedNameID) )
		{
			return( (*itRF)->getRID() );
		}
	}

	return( RuntimeID::REF_NULL );
}



} /* namespace sep */
