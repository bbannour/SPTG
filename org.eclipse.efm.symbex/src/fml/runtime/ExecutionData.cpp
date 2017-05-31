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

#include "ExecutionData.h"

#include <fml/executable/BaseInstanceForm.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeDef.h>

#include <boost/format.hpp>


namespace sep
{


/*ATTRIBUTES*/
avm_size_t ExecutionData::PARAM_MACHINE_RUNTIME_OFFSET = 0;
avm_size_t ExecutionData::SYSTEM_RUNTIME_OFFSET        = 1;



/**
 * GETTER
 * mTableOfRuntimeForm
 */

const RuntimeID & ExecutionData::getRuntimeID(
		const ExecutableForm * anExecutable) const
{
	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
	for( ; it != itEnd ; ++it )
	{
		if( (*it)->getRID().getExecutable() == anExecutable )
		{
			return( (*it)->getRID() );
		}
	}

	return( RuntimeID::REF_NULL );
}


const RuntimeID & ExecutionData::getRuntimeID(
		InstanceOfMachine * anInstance) const
{
	if( anInstance->hasRuntimeRID() )
	{
		return( anInstance->getRuntimeRID() );
	}
	else if( anInstance->isAlias() )
	{
		if( anInstance->hasAliasTarget() &&
				anInstance->getAliasTarget()->as< InstanceOfMachine >()->
						hasRuntimeRID() )
		{
			const RuntimeID & tmpRID =
					anInstance->getAliasTarget()->getRuntimeContainerRID();

			anInstance->setRuntimeRID( tmpRID );

			return( tmpRID );
		}

		ArrayOfInstanceOfMachine::iterator it =
				anInstance->getMachinePath()->begin();

		RuntimeID tmpRID = mRID;

		// SEARCH of the LCA(RID) of the current RID an the ALIAS container
		tmpRID = tmpRID.getAncestorContaining( *it );
		if( tmpRID.valid() )
		{
			ArrayOfInstanceOfMachine::iterator itEnd =
					anInstance->getMachinePath()->end();

			// Use of Alias PATH to find the INSTANCE of variable
			for( ; it != itEnd ; ++it )
			{
				tmpRID = getRuntime(tmpRID).getChild((*it)->getOffset());
			}

			AVM_OS_ASSERT_FATAL_ERROR_EXIT(
				tmpRID.getExecutable()->getBuffer().at( anInstance
				->getOffset() ).isAstElement( anInstance->getAstElement() ) )
					<< "Assign error " << tmpRID.getExecutable()->getBuffer().at(
							anInstance->getOffset()).getFullyQualifiedNameID()
					<< " != " << anInstance->getFullyQualifiedNameID()
					<< SEND_EXIT;

			return( getRuntime(tmpRID).getChild(anInstance->getOffset()) );
		}
	}

//	if( anInstance->getSpecifier().isDesignInstanceStatic() )
	{
		for( RuntimeID aRID = mRID ; aRID.valid() ; aRID = aRID.getPRID() )
		{
			if( anInstance->getContainer() == aRID.getExecutable() )
			{
				return( getRuntime(aRID).getChild(anInstance->getOffset()) );
			}
		}
	}
//	else if( anInstance->getSpecifier().isDesignModel() )
//	{
//		return( mTableOfRuntimeForm->getRID(anInstance->getExecutable()) );
//	}

	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
	for( ; it != itEnd ; ++it )
	{
		if( (*it)->getRID().getInstance() == anInstance )
		{
			return( (*it)->getRID() );
		}
	}

	return( RuntimeID::REF_NULL );
}


const RuntimeID & ExecutionData::getRuntimeID(
		const std::string & aFullyQualifiedNameID) const
{
	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
	for( ; it != itEnd ; ++it )
	{
		if( NamedElement::compareLocation(
				(*it)->getFullyQualifiedNameID(), aFullyQualifiedNameID) )
		{
			return( (*it)->getRID() );
		}
	}

	return( RuntimeID::REF_NULL );
}

const RuntimeID & ExecutionData::getRuntimeIDByNameID(
		const std::string & aNameID) const
{
	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
	for( ; it != itEnd ; ++it )
	{
		if( (*it)->getNameID() == aNameID )
		{
			return( (*it)->getRID() );
		}
	}

	return( RuntimeID::REF_NULL );
}


RuntimeID ExecutionData::getRuntimeContainerRID(
		const RuntimeID & aRID, BaseInstanceForm * anInstance) const
{
	if( anInstance->hasRuntimeContainerRID() )
	{
		return( anInstance->getRuntimeContainerRID() );
	}
	else if( anInstance->isAlias() )
	{
		RuntimeID tmpRID = aRID;

		if( anInstance->hasAliasTarget() &&
				anInstance->getAliasTarget()->hasRuntimeContainerRID() )
		{
			anInstance->setRuntimeContainerRID( tmpRID =
					anInstance->getAliasTarget()->getRuntimeContainerRID() );

			return( tmpRID );
		}

		ArrayOfInstanceOfMachine::iterator it =
				anInstance->getMachinePath()->begin();

		// SEARCH of the LCA(RID) of the current RID an the ALIAS container
		tmpRID = tmpRID.getAncestorContaining( *it );
		if( tmpRID.valid() )
		{
			ArrayOfInstanceOfMachine::iterator itEnd =
					anInstance->getMachinePath()->end();

			// Use of Alias PATH to find the INSTANCE of variable
			for( ; it != itEnd ; ++it )
			{
				tmpRID = getRuntimeFormChild(tmpRID, (*it));
			}

			AVM_OS_ASSERT_FATAL_ERROR_EXIT(
				tmpRID.getExecutable()->getBuffer().at( anInstance
				->getOffset() ).isAstElement( anInstance->getAstElement() ) )
					<< "Assign error " << tmpRID.getExecutable()->getBuffer().
						at(anInstance->getOffset()).getFullyQualifiedNameID()
					<< " != " << anInstance->getFullyQualifiedNameID()
					<< SEND_EXIT;

			return( tmpRID );
		}
	}
	else
	{
		// SEARCH of the RUNTIME FORM container
		// where this INSTANCE of variable was declared
		return( aRID.getAncestorContaining( anInstance ) );
	}

	return( RuntimeID::REF_NULL );
}


/**
 * GETTER
 * for data in RuntimeForm DataTable
 */
//const BF & ExecutionData::getData(const std::string & aFullyQualifiedNameID) const
//{
//	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
//	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
//	for( ; it != itEnd ; ++it )
//	{
//		const BF & foundData = (*it)->getData(aFullyQualifiedNameID);
//		if( foundData.valid() )
//		{
//			return( foundData );
//		}
//	}
//
//	return( BF::REF_NULL );
//}

const BF & ExecutionData::getDataByQualifiedNameID(
		const std::string & aQualifiedNameID, InstanceOfData * & var) const
{
	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
	for( ; it != itEnd ; ++it )
	{
		const BF & foundData =
				 (*it)->getDataByQualifiedNameID(aQualifiedNameID, var);
		if( foundData.valid() )
		{
			return( foundData );
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutionData::getDataByNameID(const std::string & aNameID) const
{
	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
	for( ; it != itEnd ; ++it )
	{
		const BF & foundData = (*it)->getDataByNameID(aNameID);
		if( foundData.valid() )
		{
			return( foundData );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER
 * mSaveTableOfAssignedFlag
 */
TableOfRuntimeFormState::TableOfAssignedFlag
ExecutionData::getSaveTableOfAssignedFlag() const
{
	return( mExecutionContext->getTableOfAssignedFlag() );
}



/**
 * GETTER
 * tableOfRuntimeFormState
 */
bool ExecutionData::checkRunningForm(const BF & aRunnableElementTrace,
		const RuntimeID & aRID)
{
	if( aRunnableElementTrace.is< ExecutionConfiguration >() )
	{
		ExecutionConfiguration * anExecConf =
				aRunnableElementTrace.to_ptr< ExecutionConfiguration >();

		return( anExecConf->getRuntimeID() == aRID );
	}

	else if( aRunnableElementTrace.is< AvmCode >() )
	{
		AvmCode * aCode = aRunnableElementTrace.to_ptr< AvmCode >();

		for( AvmCode::iterator it = aCode->begin() ; it != aCode->end() ; ++it )
		{
			if( checkRunningForm(*it, aRID) )
			{
				return( true );
			}
		}
	}

	return( false);
}


/**
 * INSTANCIATION BOUND TEST
 */
bool ExecutionData::couldBeInstanciated(InstanceOfMachine * anInstance) const
{
	ExecutableForm * anExecutable = anInstance->getExecutable();

	if( anExecutable->hasMaximalInstance() )
	{
		avm_size_t anInstanciationCount = 0;

		TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator endIt = mTableOfRuntime.end();
		for( ; it != endIt ; ++it )
		{
			if( (*it)->getExecutable() == anExecutable )
			{
				++anInstanciationCount;
			}
		}

//!![TRACE]: to delete
//AVM_OS_DEBUG << "Instanciation Count: " << anInstanciationCount
//		<< " ?<=? max: " << anExecutable->getMaximalInstanceCount() << std::endl;

		return( anInstanciationCount <= anExecutable->getMaximalInstanceCount() );
	}

	return( true );
}




/**
 * string of a state configuration of an ExecutionData
 */
void ExecutionData::toStreamStateIdleOrRunning(
		OutStream & os, const RuntimeForm & aRF) const
{
	if( aRF.hasOnSchedule()
		&& aRF.getOnSchedule()->singleton()
		&& aRF.getOnSchedule()->first().is< RuntimeID >()
		/*&& (aRF.getRID() != aRF.getOnSchedule()->first().bfRID())*/ )
	{
		if( aRF.getExecutable()->hasTransition() )
		{
			os << aRF.getRID().strUniqId() << " ( ";
		}

		if( isIdleOrRunning(aRF.getOnSchedule()->first().bfRID()) )
		{
			toStreamStateIdleOrRunning(os,
					getRuntime(aRF.getOnSchedule()->first().bfRID()) );

			if( aRF.getExecutable()->hasTransition() )
			{
				os << " )";
			}
		}
	}

	else if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		if( aRF.getExecutable()->hasTransition() )
		{
			os << aRF.getRID().strUniqId() << " ";
		}

		bool needComa = false;
		for( ; itRID != itRIDEnd ; ++itRID )
		{
			if( isIdleOrRunning( *itRID ) )
			{
				if( needComa )
				{
					os << " , ";
				}
				else
				{
					os << "( ";
					needComa = true;
				}
				toStreamStateIdleOrRunning(os, getRuntime(*itRID));
			}
		}
		if( needComa )
		{
			os << " )";
		}
	}
	else
	{
		os << aRF.getRID().strUniqId();
	}
}


/**
 * string of a state configuration of an ExecutionData
 *
 * LIFELINE STATE IDENTIFIER
 * %1% --> lifeline runtime pid
 * %2% --> lifeline identifier
 * %3% --> state runtime pid
 * %4% --> state identifier
 */
OutStream & ExecutionData::toStreamLifelineStateFormat(
		OutStream & os, const RuntimeForm & aRF,
		const std::string & formatLifelineStatePattern) const
{
	boost::format formatter(formatLifelineStatePattern);
	formatter.exceptions( boost::io::no_error_bits );

	RuntimeID ridLifeline = aRF.getRID().getLifeline();

	os << formatter
			% ridLifeline.strPid()
			% ridLifeline.getInstance()->getNameID()
			% aRF.getRID().strPid()
			% aRF.getRID().getNameID();

	return( os );
}


void ExecutionData::toStreamStateConf(
		OutStream & os, const RuntimeForm & aRF,
		const std::string & formatLifelineStatePattern) const
{
	if ( aRF.hasOnSchedule() )
	{
		if( aRF.getOnSchedule()->singleton()
			&& aRF.getOnSchedule()->first().is< RuntimeID >()
			&& (aRF.getRID() != aRF.getOnSchedule()->first().bfRID()) )
		{
			if( aRF.getExecutable()->hasTransition() )
			{
				toStreamLifelineStateFormat(os, aRF, formatLifelineStatePattern)
						<< " ( ";
			}

			toStreamStateConf(os,
					getRuntime( aRF.getOnSchedule()->first().bfRID() ),
					formatLifelineStatePattern );

			if( aRF.getExecutable()->hasTransition() )
			{
				os << " )";
			}

			return;
		}
	}

	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		if( aRF.getExecutable()->hasTransition() )
		{
			toStreamLifelineStateFormat(os, aRF, formatLifelineStatePattern)
					<< " ";
		}

		os << "( ";
		for( bool needComa = false ; itRID != itRIDEnd ; ++itRID )
		{
			if( (*itRID).getExecutable()->hasOnInitOrEnableOrRun() )
			{
				if( isRunnable( *itRID ) || isFinalizedOrDestroyed( *itRID ) )
				{
					if( needComa )
					{
						os << " , ";
					}
					else
					{
						needComa = true;
					}
					toStreamStateConf(os, getRuntime(*itRID),
							formatLifelineStatePattern );
				}
			}
		}
		os << " )";
	}
	else
	{
		if( isFinalized( aRF.getRID() ) )
		{
			os << "<final>";
		}
		else if( isDestroyed( aRF.getRID() ) )
		{
			os << "<destroy>";
		}

		toStreamLifelineStateFormat(os, aRF, formatLifelineStatePattern);
	}
}


/**
 * string of a state configuration of an ExecutionData to Fscn
 */
void ExecutionData::toStreamStateConfToFscn(
		OutStream & os, const RuntimeForm & aRF) const
{
	if ( aRF.hasOnSchedule() )
	{
		if( aRF.getOnSchedule()->singleton()
			&& aRF.getOnSchedule()->first().is< RuntimeID >()
			&& getRuntime(aRF.getOnSchedule()->first().bfRID()).isInstanciated() )
		{
			toStreamStateConfToFscn(os,
					getRuntime( aRF.getOnSchedule()->first().bfRID() ) );

			return;
		}
	}

	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		os << "( " ;
		for( bool needComa = false ; itRID != itRIDEnd ; ++itRID )
		{
			if( (*itRID).getExecutable()->hasOnInitOrEnableOrRun()
				&& getRuntime(*itRID).isInstanciated() )
			{
				if( needComa )
				{
					os << " , ";
				}
				else
				{
					needComa = true;
				}
				toStreamStateConfToFscn(os, getRuntime((*itRID)) );
			}
		}
		os << " )";
	}
	else
	{
		os << aRF.getRID().strUniqId();
	}
}


/**
 * Serialization
 */
void ExecutionData::toStream(OutStream & os) const
{
	os << TAB << "ed";

	const std::string conf = strStateConf();
	if( conf[0] == '(' )
	{
		os << conf;
	}
	else
	{
		os << '(' << conf << ')';
	}

	AVM_DEBUG_REF_COUNTER(os);
	os << " {" << EOL_FLUSH;

//	os << TAB2 << "name = \"" << strStateConf() << "\";" << EOL_FLUSH;

	if ( hasRunnableElementTrace() )
	{
		os << TAB2 << "fired = " << getRunnableElementTrace().str()
				<< ";" << EOL_FLUSH;
	}

	if ( hasIOElementTrace() )
	{
		os << TAB2 << "trace = " << getIOElementTrace().str() << ";" << EOL_FLUSH;
	}

	os << TAB2 << "exec_status = "
			<< RuntimeDef::strAEES( getAEES() ) << ";" << EOL_FLUSH;

	if ( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		os << TAB2 << "firedcondition = "
				<< getNodeCondition().wrapStr( os.INDENT.tab2Size(18) )
				<< ";" << EOL;
	}

	if ( hasNodeTimedCondition() &&
		getNodeTimedCondition().isNotEqualTrue() )
	{
		os << TAB2 << "firedtimedcondition = "
				<< getNodeTimedCondition().wrapStr( os.INDENT.tab2Size(23) )
				<< ";" << EOL;
	}

	if( hasPathCondition() && getPathCondition().isNotEqualTrue() )
	{
		os << TAB2 << "pathcondition = "
				<< getPathCondition().wrapStr( os.INDENT.tab2Size(17) )
				<< ";";
		getPathCondition().AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}
	else if( not hasPathCondition() )
	{
		os << TAB2 << "pathcondition = NULL;" << EOL;
	}

	if( hasPathTimedCondition() && getPathTimedCondition().isNotEqualTrue() )
	{
		os << TAB2 << "pathtimedcondition = "
				<< getPathTimedCondition().wrapStr( os.INDENT.tab2Size(22) )
				<< ";";
		getPathTimedCondition().AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}
	else if( not hasPathTimedCondition() )
	{
		os << TAB2 << "pathtimedcondition = NULL;" << EOL;
	}

	os << TAB2 << "@init{" << INCR2_INDENT;
	getOnInit()->toStreamRoutine( os );
	os << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;

	os << TAB2 << "@schedule{" << INCR2_INDENT;
	getOnSchedule()->toStreamRoutine( os );
	os << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;

	os << TAB2 << "rid = " << getRID().str() << ";" << EOL_FLUSH;


//	if( hasParam() )
//	{
//		os << EOL;
//		os << TAB << "parameter:";
//		tableOfParam->AVM_DEBUG_REF_COUNTER(os);
//		os << EOL;
//
//		tableOfParam->toStream(os);
//	}


//AVM_IF_DEBUG_ENABLED_AND( hasTableOfRID() )
//	os << EOL;
//
//	AVM_IF_DEBUG_LEVEL_GT_MEDIUM
//		os << TAB << "rid:" << EOL_INCR_INDENT;
//		TableOfRuntimeID::const_iterator it = mTableOfRID->begin();
//		TableOfRuntimeID::const_iterator itEnd = mTableOfRID->end();
//		for( ; it != itEnd ; ++it )
//		{
//			(*it).toStream(os);
//		}
//		os << DECR_INDENT;
//	AVM_ELSEIF_DEBUG_LEVEL_GT_LOW
//		os << TAB2 << "rid = [| ";
//		TableOfRuntimeID::const_iterator it = mTableOfRID->begin();
//		TableOfRuntimeID::const_iterator itEnd = mTableOfRID->end();
//		for( ; it != itEnd ; ++it )
//		{
//			os << (*it).getOffset() << " ";
//		}
//		os << "|];" << EOL_FLUSH;
//	AVM_ENDIF_DEBUG_LEVEL_GT_LOW
//AVM_ENDIF_DEBUG_ENABLED_AND


	if( hasLocalRuntimeStack() )
	{
		os << EOL_TAB << "local: ";
		getLocalRuntimes()->AVM_DEBUG_REF_COUNTER(os);

		os << EOL_INCR_INDENT;
		getLocalRuntimes()->toStream(os);
		os << DECR_INDENT;
	}

	if ( getTableOfRuntime().nonempty() )
	{
		os << EOL_TAB << "runtime#state:" << EOL_INCR_INDENT;
		mTableOfRFStateFlags->toStream(*this, os);

		os << EOL_DECR_INDENT << TAB << "runtime:" << EOL_INCR_INDENT;

AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
		TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
		for( ; it != itEnd ; ++it )
		{
			(*it)->toStream(this, os);
		}
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

		os << DECR_INDENT;
	}

	if( mSTATEMENT_QUEUE.nonempty() )
	{
		os << EOL_INCR_INDENT;
		mSTATEMENT_QUEUE.toStream(os);
		os << DECR_INDENT;
	}

	if( mEXEC_SYNC_POINT != NULL )
	{
		os << EOL_INCR_INDENT;
		mEXEC_SYNC_POINT->toStream(os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}

void ExecutionData::toStreamData(OutStream & os) const
{

	os << TAB << "ed<data>";
	AVM_DEBUG_REF_COUNTER(os);
	os << " {" << EOL;

	os << TAB2 << "name = \"" << strStateConf() << "\";" << EOL_FLUSH;


	if ( hasRunnableElementTrace() )
	{
		os << TAB2 << "fired = " << getRunnableElementTrace().str()
					<< ";" << EOL_FLUSH;
	}

	if ( hasIOElementTrace() )
	{
		os << TAB2 << "trace = " << getIOElementTrace().str() << ";" << EOL_FLUSH;
	}

	os << TAB2 << "exec_status = "
			<< RuntimeDef::strAEES( getAEES() ) << ";" << EOL_FLUSH;

	if ( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		os << TAB2 << "nodecondition = "
				<< getNodeCondition().wrapStr( os.INDENT.tab2Size(18) )
				<< ";" << EOL_FLUSH;
	}

	if ( hasPathCondition() && getPathCondition().isNotEqualTrue() )
	{
		os << TAB2 << "pathcondition = "
				<< getPathCondition().wrapStr( os.INDENT.tab2Size(17) )
				<< ";" << EOL_FLUSH;
	}

	if( hasOnInit() )
	{
		os << TAB2 << "@init{" << INCR2_INDENT;
		getOnInit()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;
	}

	if( hasOnSchedule() )
	{
		os << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;
	}

//	if( hasParam() )
//	{
//		os << EOL;
//		os << TAB << "parameter:" << EOL;
//		tableOfParam->toStream(os, TAB2, CHAR, EOL);
//	}

	if ( getTableOfRuntime().nonempty() )
	{
		os << EOL_TAB << "runtime:" << EOL_INCR_INDENT;

		TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it)->hasDataTable() )
			{
				(*it)->toStreamData(this, os);
			}
		}

		os << DECR_INDENT;
	}

	if( mSTATEMENT_QUEUE.nonempty() )
	{
		os << EOL_INCR_INDENT;
		mSTATEMENT_QUEUE.toStream(os);
		os << DECR_INDENT;
	}

	if( mEXEC_SYNC_POINT != NULL )
	{
		os << EOL_INCR_INDENT;
		mEXEC_SYNC_POINT->toStream(os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}

void ExecutionData::toFscn(OutStream & os,
		const ExecutionData * aPreviousExecData) const
{
//	os << TAB << "SC: " << strStateConfToFscn() << EOL;

	if( (aPreviousExecData == NULL)
		|| (aPreviousExecData->getPathCondition()
			!= getPathCondition()) )
	{
		os << TAB << "PC: "
				<< getPathCondition().wrapStr( os.INDENT.tab2Size(4) )
				<< EOL;
	}

	if( (aPreviousExecData == NULL)
		|| (aPreviousExecData->getPathTimedCondition()
			!= getPathTimedCondition()) )
	{
		os << TAB << "PtC: "
				<< getPathTimedCondition().wrapStr( os.INDENT.tab2Size(5) )
				<< EOL;
	}

	// DATA
	StringOutStream oss( os.INDENT );
	oss << INCR_INDENT;

	TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();

	if( aPreviousExecData != NULL )
	{
		TableOfRuntimeT::const_iterator itPrev =
				aPreviousExecData->mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itPrevEnd =
				aPreviousExecData->mTableOfRuntime.end();
		TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
		for( ; (it != itEnd) && (itPrev != itPrevEnd) ; ++it , ++itPrev )
		{
			if( (*it)->hasDataTable() && (*it)->isNTEQ(*itPrev) )
			{
				(*it)->toFscnData(oss, this, *itPrev);
			}
		}

		for( ; (it != itEnd) ; ++it)
		{
			if( (*it)->hasDataTable() )
			{
				(*it)->toFscnData(oss, this, NULL);
			}
		}
	}
	else
	{
		TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it)->hasDataTable() )
			{
				(*it)->toFscnData(oss, this, NULL);
			}
		}
	}

	if( not oss.str().empty() )
	{
		os << TAB << "DATA{" << EOL;
		os << oss.str();
		os << TAB << "}" << EOL;
	}
	// END DATA

	// BUFFER
	StringOutStream osb( os.INDENT );
	osb << INCR_INDENT;

	it = getTableOfRuntime().begin();
	itEnd = getTableOfRuntime().end();

	if( aPreviousExecData != NULL )
	{
		TableOfRuntimeT::const_iterator itPrev =
				aPreviousExecData->getTableOfRuntime().begin();
		TableOfRuntimeT::const_iterator itPrevEnd =
				aPreviousExecData->getTableOfRuntime().end();
		for( ; (it != itEnd) && (itPrev != itPrevEnd) ; ++it , ++itPrev )
		{
			if( (*it)->hasBufferTable() && (*it)->isNTEQ(*itPrev) )
			{
				(*it)->toFscnBuffer(osb, this, (*itPrev));
			}
		}

		for( ; (it != itEnd) ; ++it)
		{
			if( (*it)->hasBufferTable() )
			{
				(*it)->toFscnBuffer(osb, this, NULL);
			}
		}
	}
	else
	{
		TableOfRuntimeT::const_iterator it = mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itEnd = mTableOfRuntime.end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it)->hasBufferTable() )
			{
				(*it)->toFscnBuffer(osb, this, NULL);
			}
		}
	}

	if( not osb.str().empty() )
	{
		os << TAB << "BUFFER{" << EOL;
		os << osb.str();
		os << TAB << "}" << EOL;
	}
	// END BUFFER


	if( mSTATEMENT_QUEUE.nonempty() )
	{
		os << TAB << "/*" << EOL;
		mSTATEMENT_QUEUE.toStream(os);
		os << TAB << "*/" << EOL;
	}

	if( mEXEC_SYNC_POINT != NULL )
	{
		os << TAB << "/*" << EOL;
		mEXEC_SYNC_POINT->toStream(os);
		os << TAB << "*/" << EOL;
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * DEFAULT NULL
 */
APExecutionData APExecutionData::REF_NULL;



/**
 * GETTER - SETTER
 * the Previous ExecutionData
 */

APExecutionData & APExecutionData::getPrevious()
{
	return( raw_pointer()->getExecutionContext()->getPreviousExecutionData() );
}

const APExecutionData & APExecutionData::getPrevious() const
{
	return( raw_pointer()->getExecutionContext()->getPreviousExecutionData() );
}

bool APExecutionData::hasPrevious() const
{
	return( raw_pointer()->hasExecutionContext() &&
			raw_pointer()->getExecutionContext()->hasPrevious() );
}



}
