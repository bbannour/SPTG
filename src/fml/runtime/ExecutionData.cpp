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
std::size_t ExecutionData::PARAM_MACHINE_RUNTIME_OFFSET = 0;
std::size_t ExecutionData::SYSTEM_RUNTIME_OFFSET        = 1;

/**
 * GETTER - SETTER
 * mExecutionContext
 * Previous ExecutionData
 */
ExecutionData & ExecutionData::getPrevious()
{
	return( mSmartPtr->mExecutionContext->getwExecutionData() );
}

const ExecutionData & ExecutionData::getPrevious() const
{
	return( mSmartPtr->mExecutionContext->getExecutionData() );
}


/**
 * GETTER
 * mTableOfRuntimeForm
 */
const RuntimeID & ExecutionData::getRuntimeID(
		const ExecutableForm & anExecutable) const
{
	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		if( itRF->getRID().getExecutable() == (& anExecutable) )
		{
			return( itRF->getRID() );
		}
	}

	return( RuntimeID::nullref() );
}


const RuntimeID & ExecutionData::getRuntimeID(
		const InstanceOfMachine & anInstance) const
{
	if( anInstance.hasRuntimeRID() )
	{
		return( anInstance.getRuntimeRID() );
	}
	else if( anInstance.isAlias() )
	{
		if( anInstance.hasAliasTarget() &&
				anInstance.getAliasTarget()->as_ptr< InstanceOfMachine >()->
						hasRuntimeRID() )
		{
			const RuntimeID & tmpRID =
					anInstance.getAliasTarget()->getRuntimeContainerRID();

			const_cast< InstanceOfMachine & >(anInstance).setRuntimeRID( tmpRID );

			return( tmpRID );
		}

		ArrayOfInstanceOfMachine::iterator it =
				anInstance.getMachinePath()->begin();

		RuntimeID tmpRID = mSmartPtr->mRID;

		// SEARCH of the LCA(RID) of the current RID an the ALIAS container
		tmpRID = tmpRID.getAncestorContaining( *( *it ) );
		if( tmpRID.valid() )
		{
			ArrayOfInstanceOfMachine::iterator itEnd =
					anInstance.getMachinePath()->end();

			// Use of Alias PATH to find the INSTANCE of variable
			for( ; it != itEnd ; ++it )
			{
				tmpRID = getRuntime(tmpRID).getChild((*it)->getOffset());
			}

			AVM_OS_ASSERT_FATAL_ERROR_EXIT(
				tmpRID.refExecutable().getBuffer().at(
						anInstance.getOffset() ).isAstElement(
								anInstance.getAstElement() ) )
					<< "Assign error " << tmpRID.refExecutable().getBuffer().at(
							anInstance.getOffset()).getFullyQualifiedNameID()
					<< " != " << anInstance.getFullyQualifiedNameID()
					<< SEND_EXIT;

			return( getRuntime(tmpRID).getChild(anInstance.getOffset()) );
		}
	}

//	if( anInstance.getSpecifier().isDesignInstanceStatic() )
	{
		RuntimeID aRID = mSmartPtr->mRID;
		for( ; aRID.valid() ; aRID = aRID.getPRID() )
		{
			if( anInstance.getContainer() == aRID.getExecutable() )
			{
				return( getRuntime(aRID).getChild(anInstance.getOffset()) );
			}
		}
	}
//	else if( anInstance.getSpecifier().isDesignModel() )
//	{
//		return( mTableOfRuntimeForm->getRID(anInstance.getExecutable()) );
//	}

	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		if( itRF->getRID().getInstance() == (& anInstance) )
		{
			return( itRF->getRID() );
		}
	}

	return( RuntimeID::nullref() );
}


const RuntimeID & ExecutionData::getRuntimeID(
		const std::string & aFullyQualifiedNameID) const
{
	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		if( itRF->isLocationID(aFullyQualifiedNameID) )
		{
			return( itRF->getRID() );
		}
	}

	return( RuntimeID::nullref() );
}

const RuntimeID & ExecutionData::getRuntimeIDByNameID(
		const std::string & aNameID) const
{
	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		if( itRF->getNameID() == aNameID )
		{
			return( itRF->getRID() );
		}
	}

	return( RuntimeID::nullref() );
}

const RuntimeID & ExecutionData::getRuntimeIDByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		if( itRF->fqnEndsWith(aQualifiedNameID) )
		{
			return( itRF->getRID() );
		}
	}

	return( RuntimeID::nullref() );
}


RuntimeID ExecutionData::getRuntimeContainerRID(
		const RuntimeID & aRID, const BaseInstanceForm * anInstance) const
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
			tmpRID = anInstance->getAliasTarget()->getRuntimeContainerRID();

			const_cast< BaseInstanceForm * >(
					anInstance )->setRuntimeContainerRID( tmpRID );

			return( tmpRID );
		}

		ArrayOfInstanceOfMachine::iterator it =
				anInstance->getMachinePath()->begin();

		// SEARCH of the LCA(RID) of the current RID an the ALIAS container
		tmpRID = tmpRID.getAncestorContaining( *( *it ) );
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
				tmpRID.refExecutable().getBuffer().at( anInstance
				->getOffset() ).isAstElement( anInstance->getAstElement() ) )
					<< "Assign error " << tmpRID.refExecutable().getBuffer().
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
		return( aRID.getAncestorContaining( * anInstance ) );
	}

	return( RuntimeID::nullref() );
}


/**
 * GETTER
 * Timestamp
 */
const BF & ExecutionData::getTimeValue(const RuntimeID & aRID) const
{
	RuntimeID timedRID = aRID;
	while( timedRID.valid() && timedRID.getSpecifier().noFeatureTimed() )
	{
		timedRID = timedRID.getPRID();
	}

	if( timedRID.valid() )
	{
		return( getRuntime(timedRID).getTimeValue() );
	}
	else
	{
		return( BF::REF_NULL );
	}
}

const BF & ExecutionData::getDeltaTimeValue(const RuntimeID & aRID) const
{
	RuntimeID timedRID = aRID;
	while( timedRID.valid() && timedRID.getSpecifier().noFeatureTimed() )
	{
		timedRID = timedRID.getPRID();
	}

	if( timedRID.valid() )
	{
		return( getRuntime(timedRID).getDeltaTimeValue() );
	}
	else
	{
		return( BF::REF_NULL );
	}
}


/**
 * SYNC-SETTER
 * Synchronization of Time Values
 */
void ExecutionData::syncTimeValues(
		const RuntimeID & aRID, const ExecutionData & refED)
{
	RuntimeID timedRID = aRID;
	while( timedRID.valid() && timedRID.getSpecifier().noFeatureTimed() )
	{
		timedRID = timedRID.getPRID();
	}

	if( timedRID.valid() )
	{
		getWritableRuntime(timedRID).syncTimeValues(refED);
	}
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
	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		const BF & foundData =
				itRF->getDataByQualifiedNameID(aQualifiedNameID, var);
		if( foundData.valid() )
		{
			return( foundData );
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutionData::getDataByNameID(const std::string & aNameID) const
{
	for( const auto & itRF : mSmartPtr->mTableOfRuntime )
	{
		const BF & foundData = itRF->getDataByNameID(aNameID);
		if( foundData.valid() )
		{
			return( foundData );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER
 * tableOfRuntimeFormState
 */
bool ExecutionData::checkRunningForm(
		const BF & aRunnableElementTrace, const RuntimeID & aRID) const
{
	if( aRunnableElementTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & anExecConf =
				aRunnableElementTrace.to< ExecutionConfiguration >();

		return( anExecConf.getRuntimeID() == aRID );
	}

	else if( aRunnableElementTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = aRunnableElementTrace.to< AvmCode >();
		for( const auto & itArg : aCode.getOperands() )
		{
			if( checkRunningForm(itArg, aRID) )
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
		std::size_t anInstanciationCount = 0;

		for( const auto & itRF : mSmartPtr->mTableOfRuntime )
		{
			if( itRF->getExecutable() == anExecutable )
			{
				++anInstanciationCount;
			}
		}

		return( anInstanciationCount <= anExecutable->getMaximalInstanceCount() );
	}

	return( true );
}




/**
 * string of a state configuration of an ExecutionData
 */
void ExecutionData::toStreamStateIdleOrRunning(
		OutStream & out, const RuntimeForm & aRF) const
{
	if( aRF.hasOnSchedule()
		&& aRF.getOnSchedule()->hasOneOperand()
		&& aRF.getOnSchedule()->first().is< RuntimeID >()
		/*&& (aRF.getRID() != aRF.getOnSchedule()->first().bfRID())*/ )
	{
		if( aRF.refExecutable().hasTransition() )
		{
			out << aRF.getRID().strUniqId() << " ( ";
		}

		if( isIdleOrRunning(aRF.getOnSchedule()->first().bfRID()) )
		{
			toStreamStateIdleOrRunning(out,
					getRuntime(aRF.getOnSchedule()->first().bfRID()) );

			if( aRF.refExecutable().hasTransition() )
			{
				out << " )";
			}
		}
	}

	else if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		if( aRF.refExecutable().hasTransition() )
		{
			out << aRF.getRID().strUniqId() << " ";
		}

		bool needComa = false;
		for( ; itRID != itRIDEnd ; ++itRID )
		{
			if( isIdleOrRunning( *itRID ) )
			{
				if( needComa )
				{
					out << " , ";
				}
				else
				{
					out << "( ";
					needComa = true;
				}
				toStreamStateIdleOrRunning(out, getRuntime(*itRID));
			}
		}
		if( needComa )
		{
			out << " )";
		}
	}
	else
	{
		out << aRF.getRID().strUniqId();
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
		OutStream & out, const RuntimeForm & aRF,
		const std::string & formatLifelineStatePattern) const
{
	boost::format formatter(formatLifelineStatePattern);
	formatter.exceptions( boost::io::no_error_bits );

	RuntimeID ridLifeline = aRF.getRID().getLifeline();

	if( ridLifeline.valid() )
	{
		out << formatter
				% ridLifeline.strPid()
				% ridLifeline.getInstance()->getNameID()
				% aRF.getRID().strPid()
				% aRF.getRID().getNameID();
	}
	else
	{
		out << formatter
				% ""
				% ""
				% aRF.getRID().strPid()
				% aRF.getRID().getNameID();

	}

	return( out );
}


void ExecutionData::toStreamStateConf(
		OutStream & out, const RuntimeForm & aRF,
		const std::string & formatLifelineStatePattern) const
{
	if ( aRF.hasOnSchedule() )
	{
		if( aRF.getOnSchedule()->hasOneOperand()
			&& aRF.getOnSchedule()->first().is< RuntimeID >()
			&& (aRF.getRID() != aRF.getOnSchedule()->first().bfRID()) )
		{
			if( aRF.refExecutable().hasTransition() )
			{
				toStreamLifelineStateFormat(out, aRF, formatLifelineStatePattern)
						<< " ( ";
			}

			toStreamStateConf(out,
					getRuntime( aRF.getOnSchedule()->first().bfRID() ),
					formatLifelineStatePattern );

			if( aRF.refExecutable().hasTransition() )
			{
				out << " )";
			}

			return;
		}
	}

	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		if( aRF.refExecutable().hasTransition() )
		{
			toStreamLifelineStateFormat(out, aRF, formatLifelineStatePattern)
					<< " ";
		}

		out << "( ";
		for( bool needComa = false ; itRID != itRIDEnd ; ++itRID )
		{
			if( (*itRID).refExecutable().hasOnInitOrEnableOrRun() )
			{
				if( isRunnable( *itRID ) || isFinalizedOrDestroyed( *itRID ) )
				{
					if( needComa )
					{
						out << " , ";
					}
					else
					{
						needComa = true;
					}
					toStreamStateConf(out, getRuntime(*itRID),
							formatLifelineStatePattern );
				}
			}
		}
		out << " )";
	}
	else
	{
		if( isFinalized( aRF.getRID() ) )
		{
			out << "<final>";
		}
		else if( isDestroyed( aRF.getRID() ) )
		{
			out << "<destroy>";
		}

		toStreamLifelineStateFormat(out, aRF, formatLifelineStatePattern);
	}
}


/**
 * string of a state configuration of an ExecutionData to Fscn
 */
void ExecutionData::toStreamStateConfToFscn(
		OutStream & out, const RuntimeForm & aRF) const
{
	if ( aRF.hasOnSchedule() )
	{
		if( aRF.getOnSchedule()->hasOneOperand()
			&& aRF.getOnSchedule()->first().is< RuntimeID >()
			&& getRuntime(aRF.getOnSchedule()->first().bfRID()).isInstanciated() )
		{
			toStreamStateConfToFscn(out,
					getRuntime( aRF.getOnSchedule()->first().bfRID() ) );

			return;
		}
	}

	if( aRF.hasChild() )
	{
		TableOfRuntimeID::const_iterator itRID = aRF.beginChild();
		TableOfRuntimeID::const_iterator itRIDEnd = aRF.endChild();

		out << "( " ;
		for( bool needComa = false ; itRID != itRIDEnd ; ++itRID )
		{
			if( (*itRID).refExecutable().hasOnInitOrEnableOrRun()
				&& getRuntime(*itRID).isInstanciated() )
			{
				if( needComa )
				{
					out << " , ";
				}
				else
				{
					needComa = true;
				}
				toStreamStateConfToFscn(out, getRuntime((*itRID)) );
			}
		}
		out << " )";
	}
	else
	{
		out << aRF.getRID().strUniqId();
	}
}


/**
 * Serialization
 */
void ExecutionData::toStream(OutStream & out) const
{
	out << TAB << "ed";

	const std::string conf = strStateConf();
	if( conf[0] == '(' )
	{
		out << conf;
	}
	else
	{
		out << '(' << conf << ')';
	}

	mSmartPtr->AVM_DEBUG_REF_COUNTER(out);
	out << " {" << EOL_FLUSH;

//	out << TAB2 << "name = \"" << strStateConf() << "\";" << EOL_FLUSH;

	if ( hasRunnableElementTrace() )
	{
		out << TAB2 << "fired = " << getRunnableElementTrace().str()
			<< ";" << EOL_FLUSH;
	}

	if ( hasIOElementTrace() )
	{
		out << TAB2 << "trace = " << getIOElementTrace().str() << ";"
			<< EOL_FLUSH;
	}

	out << TAB2 << "exec_status = "
		<< RuntimeDef::strAEES( getAEES() ) << ";" << EOL_FLUSH;

	if ( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		out << TAB2 << "firedcondition = "
			<< getNodeCondition().wrapStr( out.INDENT.tab2Size(18) )
			<< ";" << EOL;
	}

	if ( hasNodeTimedCondition() &&
		getNodeTimedCondition().isNotEqualTrue() )
	{
		out << TAB2 << "firedtimedcondition = "
			<< getNodeTimedCondition().wrapStr( out.INDENT.tab2Size(23) )
			<< ";" << EOL;
	}

	if( hasPathCondition() && getPathCondition().isNotEqualTrue() )
	{
		out << TAB2 << "pathcondition = "
			<< getPathCondition().wrapStr( out.INDENT.tab2Size(17) )
			<< ";";
		getPathCondition().AVM_DEBUG_REF_COUNTER(out);
		out << EOL_FLUSH;
	}
	else if( not hasPathCondition() )
	{
		out << TAB2 << "pathcondition = nullptr;" << EOL;
	}

	if( hasPathTimedCondition() && getPathTimedCondition().isNotEqualTrue() )
	{
		out << TAB2 << "pathtimedcondition = "
			<< getPathTimedCondition().wrapStr( out.INDENT.tab2Size(22) )
			<< ";";
		getPathTimedCondition().AVM_DEBUG_REF_COUNTER(out);
		out << EOL_FLUSH;
	}
	else if( not hasPathTimedCondition() )
	{
		out << TAB2 << "pathtimedcondition = nullptr;" << EOL;
	}

	out << TAB2 << "@init{" << INCR2_INDENT;
	getOnInit()->toStreamRoutine( out );
	out << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;

	out << TAB2 << "@schedule{" << INCR2_INDENT;
	getOnSchedule()->toStreamRoutine( out );
	out << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;

	out << TAB2 << "rid = " << getRID().str() << ";" << EOL_FLUSH;


//	if( hasParam() )
//	{
//		out << EOL
//			<< TAB << "parameter:";
//		tableOfParam->AVM_DEBUG_REF_COUNTER(out);
//		out << EOL;
//
//		tableOfParam->toStream(out);
//	}


//AVM_IF_DEBUG_ENABLED_AND( hasTableOfRID() )
//	out << EOL;
//
//	AVM_IF_DEBUG_LEVEL_GT_MEDIUM
//		out << TAB << "rid:" << EOL_INCR_INDENT;
//		TableOfRuntimeID::const_iterator it = mTableOfRID->begin();
//		TableOfRuntimeID::const_iterator itEnd = mTableOfRID->end();
//		for( ; it != itEnd ; ++it )
//		{
//			(*it).toStream(out);
//		}
//		out << DECR_INDENT;
//	AVM_ELSEIF_DEBUG_LEVEL_GT_LOW
//		out << TAB2 << "rid = [| ";
//		TableOfRuntimeID::const_iterator it = mTableOfRID->begin();
//		TableOfRuntimeID::const_iterator itEnd = mTableOfRID->end();
//		for( ; it != itEnd ; ++it )
//		{
//			out << (*it).getOffset() << " ";
//		}
//		out << "|];" << EOL_FLUSH;
//	AVM_ENDIF_DEBUG_LEVEL_GT_LOW
//AVM_ENDIF_DEBUG_ENABLED_AND


	if( hasLocalRuntimeStack() )
	{
		out << EOL_TAB << "local: ";
		getLocalRuntimes()->AVM_DEBUG_REF_COUNTER(out);

		out << EOL_INCR_INDENT;
		getLocalRuntimes()->toStream(out);
		out << DECR_INDENT;
	}

	if ( getTableOfRuntime().nonempty() )
	{
		out << EOL_TAB << "runtime#state:" << EOL_INCR_INDENT;
		mSmartPtr->mTableOfRFStateFlags->toStream(*this, out);

		out << EOL_DECR_INDENT << TAB << "runtime:" << EOL_INCR_INDENT;

AVM_IF_DEBUG_LEVEL_GTE_LOW
		for( const auto & itRF : mSmartPtr->mTableOfRuntime )
		{
			itRF->toStream(*this, out);
		}
AVM_ENDIF_DEBUG_LEVEL_GTE_LOW

		out << DECR_INDENT;
	}

	if( mSmartPtr->mSTATEMENT_QUEUE.nonempty() )
	{
		out << EOL_INCR_INDENT;
		mSmartPtr->mSTATEMENT_QUEUE.toStream(out);
		out << DECR_INDENT;
	}

	if( mSmartPtr->mEXEC_SYNC_POINT != nullptr )
	{
		out << EOL_INCR_INDENT;
		mSmartPtr->mEXEC_SYNC_POINT->toStream(out);
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}

void ExecutionData::toStreamData(OutStream & out) const
{

	out << TAB << "ed<data>";
	mSmartPtr->AVM_DEBUG_REF_COUNTER(out);
	out << " {" << EOL;

	out << TAB2 << "name = \"" << strStateConf() << "\";" << EOL_FLUSH;


	if ( hasRunnableElementTrace() )
	{
		out << TAB2 << "fired = " << getRunnableElementTrace().str()
			<< ";" << EOL_FLUSH;
	}

	if ( hasIOElementTrace() )
	{
		out << TAB2 << "trace = " << getIOElementTrace().str() << ";"
			<< EOL_FLUSH;
	}

	out << TAB2 << "exec_status = "
		<< RuntimeDef::strAEES( getAEES() ) << ";" << EOL_FLUSH;

	if ( hasNodeCondition() && getNodeCondition().isNotEqualTrue() )
	{
		out << TAB2 << "nodecondition = "
			<< getNodeCondition().wrapStr( out.INDENT.tab2Size(18) )
			<< ";" << EOL_FLUSH;
	}

	if ( hasPathCondition() && getPathCondition().isNotEqualTrue() )
	{
		out << TAB2 << "pathcondition = "
			<< getPathCondition().wrapStr( out.INDENT.tab2Size(17) )
			<< ";" << EOL_FLUSH;
	}

	if( hasOnInit() )
	{
		out << TAB2 << "@init{" << INCR2_INDENT;
		getOnInit()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;
	}

	if( hasOnSchedule() )
	{
		out << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL_FLUSH;
	}

//	if( hasParam() )
//	{
//		out << EOL
//			<< TAB << "parameter:" << EOL;
//		tableOfParam->toStream(out, TAB2, CHAR, EOL);
//	}

	if ( getTableOfRuntime().nonempty() )
	{
		out << EOL_TAB << "runtime:" << EOL_INCR_INDENT;

		for( const auto & itRF : mSmartPtr->mTableOfRuntime )
		{
			if( itRF->hasDataTable() )
			{
				itRF->toStreamData(*this, out);
			}
		}

		out << DECR_INDENT;
	}

	if( mSmartPtr->mSTATEMENT_QUEUE.nonempty() )
	{
		out << EOL_INCR_INDENT;
		mSmartPtr->mSTATEMENT_QUEUE.toStream(out);
		out << DECR_INDENT;
	}

	if( mSmartPtr->mEXEC_SYNC_POINT != nullptr )
	{
		out << EOL_INCR_INDENT;
		mSmartPtr->mEXEC_SYNC_POINT->toStream(out);
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}

void ExecutionData::toFscn(OutStream & out,
		const ExecutionData & aPreviousExecData) const
{
//	out << TAB << "SC: " << strStateConfToFscn() << EOL;

	if( aPreviousExecData.isNull() ||
		(aPreviousExecData.getPathCondition() != getPathCondition()) )
	{
		out << TAB << "PC: "
			<< getPathCondition().wrapStr( out.INDENT.tab2Size(4) )
			<< EOL;
	}

	if( aPreviousExecData.isNull() ||
		(aPreviousExecData.getPathTimedCondition() != getPathTimedCondition()) )
	{
		out << TAB << "PtC: "
			<< getPathTimedCondition().wrapStr( out.INDENT.tab2Size(5) )
			<< EOL;
	}

	// DATA
	StringOutStream oss( out.INDENT );
	oss << INCR_INDENT;

	TableOfRuntimeT::const_iterator it = mSmartPtr->mTableOfRuntime.begin();
	TableOfRuntimeT::const_iterator itEnd = mSmartPtr->mTableOfRuntime.end();

	if( aPreviousExecData.isnotNull() )
	{
		TableOfRuntimeT::const_iterator itPrev =
				aPreviousExecData.mSmartPtr->mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itPrevEnd =
				aPreviousExecData.mSmartPtr->mTableOfRuntime.end();
		TableOfRuntimeT::const_iterator it = mSmartPtr->mTableOfRuntime.begin();
		TableOfRuntimeT::const_iterator itEnd = mSmartPtr->mTableOfRuntime.end();
		for( ; (it != itEnd) && (itPrev != itPrevEnd) ; ++it , ++itPrev )
		{
			if( (*it)->hasDataTable() && (*it)->isNTEQ(*itPrev) )
			{
				(*it)->toFscnData(oss, *this, *(*itPrev));
			}
		}

		for( ; (it != itEnd) ; ++it)
		{
			if( (*it)->hasDataTable() )
			{
				(*it)->toFscnData(oss, *this, RuntimeForm::nullref());
			}
		}
	}
	else
	{
		for( const auto & itRF : mSmartPtr->mTableOfRuntime )
		{
			if( itRF->hasDataTable() )
			{
				itRF->toFscnData(oss, *this, RuntimeForm::nullref());
			}
		}
	}

	if( not oss.str().empty() )
	{
		out << TAB << "DATA{" << EOL
			<< oss.str()
			<< TAB << "}" << EOL;
	}
	// END DATA

	// BUFFER
	StringOutStream osb( out.INDENT );
	osb << INCR_INDENT;

	it = getTableOfRuntime().begin();
	itEnd = getTableOfRuntime().end();

	if( aPreviousExecData.isnotNull() )
	{
		TableOfRuntimeT::const_iterator itPrev =
				aPreviousExecData.getTableOfRuntime().begin();
		TableOfRuntimeT::const_iterator itPrevEnd =
				aPreviousExecData.getTableOfRuntime().end();
		for( ; (it != itEnd) && (itPrev != itPrevEnd) ; ++it , ++itPrev )
		{
			if( (*it)->hasBufferTable() && (*it)->isNTEQ(*itPrev) )
			{
				(*it)->toFscnBuffer(osb, *this, *(*itPrev));
			}
		}

		for( ; (it != itEnd) ; ++it)
		{
			if( (*it)->hasBufferTable() )
			{
				(*it)->toFscnBuffer(osb, *this, RuntimeForm::nullref());
			}
		}
	}
	else
	{
		for( const auto & itRF : mSmartPtr->mTableOfRuntime )
		{
			if( itRF->hasBufferTable() )
			{
				itRF->toFscnBuffer(osb, *this, RuntimeForm::nullref());
			}
		}
	}

	if( not osb.str().empty() )
	{
		out << TAB << "BUFFER{" << EOL
			<< osb.str()
			<< TAB << "}" << EOL;
	}
	// END BUFFER


	if( mSmartPtr->mSTATEMENT_QUEUE.nonempty() )
	{
		out << TAB << "/*" << EOL;
		mSmartPtr->mSTATEMENT_QUEUE.toStream(out);
		out << TAB << "*/" << EOL;
	}

	if( mSmartPtr->mEXEC_SYNC_POINT != nullptr )
	{
		out << TAB << "/*" << EOL;
		mSmartPtr->mEXEC_SYNC_POINT->toStream(out);
		out << TAB << "*/" << EOL;
	}
}


}
