/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmConcurrencyPrimitive.h"

#include <computer/ExecutionEnvironment.h>

#include <computer/primitive/AvmCommunicationRdvPrimitive.h>
#include <computer/primitive/AvmSynchronizationFactory.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


/*
 ***************************************************************************
 ***************************************************************************
 * RDV COMMUNICATION UTILS
 ***************************************************************************
 ***************************************************************************
 */


// Compute EVAL where NOT OTHER
bool AvmBaseRdvPrimitive::buildRdvConfiguration(
		RdvConfigurationData & aRdvConf,
		avm_offset_t idx, ListOfExecutionData & syncEDS,
		bool & hasPossibleRdv, bool & hasPossibleMultiRdv)
{
	ExecutionData tmpED;

	while( syncEDS.nonempty() )
	{
		syncEDS.pop_first_to( tmpED );

		switch( tmpED.getAEES() )
		{
			case AEES_WAITING_INCOM_RDV:
			{
				if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					aRdvConf.IN_ED_RDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingOutputRdvFlag[ idx ] = true;
					hasPossibleRdv = true;
				}
				else if( tmpED.getExecSyncPoint()->
						mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingOutputMultiRdvFlag[ idx ] = true;
					hasPossibleMultiRdv = true;
				}

				break;
			}

			case AEES_WAITING_OUTCOM_RDV:
			{
				if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					aRdvConf.OUT_ED_RDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingInputRdvFlag[ idx ] = true;
					hasPossibleRdv = true;
				}
				else if( tmpED.getExecSyncPoint()->
						mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingInputMultiRdvFlag[ idx ] = true;
					hasPossibleMultiRdv = true;
				}

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS :> "
						<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}

	return( true );
}


void AvmBaseRdvPrimitive::computeRdv(ExecutionEnvironment & ENV,
		RdvConfigurationData & aRdvConf, avm_offset_t idx,
		bool & hasPossibleRdv, bool & hasPossibleMultiRdv)
{
	aRdvConf.resize( idx );

	if( hasPossibleRdv )
	{
		aRdvConf.updatePossibleInternalRdvFlag();
	}
	if( hasPossibleMultiRdv )
	{
		aRdvConf.updatePossibleInternalMultiRdvFlag();
	}

	if( aRdvConf.hasPossibleInternalRdvFlag
		|| aRdvConf.hasPossibleInternalMultiRdvFlag )
	{
		AvmCommunicationRdvPrimitive rdvComputer(PRIMITIVE_PROCESSOR,
				aRdvConf, hasPossibleRdv, hasPossibleMultiRdv);

		if( rdvComputer.resume_rdv(ENV.outEDS) )
		{
			// OK
		}
	}
}


/**
 ***************************************************************************
 * execution of an INTERLEAVING program
 ***************************************************************************
 */
bool AvmPrimitive_Interleaving::run(ExecutionEnvironment & ENV)
{
	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.run( itOperand );
	}

	return( true );
}

bool AvmPrimitive_RdvInterleaving::run(ExecutionEnvironment & ENV)
{
	ExecutionEnvironment tmpENV(ENV, BFCode::REF_NULL);
	ExecutionData tmpED;

	RdvConfigurationData aRdvConf(ENV, ENV.inCODE->size());
	bool hasPossibleRdv = false;
	bool hasPossibleMultiRdv = false;

	avm_offset_t idx = 0;

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		if( not tmpENV.run( itOperand ) )
		{
			return( false );
		}

		if( tmpENV.syncEDS.nonempty() )
		{
			if( buildRdvConfiguration(aRdvConf, idx, tmpENV.syncEDS,
					hasPossibleRdv, hasPossibleMultiRdv) )
			{
				idx = idx + 1;
			}
			else
			{
				return( false );
			}
		}
	}

	// output EDS traitement
	ENV.spliceOutput(tmpENV);

	// Sync EDS traitement
	if( idx > 1 )
	{
		computeRdv(ENV, aRdvConf, idx, hasPossibleRdv, hasPossibleMultiRdv);
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of an PARTIAL_ORDER program
 ***************************************************************************
 */
bool AvmPrimitive_PartialOrder::run(ExecutionEnvironment & ENV)
{
	ExecutionData poED = ENV.inED;

	const RuntimeID & poRID = poED.getRID();

	const AvmCode & scheduleCode =
			poED.getRuntimeFormOnSchedule(poRID).to< AvmCode >();

	std::size_t ScheduleSize = scheduleCode.size();

	BFCode poCode = poED.getRuntimeFormOnDefer(poRID);

	if( poCode.valid() )
	{
		// Position of current PO Code  in Scheduler Code
		AvmCode::const_iterator itOperandPosition = scheduleCode.begin();
		AvmCode::const_iterator endOperand = scheduleCode.end();
		for( ; itOperandPosition != endOperand ; ++itOperandPosition )
		{
			if( (*itOperandPosition).isEQ( poCode ) )
			{
				break;
			}
		}

		ExecutionEnvironment tmpENV(ENV);

		std::size_t runCount = 0;
		for( ; runCount < ScheduleSize ; ++runCount )
		{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
	AVM_OS_INFO << "PartialOrder: " + poCode.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )

			if( not tmpENV.run(poED, poCode) )
			{
				return( false );
			}

			// Next PO Code in Scheduler Code
			if( (++itOperandPosition) == endOperand )
			{
				itOperandPosition = scheduleCode.begin();
			}

			if( (*itOperandPosition).is< AvmCode >() )
			{
				poCode = (*itOperandPosition).bfCode();
			}

			if( tmpENV.hasOutputSyncIrq() )
			{
				break;
			}
		}

		for( auto & itED : tmpENV.outEDS )
		{
			itED.mwsetRuntimeFormOnDefer(poRID, poCode);
		}

		ENV.spliceOutput(tmpENV);

		ENV.spliceNotOutput(tmpENV);
	}
	else
	{
		for( const auto & itOperand : ENV.inCODE.getOperands() )
		{
			ENV.run( itOperand );
		}
	}

	return( true );
}


bool AvmPrimitive_RdvPartialOrder::run(ExecutionEnvironment & ENV)
{
	ExecutionEnvironment tmpENV(ENV, BFCode::REF_NULL);
	ExecutionData tmpED;

	RdvConfigurationData aRdvConf(ENV, ENV.inCODE->size());
	bool hasPossibleRdv = false;
	bool hasPossibleMultiRdv = false;

	avm_offset_t idx = 0;

	ListOfExecutionData listofRDV;

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		if( not tmpENV.run( itOperand ) )
		{
			return( false );
		}

		if( tmpENV.syncEDS.nonempty() )
		{
			if( buildRdvConfiguration(aRdvConf, idx, tmpENV.syncEDS,
					hasPossibleRdv, hasPossibleMultiRdv) )
			{
				idx = idx + 1;
			}
			else
			{
				return( false );
			}
		}
	}

	// output EDS traitement
	ENV.spliceOutput(tmpENV);

	// Sync EDS traitement
	if( idx > 1 )
	{
		computeRdv(ENV, aRdvConf, idx, hasPossibleRdv, hasPossibleMultiRdv);
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of an ASYNCHRONOUS program
 ***************************************************************************
 */
bool AvmPrimitive_Asynchronous::run(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "TODO Primitive< |a| >::run( ENV )"
				" a.k.a ASynchronous::run( ENV ) !!!"
			<< SEND_EXIT;

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.run( itOperand );
	}

	return( true );
}


bool AvmPrimitive_RdvAsynchronous::run(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "TODO Primitive< ||a|| >::run( ENV )"
				" a.k.a RDV< ASynchronous >::run( ENV ) !!!"
			<< SEND_EXIT;

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.run( itOperand );
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a STRONG SYNCHRONOUS program
 ***************************************************************************
 */
bool AvmPrimitive_StrongSynchronous::run(ExecutionEnvironment & ENV)
{
	ListOfExecutionData tmpListOfED;

	ListOfExecutionData fusionListOfOutputED;

	ListOfExecutionData::iterator itED;
	ListOfExecutionData::iterator endItED;

	ExecutionData tmpED;
	ExecutionData anED;

	AvmCode::const_iterator endOperand = ENV.inCODE->end();
	AvmCode::const_iterator itOperand = ENV.inCODE->begin();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *itOperand);
	if( not tmpENV.run() )
	{
		return( false );
	}

	if( tmpENV.outEDS.nonempty() )
	{
		tmpListOfED.splice( tmpENV.outEDS );
	}
	else
	{
		// if an execution fail, this execution fail to!!!!!
		return( false );
	}

	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
		if( not tmpENV.run(*itOperand) )
		{
			return( false );
		}

		if( tmpENV.outEDS.empty() )
		{
			// if a local execution fail, this global execution fail to!!!!!
			return( false );
		}


		// COMPUTE STRONG FUSION
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		AVM_OS_TRACE << "<< " << ENV.inED.getRID().strUniqId()
				<< " |=> strong fusion for ED :> "
				<< "frstList( " << tmpENV.outEDS.size() << " )" << " with "
				<< "scndList( " << tmpListOfED.size() << " )" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

		if( tmpListOfED.empty() )
		{
			tmpListOfED.splice(tmpENV.outEDS);
		}
		else if( tmpENV.outEDS.nonempty() )
		{
			do
			{
				tmpENV.outEDS.pop_first_to( tmpED );

				endItED = tmpListOfED.end();
				for ( itED = tmpListOfED.begin() ; itED != endItED ; ++itED )
				{
					anED = AvmSynchronizationFactory::fusion(
							ENV.inED, tmpED, (*itED));
					if( anED.valid() )
					{
						fusionListOfOutputED.append( anED );
					}
				}
			}
			while( tmpENV.outEDS.nonempty() );

			tmpListOfED.clear();
			tmpListOfED.splice(fusionListOfOutputED);
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		AVM_OS_TRACE << ">> " << ENV.inED.getRID().strUniqId()
		<< " |=> result( " << tmpListOfED.size() << " )" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	}

	ENV.outEDS.splice( tmpListOfED );

	return( true );
}


bool AvmPrimitive_RdvStrongSynchronous::run(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "TODO Primitive< ||and|| >::run( ENV )"
				" a.k.a RDV< StrongSynchronous >::run( ENV ) !!!"
			<< SEND_EXIT;

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.run( itOperand );
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a WEAK SYNCHRONOUS program
 ***************************************************************************
 */
bool AvmPrimitive_WeakSynchronous::run(ExecutionEnvironment & ENV)
{
	ENV.inED.setEnabledLocalNodeCondition( true );

	ListOfExecutionData oneListOfED;
	ListOfExecutionData otherListOfED;
	ListOfExecutionData resultListOfED;

	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
	AvmCode::const_iterator endOperand = ENV.inCODE->end();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *itOperand);
	if( not tmpENV.run() )
	{
		return( false );
	}
	oneListOfED.splice( tmpENV.outEDS );

	// Recurrence
	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
		if( not tmpENV.run(*itOperand) )
		{
			return( false );
		}

		computeWeakSynchronous(ENV.inED,
				oneListOfED, tmpENV.outEDS, resultListOfED);

		oneListOfED.clear();
		otherListOfED.clear();
		while( resultListOfED.nonempty() )
		{
			resultListOfED.last().setEnabledLocalNodeCondition( false );

			oneListOfED.append( resultListOfED.pop_last() );
		}
	}

	ENV.inED.setEnabledLocalNodeCondition( false );

	ENV.outEDS.splice( oneListOfED );

	return( true );
}



bool AvmPrimitive_WeakSynchronous::computeWeakSynchronous(
		ExecutionData & anInputED, ListOfExecutionData & oneListOfED,
		ListOfExecutionData & otherListOfED,
		ListOfExecutionData & resultListOfED)
{
	if( otherListOfED.empty() )
	{
		resultListOfED.splice( oneListOfED );
	}

	else if( oneListOfED.empty() )
	{
		resultListOfED.splice( otherListOfED );
	}

	else
	{
		for( auto & itOther : otherListOfED )
		{
			if( not computeWeakSynchronous(anInputED,
					itOther, oneListOfED, resultListOfED) )
			{
				return( false );
			}
		}
	}

	resultListOfED.makeUnique();

	return( true );
}


bool AvmPrimitive_WeakSynchronous::computeWeakSynchronous(
		ExecutionData & anInputED, ExecutionData & oneED,
		ListOfExecutionData & listOfOtherED,
		CollectionOfExecutionData & listOfOutputED)
{
	ExecutionData anED;

	ListOfExecutionData::iterator itOther;
	ListOfExecutionData::iterator endOther = listOfOtherED.end();

	// Fusion with OTHERS
	for( itOther = listOfOtherED.begin() ; itOther != endOther ; ++itOther )
	{
		anED = AvmSynchronizationFactory::fusion(anInputED, oneED, *itOther);
		if( anED.valid() )
		{
			listOfOutputED.append( anED );
		}
	}

	// Compute OTHER where NOT ONE
	if( not evalExclusive(anInputED, listOfOtherED, oneED, listOfOutputED) )
	{
		return( false );
	}


	// Compute ONE where NOT OTHERS
	return( evalExclusive(anInputED, oneED, listOfOtherED, listOfOutputED) );
}


bool AvmPrimitive_WeakSynchronous::computeWeakSynchronous(
		ExecutionData & anInputED, ExecutionData & oneED,
		ExecutionData & otherED,
		CollectionOfExecutionData & listOfOutputED)
{
	ExecutionData anED = AvmSynchronizationFactory::fusion(
			anInputED, oneED, otherED);
	if( anED.valid() )
	{
		listOfOutputED.append( anED );
	}

	// Compute OTHER where NOT ONE
	if( not evalExclusive(anInputED, otherED, oneED, listOfOutputED) )
	{
		return( false );
	}

	// Compute ONE where NOT OTHERS
	return( evalExclusive(anInputED, oneED, otherED, listOfOutputED) );
}


bool AvmPrimitive_RdvWeakSynchronous::run(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "TODO Primitive< ||or|| >::run( ENV )"
				" a.k.a RDV< WeakSynchronous >::run( ENV ) !!!"
			<< SEND_EXIT;

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.run( itOperand );
	}

	return( true );
}





/**
 ***************************************************************************
 * execution of a PARALLEL program
 ***************************************************************************
 */
bool AvmPrimitive_Parallel::run(ExecutionEnvironment & ENV)
{
//	avm_offset_t idx;
//
//	std::vector< ExecutionEnvironment > tabOfENV(
//			ENV.inCODE->size(), ExecutionEnvironment(ENV, ENV.inED) );
//
//	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
//	AvmCode::const_iterator endOperand = ENV.inCODE->end();
//
//	// Cas de l'éventuel premier exitOperandEDS
//	for( idx = 0 ; itOperand != endOperand ; ++itOperand, ++idx )
//	{
//		if( not tabOfENV[idx].run(*itOperand) )
//		{
//			return( false );
//		}
//	}

	ListOfExecutionData fusionListOfOutputED;
	ListOfExecutionData parallelOutputED;

	ListOfExecutionData fusionListOfExitED;
	ListOfExecutionData parallelExitED;

	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
	AvmCode::const_iterator endOperand = ENV.inCODE->end();

	// Cas de l'éventuel premier exitEDS
	for( ; (itOperand != endOperand) && parallelExitED.empty() ; ++itOperand )
	{
		ExecutionEnvironment tmpENV(ENV, *itOperand);
		if( tmpENV.run() )
		{
			ENV.spliceNotOutputExit(tmpENV);

			if( tmpENV.exitEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelOutputED, parallelExitED);
			}

			if( tmpENV.outEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelOutputED, fusionListOfOutputED);

				parallelOutputED.clear();
				parallelOutputED.splice(fusionListOfOutputED);
			}
			else if( tmpENV.exitEDS.nonempty() )
			{
				parallelOutputED.clear();
			}
		}
		else
		{
			return( false );
		}
	}

	// Cas de cohabitation outEDS et exitEDS
	for( ; (itOperand != endOperand) && parallelOutputED.nonempty() ; ++itOperand )
	{
		ExecutionEnvironment tmpENV(ENV, *itOperand);
		if( tmpENV.run() )
		{
			ENV.spliceNotOutputExit(tmpENV);

			if( tmpENV.outEDS.nonempty() )
			{
				// Composition entre << purs Output >>
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelOutputED, fusionListOfOutputED);

				// Composition avec les << Exit précédents >>
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelExitED, fusionListOfExitED);
			}

			if( tmpENV.exitEDS.nonempty() )
			{
				// Composition avec les << Output précédents >>
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelOutputED, fusionListOfExitED);

				// Composition entre << purs Exit >>
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelExitED, fusionListOfExitED);

			}

			if( tmpENV.outEDS.nonempty() || tmpENV.exitEDS.nonempty() )
			{
				parallelOutputED.clear();
				parallelOutputED.splice(fusionListOfOutputED);

				parallelExitED.clear();
				parallelExitED.splice(fusionListOfExitED);
			}
		}
		else
		{
			return( false );
		}
	}

	// Cas ou tout le monde est contaminé par exitEDS
	for( ; itOperand != endOperand ; ++itOperand )
	{
		ExecutionEnvironment tmpENV(ENV, *itOperand);
		if( tmpENV.run() )
		{
			ENV.spliceNotOutputExit(tmpENV);

			if( tmpENV.outEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelExitED, fusionListOfExitED);
			}
			if( tmpENV.exitEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelExitED, fusionListOfExitED);
			}

			if( tmpENV.outEDS.nonempty() || tmpENV.exitEDS.nonempty() )
			{
				parallelExitED.clear();
				parallelExitED.splice(fusionListOfExitED);
			}
		}
		else
		{
			return( false );
		}
	}


	ENV.outEDS.splice( parallelOutputED );
	ENV.exitEDS.splice( parallelExitED );

	return( true );
}


void AvmPrimitive_Parallel::computeParallel(ExecutionData & refED,
		ListOfExecutionData & outEDS,
		ListOfExecutionData & prevParallelListOfOutputED,
		ListOfExecutionData & listOfOutputED)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "<< " << refED.getRID().strUniqId()
			<< " |=> parallel fusion for ED :> "
			<< "frstList( " << outEDS.size() << " ) with "
			<< "scndList( " << prevParallelListOfOutputED.size()
			<< " )" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )

	if( prevParallelListOfOutputED.empty() )
	{
		listOfOutputED.splice(outEDS);
	}
	else if( outEDS.empty() )
	{
		listOfOutputED.splice(prevParallelListOfOutputED);
	}
	else
	{
		ListOfExecutionData::iterator itOutED;
		ListOfExecutionData::iterator endOutED;

		ExecutionData anED;

		ListOfExecutionData::iterator itParallelED =
				prevParallelListOfOutputED.begin();
		ListOfExecutionData::iterator endParallelED =
				prevParallelListOfOutputED.end();
		endOutED = outEDS.end();
		for( ; itParallelED != endParallelED ; ++itParallelED )
		{
			for( itOutED = outEDS.begin() ; itOutED != endOutED ; ++itOutED )
			{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
				AVM_OS_TRACE << "ED<frst> "
						<< (*itParallelED).getRunnableElementTrace().str()
						<< std::endl << "ED<scnd> "
						<< (*itOutED).getRunnableElementTrace().str()
						<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
				anED = AvmSynchronizationFactory::fusion(
						refED, *itParallelED, *itOutED);
				if( anED.valid() )
				{
					listOfOutputED.append( anED );
				}
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << ">> " << refED.getRID().strUniqId() << " |=> result( "
			<< listOfOutputED.size() << " )" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
}




bool AvmPrimitive_RdvParallel::run(ExecutionEnvironment & ENV)
{
//	avm_offset_t idx;
//
//	std::vector< ExecutionEnvironment > tabOfENV(
//			ENV.inCODE->size(), ExecutionEnvironment(ENV, ENV.inED) );
//
//	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
//	AvmCode::const_iterator endOperand = ENV.inCODE->end();
//
//	// Cas de l'éventuel premier exitEDS
//	for( idx = 0 ; itOperand != endOperand ; ++itOperand, ++idx )
//	{
//		if( not tabOfENV[idx].run(*itOperand) )
//		{
//			return( false );
//		}
//	}
//
//	if( AvmCommunicationRdvPrimitive::computeRdv(PRIMITIVE_PROCESSOR, tabOfENV) )
//	{
//		computeParallel(ENV.inED, listofRDV,
//				parallelOutputED, fusionListOfOutputED);
//
//		parallelOutputED.clear();
//		parallelOutputED.splice(fusionListOfOutputED);
//	}
//	else
//	{
//		return( false );
//	}


	ListOfExecutionData fusionListOfOutputED;
	ListOfExecutionData parallelOutputED;

	ListOfExecutionData fusionListOfExitED;
	ListOfExecutionData parallelExitED;

	RdvConfigurationData aRdvConf(ENV, ENV.inCODE->size());
	bool hasPossibleRdv = false;
	bool hasPossibleMultiRdv = false;

	avm_offset_t idx = 0;

	ListOfExecutionData listofRDV;


	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
	AvmCode::const_iterator endOperand = ENV.inCODE->end();

	// Cas de l'éventuel premier exitEDS
	for( ; (itOperand != endOperand) && parallelExitED.empty() ; ++itOperand )
	{
		ExecutionEnvironment tmpENV(ENV, *itOperand);
		if( tmpENV.run() )
		{
			if( tmpENV.exitEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelOutputED, parallelExitED);
			}

			if( tmpENV.outEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelOutputED, fusionListOfOutputED);

				parallelOutputED.clear();
				parallelOutputED.splice(fusionListOfOutputED);
			}
			else if( tmpENV.exitEDS.nonempty() )
			{
				parallelOutputED.clear();
			}

			if( tmpENV.syncEDS.nonempty() )
			{
				configureRdv(aRdvConf, tmpENV.syncEDS,
						hasPossibleRdv, hasPossibleMultiRdv, idx);

				idx = idx + 1;
			}

			ENV.spliceNotOutputExit(tmpENV);
		}
		else
		{
			return( false );
		}
	}

	// Cas de cohabitation outEDS et exitEDS
	for( ; (itOperand != endOperand) && parallelOutputED.nonempty() ; ++itOperand )
	{
		ExecutionEnvironment tmpENV(ENV, *itOperand);
		if( tmpENV.run() )
		{
			if( tmpENV.outEDS.nonempty() )
			{
				// Composition entre << purs Output >>
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelOutputED, fusionListOfOutputED);

				// Composition avec les << Exit précédents >>
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelExitED, fusionListOfExitED);
			}

			if( tmpENV.exitEDS.nonempty() )
			{
				// Composition avec les << Output précédents >>
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelOutputED, fusionListOfExitED);

				// Composition entre << purs Exit >>
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelExitED, fusionListOfExitED);

			}

			if( tmpENV.outEDS.nonempty() || tmpENV.exitEDS.nonempty() )
			{
				parallelOutputED.clear();
				parallelOutputED.splice(fusionListOfOutputED);

				parallelExitED.clear();
				parallelExitED.splice(fusionListOfExitED);
			}

			if( tmpENV.syncEDS.nonempty() )
			{
				configureRdv(aRdvConf, tmpENV.syncEDS,
						hasPossibleRdv, hasPossibleMultiRdv, idx);

				idx = idx + 1;
			}

			ENV.spliceNotOutputExit(tmpENV);
		}
		else
		{
			return( false );
		}
	}

	// Cas ou tout le monde est contaminé par exitEDS
	for( ; itOperand != endOperand ; ++itOperand )
	{
		ExecutionEnvironment tmpENV(ENV, *itOperand);
		if( tmpENV.run() )
		{
			if( tmpENV.outEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.outEDS,
						parallelExitED, fusionListOfExitED);
			}
			if( tmpENV.exitEDS.nonempty() )
			{
				computeParallel(ENV.inED, tmpENV.exitEDS,
						parallelExitED, fusionListOfExitED);
			}

			if( tmpENV.outEDS.nonempty() || tmpENV.exitEDS.nonempty() )
			{
				parallelExitED.clear();
				parallelExitED.splice(fusionListOfExitED);
			}

			if( tmpENV.syncEDS.nonempty() )
			{
				configureRdv(aRdvConf, tmpENV.syncEDS,
						hasPossibleRdv, hasPossibleMultiRdv, idx);

				idx = idx + 1;
			}

			ENV.spliceNotOutputExit(tmpENV);
		}
		else
		{
			return( false );
		}
	}


	if( idx > 1 )
	{
		aRdvConf.resize( idx );

		if( hasPossibleRdv )
		{
			aRdvConf.updatePossibleInternalRdvFlag();
		}
		if( hasPossibleMultiRdv )
		{
			aRdvConf.updatePossibleInternalMultiRdvFlag();
		}

		if( aRdvConf.hasPossibleInternalRdvFlag ||
				aRdvConf.hasPossibleInternalMultiRdvFlag )
		{
			AvmCommunicationRdvPrimitive rdvComputer(PRIMITIVE_PROCESSOR,
					aRdvConf, hasPossibleRdv, hasPossibleMultiRdv);

			if( rdvComputer.resume_rdv(listofRDV) )
			{
				computeParallel(ENV.inED, listofRDV,
						parallelOutputED, fusionListOfOutputED);

				parallelOutputED.clear();
				parallelOutputED.splice(fusionListOfOutputED);
			}
		}
	}


	ENV.outEDS.splice( parallelOutputED );
	ENV.exitEDS.splice( parallelExitED );

	return( true );
}


void AvmPrimitive_RdvParallel::configureRdv(
		RdvConfigurationData & aRdvConf, ListOfExecutionData & syncEDS,
		bool & hasPossibleRdv, bool & hasPossibleMultiRdv, avm_offset_t idx)
{
	ExecutionData tmpED;

	while( syncEDS.nonempty() )
	{
		syncEDS.pop_first_to( tmpED );

		switch( tmpED.getAEES() )
		{
			case AEES_WAITING_INCOM_RDV:
			{
				if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					aRdvConf.IN_ED_RDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingOutputRdvFlag[ idx ] = true;
					hasPossibleRdv = true;
				}
				else if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingOutputMultiRdvFlag[ idx ] = true;
					hasPossibleMultiRdv = true;
				}

				break;
			}

			case AEES_WAITING_OUTCOM_RDV:
			{
				if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					aRdvConf.OUT_ED_RDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingInputRdvFlag[ idx ] = true;
					hasPossibleRdv = true;
				}
				else if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingInputMultiRdvFlag[ idx ] = true;
					hasPossibleMultiRdv = true;
				}

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS :> "
						<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
						<< SEND_EXIT;
			}
		}
	}
}



/**
 ***************************************************************************
 * execution of a PRODUCT program
 ***************************************************************************
 */
bool AvmPrimitive_Product::run(ExecutionEnvironment & ENV)
{
	ENV.inED.setEnabledLocalNodeCondition( true );

	ListOfExecutionData oneListOfED;
	ListOfExecutionData otherListOfED;
	ListOfExecutionData resultListOfED;

	AvmCode::const_iterator itOperand = ENV.inCODE->begin();
	AvmCode::const_iterator endOperand = ENV.inCODE->end();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *itOperand);
	if( not tmpENV.run() )
	{
		return( false );
	}
	oneListOfED.splice( tmpENV.outEDS );

	// Recurrence
	for( ++itOperand ; itOperand != endOperand ; ++itOperand )
	{
		if( not tmpENV.run(*itOperand) )
		{
			return( false );
		}

		computeProduct(ENV.inED, oneListOfED, tmpENV.outEDS, resultListOfED);

		oneListOfED.clear();
		otherListOfED.clear();
		while( resultListOfED.nonempty() )
		{
			resultListOfED.last().setEnabledLocalNodeCondition( false );

			oneListOfED.append( resultListOfED.pop_last() );
		}
	}

	ENV.inED.setEnabledLocalNodeCondition( false );

	ENV.outEDS.splice( oneListOfED );

	return( true );
}



bool AvmPrimitive_Product::computeProduct(ExecutionData & anInputED,
		ListOfExecutionData & oneListOfED,
		ListOfExecutionData & otherListOfED,
		ListOfExecutionData & resultListOfED)
{
	if( otherListOfED.empty() )
	{
		resultListOfED.splice( oneListOfED );
	}

	else if( oneListOfED.empty() )
	{
		resultListOfED.splice( otherListOfED );
	}

	else
	{
		for( auto & itOther : otherListOfED )
		{
			if( not computeProduct(anInputED,
					itOther, oneListOfED, resultListOfED) )
			{
				return( false );
			}
		}
	}

	resultListOfED.makeUnique();

	return( true );
}


bool AvmPrimitive_Product::computeProduct(
		ExecutionData & anInputED, ExecutionData & oneED,
		ListOfExecutionData & listOfOtherED,
		CollectionOfExecutionData & listOfOutputED)
{
	ExecutionData anED;

	ListOfExecutionData::iterator itOther;
	ListOfExecutionData::iterator endOther = listOfOtherED.end();

	// Fusion with OTHERS
	for( itOther = listOfOtherED.begin() ; itOther != endOther ; ++itOther )
	{
		anED = AvmSynchronizationFactory::fusion(anInputED, oneED, *itOther);
		if( anED.valid() )
		{
			listOfOutputED.append( anED );
		}
	}

	// Compute OTHER where NOT ONE
	if( not evalExclusive(anInputED, listOfOtherED, oneED, listOfOutputED) )
	{
		return( false );
	}


	// Compute ONE where NOT OTHERS
	return( evalExclusive(anInputED, oneED, listOfOtherED, listOfOutputED) );
}


bool AvmPrimitive_Product::computeProduct(ExecutionData & anInputED,
		ExecutionData & oneED, ExecutionData & otherED,
		CollectionOfExecutionData & listOfOutputED)
{
	ExecutionData anED = AvmSynchronizationFactory::fusion(
			anInputED, oneED, otherED);
	if( anED.valid() )
	{
		listOfOutputED.append( anED );
	}

	// Compute OTHER where NOT ONE
	if( not evalExclusive(anInputED, otherED, oneED, listOfOutputED) )
	{
		return( false );
	}

	// Compute ONE where NOT OTHERS
	return( evalExclusive(anInputED, oneED, otherED, listOfOutputED) );
}



/**
 ***************************************************************************
 * execution of a SYNCHRONIZE program
 ***************************************************************************
 */
bool AvmPrimitive_Synchronize::run(ExecutionEnvironment & ENV)
{
	ExecutionEnvironment tmpENV(ENV, ENV.inCODE->first());

	if( not tmpENV.run( ENV.inCODE->first() ) )
	{
		return( false );
	}

	ExecutionData tmpED;
	while( tmpENV.syncEDS.nonempty() )
	{
		tmpENV.syncEDS.pop_first_to( tmpED );

		switch( tmpED.getAEES() )
		{
			case AEES_WAITING_INCOM_RDV:
			case AEES_WAITING_OUTCOM_RDV:
			case AEES_WAITING_JOIN_FORK:
			{
				break;
			}

			default:
			{
				ENV.outEDS.append(tmpED);

				break;
			}
		}
	}

	ENV.spliceOutput(tmpENV);
	ENV.spliceNotOutput(tmpENV);

	return( true );
}




}
