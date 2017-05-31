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


/**
 ***************************************************************************
 * execution of an INTERLEAVING program
 ***************************************************************************
 */
bool AvmPrimitive_Interleaving::run(ExecutionEnvironment & ENV)
{
	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( ; it != endIt ; ++it )
	{
		ENV.run( *it );
	}

	return( true );
}

bool AvmPrimitive_RdvInterleaving::run(ExecutionEnvironment & ENV)
{
	ExecutionEnvironment tmpENV(ENV, BFCode::REF_NULL);
	APExecutionData tmpED;

	RdvConfigurationData aRdvConf(ENV, ENV.inCODE->size());
	bool checkRdv = false;
	bool checkMultiRdv = false;

	bool hasCom = false;

	avm_offset_t idx = 0;

	ListOfAPExecutionData listofRDV;

	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( ; it != endIt ; ++it )
	{
		if( not tmpENV.run(*it) )
		{
			return( false );
		}

//		AVM_OS_COUT << "AvmPrimitive_RdvInterleaving::run :>" << std::endl;
//		tmpENV.toStream(AVM_OS_COUT);

		while( tmpENV.syncEDS.nonempty() )
		{
			tmpENV.syncEDS.pop_first_to( tmpED );

			switch( tmpED->mAEES )
			{
				case AEES_WAITING_INCOM_RDV:
				{
					hasCom = true;

					if( tmpED->mEXEC_SYNC_POINT->mRoutingData.isProtocolRDV() )
					{
						aRdvConf.IN_ED_RDV[ idx ].append( tmpED );
						aRdvConf.mAwaitingOutputRdvFlag[ idx ] = true;
						checkRdv = true;
					}
					else if( tmpED->mEXEC_SYNC_POINT->mRoutingData.
							isProtocolMULTI_RDV() )
					{
						aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
						aRdvConf.mAwaitingOutputMultiRdvFlag[ idx ] = true;
						checkMultiRdv = true;
					}

					break;
				}

				case AEES_WAITING_OUTCOM_RDV:
				{
					hasCom = true;

					if( tmpED->mEXEC_SYNC_POINT->mRoutingData.isProtocolRDV() )
					{
						aRdvConf.OUT_ED_RDV[ idx ].append( tmpED );
						aRdvConf.mAwaitingInputRdvFlag[ idx ] = true;
						checkRdv = true;
					}
					else if( tmpED->mEXEC_SYNC_POINT->mRoutingData.
							isProtocolMULTI_RDV() )
					{
						aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
						aRdvConf.mAwaitingInputMultiRdvFlag[ idx ] = true;
						checkMultiRdv = true;
					}

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		if( hasCom )
		{
			idx = idx + 1;

			hasCom = false;
		}
	}

	// output EDS traitement
	ENV.spliceOutput(tmpENV);

	// Sync EDS traitement
	if( idx > 1 )
	{
		aRdvConf.resize( idx );

		if( checkRdv )
		{
			aRdvConf.updatePossibleInternalRdvFlag();
		}
		if( checkMultiRdv )
		{
			aRdvConf.updatePossibleInternalMultiRdvFlag();
		}

		if( aRdvConf.hasPossibleInternalRdvFlag || aRdvConf.hasPossibleInternalMultiRdvFlag )
		{
			AvmCommunicationRdvPrimitive rdvComputer(PRIMITIVE_PROCESSOR, aRdvConf, checkRdv, checkMultiRdv);

			if( rdvComputer.resume_rdv(listofRDV) )
			{
				ENV.outEDS.splice( listofRDV );
			}
		}
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

	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( AvmCode::const_iterator it = ENV.inCODE->begin() ; it != endIt ; ++it )
	{
		ENV.run( *it );
	}

	return( true );
}


bool AvmPrimitive_RdvAsynchronous::run(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "TODO Primitive< ||a|| >::run( ENV )"
				" a.k.a RDV< ASynchronous >::run( ENV ) !!!"
			<< SEND_EXIT;

	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( AvmCode::const_iterator it = ENV.inCODE->begin() ; it != endIt ; ++it )
	{
		ENV.run( *it );
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
	ListOfAPExecutionData tmpListOfED;

	ListOfAPExecutionData fusionListOfOutputED;

	ListOfAPExecutionData::iterator itED;
	ListOfAPExecutionData::iterator endItED;

	APExecutionData tmpED;
	APExecutionData anED;

	AvmCode::const_iterator itEnd = ENV.inCODE->end();
	AvmCode::const_iterator it = ENV.inCODE->begin();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *it);
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

	for( ++it ; it != itEnd ; ++it )
	{
		if( not tmpENV.run(*it) )
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
		AVM_OS_TRACE << "<< " << ENV.inED->mRID.strUniqId()
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
		AVM_OS_TRACE << ">> " << ENV.inED->mRID.strUniqId()
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

	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( AvmCode::const_iterator it = ENV.inCODE->begin() ; it != endIt ; ++it )
	{
		ENV.run( *it );
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
	ENV.inED->setEnabledLocalNodeCondition( true );

	ListOfAPExecutionData oneListOfED;
	ListOfAPExecutionData otherListOfED;
	ListOfAPExecutionData resultListOfED;

	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator itEnd = ENV.inCODE->end();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *it);
	if( not tmpENV.run() )
	{
		return( false );
	}
	oneListOfED.splice( tmpENV.outEDS );

	// Recurrence
	for( ++it ; it != itEnd ; ++it )
	{
		if( not tmpENV.run(*it) )
		{
			return( false );
		}

		computeWeakSynchronous(ENV.inED,
				oneListOfED, tmpENV.outEDS, resultListOfED);

		oneListOfED.clear();
		otherListOfED.clear();
		while( resultListOfED.nonempty() )
		{
			resultListOfED.last()->setEnabledLocalNodeCondition( false );

			oneListOfED.append( resultListOfED.pop_last() );
		}
	}

	ENV.inED->setEnabledLocalNodeCondition( false );

	ENV.outEDS.splice( oneListOfED );

	return( true );
}



bool AvmPrimitive_WeakSynchronous::computeWeakSynchronous(
		APExecutionData & anInputED, ListOfAPExecutionData & oneListOfED,
		ListOfAPExecutionData & otherListOfED,
		ListOfAPExecutionData & resultListOfED)
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
		ListOfAPExecutionData::iterator itOther = otherListOfED.begin();
		ListOfAPExecutionData::iterator endOther = otherListOfED.end();
		for( ; itOther != endOther ; ++itOther )
		{
			if( not computeWeakSynchronous(anInputED,
					*itOther, oneListOfED, resultListOfED) )
			{
				return( false );
			}
		}
	}

	resultListOfED.makeUnique();

	return( true );
}


bool AvmPrimitive_WeakSynchronous::computeWeakSynchronous(
		APExecutionData & anInputED, APExecutionData & oneED,
		ListOfAPExecutionData & listOfOtherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	APExecutionData anED;

	ListOfAPExecutionData::iterator itOther;
	ListOfAPExecutionData::iterator endOther = listOfOtherED.end();

	// Fusion with OTHERS
	for( itOther = listOfOtherED.begin() ; itOther != endOther ; ++itOther )
	{
		anED = AvmSynchronizationFactory::fusion(anInputED, oneED, *itOther);
		if( anED != NULL )
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
		APExecutionData & anInputED, APExecutionData & oneED,
		APExecutionData & otherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	APExecutionData anED = AvmSynchronizationFactory::fusion(
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

	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( AvmCode::const_iterator it = ENV.inCODE->begin() ; it != endIt ; ++it )
	{
		ENV.run( *it );
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
//	AvmCode::const_iterator it = ENV.inCODE->begin();
//	AvmCode::const_iterator itEnd = ENV.inCODE->end();
//
//	// Cas de l'éventuel premier exitEDS
//	for( idx = 0 ; it != itEnd ; ++it, ++idx )
//	{
//		if( not tabOfENV[idx].run(*it) )
//		{
//			return( false );
//		}
//	}

	ListOfAPExecutionData fusionListOfOutputED;
	ListOfAPExecutionData parallelOutputED;

	ListOfAPExecutionData fusionListOfExitED;
	ListOfAPExecutionData parallelExitED;

	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator itEnd = ENV.inCODE->end();

	// Cas de l'éventuel premier exitEDS
	for( ; (it != itEnd) && parallelExitED.empty() ; ++it )
	{
		ExecutionEnvironment tmpENV(ENV, *it);
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
	for( ; (it != itEnd) && parallelOutputED.nonempty() ; ++it )
	{
		ExecutionEnvironment tmpENV(ENV, *it);
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
	for( ; it != itEnd ; ++it )
	{
		ExecutionEnvironment tmpENV(ENV, *it);
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


void AvmPrimitive_Parallel::computeParallel(APExecutionData & refED,
		ListOfAPExecutionData & outEDS,
		ListOfAPExecutionData & prevParallelListOfOutputED,
		ListOfAPExecutionData & listOfOutputED)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
	AVM_OS_TRACE << "<< " << refED->mRID.strUniqId()
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
		ListOfAPExecutionData::iterator itOutED;
		ListOfAPExecutionData::iterator endOutED;

		APExecutionData anED;

		ListOfAPExecutionData::iterator itParallelED =
				prevParallelListOfOutputED.begin();
		ListOfAPExecutionData::iterator endParallelED =
				prevParallelListOfOutputED.end();
		endOutED = outEDS.end();
		for( ; itParallelED != endParallelED ; ++itParallelED )
		{
			for( itOutED = outEDS.begin() ; itOutED != endOutED ; ++itOutED )
			{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
				AVM_OS_TRACE << "ED<frst> "
						<< (*itParallelED)->getRunnableElementTrace().str()
						<< std::endl << "ED<scnd> "
						<< (*itOutED)->getRunnableElementTrace().str()
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
	AVM_OS_TRACE << ">> " << refED->mRID.strUniqId() << " |=> result( "
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
//	AvmCode::const_iterator it = ENV.inCODE->begin();
//	AvmCode::const_iterator itEnd = ENV.inCODE->end();
//
//	// Cas de l'éventuel premier exitEDS
//	for( idx = 0 ; it != itEnd ; ++it, ++idx )
//	{
//		if( not tabOfENV[idx].run(*it) )
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


	ListOfAPExecutionData fusionListOfOutputED;
	ListOfAPExecutionData parallelOutputED;

	ListOfAPExecutionData fusionListOfExitED;
	ListOfAPExecutionData parallelExitED;

	RdvConfigurationData aRdvConf(ENV, ENV.inCODE->size());
	bool checkRdv = false;
	bool checkMultiRdv = false;

	bool hasCom = false;

	avm_offset_t idx = 0;

	ListOfAPExecutionData listofRDV;


	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator itEnd = ENV.inCODE->end();

	// Cas de l'éventuel premier exitEDS
	for( ; (it != itEnd) && parallelExitED.empty() ; ++it )
	{
		ExecutionEnvironment tmpENV(ENV, *it);
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
						checkRdv, checkMultiRdv, hasCom, idx);
			}

			ENV.spliceNotOutputExit(tmpENV);
		}
		else
		{
			return( false );
		}
	}

	// Cas de cohabitation outEDS et exitEDS
	for( ; (it != itEnd) && parallelOutputED.nonempty() ; ++it )
	{
		ExecutionEnvironment tmpENV(ENV, *it);
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
						checkRdv, checkMultiRdv, hasCom, idx);
			}

			ENV.spliceNotOutputExit(tmpENV);
		}
		else
		{
			return( false );
		}
	}

	// Cas ou tout le monde est contaminé par exitEDS
	for( ; it != itEnd ; ++it )
	{
		ExecutionEnvironment tmpENV(ENV, *it);
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
						checkRdv, checkMultiRdv, hasCom, idx);
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

		if( checkRdv )
		{
			aRdvConf.updatePossibleInternalRdvFlag();
		}
		if( checkMultiRdv )
		{
			aRdvConf.updatePossibleInternalMultiRdvFlag();
		}

		if( aRdvConf.hasPossibleInternalRdvFlag ||
				aRdvConf.hasPossibleInternalMultiRdvFlag )
		{
			AvmCommunicationRdvPrimitive rdvComputer(PRIMITIVE_PROCESSOR,
					aRdvConf, checkRdv, checkMultiRdv);

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


void AvmPrimitive_RdvParallel::configureRdv(RdvConfigurationData & aRdvConf,
		ListOfAPExecutionData & syncEDS, bool & checkRdv,
		bool & checkMultiRdv, bool & hasCom, avm_offset_t & idx)
{
	APExecutionData tmpED;

	while( syncEDS.nonempty() )
	{
		syncEDS.pop_first_to( tmpED );

		switch( tmpED->mAEES )
		{
			case AEES_WAITING_INCOM_RDV:
			{
				hasCom = true;

				if( tmpED->mEXEC_SYNC_POINT->mRoutingData.isProtocolRDV() )
				{
					aRdvConf.IN_ED_RDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingOutputRdvFlag[ idx ] = true;
					checkRdv = true;
				}
				else if( tmpED->mEXEC_SYNC_POINT->mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingOutputMultiRdvFlag[ idx ] = true;
					checkMultiRdv = true;
				}

				break;
			}

			case AEES_WAITING_OUTCOM_RDV:
			{
				hasCom = true;

				if( tmpED->mEXEC_SYNC_POINT->mRoutingData.isProtocolRDV() )
				{
					aRdvConf.OUT_ED_RDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingInputRdvFlag[ idx ] = true;
					checkRdv = true;
				}
				else if( tmpED->mEXEC_SYNC_POINT->mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf.ED_MULTIRDV[ idx ].append( tmpED );
					aRdvConf.mAwaitingInputMultiRdvFlag[ idx ] = true;
					checkMultiRdv = true;
				}

				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS :> "
						<< RuntimeDef::strAEES( tmpED->mAEES ) << " !!!"
						<< SEND_EXIT;
			}
		}
	}

	if( hasCom )
	{
		idx = idx + 1;

		hasCom = false;
	}
}



/**
 ***************************************************************************
 * execution of a PRODUCT program
 ***************************************************************************
 */
bool AvmPrimitive_Product::run(ExecutionEnvironment & ENV)
{
	ENV.inED->setEnabledLocalNodeCondition( true );

	ListOfAPExecutionData oneListOfED;
	ListOfAPExecutionData otherListOfED;
	ListOfAPExecutionData resultListOfED;

	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator itEnd = ENV.inCODE->end();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *it);
	if( not tmpENV.run() )
	{
		return( false );
	}
	oneListOfED.splice( tmpENV.outEDS );

	// Recurrence
	for( ++it ; it != itEnd ; ++it )
	{
		if( not tmpENV.run(*it) )
		{
			return( false );
		}

		computeProduct(ENV.inED, oneListOfED, tmpENV.outEDS, resultListOfED);

		oneListOfED.clear();
		otherListOfED.clear();
		while( resultListOfED.nonempty() )
		{
			resultListOfED.last()->setEnabledLocalNodeCondition( false );

			oneListOfED.append( resultListOfED.pop_last() );
		}
	}

	ENV.inED->setEnabledLocalNodeCondition( false );

	ENV.outEDS.splice( oneListOfED );

	return( true );
}



bool AvmPrimitive_Product::computeProduct(APExecutionData & anInputED,
		ListOfAPExecutionData & oneListOfED,
		ListOfAPExecutionData & otherListOfED,
		ListOfAPExecutionData & resultListOfED)
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
		ListOfAPExecutionData::iterator itOther = otherListOfED.begin();
		ListOfAPExecutionData::iterator endOther = otherListOfED.end();
		for( ; itOther != endOther ; ++itOther )
		{
			if( not computeProduct(anInputED,
					*itOther, oneListOfED, resultListOfED) )
			{
				return( false );
			}
		}
	}

	resultListOfED.makeUnique();

	return( true );
}


bool AvmPrimitive_Product::computeProduct(
		APExecutionData & anInputED, APExecutionData & oneED,
		ListOfAPExecutionData & listOfOtherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	APExecutionData anED;

	ListOfAPExecutionData::iterator itOther;
	ListOfAPExecutionData::iterator endOther = listOfOtherED.end();

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


bool AvmPrimitive_Product::computeProduct(APExecutionData & anInputED,
		APExecutionData & oneED, APExecutionData & otherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	APExecutionData anED = AvmSynchronizationFactory::fusion(
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

	APExecutionData tmpED;
	while( tmpENV.syncEDS.nonempty() )
	{
		tmpENV.syncEDS.pop_first_to( tmpED );

		switch( tmpED->mAEES )
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
