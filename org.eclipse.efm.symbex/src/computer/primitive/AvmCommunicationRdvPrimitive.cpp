/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCommunicationRdvPrimitive.h"

#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <computer/primitive/AvmSynchronizationFactory.h>
#include <fml/executable/InstanceOfConnector.h>

#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/RoutingData.h>

#include <fml/expression/StatementConstructor.h>

#include <fml/infrastructure/ComProtocol.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionSynchronizationPoint.h>
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeDef.h>



namespace sep
{


static void print_trace(const ListOfExecutionData & listofWaitingRDV,
		OutStream & out)
{
	for( const auto & itED : listofWaitingRDV )
	{
		itED.printExecSyncPointTrace( out );

//		itED.getExecSyncPoint()->toStream(out, TAB + "\t", "\t", "\n");
	}
}


static void print_trace(const VectorOfExecutionData & tableofWaitingRDV,
		OutStream & out)
{
	for( const auto & itED : tableofWaitingRDV )
	{
		itED.printExecSyncPointTrace( out );

//		itED.getExecSyncPoint()->toStream(out, TAB + "\t", "\t", "\n");
	}
}



////////////////////////////////////////////////////////////////////////////////
// FUSION
////////////////////////////////////////////////////////////////////////////////

RdvConfigurationData * RdvConfigurationData::fusion(RdvConfigurationData * aRdvConf)
{
	RdvConfigurationData * aFusionRdvConf = new RdvConfigurationData(*this, aRdvConf);

	for( std::size_t idx = 0 ; idx < mMachineCount ; ++idx )
	{
		IN_ED_RDV[ idx ].append( aRdvConf->IN_ED_RDV[ idx ] );
		OUT_ED_RDV[ idx ].append( aRdvConf->OUT_ED_RDV[ idx ] );

		ED_MULTIRDV[ idx ].append( aRdvConf->ED_MULTIRDV[ idx ] );

		RDVS[ idx ].append( aRdvConf->RDVS[ idx ] );

		if( mAwaitingMultiRdvEDS[ idx ].invalid() &&
				aRdvConf->mAwaitingMultiRdvEDS[ idx ].valid() )
		{
			mAwaitingMultiRdvEDS [ idx ] = aRdvConf->mAwaitingMultiRdvEDS[ idx ];
			mAwaitingMultiRdvFlag[ idx ] = true;
		}
	}

	return( aFusionRdvConf );
}


////////////////////////////////////////////////////////////////////////////////
// RESIZE
////////////////////////////////////////////////////////////////////////////////

void RdvConfigurationData::resize(std::size_t newSize)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( newSize <= mMachineCount )
			<< "Unexpected machine count for RDV Configuration Data !!!"
			<< SEND_EXIT;

	if( newSize < mMachineCount )
	{
		IN_ED_RDV.resize( newSize );
		OUT_ED_RDV.resize( newSize );

		ED_MULTIRDV.resize( newSize );

		mUsedMachineFlag.resize( newSize , false );

		mAwaitingInputRdvFlag.resize( newSize , false );
		mAwaitingOutputRdvFlag.resize( newSize , false );
		mAwaitingMultiRdvFlag.resize( newSize , false );

		mAwaitingMultiRdvEDS.resize( newSize );

		mMachineCount = newSize;
	}
}

////////////////////////////////////////////////////////////////////////////////
// FLAGS OPERATION
////////////////////////////////////////////////////////////////////////////////

bool RdvConfigurationData::isMultiRdvComplete()
{
	std::size_t inCount = 0;
	std::size_t outCount = 0;

	ExecutionData anED;

	for( std::size_t idx = 0 ; idx < mMachineCount; ++idx )
	{
		if( mAwaitingMultiRdvEDS[ idx ].valid() )
		{
			anED = mAwaitingMultiRdvEDS[ idx ];

			if( anED.getExecSyncPoint()->isOutput() )
			{
				++outCount;
			}
			else //if( anED.getExecSyncPoint()->isInput() )
			{
				++inCount;
			}
		}
	}


	const InstanceOfConnector & aConnector =
			anED.getExecSyncPoint()->mRoutingData.getConnector();

	switch( aConnector.getOutputProtocolCast() )
	{
		case ComProtocol::PROTOCOL_UNICAST_KIND:
		{
			if( outCount != 1 )
			{
				return( false );
			}
			break;
		}


		case ComProtocol::PROTOCOL_MULTICAST_KIND:
		{
			if( outCount != aConnector.sizeOutputMachinePort() )
			{
				return( false );
			}
			break;
		}

		case ComProtocol::PROTOCOL_BROADCAST_KIND:

		case ComProtocol::PROTOCOL_UNDEFINED_KIND:
		default:
		{
			if( outCount == 0 )
			{
				return( false );
			}
			break;
		}
	}

	switch( aConnector.getInputProtocolCast() )
	{
		case ComProtocol::PROTOCOL_UNICAST_KIND:
		{
			if( inCount != 1 )
			{
				return( false );
			}
			break;
		}

		case ComProtocol::PROTOCOL_MULTICAST_KIND:
		{
			if( inCount != aConnector.sizeInputMachinePort() )
			{
				return( false );
			}
			break;
		}

		case ComProtocol::PROTOCOL_BROADCAST_KIND:

		case ComProtocol::PROTOCOL_UNDEFINED_KIND:
		default:
		{
			if( inCount == 0 )
			{
				return( false );
			}
			break;
		}
	}

//	return( (outCount == 1) && (inCount > 0) &&
//			aConnector.sizeOutputMachinePort() == (1 + inCount) );

//	return( (aConnector.sizeOutputMachinePort()
//			+ aConnector.sizeInputMachinePort()) == count );

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION
////////////////////////////////////////////////////////////////////////////////

void RdvConfigurationData::toStream(OutStream & os) const
{
//	os << std::endl;
	os << REPEAT("----------", 10) << std::endl;
	os << "UsedMachineFlag    :> " << mUsedMachineFlag << std::endl;
	os << "AwaitingInput      :> " << mAwaitingInputRdvFlag << std::endl;
	os << "AwaitingOutput     :> " << mAwaitingOutputRdvFlag << std::endl;

	os << "AwaitingMulti      :> " << mAwaitingMultiRdvFlag << std::endl;
	os << "AwaitingInputMulti :> " << mAwaitingInputMultiRdvFlag << std::endl;
	os << "AwaitingOutpuMulti :> " << mAwaitingOutputMultiRdvFlag << std::endl;

	os << "Performed RDV ?    :> " << hasPerformedRdvFlag << std::endl;
	os << "Internal RDV ?     :> " << hasPossibleInternalRdvFlag << std::endl;
	os << "Internal MULTI ?   :> " << hasPossibleInternalMultiRdvFlag << std::endl;

	for( std::size_t idx = 0 ; idx < mMachineCount ; ++idx )
	{
		if( IN_ED_RDV[ idx ].nonempty() || OUT_ED_RDV[ idx ].nonempty() ||
				ED_MULTIRDV[ idx ].nonempty() || RDVS[ idx ].nonempty() )
		{
			os << REPEAT("----------", 10) << std::endl;
		}

//		os << "free :> " << mFreeOffsetFlag[idx] << std::endl;

		os << INCR_INDENT;
		if( IN_ED_RDV[ idx ].nonempty() )
		{
			os << "INPUTS_RDV[ " << idx << " ] :>" << EOL;
			print_trace(IN_ED_RDV[ idx ], os);
		}

		if( OUT_ED_RDV[ idx ].nonempty() )
		{
			os << "OUTPUTS_RDV[ " << idx << " ] :>" << EOL;
			print_trace(OUT_ED_RDV[ idx ], os);
		}

		if( ED_MULTIRDV[ idx ].nonempty() )
		{
			os << "ED_MULTIRDV[ " << idx << " ] :>" << EOL;
			print_trace(ED_MULTIRDV[ idx ], os);
		}

		if( RDVS[ idx ].nonempty() )
		{
			os << "RDVS[ " << idx << " ] :>" << EOL;
			print_trace(RDVS[ idx ], os);
		}
	}

	if( mAwaitingMultiRdvFlag.any() )
	{
		os << REPEAT("----------", 10) << std::endl;
		os << "AWAITING_MULTI_RDV :>" << EOL;
		print_trace(mAwaitingMultiRdvEDS, os);
	}

	os << DECR_INDENT;


	os << REPEAT("==========", 10) << std::endl;

}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// the RESUME RDV statement
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
///// GLOBAL EFFECTIVE RDV COUNT
////////////////////////////////////////////////////////////////////////////////

std::size_t AvmCommunicationRdvPrimitive::GLOBAL_EFFECTIVE_RDV_COUNT = 0;

std::size_t AvmCommunicationRdvPrimitive::GLOBAL_EFFECTIVE_MULTI_RDV_COUNT = 0;


void AvmCommunicationRdvPrimitive::reportGlobalStatistics(OutStream & os)
{
	if( GLOBAL_EFFECTIVE_RDV_COUNT > 0 )
	{
		os << EOL_TAB2 << "Effective RDV : " << GLOBAL_EFFECTIVE_RDV_COUNT;

		if( GLOBAL_EFFECTIVE_MULTI_RDV_COUNT > 0 )
		{
			os << "  &  MULTI_RDV : " << GLOBAL_EFFECTIVE_MULTI_RDV_COUNT;
		}
		os << EOL;
	}
	else if( GLOBAL_EFFECTIVE_MULTI_RDV_COUNT > 0 )
	{
		os << EOL_TAB2 << "Effective MULTI_RDV : "
				<< GLOBAL_EFFECTIVE_MULTI_RDV_COUNT
				<< EOL;
	}
}

/**
 * COMPUTE ALL RDV
 */
bool AvmCommunicationRdvPrimitive::computeRdv(
		AvmPrimitiveProcessor & aProcessor,
		std::vector< ExecutionEnvironment > & tabOfENV)
{
	return( false );
}


/**
 * the RESUME RDV instruction
 */

bool AvmCommunicationRdvPrimitive::haveRDV(ExecutionData & outED,
		ExecutionData & inED)
{
	if( inED.getExecSyncPoint()->mRoutingData.getConnector().isTEQ(
			outED.getExecSyncPoint()->mRoutingData.getConnector() ) )
	{
		return( inED.getExecSyncPoint()->mMessage.needSender(
				outED.getExecSyncPoint()->mMessage.getSenderRID()) );
	}

	return( false );
}

static bool isAddRvdConf(RdvConfigurationData * aRdvConf,
		std::size_t idx, ExecutionData & anED)
{
	if( anED.getExecSyncPoint()->mRoutingData.getConnector().isTEQ(
			aRdvConf->mConnector ) )
	{
		bool returnFlag = true;

		switch( anED.getExecSyncPoint()->mAwaitingPointNature )
		{
			case AWAITING_POINT_OUTPUT_NATURE:
			{
				switch( anED.getExecSyncPoint()->mRoutingData.
						getConnector().getOutputProtocolCast() )
				{
					case ComProtocol::PROTOCOL_UNICAST_KIND:
					{
						if( aRdvConf->mAwaitingOutputMultiRdvFlag[idx] )
						{
							aRdvConf->mAwaitingOutputMultiRdvFlag[idx] = false;
							returnFlag = aRdvConf->mAwaitingOutputMultiRdvFlag.none();
							aRdvConf->mAwaitingOutputMultiRdvFlag[idx] = true;
						}
						else
						{
							returnFlag = aRdvConf->mAwaitingOutputMultiRdvFlag.none();
						}
						break;
					}
					default:
					{
						// NOTHING
						break;
					}
				}
				break;
			}
			case AWAITING_POINT_INPUT_NATURE:
			{
				switch( anED.getExecSyncPoint()->mRoutingData.
						getConnector().getInputProtocolCast() )
				{
					case ComProtocol::PROTOCOL_UNICAST_KIND:
					{
						if( aRdvConf->mAwaitingInputMultiRdvFlag[idx] )
						{
							aRdvConf->mAwaitingInputMultiRdvFlag[idx] = false;
							returnFlag = aRdvConf->mAwaitingInputMultiRdvFlag.none();
							aRdvConf->mAwaitingInputMultiRdvFlag[idx] = true;
						}
						else
						{
							returnFlag = aRdvConf->mAwaitingInputMultiRdvFlag.none();
						}
						break;
					}
					default:
					{
						// NOTHING
						break;
					}
				}
				break;
			}
			default:
			{
				// NOTHING
				break;
			}
		}
		return returnFlag;
	}

	return false;
}



static void addRvdConf(bool isInitial,
		ListOfRdvConfigurationData & multiRdvConf,
		RdvConfigurationData * refRdvConf,
		std::size_t idx, ListOfExecutionData & theED)
{
	ListOfExecutionData::iterator itED;
	ListOfExecutionData::iterator endED = theED.end();

	std::size_t edx;
	std::size_t edCount = theED.size();
	Bitset isnotFound(edCount, true);

	RdvConfigurationData * aRdvConf = nullptr;

	ListOfRdvConfigurationData::iterator itConf = multiRdvConf.begin();
	ListOfRdvConfigurationData::iterator endConf = multiRdvConf.end();
	for( ; itConf != endConf ; ++itConf )
	{
//		AVM_OS_TRACE << REPEAT("++++++++++", 10) << std::endl;
//		AVM_OS_TRACE << REPEAT("++++++++++", 10) << std::endl;
//		(*itConf)->toStream(AVM_OS_TRACE);

		for( itED = theED.begin() , edx = 0 ; itED != endED ; ++itED , ++edx)
		{
//			AVM_OS_TRACE << ":=> ";
//			print_trace(*itED, AVM_OS_TRACE, "");

			if( isAddRvdConf(*itConf, idx, *itED) )
			{
				isnotFound[edx] = false;

				aRdvConf = (*itConf);
				if( aRdvConf->mAwaitingMultiRdvEDS[idx].valid() )
				{
					multiRdvConf.insert(itConf , aRdvConf =
							new RdvConfigurationData(*aRdvConf));
				}
				aRdvConf->mAwaitingMultiRdvEDS [ idx ] = (*itED);
				aRdvConf->mAwaitingMultiRdvFlag[ idx ] = true;

				aRdvConf->mAwaitingInputMultiRdvFlag [ idx ] =
						(*itED).getExecSyncPoint()->isInput();

				aRdvConf->mAwaitingOutputMultiRdvFlag[ idx ] =
						(*itED).getExecSyncPoint()->isOutput();
				aRdvConf->mUsedMachineFlag[ idx ] = true;

//				AVM_OS_TRACE << REPEAT("++++++++++", 10) << std::endl;
//				aRdvConf->toStream(AVM_OS_TRACE);
			}
			else if( isnotFound[edx] )
			{
				isnotFound[edx] = (*itED).getExecSyncPoint()->mRoutingData.
						getConnector().isNTEQ( (*itConf)->mConnector );
			}
		}
	}

	if( isnotFound.any() )
	{
		for( itED = theED.begin() , edx = 0 ; itED != endED ; ++itED , ++edx)
		{
			if( isnotFound[edx] )
			{
//				AVM_OS_TRACE << "|=> ";
//				print_trace(*itED, AVM_OS_TRACE, "");

				if( isInitial )
				{
					aRdvConf = new RdvConfigurationData(refRdvConf);
					aRdvConf->mConnector = &( (*itED).getExecSyncPoint()
							->mRoutingData.getConnector() );
				}
				else
				{
					aRdvConf = new RdvConfigurationData(*refRdvConf);

//					if( aRdvConf->mConnector !=
//						(*itED).getExecSyncPoint()->mRoutingData.getConnector() )
//					{
//						aRdvConf->mAwaitingMultiRdvFlag.reset();
//						for( std::size_t i = 0 ; i < aRdvConf->mMachineCount; ++i )
//						{
//							aRdvConf->mAwaitingMultiRdvEDS[ i ] = nullptr;
//						}
//					}
					aRdvConf->IN_ED_RDV[ idx ].clear();
					aRdvConf->OUT_ED_RDV[ idx ].clear();
					aRdvConf->ED_MULTIRDV[ idx ].clear();
				}

				multiRdvConf.append( aRdvConf );

				aRdvConf->mAwaitingMultiRdvEDS [ idx ] = (*itED);
				aRdvConf->mAwaitingMultiRdvFlag[ idx ] = true;

				aRdvConf->mAwaitingInputMultiRdvFlag [ idx ] =
						(*itED).getExecSyncPoint()->isInput();

				aRdvConf->mAwaitingOutputMultiRdvFlag[ idx ] =
						(*itED).getExecSyncPoint()->isOutput();

				aRdvConf->mUsedMachineFlag[ idx ] = true;

//				AVM_OS_TRACE << REPEAT("++++++++++", 10) << std::endl;
//				aRdvConf->toStream(AVM_OS_TRACE);
			}
		}
	}
}


bool AvmCommunicationRdvPrimitive::resume_rdv(ListOfExecutionData & aRDV)
{
	// TRACE
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
	AVM_OS_TRACE << "==> BEGIN" << std::endl;
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
	mBaseRdvConf.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	mEffectiveRdvCount = 0;
	mEffectiveMultiRdvCount = 0;

	if( computeAllRdv() )
	{
		aRDV.splice( RDV );

		GLOBAL_EFFECTIVE_RDV_COUNT += mEffectiveRdvCount;
		GLOBAL_EFFECTIVE_MULTI_RDV_COUNT += mEffectiveMultiRdvCount;

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
	AVM_OS_TRACE << "==> END :> count";
	if( checkRdvFlag )
	{
		AVM_OS_TRACE << " : RDV[ " << mEffectiveRdvCount << " ]";
	}
	if( checkMultiRdvFlag )
	{
		AVM_OS_TRACE << " : MULTI_RDV[ " << mEffectiveMultiRdvCount << " ]";
	}
	AVM_OS_TRACE << " !!!" << std::endl;
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

		return( true );
	}

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
	AVM_OS_TRACE << "==> END :> RDV count : ZERO !!!" << std::endl;
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	return( false );
}



bool AvmCommunicationRdvPrimitive::computeAllRdv()
{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << "==> CHECK IN INITIAL" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	// Check INITIAL RDV
	if( checkRdvFlag )
	{
		if( not checkInternalRdv(true, &mBaseRdvConf) )
		{
			// TODO ERREUR
		}
	}

	// Check INITIAL MULTI RDV
	if( checkMultiRdvFlag )
	{
		if( not checkInternalMultiRDV(true, &mBaseRdvConf) )
		{
			// TODO ERREUR
		}
	}

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_INFO << "flag:>  Rdv = " << checkRdvFlag << "  MultiRdv  = "
			<< checkMultiRdvFlag << std::endl
			<< "init:>  Rdv = " << mEffectiveRdvCount << "  MultiRdv  = "
			<< mEffectiveMultiRdvCount << std::endl
			<< "NEXT_RDV_CONF:> " << NEXT_RDV_CONF.size() << std::endl
			<< "conf:> " << InstanceCounter<
					RdvConfigurationData >::INSTANCE_ALIVE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )


	while( NEXT_RDV_CONF.nonempty() )
	{
		CURRENT_RDV_CONF.splice( NEXT_RDV_CONF );

		if( not completeAllRdv() )
		{
			// TODO ERREUR
		}

		PREVIOUS_RDV_CONF.splice( CURRENT_RDV_CONF );

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_INFO << "while:> Rdv = " << mEffectiveRdvCount << "  MultiRdv  = "
			<< mEffectiveMultiRdvCount << std::endl
			<< "NEXT_RDV_CONF:> " << NEXT_RDV_CONF.size() << std::endl
			<< "conf:> " << InstanceCounter<
					RdvConfigurationData >::INSTANCE_ALIVE << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	}

	return( RDV.nonempty() );
}


bool AvmCommunicationRdvPrimitive::completeAllRdv()
{
	ListOfRdvConfigurationData::iterator itRdvConf;
	ListOfRdvConfigurationData::iterator endItCurrentRdvConf = CURRENT_RDV_CONF.end();

	ListOfRdvConfigurationData::iterator itRdvConf2;
	ListOfRdvConfigurationData::iterator endItPreviousRdvConf2 = PREVIOUS_RDV_CONF.end();

	itRdvConf = CURRENT_RDV_CONF.begin();
	for( ; itRdvConf != endItCurrentRdvConf ; ++ itRdvConf )
	{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << std::endl
			<< "completeAllRdv ==> BEGIN CHECKING :>" << std::endl;

	(*itRdvConf)->toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

		if( (*itRdvConf)->hasPerformedRdvFlag  )
		{

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << "==> CHECK IN INTERNAL" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

			// CHECK for INTERNAL RDV in CURRENT CONF
			if( (*itRdvConf)->hasPossibleInternalRdvFlag )
			{
				if( not checkInternalRdv(false, (*itRdvConf)) )
				{
					// TODO ERREUR
				}
			}

			// Check internal MULTI_RDV
			if( (*itRdvConf)->hasPossibleInternalMultiRdvFlag )
			{
				if( not checkInternalMultiRDV(false, *itRdvConf) )
				{
					// TODO ERREUR
				}
			}


AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << "==> CHECK WITH INITIAL" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

			// CHECK for RDV with INITIAL CONF
			if( checkRdvFlag
				&& ((*itRdvConf)->mAwaitingInputRdvFlag.any()
					|| (*itRdvConf)->mAwaitingOutputRdvFlag.any())
				&& (((*itRdvConf)->mAwaitingInputRdvFlag ^
						mBaseRdvConf.mAwaitingOutputRdvFlag).any()
					|| (mBaseRdvConf.mAwaitingInputRdvFlag ^
						(*itRdvConf)->mAwaitingOutputRdvFlag).any()) )
			{
				if( not checkWithInitialRdv(*itRdvConf) )
				{
					// TODO ERREUR
				}
			}

			if( checkMultiRdvFlag
				&& (*itRdvConf)->mAwaitingMultiRdvFlag.any()
				&& ((mBaseRdvConf.mAwaitingOutputRdvFlag.any()
						&& ((*itRdvConf)->mAwaitingMultiRdvFlag ^
							mBaseRdvConf.mAwaitingOutputRdvFlag).any())
					|| (mBaseRdvConf.mAwaitingInputRdvFlag.any()
						&& ((*itRdvConf)->mAwaitingMultiRdvFlag ^
							mBaseRdvConf.mAwaitingInputRdvFlag).any())) )
			{
				if( not checkWithInitialMultiRdv(*itRdvConf) )
				{
					// TODO ERREUR
				}
			}
		}

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << "==> CHECK WITH EXTERNAL" << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

		// CHECK for RDV between CURRENT CONF
		itRdvConf2 = CURRENT_RDV_CONF.begin();
		for( ; itRdvConf2 != endItCurrentRdvConf ; ++ itRdvConf2 )
		{
			if( itRdvConf != itRdvConf2 )
			{
				if( checkRdvFlag
					&& (*itRdvConf)->hasPossibleExternalRdv(*itRdvConf2) )
				{
					if( not checkWithExternalRdv((*itRdvConf), (*itRdvConf2)) )
					{
						// TODO ERREUR
					}
				}

				if( checkMultiRdvFlag && (*itRdvConf)->mAwaitingMultiRdvFlag.any()
					&& (*itRdvConf)->hasPossibleExternalMultiRdv(*itRdvConf2) )
				{
					if( not checkWithExternalMultiRdv((*itRdvConf), (*itRdvConf2)) )
					{
						// TODO ERREUR
					}
				}
			}
		}

		// CHECK for RDV with PREVIOUS CONF
		itRdvConf2 = PREVIOUS_RDV_CONF.begin();
		for( ; itRdvConf2 != endItPreviousRdvConf2 ; ++ itRdvConf2 )
		{
			if( itRdvConf != itRdvConf2 )
			{
				if( checkRdvFlag && (*itRdvConf)->hasPossibleExternalRdv(*itRdvConf2) )
				{
					if( not checkWithExternalRdv((*itRdvConf), (*itRdvConf2)) )
					{
						// TODO ERREUR
					}
				}

				if( checkMultiRdvFlag && (*itRdvConf)->mAwaitingMultiRdvFlag.any()
						&& (*itRdvConf)->hasPossibleExternalMultiRdv(*itRdvConf2) )
				{
					if( not checkWithExternalMultiRdv((*itRdvConf), (*itRdvConf2)) )
					{
						// TODO ERREUR
					}
				}
			}
		}
	}

	return( true );
}



bool AvmCommunicationRdvPrimitive::checkInternalRdv(
		bool isInitial, RdvConfigurationData * aRdvConf)
{
	ListOfExecutionData::iterator itOutED;
	ListOfExecutionData::iterator endOutED;

	ListOfExecutionData::iterator itInED;
	ListOfExecutionData::iterator endInED;

	RdvConfigurationData * newRdvConf = nullptr;

	for( std::size_t outIdx = 0 ; outIdx < aRdvConf->mMachineCount; ++outIdx )
	{
		if( aRdvConf->OUT_ED_RDV[ outIdx ].empty() )
		{
			continue;
		}

		itOutED = aRdvConf->OUT_ED_RDV[ outIdx ].begin();
		endOutED = aRdvConf->OUT_ED_RDV[ outIdx ].end();
		for( ; itOutED != endOutED ; ++itOutED )
		{
			for( std::size_t inIdx = 0 ; inIdx < aRdvConf->mMachineCount ; ++inIdx )
			{
				if( (inIdx == outIdx) || aRdvConf->IN_ED_RDV[ inIdx ].empty() )
				{
					continue;
				}

				itInED = aRdvConf->IN_ED_RDV[ inIdx ].begin();
				endInED = aRdvConf->IN_ED_RDV[ inIdx ].end();
				for( ; itInED != endInED ; ++itInED )
				{
					if( haveRDV((*itOutED), (*itInED)) )
					{
						if( isInitial )
						{
							newRdvConf = new RdvConfigurationData( aRdvConf );

							newRdvConf->mUsedMachineFlag[ outIdx ] = true;
							newRdvConf->mUsedMachineFlag[ inIdx  ] = true;
						}
						else
						{
							newRdvConf = new RdvConfigurationData( *aRdvConf );

							newRdvConf->IN_ED_RDV[ inIdx ].clear();
							newRdvConf->OUT_ED_RDV[ outIdx ].clear();

							newRdvConf->ED_MULTIRDV[ inIdx ].clear();
						}

						newRdvConf->mAwaitingInputRdvFlag[ outIdx ] = false;
						newRdvConf->mAwaitingOutputRdvFlag[ inIdx ] = false;

//						newRdvConf->updatePossibleInternalRdvFlag();
//						newRdvConf->updatePossibleInternalMultiRdvFlag();

						if( compute_rdv(newRdvConf,
								outIdx, (*itOutED), inIdx, (*itInED)) )
						{
							complete_rdv(newRdvConf);
						}
						else
						{
							// TODO ERREUR
							delete( newRdvConf );
							newRdvConf = nullptr;
						}
					}
				}
			}
		}
	}

	return( true );
}


bool AvmCommunicationRdvPrimitive::checkInternalMultiRDV(
		bool isInitial, RdvConfigurationData * aRdvConf)
{
	ListOfRdvConfigurationData multiRdvConf;

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_INFO << "checkInternalMultiRDV:> "
			<< InstanceCounter< RdvConfigurationData >::INSTANCE_ALIVE
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	for( std::size_t idx = 0 ; idx < aRdvConf->mMachineCount; ++idx )
	{
		addRvdConf(isInitial, multiRdvConf,
				aRdvConf, idx, aRdvConf->ED_MULTIRDV[idx]);

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_INFO << "checkInternalMultiRDV:" << idx << "> "
			<< InstanceCounter< RdvConfigurationData >::INSTANCE_ALIVE
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	}

	if( not compute_multirdv(multiRdvConf) )
	{
		// TODO ERREUR
	}

	return( true );
}




bool AvmCommunicationRdvPrimitive::checkWithInitialRdv(
		RdvConfigurationData * aRdvConf)
{
	ListOfExecutionData::iterator itInED;
	ListOfExecutionData::iterator endInED;

	ListOfExecutionData::iterator itOutED;
	ListOfExecutionData::iterator endOutED;

	RdvConfigurationData * newRdvConf = nullptr;

	std::size_t outIdx = 0;
	std::size_t inIdx = 0;

	////////////////////////////////////////////////////////////////////////////
	// COMPLETE OUTPUT WITH INITIAL INPUT
	////////////////////////////////////////////////////////////////////////////
	if( aRdvConf->mAwaitingInputRdvFlag.any()
		&& mBaseRdvConf.mAwaitingOutputRdvFlag.any() )
	{
		for( inIdx = 0 ; inIdx < aRdvConf->mMachineCount ; ++inIdx )
		{
			if( mBaseRdvConf.IN_ED_RDV[ inIdx ].empty()
				|| aRdvConf->mUsedMachineFlag[ inIdx ] )
			{
				continue;
			}

			itInED = mBaseRdvConf.IN_ED_RDV[ inIdx ].begin();
			endInED = mBaseRdvConf.IN_ED_RDV[ inIdx ].end();
			for( ; itInED != endInED ; ++itInED )
			{
				for( outIdx = 0 ; (outIdx < aRdvConf->mMachineCount) ; ++outIdx )
				{
					if( (inIdx == outIdx)
						|| aRdvConf->OUT_ED_RDV[ outIdx ].empty() )
					{
						continue;
					}

					itOutED = aRdvConf->OUT_ED_RDV[ outIdx ].begin();
					endOutED = aRdvConf->OUT_ED_RDV[ outIdx ].end();
					for( ; itOutED != endOutED ; ++itOutED )
					{
						if( haveRDV((*itOutED), (*itInED)) )
						{
							newRdvConf = new RdvConfigurationData( *aRdvConf );

							newRdvConf->IN_ED_RDV[ inIdx ].clear();
							newRdvConf->OUT_ED_RDV[ outIdx ].clear();
							newRdvConf->ED_MULTIRDV[ inIdx ].clear();

							newRdvConf->mAwaitingInputRdvFlag[ outIdx ] = false;
							newRdvConf->mAwaitingOutputRdvFlag[ inIdx ] = false;

							newRdvConf->mUsedMachineFlag[ inIdx  ] = true;

							if( compute_rdv(newRdvConf,
									outIdx, (*itOutED), inIdx, (*itInED)) )
							{
								complete_rdv(newRdvConf);
							}
							else
							{
								// TODO ERREUR
								delete( newRdvConf );
								newRdvConf = nullptr;
							}
						}
					}
				}
			}
		}
	}

	////////////////////////////////////////////////////////////////////////////
	// COMPLETE INPUT WITH INITIAL OUTPUT
	////////////////////////////////////////////////////////////////////////////
	if( aRdvConf->mAwaitingOutputRdvFlag.any()
		&& mBaseRdvConf.mAwaitingInputRdvFlag.any())
	{
		for( outIdx = 0 ; (outIdx < aRdvConf->mMachineCount) ; ++outIdx )
		{
			if( mBaseRdvConf.OUT_ED_RDV[ outIdx ].empty()
				|| aRdvConf->mUsedMachineFlag[ outIdx ] )
			{
				continue;
			}

			itOutED = mBaseRdvConf.OUT_ED_RDV[ outIdx ].begin();
			endOutED = mBaseRdvConf.OUT_ED_RDV[ outIdx ].end();
			for( ; itOutED != endOutED ; ++itOutED )
			{
				for( inIdx = 0 ; inIdx < aRdvConf->mMachineCount ; ++inIdx )
				{
					if( (inIdx == outIdx) || aRdvConf->IN_ED_RDV[ inIdx ].empty() )
					{
						continue;
					}

					itInED = aRdvConf->IN_ED_RDV[ inIdx ].begin();
					endInED = aRdvConf->IN_ED_RDV[ inIdx ].end();
					for( ; itInED != endInED ; ++itInED )
					{
						if( haveRDV((*itOutED), (*itInED)) )
						{
							newRdvConf = new RdvConfigurationData( *aRdvConf );

							newRdvConf->IN_ED_RDV[ inIdx ].clear();
							newRdvConf->OUT_ED_RDV[ outIdx ].clear();
							newRdvConf->ED_MULTIRDV[ inIdx ].clear();

							newRdvConf->mAwaitingInputRdvFlag[ outIdx ] = false;
							newRdvConf->mAwaitingOutputRdvFlag[ inIdx ] = false;

							newRdvConf->mUsedMachineFlag[ outIdx ] = true;

							if( not compute_rdv(newRdvConf,
									outIdx, (*itOutED), inIdx, (*itInED)) )
							{
								// TODO ERREUR
							}

							complete_rdv(newRdvConf);
						}
					}
				}
			}
		}
	}

	return( true );
}


bool AvmCommunicationRdvPrimitive::checkWithInitialMultiRdv(
		RdvConfigurationData * aRdvConf)
{
	ListOfRdvConfigurationData multiRdvConf;

//	((*itRdvConf)->mAwaitingMultiRdvFlag ^ mBaseRdvConf.mAwaitingOutputRdvFlag).any() ||
//	((*itRdvConf)->mAwaitingMultiRdvFlag ^ mBaseRdvConf.mAwaitingInputRdvFlag).any()

	for( std::size_t idx = 0 ; idx < aRdvConf->mMachineCount; ++idx )
	{
		if( not aRdvConf->mAwaitingMultiRdvFlag[ idx ] )
		{
			addRvdConf(false, multiRdvConf,
					aRdvConf, idx, mBaseRdvConf.ED_MULTIRDV[idx]);
		}
	}

	if( not compute_multirdv(multiRdvConf) )
	{
		// TODO ERREUR
	}

	return( true );
}



bool AvmCommunicationRdvPrimitive::checkWithExternalRdv(
		RdvConfigurationData * aRdvConf, RdvConfigurationData * otherRdvConf)
{
	ListOfExecutionData::iterator itInED;
	ListOfExecutionData::iterator endInED;

	ListOfExecutionData::iterator itOutED;
	ListOfExecutionData::iterator endOutED;

	RdvConfigurationData * newRdvConf = nullptr;

	std::size_t outIdx = 0;
	std::size_t inIdx = 0;

	////////////////////////////////////////////////////////////////////////////
	// COMPLETE OUTPUT WITH OTHER INCOMPLETE RDV_CONF INPUT
	////////////////////////////////////////////////////////////////////////////
	if( aRdvConf->mAwaitingInputRdvFlag.any()
		&& otherRdvConf->mAwaitingOutputRdvFlag.any())
	{
		for( outIdx = 0 ; outIdx < aRdvConf->mMachineCount ; ++outIdx )
		{
			if( otherRdvConf->IN_ED_RDV[ inIdx ].empty()
				|| aRdvConf->mUsedMachineFlag[ inIdx ] )
			{
				continue;
			}

			itInED = otherRdvConf->IN_ED_RDV[ inIdx ].begin();
			endInED = otherRdvConf->IN_ED_RDV[ inIdx ].end();
			for( ; itInED != endInED ; ++itInED )
			{
				for( outIdx = 0 ; (outIdx < aRdvConf->mMachineCount) ; ++outIdx )
				{
					if( (inIdx == outIdx) || aRdvConf->OUT_ED_RDV[ outIdx ].empty() )
					{
						continue;
					}

					itOutED = aRdvConf->OUT_ED_RDV[ outIdx ].begin();
					endOutED = aRdvConf->OUT_ED_RDV[ outIdx ].end();
					for( ; itOutED != endOutED ; ++itOutED )
					{
						if( haveRDV((*itOutED), (*itInED)) )
						{
							newRdvConf = aRdvConf->fusion( otherRdvConf );

							newRdvConf->IN_ED_RDV[ inIdx ].clear();
							newRdvConf->OUT_ED_RDV[ outIdx ].clear();
							newRdvConf->ED_MULTIRDV[ inIdx ].clear();

							newRdvConf->mAwaitingInputRdvFlag[ outIdx ] = false;
							newRdvConf->mAwaitingOutputRdvFlag[ inIdx ] = false;

							newRdvConf->mUsedMachineFlag[ inIdx ] = true;

							if( compute_rdv(newRdvConf,
									outIdx, (*itOutED), inIdx, (*itInED)) )
							{
								complete_rdv(newRdvConf);
							}
							else
							{
								// TODO ERREUR
								delete( newRdvConf );
								newRdvConf = nullptr;
							}
						}
					}
				}
			}
		}
	}

	////////////////////////////////////////////////////////////////////////////
	// COMPLETE INPUT WITH OTHER INCOMPLETE RDV_CONF OUTPUT
	////////////////////////////////////////////////////////////////////////////
	if( aRdvConf->mAwaitingOutputRdvFlag.any()
		&& otherRdvConf->mAwaitingInputRdvFlag.any())
	{
		for( outIdx = 0 ; (outIdx < aRdvConf->mMachineCount) ; ++outIdx )
		{
			if( otherRdvConf->OUT_ED_RDV[ outIdx ].empty()
				|| aRdvConf->mUsedMachineFlag[ outIdx ] )
			{
				continue;
			}

			itOutED = otherRdvConf->OUT_ED_RDV[ outIdx ].begin();
			endOutED = otherRdvConf->OUT_ED_RDV[ outIdx ].end();
			for( ; itOutED != endOutED ; ++itOutED )
			{
				if( not (*itOutED).getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					continue;
				}

				for( inIdx = 0 ; inIdx < aRdvConf->mMachineCount ; ++inIdx )
				{
					if( (inIdx == outIdx) || aRdvConf->IN_ED_RDV[ inIdx ].empty() )
					{
						continue;
					}

					itInED = aRdvConf->IN_ED_RDV[ inIdx ].begin();
					endInED = aRdvConf->IN_ED_RDV[ inIdx ].end();
					for( ; itInED != endInED ; ++itInED )
					{
						if( haveRDV((*itOutED), (*itInED)) )
						{
							newRdvConf = aRdvConf->fusion( otherRdvConf );

							newRdvConf->IN_ED_RDV[ inIdx ].clear();
							newRdvConf->OUT_ED_RDV[ outIdx ].clear();
							newRdvConf->ED_MULTIRDV[ inIdx ].clear();

							newRdvConf->mAwaitingInputRdvFlag[ outIdx ] = false;
							newRdvConf->mAwaitingOutputRdvFlag[ inIdx ] = false;

							newRdvConf->mUsedMachineFlag[ outIdx ] = true;

							if( not compute_rdv(newRdvConf,
									outIdx, (*itOutED), inIdx, (*itInED)) )
							{
								// TODO ERREUR
							}

							complete_rdv(newRdvConf);
						}
					}
				}
			}
		}
	}

	return( true );
}


bool AvmCommunicationRdvPrimitive::checkWithExternalMultiRdv(
		RdvConfigurationData * aRdvConf,
		RdvConfigurationData * otherRdvConf)
{
	VectorOfExecutionData::iterator itED;
	VectorOfExecutionData::iterator endED;

	ListOfExecutionData::iterator endioED;

	ListOfRdvConfigurationData multiRdvConf;

	for( std::size_t idx = 0 ; idx < aRdvConf->mMachineCount; ++idx )
	{
		if( not otherRdvConf->mAwaitingMultiRdvFlag[ idx ] )
		{
			if( aRdvConf->mAwaitingMultiRdvFlag.any() )
			{
				ListOfExecutionData listED;

				itED = aRdvConf->mAwaitingMultiRdvEDS.begin();
				endED = aRdvConf->mAwaitingMultiRdvEDS.end();
				for( ; itED != endED ; ++itED )
				{
					if( (*itED).valid() )
					{
						listED.append( *itED );
					}
				}
				addRvdConf(false, multiRdvConf, otherRdvConf, idx, listED);

			}
			addRvdConf(false, multiRdvConf,
					otherRdvConf, idx, aRdvConf->ED_MULTIRDV[idx]);
		}
}

	if( not compute_multirdv(multiRdvConf) )
	{
		// TODO ERREUR
	}

	return( true );
}




bool AvmCommunicationRdvPrimitive::resume_rdv(ExecutionEnvironment & ENV,
		RdvConfigurationData * aRdvConf, avm_offset_t offset)
{
	if( not resume_rdv(ENV) )
	{
		return( false );
	}

	ExecutionData tmpED;

	while( ENV.outEDS.nonempty() )
	{
		ENV.outEDS.pop_last_to( tmpED );

		switch( tmpED.getAEES() )
		{
			case AEES_OK:
			case AEES_STMNT_NOTHING:
			case AEES_STMNT_RETURN:
			{
				aRdvConf->RDVS[ offset ].append( tmpED );
				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as outEDS :> "
						<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}

	while( ENV.exitEDS.nonempty() )
	{
		ENV.exitEDS.pop_last_to( tmpED );

		switch( tmpED.getAEES() )
		{
			case AEES_STMNT_EXIT:
			case AEES_STMNT_EXIT_ALL:
			case AEES_STMNT_FATAL_ERROR:
			case AEES_SYMBOLIC_EXECUTION_LIMITATION:
			{
				aRdvConf->RDVS[ offset ].append( tmpED );
				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as exitEDS :> "
						<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}

	while( ENV.syncEDS.nonempty() )
	{
		ENV.syncEDS.pop_last_to( tmpED );

		switch( tmpED.getAEES() )
		{
			case AEES_WAITING_INCOM_RDV:
			{
				if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					aRdvConf->IN_ED_RDV[ offset ].append( tmpED );
					aRdvConf->mAwaitingOutputRdvFlag[ offset ] = true;
				}
				else if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf->ED_MULTIRDV[ offset ].append( tmpED );
					aRdvConf->mAwaitingOutputMultiRdvFlag[ offset ] = true;
				}
				break;
			}

			case AEES_WAITING_OUTCOM_RDV:
			{
				if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolRDV() )
				{
					aRdvConf->OUT_ED_RDV[ offset ].append( tmpED );
					aRdvConf->mAwaitingInputRdvFlag[ offset ] = true;
				}
				else if( tmpED.getExecSyncPoint()->mRoutingData.isProtocolMULTI_RDV() )
				{
					aRdvConf->ED_MULTIRDV[ offset ].append( tmpED );
					aRdvConf->mAwaitingInputMultiRdvFlag[ offset ] = true;
				}
				break;
			}


			case AEES_WAITING_JOIN_FORK:
			{
				aRdvConf->RDVS[ offset ].append( tmpED );
				break;
			}

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ENDIND EXECUTION STATUS as syncEDS :> "
						<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}

	aRdvConf->hasPerformedRdvFlag = true;

	return( true );
}



bool AvmCommunicationRdvPrimitive::compute_rdv(RdvConfigurationData * aRdvConf,
		avm_offset_t outOffset, ExecutionData & outED,
		avm_offset_t inOffset, ExecutionData & inED)
{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << std::endl << "Checking RDV :>"
			<< "  Rdv = " << mEffectiveRdvCount
			<< "  MultiRdv  = " << mEffectiveMultiRdvCount
			<< "  conf =  "
			<< InstanceCounter< RdvConfigurationData >::INSTANCE_ALIVE
			<< std::endl;
	aRdvConf->toStream( AVM_OS_TRACE );
	outED.printExecSyncPointTrace( AVM_OS_TRACE );
	inED.printExecSyncPointTrace( AVM_OS_TRACE );
	AVM_OS_TRACE << REPEAT("__________", 10) << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	////////////////////////////////////////////////////////////////////////////
	// INPUT RDV
	////////////////////////////////////////////////////////////////////////////
	ExecutionEnvironment inENV(aRdvConf->ENV, inED);

	BFCode aTraceInput(OperatorManager::OPERATOR_INPUT_RDV,
			inED.getExecSyncPoint()->mMessage.bfPort());

	BFCode aTraceOutput(OperatorManager::OPERATOR_OUTPUT_RDV,
			outED.getExecSyncPoint()->mMessage.bfPort());

	Message::const_iterator itVar =
			inED.getExecSyncPoint()->mMessage.beginParameters();
	Message::const_iterator endVar =
			inED.getExecSyncPoint()->mMessage.endParameters();
	Message::const_iterator itValue =
			outED.getExecSyncPoint()->mMessage.beginParameters();

	for( ; itVar != endVar ; ++itVar , ++itValue )
	{
		inENV.inED.mwsetAEES( AEES_OK );
		if( not inENV.setRvalue((*itVar).to< InstanceOfData >(), (*itValue)) )
		{
			return( false );
		}

		aTraceInput->append( *itValue );
		aTraceOutput->append( *itValue );
	}

	ExecutionDataFactory::appendIOElementTrace(inENV.inED,
			BF( new ExecutionConfiguration(inENV.inED.getRID(),
					aTraceInput, outED.getExecSyncPoint()->mMessage,
					outED.getTimeValue(outED.getRID()) ) ) );


	if( not resume_rdv(inENV, aRdvConf, inOffset) )
	{
		return( false );
	}

	////////////////////////////////////////////////////////////////////////////
	// OUTPUT RDV
	////////////////////////////////////////////////////////////////////////////
	ExecutionEnvironment outENV(aRdvConf->ENV, outED);

	ExecutionDataFactory::appendIOElementTrace(outENV.inED,
			BF( new ExecutionConfiguration(outENV.inED.getRID(),
					aTraceOutput, outED.getExecSyncPoint()->mMessage,
					outED.getTimeValue(outED.getRID()) ) ) );

	if( not resume_rdv(outENV, aRdvConf, outOffset) )
	{
		return( false );
	}


	updatePossibleInternalRdvFlags(aRdvConf);

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	// TRACE
	aRdvConf->toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	return( true );
}


bool AvmCommunicationRdvPrimitive::compute_multirdv(
		ListOfRdvConfigurationData & multiRdvConf)
{
	RdvConfigurationData * aRdvConf = nullptr;

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_INFO << "compute_multirdv:b> "
			<< InstanceCounter< RdvConfigurationData >::INSTANCE_ALIVE
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	while( multiRdvConf.nonempty() )
	{
		multiRdvConf.pop_first_to( aRdvConf );
//		aRdvConf->updatePossibleInternalRdvFlag();
//		aRdvConf->updatePossibleInternalMultiRdvFlag();

		if( aRdvConf->isMultiRdvComplete() )
		{
			if( not compute_multirdv(aRdvConf) )
			{
				delete( aRdvConf );
				aRdvConf = nullptr;

				continue;
				// TODO ERREUR
			}
		}

		complete_rdv(aRdvConf, true);
	}

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_INFO << "compute_multirdv:e> "
			<< InstanceCounter< RdvConfigurationData >::INSTANCE_ALIVE
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	return( true );
}

bool AvmCommunicationRdvPrimitive::compute_multirdv(
		RdvConfigurationData * aRdvConf)
{
AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	AVM_OS_TRACE << std::endl << "Checking MULTI_RDV :>"
			<< "  Rdv = " << mEffectiveRdvCount
			<< "  MultiRdv  = " << mEffectiveMultiRdvCount
			<< "  conf =  "
			<< InstanceCounter< RdvConfigurationData >::INSTANCE_ALIVE
			<< std::endl;
	aRdvConf->toStream( AVM_OS_TRACE );
	print_trace(aRdvConf->mAwaitingMultiRdvEDS, AVM_OS_TRACE);
	AVM_OS_TRACE << REPEAT("__________", 10) << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	Message anOutputMsg;
	Message anInputMsg;
	BFCode aTraceIO;

	Message::const_iterator itVar;
	Message::const_iterator endVar;
	Message::const_iterator itValue;

	////////////////////////////////////////////////////////////////////////////
	// OUTPUT RDV
	////////////////////////////////////////////////////////////////////////////
	for( std::size_t idx = 0 ; idx < aRdvConf->mMachineCount; ++idx )
	{
		if( aRdvConf->mAwaitingMultiRdvEDS[ idx ].invalid() )
		{
			continue;
		}
		if( aRdvConf->mAwaitingMultiRdvEDS[ idx ].getExecSyncPoint()->isInput() )
		{
			continue;
		}
		aRdvConf->mAwaitingMultiRdvFlag[ idx ] = false;
		aRdvConf->mAwaitingInputMultiRdvFlag[ idx ] = false;

		ExecutionEnvironment outENV(
				aRdvConf->ENV, aRdvConf->mAwaitingMultiRdvEDS[ idx ]);
		aRdvConf->mAwaitingMultiRdvEDS[ idx ].destroy();

		anOutputMsg = outENV.inED.getExecSyncPoint()->mMessage;

		aTraceIO = StatementConstructor::newCode(
				OperatorManager::OPERATOR_OUTPUT_RDV, anOutputMsg.bfPort());

		aTraceIO->append( anOutputMsg.getParameters() );

		ExecutionDataFactory::appendIOElementTrace(outENV.inED,
				BF( new ExecutionConfiguration(
						outENV.inED.getRID(), aTraceIO, anOutputMsg,
						outENV.inED.getTimeValue(outENV.inED.getRID()) ) ) );

		if( not resume_rdv(outENV, aRdvConf, idx) )
		{
			return( false );
		}

		if( anOutputMsg.hasParameter() )
		{
			break; // Only one sender with values on MULTI RDV
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// INPUT RDV
	////////////////////////////////////////////////////////////////////////////

	for( std::size_t idx = 0 ; idx < aRdvConf->mMachineCount; ++idx )
	{
		if( aRdvConf->mAwaitingMultiRdvEDS[ idx ].invalid() )
		{
			continue;
		}
		if( aRdvConf->mAwaitingMultiRdvEDS[ idx ].getExecSyncPoint()->isOutput() )
		{
			continue;
		}

		aRdvConf->mAwaitingMultiRdvFlag[ idx ] = false;
		aRdvConf->mAwaitingOutputMultiRdvFlag[ idx ] = false;

		ExecutionEnvironment inENV(
				aRdvConf->ENV, aRdvConf->mAwaitingMultiRdvEDS[ idx ]);
		aRdvConf->mAwaitingMultiRdvEDS[ idx ].destroy();

		anInputMsg = inENV.inED.getExecSyncPoint()->mMessage;

		aTraceIO = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT_RDV, anInputMsg.bfPort());

		if( anOutputMsg.hasParameter() )
		{
			itVar = anInputMsg.beginParameters();
			endVar = anInputMsg.endParameters();
			itValue = anOutputMsg.beginParameters();
			for( ; itVar != endVar ; ++itVar , ++itValue )
			{
				aTraceIO->append( *itValue );

				inENV.inED.mwsetAEES( AEES_OK );
				if( not inENV.setRvalue(
						(*itVar).to< InstanceOfData >(), (*itValue)) )
				{
					return( false );
				}
			}
		}

		ExecutionDataFactory::appendIOElementTrace(inENV.inED,
				BF( new ExecutionConfiguration(
						inENV.inED.getRID(), aTraceIO, anInputMsg,
						inENV.inED.getTimeValue(inENV.inED.getRID()) ) ) );

		if( not resume_rdv(inENV, aRdvConf, idx) )
		{
			return( false );
		}
	}

	updatePossibleInternalRdvFlags(aRdvConf);

AVM_IF_DEBUG_FLAG( STATEMENT_COMMUNICATION )
	// TRACE
	aRdvConf->toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( STATEMENT_COMMUNICATION )

	return( true );
}


void AvmCommunicationRdvPrimitive::complete_rdv(
		RdvConfigurationData * & aRdvConf, bool isMulti)
{
	if( aRdvConf->isComplete() )
	{
		if( not completed_rdv(aRdvConf, isMulti) )
		{
			// TODO ERREUR
		}

		delete( aRdvConf );
		aRdvConf = nullptr;
	}
	else
	{
		NEXT_RDV_CONF.append( aRdvConf );
	}
}


bool AvmCommunicationRdvPrimitive::completed_rdv(
		RdvConfigurationData * aRdvConf, bool isMulti)
{
	ListOfExecutionData tmpListOfED;
	ExecutionData tmpED;

	ListOfExecutionData::iterator itED;
	ListOfExecutionData::iterator endItED;

	ListOfExecutionData fusionListOfED;
	ExecutionData anED;

	std::size_t idx = 0;

	for( idx = 0 ; idx < aRdvConf->mMachineCount; ++idx )
	{
		if( aRdvConf->RDVS[ idx ].nonempty() )
		{
			tmpListOfED.splice( aRdvConf->RDVS[ idx ] );
			break;
		}
	}

	for( ++idx ; idx < aRdvConf->mMachineCount; ++idx )
	{
		if( aRdvConf->RDVS[ idx ].nonempty() )
		{
			while( tmpListOfED.nonempty() )
			{
				tmpListOfED.pop_last_to( tmpED );

				itED = aRdvConf->RDVS[ idx ].begin();
				endItED = aRdvConf->RDVS[ idx ].end();
				for( ; itED != endItED ; ++itED )
				{
					anED = AvmSynchronizationFactory::fusion(
							aRdvConf->ENV.inED, tmpED, (*itED));
					if( anED.valid() )
					{
						fusionListOfED.append( anED );
					}
				}

			}

			tmpListOfED.splice(fusionListOfED);
		}
	}

	if( isMulti )
	{
		mEffectiveMultiRdvCount += tmpListOfED.size();
	}
	else
	{
		mEffectiveRdvCount += tmpListOfED.size();
	}
	RDV.splice( tmpListOfED );

	return( true );
}



bool  AvmCommunicationRdvPrimitive::resume_rdv(ExecutionEnvironment & tmpENV)
{
	tmpENV.inED.mwsetAEES( AEES_STEP_RESUME );

	tmpENV.inED.destroyExecSyncPoint();

	tmpENV.inED.pushExecutionLocationhCache();

	if( tmpENV.decode_resume() )
	{
		return( tmpENV.hasOutputSyncIrq() );
	}
	else
	{
		return( false );
	}
}





}
