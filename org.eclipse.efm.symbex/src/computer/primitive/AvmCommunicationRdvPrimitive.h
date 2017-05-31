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

#ifndef AVMCOMMUNICATIONRDVPRIMITIVE_H_
#define AVMCOMMUNICATIONRDVPRIMITIVE_H_

#include <common/AvmObject.h>

#include <collection/Bitset.h>

#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{

class ExecutionEnvironment;
class InstanceOfConnect;
class OutStream;


class RdvConfigurationData :
		public AvmObject,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( RdvConfigurationData )
{

public:
	/**
	 * ATTRIBUTES
	 */
	ExecutionEnvironment & ENV;

	avm_size_t mMachineCount;

	VectorOfListOfAPExecutionData IN_ED_RDV;
	VectorOfListOfAPExecutionData OUT_ED_RDV;

	VectorOfListOfAPExecutionData ED_MULTIRDV;

	VectorOfListOfAPExecutionData RDVS;
	bool hasPerformedRdvFlag;

	Bitset mUsedMachineFlag;

	Bitset mAwaitingInputRdvFlag;
	Bitset mAwaitingOutputRdvFlag;

	Bitset mAwaitingMultiRdvFlag;
	Bitset mAwaitingInputMultiRdvFlag;
	Bitset mAwaitingOutputMultiRdvFlag;

	InstanceOfConnect * mConnector;
	VectorOfAPExecutionData mAwaitingMultiRdvEDS;

	bool hasPossibleInternalRdvFlag;
	bool hasPossibleInternalMultiRdvFlag;


public:
	RdvConfigurationData(ExecutionEnvironment & aENV, avm_size_t machineCount)
	: AvmObject(),
	ENV( aENV ),
	mMachineCount( machineCount ),

	IN_ED_RDV( mMachineCount ),
	OUT_ED_RDV( mMachineCount ),

	ED_MULTIRDV( mMachineCount ),

	RDVS( mMachineCount ),
	hasPerformedRdvFlag( false ),

	mUsedMachineFlag( mMachineCount , false ),

	mAwaitingInputRdvFlag( mMachineCount , false ),
	mAwaitingOutputRdvFlag( mMachineCount , false  ),

	mAwaitingMultiRdvFlag( mMachineCount , false ),
	mAwaitingInputMultiRdvFlag( mMachineCount , false ),
	mAwaitingOutputMultiRdvFlag( mMachineCount , false ),

	mConnector( NULL ),
	mAwaitingMultiRdvEDS( mMachineCount ),

	hasPossibleInternalRdvFlag( false ),
	hasPossibleInternalMultiRdvFlag( false )
	{
		//!! NOTHING
	}


	RdvConfigurationData(RdvConfigurationData * aRdvConf)
	: AvmObject(),
	ENV( aRdvConf->ENV ),
	mMachineCount( aRdvConf->mMachineCount ),

	IN_ED_RDV( mMachineCount ),
	OUT_ED_RDV( mMachineCount ),

	ED_MULTIRDV( mMachineCount ),

	RDVS( mMachineCount ),
	hasPerformedRdvFlag( false ),

	mUsedMachineFlag( mMachineCount , false ),

	mAwaitingInputRdvFlag( mMachineCount , false ),
	mAwaitingOutputRdvFlag( mMachineCount , false  ),

	mAwaitingMultiRdvFlag( mMachineCount , false ),
	mAwaitingInputMultiRdvFlag( mMachineCount , false ),
	mAwaitingOutputMultiRdvFlag( mMachineCount , false ),

	mConnector( NULL ),
	mAwaitingMultiRdvEDS( mMachineCount ),

	hasPossibleInternalRdvFlag( false ),
	hasPossibleInternalMultiRdvFlag( false )
	{
		//!! NOTHING
	}


	RdvConfigurationData(const RdvConfigurationData & aRdvConfData)
	: AvmObject( aRdvConfData ),
	ENV( aRdvConfData.ENV ),
	mMachineCount( aRdvConfData.mMachineCount ),

	IN_ED_RDV( aRdvConfData.IN_ED_RDV ),
	OUT_ED_RDV( aRdvConfData.OUT_ED_RDV ),

	ED_MULTIRDV( aRdvConfData.ED_MULTIRDV ),

	RDVS( aRdvConfData.RDVS ),
	hasPerformedRdvFlag( aRdvConfData.hasPerformedRdvFlag ),

	mUsedMachineFlag( aRdvConfData.mUsedMachineFlag ),

	mAwaitingInputRdvFlag( aRdvConfData.mAwaitingInputRdvFlag ),
	mAwaitingOutputRdvFlag( aRdvConfData.mAwaitingOutputRdvFlag ),

	mAwaitingMultiRdvFlag( aRdvConfData.mAwaitingMultiRdvFlag ),
	mAwaitingInputMultiRdvFlag( aRdvConfData.mAwaitingInputMultiRdvFlag ),
	mAwaitingOutputMultiRdvFlag( aRdvConfData.mAwaitingOutputMultiRdvFlag ),

	mConnector( aRdvConfData.mConnector ),
	mAwaitingMultiRdvEDS( aRdvConfData.mAwaitingMultiRdvEDS ),

	hasPossibleInternalRdvFlag( aRdvConfData.hasPossibleInternalRdvFlag ),
	hasPossibleInternalMultiRdvFlag(
			aRdvConfData.hasPossibleInternalMultiRdvFlag )
	{
		//!! NOTHING
	}


	RdvConfigurationData(const RdvConfigurationData & aRdvConfData,
			RdvConfigurationData * aRdvConf)
	: AvmObject( aRdvConfData ),
	ENV( aRdvConfData.ENV ),
	mMachineCount( aRdvConfData.mMachineCount ),

	IN_ED_RDV( aRdvConfData.IN_ED_RDV ),
	OUT_ED_RDV( aRdvConfData.OUT_ED_RDV ),

	ED_MULTIRDV( aRdvConfData.ED_MULTIRDV ),

	RDVS( aRdvConfData.RDVS ),
	hasPerformedRdvFlag(
			aRdvConfData.hasPerformedRdvFlag
			| aRdvConf->hasPerformedRdvFlag ),

	mUsedMachineFlag(
			aRdvConfData.mAwaitingInputRdvFlag
			| aRdvConf->mAwaitingInputRdvFlag ),

	mAwaitingInputRdvFlag(
			aRdvConfData.mAwaitingInputRdvFlag
			| aRdvConf->mAwaitingInputRdvFlag ),

	mAwaitingOutputRdvFlag(
			aRdvConfData.mAwaitingOutputRdvFlag
			| aRdvConf->mAwaitingOutputRdvFlag ),

	mAwaitingMultiRdvFlag(
			aRdvConfData.mAwaitingMultiRdvFlag
			| aRdvConf->mAwaitingMultiRdvFlag ),

	mAwaitingInputMultiRdvFlag(
			aRdvConfData.mAwaitingInputMultiRdvFlag
			| aRdvConf->mAwaitingInputMultiRdvFlag ),

	mAwaitingOutputMultiRdvFlag(
			aRdvConfData.mAwaitingOutputMultiRdvFlag
			| aRdvConf->mAwaitingOutputMultiRdvFlag ),

	mConnector( aRdvConfData.mConnector ),
	mAwaitingMultiRdvEDS( aRdvConfData.mAwaitingMultiRdvEDS ),

	hasPossibleInternalRdvFlag( false ),
	hasPossibleInternalMultiRdvFlag( false )
	{
		updatePossibleInternalRdvFlag();
		updatePossibleInternalMultiRdvFlag();
	}


	virtual ~RdvConfigurationData()
	{
		//!! NOTHING
	}


	RdvConfigurationData * fusion(RdvConfigurationData * aRdvConf);

	void resize(avm_size_t newSize);


	inline bool isComplete()
	{
		return( mAwaitingInputRdvFlag.none()
				&& mAwaitingOutputRdvFlag.none()
				&& mAwaitingMultiRdvFlag.none() );
	}

	inline void updatePossibleInternalRdvFlag()
	{
		hasPossibleInternalRdvFlag =
				( mAwaitingInputRdvFlag.any() && mAwaitingOutputRdvFlag.any() );
	}

	inline void updatePossibleInternalMultiRdvFlag()
	{
		hasPossibleInternalMultiRdvFlag =
				( mAwaitingInputMultiRdvFlag.any()
						|| mAwaitingOutputMultiRdvFlag.any() );
	}


	inline bool hasPossibleExternalRdv(RdvConfigurationData * aRdvConf)
	{
		return( (hasPerformedRdvFlag
					|| aRdvConf->hasPerformedRdvFlag)
				&& (mUsedMachineFlag & aRdvConf->mUsedMachineFlag).none()
				&& ( (mAwaitingInputRdvFlag.any()
						&& aRdvConf->mAwaitingOutputRdvFlag.any())
					|| (aRdvConf->mAwaitingInputRdvFlag.any()
						&& mAwaitingOutputRdvFlag.any()) ) );
	}


	inline bool hasPossibleExternalMultiRdv(RdvConfigurationData * aRdvConf)
	{
		return( (hasPerformedRdvFlag || aRdvConf->hasPerformedRdvFlag) &&
				(mUsedMachineFlag & aRdvConf->mUsedMachineFlag).none() );
	}


	bool isMultiRdvComplete();


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const;

};


////////////////////////////////////////////////////////////////////////////////
// TYPEDEF for COLLECTION
////////////////////////////////////////////////////////////////////////////////

DEFINE_LIST_PTR(RdvConfigurationData);

DEFINE_VECTOR_PTR(RdvConfigurationData);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////




class AvmCommunicationRdvPrimitive :  public BaseAvmPrimitive
{

protected:
	/**
	 * ATTRIBUTES
	 */
	RdvConfigurationData & mBaseRdvConf;

	bool checkRdvFlag;
	bool checkMultiRdvFlag;


	ListOfRdvConfigurationData PREVIOUS_RDV_CONF;
	ListOfRdvConfigurationData CURRENT_RDV_CONF;
	ListOfRdvConfigurationData NEXT_RDV_CONF;

	ListOfAPExecutionData RDV;

	avm_uint64_t mEffectiveRdvCount;
	avm_uint64_t mEffectiveMultiRdvCount;


public:
	AvmCommunicationRdvPrimitive(AvmPrimitiveProcessor & aProcessor,
			RdvConfigurationData & aRdvConf, bool checkRdv, bool checkMultiRdv)
	: BaseAvmPrimitive( aProcessor ),
	mBaseRdvConf( aRdvConf ),
	checkRdvFlag( checkRdv ),
	checkMultiRdvFlag( checkMultiRdv ),
	PREVIOUS_RDV_CONF( ),
	CURRENT_RDV_CONF( ),
	NEXT_RDV_CONF( ),
	RDV( ),

	mEffectiveRdvCount( 0 ),
	mEffectiveMultiRdvCount( 0 )
	{
		//!! NOTHING
	}


	virtual ~AvmCommunicationRdvPrimitive()
	{
		while( PREVIOUS_RDV_CONF.nonempty() )
		{
			delete( PREVIOUS_RDV_CONF.pop_last() );
		}

		while( CURRENT_RDV_CONF.nonempty() )
		{
			delete( CURRENT_RDV_CONF.pop_last() );
		}

		while( NEXT_RDV_CONF.nonempty() )
		{
			delete( NEXT_RDV_CONF.pop_last() );
		}
	}


	/**
	 * COMPUTE ALL RDV
	 */
	static bool computeRdv(AvmPrimitiveProcessor & aProcessor,
			std::vector< ExecutionEnvironment > & tabOfENV);

	/**
	 * the RESUME RDV instruction
	 */

	bool haveRDV(APExecutionData & outED, APExecutionData & inED);

	inline void updatePossibleInternalRdvFlags(RdvConfigurationData * aRdvConf)
	{
		if( checkRdvFlag )
		{
			aRdvConf->updatePossibleInternalRdvFlag();
		}
		if( checkMultiRdvFlag )
		{
			aRdvConf->updatePossibleInternalMultiRdvFlag();
		}
	}

	bool resume_rdv(ListOfAPExecutionData & aRDV);

	bool computeAllRdv();

	bool completeAllRdv();

	bool checkInternalRdv(bool isInitial, RdvConfigurationData * aRdvConf);
	bool checkInternalMultiRDV(bool isInitial, RdvConfigurationData * aRdvConf);

	bool checkWithInitialRdv(RdvConfigurationData * aRdvConf);
	bool checkWithInitialMultiRdv(RdvConfigurationData * aRdvConf);

	bool checkWithExternalRdv(RdvConfigurationData * aRdvConf,
			RdvConfigurationData * otherRdvConf);
	bool checkWithExternalMultiRdv(RdvConfigurationData * aRdvConf,
			RdvConfigurationData * otherRdvConf);


	bool compute_rdv(RdvConfigurationData * aRdvConf,
			avm_offset_t outOffset, APExecutionData & outED,
			avm_offset_t inOffset, APExecutionData & inED);

	bool compute_multirdv(ListOfRdvConfigurationData & multiRdvConf);
	bool compute_multirdv(RdvConfigurationData * aRdvConf);


	void complete_rdv(RdvConfigurationData * & aRdvConf, bool isMulti = false);
	void complete_multirdv(RdvConfigurationData * & aRdvConf);

	bool completed_rdv(RdvConfigurationData * aRdvConf, bool isMulti);


	bool resume_rdv(ExecutionEnvironment & ENV,
			RdvConfigurationData * aRdvConf, avm_offset_t offset);

	bool resume_rdv(ExecutionEnvironment & tmpENV);


	/**
	 * GLOBALS
	 */
	static avm_size_t GLOBAL_EFFECTIVE_RDV_COUNT;
	static avm_size_t GLOBAL_EFFECTIVE_MULTI_RDV_COUNT;

	static void reportGlobalStatistics(OutStream & os);

};



}

#endif /* AVMCOMMUNICATIONRDVPRIMITIVE_H_ */
