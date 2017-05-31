/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 févr. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXECUTIONENVIRONMENT_H_
#define EXECUTIONENVIRONMENT_H_

#include <computer/BaseEnvironment.h>

#include <common/AvmPointer.h>

#include <computer/primitive/AvmPrimitiveProcessor.h>

#include <fml/expression/AvmCode.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionLocation.h>
#include <fml/runtime/RuntimeDef.h>


namespace sep
{

class EvaluationEnvironment;
class AvmPrimitiveProcessor;

class RuntimeID;


class ExecutionEnvironment :
		public BaseEnvironment ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionEnvironment )
{

public :
	/**
	 * ATTRIBUTES
	 */
	////////////////////////////////////////////////////////////////////////////
	// INPUTs
	////////////////////////////////////////////////////////////////////////////
	BF saveEXEC_LOCATION;
	ExecutionLocation * inEXEC_LOCATION;


	////////////////////////////////////////////////////////////////////////////
	// OUTPUTs
	////////////////////////////////////////////////////////////////////////////
	ListOfAPExecutionData outEDS;


	////////////////////////////////////////////////////////////////////////////
	// SYNC Execution Data
	////////////////////////////////////////////////////////////////////////////
	ListOfAPExecutionData syncEDS;

	////////////////////////////////////////////////////////////////////////////
	// INTERRUPT REQUEST Execution Data
	////////////////////////////////////////////////////////////////////////////
	ListOfAPExecutionData irqEDS;

	////////////////////////////////////////////////////////////////////////////
	// INTERRUPT REQUEST Execution Data
	////////////////////////////////////////////////////////////////////////////
	ListOfAPExecutionData exitEDS;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionEnvironment(AvmPrimitiveProcessor & aPrimitiveProcessor)
	: BaseEnvironment( aPrimitiveProcessor ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}

	ExecutionEnvironment(AvmPrimitiveProcessor & aPrimitiveProcessor,
			const ExecutionContext * aParentEC)
	: BaseEnvironment( aPrimitiveProcessor , aParentEC ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}


	/**
	* CONSTRUCTOR
	* Copy
	*/
	explicit ExecutionEnvironment(const ExecutionEnvironment & form)
	: BaseEnvironment( form ),
	saveEXEC_LOCATION( form.saveEXEC_LOCATION ),
	inEXEC_LOCATION( form.inEXEC_LOCATION ),
	outEDS( form.outEDS ),
	syncEDS( form.syncEDS ),
	irqEDS( form.irqEDS ),
	exitEDS( form.exitEDS )
	{
		//!! NOTHING
	}


	ExecutionEnvironment(const BaseEnvironment & form, const BF & bf)
	: BaseEnvironment( form , bf ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}

	ExecutionEnvironment(const BaseEnvironment & form, const BFCode & aCode)
	: BaseEnvironment( form , aCode ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}

	ExecutionEnvironment(const BaseEnvironment & form,
			const RuntimeID & aRID, const BFCode & aCode)
	: BaseEnvironment( form , aRID , aCode ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}


	ExecutionEnvironment(const BaseEnvironment & form,
			const APExecutionData & anED)
	: BaseEnvironment( form , anED ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}


	ExecutionEnvironment(const BaseEnvironment & form,
			const APExecutionData & anED, const BF & bf)
	: BaseEnvironment( form , anED , bf ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}

	ExecutionEnvironment(const BaseEnvironment & form,
			const APExecutionData & anED, const BFCode & aCode)
	: BaseEnvironment( form , anED , aCode ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}


	ExecutionEnvironment(const BaseEnvironment & form,
			const APExecutionData & anED, const RuntimeID & aRID,
			const BFCode & aCode)
	: BaseEnvironment( form , anED , aRID , aCode ),
	saveEXEC_LOCATION( ),
	inEXEC_LOCATION( NULL ),
	outEDS( ),
	syncEDS( ),
	irqEDS( ),
	exitEDS( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionEnvironment()
	{
		//!! NOTHING
	}


	/**
	 * DESTROY OUTPUTS
	 */
	inline void destroyOutED()
	{
		outEDS.clear();
	}


	////////////////////////////////////////////////////////////////////////////
	///// the OUTPUT management
	////////////////////////////////////////////////////////////////////////////

	inline void appendOutput(const APExecutionData & anED)
	{
		outEDS.append(anED);
	}

	void appendOutput(EvaluationEnvironment & ENV);


	inline virtual bool hasOutput() const
	{
		return( outEDS.nonempty() );
	}

	inline virtual bool hasntOutput() const
	{
		return( outEDS.empty() );
	}

	bool extractOtherOutputED(const APExecutionData & anED,
			ListOfAPExecutionData & listEDS);


	/**
	 * appendOutput
	 * w.r.t. AVM_EXEC_ENDING_STATUS
	 */
	void appendOutput_wrtAEES(APExecutionData & anED);


	/**
	 * appendOutput
	 * mwset PROCESS_EVAL_STATE
	 */
	inline bool appendOutput_mwsetPES(APExecutionData & anED,
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES)
	{
		anED.mwsetRuntimeFormState(aRID, aPES);

		outEDS.append( anED );

		return( true );
	}


	/**
	 * appendOutput
	 * mwset PROCESS_EVAL_STATE
	 * mwset AVM_EXEC_ENDING_STATUS
	 */
	bool mwsetPES_mwsetAEES(APExecutionData & anED,
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES);

	bool appendOutput_mwsetPES_mwsetAEES(APExecutionData & anED,
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES);

	bool appendOutput_mwsetPES_mwsetAEES(ExecutionEnvironment & ENV,
			const RuntimeID & aRID, PROCESS_EVAL_STATE aPES);


	bool appendOutput_mwsetPES_mwsetAEES(APExecutionData & anED,
			const RuntimeID & aRID,
			PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES);

	bool appendOutput_mwsetPES_mwsetAEES(ExecutionEnvironment & ENV,
			const RuntimeID & aRID,
			PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES);


	bool appendOutput_mwsetPES_mwsetAEES_mwsetRID(APExecutionData & anED,
			const RuntimeID & currentRID, const RuntimeID & nextRID,
			PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES);

	bool appendOutput_mwsetPES_mwsetAEES_mwsetRID(ExecutionEnvironment & ENV,
			const RuntimeID & currentRID, const RuntimeID & nextRID,
			PROCESS_EVAL_STATE oldPES, PROCESS_EVAL_STATE aPES);

	/**
	 * splice
	 * OUTPUT ExecutionData
	 */

	inline void spliceOutput(ExecutionEnvironment & ENV)
	{
		outEDS.splice( ENV.outEDS );

		spliceNotOutput( ENV );
	}

	inline void spliceNotOutput(ExecutionEnvironment & ENV)
	{
		spliceExit( ENV );
		spliceIrq( ENV );
		spliceFailure( ENV );
		spliceSync( ENV );
	}

	inline void spliceNotOutputExit(ExecutionEnvironment & ENV)
	{
		spliceIrq( ENV );
		spliceFailure( ENV );
		spliceSync( ENV );
	}



	////////////////////////////////////////////////////////////////////////////
	///// the SYNC management
	////////////////////////////////////////////////////////////////////////////
	/**
	 * GETTER - SETTER
	 * SYNC EDS
	 */
	inline void appendSync(const APExecutionData & anED)
	{
		syncEDS.append(anED);
	}

	inline void spliceSync(ExecutionEnvironment & ENV)
	{
		syncEDS.splice( ENV.syncEDS );
	}

	inline bool hasSync() const
	{
		return( syncEDS.nonempty() );
	}

	inline bool isSync() const
	{
		return( hasntOutput() && syncEDS.nonempty() );
	}


	/**
	 * appendOutput
	 * mwset PROCESS_EVAL_STATE
	 */
	inline bool appendSync_mwsetAEES(APExecutionData & anED,
			AVM_EXEC_ENDING_STATUS anAEES)
	{
		anED.mwsetAEES(anAEES);

		syncEDS.append( anED );

		return( true );
	}


	/**
	 * append SYNC
	 * w.r.t. AVM_EXEC_ENDING_STATUS
	 *
	 * case AEES_STEP_MARK:
	 * case AEES_WAITING_INCOM_RDV:
	 * case AEES_WAITING_OUTCOM_RDV:
	 * case AEES_WAITING_JOIN_FORK:
	 *
	 * store statement position
	 */
	inline bool appendSync_mwStorePos(APExecutionData anED)
	{
		anED.makeWritable();
		anED->mSTATEMENT_QUEUE.push(anED->mRID, inCODE);

		syncEDS.append( anED );

		return( true );
	}

	inline bool appendSync_mwStorePos(APExecutionData anED,
			const AvmCode::const_iterator & it,
			const AvmCode::const_iterator & endIt)
	{
		anED.makeWritable();
		anED->mSTATEMENT_QUEUE.push(anED->mRID, inCODE, it, endIt);

		syncEDS.append( anED );

		return( true );
	}


	/**
	 * splice SYNC
	 * w.r.t. AVM_EXEC_ENDING_STATUS
	 *
	 * case AEES_STEP_MARK:
	 * case AEES_WAITING_INCOM_RDV:
	 * case AEES_WAITING_OUTCOM_RDV:
	 * case AEES_WAITING_JOIN_FORK:
	 *
	 * store statement position
	 */
	inline void spliceSync_mwStorePos(ExecutionEnvironment & ENV)
	{
		while( ENV.syncEDS.nonempty() )
		{
			appendSync_mwStorePos( ENV.syncEDS.pop_first() );
		}
	}

	inline void spliceSync_mwStorePos(ExecutionEnvironment & ENV,
			const AvmCode::const_iterator & it,
			const AvmCode::const_iterator & endIt)
	{
		while( ENV.syncEDS.nonempty() )
		{
			appendSync_mwStorePos(ENV.syncEDS.pop_first(), it, endIt);
		}
	}



	////////////////////////////////////////////////////////////////////////////
	///// the IRQ management
	////////////////////////////////////////////////////////////////////////////
	/**
	 * GETTER - SETTER
	 * INTERRUPT REQUEST EDS
	 */
	inline void appendIrq(const APExecutionData & anED)
	{
		irqEDS.append(anED);
	}

	inline void spliceIrq(ExecutionEnvironment & ENV)
	{
		irqEDS.splice( ENV.irqEDS );
	}

	inline bool hasIrq() const
	{
		return( irqEDS.nonempty() );
	}

	inline bool hasntIrq() const
	{
		return( irqEDS.empty() );
	}

	inline bool isIrq() const
	{
		return( hasntOutput() && irqEDS.nonempty() );
	}


	/**
	 * appendOutput
	 * mwset PROCESS_EVAL_STATE
	 */
	inline bool appendIrq_mwsetAEES(APExecutionData & anED,
			AVM_EXEC_ENDING_STATUS anAEES)
	{
		anED.mwsetAEES(anAEES);

		irqEDS.append( anED );

		return( true );
	}



	////////////////////////////////////////////////////////////////////////////
	///// the EXIT management
	////////////////////////////////////////////////////////////////////////////
	/**
	 * GETTER - SETTER
	 * EXIT REQUEST EDS
	 */
	inline void appendExit(const APExecutionData & anED)
	{
		exitEDS.append(anED);
	}

	inline void spliceExit(ExecutionEnvironment & ENV)
	{
		exitEDS.splice( ENV.exitEDS );
	}

	inline bool hasExit() const
	{
		return( exitEDS.nonempty() );
	}

	inline bool hasntExit() const
	{
		return( exitEDS.empty() );
	}

	inline bool isExit() const
	{
		return( hasntOutput() && exitEDS.nonempty() );
	}


	/**
	 * appendOutput
	 * mwset PROCESS_EVAL_STATE
	 */
	inline bool appendExit_mwsetAEES(APExecutionData & anED,
			AVM_EXEC_ENDING_STATUS anAEES)
	{
		anED.mwsetAEES(anAEES);

		exitEDS.append( anED );

		return( true );
	}



	////////////////////////////////////////////////////////////////////////////
	///// ALL OUTPUT ED management
	////////////////////////////////////////////////////////////////////////////

	inline bool hasSyncIrq() const
	{
		return( syncEDS.nonempty() || irqEDS.nonempty() );
	}


	inline bool hasOutputSyncIrq() const
	{
		return( outEDS.nonempty() || syncEDS.nonempty() || irqEDS.nonempty() );
	}

	inline bool hasntOutputSyncIrq() const
	{
		return( outEDS.empty() && syncEDS.empty() && irqEDS.empty() );
	}


	inline bool hasNoneOutput() const
	{
		return( outEDS.empty() && syncEDS.empty() &&
				irqEDS.empty() && failureEDS.empty() );
	}


	////////////////////////////////////////////////////////////////////////////
	///// the RUN statement
	////////////////////////////////////////////////////////////////////////////

	inline bool run()
	{
		return( PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) );
	}

	inline bool run(PROCESS_EVAL_STATE aPES)
	{
		inED.mwsetRuntimeFormState(aPES);

		return( PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) );
	}

	inline bool run(Operator * op, const BFCode & aCode)
	{
		inFORM = inCODE = aCode;

		return( PRIMITIVE_PROCESSOR.run(op->getOffset(), *this) );
	}

	inline bool run(const BFCode & aCode)
	{
		inFORM = inCODE = aCode;

		return( PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) );
	}


	inline bool run(const BF & bf)
	{
		inFORM = inCODE = bf.bfCode();

		return( PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) );
	}

	inline bool run(APExecutionData & anED, const BFCode & aCode)
	{
		inEC = anED->getExecutionContext();

		inED = anED;

		inFORM = inCODE = aCode;

		return( PRIMITIVE_PROCESSOR.run(inCODE->getOpOffset(), *this) );
	}

	bool run(ListOfAPExecutionData & inEDS, const BFCode & aCode);


	////////////////////////////////////////////////////////////////////////////
	///// run from OUT EDS
	////////////////////////////////////////////////////////////////////////////

	bool runFromOutputs(const BFCode & aCode);

	bool runFromOutputs(Operator * op, const BFCode & aCode);



	////////////////////////////////////////////////////////////////////////////
	///// the RESUME statement
	////////////////////////////////////////////////////////////////////////////

	bool resume(ExecutionEnvironment & ENV, APExecutionData & anED);

	inline bool decode_resume()
	{
		return( PRIMITIVE_PROCESSOR.decode_resume(*this) );
	}


	////////////////////////////////////////////////////////////////////////////
	///// the RESTORE CONTEXT
	////////////////////////////////////////////////////////////////////////////
	inline void restoreContext(const RuntimeID & aRID)
	{
		ListOfAPExecutionData::iterator itED = outEDS.begin();
		ListOfAPExecutionData::iterator endED = outEDS.end();
		for( ; itED != endED ; ++itED )
		{
			(*itED)->mRID = aRID;
		}
	}



	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;


	///////////////////////////////////////////////////////////////////////////
	// CACHE MANAGER
	///////////////////////////////////////////////////////////////////////////

	struct _EXEC_ENV_
	{
		////////////////////////////////////////////////////////////////////////
		// INPUTs
		////////////////////////////////////////////////////////////////////////
		AvmPrimitiveProcessor * PRIMITIVE_PROCESSOR;

		const ExecutionContext * inEC;

		BF inFORM;

		BFCode inCODE;

		APExecutionData inED;


		////////////////////////////////////////////////////////////////////////
		// ARGS ENV
		////////////////////////////////////////////////////////////////////////

		ARGS_ENV * arg;


		////////////////////////////////////////////////////////////////////////
		// OUTPUTs
		////////////////////////////////////////////////////////////////////////
		ListOfAPExecutionData outEDS;


		////////////////////////////////////////////////////////////////////////
		// SYNC Execution Data
		////////////////////////////////////////////////////////////////////////
		ListOfAPExecutionData syncEDS;

		////////////////////////////////////////////////////////////////////////
		// INTERRUPT REQUEST Execution Data
		////////////////////////////////////////////////////////////////////////
		ListOfAPExecutionData irqEDS;

		////////////////////////////////////////////////////////////////////////
		// INTERRUPT REQUEST Execution Data
		////////////////////////////////////////////////////////////////////////
		ListOfAPExecutionData exitEDS;

		////////////////////////////////////////////////////////////////////////
		// FAILED Execution Data
		////////////////////////////////////////////////////////////////////////

		ListOfAPExecutionData failureEDS;

	};

	/**
	 * CACHE
	 */
	static List< _EXEC_ENV_ * >  EXEC_ENV_CACHE;

	static void initENVS();

	static void finalizeENVS();


	inline static _EXEC_ENV_ * newENV();

	inline static void freeENV(_EXEC_ENV_ * & exec_env);


};







}

#endif /* EXECUTIONENVIRONMENT_H_ */
