/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_BEHAVIORALPART_H_
#define FML_INFRASTRUCTURE_BEHAVIORALPART_H_

#include <fml/common/ObjectClassifier.h>
#include <fml/common/ObjectElement.h>

#include <collection/BFContainer.h>

#include <fml/expression/AvmCode.h>

#include <fml/operator/OperatorLib.h>

#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Transition.h>

#include <fml/workflow/WObject.h>


namespace sep
{

class Machine;


class BehavioralPart : public ObjectClassifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BehavioralPart )
{

	AVM_DECLARE_CLONABLE_CLASS( BehavioralPart )

public:
	/**
	 * TYPEDEF
	 */
	typedef TableOfBF_T< Transition >  TableOfTransition;

	typedef TableOfTransition::const_raw_iterator  const_transition_iterator;


	typedef TableOfBF_T< Routine >  TableOfRoutine;

	typedef TableOfRoutine::const_raw_iterator  const_routine_iterator;


protected:
	/**
	 * ATTRIBUTES
	 */
	TableOfTransition mOutgoingTransitions;

	TableOfTransition mIncomingTransitions;

	Routine onCreateRoutine;

	Routine onInitRoutine;
	Routine onFinalRoutine;

	Routine onReturnRoutine;

	Routine onStartRoutine;
	Routine onStopRoutine;

	Routine onIEnableRoutine;
	Routine onEnableRoutine;

	Routine onIDisableRoutine;
	Routine onDisableRoutine;

	Routine onIAbortRoutine;
	Routine onAbortRoutine;

	Routine onIRunRoutine;
	Routine onRunRoutine;
	Routine onRtcRoutine;

	Routine onConcurrencyRoutine;
	Routine onScheduleRoutine;

	Routine onSynchronizeRoutine;


	TableOfRoutine mRoutines;

	TableOfRoutine mAnonymousInnerRoutines;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BehavioralPart(ObjectElement * aContainer,
			const std::string & aNameID = "moe")
	: ObjectClassifier( CLASS_KIND_T( BehavioralPart ) , aContainer , aNameID ),
	mOutgoingTransitions( ),
	mIncomingTransitions( ),

	onCreateRoutine( *this , "create" ),
	onInitRoutine( *this , "init" ),
	onFinalRoutine( *this , "final" ),

	onReturnRoutine( *this , "return" ),

	onStartRoutine( *this , "start" ),
	onStopRoutine( *this , "stop" ),

	onIEnableRoutine( *this , "ienable" ),
	onEnableRoutine( *this , "enable" ),

	onIDisableRoutine( *this , "idisable" ),
	onDisableRoutine( *this , "disable" ),

	onIAbortRoutine( *this , "iabort" ),
	onAbortRoutine( *this , "abort" ),

	onIRunRoutine( *this , "irun" ),
	onRunRoutine( *this , "run" ),
	onRtcRoutine( *this , "rtc" ),

	onConcurrencyRoutine( *this , "concurrency"  ),
	onScheduleRoutine( *this , "schedule" ),

	onSynchronizeRoutine( *this , "synchronized" ),

	mRoutines( ),
	mAnonymousInnerRoutines( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BehavioralPart()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mOutgoingTransitions
	 */
	inline const TableOfTransition & getOutgoingTransitions() const
	{
		return( mOutgoingTransitions );
	}

	inline bool hasOutgoingTransition() const
	{
		return( mOutgoingTransitions.nonempty() );
	}

	inline void appendOutgoingTransition(const BF & aTransition)
	{
		mOutgoingTransitions.append( aTransition );
	}

	inline void saveOutgoingTransition(Transition * aTransition)
	{
		mOutgoingTransitions.append( BF(aTransition) );
	}

	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_transition_iterator outgoing_transition_begin() const
	{
		return( mOutgoingTransitions.begin() );
	}

	inline const_transition_iterator outgoing_transition_end() const
	{
		return( mOutgoingTransitions.end() );
	}


	/**
	 * GETTER - SETTER
	 * mTransitions
	 * Attention ! pas de SmartPointer pour cet attribut
	 * Problème de référence circulaire au << delete avec le model ARC >>
	 */
	inline const TableOfTransition & getIncomingTransitions() const
	{
		return( mIncomingTransitions );
	}

	inline bool hasIncomingTransition() const
	{
		return( mIncomingTransitions.nonempty() );
	}

	inline void appendIncomingTransition(const BF & aTransition)
	{
		mIncomingTransitions.append( aTransition );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_transition_iterator incoming_transition_begin() const
	{
		return( mIncomingTransitions.begin() );
	}

	inline const_transition_iterator incoming_transition_end() const
	{
		return( mIncomingTransitions.end() );
	}


	/**
	 * GETTER - SETTER
	 * onCreateRoutine
	 */
	inline Routine & getOnCreateRoutine()
	{
		return( onCreateRoutine );
	}

	inline const Routine & getOnCreateRoutine() const
	{
		return( onCreateRoutine );
	}

	inline const BFCode & getOnCreate() const
	{
		return( onCreateRoutine.getCode() );
	}

	inline bool hasOnCreate() const
	{
		return( onCreateRoutine.hasCode() );
	}

	inline void setOnCreate(const BFCode & aCode)
	{
		onCreateRoutine.setCode( aCode );
	}

	inline void seqOnCreate(const BFCode & aCode)
	{
		onCreateRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onInitRoutine
	 */
	inline Routine & getOnInitRoutine()
	{
		return( onInitRoutine );
	}

	inline const Routine & getOnInitRoutine() const
	{
		return( onInitRoutine );
	}

	inline const BFCode & getOnInit() const
	{
		return( onInitRoutine.getCode() );
	}

	inline bool hasOnInit() const
	{
		return( onInitRoutine.hasCode() );
	}

	inline void setOnInit(const BFCode & aCode)
	{
		onInitRoutine.setCode( aCode );
	}

	inline void seqOnInit(const BFCode & aCode)
	{
		onInitRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onFinalRoutine
	 */
	inline Routine & getOnFinalRoutine()
	{
		return( onFinalRoutine );
	}

	inline const Routine & getOnFinalRoutine() const
	{
		return( onFinalRoutine );
	}

	inline const BFCode & getOnFinal() const
	{
		return( onFinalRoutine.getCode() );
	}

	inline bool hasOnFinal() const
	{
		return( onFinalRoutine.hasCode() );
	}

	inline void setOnFinal(const BFCode & aCode)
	{
		onFinalRoutine.setCode( aCode );
	}

	inline void seqOnFinal(const BFCode & aCode)
	{
		onFinalRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onReturnRoutine
	 */
	inline Routine & getOnReturnRoutine()
	{
		return( onReturnRoutine );
	}

	inline const Routine & getOnReturnRoutine() const
	{
		return( onReturnRoutine );
	}

	inline const BFCode & getOnReturn() const
	{
		return( onReturnRoutine.getCode() );
	}

	inline bool hasOnReturn() const
	{
		return( onReturnRoutine.hasCode() );
	}

	inline void setOnReturn(const BFCode & aCode)
	{
		onReturnRoutine.setCode( aCode );
	}

	inline void seqOnReturn(const BFCode & aCode)
	{
		onReturnRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onStartRoutine
	 */
	inline Routine & getOnStartRoutine()
	{
		return( onStartRoutine );
	}

	inline const Routine & getOnStartRoutine() const
	{
		return( onStartRoutine );
	}

	inline const BFCode & getOnStart() const
	{
		return( onStartRoutine.getCode() );
	}

	inline bool hasOnStart() const
	{
		return( onStartRoutine.hasCode() );
	}

	inline void setOnStart(const BFCode & aCode)
	{
		onStartRoutine.setCode( aCode );
	}

	inline void seqOnStart(const BFCode & aCode)
	{
		onStartRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onStopRoutine
	 */
	inline Routine & getOnStopRoutine()
	{
		return( onStopRoutine );
	}

	inline const Routine & getOnStopRoutine() const
	{
		return( onStopRoutine );
	}

	inline const BFCode & getOnStop() const
	{
		return( onStopRoutine.getCode() );
	}

	inline bool hasOnStop() const
	{
		return( onStopRoutine.hasCode() );
	}

	inline void setOnStop(const BFCode & aCode)
	{
		onStopRoutine.setCode( aCode );
	}

	inline void seqOnStop(const BFCode & aCode)
	{
		onStopRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onEnableRoutine
	 */
	inline Routine & getOnEnableRoutine()
	{
		return( onEnableRoutine );
	}

	inline const Routine & getOnEnableRoutine() const
	{
		return( onEnableRoutine );
	}

	inline const BFCode & getOnEnable() const
	{
		return( onEnableRoutine.getCode() );
	}

	inline bool hasOnEnable() const
	{
		return( onEnableRoutine.hasCode() );
	}

	inline void setOnEnable(const BFCode & aCode)
	{
		onEnableRoutine.setCode( aCode );
	}

	inline void seqOnEnable(const BFCode & aCode)
	{
		onEnableRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onIEnableRoutine
	 */
	inline Routine & getOnIEnableRoutine()
	{
		return( onIEnableRoutine );
	}

	inline const Routine & getOnIEnableRoutine() const
	{
		return( onIEnableRoutine );
	}

	inline const BFCode & getOnIEnable() const
	{
		return( onIEnableRoutine.getCode() );
	}

	inline bool hasOnIEnable() const
	{
		return( onIEnableRoutine.hasCode() );
	}

	inline void setOnIEnable(const BFCode & aCode)
	{
		onIEnableRoutine.setCode( aCode );
	}

	inline void seqOnIEnable(const BFCode & aCode)
	{
		onIEnableRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onDisableRoutine
	 */
	inline Routine & getOnDisableRoutine()
	{
		return( onDisableRoutine );
	}

	inline const Routine & getOnDisableRoutine() const
	{
		return( onDisableRoutine );
	}

	inline const BFCode & getOnDisable() const
	{
		return( onDisableRoutine.getCode() );
	}

	inline bool hasOnDisable() const
	{
		return( onDisableRoutine.hasCode() );
	}

	inline void setOnDisable(const BFCode & aCode)
	{
		onDisableRoutine.setCode( aCode );
	}

	inline void seqOnDisable(const BFCode & aCode)
	{
		onDisableRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onIDisableRoutine
	 */
	inline Routine & getOnIDisableRoutine()
	{
		return( onIDisableRoutine );
	}

	inline const Routine & getOnIDisableRoutine() const
	{
		return( onIDisableRoutine );
	}

	inline const BFCode & getOnIDisable() const
	{
		return( onIDisableRoutine.getCode() );
	}

	inline bool hasOnIDisable() const
	{
		return( onIDisableRoutine.hasCode() );
	}

	inline void setOnIDisable(const BFCode & aCode)
	{
		onIDisableRoutine.setCode( aCode );
	}

	inline void seqOnIDisable(const BFCode & aCode)
	{
		onIDisableRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onAbortRoutine
	 */
	inline Routine & getOnAbortRoutine()
	{
		return( onAbortRoutine );
	}

	inline const Routine & getOnAbortRoutine() const
	{
		return( onAbortRoutine );
	}

	inline const BFCode & getOnAbort() const
	{
		return( onAbortRoutine.getCode() );
	}

	inline bool hasOnAbort() const
	{
		return( onAbortRoutine.hasCode() );
	}

	inline void setOnAbort(const BFCode & aCode)
	{
		onAbortRoutine.setCode( aCode );
	}

	inline void seqOnAbort(const BFCode & aCode)
	{
		onAbortRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onIAbortRoutine
	 */
	inline Routine & getOnIAbortRoutine()
	{
		return( onIAbortRoutine );
	}

	inline const Routine & getOnIAbortRoutine() const
	{
		return( onIAbortRoutine );
	}

	inline const BFCode & getOnIAbort() const
	{
		return( onIAbortRoutine.getCode() );
	}

	inline bool hasOnIAbort() const
	{
		return( onIAbortRoutine.hasCode() );
	}

	inline void setOnIAbort(const BFCode & aCode)
	{
		onIAbortRoutine.setCode( aCode );
	}

	inline void seqOnIAbort(const BFCode & aCode)
	{
		onIAbortRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onIRunRoutine
	 */
	inline Routine & getOnIRunRoutine()
	{
		return( onIRunRoutine );
	}

	inline const Routine & getOnIRunRoutine() const
	{
		return( onIRunRoutine );
	}

	inline const BFCode & getOnIRun() const
	{
		return( onIRunRoutine.getCode() );
	}

	inline bool hasOnIRun() const
	{
		return( onIRunRoutine.hasCode() );
	}

	inline void setOnIRun(const BFCode & aCode)
	{
		onIRunRoutine.setCode( aCode );
	}

	inline void seqOnIRun(const BFCode & aCode)
	{
		onIRunRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onRunRoutine
	 */
	inline Routine & getOnRunRoutine()
	{
		return( onRunRoutine );
	}

	inline const Routine & getOnRunRoutine() const
	{
		return( onRunRoutine );
	}

	inline const BFCode & getOnRun() const
	{
		return( onRunRoutine.getCode() );
	}

	inline bool hasOnRun() const
	{
		return( onRunRoutine.hasCode() );
	}

	inline void setOnRun(const BFCode & aCode)
	{
		onRunRoutine.setCode( aCode );
	}

	inline void seqOnRun(const BFCode & aCode)
	{
		onRunRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * onRtcRoutine
	 */
	inline Routine & getOnRtcRoutine()
	{
		return( onRtcRoutine );
	}

	inline const Routine & getOnRtcRoutine() const
	{
		return( onRtcRoutine );
	}

	inline const BFCode & getOnRtc() const
	{
		return( onRtcRoutine.getCode() );
	}

	inline bool hasOnRtc() const
	{
		return( onRtcRoutine.hasCode() );
	}

	inline void setOnRtc(const BFCode & aCode)
	{
		onRtcRoutine.setCode( aCode );
	}

	inline void seqOnRtc(const BFCode & aCode)
	{
		onRtcRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * theSchedule
	 */
	inline Routine & getOnScheduleRoutine()
	{
		return( onScheduleRoutine );
	}

	inline const Routine & getOnScheduleRoutine() const
	{
		return( onScheduleRoutine );
	}

	inline const BFCode & getOnSchedule() const
	{
		return( onScheduleRoutine.getCode() );
	}

	inline bool hasOnSchedule() const
	{
		return( onScheduleRoutine.hasCode() );
	}

	inline void setOnSchedule(const BFCode & aCode)
	{
		onScheduleRoutine.setCode( aCode );
	}

	inline void seqOnSchedule(const BFCode & aCode)
	{
		onScheduleRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * theConcurrency
	 */
	inline Routine & getOnConcurrencyRoutine()
	{
		return( onConcurrencyRoutine );
	}

	inline const Routine & getOnConcurrencyRoutine() const
	{
		return( onConcurrencyRoutine );
	}

	inline const BFCode & getOnConcurrency() const
	{
		return( onConcurrencyRoutine.getCode() );
	}

	inline bool hasOnConcurrency() const
	{
		return( onConcurrencyRoutine.hasCode() );
	}

	inline void setOnConcurrency(const BFCode & aCode)
	{
		onConcurrencyRoutine.setCode( aCode );
	}

	inline void seqOnConcurrency(const BFCode & aCode)
	{
		onConcurrencyRoutine.seqCode( aCode );
	}


	/**
	 * GETTER - SETTER
	 * theSynchronize
	 */
	inline Routine & getOnSynchronizeRoutine()
	{
		return( onSynchronizeRoutine );
	}

	inline const Routine & getOnSynchronizeRoutine() const
	{
		return( onSynchronizeRoutine );
	}

	inline const BFCode & getOnSynchronize() const
	{
		return( onSynchronizeRoutine.getCode() );
	}

	inline bool hasOnSynchronize() const
	{
		return( onSynchronizeRoutine.hasCode() );
	}

	inline void setOnSynchronize(const BFCode & aCode)
	{
		onSynchronizeRoutine.setCode( aCode );
	}


	/**
	 * UTIL
	 */
	Routine & getActivity(AVM_OPCODE opcodeActivity);

	const Routine & getActivity(AVM_OPCODE opcodeActivity) const;



	/**
	 * GETTER - SETTER
	 * User Routines
	 */
	inline void appendRoutine(const BF & routine)
	{
		mRoutines.append(routine);
	}

	inline void saveRoutine(Routine * routine)
	{
		mRoutines.append( BF(routine) );
	}

	Routine * rawRoutineByNameID(const std::string & id) const
	{
		return( mRoutines.rawByNameID(id) );
	}

	const TableOfRoutine & getRoutines() const
	{
		return( mRoutines );
	}


	inline bool hasRoutine() const
	{
		return( mRoutines.nonempty() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_routine_iterator routine_begin() const
	{
		return( mRoutines.begin() );
	}

	inline const_routine_iterator routine_end() const
	{
		return( mRoutines.end() );
	}


	/**
	 * GETTER - SETTER
	 * mAnonymousInnerRoutines
	 * like << variable::on_write >> or << type::constraint >> routines
	 */
	inline void saveAnonymousInnerRoutine(Routine * routine)
	{
		mAnonymousInnerRoutines.append( BF(routine) );
	}

	inline bool hasAnonymousInnerRoutine() const
	{
		return( mAnonymousInnerRoutines.nonempty() );
	}

	/**
	 * TESTER
	 * mRoutines
	 * mAutomaticRoutines
	 */
	inline bool hasAnyRoutine() const
	{
		return( mRoutines.nonempty() || mAnonymousInnerRoutines.nonempty() );
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & os) const
	{
		os << "moe:";
	}


	void toStreamRoutine(OutStream & os) const;

	void toStreamAnonymousInnerRoutine(OutStream & os) const;

	inline void toStreamAnyRoutine(OutStream & os) const
	{
		if( mAnonymousInnerRoutines.nonempty() )
		{
			toStreamAnonymousInnerRoutine(os);
		}

		if( mRoutines.nonempty() )
		{
			toStreamRoutine( os );
		}
	}

	void toStreamMoe(OutStream & os) const;

	inline void toStream(OutStream & os) const
	{
		if( mAnonymousInnerRoutines.nonempty() )
		{
			toStreamAnonymousInnerRoutine(os);
		}

		if( mRoutines.nonempty() )
		{
			toStreamRoutine( os );
		}

		toStreamMoe(os);
	}

};


}

#endif /* FML_INFRASTRUCTURE_BEHAVIORALPART_H_ */
