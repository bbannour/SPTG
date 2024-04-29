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

#ifndef AVMACTIVITYPRIMITIVE_H_
#define AVMACTIVITYPRIMITIVE_H_

#include <computer/primitive/BaseAvmPrimitive.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/Message.h>



namespace sep
{


class InstanceOfBuffer;
class RuntimeID;


AVM_PRIMITIVE_EVAL_CLASS(Self , BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(Super, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(ContextSwitcher, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Init, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Final, BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS_HEADER(Destroy, BaseAvmPrimitive)
	bool destroyedParent(ExecutionEnvironment & ENV,
			ExecutionEnvironment & tmpENV, const RuntimeID & aRID);

	bool destroyedParent(ExecutionEnvironment & ENV,
			ExecutionData & anED,	const RuntimeID & aRID);
};


AVM_PRIMITIVE_RUN_CLASS(Start            , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Restart          , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Stop             , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Wait             , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Suspend          , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Resume           , BaseAvmPrimitive)


// Runtime State Setter
AVM_PRIMITIVE_RUN_CLASS(ProcessStateSet  , BaseAvmPrimitive)

// Enable family
AVM_PRIMITIVE_RUN_CLASS(IEnableInvoke    , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(EnableInvoke     , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(EnableSet        , BaseAvmPrimitive)

// Disable family
AVM_PRIMITIVE_RUN_CLASS(IDisableInvoke   , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(DisableInvoke    , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(DisableSet       , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(DisableChild     , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(DisableSelf      , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(DisableSelves    , BaseAvmPrimitive)

// Abort family
AVM_PRIMITIVE_RUN_CLASS(IAbortInvoke     , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(AbortInvoke      , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(AbortSet         , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(AbortChild       , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(AbortSelf        , BaseAvmPrimitive)
AVM_PRIMITIVE_RUN_CLASS(AbortSelves      , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Nop              , BaseAvmPrimitive)


// History family
AVM_PRIMITIVE_RUN_CLASS(HistoryClear     , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(DeepHistoryInvoke, BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(ShallowHistoryInvoke, BaseAvmPrimitive)


// Run family
AVM_PRIMITIVE_RUN_CLASS(IRun             , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(Run              , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_RESUME_CLASS(Rtc       , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(ScheduleInvoke   , BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(ScheduleGet     , BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(ScheduleIn      , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(ScheduleSet      , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(DeferInvoke      , BaseAvmPrimitive)

AVM_PRIMITIVE_EVAL_CLASS(DeferGet        , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS(DeferSet         , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Goto             , BaseAvmPrimitive)


AVM_PRIMITIVE_RUN_CLASS(Fork             , BaseAvmPrimitive)

AVM_PRIMITIVE_RUN_CLASS_HEADER(Join      , BaseAvmPrimitive)
	bool checksatJoin(ExecutionEnvironment & ENV, const BF & aJoinSpec);
protected:
	Vector< ListOfExecutionData > tableOfWaitingJoin;
};


AVM_PRIMITIVE_RUN_CLASS(Rdv              , BaseAvmPrimitive)




}

#endif /* AVMACTIVITYPRIMITIVE_H_ */
