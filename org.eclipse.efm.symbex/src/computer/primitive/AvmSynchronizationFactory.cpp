/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmSynchronizationFactory.h"

#include <computer/PathConditionProcessor.h>

#include <fml/executable/InstanceOfData.h>
#include <fml/executable/Router.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/AvmCodeFactory.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionSimplifier.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>



namespace sep
{


/*
 *******************************************************************************
 *******************************************************************************
 * FUSION
 * ExecutionData -- RuntimeForm
 *******************************************************************************
 *******************************************************************************
 */

BF AvmSynchronizationFactory::buildScheduleForm(const Operator * buildOp,
		const BF & refScheduleForm, const BF & frstScheduleForm,
		const BF & sndScheduleForm)
{
	return( AvmCodeFactory::flattenCode( StatementConstructor::newCode(
			buildOp, frstScheduleForm, sndScheduleForm) ) );
}


ExecutionData AvmSynchronizationFactory::fusion(const ExecutionData & refED,
		const ExecutionData & firstED, const ExecutionData & sndED)
{
	std::size_t refMachineCount = refED.getTableOfRuntime().size();

	std::size_t syncMachineCount = std::max(
			sndED.getTableOfRuntime().size(),
			firstED.getTableOfRuntime().size() );

	ExecutionData newED( syncMachineCount );

	// fusion of ExecutionContext
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasExecutionContext() )
			<< "firstED must have ExecutionContext container !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasExecutionContext() )
			<< "sndED must have ExecutionContext container !!!"
			<< SEND_EXIT;
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//			firstED.getExecutionContext() == sndED.getExecutionContext() )
//			<< "firstED & sndED must have the same ExecutionContext container !!!"
//			<< SEND_EXIT;

	newED.setExecutionContext( firstED.getExecutionContext() );


	// fusion of mAEES
	newED.setAEES( RuntimeDef::syncAEES(firstED.getAEES(), sndED.getAEES()) );
	if( newED.getAEES() == AEES_UNKNOWN_SYNC )
	{
		AVM_OS_ERROR_ALERT << "ExecutionData:> fusion of AEES FAILED : ( "
				<< RuntimeDef::strAEES(firstED.getAEES())  << " |sync| "
				<< RuntimeDef::strAEES(sndED.getAEES()) << " ) !!!"
				<< SEND_ALERT;

		return( ExecutionData::_NULL_ );
	}


	// fusion of mRID
	if( firstED.getRID() == sndED.getRID() )
	{
		newED.setRID( firstED.getRID() );
	}
	else
	{
		newED.setRID( refED.getRID() );

//		AVM_OS_WARNING_ALERT << "ExecutionData:> fusion of RID FAILED : ( ref< "
//				<< refED.getRID().str() << " > , " << firstED.getRID().str()
//				<< " != " << sndED.getRID().str() << " )"
//				<< SEND_ALERT;
//
//		return( ExecutionData::_NULL_ );
	}


	// fusion of onInit
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasOnInit() )
			<< "firstED must have onInit !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasOnInit() )
			<< "sndED must have onInit !!!"
			<< SEND_EXIT;

	if( refED.getOnInit() == firstED.getOnInit() )
	{
		newED.setOnInit( sndED.getOnInit() );
	}
	else if( refED.getOnInit() == sndED.getOnInit() )
	{
		newED.setOnInit( firstED.getOnInit() );
	}
	else if( firstED.getOnInit() == sndED.getOnInit() )
	{
		newED.setOnInit( firstED.getOnInit() );
	}
//	else if( firstED.hasOnInit() && sndED.hasOnInit() )
//	{
////		BFCode onInit = AvmCodeFactory::flattenCode(
////				StatementConstructor::newCode(
////						OperatorManager::OPERATOR_PARALLEL,
////						firstED.getOnInit(), sndED.getOnInit()) );
////		newED.setOnInit( onInit );
//
//		AVM_OS_ERROR_ALERT << "ExecutionData:> fusion of routine OnInit FAILED :"
//				<< "\n\t$0 = " << refED.getOnInit().str()
//				<< "\n\t$1 = " << firstED.getOnInit().str()
//				<< "\n\t$2 = " << sndED.getOnInit().str()
//				<< SEND_ALERT;
//
//		return( ExecutionData::_NULL_ );
//	}
	else
	{
		AVM_OS_ERROR_ALERT << "ExecutionData:> fusion of routine OnInit FAILED :"
				<< "\n\t$0 = " << refED.getOnInit().str()
				<< "\n\t$1 = " << firstED.getOnInit().str()
				<< "\n\t$2 = " << sndED.getOnInit().str()
				<< SEND_ALERT;

		return( ExecutionData::_NULL_ );
	}

	// fusion of onSchedule
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasOnSchedule() )
			<< "firstED must have onSchedule !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasOnSchedule() )
			<< "sndED must have onSchedule !!!"
			<< SEND_EXIT;

	if( refED.getOnSchedule() == firstED.getOnSchedule() )
	{
		newED.setOnSchedule( sndED.getOnSchedule() );
	}
	else if( refED.getOnSchedule() == sndED.getOnSchedule() )
	{
		newED.setOnSchedule( firstED.getOnSchedule() );
	}
	else if( firstED.getOnSchedule() == sndED.getOnSchedule() )
	{
		newED.setOnSchedule( firstED.getOnSchedule() );
	}
//	else if( firstED.hasOnSchedule() && sndED.hasOnSchedule() )
//	{
////		BFCode onSchedule = AvmCodeFactory::flattenCode(
////				StatementConstructor::newCode(
////						OperatorManager::OPERATOR_PARALLEL,
////						firstED.getOnSchedule(), sndED.getOnSchedule()) );
////		newED.setOnSchedule( onSchedule );
//
//		AVM_OS_ERROR_ALERT << "ExecutionData:> fusion of routine OnSchedule FAILED :"
//				<< "\n\t$0 = " << refED.getOnSchedule().str()
//				<< "\n\t$1 = " << firstED.getOnSchedule().str()
//				<< "\n\t$2 = " << sndED.getOnSchedule().str()
//				<< SEND_ALERT;
//
//		return( ExecutionData::_NULL_ );
//	}
	else
	{
		AVM_OS_ERROR_ALERT << "ExecutionData:> fusion of routine OnSchedule FAILED :"
				<< "\n\t$0 = " << refED.getOnSchedule().str()
				<< "\n\t$1 = " << firstED.getOnSchedule().str()
				<< "\n\t$2 = " << sndED.getOnSchedule().str()
				<< SEND_ALERT;

		return( ExecutionData::_NULL_ );
	}


	// fusion of RunnableElementTrace
	if( firstED.hasRunnableElementTrace()
		&& sndED.hasRunnableElementTrace() )
	{
		if( firstED.getRunnableElementTrace() ==
				sndED.getRunnableElementTrace() )
		{
			newED.setRunnableElementTrace(
					firstED.getRunnableElementTrace() );
		}
		else
		{
			newED.setRunnableElementTrace( buildRunnableElementTrace(
					OperatorManager::OPERATOR_PARALLEL,
					refED.getRunnableElementTrace(),
					firstED.getRunnableElementTrace(),
					sndED.getRunnableElementTrace() ) );
		}
	}
	else if( firstED.hasRunnableElementTrace() )
	{
		newED.setRunnableElementTrace( firstED.getRunnableElementTrace() );
	}
	else if(  sndED.hasRunnableElementTrace() )
	{
		newED.setRunnableElementTrace( sndED.getRunnableElementTrace() );
	}
	else
	{
		newED.setRunnableElementTrace( refED.getRunnableElementTrace() );
	}


	// fusion of IOElementTrace
	if( firstED.hasIOElementTrace() &&  sndED.hasIOElementTrace() )
	{
		if( firstED.getIOElementTrace() == sndED.getIOElementTrace() )
		{
			newED.setIOElementTrace( firstED.getIOElementTrace() );
		}
		else
		{
			newED.setIOElementTrace( buildIOElementTrace(
					OperatorManager::OPERATOR_PARALLEL, refED.getIOElementTrace(),
					firstED.getIOElementTrace(), sndED.getIOElementTrace() ) );
		}
	}
	else if( firstED.hasIOElementTrace() )
	{
		newED.setIOElementTrace( firstED.getIOElementTrace() );
	}
	else if(  sndED.hasIOElementTrace() )
	{
		newED.setIOElementTrace( sndED.getIOElementTrace() );
	}
	else
	{
		newED.setIOElementTrace( refED.getIOElementTrace() );
	}


	// fusion of NodeCondition
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasNodeCondition() )
			<< "firstED must have NodeCondition !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasNodeCondition() )
			<< "sndED must have NodeCondition !!!"
			<< SEND_EXIT;

	BF theNodeCondition = ExpressionSimplifier::simplif_and(
			firstED.getNodeCondition(),
			sndED.getNodeCondition());

	if( PathConditionProcessor::isWeakSatisfiable(theNodeCondition) )
	{
		newED.setNodeCondition( theNodeCondition );
	}
	else
	{
		return( ExecutionData::_NULL_ );
	}

	// fusion of NodeTimedCondition
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasNodeTimedCondition() )
			<< "firstED must have NodeTimedCondition !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasNodeTimedCondition() )
			<< "sndED must have NodeTimedCondition !!!"
			<< SEND_EXIT;

	BF theNodeTimedCondition = ExpressionSimplifier::simplif_and(
			firstED.getNodeTimedCondition(),
			sndED.getNodeTimedCondition());


	if( PathConditionProcessor::isWeakSatisfiable(theNodeTimedCondition) )
	{
		newED.setNodeTimedCondition( theNodeTimedCondition );
	}
	else
	{
		return( ExecutionData::_NULL_ );
	}


	// fusion of PathCondition
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasPathCondition() )
			<< "firstED must have PathCondition !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasPathCondition() )
			<< "sndED must have PathCondition !!!"
			<< SEND_EXIT;

	if( firstED.getPathCondition() == sndED.getPathCondition() )
	{
		newED.setPathCondition( firstED.getPathCondition() );
	}
	else
	{
		BF thePathCondition = ExpressionSimplifier::simplif_and(
				firstED.getPathCondition(), sndED.getPathCondition());
		if( PathConditionProcessor::isWeakSatisfiable(thePathCondition))
		{
			newED.setPathCondition( thePathCondition );
		}
		else
		{
			return( ExecutionData::_NULL_ );
		}
	}


	// fusion of PathTimedCondition
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstED.hasPathTimedCondition() )
			<< "firstED must have PathTimedCondition !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndED.hasPathTimedCondition() )
			<< "sndED must have PathTimedCondition !!!"
			<< SEND_EXIT;

	if( firstED.getPathTimedCondition() == sndED.getPathTimedCondition() )
	{
		newED.setPathTimedCondition( firstED.getPathTimedCondition() );
	}
	else
	{
		BF thePathTimedCondition = ExpressionSimplifier::simplif_and(
				firstED.getPathTimedCondition(),
				sndED.getPathTimedCondition());
		if( PathConditionProcessor::isWeakSatisfiable(thePathTimedCondition) )
		{
			newED.setPathTimedCondition( thePathTimedCondition );
		}
		else
		{
			return( ExecutionData::_NULL_ );
		}
	}


	// ExecutionData::PARAM_MACHINE_RUNTIME_OFFSET === 0
	if( not fusion(newED, refED.getParametersRuntimeForm(),
		firstED.getParametersRuntimeForm(), sndED.getParametersRuntimeForm()) )
	{
		// AvmConcurrencyStatement Failed
		return( ExecutionData::_NULL_ );
	}

	// ExecutionData::SYSTEM_RUNTIME_OFFSET === 1
	std::size_t offset = ExecutionData::SYSTEM_RUNTIME_OFFSET;
	for( ; offset < refMachineCount ; ++offset )
	{
		// fusion of Process Eval State
		newED.setRuntimeFormState( offset,
				RuntimeDef::syncPES(
						refED.getRuntimeFormState(offset),
						firstED.getRuntimeFormState(offset),
						sndED.getRuntimeFormState(offset) ) );

		if( newED.isUndefinedPES(offset) )
		{
			AVM_OS_ERROR_ALERT << "ExecutionData:> "
				"Fusion of Runtime State FAILED : "
				"(ref != first) && (ref != snd) && (first != snd)"
				"\n\tExecutionData Control Configuration:>"
				<< "\n\t$0: " << refED.strStateConf()
				<< "\n\t$1: " << firstED.strStateConf()
				<< "\n\t$2: " << sndED.strStateConf()

				<< "\n\tFiring Code:>"
				<< "\n\t$1: " << refED.getRunnableElementTrace().str()
				<< "\n\t$1: " << firstED.getRunnableElementTrace().str()
				<< "\n\t$2: " << sndED.getRunnableElementTrace().str()

				<< "\n\tTrace Code:>"
				<< "\n\t$0: " << refED.getIOElementTrace().str()
				<< "\n\t$1: " << firstED.getIOElementTrace().str()
				<< "\n\t$2: " << sndED.getIOElementTrace().str()

				<< "\n\tMachine Status:> " << refED.getRuntime(offset).str()
				<< "\n\tMachine Control Configuration:>"
				<< "\n\t$0: " << refED.strStateConf(refED.getRuntime(offset))
				<< "\n\t$1: " << firstED.strStateConf(firstED.getRuntime(offset))
				<< "\n\t$2: " << sndED.strStateConf(sndED.getRuntime(offset))

				<< "\n\t$0 = " << RuntimeDef::strPES(refED.getRuntimeFormState(offset))
				<< "\n\t$1 = " << RuntimeDef::strPES(firstED.getRuntimeFormState(offset))
				<< "\n\t$2 = " << RuntimeDef::strPES(sndED.getRuntimeFormState(offset))
				<< SEND_ALERT;

			return( ExecutionData::_NULL_ );
		}

//		// Propagate synchronized EVAL STATE form childs to parent
//		if( firstED.isFinalizedOrDestroyed(offset) ||
//				sndED.isFinalizedOrDestroyed(offset) )
//		{
//			RuntimeID aRID = newED.getRuntimeID(offset);
//			RuntimeForm * aRF = nullptr;
//			while( aRID.hasPRID() && aRID.getPRID().hasKindAND() )
//			{
//				aRF = newED.getRuntimeForm( aRID = aRID.getPRID() );
//
//				// TODO:> Child may not be synchronized ==> defined
//				TableOfRuntimeID::const_iterator it = aRF.beginChild();
//				TableOfRuntimeID::const_iterator endIt = aRF.endChild();
//				for( ; it != endIt ; ++it )
//				{
//					if( not newED.isFinalizedOrDestroyed(*it) )
//					{
//						break;
//					}
//				}
//
//				if( it == endIt )
//				{
//					newED.setRuntimeFormState( aRID,
//							(firstED.isFinalized(offset) ||
//									sndED.isFinalized(offset)) ?
//											PROCESS_FINALIZED_STATE :
//											PROCESS_DESTROYED_STATE );
//				}
//				else
//				{
//					break;
//				}
//			}
//
//			if( newED.isunRunnableSystem() )
//			{
//				newED.setAEES(AEES_STMNT_EXIT);
//			}
//		}

		// fusion of Assign State
		newED.wrRuntimeFormStateTable()->setAssignedUnion(offset,
				firstED.getAssigned(offset), sndED.getAssigned(offset));

		// fusion of RuntimeForm
		if( not fusion(newED, refED.getRuntime(offset),
			firstED.getRuntime(offset), sndED.getRuntime(offset)) )
		{
			// AvmConcurrencyStatement Failed
			return( ExecutionData::_NULL_ );
		}
	}


	if( refMachineCount != syncMachineCount )
	{
		// for new RuntimeForm since refED
		const ExecutionData & maxED =
				( firstED.getTableOfRuntime().size() == syncMachineCount )
				? firstED : sndED;

		if( firstED.getTableOfRuntime().size() == syncMachineCount )
		{
			if( sndED.getTableOfRuntime().size() != refMachineCount )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "sndED must have refMachineCount Machine !!!"
						<< SEND_EXIT;
			}
		}
		else// if( sndED.getTableOfRuntime().size() == syncMachineCount )
		{
			if( firstED.getTableOfRuntime().size() != refMachineCount )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "firstED must have refMachineCount Machine !!!"
						<< SEND_EXIT;
			}
		}

		for( ; offset < syncMachineCount ; ++offset )
		{
			// fusion of Process Eval State
			newED.setRuntimeFormState(offset,
					maxED.getRuntimeFormState(offset));

			// fusion of Assign State
			newED.wrRuntimeFormStateTable()->setAssigned(
					offset, maxED.getAssigned(offset) );

			// fusion of RuntimeForm
			newED.assignRuntimeForm(offset,
					const_cast< RuntimeForm * >( maxED.ptrRuntime(offset) ) );

//			// Propagate synchronized EVAL STATE form childs to parent
//			if( maxED.isFinalizedOrDestroyed(offset) )
//			{
//				RuntimeID aRID = newED.getRuntimeID(offset);
//				while( aRID.hasPRID() && aRID.getPRID().hasKindAND() )
//				{
//					const RuntimeForm & aRF =
//							newED.getRuntime( aRID = aRID.getPRID() );
//
//					// TODO:> Child may not be synchronized / defined
//					TableOfRuntimeID::const_iterator it = aRF.beginChild();
//					TableOfRuntimeID::const_iterator endIt = aRF.endChild();
//					for( ; it != endIt ; ++it )
//					{
//						if( not newED.isFinalizedOrDestroyed(*it) )
//						{
//							break;
//						}
//					}
//
//					if( it == endIt )
//					{
//						newED.setRuntimeFormState(aRID,
//								(firstED.isFinalized(offset) ||
//										sndED.isFinalized(offset)) ?
//												PROCESS_FINALIZED_STATE :
//												PROCESS_DESTROYED_STATE);
//					}
//					else
//					{
//						break;
//					}
//				}
//
//				if( newED.isunRunnableSystem() )
//				{
//					newED.setAEES(AEES_STMNT_EXIT);
//				}
//			}
		}
	}


	return( newED );
}


bool AvmSynchronizationFactory::fusion(const ExecutionData & newED,
		const ParametersRuntimeForm & refParamsRF,
		const ParametersRuntimeForm & firstParamsRF,
		const ParametersRuntimeForm & sndParamsRF)
{
	if( ((& firstParamsRF) == (& sndParamsRF))
		|| ((& refParamsRF) == (& sndParamsRF)) )
	{
		newED.assignParametersRuntimeForm(
				const_cast< ParametersRuntimeForm * >( & firstParamsRF ) );

		return( true );
	}
	else if( (& refParamsRF) == (& firstParamsRF) )
	{
		newED.assignParametersRuntimeForm(
				const_cast< ParametersRuntimeForm * >( & sndParamsRF ) );

		return( true );
	}
	else
	{
		std::size_t refParamsCount = refParamsRF.getParametersSize();

		ParametersRuntimeForm * newParamsRF =
				new ParametersRuntimeForm(refParamsRF.getRID(), refParamsCount);

		newED.saveParametersRuntimeForm( newParamsRF );

		std::size_t offset = 0;
		for( ; offset < refParamsCount ; ++offset )
		{
			// fusion of DATA
			if( refParamsRF.rawParameter(offset)->getModifier().hasFeatureTransient() )
			{
				newParamsRF->setParameter(offset,
						refParamsRF.getParameter(offset),
						refParamsRF.getData(offset) );
			}

			else if( refParamsRF.getData(offset) == firstParamsRF.getData(offset) )
			{
				newParamsRF->setParameter(offset,
						refParamsRF.getParameter(offset),
						sndParamsRF.getData(offset) );
			}
			else if( refParamsRF.getData(offset) == sndParamsRF.getData(offset) )
			{
				newParamsRF->setParameter(offset,
						refParamsRF.getParameter(offset),
						firstParamsRF.getData(offset) );
			}
			// TODO Equality between Element
			else if( firstParamsRF.getData(offset) == sndParamsRF.getData(offset) )
			{
				newParamsRF->setParameter(offset,
						refParamsRF.getParameter(offset),
						firstParamsRF.getData(offset) );
			}
			else if( //refParamsRF.getParameter(offset)->isTypedArrayOrStructure() &&
					refParamsRF.getData(offset).is< ArrayBF >() &&
					firstParamsRF.getData(offset).is< ArrayBF >() &&
					sndParamsRF.getData(offset).is< ArrayBF >() )
			{
				BF syncValue = fusionArrayData(refParamsRF,
						refParamsRF.getData(offset).to_ptr< ArrayBF >(),
						firstParamsRF.getData(offset).to_ptr< ArrayBF >(),
						sndParamsRF.getData(offset).to_ptr< ArrayBF >() );

				if( syncValue.valid() )
				{
					newParamsRF->setParameter(offset,
							refParamsRF.getParameter(offset), syncValue );
				}
				else
				{
					// AvmConcurrencyStatement Failed
					AVM_OS_ERROR_ALERT
							<< "Runtime< " << refParamsRF.getRID().str()
							<< "> :> fusion of Data Table ARRAY Element FAILED "
								": (itFirstData != itSndData) :"
							<< "\n\t$0 = " << refParamsRF.getData(offset).str()
							<< "\n\t$1 = " << firstParamsRF.getData(offset).str()
							<< "\n\t$2 = " << sndParamsRF.getData(offset).str()
							<< SEND_ALERT;

					return( false );
				}
			}
			else if( refParamsRF.rawParameter(offset)->
					getTypeSpecifier().hasTypeComposite() )
			{
				// AvmConcurrencyStatement Failed
				AVM_OS_WARNING_ALERT
						<< "Runtime< " << refParamsRF.getRID().str()
						<< "> :> fusion of Data Table ARRAY Element FAILED : "
							"(itFirstData<array> != itSndData<array>) :"
						<< "\n\t$0 = " << refParamsRF.getData(offset).str()
						<< "\n\t$1 = " << firstParamsRF.getData(offset).str()
						<< "\n\t$2 = " << sndParamsRF.getData(offset).str()
						<< SEND_ALERT;

				return( false );
			}
			else
			{
				// AvmConcurrencyStatement Failed
				AVM_OS_ERROR_ALERT
						<< "Runtime< " << refParamsRF.getRID().str()
						<< "> :> fusion of Data Table Element FAILED : "
							"(itFirstData != itSndData) :"
						<< "\n\t$0 = " << refParamsRF.getData(offset).str()
						<< "\n\t$1 = " << firstParamsRF.getData(offset).str()
						<< "\n\t$2 = " << sndParamsRF.getData(offset).str()
						<< SEND_ALERT;

				return( false );
			}
		}

		for( offset = refParamsCount ;
				offset < firstParamsRF.getParametersSize() ; ++offset )
		{
			newParamsRF->appendParameter( firstParamsRF.getParameter(offset),
					firstParamsRF.getData(offset) );
		}

		for( offset = refParamsCount ;
				offset < sndParamsRF.getParametersSize() ; ++offset )
		{
			newParamsRF->appendParameter( sndParamsRF.getParameter(offset),
					sndParamsRF.getData(offset) );
		}
	}

	return( true );
}


bool AvmSynchronizationFactory::fusion(
		const ExecutionData & newED, const RuntimeForm & refRF,
		const RuntimeForm & firstRF, const RuntimeForm & sndRF)
{
	if( ((& firstRF) == (& sndRF)) || ((& refRF) == (& sndRF)) )
	{
		newED.assignRuntimeForm( firstRF.getOffset() ,
				const_cast< RuntimeForm* >(& firstRF) );

		return( true );
	}
	else if( &refRF == &firstRF )
	{
		newED.assignRuntimeForm( firstRF.getOffset() ,
				const_cast< RuntimeForm* >(& sndRF) );

		return( true );
	}

	// new synchronized RuntimeForm
	RuntimeForm * newRF = new RuntimeForm( refRF.getRID() );

	newED.saveRuntimeForm( newRF->getOffset() , newRF );

	// fusion of InstanciationCount
	if( refRF.getInstanciationCount() == firstRF.getInstanciationCount() )
	{
		newRF->setInstanciationCount( sndRF.getInstanciationCount() );
	}
	else if( refRF.getInstanciationCount() == sndRF.getInstanciationCount() )
	{
		newRF->setInstanciationCount( firstRF.getInstanciationCount() );
	}
	else if( firstRF.getInstanciationCount() != sndRF.getInstanciationCount() )
	{
		newRF->setInstanciationCount(
				std::max(firstRF.getInstanciationCount(),
						sndRF.getInstanciationCount() ) );
	}

	// fusion of ChildTable
	if( refRF.getChildTable() == firstRF.getChildTable() )
	{
		newRF->setChildTable( sndRF.getChildTable() );
	}
	else if( refRF.getChildTable() == sndRF.getChildTable() )
	{
		newRF->setChildTable( firstRF.getChildTable() );
	}
	else if( firstRF.getChildTable() != sndRF.getChildTable() )
	{
		// TODO AvmConcurrencyStatement of Child Table
	}
	else
	{
		AVM_OS_ERROR_ALERT
				<< "Runtime< " << refRF.getRID().str()
				<< "> :> fusion of Child Table FAILED : "
					"(ref != first) && (ref != snd) && (first = snd) :\n"
				<< refRF.getChildTable()->toString(AVM_TAB1_INDENT)
				<< firstRF.getChildTable()->toString(AVM_TAB1_INDENT)
				<< sndRF.getChildTable()->toString(AVM_TAB1_INDENT)
				<< SEND_ALERT;

		return( false );
	}

	// fusion of DATA
	if( not fusion((*newRF), refRF.getDataTable(),
			firstRF.getDataTable(), sndRF.getDataTable()) )
	{
		return( false );
	}

	// fusion of BUFFER
	if( not fusion((*newRF), refRF.getBufferTable(), firstRF.getBufferTable(),
			sndRF.getBufferTable()) )
	{
		return( false );
	}

	// fusion of ROUTER
	if( not fusion((*newRF), refRF.getRouter(),
			firstRF.getRouter(), sndRF.getRouter()) )
	{
		return( false );
	}


//!?! Code pour évolution future
//	// fusion of NodeCondition
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstRF.hasNodeCondition() )
//			<< "firstRF must have NodeCondition !!!"
//			<< SEND_EXIT;
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndRF.hasNodeCondition() )
//			<< "sndRF must have NodeCondition !!!"
//			<< SEND_EXIT;
//
//	BF theNodeCondition = ExpressionSimplifier::simplif_and(
//			firstRF.getNodeCondition(),
//			sndRF.getNodeCondition());
//	if( PathConditionProcessor::isWeakSatisfiable(theNodeCondition) )
//	{
//		newRF->setNodeCondition( theNodeCondition );
//	}
//	else
//	{
//		return( false );
//	}
//
//
//	// fusion of NodeTimedCondition
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( firstRF.hasNodeTimedCondition() )
//			<< "firstRF must have NodeTimedCondition !!!"
//			<< SEND_EXIT;
//	AVM_OS_ASSERT_FATAL_ERROR_EXIT( sndRF.hasNodeTimedCondition() )
//			<< "sndRF must have NodeTimedCondition !!!"
//			<< SEND_EXIT;
//
//	BF theNodeTimedCondition = ExpressionSimplifier::simplif_and(
//			firstRF.getNodeTimedCondition(),
//			sndRF.getNodeTimedCondition());
//	if( PathConditionProcessor::isWeakSatisfiable(theNodeTimedCondition) )
//	{
//		newRF->setNodeTimedCondition( theNodeTimedCondition );
//	}
//	else
//	{
//		return( false );
//	}


	// fusion of onSchedule
	if( refRF.getOnSchedule() == firstRF.getOnSchedule() )
	{
		newRF->setOnSchedule( sndRF.getOnSchedule() );
	}
	else if( refRF.getOnSchedule() == sndRF.getOnSchedule() )
	{
		newRF->setOnSchedule( firstRF.getOnSchedule() );
	}
	else if( firstRF.getOnSchedule() == sndRF.getOnSchedule() )
	{
		newRF->setOnSchedule( firstRF.getOnSchedule() );
	}
//	else if( firstRF.hasOnSchedule() && sndRF.hasOnSchedule() )
//	{
////		newRF->setOnSchedule( buildScheduleForm(
////				OperatorManager::OPERATOR_PARALLEL, refRF.getOnSchedule(),
////				firstRF.getOnSchedule(), sndRF.getOnSchedule()) );
//
//		AVM_OS_ERROR_ALERT
//				<< "Runtime< " << refRF.getRID().str()
//				<< "> :> fusion of routine OnSchedule FAILED :"
//				<< "\n\t$0 = " << refRF.getOnSchedule().str()
//				<< "\n\t$1 = " << firstRF.getOnSchedule().str()
//				<< "\n\t$2 = " << sndRF.getOnSchedule().str()
//				<< SEND_ALERT;
//
//		return( false );
//	}
	else
	{
		AVM_OS_ERROR_ALERT
				<< "Runtime< " << refRF.getRID().str()
				<< "> :> fusion of routine OnSchedule FAILED :"
				<< "\n\t$0 = " << refRF.getOnSchedule().str()
				<< "\n\t$1 = " << firstRF.getOnSchedule().str()
				<< "\n\t$2 = " << sndRF.getOnSchedule().str()
				<< SEND_ALERT;

		return( false );
	}


	// fusion of onDefer
	if( refRF.getOnDefer() == firstRF.getOnDefer() )
	{
		newRF->setOnDefer( sndRF.getOnDefer() );
	}
	else if( refRF.getOnDefer() == sndRF.getOnDefer() )
	{
		newRF->setOnDefer( firstRF.getOnDefer() );
	}
	else if( firstRF.getOnDefer() == sndRF.getOnDefer() )
	{
		newRF->setOnDefer( firstRF.getOnDefer() );
	}
//	else if( firstRF.hasOnDefer() && sndRF.hasOnDefer() )
//	{
////		newRF->setOnDefer( buildScheduleForm(
////				OperatorManager::OPERATOR_PARALLEL, refRF.getOnDefer(),
////				firstRF.getOnDefer(), sndRF.getOnDefer()) );
//
//		AVM_OS_ERROR_ALERT
//				<< "Runtime< " << refRF.getRID().str()
//				<< "> :> fusion of routine OnDefer FAILED :"
//				<< "\n\t$0 = " << refRF.getOnDefer().str()
//				<< "\n\t$1 = " << firstRF.getOnDefer().str()
//				<< "\n\t$2 = " << sndRF.getOnDefer().str()
//				<< SEND_ALERT;
//
//		return( false );
//	}
	else
	{
		AVM_OS_ERROR_ALERT
				<< "Runtime< " << refRF.getRID().str()
				<< "> :> fusion of routine OnDefer FAILED :"
				<< "\n\t$0 = " << refRF.getOnDefer().str()
				<< "\n\t$1 = " << firstRF.getOnDefer().str()
				<< "\n\t$2 = " << sndRF.getOnDefer().str()
				<< SEND_ALERT;

		return( false );
	}


//!?! Code pour évolution future
//	// fusion of RunnableElementTrace
//	if( firstRF.hasRunnableElementTrace()
//		&& sndRF.hasRunnableElementTrace() )
//	{
//		if( firstRF.getRunnableElementTrace() ==
//				sndRF.getRunnableElementTrace() )
//		{
//			newRF.setRunnableElementTrace(
//					firstRF.getRunnableElementTrace() );
//		}
//		else
//		{
//			newRF->setRunnableElementTrace( buildRunnableElementTrace(
//					OperatorManager::OPERATOR_PARALLEL,
//					refRF.getRunnableElementTrace(),
//					firsRF.>getRunnableElementTrace(),
//					sndRF.getRunnableElementTrace() )  );
//		}
//	}
//	else if( firstRF.hasRunnableElementTrace() )
//	{
//		newRF->setRunnableElementTrace( firstRF.getRunnableElementTrace() );
//	}
//	else if(  sndRF.hasRunnableElementTrace() )
//	{
//		newRF->setRunnableElementTrace( sndRF.getRunnableElementTrace() );
//	}


	return( true );
}



bool AvmSynchronizationFactory::fusion(RuntimeForm & aRF,
		const APTableOfData & refDataTable,
		const APTableOfData & firstDataTable,
		const APTableOfData & sndDataTable)
{
	// fusion of DATA
	if( firstDataTable.valid() && sndDataTable.valid() )
	{
		if( firstDataTable == sndDataTable )
		{
			aRF.setDataTable( firstDataTable );
		}
		else if( refDataTable == firstDataTable )
		{
			aRF.setDataTable( sndDataTable );
		}
		else if( refDataTable == sndDataTable )
		{
			aRF.setDataTable( firstDataTable );
		}
		else if( (refDataTable->size() == firstDataTable->size()) &&
				(refDataTable->size() == sndDataTable->size()) )
		{
			// Comparison between all data
			TableOfData * aDataTable = new TableOfData( refDataTable->size() );
			aRF.setDataTable( aDataTable );

			TableOfData::iterator itRef = refDataTable->begin();
			TableOfData::iterator itRefEnd = refDataTable->end();
			TableOfData::iterator itFirst = firstDataTable->begin();
			TableOfData::iterator itSnd = sndDataTable->begin();

			std::size_t offset = 0;
			for( ; itRef != itRefEnd ; ++itRef , ++itFirst, ++itSnd, ++offset )
			{
//	AVM_OS_COUT << str_header( aRF.rawVariable(offset) ) << std::endl
//			<< "ref:" << (*itRef).str(" ")   << std::endl
//			<< "fst:" << (*itFirst).str(" ") << std::endl
//			<< "snd:" << (*itSnd).str(" ")   << std::endl << std::endl;

				if( (*itRef) == (*itFirst) )
				{
					aDataTable->set( offset , (*itSnd) );
				}
				else if( (*itRef) == (*itSnd) )
				{
					aDataTable->set( offset , (*itFirst) );
				}
				else if( (*itFirst) == (*itSnd) ) // TODO Equality between Element
				{
					aDataTable->set( offset , (*itFirst) );
				}
				else if( //aRF.getVariable(offset)->isTypedArrayOrStructure() &&
						(*itRef).is< ArrayBF >() &&
						(*itFirst).is< ArrayBF >() &&
						(*itSnd).is< ArrayBF >() )
				{
					BF syncValue = fusionArrayData(aRF,
							(*itRef).to_ptr< ArrayBF >(),
							(*itFirst).to_ptr< ArrayBF >(),
							(*itSnd).to_ptr< ArrayBF >() );

					if( syncValue.valid() )
					{
						aDataTable->set( offset , syncValue );
					}
					else
					{
						// AvmConcurrencyStatement Failed
						AVM_OS_ERROR_ALERT
								<< "Runtime< " << aRF.getRID().str()
								<< "> :> fusion of Data Table ARRAY Element "
									"FAILED : (itFirstData != itSndData) :"
								<< "\n\t" << str_header( aRF.rawVariable(offset) )
								<< "\n\t$0 = " << (*itRef).str()
								<< "\n\t$1 = " << (*itFirst).str()
								<< "\n\t$2 = " << (*itSnd).str()
								<< SEND_ALERT;

						return( false );
					}
				}
				else if( aRF.rawVariable(offset)->
						getTypeSpecifier().hasTypeComposite() )
				{
					// AvmConcurrencyStatement Failed
					AVM_OS_WARNING_ALERT
							<< "Runtime< " << aRF.getRID().str()
							<< "> :> fusion of Data Table ARRAY Element FAILED "
								": (itFirstData<array> != itSndData<array>) :"
							<< "\n\t" << str_header( aRF.rawVariable(offset) )
							<< "\n\t$0 = " << (*itRef).str()
							<< "\n\t$1 = " << (*itFirst).str()
							<< "\n\t$2 = " << (*itSnd).str()
							<< SEND_ALERT;

					return( false );
				}
				else
				{
					// AvmConcurrencyStatement Failed
					AVM_OS_ERROR_ALERT
							<< "Runtime< " << aRF.getRID().str()
							<< "> :> fusion of Data Table Element FAILED : "
								"(itFirstData != itSndData) :"
							<< "\n\t" << str_header( aRF.rawVariable(offset) )
							<< "\n\t$0 = " << (*itRef).str()
							<< "\n\t$1 = " << (*itFirst).str()
							<< "\n\t$2 = " << (*itSnd).str()
							<< SEND_ALERT;

					return( false );
				}

//				if( (*itRef).is< BuiltinQueue >() )
//				{
//					AVM_OS_TRACE
//							<< "Runtime< " << aRF.getRID().str()
//							<< " , " << str_header( aRF.getVariable(offset) )
//							<< " > :> " << std::endl
//							<< "\n\t$0 = " << (*itRef).str()
//							<< "\n\t$1 = " << (*itFirst).str()
//							<< "\n\t$2 = " << (*itSnd).str()
//							<< "\n\t$$ = " << aDataTable->at(offset).str()
//							<< std::endl;
//				}
			}
		}
		else
		{
			// AvmConcurrencyStatement Failed
			AVM_OS_ERROR_ALERT
					<< "Runtime< " << aRF.getRID().str()
					<< "> :> fusion of Data Table Size FAILED : "
						"((refDataTable->size() == firstDataTable->size()) && "
						"(refDataTable->size() == sndDataTable->size())) :\n"
					<< refDataTable->toString(aRF.getVariables(), AVM_TAB1_INDENT)
					<< firstDataTable->toString(aRF.getVariables(), AVM_TAB1_INDENT)
					<< sndDataTable->toString(aRF.getVariables(), AVM_TAB1_INDENT)
					<< SEND_ALERT;

			return( false );
		}
	}
	else if( refDataTable.valid() )
	{
		// AvmConcurrencyStatement Failed
		AVM_OS_ERROR_ALERT
				<< "Runtime< " << aRF.getRID().str()
				<< "> :> fusion of Data Table FAILED : (refDataTable != nullptr) "
					"&& ((firstDataTable == nullptr) || (sndDataTable == nullptr)) :\n"
				<< refDataTable->toString(aRF.getVariables(), AVM_TAB1_INDENT)
				<< firstDataTable->toString(aRF.getVariables(), AVM_TAB1_INDENT)
				<< sndDataTable->toString(aRF.getVariables(), AVM_TAB1_INDENT)
				<< SEND_ALERT;


		return( false );
	}

	return( true );
}


BF AvmSynchronizationFactory::fusionArrayData(const RuntimeForm & aRF,
		ArrayBF * refArray, ArrayBF * firstArray, ArrayBF * sndArray)
{
	ArrayBF * syncArray =
			new ArrayBF(refArray->getTypeSpecifier(), refArray->size());
	BF bfArray( syncArray );

	for( std::size_t offset = 0 ; offset < syncArray->size() ; ++offset )
	{
		//??? TABLEAUX
		if( refArray->at(offset) == firstArray->at(offset) )
		{
			syncArray->set( offset , sndArray->at(offset) );
		}
		else if( refArray->at(offset) == sndArray->at(offset) )
		{
			syncArray->set( offset , firstArray->at(offset) );
		}
		// TODO Equality between Element
		else if( firstArray->at(offset) == sndArray->at(offset) )
		{
			syncArray->set( offset , firstArray->at(offset) );
		}
		else if( refArray->at(offset).is< ArrayBF >() &&
				firstArray->at(offset).is< ArrayBF >() &&
				sndArray->at(offset).is< ArrayBF >() )
		{
			BF syncValue = fusionArrayData(aRF,
					refArray->at(offset).to_ptr< ArrayBF >(),
					firstArray->at(offset).to_ptr< ArrayBF >(),
					sndArray->at(offset).to_ptr< ArrayBF >() );

			if( syncValue.valid() )
			{
				syncArray->set( offset , syncValue );
			}
			else
			{
				// AvmConcurrencyStatement Failed
				AVM_OS_ERROR_ALERT
						<< "Runtime< " << aRF.getRID().str()
						<< "> :> fusion of Data Table ARRAY Element FAILED : "
							"(itFirstData[...] != itSndData[...]) :"
						<< "\n\t$0 = " << refArray->at(offset).str()
						<< "\n\t$1 = " << firstArray->at(offset).str()
						<< "\n\t$2 = " << sndArray->at(offset).str()
						<< SEND_ALERT;

				return( BF::REF_NULL );
			}
		}
//		else if( aRF.getVariable(i)->
//				getTypeSpecifier().isTypedComposite() )
//		{
//			// AvmConcurrencyStatement Failed
//			AVM_OS_WARNING_ALERT
//					<< "Runtime< " << aRF.getRID().str()
//					<< "> :> fusion of Data Table Element FAILED : "
//						"(itFirstData[...] != itSndData[...]) :"
//					<< "\n\t$0 = " << refArray->at(offset).str()
//					<< "\n\t$1 = " << firstArray->at(offset).str()
//					<< "\n\t$2 = " << sndArray->at(offset).str()
//					<< SEND_ALERT;
//
//			return( BF::REF_NULL );
//		}
		else
		{
			// AvmConcurrencyStatement Failed
			AVM_OS_ERROR_ALERT
					<< "Runtime< " << aRF.getRID().str()
					<< "> :> fusion of Data Table Element FAILED : "
						"(itFirstData[...] != itSndData[...]) :"
					<< "\n\t$0 = " << refArray->at(offset).str()
					<< "\n\t$1 = " << firstArray->at(offset).str()
					<< "\n\t$2 = " << sndArray->at(offset).str()
					<< SEND_ALERT;

			return( BF::REF_NULL );
		}
	}

	return( bfArray );
}


bool AvmSynchronizationFactory::fusion(RuntimeForm & aRF,
		const TableOfBufferT & refBufferTable,
		const TableOfBufferT & firstBufferTable,
		const TableOfBufferT & sndBufferTable)
{
	// fusion of BUFFER
	if( firstBufferTable.valid() && sndBufferTable.valid() )
	{
		if( firstBufferTable == sndBufferTable )
		{
			aRF.setBufferTable( firstBufferTable );
		}
		else if( refBufferTable == firstBufferTable )
		{
			aRF.setBufferTable( sndBufferTable );
		}
		else if( refBufferTable == sndBufferTable )
		{
			aRF.setBufferTable( firstBufferTable );
		}
		else if( (refBufferTable.size() == firstBufferTable.size()) &&
				(refBufferTable.size() == sndBufferTable.size()) )
		{
			// Comparison between all data
			TableOfBufferT aBufferTable( refBufferTable.size() );

			TableOfBufferT::const_iterator itRef = refBufferTable.begin();
			TableOfBufferT::const_iterator itRefEnd = refBufferTable.end();
			TableOfBufferT::const_iterator itFirst = firstBufferTable.begin();
			TableOfBufferT::const_iterator itSnd = sndBufferTable.begin();

			std::size_t offset = 0;
			for( ; itRef != itRefEnd ; ++itRef , ++itFirst, ++itSnd, ++offset )
			{
				if( (*itRef)->equals( *(*itFirst) ) )
				{
					aBufferTable.assign( offset , (*itSnd) );
				}
				else if( (*itRef)->equals( *(*itSnd) ) )
				{
					aBufferTable.assign( offset , (*itFirst) );
				}
				else if( (*itFirst)->equals( *(*itSnd) ) ) // TODO Equality between Buffer
				{
					aBufferTable.assign( offset , (*itFirst) );
				}
				else
				{
					// AvmConcurrencyStatement Failed
					AVM_OS_ERROR_ALERT
							<< "Runtime< " << aRF.getRID().str()
							<< "> :> fusion of Buffer Table Element FAILED : "
								"(itFirstBuffer != itSndBuffer) :\n"
							<< (*itRef)->toString(AVM_TAB1_INDENT)
							<< (*itFirst)->toString(AVM_TAB1_INDENT)
							<< (*itSnd)->toString(AVM_TAB1_INDENT)
							<< SEND_ALERT;

					return( false );
				}
			}
			aRF.setBufferTable( aBufferTable );
		}
		else
		{
			// AvmConcurrencyStatement Failed
			AVM_OS_ERROR_ALERT
					<< "Runtime< " << aRF.getRID().str()
					<< "> :> fusion of Buffer Table Size FAILED : "
					"((refBufferTable->size() == firstBufferTable->size()) && "
					"(refBufferTable->size() == sndBufferTable->size())) :\n"
					<< refBufferTable.toString(AVM_TAB1_INDENT)
					<< firstBufferTable.toString(AVM_TAB1_INDENT)
					<< sndBufferTable.toString(AVM_TAB1_INDENT)
					<< SEND_ALERT;

			return( false );
		}
	}
	else if( refBufferTable.valid() )
	{
		// AvmConcurrencyStatement Failed
		AVM_OS_ERROR_ALERT
				<< "Runtime< " << aRF.getRID().str()
				<< "> :> fusion of Buffer Table FAILED : (refBufferTable != nullptr) "
				"&& ((firstBufferTable == nullptr) || (sndBufferTable == nullptr)) :\n"
				<< refBufferTable.toString(AVM_TAB1_INDENT)
				<< firstBufferTable.toString(AVM_TAB1_INDENT)
				<< sndBufferTable.toString(AVM_TAB1_INDENT)
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}


// TODO fusion ROUTER
bool AvmSynchronizationFactory::fusion(RuntimeForm & aRF,
		const Router & refRouter,
		const Router & firstRouter,
		const Router & sndRouter)
{
	// fusion of BUFFER
	if( firstRouter.valid() && sndRouter.valid() )
	{
		if( firstRouter == sndRouter )
		{
			aRF.setRouter( firstRouter );
		}
		else if( refRouter == firstRouter )
		{
			aRF.setRouter( sndRouter );
		}
		else if( refRouter == sndRouter )
		{
			aRF.setRouter( firstRouter );
		}
		else
		{
			aRF.setRouter( refRouter );
		}
	}
	else if( refRouter.valid() )
	{
		// AvmConcurrencyStatement Failed
		AVM_OS_ERROR_ALERT
				<< "Runtime< " << aRF.getRID().str()
				<< "> :> fusion of Router FAILED : (refRouter != nullptr) && "
				"((firstRouter == nullptr) || (sndRouter == nullptr)) :\n"
				<< refRouter.toString(AVM_TAB1_INDENT)
				<< firstRouter.toString(AVM_TAB1_INDENT)
				<< sndRouter.toString(AVM_TAB1_INDENT)
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}






BF AvmSynchronizationFactory::syncBF(const Operator * buildOp,
		const BF & refBF, const BF & frstBF, const BF & sndBF)
{
	if( refBF.invalid() )
	{
		BFCode buildCode(buildOp, frstBF, sndBF);

		return( AvmCodeFactory::flattenCode( buildCode ) );
	}
	else if( frstBF.isTEQ(sndBF) || refBF.isTEQ(sndBF) )
	{
		return( frstBF );
	}

	if( refBF.isTEQ(frstBF) )
	{
		return( sndBF );
	}

	else if( frstBF.is< AvmCode >() && sndBF.is< AvmCode >() &&
			(frstBF.to< AvmCode >().getOperator() ==
					sndBF.to< AvmCode >().getOperator()) )
	{
		const AvmCode & frstCode = frstBF.to< AvmCode >();
		const AvmCode & sndCode  = sndBF.to< AvmCode >();

		std::size_t frstSize = frstCode.size();
		std::size_t sndSize  = sndCode.size();


		if( refBF.valid() && refBF.isEQ(frstCode.first()) &&
				refBF.isEQ(sndCode.first()) )
		{
			BFCode newCode(buildOp);
			BFCode buildCode(frstCode.getOperator(), refBF, newCode);

			if( frstSize == 2 )
			{
				newCode->append( frstCode.second() );
			}
			else if( frstSize > 2 )
			{
				BFCode restCode(frstCode.getOperator());

				for( std::size_t offset = 1 ; offset < frstSize ; ++offset )
				{
					restCode->append( frstCode.at(offset) );
				}

				newCode->append( restCode );
			}

			if( sndSize == 2 )
			{
				newCode->append( sndCode.second() );
			}
			else if( sndSize > 2 )
			{
				BFCode restCode(sndCode.getOperator());

				for( std::size_t offset = 1 ; offset < sndSize ; ++offset )
				{
					restCode->append( sndCode.at(offset) );
				}

				newCode->append( restCode );
			}

			return( AvmCodeFactory::flattenCode( buildCode ) );
		}
		else if( refBF.is< AvmCode >() )
		{
			const BFCode & refCode  = refBF.bfCode();

			if( refCode->getOperator() == sndCode.getOperator() )
			{
				std::size_t refSize = refCode->size();

				BFCode buildCode( refCode->getOperator() );

				std::size_t k = 0;
				for( ; (k < refSize) && (k < frstSize) && (k < sndSize) ; ++k )
				{
					if( frstCode.at(k).isEQ(sndCode.at(k)) &&
							refCode->at(k).isEQ(sndCode.at(k)))
					{
						buildCode->append( refCode->at(k) );
					}
					else
					{
						break;
					}
				}

				BFCode newCode(buildOp);
				buildCode.append( newCode );

				if( frstSize == (k + 1) )
				{
					newCode->append( frstCode.last() );
				}
				else if( frstSize != k )
				{
					BFCode restCode(frstCode.getOperator());

					for( std::size_t idx = k ; idx < frstSize ; ++idx )
					{
						restCode->append( frstCode.at(idx) );
					}

					newCode->append( restCode );
				}

				if( sndSize == (k + 1) )
				{
					newCode->append( sndCode.last() );
				}
				else if( sndSize != k )
				{
					BFCode restCode(sndCode.getOperator());

					for( std::size_t idx = k ; idx < sndSize ; ++idx )
					{
						restCode->append( sndCode.at(idx) );
					}

					newCode->append( restCode );
				}

				return( AvmCodeFactory::flattenCode( buildCode ) );
			}
		}

		if( frstCode.first().isEQ(sndCode.first()) )
		{
			BFCode buildCode(frstCode.getOperator(),
					frstCode.first());

			std::size_t k = 1;
			for( ; (k < frstSize) && (k < sndSize) &&
					frstCode.at(k).isEQ(sndCode.at(k)) ; ++k )
			{
				buildCode->append( frstCode.at(k) );
			}

			BFCode newCode(buildOp);
			buildCode->append( newCode );

			if( frstSize == (k + 1) )
			{
				newCode->append( frstCode.last() );
			}
			else if( frstSize != k )
			{
				BFCode restCode(frstCode.getOperator());

				for( std::size_t idx = k ; idx < frstSize ; ++idx )
				{
					restCode->append( frstCode.at(idx) );
				}

				newCode->append( restCode );
			}

			if( sndSize == (k + 1) )
			{
				newCode->append( sndCode.last() );
			}
			else if( sndSize != k )
			{
				BFCode restCode(sndCode.getOperator());

				for( std::size_t idx = k ; idx < sndSize ; ++idx )
				{
					restCode->append( sndCode.at(idx) );
				}

				newCode->append( restCode );
			}

			return( AvmCodeFactory::flattenCode( buildCode ) );
		}
	}

	return( AvmCodeFactory::flattenCode( StatementConstructor::newCode(
			buildOp, frstBF, sndBF) ) );
}




BF AvmSynchronizationFactory::buildRunnableElementTrace(
		const Operator * buildOp, const BF & refRunnableElementTrace,
		const BF & frstRunnableElementTrace, const BF & sndRunnableElementTrace)
{
	return( syncBF(buildOp, refRunnableElementTrace,
			frstRunnableElementTrace, sndRunnableElementTrace) );
}

BF AvmSynchronizationFactory::buildIOElementTrace(
		const Operator * buildOp, const BF & refIOElementTrace,
		const BF & frstIOElementTrace, const BF & sndIOElementTrace)
{
	return( syncBF(buildOp, refIOElementTrace,
			frstIOElementTrace, sndIOElementTrace) );
}



}
