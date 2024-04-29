/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 juil. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include <famcore/api/BaseCoverageFilter.h>
#include <famcore/StatemachineReachability.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>

#include <fml/infrastructure/BehavioralPart.h>

#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{

/**
 * Backward Reachability Analysis
 */
bool StatemachineReachability::computeBackwardReachableComponent(
		const Configuration & aConfiguration)
{
	std::size_t currentBackwardDepth = 0;

	AvmTransition * aCompiledTransition;
	InstanceOfMachine * aSourceState;

	const TableOfExecutableForm & executables =
			aConfiguration.getExecutableSystem().getExecutables();

	ListOfExecutableForm listOfTreatedStates;

	TableOfExecutableForm::const_raw_iterator itExec = executables.begin();
	TableOfExecutableForm::const_raw_iterator endExec = executables.end();

	if( mBackwardAnalysisLookaheadDepth >= 1 )
	{
		ExecutableQuery XQuery( aConfiguration );

		// Pour tous les états itExec
		//	on rajoute  les transitions immédiatement entrantes dans BackwardReachableTransition
		for( ; itExec != endExec ; ++itExec )
		{
			if( (itExec)->hasPrototypeInstance() )
			{
				const Machine & aMachine = (itExec)->getAstMachine();
				if( aMachine.hasIncomingTransition() )
				{
					// Pour l'état itExec on rajoute :
					// - les transitions entrantes à la liste des BackwardReachableTransition
					// - les états sources des transitions entrantes à la liste des BackwardReachableMachine
					//
					for( const auto & itTransition :
							aMachine.getBehavior()->getIncomingTransitions() )
					{
						aCompiledTransition = XQuery.getTransitionByAstElement(
							itTransition.to< Transition >()).to_ptr< AvmTransition >();
						(itExec)->addBackwardReachableTransition( aCompiledTransition );

						aSourceState = aCompiledTransition->
								getExecutableContainer()->getPrototypeInstance();
						if( (aSourceState != nullptr)
							&& ((itExec) != aSourceState->getExecutable())
							&& (not (itExec)->getBackwardReachableMachine().
									contains( aSourceState )) )
						{
							(itExec)->addBackwardReachableMachine( aSourceState );
						}
					}
				}
			}
		}
		currentBackwardDepth = 1;
	}

	if( mBackwardAnalysisLookaheadDepth > currentBackwardDepth )
	{
		// Pour tous les états itExec, on ajoute par récursivité :
		//	- les transitions arrières non directement entrantes
		//    dans BackwardReachableTransition
		//	- les états sources de toutes les transitions arrières
		//    non directement entrantes dans BackwardReachableMachine
		//
		for( itExec = executables.begin() ; itExec != endExec ; ++itExec )
		{
			if( (itExec)->hasPrototypeInstance() )
			{
				computeBackwardReachableComponent( aConfiguration,
						(itExec), listOfTreatedStates, currentBackwardDepth );
			}
		}
	}

	// Pour tous les états itExec :
	//    élimination de l'état itExec dans la liste BackwardReachableMachine
	//
	for( itExec = executables.begin() ; itExec != endExec ; ++itExec )
	{
		if( (itExec)->hasPrototypeInstance() )
		{
			if( (itExec)->getBackwardReachableMachine().nonempty() )
			{
				(itExec)->removeBackwardReachableMachine(
						(itExec)->getPrototypeInstance() );
			}

			if( (itExec)->hasTransition()
				&& (not (itExec)->getSpecifier().
						isPseudostateInitialOrStateStart())
				&& (not (itExec)->hasBackwardReachableMachine()) )
			{
				(itExec)->setReachableState( false );
			}
		}
	}



	//	Affichage du résultat dans le fichier trace
	//
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )

	AVM_OS_TRACE << AVM_TAB1_INDENT;

	for( itExec = executables.begin() ; itExec != endExec ; ++itExec )
	{
		if( (itExec)->hasPrototypeInstance() )
		{
			AVM_OS_TRACE << "Statemachine Reachability:> "
					"compute backward reachable state/transition"
					<< std::endl
					<< TAB << "state :> "
					<< (itExec)->getFullyQualifiedNameID()
					<< std::endl
					<< "nb backward states :> "
					<< (itExec)->getBackwardReachableMachine().size()
					<< std::endl
					<< "nb backward transitions :> "
					<< (itExec)->getBackwardReachableTransition().size()
					<< std::endl;

	AVM_IF_DEBUG_LEVEL_GTE_HIGH
			ListOfInstanceOfMachine::iterator itState =
					(itExec)->getBackwardReachableMachine().begin();
			ListOfInstanceOfMachine::iterator endState =
					(itExec)->getBackwardReachableMachine().end();
			for( ; itState != endState ; ++itState )
			{
				AVM_OS_TRACE << TAB2 << "backward state :> "
						<< (* itState)->getFullyQualifiedNameID()
						<< std::endl;
			}
	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH

	AVM_IF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
			ListOfAvmTransition::iterator itTransition =
					(itExec)->getBackwardReachableTransition().begin();
			ListOfAvmTransition::iterator endTransition =
					(itExec)->getBackwardReachableTransition().end();
			for( ; itTransition != endTransition ; ++itTransition )
			{
				AVM_OS_TRACE << TAB2 << "backward transition :> "
						<< (* itTransition)->getFullyQualifiedNameID()
						<< std::endl;
			}
	AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , TRANSITION )
		}
	}

	AVM_OS_TRACE << END_INDENT;

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , CONFIGURING )

	return( true );
}


void StatemachineReachability::computeBackwardReachableComponent(
		const Configuration & aConfiguration, ExecutableForm * aState,
		ListOfExecutableForm & aListOfTreatedStates,
		std::size_t theCurrentBackwardDepth)
{

//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_TRACE << "\t" << "state :> " << aState->getFullyQualifiedNameID()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	AvmTransition * aCompiledTransition;
	ExecutableForm * aSourceState;
	ExecutableForm * aContainerState;

	const Machine & aMachine = aState->getAstMachine();
	if( aMachine.hasIncomingTransition() )
	{
		ExecutableQuery XQuery( aConfiguration );

		theCurrentBackwardDepth += 1;

		// Pour chaque transition entrante
		for( const auto & itTransition :
				aMachine.getBehavior()->getIncomingTransitions() )
		{
			aCompiledTransition = XQuery.getTransitionByAstElement(
				itTransition.to< Transition >()).to_ptr< AvmTransition >();
			aSourceState = aCompiledTransition->getExecutableContainer();

			if( aSourceState->getSpecifier().
					isPseudostateInitialOrStateStart() )
			{
				aContainerState = aSourceState->getExecutableContainer();
				if( not aListOfTreatedStates.contains( aContainerState ) )
				{
					aListOfTreatedStates.append( aContainerState );
					if( mBackwardAnalysisLookaheadDepth > theCurrentBackwardDepth )
					{
						computeBackwardReachableComponent(
								aConfiguration, aContainerState,
								aListOfTreatedStates, theCurrentBackwardDepth );
					}

//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_TRACE << "\t" << "aContainerState :> "
//			<< aContainerState->getFullyQualifiedNameID() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				}
				aState->addBackwardReachableTransition(
						aContainerState->getBackwardReachableTransition() );
				aState->addBackwardReachableMachine(
						aContainerState->getBackwardReachableMachine() );
			}
			else
			{
				if( not aListOfTreatedStates.contains( aSourceState ) )
				{
					aListOfTreatedStates.append( aSourceState );
					if( mBackwardAnalysisLookaheadDepth > theCurrentBackwardDepth )
					{
						computeBackwardReachableComponent(
								aConfiguration, aSourceState,
								aListOfTreatedStates, theCurrentBackwardDepth );
					}

//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_TRACE << "\t" << "aSourceState :> "
//			<< aSourceState->getFullyQualifiedNameID() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				}
				aState->addBackwardReachableTransition(
						aSourceState->getBackwardReachableTransition() );
				aState->addBackwardReachableMachine(
						aSourceState->getBackwardReachableMachine() );
			}
		}
	}
}


/**
 * Forward Reachability Analysis
 */
bool StatemachineReachability::computeForwardReachableComponent(
		const Configuration & aConfiguration)
{
	const TableOfExecutableForm & executables =
			aConfiguration.getExecutableSystem().getExecutables();

	ListOfInstanceOfMachine::iterator itMachine;
	ListOfInstanceOfMachine::iterator endMachine;

	TableOfExecutableForm::const_raw_iterator itExec = executables.begin();
	TableOfExecutableForm::const_raw_iterator endExec = executables.end();
	for( ; itExec != endExec ; ++itExec )
	{
		if( (itExec)->getSpecifier().
				isPseudostateInitialOrStateStart() )
		{
			ListOfExecutableForm aTraceMachine( (itExec) );

			computeForwardReachableComponent(
					(itExec), aTraceMachine, (itExec));

			itMachine = (itExec)->getForwardReachableMachine().begin();
			endMachine = (itExec)->getForwardReachableMachine().end();
			for( ; itMachine != endMachine ; ++itMachine )
			{
				if( (*itMachine) != nullptr )
				{
					ListOfExecutableForm newTraceMachine(
							(*itMachine)->getExecutable() );

					computeForwardReachableComponent(
							(*itMachine)->getExecutable(),
							newTraceMachine, (*itMachine)->getExecutable());
				}
			}
		}
	}

	for( itExec = executables.begin() ; itExec != endExec ; ++itExec )
	{
		if( (itExec)->getForwardReachableMachine().nonempty() &&
				(itExec)->hasPrototypeInstance()  )
		{
			(itExec)->removeForwardReachableMachine(
					(itExec)->getPrototypeInstance() );
		}
	}

	return( true );
}


void StatemachineReachability::computeForwardReachableComponent(
		ExecutableForm * execMachine,
		ListOfExecutableForm & aTraceMachine, ExecutableForm * fwdMachine)
{
	ListOfAvmTransition listOfOutgoingTransition;
	fwdMachine->getOutgoingTransition( listOfOutgoingTransition );

	ListOfInstanceOfMachine listOfOutgoingMachine;
	fwdMachine->getOutgoingMachine( listOfOutgoingMachine );

	execMachine->addForwardReachableMachine(listOfOutgoingMachine);

	execMachine->addForwardReachableTransition(listOfOutgoingTransition);

	for( const auto & itOutgoing : listOfOutgoingMachine )
	{
		if( not aTraceMachine.contains( itOutgoing->getExecutable() ) )
		{
			ListOfExecutableForm newTraceMachine( aTraceMachine );

			newTraceMachine.append( itOutgoing->getExecutable() );

			computeForwardReachableComponent(execMachine,
					newTraceMachine, itOutgoing->getExecutable());
		}
	}
}

} /* namespace sep */
