/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmDeadBranchPruner.h"
#include "AvmTestCaseUtils.h"

#include <famcore/api/AbstractProcessorUnit.h>

#include <fml/builtin/Identifier.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmDeadBranchPruner::AvmDeadBranchPruner(AbstractProcessorUnit & aProcessor)
: mProcessor(aProcessor),
INFO_DEAD_BRANCH_PRUNED( new Identifier("DEAD_BRANCH_PRUNED") ),
mTestPurposePassEC( nullptr ),
mNewfreshInitialParams(),
mDeadBranchNumber( 0 )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// QUIESCENCE
////////////////////////////////////////////////////////////////////////////////

void AvmDeadBranchPruner::pruneDeadBranch()
{
	ExecutionContext & rootEC =
			mProcessor.getConfiguration().getFirstExecutionTrace();

//!@! PREVIOUS GRAPH
	ExecutionContext * symbexGraph = rootEC.cloneGraph(nullptr, true);
	mProcessor.getConfiguration().appendExecutionTrace(symbexGraph);

//	for( const auto & aChildEC : rootQuiescenceGraph.getChildContexts()  )
//	{
//		checkDeterminism(*aChildEC);
//	}

	ExecutionContext::VectorOfConstPtr testPurposeTrace;
	AvmTestCaseUtils::getTestPurposeTrace(rootEC, testPurposeTrace);
	mTestPurposePassEC = testPurposeTrace.last();

	AvmTestCaseUtils::getInitialParameters(rootEC, mNewfreshInitialParams);

AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "DEAD_BRANCH PRUNING " ) << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )

	pruneDeadBranch(rootEC);
}


void AvmDeadBranchPruner::pruneDeadBranch(ExecutionContext & anEC)

{
	auto itChild = anEC.begin();
	const auto & endChild = anEC.end();
	for( ; itChild != endChild ; )
	{
		if( (*itChild)->hasChildContext() )
		{
			pruneDeadBranch(*(*itChild));
			++itChild;
		}
		else if( isDeadBranch(*(*itChild)) )
		{
			anEC.addInfo( mProcessor,
					BF(new Identifier("DEAD_BRANCH_PRUNED\n" + (*itChild)->str())) );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
AVM_OS_DEBUG << "DEAD_BRANCH_PRUNED :> " << (*itChild)->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

			itChild = anEC.eraseChildContext(itChild);
		}
		else
		{
			++itChild;
		}
	}

}


bool AvmDeadBranchPruner::isDeadBranch(ExecutionContext & anEC)
{
	InstanceOfData::Table boundParam( mNewfreshInitialParams );
	AvmTestCaseUtils::newfreshInoutParamsOfEC(anEC, boundParam);
	AvmTestCaseUtils::newfreshDurationParamsOfEC(anEC, boundParam);

	BF condition;
	if( boundParam.empty() )
	{
		condition = ExpressionConstructor::andExpr(
				anEC.getAllPathCondition(),
				mTestPurposePassEC->getAllPathCondition());
	}
	else
	{
		condition = ExpressionConstructor::andExpr(
				ExpressionConstructor::existsExpr(
						boundParam,
						anEC.getAllPathCondition()
				),
				ExpressionConstructor::existsExpr(
						boundParam,
						mTestPurposePassEC->getAllPathCondition()
				)
		);
	}

	return not SolverFactory::isStrongSatisfiable(condition, true);
}

} /* namespace sep */
