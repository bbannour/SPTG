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

#include "AvmOutputNormalizer.h"
#include "AvmTestCaseUtils.h"

#include <computer/BaseEnvironment.h>
#include <computer/PathConditionProcessor.h>

#include  <famcore/api/AbstractProcessorUnit.h>

#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/AvmCodeFactory.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/expression/StatementTypeChecker.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{

const std::string AvmOutputNormalizer::DEFAULT_VAR_PREFIX_NAME_OUTPUT_ARG = "$_";

bool AvmOutputNormalizer::getOutportParameters(std::size_t height,
		const std::string & portID, std::vector<BF> & mewfreshParams)
{
	for( auto & portNewfreshParams : mNewfreshParamsHeightMap[height] )
	{
		if( portNewfreshParams.first->getNameID() == portID )
		{
			mewfreshParams.insert(mewfreshParams.begin(),
					portNewfreshParams.second.begin(), portNewfreshParams.second.end());
			return true;
		}
	}
	return false;
}


bool AvmOutputNormalizer::normalizeSymbexOf(ExecutionContext & anEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << "Normalization " + anEC.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	mNewfreshParamsHeightMap.emplace( mNewfreshParamsHeightMap.end() );

	for( auto & aChildEC : anEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			if( comTrace.invalid() )
			{
				continue;
			}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "\tNormalize of child " + aChildEC->str() << std::endl;
	AVM_OS_DEBUG << "\t\tComStatement:> " << comTrace;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

			if( StatementTypeChecker::isOutput(comTrace) )
			{
				if( not normalizeSymbexOuput(*aChildEC, comTrace) )
				{
					return false;
				}
			}
		}
	}

	return true;
}

bool AvmOutputNormalizer::normalizeSymbexOuput(
		ExecutionContext & anEC, const BFCode & comTrace)
{
	BFList newfreshParamsList;
	ExecutionData & anED = anEC.getwExecutionData();

	const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

	BF freshParam;
	std::vector<BF> * freshParamArray;
	std::uint32_t height = anEC.getHeight();
	auto foundIt = mNewfreshParamsHeightMap[height].find(&comPort);
	if( foundIt != mNewfreshParamsHeightMap[height].end() )
	{
		freshParamArray = & foundIt->second;
	}
	else
	{
//		freshParamArray = &( mNewfreshParamsHeightMap[height].emplace(&comPort, std::vector<BF>()).first->second );
		freshParamArray = & mNewfreshParamsHeightMap[height][&comPort];

		const std::size_t count = comPort.getParameterCount();
		for( std::size_t offset = 0 ;  offset < count ; ++offset)
		{
//			const std::string & newParamID = (OSS() << "y_" << comPort.getNameID()
//					<< "_obs_h_" << (anEC.getHeight() - 1) << "_arg_" << (offset + 1));
			const std::string & newParamID = newFreshOutportParameter();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "\t\tnewfresh paramID :> " << newParamID << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

			auto portParameter = comPort.getParameter(offset);

			freshParam = mENV.create(anED.getRID(), newParamID,
					comPort.getParameterType(offset), BF::REF_NULL);

			(*freshParamArray).push_back(freshParam);

			newfreshParamsList.append( freshParam );
		}
	}

	auto itArg = comTrace.getOperands().begin();
	const auto & endArg = comTrace.getOperands().end();
	std::size_t offset = 0;
	for( ++itArg ; itArg != endArg ; ++itArg, ++offset)
	{
		freshParam = (*freshParamArray)[offset];

		BF identCond = ExpressionConstructor::eqExpr(freshParam, *itArg);
		PathConditionProcessor::addPathCondition(anED, identCond);

		comTrace->set(offset + 1, freshParam);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "\t\tidentCond :> " << identCond << std::endl;
	AVM_OS_DEBUG << "\t\tnewfresh PC :> " << anED.getPathCondition() << std::endl;
	AVM_OS_DEBUG << "\t\tnewfresh comStatement :> " << comTrace << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	}

	anED.appendParameters( newfreshParamsList );

	return true;
}


} /* namespace sep */
