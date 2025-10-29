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

#ifndef AVM_OUTPUT_NORMALIZER_H_
#define AVM_OUTPUT_NORMALIZER_H_

#include <common/BF.h>

#include <map>
#include <vector>


namespace sep
{

class BaseEnvironment;
class ExecutionEnvironment;
class ExecutionContext;
class InstanceOfPort;

class BFCode;


class AvmOutputNormalizer
{

public:
	/**
	 * CONSTANT
	 */
	static const std::string DEFAULT_VAR_PREFIX_NAME_OUTPUT_ARG;

	/**
	 * ATTRIBUTE
	 */
	BaseEnvironment & mENV;

	std::vector< std::map< const InstanceOfPort * , std::vector<BF> > > mNewfreshParamsHeightMap;

	std::string mNewfreshArgPrefixName;
	std::size_t mNewfreshArgIndex;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmOutputNormalizer(BaseEnvironment & ENV)
	: mENV( ENV ),
	mNewfreshParamsHeightMap( ),
	mNewfreshArgPrefixName( DEFAULT_VAR_PREFIX_NAME_OUTPUT_ARG ),
	mNewfreshArgIndex( 0 )
	{
		mNewfreshParamsHeightMap.emplace( mNewfreshParamsHeightMap.end() );

		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmOutputNormalizer()
	{
		//!! NOTHING
	}

	void setNewfreshArgPrefixName(const std::string & aNewfreshArgPrefixName) {
		this->mNewfreshArgPrefixName = aNewfreshArgPrefixName;
	}

	bool getOutportParameters(std::size_t height,
			const std::string & portID, std::vector<BF> & mewfreshParams);


	inline std::string newFreshOutportParameter()
	{
		return (OSS() << mNewfreshArgPrefixName << ++mNewfreshArgIndex);
	}

	bool normalizeSymbexOf(ExecutionContext & anEC);

	bool normalizeSymbexOuput(ExecutionContext & anEC, const BFCode & comTrace);
};


} /* namespace sep */

#endif /* AVM_OUTPUT_NORMALIZER_H_ */
