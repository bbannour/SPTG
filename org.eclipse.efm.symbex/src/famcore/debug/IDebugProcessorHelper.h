/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 30 avr. 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef IDEBUGPROCESSORHELPER_H_
#define IDEBUGPROCESSORHELPER_H_

#include <cstdint>
#include <string>


namespace sep
{

class ExecutionContext;


class IDebugProcessorHelper
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IDebugProcessorHelper()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~IDebugProcessorHelper()
	{
		//!! NOTHING
	}


	/**
	 * UTILS
	 */
	static const ExecutionContext * searchContext(
			const ExecutionContext * anEC, std::uint32_t ctxID);

	static bool hasExecutionContextTag(
			const ExecutionContext & anEC, const std::string & strFlag);

};


} /* namespace sep */

#endif /* IDEBUGPROCESSORHELPER_H_ */
