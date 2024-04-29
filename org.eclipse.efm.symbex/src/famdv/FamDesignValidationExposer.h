/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 juin 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_EXPOSER_H_
#define FAM_EXPOSER_H_

#include <string>

namespace sep
{

class OutStream;


class FamDesignValidationExposer
{

protected:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	FamDesignValidationExposer()
	{
		//!!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~FamDesignValidationExposer()
	{
		//!!! NOTHING
	}


public:

	////////////////////////////////////////////////////////////////////////////
	// EXPORTED FAM LIST
	////////////////////////////////////////////////////////////////////////////

	static void toStreamExported(OutStream & out,
			const std::string & header = "export processors");


};



} /* namespace sep */
#endif /* FAM_EXPOSER_H_ */
