/*******************************************************************************
 * Copyright (c) 2020 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2020
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef SERVER_GRPC_SYMBEXSERVERWORKFLOWUTILS_H_
#define SERVER_GRPC_SYMBEXSERVERWORKFLOWUTILS_H_

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include <string>


namespace sep
{

namespace grpc
{
	class ModelDefinitionRequest;
}


class SymbexServerWorkflowUtils
{

public:

	static const std::string & WORKSPACE_FOLDER_NAME;

	static const std::string & RAW_TEXT_SEW_FILE_PATH;

	static const std::string & RAW_TEXT_MODEL_FILE_PATH;

	static const std::string & PATTERN_FILE_PATH;

	static const std::string & PATTERN_FILE_BASENAME;

	static const std::string & DEFAULT_GENERIC_SEW;


	static inline std::string getDefaultSEW(const std::string & sewPath)
	{
		return prepareSEW(DEFAULT_GENERIC_SEW , sewPath);
	}

	static std::string prepareSEW(
			const std::string & textualSEW, const std::string & sewPath);


	static bool prepareWorkspaceFolder();

	static std::string saveRawTextModel(const std::string & rawTextModel);


	static std::string getSEW(
			const grpc::ModelDefinitionRequest * request,
			const std::string & modelFileLocation);

};

} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

#endif /* SERVER_GRPC_SYMBEXSERVERWORKFLOWUTILS_H_ */
