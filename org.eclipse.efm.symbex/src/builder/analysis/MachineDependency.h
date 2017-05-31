/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 juil. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef MACHINEDEPENDENCY_H_
#define MACHINEDEPENDENCY_H_

namespace sep
{


class BF;

class AvmCode;

class AvmLambda;
class AvmProgram;
class ExecutableForm;
class ExecutableSystem;


class MachineDependency
{

public:

	static bool computeVariableDependency(ExecutableSystem * anExecSystem);


	static bool computeVariableDependency(ExecutableForm * anExecutable);

	static bool isVariableDependency(
			ExecutableForm * anExecutable, AvmCode * aCode);
	static bool isVariableDependency(
			ExecutableForm * anExecutable, const BF & aVar);


	static bool computeVariableDependency(AvmProgram * aProgram);

	static bool isVariableDependency(
			AvmProgram * aProgram, AvmCode * aCode);
	static bool isVariableDependency(
			AvmProgram * aProgram, const BF & aVar);


	static bool computeVariableDependency(AvmLambda * aLambda);

	static bool isVariableDependency(
			AvmLambda * aLambda, AvmCode * aCode);

	static bool isVariableDependency(
			AvmLambda * aLambda, const BF & aVar);


};

} /* namespace sep */
#endif /* MACHINEDEPENDENCY_H_ */
