/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 déc. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXPRESSIONEVAL_H_
#define EXPRESSIONEVAL_H_

#include <common/BF.h>



namespace sep
{


class AvmCode;



class ExpressionEval
{

public:

	static BF value(const BFCode & aCode, bool destroy_arg = true);


	static BF random(const BF & aCode);

	static BF abs(const BF & aCode);
	static BF ceil(const BF & aCode);
	static BF floor(const BF & aCode);
	static BF round(const BF & aCode);
	static BF truncate(const BF & aCode);


	static BF min(const BF & frst, const BF & snd);
	static BF max(const BF & frst, const BF & snd);

	static BF min(const BFCode & aCode);
	static BF max(const BFCode & aCode);


	static BF mod(const BF & aCode1, const BF & aCode2);

	static BF sqrt(const BF & aCode);

	static BF exp(const BF & aCode);
	static BF ln(const BF & aCode);
	static BF log(const BF & aCode);

	static BF sin(const BF & aCode);
	static BF cos(const BF & aCode);
	static BF tan(const BF & aCode);

	static BF sinh(const BF & aCode);
	static BF cosh(const BF & aCode);
	static BF tanh(const BF & aCode);

	static BF asin(const BF & aCode);
	static BF acos(const BF & aCode);
	static BF atan(const BF & aCode);
	static BF atan2(const BF & aCode1, const BF & aCode2);

	static BF asinh(const BF & aCode);
	static BF acosh(const BF & aCode);
	static BF atanh(const BF & aCode);



};

}

#endif /* EXPRESSIONEVAL_H_ */
