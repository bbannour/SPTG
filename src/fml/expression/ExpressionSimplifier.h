/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 janv. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXPRESSIONSIMPLIFIER_H_
#define EXPRESSIONSIMPLIFIER_H_

#include <common/BF.h>

#include <collection/Vector.h>

#include <fml/expression/AvmCode.h>


namespace sep
{


class ExpressionSimplifier
{

public:

	////////////////////////////////////////////////////////////////////////////
	// ARITHMETIC SIMPLIFIER
	////////////////////////////////////////////////////////////////////////////

	static BF PLUS(const BF & lhs, const BF & rhs);
	static BF PLUS(Vector< BF > & args);

	static BF MINUS(const BF & lhs, const BF & rhs);

	static BF UMINUS(const BF & arg);

	static BF MULT(const BF & lhs, const BF & rhs);
	static BF MULT(Vector< BF > & args);

	static BF POW(const BF & lhs, const BF & rhs);

	static BF DIV(const BF & lhs, const BF & rhs);


	////////////////////////////////////////////////////////////////////////////
	// COMPARER SIMPLIFIER
	////////////////////////////////////////////////////////////////////////////

	static BF EQ(const BF & lhs, const BF & rhs);
	static BF NEQ(const BF & lhs, const BF & rhs);

	static BF SEQ(const BF & lhs, const BF & rhs);
	static BF NSEQ(const BF & lhs, const BF & rhs);

	static BF LT(const BF & lhs, const BF & rhs);
	static BF LTE(const BF & lhs, const BF & rhs);

	static BF GT(const BF & lhs, const BF & rhs);
	static BF GTE(const BF & lhs, const BF & rhs);


	////////////////////////////////////////////////////////////////////////////
	// LOGIC SIMPLIFIER
	////////////////////////////////////////////////////////////////////////////

	static BF NOT(const BF & arg);

	static BF AND(const BF & lhs, const BF & rhs);
	static BF AND(Vector< BF > & args);

	static BF NAND(const BF & lhs, const BF & rhs);
	static BF NAND(Vector< BF > & args);

	static BF XAND(const BF & lhs, const BF & rhs);
	static BF XAND(Vector< BF > & args);

	static BF OR(const BF & lhs, const BF & rhs);
	static BF OR(Vector< BF > & args);

	static BF NOR(const BF & lhs, const BF & rhs);
	static BF NOR(Vector< BF > & args);

	static BF XOR(const BF & lhs, const BF & rhs);
	static BF XOR(Vector< BF > & args);

	static BF XNOR(const BF & lhs, const BF & rhs);
	static BF XNOR(Vector< BF > & args);


	////////////////////////////////////////////////////////////////////////////
	// PREDICATE SIMPLIFIER
	////////////////////////////////////////////////////////////////////////////

	static BF simplif(const BF & expr);

	static BF simplif_and(const BF & arg0, const BF & arg1);

	static BF simplif_or(const BF & arg0, const BF & arg1);

	static BF simplif_not(const BF & arg0);

};


} /* namespace sep */
#endif /* EXPRESSIONSIMPLIFIER_H_ */
