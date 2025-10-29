/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef AVMCODE_2_PUML_H_
#define AVMCODE_2_PUML_H_

#include <fml/expression/AvmCode.h>

namespace sep
{

class AvmCode2Puml final
{
	friend AvmCode;

public:
	/**
	 * PRETTY PRINTER WRAP
	 */
	static OutStream & toStream(OutStream & out, const AvmCode & aCode);

protected:
	static void prettyPrinter(OutStream & out,
			const AvmCode & aCode, bool isStatement = true);

	static void prettyPrinterBasicStatement(OutStream & out,
			const AvmCode & aCode, bool isStatement = true);

	static void prettyPrinterBlockStatement(OutStream & out,
			const AvmCode & aCode, bool isStatement = true);

	static void prettyPrinterDefault(OutStream & out,
			const AvmCode & aCode, bool isStatement = true);

	static void prettyPrinterFunctional(OutStream & out,
			const AvmCode & aCode, bool isExpression = true);
	static void prettyPrinterInfix(OutStream & out, const AvmCode & aCode,
			bool isExpression = true, bool isWrap = false);
	static void prettyPrinterPrefix(OutStream & out,
			const AvmCode & aCode, bool isExpression = true);
	static void prettyPrinterSuffix(OutStream & out,
			const AvmCode & aCode, bool isExpression = true);

	static void prettyPrinter(OutStream & out,
			const BF & arg, bool isStatement = true);

	static void prettyPrinter(OutStream & out,
			const BF & arg, const BaseTypeSpecifier & aType);

	static void prettyPrinterCondition(OutStream & out, const BF & arg);

	static void prettyPrinterBlock(OutStream & out, const BF & arg);
};

}

#endif /*AVMCODE_2_PUML_H_*/
