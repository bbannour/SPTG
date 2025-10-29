/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCtorPrimitive.h"

#include <computer/EvaluationEnvironment.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>


namespace sep
{


bool AvmPrimitive_Ctor::seval(EvaluationEnvironment & ENV)
{
	const BF & type = ENV.inCODE->first();

	const BaseTypeSpecifier & typeSpecifier = type.to< BaseTypeSpecifier >();

	if( ENV.seval( ENV.inCODE->second() ) )
	{
		switch( typeSpecifier.getTypeSpecifierKind() )
		{
			case TYPE_STRING_SPECIFIER:
			{
				ENV.outVAL = ExpressionConstructor::newString( ENV.outVAL.str() );

				return( true );
			}
			case TYPE_ENUM_SPECIFIER:
			{
				const EnumTypeSpecifier & enumT =
						typeSpecifier.to< EnumTypeSpecifier >();

				ENV.outVAL = enumT.getSymbolDataByValue( ENV.outVAL );

				if( ENV.outVAL.invalid() )
				{
					ENV.outVAL = BFCode(
							OperatorManager::OPERATOR_CTOR, type, ENV.outVAL);
				}

				return( true );
			}
			case TYPE_CHARACTER_SPECIFIER:
			{
				const std::string & value = ENV.outVAL.is< String >()
						? ENV.outVAL.to< String >().getValue()
						: ENV.outVAL.str();

				if( not value.empty() )
				{
					ENV.outVAL = ExpressionConstructor::newChar(value[0]);

					return true;
				}

				return false;
			}

			case TYPE_BOOLEAN_SPECIFIER:
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						ENV.outVAL.valid() && (not  ENV.outVAL.isEqualZero()) );

				return( true );
			}
			case AVM_ARG_INTEGER_KIND:
			{
				if( ENV.outVAL.isNumeric() )
				{
					ENV.outVAL = ExpressionConstructor::newInteger(
							ENV.outVAL.toInteger() );
				}
				else
				{
					ENV.outVAL = BFCode(
							OperatorManager::OPERATOR_CTOR, type, ENV.outVAL);
				}

				return true;
			}
			case AVM_ARG_RATIONAL_KIND:
			{
				if( ENV.outVAL.isNumeric() )
				{
					ENV.outVAL = ExpressionConstructor::newExprRational(
							ENV.outVAL.str() );
				}
				else
				{
					ENV.outVAL = BFCode(
							OperatorManager::OPERATOR_CTOR, type, ENV.outVAL);
				}

				return true;
			}
			case AVM_ARG_FLOAT_KIND:
			{
				if( ENV.outVAL.isNumeric() )
				{
					ENV.outVAL = ExpressionConstructor::newFloat(
							ENV.outVAL.toFloat() );
				}
				else
				{
					ENV.outVAL = BFCode(
							OperatorManager::OPERATOR_CTOR, type, ENV.outVAL);
				}

				return true;
			}

			default:
			{
				ENV.outVAL = BFCode(
						OperatorManager::OPERATOR_CTOR, type, ENV.outVAL);

				return true;
			}
		}
	}

	return( false );
}


} /* namespace sep */
