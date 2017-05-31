/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 juil. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "IntervalTypeSpecifier.h"

#include <fml/expression/ExpressionConstructorImpl.h>

#include <fml/type/TypeManager.h>

namespace sep
{


/**
 * CONSTRAINT generation
 * for a given parameter
 */
BF IntervalTypeSpecifier::minConstraint(const BF & aParam) const
{
	switch( getIntervalKind() )
	{
		case IIntervalKind::CLOSED:
		case IIntervalKind::ROPEN:
		{
			return( ExpressionConstructorNative::gteExpr(aParam, getInfimum()) );
		}

		case IIntervalKind::OPEN:
		case IIntervalKind::LOPEN:
		default:
		{
			return( ExpressionConstructorNative::gtExpr(aParam, getInfimum()) );
		}
	}
}


BF IntervalTypeSpecifier::maxConstraint(const BF & aParam) const
{
	switch( getIntervalKind() )
	{
		case IIntervalKind::CLOSED:
		case IIntervalKind::LOPEN:
		{
			return( ExpressionConstructorNative::lteExpr(aParam, getSupremum()) );
		}

		case IIntervalKind::ROPEN:
		case IIntervalKind::OPEN:
		default:
		{
			return( ExpressionConstructorNative::ltExpr(aParam, getSupremum()) );
		}
	}
}


BF IntervalTypeSpecifier::genConstraint(const BF & aParam) const
{
	if( hasConstraint() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "TODO << IntervalTypeSpecifier::genConstraint( "
				<< aParam << " ) >> with compiled constraint:" << std::endl
				<< getConstraint()
				<< SEND_EXIT;
	}

	switch( getIntervalKind() )
	{
		case IIntervalKind::CLOSED:
		{
			return( ExpressionConstructorNative::andExpr(
					ExpressionConstructorNative::gteExpr(aParam, getInfimum()),
					ExpressionConstructorNative::lteExpr(aParam, getSupremum())) );
		}

		case IIntervalKind::LOPEN:
		{
			return( ExpressionConstructorNative::andExpr(
					ExpressionConstructorNative::gtExpr(aParam, getInfimum()),
					ExpressionConstructorNative::lteExpr(aParam, getSupremum())) );
		}

		case IIntervalKind::ROPEN:
		{
			return( ExpressionConstructorNative::andExpr(
					ExpressionConstructorNative::gteExpr(aParam, getInfimum()),
					ExpressionConstructorNative::ltExpr(aParam, getSupremum())) );
		}

		case IIntervalKind::OPEN:
		default:
		{
			return( ExpressionConstructorNative::andExpr(
					ExpressionConstructorNative::gtExpr(aParam, getInfimum()),
					ExpressionConstructorNative::ltExpr(aParam, getSupremum())) );
		}
	}
}


/**
 * Serialization
 */
std::string IntervalTypeSpecifier::strT() const
{
	if( getFullyQualifiedNameID().empty() || getNameID().empty() )
	{
		return( strIso() );
	}
	else
	{
		return( getNameID() );
	}
}


void IntervalTypeSpecifier::toStream(OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(os);

		return;
	}

	os << TAB << "type " << getFullyQualifiedNameID() << " interval< "
			<< mSupportTypeSpecifier.strT() << strIso() << " >";

	if( hasConstraint() )
	{
		os << " {" << EOL_TAB2 << "@constraint {" << EOL_INCR2_INDENT;
		getConstraint().toStream(os);
		os << DECR2_INDENT_TAB2 << "}" << EOL_TAB << "}";
	}
	else
	{
		os << ";";
	}

	os << EOL_FLUSH;
}


}


