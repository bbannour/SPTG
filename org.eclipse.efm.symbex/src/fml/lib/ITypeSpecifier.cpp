/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 févr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ITypeSpecifier.h"

#include <common/BF.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>


namespace sep
{

///////////////////
// CLOCK TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedClockInteger() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER)
			&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
				|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().weaklyTypedInteger() ) );
}

bool ITypeSpecifier::weaklyTypedClockRational() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER)
			&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
				|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().weaklyTypedRational() ) );
}

bool ITypeSpecifier::weaklyTypedClockFloat() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER)
			&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
				|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().weaklyTypedFloat() ) );
}


bool ITypeSpecifier::weaklyTypedClockReal() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER)
			&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
				|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().weaklyTypedReal() ) );
}


///////////////////
// TIME TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedTimeInteger() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_DISCRETE_TIME_SPECIFIER)
			|| ( referedTypeSpecifier.hasTypedTime()
				&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
					|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedInteger() ) ) );
}


bool ITypeSpecifier::weaklyTypedTimeRational() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.hasTypedTime()
			&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
				|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().weaklyTypedRational() ) );
}

bool ITypeSpecifier::weaklyTypedTimeFloat() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_DENSE_TIME_SPECIFIER)
			|| ( referedTypeSpecifier.hasTypedTime()
				&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
					|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedFloat() ) ) );
	}

bool ITypeSpecifier::weaklyTypedTimeReal() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_DENSE_TIME_SPECIFIER)
			|| ( referedTypeSpecifier.hasTypedTime()
				&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
					|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedReal() ) ) );
}


///////////////////
// CLOCK/TIME TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedClockTimeInteger() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_DISCRETE_TIME_SPECIFIER)
			|| ( referedTypeSpecifier.hasTypedClockTime()
				&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
					|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedInteger() ) ) );
}

bool ITypeSpecifier::weaklyTypedClockTimeRational() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.hasTypedClockTime()
			&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
				|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().weaklyTypedRational() ) );
}

bool ITypeSpecifier::weaklyTypedClockTimeFloat() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_DENSE_TIME_SPECIFIER)
				|| ( referedTypeSpecifier.hasTypedClockTime()
					&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
							&& referedTypeSpecifier.to< ContainerTypeSpecifier >()
						.getContentsTypeSpecifier().weaklyTypedFloat() ) ) );
}

bool ITypeSpecifier::weaklyTypedClockTimeReal() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( (referedTypeSpecifier.getTypeSpecifierKind() == TYPE_DENSE_TIME_SPECIFIER)
				|| ( referedTypeSpecifier.hasTypedClockTime()
					&& ( referedTypeSpecifier.isnot< ContainerTypeSpecifier >()
						|| referedTypeSpecifier.to< ContainerTypeSpecifier >()
							.getContentsTypeSpecifier().weaklyTypedReal() ) ) );
}


///////////////////
// INTEGER TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedUInteger() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedUInteger()
			||weaklyTypedClockTimeInteger()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.isnotNullref()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedUInteger()) );
}

bool ITypeSpecifier::weaklyTypedInteger() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedInteger() //|| isTypedUInteger()
			|| referedTypeSpecifier.weaklyTypedClockTimeInteger()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.isnotNullref()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedInteger() ) );
}


///////////////////
// RATIONAL TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedURational() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedURational()
			|| weaklyTypedUInteger()
			|| weaklyTypedClockTimeRational()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedURational() ) );
}

bool ITypeSpecifier::weaklyTypedRational() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedRational() //|| isTypedURational()
			|| weaklyTypedInteger()
			|| weaklyTypedClockTimeRational()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedRational() ) );
}


///////////////////
// FLOAT TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedUFloat() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedUFloat()
			|| weaklyTypedURational()
			|| weaklyTypedClockTimeFloat()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedUFloat()) );
}

bool ITypeSpecifier::weaklyTypedFloat() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedFloat()
			|| weaklyTypedRational()
			|| weaklyTypedClockTimeFloat()
			|| ( referedTypeSpecifier.isTypedInterval()
			&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
				.getSupportTypeSpecifier().weaklyTypedFloat()) );
}


///////////////////
// REAL TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedUReal() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedUReal()
			|| weaklyTypedUFloat()
			|| weaklyTypedClockTimeReal()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedUReal()));
}

bool ITypeSpecifier::weaklyTypedReal() const
{
	const BaseTypeSpecifier & referedTypeSpecifier =
			thisTypeSpecifier().referedTypeSpecifier();

	return( referedTypeSpecifier.isTypedReal()
			|| weaklyTypedFloat()
			|| weaklyTypedClockTimeReal()
			|| ( referedTypeSpecifier.isTypedInterval()
				&& referedTypeSpecifier.as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().weaklyTypedReal() ) );
}


//////////////////////////////
// TYPE ALGEBRA
//////////////////////////////

bool ITypeSpecifier::isTypeFamily(avm_type_specifier_kind_t typeFamily) const
{
	avm_type_specifier_kind_t typeSpecifierKind = getTypeSpecifierKind();

	if( (typeFamily == typeSpecifierKind)
		|| (typeFamily == TYPE_UNIVERSAL_SPECIFIER)
		|| (typeFamily == TYPE_UNDEFINED_SPECIFIER) )
	{
		return( true );
	}
	else switch( typeFamily )
	{
		case TYPE_UNIVERSAL_SPECIFIER:
		case TYPE_UNDEFINED_SPECIFIER:
		{
			return( true );
		}

		case TYPE_PORT_SPECIFIER:
		case TYPE_SIGNAL_SPECIFIER:
		case TYPE_MESSAGE_SPECIFIER:
		{
			switch( typeSpecifierKind )
			{
				case TYPE_PORT_SPECIFIER:
				case TYPE_SIGNAL_SPECIFIER:
				case TYPE_MESSAGE_SPECIFIER:
				{
					return( true );
				}

				default:
				{
					return( false );
				}
			}

			return( false );
		}

		case TYPE_ALIAS_SPECIFIER:
		{
			return( thisTypeSpecifier().referedTypeSpecifier()
					.isTypeFamily(typeFamily) );
		}

		default:
		{
			return( false );
		}
	}
}


bool ITypeSpecifier::weaklyTyped(avm_type_specifier_kind_t otherTSK) const
{
	avm_type_specifier_kind_t typeSpecifierKind = getTypeSpecifierKind();

	if( typeSpecifierKind == otherTSK )
	{
		return( true );
	}
	else switch( typeSpecifierKind )
	{
		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		{
			return( weaklyTypedUInteger() );
		}
		case TYPE_INTEGER_SPECIFIER:
		{
			return( weaklyTypedInteger() );
		}

		case TYPE_POS_RATIONAL_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		{
			return( weaklyTypedURational() );
		}
		case TYPE_RATIONAL_SPECIFIER:
		{
			return( weaklyTypedRational() );
		}

		case TYPE_POS_FLOAT_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		{
			return( weaklyTypedUFloat() );
		}
		case TYPE_FLOAT_SPECIFIER:
		{
			return( weaklyTypedFloat() );
		}

		case TYPE_POS_REAL_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
		{
			return( weaklyTypedUReal() );
		}
		case TYPE_REAL_SPECIFIER:
		{
			return( weaklyTypedReal() );
		}

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_DENSE_TIME_SPECIFIER:
		{
			return( weaklyTypedReal() );
		}
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
			return( weaklyTypedInteger() );
		}

		case TYPE_ALIAS_SPECIFIER:
		{
			return( thisTypeSpecifier().referedTypeSpecifier()
					.weaklyTyped(otherTSK) );
		}

		default:
		{
			return( false );
		}
	}
}


//////////////////////////////
// NUMERIC TYPE
//////////////////////////////

bool ITypeSpecifier::isTypedNumeric() const
{
	switch( getTypeSpecifierKind() )
	{
		case TYPE_INTEGER_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:
		case TYPE_REAL_SPECIFIER:

		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_POS_RATIONAL_SPECIFIER:
		case TYPE_POS_FLOAT_SPECIFIER:
		case TYPE_POS_REAL_SPECIFIER:

		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_DENSE_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
			return( true );

		case TYPE_INTERVAL_SPECIFIER:
			return( thisTypeSpecifier().as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().isTypedNumeric() );

		case TYPE_ALIAS_SPECIFIER:
			return( thisTypeSpecifier().referedTypeSpecifier().isTypedNumeric() );

		default: return( false );
	}
}

bool ITypeSpecifier::isTypedPositiveNumber() const
{
	switch( getTypeSpecifierKind() )
	{
		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_POS_RATIONAL_SPECIFIER:
		case TYPE_POS_FLOAT_SPECIFIER:
		case TYPE_POS_REAL_SPECIFIER:

		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
			return( true );

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_DENSE_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
			return( thisTypeSpecifier().as< ContainerTypeSpecifier >()
					.getContentsTypeSpecifier().isTypedPositiveNumber() );

		case TYPE_INTERVAL_SPECIFIER:
			return( thisTypeSpecifier().as< IntervalTypeSpecifier >()
					.getSupportTypeSpecifier().isTypedPositiveNumber() );

		case TYPE_ALIAS_SPECIFIER:
			return( thisTypeSpecifier().referedTypeSpecifier()
					.isTypedPositiveNumber() );

		default: return( false );
	}
}

bool ITypeSpecifier::isTypedStrictlyPositiveNumber() const
{
	switch( getTypeSpecifierKind() )
	{
		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_POS_RATIONAL_SPECIFIER:
		case TYPE_POS_FLOAT_SPECIFIER:
		case TYPE_POS_REAL_SPECIFIER:
			return( true );

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_DENSE_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
			return( thisTypeSpecifier().as< ContainerTypeSpecifier >()
				.getContentsTypeSpecifier().isTypedStrictlyPositiveNumber() );

		case TYPE_INTERVAL_SPECIFIER:
			return( thisTypeSpecifier().as< IntervalTypeSpecifier >()
				.getSupportTypeSpecifier().isTypedStrictlyPositiveNumber() );

		case TYPE_ALIAS_SPECIFIER:
			return( thisTypeSpecifier().referedTypeSpecifier()
					.isTypedStrictlyPositiveNumber() );

		default: return( false );
	}
}

/**
 * TYPE SPECIFICER KIND TO STRING
 */

std::string ITypeSpecifier::strSpecifierKind() const
{
#define PRINT_TYPE_SPECIFIER_KIND( OBJ )  \
		case TYPE_##OBJ##_SPECIFIER : return( QUOTEME( TYPE_##OBJ ) )

	switch ( getTypeSpecifierKind() )
//	switch ( getTypeSpecifierKind() )
	{
		PRINT_TYPE_SPECIFIER_KIND( BOOLEAN     );

		PRINT_TYPE_SPECIFIER_KIND( CHARACTER   );

		PRINT_TYPE_SPECIFIER_KIND( POS_INTEGER );

		PRINT_TYPE_SPECIFIER_KIND( UINTEGER    );
		PRINT_TYPE_SPECIFIER_KIND( INTEGER     );

		PRINT_TYPE_SPECIFIER_KIND( URATIONAL   );
		PRINT_TYPE_SPECIFIER_KIND( RATIONAL    );

		PRINT_TYPE_SPECIFIER_KIND( UFLOAT      );
		PRINT_TYPE_SPECIFIER_KIND( FLOAT       );

		PRINT_TYPE_SPECIFIER_KIND( UREAL       );
		PRINT_TYPE_SPECIFIER_KIND( REAL        );

		PRINT_TYPE_SPECIFIER_KIND( DENSE_TIME    );
		PRINT_TYPE_SPECIFIER_KIND( DISCRETE_TIME );

		PRINT_TYPE_SPECIFIER_KIND( INTERVAL    );

		PRINT_TYPE_SPECIFIER_KIND( STRING      );

		PRINT_TYPE_SPECIFIER_KIND( IDENTIFIER  );
		PRINT_TYPE_SPECIFIER_KIND( QUALIFIED_IDENTIFIER );

		PRINT_TYPE_SPECIFIER_KIND( BUFFER      );
		PRINT_TYPE_SPECIFIER_KIND( CONNECTOR  );
		PRINT_TYPE_SPECIFIER_KIND( PORT        );
		PRINT_TYPE_SPECIFIER_KIND( MACHINE     );

		PRINT_TYPE_SPECIFIER_KIND( OPERATOR    );

		PRINT_TYPE_SPECIFIER_KIND( LAMBDA      );

		PRINT_TYPE_SPECIFIER_KIND( ARRAY       );
		PRINT_TYPE_SPECIFIER_KIND( CLASS       );
		PRINT_TYPE_SPECIFIER_KIND( ENUM        );
		PRINT_TYPE_SPECIFIER_KIND( UNION       );

		PRINT_TYPE_SPECIFIER_KIND( VECTOR      );
		PRINT_TYPE_SPECIFIER_KIND( LIST        );
		PRINT_TYPE_SPECIFIER_KIND( SET         );
		PRINT_TYPE_SPECIFIER_KIND( MULTISET    );

		PRINT_TYPE_SPECIFIER_KIND( FIFO        );
		PRINT_TYPE_SPECIFIER_KIND( LIFO        );
		PRINT_TYPE_SPECIFIER_KIND( MULTI_FIFO  );
		PRINT_TYPE_SPECIFIER_KIND( MULTI_LIFO  );

		PRINT_TYPE_SPECIFIER_KIND( RAM         );

		PRINT_TYPE_SPECIFIER_KIND( UNIVERSAL   );

		PRINT_TYPE_SPECIFIER_KIND( NULL        );

		PRINT_TYPE_SPECIFIER_KIND( UNDEFINED   );

//		PRINT_TYPE_SPECIFIER_KIND( ALIAS       );

		case TYPE_ALIAS_SPECIFIER:
			return( thisTypeSpecifier().referedTypeSpecifier().strSpecifierKind() );

		default :  return( "TYPE_UNKNOWN_SPECIFIER" );
	}
}


////////////////////////////////////////////////////////////////////////////////
// INTERVAL::KIND
////////////////////////////////////////////////////////////////////////////////

std::string IIntervalKind::to_string(KIND kind, const BF & inf, const BF & sup)
{
	char leftChar;
	char rightChar;

	switch( kind )
	{
		case IIntervalKind::CLOSED:
		{
			leftChar  = '[';
			rightChar = ']';
			break;
		}

		case IIntervalKind::LOPEN:
		{
			leftChar  = ']';
			rightChar = ']';
			break;
		}

		case IIntervalKind::ROPEN:
		{
			leftChar  = '[';
			rightChar = '[';
			break;
		}

		case IIntervalKind::OPEN:
		default:
		{
			leftChar  = ']';
			rightChar = '[';
			break;
		}
	}

	return( OSS() << leftChar << inf.str() << ',' << sup.str() << rightChar );
}




} /* namespace sep */
