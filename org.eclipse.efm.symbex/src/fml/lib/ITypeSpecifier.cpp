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
	return( (getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER) &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
				thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedInteger() ) );
}

bool ITypeSpecifier::weaklyTypedClockRational() const
{
	return( (getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER) &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
				thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedRational() ) );
}

bool ITypeSpecifier::weaklyTypedClockFloat() const
{
	return( (getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER) &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
				thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedFloat() ) );
}


bool ITypeSpecifier::weaklyTypedClockReal() const
{
	return( (getTypeSpecifierKind() == TYPE_CLOCK_SPECIFIER) &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
				thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedReal() ) );
}


///////////////////
// TIME TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedTimeInteger() const
{
	return( (getTypeSpecifierKind() == TYPE_DISCRETE_TIME_SPECIFIER) ||
			( isTypedTime() &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
			thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
				getContentsTypeSpecifier().weaklyTypedInteger() ) ) );
}


bool ITypeSpecifier::weaklyTypedTimeRational() const
{
	return( hasTypedTime() &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
				thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedRational() ) );
}

bool ITypeSpecifier::weaklyTypedTimeFloat() const
{
	return( (getTypeSpecifierKind() == TYPE_CONTINUOUS_TIME_SPECIFIER) ||
			( isTypedTime() &&
				( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
					thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedFloat() ) ) );
	}

bool ITypeSpecifier::weaklyTypedTimeReal() const
{
	return( (getTypeSpecifierKind() == TYPE_CONTINUOUS_TIME_SPECIFIER) ||
			( isTypedTime() &&
				( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
				thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedReal() ) ) );
}


///////////////////
// CLOCK/TIME TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedClockTimeInteger() const
{
	return( (getTypeSpecifierKind() == TYPE_DISCRETE_TIME_SPECIFIER) ||
			( isTypedClockTime() &&
				( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
					thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedInteger() ) ) );
}

bool ITypeSpecifier::weaklyTypedClockTimeRational() const
{
	return( hasTypedClockTime() &&
			( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
			thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
				getContentsTypeSpecifier().weaklyTypedRational() ) );
}

bool ITypeSpecifier::weaklyTypedClockTimeFloat() const
{
	return( (getTypeSpecifierKind() == TYPE_CONTINUOUS_TIME_SPECIFIER) ||
			( isTypedClockTime() &&
				( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() &&
					thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedFloat() ) ) );
}

bool ITypeSpecifier::weaklyTypedClockTimeReal() const
{
	return( (getTypeSpecifierKind() == TYPE_CONTINUOUS_TIME_SPECIFIER) ||
			( isTypedClockTime() &&
				( thisTypeSpecifier()->isnot< ContainerTypeSpecifier >() ||
					thisTypeSpecifier()->to< ContainerTypeSpecifier >()->
					getContentsTypeSpecifier().weaklyTypedReal() ) ) );
}


///////////////////
// INTEGER TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedUInteger() const
{
	return( isTypedUInteger() ||
			weaklyTypedClockTimeInteger() ||
			(isTypedInterval() && (thisTypeSpecifier() != NULL) &&
					thisTypeSpecifier()->as< IntervalTypeSpecifier >()->
						getSupportTypeSpecifier().weaklyTypedUInteger()) );
}

bool ITypeSpecifier::weaklyTypedInteger() const
{
	return( isTypedInteger() || //isTypedUInteger() ||
			weaklyTypedClockTimeInteger() ||
			( isTypedInterval() && (thisTypeSpecifier() != NULL) &&
			thisTypeSpecifier()->as< IntervalTypeSpecifier >()->
				getSupportTypeSpecifier().weaklyTypedInteger() ) );
}


///////////////////
// RATIONAL TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedURational() const
{
	return( isTypedURational() || weaklyTypedUInteger() ||
			weaklyTypedClockTimeRational() ||
			(isTypedInterval() &&
			thisTypeSpecifier()->as< IntervalTypeSpecifier >()
				->getSupportTypeSpecifier().weaklyTypedURational()) );
}

bool ITypeSpecifier::weaklyTypedRational() const
{
	return( isTypedRational() || //isTypedURational() ||
			weaklyTypedInteger() ||
			weaklyTypedClockTimeRational() ||
			( isTypedInterval() &&
				thisTypeSpecifier()->as< IntervalTypeSpecifier >()
					->getSupportTypeSpecifier().weaklyTypedRational()) );
}


///////////////////
// FLOAT TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedUFloat() const
{
	return( isTypedUFloat() || weaklyTypedURational() ||
			weaklyTypedClockTimeFloat() ||
			( isTypedInterval() &&
			thisTypeSpecifier()->as< IntervalTypeSpecifier >()
				->getSupportTypeSpecifier().weaklyTypedUFloat()) );
}

bool ITypeSpecifier::weaklyTypedFloat() const
{
	return( isTypedFloat() || weaklyTypedRational() ||
			weaklyTypedClockTimeFloat() ||
			( isTypedInterval() &&
			thisTypeSpecifier()->as< IntervalTypeSpecifier >()
				->getSupportTypeSpecifier().weaklyTypedFloat()) );
}


///////////////////
// REAL TYPE
///////////////////

bool ITypeSpecifier::weaklyTypedUReal() const
{
	return( isTypedUReal() || weaklyTypedUFloat() || weaklyTypedClockTimeReal() ||
			(isTypedInterval() && thisTypeSpecifier()->as< IntervalTypeSpecifier >()
					->getSupportTypeSpecifier().weaklyTypedUReal()));
}

bool ITypeSpecifier::weaklyTypedReal() const
{
	return( isTypedReal() || weaklyTypedFloat() || weaklyTypedClockTimeReal() ||
			(isTypedInterval() && thisTypeSpecifier()->as< IntervalTypeSpecifier >()
					->getSupportTypeSpecifier().weaklyTypedReal()));
}


//////////////////////////////
// TYPE ALGEBRA
//////////////////////////////

bool ITypeSpecifier::isTypeFamily(avm_type_specifier_kind_t typeFamily)
{
	if( (getTypeSpecifierKind() == typeFamily)   ||
		(typeFamily == TYPE_UNIVERSAL_SPECIFIER) ||
		(typeFamily == TYPE_UNDEFINED_SPECIFIER) )
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
			switch( getTypeSpecifierKind() )
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

		default:
		{
			return( false );
		}
	}
}


bool ITypeSpecifier::weaklyTyped(avm_type_specifier_kind_t otherTSK)
{
	if( getTypeSpecifierKind() == otherTSK )
	{
		return( true );
	}
	else switch( getTypeSpecifierKind() )
	{
		case TYPE_POS_INTEGER_SPECIFIER:
		{
			return( weaklyTypedUInteger() );
		}
		case TYPE_UINTEGER_SPECIFIER:
		{
			return( weaklyTypedUInteger() );
		}
		case TYPE_INTEGER_SPECIFIER:
		{
			return( weaklyTypedInteger() );
		}

		case TYPE_URATIONAL_SPECIFIER:
		{
			return( weaklyTypedURational() );
		}
		case TYPE_RATIONAL_SPECIFIER:
		{
			return( weaklyTypedRational() );
		}

		case TYPE_UFLOAT_SPECIFIER:
		{
			return( weaklyTypedUFloat() );
		}
		case TYPE_FLOAT_SPECIFIER:
		{
			return( weaklyTypedFloat() );
		}

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
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		{
			return( weaklyTypedReal() );
		}
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
			return( weaklyTypedInteger() );
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

		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:

		case TYPE_CLOCK_SPECIFIER:
		case TYPE_TIME_SPECIFIER:
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
			return( true );

		case TYPE_INTERVAL_SPECIFIER:
			return( thisTypeSpecifier()->as< IntervalTypeSpecifier >()->
					getSupportTypeSpecifier().isTypedNumeric() );

		default:
			return( false );
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

		PRINT_TYPE_SPECIFIER_KIND( CONTINUOUS_TIME );
		PRINT_TYPE_SPECIFIER_KIND( DISCRETE_TIME );

		PRINT_TYPE_SPECIFIER_KIND( INTERVAL    );

		PRINT_TYPE_SPECIFIER_KIND( STRING      );

		PRINT_TYPE_SPECIFIER_KIND( IDENTIFIER  );
		PRINT_TYPE_SPECIFIER_KIND( QUALIFIED_IDENTIFIER );

		PRINT_TYPE_SPECIFIER_KIND( BUFFER      );
		PRINT_TYPE_SPECIFIER_KIND( CONNECTOR   );
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

		PRINT_TYPE_SPECIFIER_KIND( ALIAS       );

		PRINT_TYPE_SPECIFIER_KIND( UNIVERSAL   );

		PRINT_TYPE_SPECIFIER_KIND( NULL        );

		PRINT_TYPE_SPECIFIER_KIND( UNDEFINED   );

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
