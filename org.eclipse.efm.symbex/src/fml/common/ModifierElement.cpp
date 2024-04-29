/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ModifierElement.h"

#include <limits>
#include <string>
#include <sstream>


namespace sep
{

/**
 * PROPERTY MODIFIER
 */
Modifier Modifier::OBJECT_NULL_MODIFIER( NULL_TRUE_FLAG );


Modifier Modifier::PROPERTY_UNDEFINED_MODIFIER;


/**
 * VISIBILITY
 */
Modifier Modifier::PROPERTY_PUBLIC_MODIFIER(
		VISIBILITY_PUBLIC_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_PROTECTED_MODIFIER(
		VISIBILITY_PROTECTED_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_PRIVATE_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_UNDEFINED_KIND
);


/**
 * DIRECTION
 */
Modifier Modifier::PROPERTY_INPUT_DIRECTION(
		VISIBILITY_UNDEFINED_KIND,
		DIRECTION_INPUT_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_INOUT_DIRECTION(
		VISIBILITY_UNDEFINED_KIND,
		DIRECTION_INOUT_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_OUTPUT_DIRECTION(
		VISIBILITY_UNDEFINED_KIND,
		DIRECTION_OUTPUT_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_UNDEFINED_KIND
);

/**
 * NATURE
 */
Modifier Modifier::PROPERTY_PARAMETER_MACRO_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_PARAMETER_MACRO_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_RETURN_PARAMETER_MACRO_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_RETURN_KIND,
		NATURE_PARAMETER_MACRO_KIND,
		FEATURE_UNDEFINED_KIND
);


/**
 * VARIABLE ALIAS
 * CONSTANT
 */
Modifier Modifier::PROPERTY_VARIABLE_CONST_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_VARIABLE_KIND,
		FEATURE_CONST_KIND
);

Modifier Modifier::PROPERTY_PUBLIC_VARIABLE_CONST_MODIFIER(
		VISIBILITY_PUBLIC_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_VARIABLE_KIND,
		FEATURE_CONST_KIND
);


/**
 * ALIAS
 */
Modifier Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER(
		VISIBILITY_PUBLIC_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_VOLATILE_KIND
);

Modifier Modifier::PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER(
		VISIBILITY_PUBLIC_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_UNDEFINED_KIND,
		FEATURE_FINAL_KIND | FEATURE_STATIC_KIND
);


Modifier Modifier::PARAMETER_PUBLIC_FINAL_STATIC_MODIFIER(
		VISIBILITY_PUBLIC_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_FINAL_KIND | FEATURE_STATIC_KIND
);


/**
 * [ DIRECTED ] PARAMETER
 */
Modifier Modifier::PROPERTY_PARAMETER_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_INPUT_PARAMETER_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_INPUT_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_OUTPUT_PARAMETER_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_OUTPUT_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_INOUT_PARAMETER_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_INOUT_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_UNDEFINED_KIND
);

Modifier Modifier::PROPERTY_RETURN_PARAMETER_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_RETURN_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_UNDEFINED_KIND
);


Modifier Modifier::PROPERTY_QUANTIFIER_PARAMETER_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_PARAMETER_KIND,
		FEATURE_FINAL_KIND
);


/**
 * [ BIND ] PARAMETER
 */
Modifier Modifier::PROPERTY_PARAMETER_BIND_MODIFIER(
		VISIBILITY_PRIVATE_KIND,
		DIRECTION_UNDEFINED_KIND,
		NATURE_PARAMETER_BIND_KIND,
		FEATURE_UNDEFINED_KIND
);


/**
 * VISIBILITY KIND to STRING
 */
std::string Modifier::strVisibility(
		bit_field_t visibilityKind, const std::string & separator)
{
	switch( visibilityKind )
	{
//			case VISIBILITY_UNDEFINED_KIND:
//				return( "<visibility:undef>" + separator );
		case VISIBILITY_PRIVATE_KIND:
//				return( "private" + separator );
			return( "" );
		case VISIBILITY_PUBLIC_KIND:
			return( "public" + separator );
		case VISIBILITY_PROTECTED_KIND:
			return( "protected" + separator );
		case VISIBILITY_PACKAGE_KIND:
			return( "package" + separator );

		default:
			return( xstrVisibility(visibilityKind, separator) );
	}
}


std::string Modifier::xstrVisibility(
		bit_field_t visibilityKind, const std::string & separator)
{
	if( (visibilityKind != VISIBILITY_UNDEFINED_KIND) )
//		&& (visibilityKind != VISIBILITY_PRIVATE_KIND) )
	{
		std::ostringstream oss;

		if( (visibilityKind & VISIBILITY_PACKAGE_KIND) ==
				VISIBILITY_PACKAGE_KIND )
		{
			oss << "package" << separator;
		}
		else if( (visibilityKind & VISIBILITY_PUBLIC_KIND) != 0 )
		{
			oss << "public" << separator;
		}
		else if( (visibilityKind & VISIBILITY_PROTECTED_KIND) != 0 )
		{
			oss << "protected" << separator;
		}

		return( oss.str() );
	}

	return( "<visibility:undef>" );
}


/**
 * DIRECTION KIND to STRING
 */
std::string Modifier::strDirection(
		bit_field_t directionKind, const std::string & separator)
{
	switch( directionKind )
	{
		case DIRECTION_UNDEFINED_KIND:
			return( "" );

		case DIRECTION_INPUT_KIND:
			return( "input" + separator );
		case DIRECTION_OUTPUT_KIND:
			return( "output" + separator );
		case DIRECTION_INOUT_KIND:
			return( "inout" + separator );
		case DIRECTION_RETURN_KIND:
			return( "return" + separator );

		default:
			return( xstrDirection(directionKind, separator) );
	}
}

std::string Modifier::xstrDirection(
		bit_field_t directionKind, const std::string & separator)
{
	if( (directionKind != DIRECTION_UNDEFINED_KIND) )
	{
		std::ostringstream oss;

		if( (directionKind & DIRECTION_RETURN_KIND) != 0 )
		{
			oss << "return" << separator;
		}

		if( (directionKind & DIRECTION_INOUT_KIND) == DIRECTION_INOUT_KIND )
		{
			oss << "inout" << separator;
		}
		else if( (directionKind & DIRECTION_INPUT_KIND) != 0 )
		{
			oss << "input" << separator;
		}
		else if( (directionKind & DIRECTION_OUTPUT_KIND) != 0 )
		{
			oss << "output" << separator;
		}

		return( oss.str() );
	}

	return( "<direction:undef>" );
}


Modifier::DIRECTION_KIND Modifier::toDirectionKind(const std::string & id)
{
	if( id == "inout"  ) return DIRECTION_INOUT_KIND;
	if( id == "input"  ) return DIRECTION_INPUT_KIND;
	if( id == "output" ) return DIRECTION_OUTPUT_KIND;

	return DIRECTION_UNDEFINED_KIND;
}


/**
 * FEATURE KIND to STRING
 */
std::string Modifier::strFeature(
		bit_field_t featureKind, const std::string & separator)
{
	if( featureKind != FEATURE_UNDEFINED_KIND )
	{
		std::ostringstream oss;

		if( (featureKind & FEATURE_FINAL_KIND) != 0 )
		{
			oss << "final" << separator;
		}
		if( (featureKind & FEATURE_STATIC_KIND) != 0 )
		{
			oss << "static" << separator;
		}
		if( (featureKind & FEATURE_TRANSIENT_KIND) != 0 )
		{
			oss << "transient" << separator;
		}
		if( (featureKind & FEATURE_VOLATILE_KIND) != 0 )
		{
			oss << "volatile" << separator;
		}
		if( (featureKind & FEATURE_UNSAFE_KIND) != 0 )
		{
			oss << "unsafe" << separator;
		}

		return( oss.str() );
	}

	return( "" /*"<feature:undef>"*/ );
}


/**
 * NATURE KIND to STRING
 */
std::string Modifier::strNature(
		bit_field_t nature, const std::string & separator)
{
	if( (nature != NATURE_UNDEFINED_KIND) )
//		&& (nature != NATURE_VARIABLE_KIND) )
	{
		std::ostringstream oss;

		if( (nature & NATURE_REFERENCE_KIND) != 0 )
		{
			oss << "reference" << separator;
		}
		if( (nature & NATURE_MACRO_KIND) != 0 )
		{
			oss << "macro" << separator;
		}
		if( (nature & NATURE_BIND_KIND) != 0 )
		{
			oss << "bind" << separator;
		}

		if( (nature & NATURE_PARAMETER_KIND) != 0 )
		{
			oss << "parameter" << separator;
		}

		return( oss.str() );
	}

	return( "" /*"<nature:undef>"*/ );
}


/**
 * Serialization
 */
std::string Modifier::toString(bit_field_t enabledFields,
		const std::string & separator) const
{
	std::ostringstream oss;

	if( isNullFlagEnabled() )
	{
		oss << "#null<Modifier>" << separator;
	}

	if( (enabledFields & FIELD_VISIBILITY_POSITION) != 0 )
	{
		oss << Modifier::strVisibility( visibility , separator );
	}

	if( (enabledFields & FIELD_DIRECTION_POSITION) != 0 )
	{
		oss << Modifier::strDirection ( direction  , separator );
	}

	if( (enabledFields & FIELD_FEATURE_POSITION) != 0 )
	{
		oss << Modifier::strFeature( feature , separator );
	}

	if( (enabledFields & FIELD_NATURE_POSITION) != 0 )
	{
		oss << Modifier::strNature ( nature , separator );
	}

	return( oss.str() );
}


}
