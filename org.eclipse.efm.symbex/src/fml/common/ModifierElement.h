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

#ifndef MODIFIERELEMENT_H_
#define MODIFIERELEMENT_H_

#include <string>

#include <util/avm_numeric.h>


namespace sep
{


struct Modifier
{

	/**
	 * VISIBILITY_KIND
	 * 2 bits
	 */
	enum VISIBILITY_KIND
	{
		VISIBILITY_UNDEFINED_KIND  = 0x00, // DEFAULT
		VISIBILITY_PRIVATE_KIND    = 0x00, // DEFAULT

		VISIBILITY_PUBLIC_KIND     = 0x01,

		VISIBILITY_PROTECTED_KIND  = 0x02,

		VISIBILITY_PACKAGE_KIND    = 0x03

	};


	/**
	 * DIRECTION_KIND
	 * 3 bits
	 */
	enum DIRECTION_KIND
	{
		DIRECTION_UNDEFINED_KIND   = 0x00, // DEFAULT

		DIRECTION_INPUT_KIND       = 0x01,

		DIRECTION_OUTPUT_KIND      = 0x02,

		DIRECTION_INOUT_KIND       = DIRECTION_INPUT_KIND
		                           | DIRECTION_OUTPUT_KIND,

		DIRECTION_RETURN_KIND      = 0x04

	};



	/**
	 * NATURE_KIND
	 * 4 bits
	 */
	enum NATURE_KIND
	{
		NATURE_UNDEFINED_KIND            = 0x000, // DEFAULT
		NATURE_VARIABLE_KIND             = 0x000, // DEFAULT

		NATURE_PARAMETER_KIND            = 0x001,

		NATURE_REFERENCE_KIND            = 0x002,

		NATURE_MACRO_KIND                = 0x004,

		NATURE_BIND_KIND                 = 0x008,

		NATURE_PARAMETER_BIND_KIND       = NATURE_PARAMETER_KIND
		                                 | NATURE_BIND_KIND,

		NATURE_REFERENCE_MACRO_KIND      = NATURE_REFERENCE_KIND
		                                 | NATURE_MACRO_KIND,

		NATURE_PARAMETER_REFERENCE_MACRO_KIND
		                                 = NATURE_PARAMETER_KIND
		                                 | NATURE_REFERENCE_KIND
		                                 | NATURE_MACRO_KIND

	};


	/**
	 * FEATURE_KIND
	 * 5 bits
	 */
	enum FEATURE_KIND
	{
		FEATURE_UNDEFINED_KIND     = 0x000, // DEFAULT

		FEATURE_FINAL_KIND         = 0x001,
		FEATURE_CONST_KIND         = 0x001,

		FEATURE_STATIC_KIND        = 0x002,

		FEATURE_TRANSIENT_KIND     = 0x004,

		FEATURE_VOLATILE_KIND      = 0x008,

		FEATURE_UNSAFE_KIND        = 0x010,

		FEATURE_FINAL_STATIC_KIND  = FEATURE_FINAL_KIND
		                           | FEATURE_STATIC_KIND

	};


	/**
	 * TYPEDEF
	 */
	typedef unsigned short  bit_field_t;

	/**
	 * BIT FIELDS
	 */
	bit_field_t visibility     : 2;

	bit_field_t direction      : 3;

	bit_field_t nature         : 4;

	bit_field_t feature        : 5;


	/**
	 * ENABLING POSITION
	 */
	enum
	{
		FIELD_VISIBILITY_POSITION        = 0x01,
		FIELD_DIRECTION_POSITION         = 0x02,
		FIELD_NATURE_POSITION            = 0x04,
		FIELD_FEATURE_POSITION           = 0x08,

		ENABLE_ALL_FIELDS                = 0xFF,

		DISABLE_VISIBILITY_FIELD         = (~ FIELD_VISIBILITY_POSITION),
		DISABLE_DIRECTION_FIELD          = (~ FIELD_DIRECTION_POSITION ),
		DISABLE_FEATURE_DESIGN_FIELD     = (~ FIELD_FEATURE_POSITION   ),
		DISABLE_NATURE_FIELD             = (~ FIELD_NATURE_POSITION    )

	};


	/**
	 * STATIC PROPERTY MODIFIER
	 */
	static Modifier PROPERTY_UNDEFINED_MODIFIER;

	/**
	 * VISIBILITY
	 */
	static Modifier PROPERTY_PUBLIC_MODIFIER;

	static Modifier PROPERTY_PROTECTED_MODIFIER;

	static Modifier PROPERTY_PRIVATE_MODIFIER;

	/**
	 * DIRECTION
	 */
	static Modifier PROPERTY_INOUT_DIRECTION;

	/**
	 * NATURE
	 */
	static Modifier PROPERTY_MACRO_MODIFIER;

	/**
	 * ALIAS
	 */
	static Modifier PROPERTY_PUBLIC_VOLATILE_MODIFIER;

	static Modifier PROPERTY_PUBLIC_FINAL_STATIC_MODIFIER;

	static Modifier PARAMETER_PUBLIC_FINAL_STATIC_MODIFIER;

	/**
	 * [ DIRECTION ] PARAMETER
	 */
	static Modifier PROPERTY_PARAMETER_MODIFIER;

	static Modifier PROPERTY_INPUT_PARAMETER_MODIFIER;

	static Modifier PROPERTY_OUTPUT_PARAMETER_MODIFIER;

	static Modifier PROPERTY_INOUT_PARAMETER_MODIFIER;

	static Modifier PROPERTY_RETURN_PARAMETER_MODIFIER;

	/**
	 * [ BIND ] PARAMETER
	 */
	static Modifier PROPERTY_PARAMETER_BIND_MODIFIER;


	/**
	 * CONSTRUCTORS
	 */
	Modifier()
	: visibility( VISIBILITY_UNDEFINED_KIND ),
	direction   ( DIRECTION_UNDEFINED_KIND  ),
	nature      ( NATURE_UNDEFINED_KIND     ),
	feature     ( FEATURE_UNDEFINED_KIND    )
	{
		//!! NOTHING
	}

//	Modifier(const Modifier & aModifier)
//	: visibility( aModifier.visibility ),
//	direction   ( aModifier.direction  ),
//	nature      ( aModifier.nature     ),
//	feature     ( aModifier.feature    )
//	{
//		//!! NOTHING
//	}

	Modifier(bit_field_t visibilityKind, bit_field_t directionKind,
			bit_field_t natureKind, bit_field_t featureKind)
	: visibility( visibilityKind ),
	direction   ( directionKind  ),
	nature      ( natureKind  ),
	feature     ( featureKind )
	{
		//!! NOTHING
	}

	Modifier(NATURE_KIND natureKindind, FEATURE_KIND featureKindind)
	: visibility( VISIBILITY_UNDEFINED_KIND ),
	direction   ( DIRECTION_UNDEFINED_KIND  ),
	nature      ( natureKindind  ),
	feature     ( featureKindind )
	{
		//!! NOTHING
	}


	Modifier(VISIBILITY_KIND visibilityKind)
	: visibility( visibilityKind ),
	direction   ( DIRECTION_UNDEFINED_KIND  ),
	nature      ( NATURE_UNDEFINED_KIND     ),
	feature     ( FEATURE_UNDEFINED_KIND    )
	{
		//!! NOTHING
	}

	Modifier(DIRECTION_KIND directionKind)
	: visibility( VISIBILITY_UNDEFINED_KIND ),
	direction   ( directionKind             ),
	nature      ( NATURE_UNDEFINED_KIND     ),
	feature     ( FEATURE_UNDEFINED_KIND    )
	{
		//!! NOTHING
	}

	Modifier(NATURE_KIND natureKind)
	: visibility( VISIBILITY_UNDEFINED_KIND ),
	direction   ( DIRECTION_UNDEFINED_KIND  ),
	nature      ( natureKind                ),
	feature     ( FEATURE_UNDEFINED_KIND    )
	{
		//!! NOTHING
	}

	Modifier(FEATURE_KIND featureKind)
	: visibility( VISIBILITY_UNDEFINED_KIND ),
	direction   ( DIRECTION_UNDEFINED_KIND  ),
	nature      ( NATURE_UNDEFINED_KIND     ),
	feature     ( featureKind               )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	~Modifier()
	{
		//!! NOTHING
	}


	/**
	 * TESTER
	 */
	inline bool hasModifier() const
	{
		return(    (visibility != VISIBILITY_UNDEFINED_KIND)
				|| (direction  != DIRECTION_UNDEFINED_KIND )
				|| (nature     != NATURE_UNDEFINED_KIND    )
				|| (feature    != FEATURE_UNDEFINED_KIND   ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR =
	////////////////////////////////////////////////////////////////////////////

	inline Modifier & override_ifdef(const Modifier & other)
	{
		if( other.visibility != VISIBILITY_UNDEFINED_KIND )
		{
			visibility = other.visibility;
		}
		if( other.direction != DIRECTION_UNDEFINED_KIND )
		{
			direction = other.direction;
		}

		nature  |= other.nature;
		feature |= other.feature;

		return( *this );
	}

	inline Modifier & ifnot_define(const Modifier & other)
	{
		if( visibility == VISIBILITY_UNDEFINED_KIND )
		{
			visibility = other.visibility;
		}
		if( direction == DIRECTION_UNDEFINED_KIND )
		{
			direction = other.direction;
		}

		nature  |= other.nature;
		feature |= other.feature;

		return( *this );
	}


	inline Modifier & operator=(const Modifier & other)
	{
		visibility = other.visibility;
		direction  = other.direction;
		nature     = other.nature;
		feature    = other.feature;

		return( *this );
	}

	inline Modifier & operator=(VISIBILITY_KIND visibilityKind)
	{
		visibility = visibilityKind;

		return( *this );
	}

	inline Modifier & operator=(DIRECTION_KIND directionKind)
	{
		direction = directionKind;

		return( *this );
	}

	inline Modifier & operator=(NATURE_KIND natureKind)
	{
		nature = natureKind;

		return( *this );
	}

	inline Modifier & operator=(FEATURE_KIND featureKind)
	{
		feature = featureKind;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR |=
	////////////////////////////////////////////////////////////////////////////

	inline Modifier & operator|=(const Modifier & other)
	{
		visibility |= other.visibility;
		direction  |= other.direction;
		nature     |= other.nature;
		feature    |= other.feature;

		return( *this );
	}

	inline Modifier & operator|=(VISIBILITY_KIND visibilityKind)
	{
		visibility |= visibilityKind;

		return( *this );
	}

	inline Modifier & operator|=(DIRECTION_KIND directionKind)
	{
		direction |= directionKind;

		return( *this );
	}

	inline Modifier & operator|=(NATURE_KIND natureKind)
	{
		nature |= natureKind;

		return( *this );
	}

	inline Modifier & operator|=(FEATURE_KIND featureKind)
	{
		feature |= featureKind;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR &=
	////////////////////////////////////////////////////////////////////////////

	inline Modifier & operator&=(const Modifier & other)
	{
		visibility &= other.visibility;
		direction  &= other.direction;
		nature     &= other.nature;
		feature    &= other.feature;

		return( *this );
	}

	inline Modifier & operator&=(VISIBILITY_KIND visibilityKind)
	{
		visibility &= visibilityKind;

		return( *this );
	}

	inline Modifier & operator&=(DIRECTION_KIND directionKind)
	{
		direction &= directionKind;

		return( *this );
	}

	inline Modifier & operator&=(NATURE_KIND natureKind)
	{
		nature &= natureKind;

		return( *this );
	}

	inline Modifier & operator&=(FEATURE_KIND featureKind)
	{
		feature &= featureKind;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR ==  !=
	////////////////////////////////////////////////////////////////////////////

	inline bool operator==(const Modifier & other) const
	{
		return(    (visibility == other.visibility)
				&& (direction  == other.direction )
				&& (nature     == other.nature    )
				&& (feature    == other.feature   ) );
	}

	inline bool operator!=(const Modifier & other) const
	{
		return(    (visibility != other.visibility)
				|| (direction  != other.direction )
				|| (nature     != other.nature    )
				|| (feature    != other.feature   ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR |
	////////////////////////////////////////////////////////////////////////////

	inline Modifier operator|(const Modifier & other) const
	{
		return( Modifier(
				visibility | other.visibility,
				direction  | other.direction,
				nature     | other.nature,
				feature    | other.feature) );
	}

	inline Modifier operator|(VISIBILITY_KIND visibilityKind) const
	{
		return( Modifier(visibility | visibilityKind,
				direction, nature, feature) );
	}

	inline Modifier operator|(DIRECTION_KIND directionKind) const
	{
		return( Modifier(visibility,
				direction | directionKind, nature, feature) );
	}

	inline Modifier operator|(NATURE_KIND natureKind) const
	{
		return( Modifier(visibility,
				direction, nature | natureKind, feature) );
	}

	inline Modifier operator|(FEATURE_KIND featureKind) const
	{
		return( Modifier(visibility,
				direction, nature, feature | featureKind) );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR &
	////////////////////////////////////////////////////////////////////////////

	inline Modifier operator&(const Modifier & other) const
	{
		return( Modifier(
				visibility & other.visibility,
				direction  & other.direction,
				nature     & other.nature,
				feature    & other.feature) );
	}

	inline Modifier operator&(VISIBILITY_KIND visibilityKind) const
	{
		return( Modifier(visibility & visibilityKind,
				direction, nature, feature) );
	}

	inline Modifier operator&(DIRECTION_KIND directionKind) const
	{
		return( Modifier(visibility,
				direction & directionKind, nature, feature) );
	}

	inline Modifier operator&(NATURE_KIND natureKind) const
	{
		return( Modifier(visibility,
				direction, nature & natureKind, feature) );
	}

	inline Modifier operator&(FEATURE_KIND featureKind) const
	{
		return( Modifier(visibility,
				direction, nature, feature & featureKind) );
	}


	////////////////////////////////////////////////////////////////////////////
	// VISIBILITY KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * visibility
	 */
	inline VISIBILITY_KIND getVisibilityKind() const
	{
		return( static_cast< VISIBILITY_KIND >( visibility ) );
	}

	inline bool hasVisibilityKind() const
	{
		return( visibility != VISIBILITY_UNDEFINED_KIND );
	}

	inline bool isVisibilityKind(VISIBILITY_KIND visibilityKind) const
	{
		return( visibility == visibilityKind );
	}

	inline Modifier & setVisibilityKind(VISIBILITY_KIND visibilityKind)
	{
		visibility = visibilityKind;

		return( *this );
	}

	inline Modifier & unsetVisibilityKind()
	{
		visibility = VISIBILITY_UNDEFINED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "public" visibility
	 */
	inline bool isVisibilityPublic() const
	{
		return( visibility == VISIBILITY_PUBLIC_KIND );
	}

	inline bool isVisibilityPublic(const Modifier & mask) const
	{
		return( ((visibility | mask.visibility) & VISIBILITY_PUBLIC_KIND) != 0 );
	}

	inline Modifier & setVisibilityPublic()
	{
		visibility = VISIBILITY_PUBLIC_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "private" visibility
	 */
	inline bool isVisibilityPrivate() const
	{
		return( visibility == VISIBILITY_PRIVATE_KIND );
	}

	inline Modifier & setVisibilityPrivate()
	{
		visibility = VISIBILITY_PRIVATE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "protected" visibility
	 */
	inline bool isVisibilityProtected() const
	{
		return( visibility == VISIBILITY_PROTECTED_KIND );
	}

	inline Modifier & setVisibilityProtected()
	{
		visibility = VISIBILITY_PROTECTED_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "package" visibility
	 */
	inline bool isVisibilityPackage() const
	{
		return( visibility == VISIBILITY_PACKAGE_KIND );
	}

	inline Modifier & setVisibilityPackage()
	{
		visibility = VISIBILITY_PACKAGE_KIND;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// DIRECTION KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * direction
	 */
	inline DIRECTION_KIND getDirectionKind() const
	{
		return( static_cast< DIRECTION_KIND >( direction ) );
	}

	inline bool hasDirectionKind() const
	{
		return( direction != DIRECTION_UNDEFINED_KIND );
	}

	inline bool hasDirectionKind(DIRECTION_KIND directionKind) const
	{
		return( (direction & directionKind) != 0 );
	}


	inline bool isDirectionKind(DIRECTION_KIND directionKind) const
	{
		return( direction == directionKind );
	}

	inline bool isnotDirectionKind(DIRECTION_KIND directionKind) const
	{
		return( direction != directionKind );
	}


	inline bool isDirectionKind(
			DIRECTION_KIND directionKind, bool isStrongly) const
	{
		return( isStrongly ? (direction == directionKind)
				: ((direction & directionKind) != 0) );
	}

	inline bool isnotDirectionKind(
			DIRECTION_KIND directionKind, bool isStrongly) const
	{
		return( isStrongly ? (direction != directionKind)
				: ((direction & directionKind) == 0) );
	}


	inline bool isDirectionUndefined() const
	{
		return( direction == DIRECTION_UNDEFINED_KIND );
	}

	inline Modifier & setDirectionKind(DIRECTION_KIND directionKind)
	{
		direction = directionKind;

		return( *this );
	}

	inline Modifier & unsetDirectionKind()
	{
		direction = DIRECTION_UNDEFINED_KIND;

		return( *this );
	}


	inline std::string strDirection() const
	{
		switch( direction )
		{
			case DIRECTION_INPUT_KIND:	   return( "input"  );
			case DIRECTION_OUTPUT_KIND:	   return( "output" );
			case DIRECTION_INOUT_KIND:     return( "inout"  );
			case DIRECTION_RETURN_KIND:	   return( "return" );

			case DIRECTION_UNDEFINED_KIND: return( "undefined<direction#kind>" );

			default: return( "unknown<direction#kind>" );
		}
	}



	/**
	 * GETTER - SETTER
	 * "input" direction modifier
	 */
	inline bool isDirectionInput() const
	{
		return( direction == DIRECTION_INPUT_KIND );
	}

	inline bool hasDirectionInput() const
	{
		return( (direction & DIRECTION_INPUT_KIND) != 0 );
	}

	inline Modifier & setDirectionInput()
	{
		direction = DIRECTION_INPUT_KIND;

		return( *this );
	}



	/**
	 * GETTER - SETTER
	 * "instance" direction modifier
	 */
	inline bool isDirectionOutput() const
	{
		return( direction == DIRECTION_OUTPUT_KIND );
	}

	inline bool hasDirectionOutput() const
	{
		return( (direction & DIRECTION_OUTPUT_KIND) != 0 );
	}

	inline Modifier & setDirectionOutput()
	{
		direction = DIRECTION_OUTPUT_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "prototype" direction modifier
	 */
	inline bool isDirectionInout() const
	{
		return( direction == DIRECTION_INOUT_KIND );
	}


	inline Modifier & setDirectionInout()
	{
		direction = DIRECTION_INOUT_KIND;

		return( *this );
	}

	inline Modifier & setDirectionInoutElse()
	{
		if( direction == DIRECTION_UNDEFINED_KIND )
		{
			direction = DIRECTION_INOUT_KIND;
		}

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "runtime" direction modifier
	 */
	inline bool isDirectionReturn() const
	{
		return( direction == DIRECTION_RETURN_KIND );
	}

	inline bool noDirectionReturn() const
	{
		return( direction != DIRECTION_RETURN_KIND );
	}

	inline Modifier & setDirectionReturn()
	{
		direction = DIRECTION_RETURN_KIND;

		return( *this );
	}

	inline bool hasDirectionOtheThanReturn() const
	{
		return( (direction & DIRECTION_INOUT_KIND) != 0 );
	}

	////////////////////////////////////////////////////////////////////////////
	// NATURE KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * nature
	 */
	inline bit_field_t getNatureKind() const
	{
		return( nature );
	}

	inline bool hasNatureKind() const
	{
		return( nature != NATURE_UNDEFINED_KIND );
	}

	inline bool hasNatureKind(bit_field_t kind) const
	{
		return( (nature & kind) != 0 );
	}

	inline bool isNatureKind(bit_field_t kind) const
	{
		return( nature == kind );
	}

	inline Modifier & addNatureKind(bit_field_t kind)
	{
		nature |= kind;

		return( *this );
	}

	inline Modifier & remNatureKind(bit_field_t kind)
	{
		nature &= (~ kind);

		return( *this );
	}

	inline Modifier & setNatureKind(bit_field_t kind)
	{
		nature = kind;

		return( *this );
	}



	////////////////////////////////////////////////////////////////////////////
	// FEATURE KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * feature
	 */
	inline bit_field_t getFeatureKind() const
	{
		return( feature );
	}

	inline bool hasFeatureKind() const
	{
		return( feature != FEATURE_UNDEFINED_KIND );
	}

	inline bool hasFeatureKind(bit_field_t kind) const
	{
		return( (feature & kind) != 0 );
	}

	inline bool isFeatureKind(bit_field_t kind) const
	{
		return( feature == kind );
	}


	inline Modifier & addFeatureKind(bit_field_t kind)
	{
		feature |= kind;

		return( *this );
	}

	inline Modifier & remFeatureKind(bit_field_t kind)
	{
		feature &= (~ kind);

		return( *this );
	}

	inline Modifier & setFeatureKind(bit_field_t kind)
	{
		feature = kind;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "variable" nature
	 */
	inline bool hasNatureVariable() const
	{
		return( (nature & NATURE_VARIABLE_KIND) != 0 );
	}

	inline Modifier & setNatureVariable(bool bNatureVariable = true)
	{
		if( bNatureVariable )
		{
			nature |= NATURE_VARIABLE_KIND;
		}
		else
		{
			nature &= (~ NATURE_VARIABLE_KIND);
		}

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "parameter" nature
	 */
	inline bool hasNatureParameter() const
	{
		return( (nature & NATURE_PARAMETER_KIND) != 0 );
	}

	inline bool noNatureParameter() const
	{
		return( (nature & NATURE_PARAMETER_KIND) == 0 );
	}

	inline Modifier & setNatureParameter(bool bNatureParameter = true)
	{
		if( bNatureParameter )
		{
			nature |= NATURE_PARAMETER_KIND;
		}
		else
		{
			nature &= (~ NATURE_PARAMETER_KIND);
		}

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "reference" nature
	 */
	inline bool hasNatureReference() const
	{
		return( (nature & NATURE_REFERENCE_KIND) != 0 );
	}

	inline Modifier & setNatureReference(bool bNatureReference = true)
	{
		if( bNatureReference )
		{
			nature |= NATURE_REFERENCE_KIND;
		}
		else
		{
			nature &= (~ NATURE_REFERENCE_KIND);
		}

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "macro" nature
	 */
	inline bool hasNatureMacro() const
	{
		return( (nature & NATURE_MACRO_KIND) != 0 );
	}

	inline Modifier & setNatureMacro(bool bNatureMacro = true)
	{
		if( bNatureMacro )
		{
			nature |= NATURE_MACRO_KIND;
		}
		else
		{
			nature &= (~ NATURE_MACRO_KIND);
		}

		return( *this );
	}


	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "reference" or "macro" modifier
	 */
	inline bool anyNatureReferenceMacro() const
	{
		return( (nature & NATURE_REFERENCE_MACRO_KIND) != 0 );
	}

	inline bool noneNatureReferenceMacro() const
	{
		return( (nature & NATURE_REFERENCE_MACRO_KIND) == 0 );
	}


	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "parameter" or "reference" or "macro" modifier
	 */
	inline bool anyNatureParameterReferenceMacro() const
	{
		return( (nature & NATURE_PARAMETER_REFERENCE_MACRO_KIND) != 0 );
	}

	inline bool noneNatureParameterReferenceMacro() const
	{
		return( (nature & NATURE_PARAMETER_REFERENCE_MACRO_KIND) == 0 );
	}

	/**
	 * GETTER - SETTER
	 * "bind" nature
	 */
	inline bool hasNatureBind() const
	{
		return( (nature & NATURE_BIND_KIND) != 0 );
	}

	inline Modifier & setNatureBind(bool bNatureBind = true)
	{
		if( bNatureBind )
		{
			nature |= NATURE_BIND_KIND;
		}
		else
		{
			nature &= (~ NATURE_BIND_KIND);
		}

		return( *this );
	}


	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "parameter" or "bind" modifier
	 */
	inline bool hasNatureParameterBind() const
	{
		return( (nature & NATURE_PARAMETER_BIND_KIND) ==
						NATURE_PARAMETER_BIND_KIND );
	}

	inline Modifier & setNatureParameterBind(bool bNatureParameterBind = true)
	{
		if( bNatureParameterBind )
		{
			nature |= NATURE_PARAMETER_BIND_KIND;
		}
		else
		{
			nature &= (~ NATURE_PARAMETER_BIND_KIND);
		}

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "final" or "const" feature
	 */
	inline bool hasFeatureFinal() const
	{
		return( (feature & FEATURE_FINAL_KIND) != 0 );
	}

	inline bool noFeatureFinal() const
	{
		return( (feature & FEATURE_FINAL_KIND) == 0 );
	}

	inline Modifier & setFeatureFinal(bool bFeatureFinal = true)
	{
		if( bFeatureFinal )
		{
			feature |= FEATURE_FINAL_KIND;
		}
		else
		{
			feature &= (~ FEATURE_FINAL_KIND);
		}

		return( *this );
	}


	inline bool hasFeatureConst() const
	{
		return( (feature & FEATURE_CONST_KIND) != 0 );
	}

	inline Modifier & setFeatureConst(bool bFeatureConst = true)
	{
		if( bFeatureConst )
		{
			feature |= FEATURE_CONST_KIND;
		}
		else
		{
			feature &= (~ FEATURE_CONST_KIND);
		}

		return( *this );
	}


	inline bool hasFeatureMutable() const
	{
		return( (feature & FEATURE_FINAL_KIND) == 0 );
	}

	inline Modifier & setFeatureMutable(bool bFeatureMutable = true)
	{
		if( bFeatureMutable )
		{
			feature &= (~ FEATURE_FINAL_KIND);
		}
		else
		{
			feature |= FEATURE_FINAL_KIND;
		}

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "static" feature
	 */
	inline bool hasFeatureStatic() const
	{
		return( (feature & FEATURE_STATIC_KIND) != 0 );
	}

	inline Modifier & setFeatureStatic(bool bFeatureStatic = true)
	{
		if( bFeatureStatic )
		{
			feature |= FEATURE_STATIC_KIND;
		}
		else
		{
			feature &= (~ FEATURE_STATIC_KIND);
		}

		return( *this );
	}


	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "final static" modifier
	 */
	inline bool hasFeatureFinalStatic() const
	{
		return( (feature & FEATURE_FINAL_STATIC_KIND) ==
					FEATURE_FINAL_STATIC_KIND );
	}

	inline Modifier & setFeatureFinalStatic(bool bFeatureFinalStatic = true)
	{
		if( bFeatureFinalStatic )
		{
			feature |= FEATURE_FINAL_STATIC_KIND;
		}
		else
		{
			feature &= (~ FEATURE_FINAL_STATIC_KIND);
		}

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "transient" feature
	 */
	inline bool hasFeatureTransient() const
	{
		return( (feature & FEATURE_TRANSIENT_KIND) != 0 );
	}

	inline bool noFeatureTransient() const
	{
		return( (feature & FEATURE_TRANSIENT_KIND) == 0 );
	}

	inline Modifier & setFeatureTransient(bool bFeatureTransient = true)
	{
		if( bFeatureTransient )
		{
			feature |= FEATURE_TRANSIENT_KIND;
		}
		else
		{
			feature &= (~ FEATURE_TRANSIENT_KIND);
		}

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "volatile" feature
	 */
	inline bool hasFeatureVolatile() const
	{
		return( (feature & FEATURE_VOLATILE_KIND) != 0 );
	}

	inline bool hasFeatureVolatile(const Modifier & mask) const
	{
		return( ((feature | mask.feature) & FEATURE_VOLATILE_KIND) != 0 );
	}

	inline Modifier & setFeatureVolatile(bool bFeatureVolatile = true)
	{
		if( bFeatureVolatile )
		{
			feature |= FEATURE_VOLATILE_KIND;
		}
		else
		{
			feature &= (~ FEATURE_VOLATILE_KIND);
		}

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "unsafe" feature
	 */
	inline bool hasFeatureUnsafe() const
	{
		return( (feature & FEATURE_UNSAFE_KIND) != 0 );
	}

	inline Modifier & setFeatureUnsafe(bool bFeatureUnsafe = true)
	{
		if( bFeatureUnsafe )
		{
			feature |= FEATURE_UNSAFE_KIND;
		}
		else
		{
			feature &= (~ FEATURE_UNSAFE_KIND);
		}

		return( *this );
	}


	inline bool hasFeatureSafe() const
	{
		return( (feature & FEATURE_UNSAFE_KIND) == 0 );
	}

	inline Modifier & setFeatureSafe(bool bFeatureSafe = true)
	{
		if( bFeatureSafe )
		{
			feature &= (~ FEATURE_UNSAFE_KIND);
		}
		else
		{
			feature |= FEATURE_UNSAFE_KIND;
		}

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// MIX-IN MODIFIER
	////////////////////////////////////////////////////////////////////////////

	/**
	 * HYBRID ALIAS
	 * GETTER - SETTER
	 * "public final static" modifier
	 */
	inline bool hasModifierPublicFinalStatic() const
	{
		return( isVisibilityPublic()
				&& hasFeatureFinalStatic() );
	}

	inline Modifier & setModifierPublicFinalStatic()
	{
		setVisibilityPublic();

		setFeatureFinalStatic();

		return( *this );
	}


	inline bool hasModifierPublicFinalStaticParameter() const
	{
		return( isVisibilityPublic()
				&& hasFeatureFinalStatic()
				&& hasNatureParameter() );
	}

	inline Modifier & setModifierPublicFinalStaticParameter()
	{
		setVisibilityPublic();

		setModifierPublicFinalStatic();

		setNatureParameter( true );

		return( *this );
	}


	/**
	 * HYBRID ALIAS
	 * GETTER - SETTER
	 * "public volatile" modifier
	 */
	inline bool hasModifierPublicVolatile() const
	{
		return( isVisibilityPublic()
				&& hasFeatureVolatile() );
	}

	inline Modifier & setModifierPublicVolatile()
	{
		setVisibilityPublic();

		setFeatureVolatile( true );

		return( *this );
	}


	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "reference" , "macro" , final modifier
	 */
	inline bool anyModifierFinalReferenceMacro() const
	{
		return( hasFeatureFinal()
				|| anyNatureReferenceMacro() );
	}

	inline bool noneModifierFinalReferenceMacro() const
	{
		return( noFeatureFinal()
				&& noneNatureReferenceMacro() );
	}


	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "reference" , "macro" , "transient" modifier
	 */
	inline bool anyModifierTransientReferenceMacro() const
	{
		return( hasFeatureTransient()
				|| anyNatureReferenceMacro() );
	}

	inline bool noneModifierTransientReferenceMacro() const
	{
		return( noFeatureTransient()
				&& noneNatureReferenceMacro() );
	}



	/**
	 * ALIAS
	 * GETTER - SETTER
	 * "bind return" modifier
	 */
	inline bool hasModifierReturnBind() const
	{
		return( isDirectionReturn()
				&& hasNatureBind() );
	}

	inline Modifier & setModifierReturnBind()
	{
		setDirectionReturn();

		setNatureBind( true );

		return( *this );
	}

	/**
	 * ALIAS
	 * TEST
	 * for state data var modifier
	 * "reference" , "macro" , "transient" , "parameter" , "return"
	 */
	bool anyModifierOfStateData() const
	{
		return( noFeatureTransient()
				&& noneNatureParameterReferenceMacro() );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	/**
	 * Serialization
	 */
	static std::string strVisibility(bit_field_t visibilityKind,
			const std::string & separator = " ");

	static std::string xstrVisibility(bit_field_t directionKind,
			const std::string & separator = " ");


	static std::string strDirection(bit_field_t directionKind,
			const std::string & separator = " ");


	static std::string xstrDirection(bit_field_t directionKind,
			const std::string & separator = " ");

	static Modifier::DIRECTION_KIND toDirectionKind(const std::string & id);

	static std::string strFeature(bit_field_t featureKind,
			const std::string & separator = " ");

	static std::string strNature(bit_field_t natureKind,
			const std::string & separator = " ");


	std::string toString(bit_field_t enabledFields = ENABLE_ALL_FIELDS,
			const std::string & separator = " ") const;

	inline std::string toString(const std::string & separator) const
	{
		return( toString( ENABLE_ALL_FIELDS , separator) );
	}

	inline std::string toString_not(DIRECTION_KIND directionKind,
			const std::string & separator = " ") const
	{
		if( isDirectionKind(directionKind) )
		{
			Modifier mdfr( *this );

			return( mdfr.unsetDirectionKind().toString(separator) );
		}
		else
		{
			return( toString(separator) );
		}
	}

	inline std::string toString_not(NATURE_KIND natureKind,
			const std::string & separator = " ") const
	{
		if( hasNatureKind(natureKind) )
		{
			Modifier mdfr( *this );

			return( mdfr.remNatureKind(natureKind).toString(separator) );
		}
		else
		{
			return( toString(separator) );
		}
	}

	inline std::string toString_not(FEATURE_KIND featureKind,
			const std::string & separator = " ") const
	{
		if( hasFeatureKind(featureKind) )
		{
			Modifier mdfr( *this );

			return( mdfr.remFeatureKind(featureKind).toString(separator) );
		}
		else
		{
			return( toString(separator) );
		}
	}


};


//ostream & operator<<(ostream & os, const Modifier & aModifier)
//{
//	os  << Modifier::strVisibility( aModifier.visibility )
//		<< Modifier::strDirection(  aModifier.direction )
//		<< Modifier::strFeature(  aModifier.feature )
//		<< Modifier::strNature(  aModifier.nature );
//
//	return( os );
//}


/**
 * Modifier Implementation
 */
class ModifierImpl
{

protected:
	/**
	 * ATTRIBUTES
	 */
	Modifier mModifier;


public:
	/**
	 * CONSTRUCTOR
	 */
	ModifierImpl()
	: mModifier( )
	{
		//!! NOTHING
	}

	ModifierImpl(const Modifier & aModifier)
	: mModifier( aModifier )
	{
		//!! NOTHING
	}

	ModifierImpl(const ModifierImpl & aCopy)
	: mModifier( aCopy.mModifier )
	{
		//!! NOTHING
	}

	ModifierImpl(const ModifierImpl * aCopy)
	: mModifier( (aCopy != NULL) ?
			aCopy->mModifier : Modifier::PROPERTY_UNDEFINED_MODIFIER )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	~ModifierImpl()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mModifier
	 */
	inline const Modifier & getModifier() const
	{
		return( mModifier );
	}

	inline Modifier & getwModifier()
	{
		return( mModifier );
	}

	inline bool hasModifier() const
	{
		return( mModifier != Modifier::PROPERTY_UNDEFINED_MODIFIER );
	}

	inline void setModifier(const Modifier & aModifier)
	{
		mModifier = aModifier;
	}

};


}

#endif /* MODIFIERELEMENT_H_ */
