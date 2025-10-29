/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 avr. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_COMMON_SPECIFIERELEMENT_H_
#define FML_COMMON_SPECIFIERELEMENT_H_


#include <string>

#include <util/avm_numeric.h>
#include <util/avm_string.h>



namespace sep
{


class Specifier
{

public:
	/**
	 * NULL_FLAG
	 * 1 bits
	 */
	enum NULL_FLAG
	{
		NULL_FALSE_FLAG  = 0x00, // IS NOT NULL

		NULL_TRUE_FLAG   = 0x01, // IS NULL

	};


	/**
	 * SCOPE_KIND
	 * 3 bits
	 */
	enum SCOPE_KIND
	{
		SCOPE_MACHINE_KIND,

		SCOPE_PROGRAM_KIND,

		SCOPE_TRANSITION_KIND,

		SCOPE_ROUTINE_KIND,

		SCOPE_RUNNABLE_KIND,

		SCOPE_UNDEFINED_KIND
	};

	// Utils
	static SCOPE_KIND toScope(const std::string & id);

	static std::string strScope(SCOPE_KIND mMocKind);


	/**
	 * COMPONENT_KIND
	 * 8 bits
	 */
	enum COMPONENT_KIND {

		COMPONENT_UNDEFINED_KIND           = 0x000,

		COMPONENT_SYSTEM_KIND              = 0x001,

		COMPONENT_EXECUTABLE_KIND          = 0x002,


		COMPONENT_PROCEDURE_KIND           = 0x004,

		COMPONENT_ROUTINE_KIND             = 0x008,


		COMPONENT_INTERACTION_KIND         = 0x010,


		COMPONENT_STATEMACHINE_KIND        = 0x020,

		COMPONENT_STATE_KIND               = 0x040,
//		                                   | COMPONENT_STATEMACHINE_KIND,

		COMPONENT_PSEUDOSTATE_KIND         = 0x080,
//										   | COMPONENT_STATE_KIND,


		FAMILY_COMPONENT_STATE_KIND        = COMPONENT_STATE_KIND
		                                   | COMPONENT_PSEUDOSTATE_KIND,

		FAMILY_COMPONENT_STATEMACHINE_KIND = COMPONENT_STATEMACHINE_KIND
		                                   | FAMILY_COMPONENT_STATE_KIND,

		FAMILY_COMPONENT_COMPOSITE_KIND    = COMPONENT_SYSTEM_KIND
		                                   | COMPONENT_INTERACTION_KIND
		                                   | COMPONENT_STATEMACHINE_KIND
		                                   | COMPONENT_EXECUTABLE_KIND,


	};


	/**
	 * Model Of Computation
	 * MOC_KIND
	 * 7 bits
	 */
	enum MOC_KIND {

		MOC_UNDEFINED_KIND                  = 0x000,

		MOC_COMPOSITE_MASK_KIND             = 0x001,

		MOC_COMPOSITE_STRUCTURE_KIND        = 0x002
		                                    | MOC_COMPOSITE_MASK_KIND,


		MOC_COMPOSITE_INTERACTION__KIND     = 0x004
		                                    | MOC_COMPOSITE_MASK_KIND,


		MOC_STATE_TRANSITION_STRUCTURE_KIND = 0x008
		                                    | MOC_COMPOSITE_MASK_KIND,

		MOC_STATE_TRANSITION_SYSTEM_KIND    = 0x010
											| MOC_STATE_TRANSITION_STRUCTURE_KIND,

		MOC_STATE_TRANSITION_FLOW_KIND      = 0x020
		                                    | MOC_STATE_TRANSITION_STRUCTURE_KIND,


		MOC_DATA_FLOW_KIND                  = 0x040
		                                    | MOC_COMPOSITE_MASK_KIND,

	};


	/**
	 * GROUP_KIND
	 * 3 bits
	 */
	enum GROUP_KIND
	{

		GROUP_UNDEFINED_KIND             = 0x000,

		GROUP_MASK_KIND                  = 0x001,

		GROUP_SOME_KIND                  = 0x002 | GROUP_MASK_KIND,

		GROUP_EXCEPT_KIND                = 0x004 | GROUP_MASK_KIND,

		GROUP_EVERY_KIND                 = 0x006 | GROUP_MASK_KIND

	};


	/**
	 * INTERACTION MOC
	 * 4 bits
	 */
	enum INTERACTION_MOC
	{
		INTERACTION_UNDEFINED_MOC,

		INTERACTION_ALTERNATIVE_MOC,

		INTERACTION_OPTION_MOC,

		INTERACTION_LOOP_MOC,

		INTERACTION_BREAK_MOC,

		INTERACTION_PARALLEL_MOC,

		INTERACTION_STRICT_SEQUENCE_MOC,

		INTERACTION_WEAK_SEQUENCE_MOC,

		INTERACTION_CRITICAL_MOC,

		INTERACTION_IGNORE_MOC,

		INTERACTION_CONSIDER_MOC,

		INTERACTION_ASSERT_MOC,

		INTERACTION_NEGATIVE_MOC

	};


	/**
	 * STATE_MOC
	 * 4 bits
	 */
	enum STATE_MOC
	{

		STATE_UNDEFINED_MOC              = 0x000,

		STATE_SIMPLE_MOC                 = 0x001,

		STATE_START_MOC                  = 0x002,

		STATE_FINAL_MOC                  = 0x004,

		STATE_SYNC_MOC                   = 0x008

	};


	/**
	 * PSEUDOSTATE_MOC
	 * 11 bits
	 */
	enum PSEUDOSTATE_MOC
	{

		PSEUDOSTATE_UNDEFINED_MOC         = 0x000,

		PSEUDOSTATE_INITIAL_MOC           = 0x001,

		PSEUDOSTATE_TERMINAL_MOC          = 0x002,
		PSEUDOSTATE_RETURN_MOC            = 0x004,

		FAMILY_PSEUDO_ENDING_MOC          = PSEUDOSTATE_TERMINAL_MOC
		                                  | PSEUDOSTATE_RETURN_MOC,

		PSEUDOSTATE_JUNCTION_MOC          = 0x008,
		PSEUDOSTATE_CHOICE_MOC            = 0x010,

		PSEUDOSTATE_ENTRY_POINT_MOC       = 0x020,
		PSEUDOSTATE_EXIT_POINT_MOC        = 0x040,

		FAMILY_PSEUDO_CONNECTOR_POINT_MOC = PSEUDOSTATE_ENTRY_POINT_MOC
		                                  | PSEUDOSTATE_EXIT_POINT_MOC,

		PSEUDOSTATE_FORK_MOC              = 0x080,
		PSEUDOSTATE_JOIN_MOC              = 0x100,

		PSEUDOSTATE_DEEP_HISTORY_MOC      = 0x200,
		PSEUDOSTATE_SHALLOW_HISTORY_MOC   = 0x400,

		FAMILY_PSEUDO_HISTORY_MOC         = PSEUDOSTATE_DEEP_HISTORY_MOC
		                                 | PSEUDOSTATE_SHALLOW_HISTORY_MOC,

	};


	/**
	 * FEATURE_KIND
	 * 6 bits
	 */
	enum FEATURE_KIND
	{
		FEATURE_UNDEFINED_KIND           = 0x000, // DEFAULT

		FEATURE_DENSE_TIMED_KIND         = 0x001,

		FEATURE_CONTINUOUS_TIMED_KIND    = 0x002
                                         | FEATURE_DENSE_TIMED_KIND,

		FEATURE_DISCRETE_TIMED_KIND      = 0x004,

		FEATURE_TIMED_KIND               = FEATURE_DENSE_TIMED_KIND
		                                 | FEATURE_CONTINUOUS_TIMED_KIND
		                                 | FEATURE_DISCRETE_TIMED_KIND,

		FEATURE_INPUT_ENABLED_KIND       = 0x008,

		FEATURE_LIFELINE_KIND            = 0x010,

		FEATURE_USER_DEFINED_SCHEDULE_KIND = 0x020

	};



	/**
	 * DESIGN_KIND
	 * 5 bits
	 */
	enum DESIGN_KIND
	{
		DESIGN_UNDEFINED_KIND            = 0x000, // UNUSED
//		DESIGN_META_KIND                 = 0x000, // UNUSED

		DESIGN_MODEL_KIND                = 0x001,

		DESIGN_INSTANCE_KIND             = 0x002,

		DESIGN_STATIC_KIND               = 0x004,

		DESIGN_DYNAMIC_KIND              = 0x008,

		DESIGN_RUNTIME_KIND              = 0x010,

		DESIGN_INSTANCE_STATIC_KIND      = DESIGN_INSTANCE_KIND
		                                 | DESIGN_STATIC_KIND,

		DESIGN_INSTANCE_DYNAMIC_KIND     = DESIGN_INSTANCE_KIND
		                                 | DESIGN_DYNAMIC_KIND,

		// DEFAULT
		DESIGN_PROTOTYPE_STATIC_KIND     = DESIGN_INSTANCE_STATIC_KIND
		                                 | DESIGN_MODEL_KIND,

		DESIGN_PROTOTYPE_DYNAMIC_KIND    = DESIGN_INSTANCE_DYNAMIC_KIND
		                                 | DESIGN_MODEL_KIND,

		DESIGN_INSTANCE_RUNTIME_KIND     = DESIGN_INSTANCE_KIND
		                                 | DESIGN_RUNTIME_KIND,

	};


	/**
	 * TYPEDEF
	 */
	typedef std::uint16_t  bit_field_t;

	/**
	 * BIT FIELDS
	 */

	// group 1 : 16 bits
	bit_field_t is_null_flag   : 1;

	bit_field_t component      : 8;

	bit_field_t computation    : 7;

	// group 2 : 16 bits
	bit_field_t design         : 5;

	bit_field_t group          : 3;

	bit_field_t interaction	   : 4;

	bit_field_t state	       : 4;

	// group 3 : 11 bits
	bit_field_t pseudostate    : 11;

	// group 4 : 6 bits
	bit_field_t feature        : 6;


	/**
	 * ENABLING POSITION
	 */
	enum
	{
		FIELD_COMPONENT_POSITION         = 0x001,
		FIELD_COMPUTATION_POSITION       = 0x002,
		FIELD_GROUP_POSITION             = 0x004,
		FIELD_INTERACTION_POSITION       = 0x008,
		FIELD_STATE_POSITION             = 0x010,
		FIELD_PSEUDOSTATE_POSITION       = 0x020,
		FIELD_FEATURE_POSITION           = 0x040,
		FIELD_DESIGN_POSITION            = 0x080,

		ENABLE_ALL_FIELDS                = 0xFFF,


		ENABLE_COMPONENT_DESIGN_FIELD    = FIELD_COMPONENT_POSITION
		                                 | FIELD_DESIGN_POSITION,

		DISABLE_COMPONENT_DESIGN_FIELD   = (~ ENABLE_COMPONENT_DESIGN_FIELD),


		ENABLE_FEATURE_DESIGN_FIELD      = FIELD_FEATURE_POSITION
		                                 | FIELD_DESIGN_POSITION,

		DISABLE_FEATURE_DESIGN_FIELD     = (~ ENABLE_FEATURE_DESIGN_FIELD),


		ENABLE_COMPONENT_FEATURE_DESIGN_FIELD = FIELD_COMPONENT_POSITION
		                                 | FIELD_FEATURE_POSITION
		                                 | FIELD_DESIGN_POSITION,

		DISABLE_FCOMPONENT_EATURE_DESIGN_FIELD = (~ ENABLE_COMPONENT_FEATURE_DESIGN_FIELD)

	};


	/**
	 * STATIC EXECUTABLE SPECIFIER
	 */
	static Specifier OBJECT_NULL_SPECIFIER;

	static Specifier EXECUTABLE_UNDEFINED_SPECIFIER;

	static Specifier COMPONENT_PACKAGE_SPECIFIER;

	static Specifier COMPONENT_SYSTEM_SPECIFIER;

	static Specifier COMPONENT_EXECUTABLE_SPECIFIER;


	static Specifier COMPONENT_PROCEDURE_SPECIFIER;

	static Specifier EXECUTABLE_PROCEDURE_COMPOSITE_SPECIFIER;

	static Specifier EXECUTABLE_PROCEDURE_MODEL_SPECIFIER;

	static Specifier EXECUTABLE_PROCEDURE_INSTANCE_STATIC_SPECIFIER;


	/**
	 * PROTOTYPE MACHINE FACADE SPECIFIER
	 */
	static Specifier EXECUTABLE_STATEMACHINE_SPECIFIER;


	static Specifier EXECUTABLE_STATE_AND_SPECIFIER;

	static Specifier EXECUTABLE_STATE_OR_SPECIFIER;


	static Specifier EXECUTABLE_STATE_SPECIFIER;

	static Specifier EXECUTABLE_STATE_START_SPECIFIER;

	static Specifier EXECUTABLE_STATE_FINAL_SPECIFIER;


	static Specifier EXECUTABLE_PSEUDOSTATE_INITIAL_SPECIFIER;

	static Specifier EXECUTABLE_PSEUDOSTATE_JUNCTION_SPECIFIER;

	static Specifier EXECUTABLE_PSEUDOSTATE_CHOICE_SPECIFIER;

	static Specifier EXECUTABLE_PSEUDOSTATE_TERMINAL_SPECIFIER;



	/**
	 * EXECUTABLE DESIGN
	 */
	static Specifier DESIGN_MODEL_SPECIFIER;

	static Specifier DESIGN_PROTOTYPE_STATIC_SPECIFIER;

	static Specifier DESIGN_INSTANCE_STATIC_SPECIFIER;

	static Specifier DESIGN_INSTANCE_DYNAMIC_SPECIFIER;



	/**
	 * CONSTRUCTORS
	 */
	Specifier(NULL_FLAG is_null = NULL_FALSE_FLAG )
	: is_null_flag( is_null           ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND ),
	design ( DESIGN_UNDEFINED_KIND  ),

	group( GROUP_UNDEFINED_KIND  ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC   ),
	pseudostate( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}

	Specifier(bit_field_t componentKind, bit_field_t modelOfComputationKind,
			bit_field_t groupKind, bit_field_t interactionOp,
			bit_field_t stateMoc, bit_field_t pseudostateMoc,
			bit_field_t featureKind, bit_field_t designKind)
	: is_null_flag( NULL_FALSE_FLAG ),
	component( componentKind ),
	computation( modelOfComputationKind ),
	design ( designKind  ),

	group( groupKind ),
	interaction( interactionOp ),
	state( stateMoc ),
	pseudostate( pseudostateMoc ),

	feature( featureKind )
	{
		//!! NOTHING
	}

	Specifier(COMPONENT_KIND componentKind,
			MOC_KIND modelOfComputationKind,
			DESIGN_KIND designKind = DESIGN_PROTOTYPE_STATIC_KIND)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( componentKind            ),
	computation( modelOfComputationKind ),
	design ( designKind                 ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}


	Specifier(COMPONENT_KIND componentKind, STATE_MOC stateMoc,
			DESIGN_KIND designKind = DESIGN_INSTANCE_STATIC_KIND)
	: is_null_flag( NULL_FALSE_FLAG ),
	component( componentKind        ),
	computation( MOC_UNDEFINED_KIND ),
	design ( designKind             ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( stateMoc  ),
	pseudostate( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}

	Specifier(COMPONENT_KIND componentKind, PSEUDOSTATE_MOC pseudostateMoc,
			DESIGN_KIND designKind = DESIGN_INSTANCE_STATIC_KIND)
	: is_null_flag( NULL_FALSE_FLAG ),
	component( componentKind        ),
	computation( MOC_UNDEFINED_KIND ),
	design ( designKind             ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate( pseudostateMoc ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}


	Specifier(COMPONENT_KIND componentKind,
			DESIGN_KIND designKind = DESIGN_UNDEFINED_KIND)
	: is_null_flag( NULL_FALSE_FLAG ),
	component( componentKind        ),
	computation( MOC_UNDEFINED_KIND ),
	design ( designKind             ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}


	Specifier(MOC_KIND modelOfComputationKind)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( modelOfComputationKind ),
	design ( DESIGN_UNDEFINED_KIND      ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate ( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}

	Specifier(GROUP_KIND groupKind)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND     ),
	design ( DESIGN_UNDEFINED_KIND      ),

	group( groupKind ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC ),
	pseudostate ( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )

	{
		//!! NOTHING
	}

	Specifier(INTERACTION_MOC interactionOp)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND     ),
	design ( DESIGN_UNDEFINED_KIND      ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( interactionOp  ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate ( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )


	{
		//!! NOTHING
	}

	Specifier(STATE_MOC stateMoc)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND     ),
	design ( DESIGN_UNDEFINED_KIND      ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( stateMoc ),
	pseudostate ( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}

	Specifier(PSEUDOSTATE_MOC pseudostateMoc)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND     ),
	design ( DESIGN_UNDEFINED_KIND      ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate( pseudostateMoc ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}

	Specifier(FEATURE_KIND featureKind)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND     ),
	design ( DESIGN_UNDEFINED_KIND      ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate ( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( featureKind )
	{
		//!! NOTHING
	}

	Specifier(DESIGN_KIND designKind)
	: is_null_flag( NULL_FALSE_FLAG     ),
	component( COMPONENT_UNDEFINED_KIND ),
	computation( MOC_UNDEFINED_KIND     ),
	design ( designKind                 ),

	group( GROUP_UNDEFINED_KIND ),
	interaction( INTERACTION_UNDEFINED_MOC ),
	state( STATE_UNDEFINED_MOC  ),
	pseudostate ( PSEUDOSTATE_UNDEFINED_MOC ),

	feature( FEATURE_UNDEFINED_KIND )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	~Specifier()
	{
		//!! NOTHING
	}


	/**
	 * VALIDITY TEST
	 * _NULL_
	 */
	inline bool isNullref() const
	{
		return( is_null_flag == NULL_TRUE_FLAG );
	}

	inline bool isnotNullref() const
	{
		return( is_null_flag != NULL_TRUE_FLAG );
	}


	/**
	 * TESTER
	 */
	inline bool isDefined() const
	{
		return(    (component   != COMPONENT_UNDEFINED_KIND  )
				|| (computation != MOC_UNDEFINED_KIND        )
				|| (design      != DESIGN_UNDEFINED_KIND     )
				|| (group       != GROUP_UNDEFINED_KIND      )
				|| (interaction != INTERACTION_UNDEFINED_MOC )
				|| (state       != STATE_UNDEFINED_MOC       )
				|| (pseudostate != PSEUDOSTATE_UNDEFINED_MOC )
				|| (feature     != FEATURE_UNDEFINED_KIND    ) );
	}


	inline bool isDefined(bit_field_t enabledFields) const
	{
		return( (((enabledFields     & FIELD_COMPONENT_POSITION  ) != 0)
					&& (component   != COMPONENT_UNDEFINED_KIND  ))

				|| (((enabledFields  & FIELD_COMPUTATION_POSITION) != 0)
					&& (computation != MOC_UNDEFINED_KIND        ))

				|| (((enabledFields  & FIELD_DESIGN_POSITION     ) != 0)
					&& (design      != DESIGN_UNDEFINED_KIND     ))

				|| (((enabledFields  & FIELD_GROUP_POSITION      ) != 0)
					&& (group       != GROUP_UNDEFINED_KIND      ))

				|| (((enabledFields  & FIELD_INTERACTION_POSITION) != 0)
					&& (interaction != INTERACTION_UNDEFINED_MOC ))

				|| (((enabledFields  & FIELD_STATE_POSITION      ) != 0)
					&& (state       != STATE_UNDEFINED_MOC       ))

				|| (((enabledFields  & FIELD_PSEUDOSTATE_POSITION) != 0)
					&& (pseudostate != PSEUDOSTATE_UNDEFINED_MOC ))

				|| (((enabledFields  & FIELD_FEATURE_POSITION    ) != 0)
					&& (feature     != FEATURE_UNDEFINED_KIND    )) );
	}


	inline bool isDefined_otherThan(const Specifier & other) const
	{
		return( ( (*this) & (~ other) ).isDefined() );
	}


	inline bool isUndefined() const
	{
		return(    (component   == COMPONENT_UNDEFINED_KIND  )
				&& (computation == MOC_UNDEFINED_KIND        )
				&& (design      == DESIGN_UNDEFINED_KIND     )
				&& (group       == GROUP_UNDEFINED_KIND      )
				&& (interaction == INTERACTION_UNDEFINED_MOC )
				&& (state       == STATE_UNDEFINED_MOC       )
				&& (pseudostate == PSEUDOSTATE_UNDEFINED_MOC )
				&& (feature     == FEATURE_UNDEFINED_KIND    ) );
	}


	/**
	 * SETTER
	 */
	Specifier & set(const std::string strSpecifier);

	Specifier & setMoc(const std::string strSpecifier);


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR =
	////////////////////////////////////////////////////////////////////////////

	inline Specifier & override_ifdef(const Specifier & other)
	{
		if( other.component != COMPONENT_UNDEFINED_KIND )
		{
			component = other.component;
		}

		if( other.computation != MOC_UNDEFINED_KIND )
		{
			computation = other.computation;
		}

		if( other.design != DESIGN_UNDEFINED_KIND )
		{
			design = other.design;
		}

		if( other.group != GROUP_UNDEFINED_KIND )
		{
			group = other.group;
		}

		if( other.interaction != INTERACTION_UNDEFINED_MOC )
		{
			interaction = other.interaction;
		}
		if( other.state != STATE_UNDEFINED_MOC )
		{
			state = other.state;
		}
		if( other.pseudostate != PSEUDOSTATE_UNDEFINED_MOC )
		{
			pseudostate = other.pseudostate;
		}

		if( other.feature != FEATURE_UNDEFINED_KIND )
		{
			feature |= other.feature;
		}

		return( *this );
	}

	inline Specifier & ifnot_define(const Specifier & other)
	{
		if( component == COMPONENT_UNDEFINED_KIND )
		{
			component = other.component;
		}

		if( (computation <= MOC_COMPOSITE_MASK_KIND)
			&& (other.computation != MOC_UNDEFINED_KIND) )
		{
			computation = other.computation;
		}

		if( design == DESIGN_UNDEFINED_KIND )
		{
			design = other.design;
		}

		if( (group <= GROUP_MASK_KIND)
			&& (other.group != GROUP_UNDEFINED_KIND) )
		{
			group = other.group;
		}

		if( interaction == INTERACTION_UNDEFINED_MOC )
		{
			interaction = other.interaction;
		}

		if( state == STATE_UNDEFINED_MOC )
		{
			state = other.state;
		}
		if( pseudostate == PSEUDOSTATE_UNDEFINED_MOC )
		{
			pseudostate = other.pseudostate;
		}

		if( feature == FEATURE_UNDEFINED_KIND )
		{
			feature |= other.feature;
		}

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR &=
	////////////////////////////////////////////////////////////////////////////

	inline Specifier & operator&=(const Specifier & other)
	{
		component   &= other.component;
		computation &= other.computation;
		design      &= other.design;
		group       &= other.group;
		interaction &= other.interaction;
		state       &= other.state;
		pseudostate &= other.pseudostate;
		feature     &= other.feature;
		return( *this );
	}

	////////////////////////////////////////////////////////////////////////////
	// OPERATOR |=
	////////////////////////////////////////////////////////////////////////////

	inline Specifier & operator|=(const Specifier & other)
	{
		component   |= other.component;
		computation |= other.computation;
		design      |= other.design;
		group       |= other.group;
		interaction |= other.interaction;
		state       |= other.state;
		pseudostate |= other.pseudostate;
		feature     |= other.feature;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR ==  !=
	////////////////////////////////////////////////////////////////////////////

	inline bool operator==(const Specifier & other) const
	{
		return(    (component   == other.component   )
				&& (computation == other.computation )
				&& (design      == other.design      )
				&& (group       == other.group       )
				&& (interaction == other.interaction )
				&& (state       == other.state       )
				&& (pseudostate == other.pseudostate )
				&& (feature     == other.feature     ) );
	}

	inline bool operator!=(const Specifier & other) const
	{
		return(    (component   != other.component   )
				|| (computation != other.computation )
				|| (design      != other.design      )
				|| (group       != other.group       )
				|| (interaction != other.interaction )
				|| (state       != other.state       )
				|| (pseudostate != other.pseudostate )
				|| (feature     != other.feature     ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// OPERATOR |
	////////////////////////////////////////////////////////////////////////////

	inline Specifier operator|(const Specifier & other) const
	{
		return( Specifier(
				component   | other.component,
				computation | other.computation,
				design      | other.design,
				group       | other.group,
				interaction | other.interaction,
				state       | other.state,
				pseudostate | other.pseudostate,
				feature     | other.feature ) );
	}

	////////////////////////////////////////////////////////////////////////////
	// OPERATOR &
	////////////////////////////////////////////////////////////////////////////

	inline Specifier operator&(const Specifier & other) const
	{
		return( Specifier(
				component   & other.component,
				computation & other.computation,
				design      & other.design,
				group       & other.group,
				interaction & other.interaction,
				state       & other.state,
				pseudostate & other.pseudostate,
				feature     & other.feature ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// OPERATOR &
	////////////////////////////////////////////////////////////////////////////

	inline Specifier operator~() const
	{
		return( Specifier(
				(~ component),
				(~ computation),
				(~ design),
				(~ group),
				(~ interaction),
				(~ state),
				(~ pseudostate),
				(~ feature) ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// COMPONENT KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * component
	 */
	inline COMPONENT_KIND getComponentKind() const
	{
		return( static_cast< COMPONENT_KIND >( component ) );
	}

	inline bool hasComponentKind() const
	{
		return( component != COMPONENT_UNDEFINED_KIND );
	}

	inline bool noneComponentKind() const
	{
		return( component == COMPONENT_UNDEFINED_KIND );
	}

	inline bool isComponentKind(COMPONENT_KIND componentKind) const
	{
		return( component == componentKind );
	}

	inline Specifier & addComponentKind(COMPONENT_KIND componentKind)
	{
		component |= componentKind;

		return( *this );
	}

	inline Specifier & remComponentKind(COMPONENT_KIND componentKind)
	{
		component &= (~ componentKind);

		return( *this );
	}

	inline Specifier & setComponentKind(COMPONENT_KIND componentKind)
	{
		component = componentKind;

		return( *this );
	}

	inline Specifier & unsetComponentKind()
	{
		component = COMPONENT_UNDEFINED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "system" component
	 */
	inline bool isComponentSystem() const
	{
		return( component == COMPONENT_SYSTEM_KIND );
	}

	inline bool isnotComponentSystem() const
	{
		return( component != COMPONENT_SYSTEM_KIND );
	}

	inline Specifier & setComponentSystem()
	{
		component = COMPONENT_SYSTEM_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "executable" component
	 */
	inline bool isComponentExecutable() const
	{
		return( component == COMPONENT_EXECUTABLE_KIND );
	}

	inline Specifier & setComponentExecutable()
	{
		component = COMPONENT_EXECUTABLE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "interaction" component
	 */
	inline bool isComponentInteraction() const
	{
		return( component == COMPONENT_INTERACTION_KIND );
	}

	inline Specifier & setComponentInteraction()
	{
		component = COMPONENT_INTERACTION_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "procedure" component
	 */
	inline bool isComponentProcedure() const
	{
		return( component == COMPONENT_PROCEDURE_KIND );
	}

	inline Specifier & setComponentProcedure()
	{
		component = COMPONENT_PROCEDURE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "routine" component
	 */
	inline bool isComponentRoutine() const
	{
		return( component == COMPONENT_ROUTINE_KIND );
	}

	inline Specifier & setComponentRoutine()
	{
		component = COMPONENT_ROUTINE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "statemachine" component
	 */
	inline bool isComponentStatemachine() const
	{
		return( component == COMPONENT_STATEMACHINE_KIND );
	}

	inline Specifier & setComponentStatemachine()
	{
		component = COMPONENT_STATEMACHINE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "state" component
	 */
	inline bool isComponentState() const
	{
		return( component == COMPONENT_STATE_KIND );
	}

	inline Specifier & setComponentState()
	{
		component = COMPONENT_STATE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "pseudostate" component
	 */
	inline bool isComponentPseudostate() const
	{
		return( component == COMPONENT_PSEUDOSTATE_KIND );
	}

	inline Specifier & setComponentPseudostate()
	{
		component = COMPONENT_PSEUDOSTATE_KIND;

		return( *this );
	}



	////////////////////////////////////////////////////////////////////////////
	// MODEL OF COMPUTATION
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * Model Of Computation
	 */
	inline MOC_KIND getModelOfComputation() const
	{
		return( static_cast< MOC_KIND >( computation ) );
	}

	inline bool hasModelOfComputation() const
	{
		return( computation != MOC_UNDEFINED_KIND );
	}

	inline bool isModelOfComputation(MOC_KIND modelOfComputationKind) const
	{
		return( computation == modelOfComputationKind );
	}

	inline Specifier & setModelOfComputation(MOC_KIND modelOfComputationKind)
	{
		computation = modelOfComputationKind;

		return( *this );
	}

	inline Specifier & unsetModelOfComputation()
	{
		computation = MOC_UNDEFINED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "composite" Model Of Computation
	 */
	inline bool hasMocComposite() const
	{
		return( (computation & MOC_COMPOSITE_MASK_KIND) != 0 );
	}

	inline bool noneMocComposite() const
	{
		return( computation == MOC_UNDEFINED_KIND );
	}

	inline Specifier & setMocComposite()
	{
		computation = MOC_COMPOSITE_MASK_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "AND" as composite structure MOC
	 */
	inline bool isMocCompositeStructure() const
	{
		return( computation == MOC_COMPOSITE_STRUCTURE_KIND );
	}

	inline Specifier & setMocCompositeStructure()
	{
		computation = MOC_COMPOSITE_STRUCTURE_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "AND" as composite structure MOC
	 */
	inline bool isMocCompositeInteraction() const
	{
		return( computation == MOC_COMPOSITE_INTERACTION__KIND );
	}

	inline Specifier & setMocCompositeInteraction()
	{
		computation = MOC_COMPOSITE_INTERACTION__KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "OR" as State Transition MOC
	 */
	inline bool isMocStateTransitionStructure() const
	{
		return( (computation & MOC_STATE_TRANSITION_STRUCTURE_KIND)
				== MOC_STATE_TRANSITION_STRUCTURE_KIND );
	}

	/**
	 * GETTER - SETTER
	 * "OR" as State Transition System MOC
	 * has at least one state< simple >
	 */
	inline bool isMocStateTransitionSystem() const
	{
		return( computation == MOC_STATE_TRANSITION_SYSTEM_KIND );
	}

	inline Specifier & setMocStateTransitionSystem()
	{
		computation = MOC_STATE_TRANSITION_SYSTEM_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "OR" as State Transition Flow MOC
	 * has only pseudostate
	 */
	inline bool isMocStateTransitionFlow() const
	{
		return( computation == MOC_STATE_TRANSITION_FLOW_KIND );
	}

	inline Specifier & setMocStateTransitionFlow()
	{
		computation = MOC_STATE_TRANSITION_FLOW_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "FLOW" as DataFlow computation
	 */
	inline bool isCompositeMocDataFlow() const
	{
		return( computation == MOC_DATA_FLOW_KIND );
	}

	inline Specifier & setCompositeMocDataFlow()
	{
		computation = MOC_DATA_FLOW_KIND;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// DESIGN KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * design
	 */
	inline DESIGN_KIND getDesignKind() const
	{
		return( static_cast< DESIGN_KIND >( design ) );
	}

	inline bool hasDesignKind() const
	{
		return( design != DESIGN_UNDEFINED_KIND );
	}

	inline bool noneDesignKind() const
	{
		return( design == DESIGN_UNDEFINED_KIND );
	}

	inline bool hasDesignKind(DESIGN_KIND designKind) const
	{
		return( (design & designKind) != 0 );
	}

	inline bool isDesignKind(DESIGN_KIND designKind) const
	{
		return( design == designKind );
	}

	inline Specifier & setDesignKind(DESIGN_KIND designKind)
	{
		design = designKind;

		return( *this );
	}

	inline Specifier & addDesignKind(DESIGN_KIND designKind)
	{
		design |= designKind;

		return( *this );
	}

	inline Specifier & remDesignKind(DESIGN_KIND designKind)
	{
		design &= (~ designKind);

		return( *this );
	}

	inline Specifier & unsetDesignKind()
	{
		design = DESIGN_UNDEFINED_KIND;

		return( *this );
	}

	static DESIGN_KIND toDesignKind(const std::string & strDesign);


	/**
	 * GETTER - SETTER
	 * "#model" design
	 */
	inline bool isDesignModel() const
	{
		return(design == DESIGN_MODEL_KIND );
	}

	inline bool hasDesignModel() const
	{
		return( (design & DESIGN_MODEL_KIND) != 0 );
	}

	inline Specifier & setDesignModel()
	{
		design = DESIGN_MODEL_KIND;

		return( *this );
	}

	inline Specifier & addDesignModel()
	{
		design |= DESIGN_MODEL_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "#instance" design
	 */
	inline bool isDesignInstance() const
	{
		return(design == DESIGN_INSTANCE_KIND );
	}

	inline bool hasDesignInstance() const
	{
		return( (design & DESIGN_INSTANCE_KIND) != 0 );
	}

	inline Specifier & setDesignInstance()
	{
		design = DESIGN_INSTANCE_KIND;

		return( *this );
	}

	inline Specifier & addDesignInstance()
	{
		design |= DESIGN_INSTANCE_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "#static" design
	 */
	inline bool isDesignStatic() const
	{
		return(design == DESIGN_STATIC_KIND );
	}

	inline bool hasDesignStatic() const
	{
		return( (design & DESIGN_STATIC_KIND) != 0 );
	}

	inline Specifier & setDesignStatic()
	{
		design = DESIGN_STATIC_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "#static instance" design
	 */
	inline bool isDesignInstanceStatic() const
	{
		return(design == DESIGN_INSTANCE_STATIC_KIND );
	}

	inline bool hasDesignInstanceStatic() const
	{
		return( (design & DESIGN_INSTANCE_STATIC_KIND) ==
				DESIGN_INSTANCE_STATIC_KIND );
	}

	inline Specifier & setDesignInstanceStatic()
	{
		design = DESIGN_INSTANCE_STATIC_KIND;

		return( *this );
	}

	inline Specifier & addDesignInstanceStatic()
	{
		design |= DESIGN_INSTANCE_STATIC_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "#static prototype" design
	 */
	inline bool isDesignPrototypeStatic() const
	{
		return(design == DESIGN_PROTOTYPE_STATIC_KIND );
	}

	inline Specifier & setDesignPrototypeStatic()
	{
		design = DESIGN_PROTOTYPE_STATIC_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "dynamic" design
	 */
	inline bool isDesignDynamic() const
	{
		return(design == DESIGN_DYNAMIC_KIND );
	}

	inline bool hasDesignDynamic() const
	{
		return( (design & DESIGN_DYNAMIC_KIND) != 0 );
	}

	inline Specifier & setDesignDynamic()
	{
		design = DESIGN_DYNAMIC_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "#dynamic instance" design
	 */
	inline bool isDesignInstanceDynamic() const
	{
		return(design == DESIGN_INSTANCE_DYNAMIC_KIND );
	}

	inline bool hasDesignInstanceDynamic() const
	{
		return( (design & DESIGN_INSTANCE_DYNAMIC_KIND) ==
					DESIGN_INSTANCE_DYNAMIC_KIND );
	}

	inline Specifier & setDesignInstanceDynamic()
	{
		design = DESIGN_INSTANCE_DYNAMIC_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "instance [ dynamic ]" design
	 */
	inline bool hasDesignInstanceNotModel() const
	{
		return( ((design & DESIGN_INSTANCE_KIND) != 0)
				&& ((design & DESIGN_MODEL_KIND) == 0) );
	}


	/**
	 * GETTER - SETTER
	 * "runtime" design
	 */
	inline bool isDesignRuntime() const
	{
		return(design == DESIGN_RUNTIME_KIND );
	}

	inline Specifier & setDesignRuntime()
	{
		design = DESIGN_RUNTIME_KIND;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// GROUP KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * group
	 */
	inline GROUP_KIND getGroupKind() const
	{
		return( static_cast< GROUP_KIND >( group ) );
	}

	inline bool hasGroupKind() const
	{
		return( group != GROUP_UNDEFINED_KIND );
	}

	inline bool isGroupKind(GROUP_KIND groupKind) const
	{
		return( group == groupKind );
	}

	inline Specifier & setGroupKind(GROUP_KIND groupKind)
	{
		group = groupKind;

		return( *this );
	}

	inline Specifier & unsetGroupKind()
	{
		group = GROUP_UNDEFINED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "group"
	 */
	inline bool hasGroupMask() const
	{
		return( (group & GROUP_MASK_KIND) != 0 );
	}

	inline Specifier & setGroupMasK()
	{
		group = GROUP_MASK_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "some" group
	 */
	inline bool isGroupSome() const
	{
		return( group == GROUP_SOME_KIND );
	}

	inline Specifier & setGroupSome()
	{
		group = GROUP_SOME_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "except" group
	 */
	inline bool isGroupExcept() const
	{
		return( group == GROUP_EXCEPT_KIND );
	}

	inline Specifier & setGroupExcept()
	{
		group = GROUP_EXCEPT_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "every" group
	 */
	inline bool isGroupEvery() const
	{
		return( group == GROUP_EVERY_KIND );
	}

	inline Specifier & setGroupEvery()
	{
		group = GROUP_EVERY_KIND;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// INTERACTION MOC
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * interaction
	 */
	inline INTERACTION_MOC getInteractionMoc() const
	{
		return( static_cast< INTERACTION_MOC >( interaction ) );
	}

	inline bool hasInteractionMoc() const
	{
		return( interaction != INTERACTION_UNDEFINED_MOC );
	}

	inline bool isInteractionMoc(INTERACTION_MOC interactionMoc) const
	{
		return( interaction == interactionMoc );
	}

	inline Specifier & setInteractionMoc(INTERACTION_MOC interactionMoc)
	{
		interaction = interactionMoc;

		return( *this );
	}

	inline Specifier & unsetInteractionMoc()
	{
		interaction = INTERACTION_UNDEFINED_MOC;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "alternative" interaction
	 */
	inline bool isInteractionAlternative() const
	{
		return( interaction == INTERACTION_ALTERNATIVE_MOC );
	}

	inline Specifier & setInteractionAlternative()
	{
		interaction = INTERACTION_ALTERNATIVE_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "option" interaction
	 */
	inline bool isInteractionOption() const
	{
		return( interaction == INTERACTION_OPTION_MOC );
	}

	inline Specifier & setInteractionOption()
	{
		interaction = INTERACTION_OPTION_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "loop" interaction
	 */
	inline bool isInteractionLoop() const
	{
		return( interaction == INTERACTION_LOOP_MOC );
	}

	inline Specifier & setInteractionLoop()
	{
		interaction = INTERACTION_LOOP_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "break" interaction
	 */
	inline bool isInteractionBreak() const
	{
		return( interaction == INTERACTION_BREAK_MOC );
	}

	inline Specifier & setInteractionBreak()
	{
		interaction = INTERACTION_BREAK_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "parallel" interaction
	 */
	inline bool isInteractionParallel() const
	{
		return( interaction == INTERACTION_PARALLEL_MOC );
	}

	inline Specifier & setInteractionParallel()
	{
		interaction = INTERACTION_PARALLEL_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "strict sequence" interaction
	 */
	inline bool isInteractionStrictSequence() const
	{
		return( interaction == INTERACTION_STRICT_SEQUENCE_MOC );
	}

	inline Specifier & setInteractionStrictSequence()
	{
		interaction = INTERACTION_STRICT_SEQUENCE_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "weak sequence" interaction
	 */
	inline bool isInteractionWeakSequence() const
	{
		return( interaction == INTERACTION_WEAK_SEQUENCE_MOC );
	}

	inline Specifier & setInteractionWeakSequence()
	{
		interaction = INTERACTION_WEAK_SEQUENCE_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "critical" interaction
	 */
	inline bool isInteractionCritical() const
	{
		return( interaction == INTERACTION_CRITICAL_MOC );
	}

	inline Specifier & setInteractionCritical()
	{
		interaction = INTERACTION_CRITICAL_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "ignore" interaction
	 */
	inline bool isInteractionIgnore() const
	{
		return( interaction == INTERACTION_IGNORE_MOC );
	}

	inline Specifier & setInteractionIgnore()
	{
		interaction = INTERACTION_IGNORE_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "consider" interaction
	 */
	inline bool isInteractionConsider() const
	{
		return( interaction == INTERACTION_CONSIDER_MOC );
	}

	inline Specifier & setInteractionConsider()
	{
		interaction = INTERACTION_CONSIDER_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "assert" interaction
	 */
	inline bool isInteractionAssert() const
	{
		return( interaction == INTERACTION_ASSERT_MOC );
	}

	inline Specifier & setInteractionAssert()
	{
		interaction = INTERACTION_ASSERT_MOC;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "negative" interaction
	 */
	inline bool isInteractionNegative() const
	{
		return( interaction == INTERACTION_NEGATIVE_MOC );
	}

	inline Specifier & setInteractionNegative()
	{
		interaction = INTERACTION_NEGATIVE_MOC;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// STATE MOC
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * state
	 */
	inline STATE_MOC getStateMoc() const
	{
		return( static_cast< STATE_MOC >( state ) );
	}

	inline bool hasStateMoc() const
	{
		return( state != STATE_UNDEFINED_MOC );
	}

	inline bool noneStateMoc() const
	{
		return( state == STATE_UNDEFINED_MOC );
	}

	inline bool isStateMoc(STATE_MOC stateMoc) const
	{
		return( state == stateMoc );
	}

	inline Specifier & addStateMoc(STATE_MOC stateMoc)
	{
		state |= stateMoc;

		return( *this );
	}

	inline Specifier & remStateMoc(STATE_MOC stateMoc)
	{
		state &= (~ stateMoc);

		return( *this );
	}

	inline Specifier & setStateMoc(STATE_MOC stateMoc)
	{
		state = stateMoc;

		return( *this );
	}

	inline Specifier & unsetStateMoc()
	{
		state = STATE_UNDEFINED_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "state"
	 */
	inline bool isState() const
	{
		return( isComponentState() && hasStateMoc() );
	}


	/**
	 * GETTER - SETTER
	 * "SIMPLE" state
	 */
	inline bool isStateMocSIMPLE() const
	{
		return( state == STATE_SIMPLE_MOC );
	}

	inline Specifier & setStateMocSIMPLE()
	{
		state = STATE_SIMPLE_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "state"
	 */
	inline bool isStateSimple() const
	{
		return( isComponentState() && isStateMocSIMPLE() );
	}

	inline Specifier & setStateSimple()
	{
		setComponentState();
		setStateMocSIMPLE();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "START" state
	 */
	inline bool isStateMocSTART() const
	{
		return( state == STATE_START_MOC );
	}

	inline bool hasStateMocSTART() const
	{
		return( (state & STATE_START_MOC) != 0 );
	}

	inline Specifier & addStateMocSTART()
	{
		state |= STATE_START_MOC;

		return( *this );
	}

	inline Specifier & setStateMocSTART()
	{
		state = STATE_START_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "state"
	 */
	inline bool isStateStart() const
	{
		return( isComponentState() && isStateMocSTART() );
	}

	inline Specifier & setStateStart()
	{
		setComponentState();
		setStateMocSTART();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "FINAL" state
	 */
	inline bool isStateMocFINAL() const
	{
		return( state == STATE_FINAL_MOC );
	}

	inline bool hasStateMocFINAL() const
	{
		return( (state & STATE_FINAL_MOC) != 0 );
	}

	inline Specifier & addStateMocFINAL()
	{
		state |= STATE_FINAL_MOC;

		return( *this );
	}

	inline Specifier & setStateMocFINAL()
	{
		state = STATE_FINAL_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "state"
	 */
	inline bool isStateFinal() const
	{
		return( isComponentState() && isStateMocFINAL() );
	}

	inline Specifier & setStateFinal()
	{
		setComponentState();
		setStateMocFINAL();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "SYNC" state
	 */
	inline bool isStateMocSYNC() const
	{
		return( state == STATE_SYNC_MOC );
	}

	inline Specifier & setStateMocSYNC()
	{
		state = STATE_SYNC_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "state"
	 */
	inline bool isStateSync() const
	{
		return( isComponentState() && isStateMocSYNC() );
	}

	inline Specifier & setStateSync()
	{
		setComponentState();
		setStateMocSYNC();

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// PSEUDOSTATE MOC
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * pseudostate
	 */
	inline PSEUDOSTATE_MOC getPseudostateMoc() const
	{
		return( static_cast< PSEUDOSTATE_MOC >( pseudostate ) );
	}

	inline bool hasPseudostateMoc() const
	{
		return( pseudostate != PSEUDOSTATE_UNDEFINED_MOC );
	}

	inline bool nonePseudostateMoc() const
	{
		return( pseudostate == PSEUDOSTATE_UNDEFINED_MOC );
	}

	inline bool isPseudostateMoc(PSEUDOSTATE_MOC pseudostateMoc) const
	{
		return( pseudostate == pseudostateMoc );
	}

	inline Specifier & addPseudostateMoc(PSEUDOSTATE_MOC pseudostateMoc)
	{
		pseudostate |= pseudostateMoc;

		return( *this );
	}

	inline Specifier & remPseudostateMoc(PSEUDOSTATE_MOC pseudostateMoc)
	{
		pseudostate &= (~ pseudostateMoc);

		return( *this );
	}

	inline Specifier & setPseudostateMoc(PSEUDOSTATE_MOC pseudostateMoc)
	{
		pseudostate = pseudostateMoc;

		return( *this );
	}

	inline Specifier & unsetPseudostateMoc()
	{
		pseudostate = PSEUDOSTATE_UNDEFINED_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostate() const
	{
		return( isComponentPseudostate() && hasPseudostateMoc() );
	}


	/**
	 * GETTER - SETTER
	 * "INITIAL" pseudostate
	 */
	inline bool isPseudostateMocINITIAL() const
	{
		return( pseudostate == PSEUDOSTATE_INITIAL_MOC );
	}

	inline bool hasPseudostateMocINITIAL() const
	{
		return( (pseudostate & PSEUDOSTATE_INITIAL_MOC) != 0 );
	}

	inline Specifier & addPseudostateMocINITIAL()
	{
		pseudostate |= PSEUDOSTATE_INITIAL_MOC;

		return( *this );
	}

	inline Specifier & setPseudostateMocINITIAL()
	{
		pseudostate = PSEUDOSTATE_INITIAL_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateInitial() const
	{
		return( isComponentPseudostate() && isPseudostateMocINITIAL() );
	}

	inline Specifier & setPseudostateInitial()
	{
		setComponentPseudostate();
		setPseudostateMocINITIAL();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "TERMINAL" pseudostate
	 */
	inline bool isPseudostateMocTERMINAL() const
	{
		return( pseudostate == PSEUDOSTATE_TERMINAL_MOC );
	}

	inline bool hasPseudostateMocTERMINAL() const
	{
		return( (pseudostate & PSEUDOSTATE_TERMINAL_MOC) != 0 );
	}

	inline Specifier & addPseudostateMocTERMINAL()
	{
		pseudostate |= PSEUDOSTATE_TERMINAL_MOC;

		return( *this );
	}

	inline Specifier & setPseudostateMocTERMINAL()
	{
		pseudostate = PSEUDOSTATE_TERMINAL_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateTerminal() const
	{
		return( isComponentPseudostate() && isPseudostateMocTERMINAL() );
	}

	inline Specifier & setPseudostateTerminal()
	{
		setComponentPseudostate();
		setPseudostateMocTERMINAL();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "RETURN" pseudostate
	 */
	inline bool isPseudostateMocRETURN() const
	{
		return( pseudostate == PSEUDOSTATE_RETURN_MOC );
	}

	inline bool hasPseudostateMocRETURN() const
	{
		return( (pseudostate & PSEUDOSTATE_RETURN_MOC) != 0 );
	}

	inline Specifier & addPseudostateMocRETURN()
	{
		pseudostate |= PSEUDOSTATE_RETURN_MOC;

		return( *this );
	}

	inline Specifier & setPseudostateMocRETURN()
	{
		pseudostate = PSEUDOSTATE_RETURN_MOC;

		return( *this );
	}


	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateReturn() const
	{
		return( isComponentPseudostate() && isPseudostateMocRETURN() );
	}

	inline Specifier & setPseudostateReturn()
	{
		setComponentPseudostate();
		setPseudostateMocRETURN();

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool hasFamilyPseudostateENDING() const
	{
		return( (pseudostate & FAMILY_PSEUDO_ENDING_MOC) != 0 );
	}

	inline bool hasFamilyPseudostateEnding() const
	{
		return( isComponentPseudostate() && hasFamilyPseudostateENDING() );
	}



	/**
	 * GETTER - SETTER
	 * "JUNCTION" pseudostate
	 */
	inline bool isPseudostateMocJUNCTION() const
	{
		return( pseudostate == PSEUDOSTATE_JUNCTION_MOC );
	}

	inline Specifier & setPseudostateMocJUNCTION()
	{
		pseudostate = PSEUDOSTATE_JUNCTION_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateJunction() const
	{
		return( isComponentPseudostate() && isPseudostateMocJUNCTION() );
	}

	inline Specifier & setPseudostateJunction()
	{
		setComponentPseudostate();
		setPseudostateMocJUNCTION();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "CHOICE" pseudostate
	 */
	inline bool isPseudostateMocCHOICE() const
	{
		return( pseudostate == PSEUDOSTATE_CHOICE_MOC );
	}

	inline Specifier & setPseudostateMocCHOICE()
	{
		pseudostate = PSEUDOSTATE_CHOICE_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateChoice() const
	{
		return( isComponentPseudostate() && isPseudostateMocCHOICE() );
	}

	inline Specifier & setPseudostateChoice()
	{
		setComponentPseudostate();
		setPseudostateMocCHOICE();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "ENTRY_POINT" pseudostate
	 */
	inline bool isPseudostateMocENTRY_POINT() const
	{
		return( pseudostate == PSEUDOSTATE_ENTRY_POINT_MOC );
	}

	inline Specifier & setPseudostateMocENTRY_POINT()
	{
		pseudostate = PSEUDOSTATE_ENTRY_POINT_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateEntryPoint() const
	{
		return( isComponentPseudostate() && isPseudostateMocENTRY_POINT() );
	}

	inline Specifier & setPseudostateEntryPoint()
	{
		setComponentPseudostate();
		setPseudostateMocENTRY_POINT();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "EXIT_POINT" pseudostate
	 */
	inline bool isPseudostateMocEXIT_POINT() const
	{
		return( pseudostate == PSEUDOSTATE_EXIT_POINT_MOC );
	}

	inline Specifier & setPseudostateMocEXIT_POINT()
	{
		pseudostate = PSEUDOSTATE_EXIT_POINT_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateExitPoint() const
	{
		return( isComponentPseudostate() && isPseudostateMocEXIT_POINT() );
	}

	inline Specifier & setPseudostateExitPoint()
	{
		setComponentPseudostate();
		setPseudostateMocEXIT_POINT();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "CONECTION POINT" pseudostate
	 */
	inline bool hasPseudostateMocConnectorPoint() const
	{
		return( (pseudostate & FAMILY_PSEUDO_CONNECTOR_POINT_MOC) != 0 );
	}

	/**
	 * GETTER - SETTER
	 * "FORK" pseudostate
	 */
	inline bool isPseudostateMocFORK() const
	{
		return( pseudostate == PSEUDOSTATE_FORK_MOC );
	}

	inline Specifier & setPseudostateMocFORK()
	{
		pseudostate = PSEUDOSTATE_FORK_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateFork() const
	{
		return( isComponentPseudostate() && isPseudostateMocFORK() );
	}

	inline Specifier & setPseudostateFork()
	{
		setComponentPseudostate();
		setPseudostateMocFORK();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "JOIN" pseudostate
	 */
	inline bool isPseudostateMocJOIN() const
	{
		return( pseudostate == PSEUDOSTATE_JOIN_MOC );
	}

	inline Specifier & setPseudostateMocJOIN()
	{
		pseudostate = PSEUDOSTATE_JOIN_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateJoin() const
	{
		return( isComponentPseudostate() && isPseudostateMocJOIN() );
	}

	inline Specifier & setPseudostateJoin()
	{
		setComponentPseudostate();
		setPseudostateMocJOIN();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "DHISTORY" pseudostate
	 */
	inline bool isPseudostateMocDEEP_HISTORY() const
	{
		return( pseudostate == PSEUDOSTATE_DEEP_HISTORY_MOC );
	}

	inline bool hasPseudostateMocDEEP_HISTORY() const
	{
		return( (pseudostate & PSEUDOSTATE_DEEP_HISTORY_MOC) != 0 );
	}

	inline Specifier & addPseudostateMocDEEP_HISTORY()
	{
		pseudostate |= PSEUDOSTATE_DEEP_HISTORY_MOC;

		return( *this );
	}

	inline Specifier & setPseudostateMocDEEP_HISTORY()
	{
		pseudostate = PSEUDOSTATE_DEEP_HISTORY_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateDeepHistory() const
	{
		return( isComponentPseudostate() && isPseudostateMocDEEP_HISTORY() );
	}

	inline Specifier & setPseudostateDeepHistory()
	{
		setComponentPseudostate();
		setPseudostateMocDEEP_HISTORY();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "SHISTORY" pseudostate
	 */
	inline bool isPseudostateMocSHALLOW_HISTORY() const
	{
		return( pseudostate == PSEUDOSTATE_SHALLOW_HISTORY_MOC );
	}

	inline bool hasPseudostateMocSHALLOW_HISTORY() const
	{
		return( (pseudostate & PSEUDOSTATE_SHALLOW_HISTORY_MOC) != 0 );
	}

	inline Specifier & addPseudostateMocSHALLOW_HISTORY()
	{
		pseudostate |= PSEUDOSTATE_SHALLOW_HISTORY_MOC;

		return( *this );
	}

	inline Specifier & setPseudostateMocSHALLOW_HISTORY()
	{
		pseudostate = PSEUDOSTATE_SHALLOW_HISTORY_MOC;

		return( *this );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool isPseudostateShallowHistory() const
	{
		return( isComponentPseudostate() && isPseudostateMocSHALLOW_HISTORY() );
	}

	inline Specifier & setPseudostateShallowHistory()
	{
		setComponentPseudostate();
		setPseudostateMocSHALLOW_HISTORY();

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "HISTORY" pseudostate
	 */
	inline bool hasPseudostateMocHISTORY() const
	{
		return( (pseudostate & FAMILY_PSEUDO_HISTORY_MOC) != 0 );
	}

	/**
	 * MIX-IN with component "pseudostate"
	 */
	inline bool hasPseudostateHistory() const
	{
		return( isComponentPseudostate() && hasPseudostateMocHISTORY() );
	}


	////////////////////////////////////////////////////////////////////////////
	// FEATURE KIND
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * feature
	 */
	inline FEATURE_KIND getFeatureKind() const
	{
		return( static_cast< FEATURE_KIND >( feature ) );
	}

	inline bool hasFeatureKind() const
	{
		return( feature != FEATURE_UNDEFINED_KIND );
	}

	inline bool hasFeatureKind(FEATURE_KIND designKind) const
	{
		return( (feature & designKind) != 0 );
	}

	inline bool isFeatureKind(FEATURE_KIND designKind) const
	{
		return( feature == designKind );
	}

	inline Specifier & setFeatureKind(FEATURE_KIND designKind)
	{
		feature = designKind;

		return( *this );
	}

	inline Specifier & addFeatureKind(FEATURE_KIND designKind)
	{
		feature |= designKind;

		return( *this );
	}

	inline Specifier & remFeatureKind(FEATURE_KIND designKind)
	{
		feature &= (~ designKind);

		return( *this );
	}

	inline Specifier & unsetFeatureKind()
	{
		feature = FEATURE_UNDEFINED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "timed#continuous" feature
	 */
	inline bool hasFeatureContinuousTimed() const
	{
		return( (feature & FEATURE_CONTINUOUS_TIMED_KIND) != 0 );
	}

	inline bool isFeatureContinuousTimed() const
	{
		return( (feature & FEATURE_TIMED_KIND) == FEATURE_CONTINUOUS_TIMED_KIND );
	}

	inline bool noFeatureContinuousTimed() const
	{
		return( (feature & FEATURE_CONTINUOUS_TIMED_KIND) == 0 );
	}

	inline Specifier & remFeatureContinuousTimed()
	{
		feature &= (~ FEATURE_CONTINUOUS_TIMED_KIND);

		return( *this );
	}

	inline Specifier & setFeatureContinuousTimed()
	{
		feature |= FEATURE_CONTINUOUS_TIMED_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "timed#dense" feature
	 */
	inline bool hasFeatureDenseTimed() const
	{
		return( (feature & FEATURE_DENSE_TIMED_KIND) != 0 );
	}

	inline bool isFeatureDenseTimed() const
	{
		return( (feature & FEATURE_TIMED_KIND) == FEATURE_DENSE_TIMED_KIND );
	}

	inline bool noFeatureDenseTimed() const
	{
		return( (feature & FEATURE_DENSE_TIMED_KIND) == 0 );
	}

	inline Specifier & remFeatureDenseTimed()
	{
		feature &= (~ FEATURE_DENSE_TIMED_KIND);

		return( *this );
	}

	inline Specifier & setFeatureDenseTimed()
	{
		feature |= FEATURE_DENSE_TIMED_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "timed#discrete" feature
	 */
	inline bool hasFeatureDiscreteTimed() const
	{
		return( (feature & FEATURE_DISCRETE_TIMED_KIND) != 0 );
	}

	inline bool isFeatureDiscreteTimed() const
	{
		return( (feature & FEATURE_TIMED_KIND) == FEATURE_DISCRETE_TIMED_KIND );
	}

	inline bool noFeatureDiscreteTimed() const
	{
		return( (feature & FEATURE_DISCRETE_TIMED_KIND) == 0 );
	}

	inline Specifier & remFeatureDiscreteTimed()
	{
		feature &= (~ FEATURE_DISCRETE_TIMED_KIND);

		return( *this );
	}

	inline Specifier & setFeatureDiscreteTimed()
	{
		feature |= FEATURE_DISCRETE_TIMED_KIND;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "timed" feature
	 */
	inline bool hasFeatureTimed() const
	{
		return( (feature & FEATURE_TIMED_KIND) != 0 );
	}

	inline bool isFeatureTimed() const
	{
		return( (feature & FEATURE_TIMED_KIND) == FEATURE_TIMED_KIND );
	}

	inline bool noFeatureTimed() const
	{
		return( (feature & FEATURE_TIMED_KIND) == 0 );
	}

	inline Specifier & remFeatureTimed()
	{
		feature &= (~ FEATURE_TIMED_KIND);

		return( *this );
	}

	inline Specifier & setFeatureTimed()
	{
		feature |= FEATURE_TIMED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "input_enabled" feature
	 */
	inline bool hasFeatureInputEnabled() const
	{
		return( (feature & FEATURE_INPUT_ENABLED_KIND) != 0 );
	}

	inline bool noFeatureInputEnabled() const
	{
		return( (feature & FEATURE_INPUT_ENABLED_KIND) == 0 );
	}

	inline Specifier & remFeatureInputEnabled()
	{
		feature &= (~ FEATURE_INPUT_ENABLED_KIND);

		return( *this );
	}

	inline Specifier & setFeatureInputEnabled()
	{
		feature |= FEATURE_INPUT_ENABLED_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "lifeline" feature
	 */
	inline bool hasFeatureLifeline() const
	{
		return( (feature & FEATURE_LIFELINE_KIND) != 0 );
	}

	inline bool noFeatureLifeline() const
	{
		return( (feature & FEATURE_LIFELINE_KIND) == 0 );
	}

	inline Specifier & remFeatureLifeline()
	{
		feature &= (~ FEATURE_LIFELINE_KIND);

		return( *this );
	}

	inline Specifier & setFeatureLifeline()
	{
		feature |= FEATURE_LIFELINE_KIND;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "user defined schedule" feature
	 */
	inline bool hasFeatureUserDefinedSchedule() const
	{
		return( (feature & FEATURE_USER_DEFINED_SCHEDULE_KIND) != 0 );
	}

	inline bool noFeatureUserDefinedSchedule() const
	{
		return( (feature & FEATURE_USER_DEFINED_SCHEDULE_KIND) == 0 );
	}

	inline Specifier & remFeatureUserDefinedSchedule()
	{
		feature &= (~ FEATURE_USER_DEFINED_SCHEDULE_KIND);

		return( *this );
	}

	inline Specifier & setFeatureUserDefinedSchedule()
	{
		feature |= FEATURE_USER_DEFINED_SCHEDULE_KIND;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// MIX-IN MODIFIER
	////////////////////////////////////////////////////////////////////////////

	// Composite strict by definition:
	// Exclude COMPONENT_STATE_KIND like state< and > &  state< or >
	inline bool isFamilyCompositeComponent() const
	{
		return( hasMocComposite()
				&& ((component & FAMILY_COMPONENT_COMPOSITE_KIND) != 0) );
	}

	// Composite by constitution (or definition):
	// Include COMPONENT_STATE_KIND like state< and > &  state< or >
	inline bool isFamilyComponentComposite() const
	{
		return( hasMocComposite()
				|| ((component & FAMILY_COMPONENT_COMPOSITE_KIND) != 0) );
	}

	inline bool isFamilyComponentState() const
	{
		return( (component & FAMILY_COMPONENT_STATE_KIND) != 0 );
	}

	inline bool isFamilyComponentStatemachine() const
	{
		return( ( (component & FAMILY_COMPONENT_STATEMACHINE_KIND) != 0) );
//				|| isMocStateTransitionStructure() );
	}


	inline bool isStateBasic() const
	{
		return( noneMocComposite() && (isState() || isPseudostate()) );
	}

	inline bool isStateComposite() const
	{
		return( hasMocComposite() && isState() );
	}

	inline bool isPseudostateInitialOrStateStart() const
	{
		return( isPseudostateInitial() || isStateStart() );
	}

	inline bool hasMocINITIAL_START() const
	{
		return( hasPseudostateMocINITIAL() || hasStateMocSTART() );
	}

	inline bool couldBeStateMocSIMPLE() const
	{
		return( noneStateMoc() && nonePseudostateMoc() && noneMocComposite() );
	}



	/**
	 * COMPONENT KIND to STRING
	 */
	inline std::string keywordComponent() const
	{
		return( Specifier::keywordComponent( component ) );
	}

	static std::string keywordComponent(bit_field_t componentKind);


	inline std::string strComponent(const std::string & separator = " ") const
	{
		return( Specifier::strComponent( component , separator ) );
	}

	static std::string strComponent(bit_field_t componentKind,
			const std::string & separator = " ");

	static std::string xstrComponent(bit_field_t direction,
			const std::string & separator = " ");

	/**
	 * COMPOSITE MOC to STRING
	 */
	inline std::string strModelOfComputation(
			const std::string & separator = " ") const
	{
		return( Specifier::strModelOfComputation( computation , separator ) );
	}

	static std::string strModelOfComputation(
			bit_field_t modelOfComputationKind,
			const std::string & separator = " ");

	/**
	 * GROUP KIND to STRING
	 */
	inline std::string strGroup(const std::string & separator = " ") const
	{
		return( Specifier::strGroup( group , separator ) );
	}

	static std::string strGroup(bit_field_t groupKind,
			const std::string & separator = " ");

	/**
	 * INTERACTION MOC to STRING
	 */
	inline std::string strInteractionMoc(const std::string & separator = " ") const
	{
		return( Specifier::strInteractionMoc( interaction , separator ) );
	}

	static std::string strInteractionMoc(bit_field_t interactionMoc,
			const std::string & separator = " ");

	static std::string xstrInteractionMoc(bit_field_t interactionMoc,
			const std::string & separator = " ");

	/**
	 * STATE MOC to STRING
	 */
	inline std::string strStateMoc(const std::string & separator = " ") const
	{
		return( Specifier::strStateMoc( state , separator ) );
	}

	static std::string strStateMoc(bit_field_t stateMoc,
			const std::string & separator = " ");

	static std::string xstrStateMoc(bit_field_t stateMoc,
			const std::string & separator = " ");

	/**
	 * PSEUDOSTATE MOC to STRING
	 */
	inline std::string strPseudostateMoc(
			const std::string & separator = " ") const
	{
		return( Specifier::strPseudostateMoc( pseudostate , separator ) );
	}

	static std::string strPseudostateMoc(bit_field_t pseudostateMoc,
			const std::string & separator = " ");

	static std::string xstrPseudostateMoc(bit_field_t pseudostateMoc,
			const std::string & separator = " ");

	/**
	 * ANY-STATE MOC to STRING
	 */
	inline std::string strAnyStateMoc(
			const std::string & separator = " ") const
	{
		if( pseudostate != PSEUDOSTATE_UNDEFINED_MOC )
		{
			return( Specifier::strPseudostateMoc( pseudostate , separator ) );
		}
		else if( state != STATE_UNDEFINED_MOC )
		{
			return( Specifier::strStateMoc( pseudostate , separator ) );
		}
		else if( computation != MOC_UNDEFINED_KIND )
		{
			return( Specifier::strModelOfComputation( computation , separator ) );
		}
		else
		{
			return( "<any:state:undef>" );
		}
	}


	/**
	 * FEATURE KIND to STRING
	 */
	inline std::string strFeature(const std::string & separator = " ") const
	{
		return( Specifier::strFeature( feature , separator ) );
	}

	static std::string strFeature(bit_field_t featureKind,
			const std::string & separator = " ");

	/**
	 * DESIGN KIND to STRING
	 */
	inline std::string strDesign(const std::string & separator = " ") const
	{
		return( Specifier::strDesign( design , separator ) );
	}

	std::string strDesign_not(DESIGN_KIND designKind,
			const std::string & separator = " ") const;

	static std::string strDesign(bit_field_t designKind,
			const std::string & separator = " ");

	static std::string xstrDesign(bit_field_t designKind,
			const std::string & separator = " ");


	/**
	 * Serialization
	 */
	static std::string SEPARATOR;


	inline std::string str(bit_field_t enabledFields,
			const std::string & separator = SEPARATOR) const
	{
		return( StringTools::removeLastIfEndsWith(
				toString(enabledFields, separator ), separator) );
	}

	inline std::string str(const std::string & separator = SEPARATOR) const
	{
		return( StringTools::removeLastIfEndsWith(
				toString(ENABLE_ALL_FIELDS, separator ), separator) );
	}

	inline std::string str_otherThan(
			Specifier::COMPONENT_KIND componentKing,
			const std::string & separator = SEPARATOR) const
	{
		Specifier xSpecifier( *this );

		xSpecifier.remComponentKind( componentKing );

		return( StringTools::removeLastIfEndsWith(
				xSpecifier.toString( separator ), separator) );

	}

	inline std::string str_otherThan(
			Specifier::COMPONENT_KIND componentKing,
			Specifier::STATE_MOC stateMoc,
			const std::string & separator = SEPARATOR) const
	{
		Specifier xSpecifier( *this );

		xSpecifier.remComponentKind( componentKing );

		xSpecifier.remStateMoc( stateMoc );

		return( StringTools::removeLastIfEndsWith(
				xSpecifier.toString( separator ), separator) );

	}

	std::string toString(bit_field_t enabledFields = ENABLE_ALL_FIELDS,
			const std::string & separator = " ") const;

	inline std::string toString(const std::string & separator) const
	{
		return( toString( ENABLE_ALL_FIELDS , separator) );
	}


	std::string toString_not(DESIGN_KIND designKind,
			const std::string & separator = " ") const
	{
		return( Specifier::strComponent( component , separator ) +
				Specifier::strModelOfComputation( computation , separator ) +
				Specifier::strGroup   ( group , separator ) +
				Specifier::strStateMoc( state , separator ) +
				Specifier::strPseudostateMoc( pseudostate , separator ) +
				Specifier::strFeature( feature , separator ) +
				Specifier::strDesign_not( designKind , separator) );
	}

};



class SpecifierImpl
{

protected:
	/**
	 * ATTRIBUTES
	 */
	Specifier mSpecifier;


public:
	/**
	 * CONSTRUCTOR
	 */
	SpecifierImpl()
	: mSpecifier( )
	{
		//!! NOTHING
	}

	SpecifierImpl(const Specifier & aSpecifier)
	: mSpecifier( aSpecifier )
	{
		//!! NOTHING
	}

	SpecifierImpl(const SpecifierImpl & aCopy)
	: mSpecifier( aCopy.mSpecifier )
	{
		//!! NOTHING
	}

	SpecifierImpl(const SpecifierImpl * aCopy)
	: mSpecifier( (aCopy != nullptr) ?
			aCopy->getSpecifier() : Specifier::EXECUTABLE_UNDEFINED_SPECIFIER )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	~SpecifierImpl()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mSpecifier
	 */
	inline const Specifier & getSpecifier() const
	{
		return( mSpecifier );
	}

	inline Specifier & getwSpecifier()
	{
		return( mSpecifier );
	}

	inline bool hasSpecifier() const
	{
		return( mSpecifier.isDefined() );
	}

	inline bool hasSpecifier_otherThan(const Specifier & aSpecifier) const
	{
		return( mSpecifier.isDefined_otherThan( aSpecifier ) );
	}

	inline void setSpecifier(const Specifier & xSpecifier)
	{
		mSpecifier = xSpecifier;
	}

};


} /* namespace sep */

#endif /* FML_COMMON_SPECIFIERELEMENT_H_ */
