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

#include "SpecifierElement.h"

#include <sstream>


namespace sep
{


/**
 * STATIC EXECUTABLE SPECIFIER
 */
Specifier Specifier::OBJECT_NULL_SPECIFIER( NULL_TRUE_FLAG );

Specifier Specifier::EXECUTABLE_UNDEFINED_SPECIFIER;

Specifier Specifier::COMPONENT_PACKAGE_SPECIFIER(
		Specifier::COMPONENT_UNDEFINED_KIND);//*COMPONENT_PACKAGE_KIND);

Specifier Specifier::COMPONENT_SYSTEM_SPECIFIER(
		Specifier::COMPONENT_SYSTEM_KIND );

Specifier Specifier::COMPONENT_EXECUTABLE_SPECIFIER(
		Specifier::COMPONENT_EXECUTABLE_KIND );


Specifier Specifier::COMPONENT_PROCEDURE_SPECIFIER(
		Specifier::COMPONENT_PROCEDURE_KIND );

Specifier Specifier::EXECUTABLE_PROCEDURE_COMPOSITE_SPECIFIER(
		Specifier::COMPONENT_PROCEDURE_KIND,
		Specifier::MOC_COMPOSITE_STRUCTURE_KIND );

Specifier Specifier::EXECUTABLE_PROCEDURE_MODEL_SPECIFIER(
		Specifier::COMPONENT_PROCEDURE_KIND,
		Specifier::DESIGN_MODEL_KIND );

Specifier Specifier::EXECUTABLE_PROCEDURE_INSTANCE_STATIC_SPECIFIER(
		Specifier::COMPONENT_PROCEDURE_KIND,
		Specifier::DESIGN_INSTANCE_STATIC_KIND );


/**
 * PROTOTYPE MACHINE FACADE SPECIFIER
 */
Specifier Specifier::EXECUTABLE_STATEMACHINE_SPECIFIER(
		Specifier::COMPONENT_STATEMACHINE_KIND,
		Specifier::MOC_STATE_TRANSITION_SYSTEM_KIND,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );


Specifier Specifier::EXECUTABLE_STATE_AND_SPECIFIER(
		Specifier::COMPONENT_STATE_KIND,
		Specifier::MOC_COMPOSITE_STRUCTURE_KIND,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );

Specifier Specifier::EXECUTABLE_STATE_OR_SPECIFIER(
		Specifier::COMPONENT_STATE_KIND,
		Specifier::MOC_STATE_TRANSITION_SYSTEM_KIND,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );


Specifier Specifier::EXECUTABLE_STATE_SPECIFIER(
		Specifier::COMPONENT_STATE_KIND,
		Specifier::STATE_SIMPLE_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );

Specifier Specifier::EXECUTABLE_STATE_START_SPECIFIER(
		Specifier::COMPONENT_STATE_KIND,
		Specifier::STATE_START_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );

Specifier Specifier::EXECUTABLE_STATE_FINAL_SPECIFIER(
		Specifier::COMPONENT_STATE_KIND,
		Specifier::STATE_FINAL_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );


Specifier Specifier::EXECUTABLE_PSEUDOSTATE_INITIAL_SPECIFIER(
		Specifier::COMPONENT_PSEUDOSTATE_KIND,
		Specifier::PSEUDOSTATE_INITIAL_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );

Specifier Specifier::EXECUTABLE_PSEUDOSTATE_JUNCTION_SPECIFIER(
		Specifier::COMPONENT_PSEUDOSTATE_KIND,
		Specifier::PSEUDOSTATE_JUNCTION_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );

Specifier Specifier::EXECUTABLE_PSEUDOSTATE_CHOICE_SPECIFIER(
		Specifier::COMPONENT_PSEUDOSTATE_KIND,
		Specifier::PSEUDOSTATE_CHOICE_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );

Specifier Specifier::EXECUTABLE_PSEUDOSTATE_TERMINAL_SPECIFIER(
		Specifier::COMPONENT_PSEUDOSTATE_KIND,
		Specifier::PSEUDOSTATE_TERMINAL_MOC,
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND );


/**
 * EXECUTABLE DESIGN
 */
Specifier Specifier::DESIGN_MODEL_SPECIFIER(
		Specifier::DESIGN_MODEL_KIND);

Specifier Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER(
		Specifier::DESIGN_PROTOTYPE_STATIC_KIND);

Specifier Specifier::DESIGN_INSTANCE_STATIC_SPECIFIER(
		Specifier::DESIGN_INSTANCE_STATIC_KIND);

Specifier Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER(
		Specifier::DESIGN_INSTANCE_DYNAMIC_KIND);


////////////////////////////////////////////////////////////////////////////////
// SCOPE <KIND
////////////////////////////////////////////////////////////////////////////////

Specifier::SCOPE_KIND Specifier::toScope(const std::string & id)
{
	if( id == "machine"    ) return SCOPE_MACHINE_KIND;

	if( id == "program"    ) return SCOPE_PROGRAM_KIND;

	if( id == "transition" ) return SCOPE_TRANSITION_KIND;

	if( id == "routine"    ) return SCOPE_ROUTINE_KIND;

	if( id == "runnable"   ) return SCOPE_RUNNABLE_KIND;

	return SCOPE_UNDEFINED_KIND;
}


std::string Specifier::strScope(SCOPE_KIND kind)
{
	switch( kind )
	{
		case SCOPE_MACHINE_KIND    : return( "machine"    );

		case SCOPE_PROGRAM_KIND    : return( "program"    );

		case SCOPE_TRANSITION_KIND : return( "transition" );

		case SCOPE_ROUTINE_KIND    : return( "routine"    );

		case SCOPE_RUNNABLE_KIND   : return( "runnable"   );

		case SCOPE_UNDEFINED_KIND  : return( "undefined<specifier#scope#kind>");

		default                    : return( "unknown<specifier#scope#kind>" );
	}
}


/**
 * SETTER
 */
Specifier & Specifier::set(const std::string strSpecifier)
{
#define IF_IS( spec  )  if( strSpecifier == spec )
#define IF_HAS( spec )  if( strSpecifier.find(spec) != std::string::npos )

	IF_HAS( "executable"     ) { setComponentExecutable();   }
	IF_HAS( "machine"        ) { setComponentExecutable();   }
	IF_HAS( "interaction"    ) { setComponentInteraction();  }
	IF_HAS( "system"         ) { setComponentSystem();       }
	IF_HAS( "procedure"      ) { setComponentProcedure();    }

	IF_HAS( "package"        ) { /*setComponentPackage();*/  }


	IF_HAS( "group"          ) { setGroupMasK();   }
	IF_HAS( "every"          ) { setGroupEvery();  }
	IF_HAS( "some"           ) { setGroupSome();   }
	IF_HAS( "except"         ) { setGroupExcept(); }

	IF_HAS( "composite"      ) { setMocComposite();             }
	IF_HAS( "and"            ) { setMocCompositeStructure();    }

	IF_HAS( "alt"            ) { setInteractionAlternative();    }
	IF_HAS( "opt"            ) { setInteractionOption();         }
	IF_HAS( "loop"           ) { setInteractionLoop();           }
	IF_HAS( "break"          ) { setInteractionBreak();          }
	IF_HAS( "par"            ) { setInteractionParallel();       }
	IF_HAS( "strict"         ) { setInteractionStrictSequence(); }
	IF_HAS( "weak"           ) { setInteractionWeakSequence();   }
	IF_HAS( "seq"            ) { setInteractionWeakSequence();   }
	IF_HAS( "critical"       ) { setInteractionCritical();       }
	IF_HAS( "ignore"         ) { setInteractionIgnore();         }
	IF_HAS( "consider"       ) { setInteractionConsider();       }
	IF_HAS( "assert"         ) { setInteractionAssert();         }
	IF_HAS( "neg"            ) { setInteractionNegative();       }

	IF_HAS( "or"             ) { setMocStateTransitionSystem(); }
	IF_HAS( "STS"            ) { setMocStateTransitionSystem(); }
	IF_HAS( "stf"            ) { setMocStateTransitionFlow();   }
	IF_HAS( "STF"            ) { setMocStateTransitionFlow();   }

	IF_HAS( "flow"           ) { setCompositeMocDataFlow();     }
	IF_HAS( "DF"             ) { setCompositeMocDataFlow();     }

	IF_HAS( "simple"         ) { setStateMocSIMPLE();  }
	IF_HAS( "start"          ) { setStateMocSTART();   }
	IF_HAS( "final"          ) { setStateMocFINAL();   }
	IF_HAS( "sync"           ) { setStateMocSYNC();    }

	IF_HAS( "initial"        ) { setPseudostateMocINITIAL();  }
	IF_HAS( "terminal"       ) { setPseudostateMocTERMINAL(); }
	IF_HAS( "return"         ) { setPseudostateMocRETURN();   }

	IF_HAS( "junction"       ) { setPseudostateMocJUNCTION(); }
	IF_HAS( "choice"         ) { setPseudostateMocCHOICE();   }

	IF_HAS( "fork"           ) { setPseudostateMocFORK();     }
	IF_HAS( "join"           ) { setPseudostateMocJOIN();     }

	IF_HAS( "dhistory"       ) { setPseudostateMocDEEP_HISTORY();    }
	IF_HAS( "deepHistory"    ) { setPseudostateMocDEEP_HISTORY();    }

	IF_HAS( "shistory"       ) { setPseudostateMocSHALLOW_HISTORY(); }
	IF_HAS( "shallowHistory" ) { setPseudostateMocSHALLOW_HISTORY(); }

	IF_HAS( "history"        ) { setPseudostateMocSHALLOW_HISTORY(); }

	return( *this );
}


Specifier & Specifier::setMoc(const std::string strSpecifier)
{
#define IF_HAS( spec )  if( strSpecifier.find(spec) != std::string::npos )

	IF_HAS( "composite"      ) { setMocComposite();              }

	IF_HAS( "interaction"    ) { setMocCompositeInteraction();   }

	IF_HAS( "alt"            ) { setInteractionAlternative();    }
	IF_HAS( "opt"            ) { setInteractionOption();         }
	IF_HAS( "loop"           ) { setInteractionLoop();           }
	IF_HAS( "break"          ) { setInteractionBreak();          }
	IF_HAS( "par"            ) { setInteractionParallel();       }
	IF_HAS( "strict"         ) { setInteractionStrictSequence(); }
	IF_HAS( "weak"           ) { setInteractionWeakSequence();   }
	IF_HAS( "seq"            ) { setInteractionWeakSequence();   }
	IF_HAS( "critical"       ) { setInteractionCritical();       }
	IF_HAS( "ignore"         ) { setInteractionIgnore();         }
	IF_HAS( "consider"       ) { setInteractionConsider();       }
	IF_HAS( "assert"         ) { setInteractionAssert();         }
	IF_HAS( "neg"            ) { setInteractionNegative();       }

	IF_HAS( "and"            ) { setMocCompositeStructure();     }

	IF_HAS( "or"             ) { setMocStateTransitionSystem();  }
	IF_HAS( "sts"            ) { setMocStateTransitionSystem();  }
	IF_HAS( "STS"            ) { setMocStateTransitionSystem();  }
	IF_HAS( "stf"            ) { setMocStateTransitionFlow();    }
	IF_HAS( "STF"            ) { setMocStateTransitionFlow();    }

	IF_HAS( "flow"           ) { setCompositeMocDataFlow();      }
	IF_HAS( "DF"             ) { setCompositeMocDataFlow();      }

	IF_HAS( "simple"         ) { setStateMocSIMPLE();  }
	IF_HAS( "start"          ) { setStateMocSTART();   }
	IF_HAS( "final"          ) { setStateMocFINAL();   }
	IF_HAS( "sync"           ) { setStateMocSYNC();    }

	IF_HAS( "initial"        ) { setPseudostateMocINITIAL();  }
	IF_HAS( "terminal"       ) { setPseudostateMocTERMINAL(); }
	IF_HAS( "return"         ) { setPseudostateMocRETURN();   }

	IF_HAS( "junction"       ) { setPseudostateMocJUNCTION(); }
	IF_HAS( "choice"         ) { setPseudostateMocCHOICE();   }

	IF_HAS( "fork"           ) { setPseudostateMocFORK();     }
	IF_HAS( "join"           ) { setPseudostateMocJOIN();     }

	IF_HAS( "dhistory"       ) { setPseudostateMocDEEP_HISTORY();    }
	IF_HAS( "deepHistory"    ) { setPseudostateMocDEEP_HISTORY();    }

	IF_HAS( "shistory"       ) { setPseudostateMocSHALLOW_HISTORY(); }
	IF_HAS( "shallowHistory" ) { setPseudostateMocSHALLOW_HISTORY(); }

	IF_HAS( "history"        ) { setPseudostateMocSHALLOW_HISTORY(); }

	return( *this );
}


/**
 * STRING TO DESIGN KIND
 */
Specifier::DESIGN_KIND Specifier::toDesignKind(const std::string & strDesign)
{
	std::string aDesign = strDesign;
	StringTools::tolower(aDesign);

	if( aDesign == "instance" )
	{
		return( Specifier::DESIGN_INSTANCE_KIND );
	}
	else if( (aDesign == "model") || (aDesign == "form") )
	{
		return( Specifier::DESIGN_MODEL_KIND );

	}
	else if( aDesign == "prototype" )
	{
		return( Specifier::DESIGN_PROTOTYPE_STATIC_KIND );
	}

	else if( aDesign == "dynamic" )
	{
		return( Specifier::DESIGN_DYNAMIC_KIND );
	}
	else if( aDesign == "runtime" )
	{
		return( Specifier::DESIGN_RUNTIME_KIND );
	}
//	else if( aDesign == "meta" )
//	{
//		return( Specifier::DESIGN_META_KIND );
//	}
	else
	{
		return( Specifier::DESIGN_UNDEFINED_KIND );
	}
}


/**
 * COMPONENT KIND to STRING
 */
std::string Specifier::keywordComponent(bit_field_t componentKind)
{
	switch( componentKind )
	{
		case COMPONENT_UNDEFINED_KIND:
			return( "<keyword:component:undef>" );

		case COMPONENT_SYSTEM_KIND:
			return( "system" );

		case COMPONENT_EXECUTABLE_KIND:
			return( "executable" );

		case COMPONENT_PROCEDURE_KIND:
			return( "procedure" );

		case COMPONENT_ROUTINE_KIND:
			return( "routine" );

		case COMPONENT_INTERACTION_KIND:
			return( "interaction" );

		case COMPONENT_STATEMACHINE_KIND:
			return( "statemachine" );

		case COMPONENT_STATE_KIND:
			return( "state" );

		case COMPONENT_PSEUDOSTATE_KIND:
//			return( "pseudostate" );
			return( "state" );

		default:
			return( xstrComponent(componentKind, "#") );
	}
}


std::string Specifier::strComponent(
		bit_field_t componentKind, const std::string & separator)
{
	switch( componentKind )
	{
		case COMPONENT_UNDEFINED_KIND:
			return( "" );
//			return( "<component:undef>" + separator );

		case COMPONENT_SYSTEM_KIND:
			return( "system" + separator );

		case COMPONENT_EXECUTABLE_KIND:
			return( "executable" + separator );

		case COMPONENT_PROCEDURE_KIND:
			return( "procedure" + separator );

		case COMPONENT_ROUTINE_KIND:
			return( "routine" + separator );

		case COMPONENT_INTERACTION_KIND:
			return( "interaction" + separator );

		case COMPONENT_STATEMACHINE_KIND:
			return( "statemachine" + separator );

		case COMPONENT_STATE_KIND:
			return( "state" + separator );

		case COMPONENT_PSEUDOSTATE_KIND:
			return( "pseudostate" + separator );

		default:
			return( xstrComponent(componentKind, separator) );
	}
}


std::string Specifier::xstrComponent(
		bit_field_t componentKind, const std::string & separator)
{
	if( componentKind != COMPONENT_UNDEFINED_KIND)
	{
		std::ostringstream oss;

		if( (componentKind & COMPONENT_SYSTEM_KIND) != 0 )
		{
			oss << "system" << separator;
		}

		if( (componentKind & COMPONENT_EXECUTABLE_KIND) != 0 )
		{
			oss << "executable" << separator;
		}

		if( (componentKind & COMPONENT_PROCEDURE_KIND) != 0 )
		{
			oss << "procedure" << separator;
		}
		if( (componentKind & COMPONENT_ROUTINE_KIND) != 0 )
		{
			oss << "routine" << separator;
		}

		if( (componentKind & COMPONENT_INTERACTION_KIND) != 0 )
		{
			oss << "interaction" << separator;
		}

		if( (componentKind & COMPONENT_STATEMACHINE_KIND) != 0 )
		{
			oss << "statemachine" << separator;
		}
		if( (componentKind & COMPONENT_STATE_KIND) != 0 )
		{
			oss << "state" << separator;
		}
		if( (componentKind & COMPONENT_PSEUDOSTATE_KIND) != 0 )
		{
			oss << "pseudostate" << separator;
		}

		return( oss.str() );
	}

	return "<component:undef>";
}


/**
 * COMPOSITE MOC to STRING
 */
std::string Specifier::strModelOfComputation(
		bit_field_t modelOfComputationKind, const std::string & separator)
{
	switch( modelOfComputationKind )
	{
		case MOC_UNDEFINED_KIND:
			return( "" );
//			return( "<composite:undef>" + separator );

		case MOC_COMPOSITE_STRUCTURE_KIND:
			return( "and" + separator );

		case MOC_COMPOSITE_INTERACTION__KIND:
			return( "interaction" + separator );

		case MOC_STATE_TRANSITION_SYSTEM_KIND:
			return( "or" + separator );

		case MOC_STATE_TRANSITION_FLOW_KIND:
			return( "#STF" + separator );

		case MOC_STATE_TRANSITION_STRUCTURE_KIND:
			return( "#STS" + separator );

		case MOC_DATA_FLOW_KIND:
			return( "#DF" + separator );

		case MOC_COMPOSITE_MASK_KIND:
			return( "composite" + separator );

		default:
			return( "<composite:unknown>" + separator );
	}
}


/**
 * GROUP KIND to STRING
 */
std::string Specifier::strGroup(
		bit_field_t groupKind, const std::string & separator)
{
	switch( groupKind )
	{
		case GROUP_UNDEFINED_KIND:
			return( "" );
//			return( "<group:undef>" + separator );

		case GROUP_EVERY_KIND:
			return( "every" + separator );

		case GROUP_SOME_KIND:
			return( "some" + separator );

		case GROUP_EXCEPT_KIND:
			return( "except" + separator );

		case GROUP_MASK_KIND:
			return( "group" + separator );

		default:
			return( "<group:unknown>" + separator );
	}
}


/**
 * STATE MOC to STRING
 */
std::string Specifier::strInteractionMoc(
		bit_field_t interactionMoc, const std::string & separator)
{
	switch( interactionMoc )
	{
		case INTERACTION_UNDEFINED_MOC:
			return( "" );
//			return( "<interaction:undef>" + separator );

		case INTERACTION_ALTERNATIVE_MOC:
			return( "alt" + separator );

		case INTERACTION_OPTION_MOC:
			return( "option" + separator );

		case INTERACTION_LOOP_MOC:
			return( "loop" + separator );

		case INTERACTION_BREAK_MOC:
			return( "break" + separator );

		case INTERACTION_PARALLEL_MOC:
			return( "par" + separator );

		case INTERACTION_STRICT_SEQUENCE_MOC:
			return( "strict" + separator );

		case INTERACTION_WEAK_SEQUENCE_MOC:
			return( "seq" + separator );

		case INTERACTION_CRITICAL_MOC:
			return( "critical" + separator );

		case INTERACTION_IGNORE_MOC:
			return( "ignore" + separator );

		case INTERACTION_CONSIDER_MOC:
			return( "consider" + separator );

		case INTERACTION_ASSERT_MOC:
			return( "assert" + separator );

		case INTERACTION_NEGATIVE_MOC:
			return( "neg" + separator );

		default:
			return( xstrInteractionMoc(interactionMoc, separator) );
	}
}


std::string Specifier::xstrInteractionMoc(
		bit_field_t interactionMoc, const std::string & separator)
{
	if( interactionMoc != INTERACTION_UNDEFINED_MOC)
	{
		std::ostringstream oss;

		if( (interactionMoc & INTERACTION_ALTERNATIVE_MOC) != 0 )
		{
			oss << "alt" << separator;
		}
		if( (interactionMoc & INTERACTION_OPTION_MOC) != 0 )
		{
			oss << "option" << separator;
		}
		if( (interactionMoc & INTERACTION_LOOP_MOC) != 0 )
		{
			oss << "loop" << separator;
		}
		if( (interactionMoc & INTERACTION_BREAK_MOC) != 0 )
		{
			oss << "break" << separator;
		}
		if( (interactionMoc & INTERACTION_PARALLEL_MOC) != 0 )
		{
			oss << "par" << separator;
		}
		if( (interactionMoc & INTERACTION_STRICT_SEQUENCE_MOC) != 0 )
		{
			oss << "strict" << separator;
		}
		if( (interactionMoc & INTERACTION_WEAK_SEQUENCE_MOC) != 0 )
		{
			oss << "seq" << separator;
		}
		if( (interactionMoc & INTERACTION_CRITICAL_MOC) != 0 )
		{
			oss << "critical" << separator;
		}
		if( (interactionMoc & INTERACTION_IGNORE_MOC) != 0 )
		{
			oss << "ignore" << separator;
		}
		if( (interactionMoc & INTERACTION_CONSIDER_MOC) != 0 )
		{
			oss << "consider" << separator;
		}
		if( (interactionMoc & INTERACTION_ASSERT_MOC) != 0 )
		{
			oss << "assert" << separator;
		}
		if( (interactionMoc & INTERACTION_NEGATIVE_MOC) != 0 )
		{
			oss << "neg" << separator;
		}

		return( oss.str() );
	}

	return "<interaction:undef>";
}


/**
 * STATE MOC to STRING
 */
std::string Specifier::strStateMoc(
		bit_field_t stateMoc, const std::string & separator)
{
	switch( stateMoc )
	{
		case STATE_UNDEFINED_MOC:
			return( "" );
//			return( "<state:undef>" + separator );

		case STATE_SIMPLE_MOC:
			return( "simple" + separator );

		case STATE_START_MOC:
			return( "start" + separator );

		case STATE_FINAL_MOC:
			return( "final" + separator );

		case STATE_SYNC_MOC:
			return( "sync" + separator );

		default:
			return( xstrStateMoc(stateMoc, separator) );
	}
}


std::string Specifier::xstrStateMoc(
		bit_field_t stateMoc, const std::string & separator)
{
	if( stateMoc != STATE_UNDEFINED_MOC)
	{
		std::ostringstream oss;

		if( (stateMoc & STATE_SIMPLE_MOC) != 0 )
		{
			oss << "simple" << separator;
		}
		if( (stateMoc & STATE_START_MOC) != 0 )
		{
			oss << "start" << separator;
		}
		if( (stateMoc & STATE_FINAL_MOC) != 0 )
		{
			oss << "final" << separator;
		}
		if( (stateMoc & STATE_SYNC_MOC) != 0 )
		{
			oss << "sync" << separator;
		}

		return( oss.str() );
	}

	return "<state:undef>";
}


/**
 * PSEUDOSTATE MOC to STRING
 */
std::string Specifier::strPseudostateMoc(
		bit_field_t pseudostateMoc, const std::string & separator)
{
	switch( pseudostateMoc )
	{
		case PSEUDOSTATE_UNDEFINED_MOC:
			return( "" );
//			return( "<pseudostate:undef>" + separator );

		case PSEUDOSTATE_INITIAL_MOC:
			return( "initial" + separator );
		case PSEUDOSTATE_TERMINAL_MOC:
			return( "terminal" + separator );

		case PSEUDOSTATE_RETURN_MOC:
			return( "return" + separator );

		case PSEUDOSTATE_JUNCTION_MOC:
			return( "junction" + separator );
		case PSEUDOSTATE_CHOICE_MOC:
			return( "choice" + separator );

		case PSEUDOSTATE_ENTRY_POINT_MOC:
			return( "entryPoint" + separator );
		case PSEUDOSTATE_EXIT_POINT_MOC:
			return( "exitPoint" + separator );

		case PSEUDOSTATE_FORK_MOC:
			return( "fork" + separator );
		case PSEUDOSTATE_JOIN_MOC:
			return( "join" + separator );

		case PSEUDOSTATE_DEEP_HISTORY_MOC:
			return( "dhistory" + separator );
		case PSEUDOSTATE_SHALLOW_HISTORY_MOC:
			return( "shistory" + separator );

		default:
			return( xstrPseudostateMoc(pseudostateMoc, separator) );
	}
}


std::string Specifier::xstrPseudostateMoc(
		bit_field_t pseudostateMoc, const std::string & separator)
{
	if( pseudostateMoc != PSEUDOSTATE_UNDEFINED_MOC)
	{
		std::ostringstream oss;

		if( (pseudostateMoc & PSEUDOSTATE_INITIAL_MOC) != 0 )
		{
			oss << "initial" << separator;
		}
		if( (pseudostateMoc & PSEUDOSTATE_TERMINAL_MOC) != 0 )
		{
			oss << "terminal" << separator;
		}

		if( (pseudostateMoc & PSEUDOSTATE_RETURN_MOC) != 0 )
		{
			oss << "return" << separator;
		}

		if( (pseudostateMoc & PSEUDOSTATE_JUNCTION_MOC) != 0 )
		{
			oss << "junction" << separator;
		}
		if( (pseudostateMoc & PSEUDOSTATE_CHOICE_MOC) != 0 )
		{
			oss << "choice" << separator;
		}

		if( (pseudostateMoc & PSEUDOSTATE_ENTRY_POINT_MOC) != 0 )
		{
			oss << "entryPoint" << separator;
		}
		if( (pseudostateMoc & PSEUDOSTATE_EXIT_POINT_MOC) != 0 )
		{
			oss << "exitPoint" << separator;
		}

		if( (pseudostateMoc & PSEUDOSTATE_FORK_MOC) != 0 )
		{
			oss << "fork" << separator;
		}
		if( (pseudostateMoc & PSEUDOSTATE_JOIN_MOC) != 0 )
		{
			oss << "join" << separator;
		}

		if( (pseudostateMoc & PSEUDOSTATE_DEEP_HISTORY_MOC) != 0 )
		{
			oss << "dhistory" << separator;
		}
		if( (pseudostateMoc & PSEUDOSTATE_SHALLOW_HISTORY_MOC) != 0 )
		{
			oss << "shistory" << separator;
		}

			return( oss.str() );
	}

	return "<pseudostate:undef>";
}


/**
 * DESIGN KIND to STRING
 */
std::string Specifier::strFeature(
		bit_field_t featureKind, const std::string & separator)
{
	if( (featureKind != FEATURE_UNDEFINED_KIND) )
	{
		std::ostringstream oss;

		if( (featureKind & FEATURE_TIMED_KIND) == FEATURE_TIMED_KIND )
		{
			oss << "timed" << separator;
		}
		else if( (featureKind & FEATURE_TIMED_KIND) == FEATURE_DISCRETE_TIMED_KIND )
		{
			oss << "timed#discrete" << separator;
		}
		else if( (featureKind & FEATURE_TIMED_KIND) == FEATURE_DENSE_TIMED_KIND )
		{
			oss << "timed#dense" << separator;
		}
		else if( (featureKind & FEATURE_TIMED_KIND) == FEATURE_CONTINUOUS_TIMED_KIND )
		{
			oss << "timed#continuous" << separator;
		}

		if( (featureKind & FEATURE_INPUT_ENABLED_KIND) != 0 )
		{
			oss << "input_enabled" << separator;
		}

		if( (featureKind & FEATURE_LIFELINE_KIND) != 0 )
		{
			oss << "lifeline" << separator;
		}

		if( (featureKind & FEATURE_USER_DEFINED_SCHEDULE_KIND) != 0 )
		{
			oss << "#user#schedule" << separator;
		}

		return( oss.str() );
	}

	return( "" /*"<feature:undef>"*/ );
}


/**
 * DESIGN KIND to STRING
 */
std::string Specifier::strDesign_not(
		DESIGN_KIND designKind, const std::string & separator) const
{
	if( isDesignKind(designKind) )
	{
		return( "" );
	}
	else if( isDesignPrototypeStatic() )
	{
		return( strDesign(this->design, separator) );
	}
	else
	{
		switch( designKind )
		{
			case DESIGN_MODEL_KIND:
			case DESIGN_INSTANCE_KIND:
			case DESIGN_DYNAMIC_KIND:
			case DESIGN_STATIC_KIND:
			case DESIGN_RUNTIME_KIND:
			{
				return( strDesign(this->design & (~ designKind), separator) );
			}
			default:
			{
				return( strDesign(this->design, separator) );
			}
		}
	}
}


std::string Specifier::strDesign(
		bit_field_t designKind, const std::string & separator)
{
	switch( designKind )
	{
		case DESIGN_UNDEFINED_KIND:
			return( "" );
//			return( "<design:undef>" + separator );
//			case DESIGN_META_KIND:
//				return( "#meta" + separator );

		case DESIGN_MODEL_KIND:
			return( "#model" + separator );
		case DESIGN_INSTANCE_KIND:
			return( "#instance" + separator );
		case DESIGN_STATIC_KIND:
			return( "#static" + separator );
		case DESIGN_DYNAMIC_KIND:
			return( "#dynamic" + separator );
		case DESIGN_RUNTIME_KIND:
			return( "#runtime" + separator );

		case DESIGN_INSTANCE_STATIC_KIND:
			return( "#static#instance" + separator );
		case DESIGN_INSTANCE_DYNAMIC_KIND:
			return( "#dynamic#instance" + separator );

		case DESIGN_PROTOTYPE_STATIC_KIND:
//			return( "#static #prototype" + separator );
			return( "#prototype" + separator );
		case DESIGN_PROTOTYPE_DYNAMIC_KIND:
			return( "#dynamic#prototype" + separator );

		default:
			return( xstrDesign(designKind, separator) );
	}
}


std::string Specifier::xstrDesign(
		bit_field_t designKind, const std::string & separator)
{
	if( (designKind != DESIGN_UNDEFINED_KIND) )
//		&& (designKind != DESIGN_META_KIND) )
	{
		std::ostringstream oss;

		if( (designKind & DESIGN_MODEL_KIND) != 0 )
		{
			oss << "#model" << separator;
		}
		else if( (designKind & DESIGN_INSTANCE_KIND) != 0 )
		{
			oss << "#instance" << separator;
		}
		else if( (designKind & DESIGN_STATIC_KIND) != 0 )
		{
			oss << "#static" << separator;
		}
		else if( (designKind & DESIGN_DYNAMIC_KIND) != 0 )
		{
			oss << "#dynamic" << separator;
		}

		if( (designKind & DESIGN_RUNTIME_KIND) != 0 )
		{
			oss << "#runtime" << separator;
		}

		return( oss.str() );
	}

	return( "<design:undef>" );
}


/**
 * Serialization
 */
std::string Specifier::SEPARATOR = " % ";


std::string Specifier::toString(bit_field_t enabledFields,
		const std::string & separator) const
{
	std::ostringstream oss;

	if( isNullref() )
	{
		oss << "#null<Specifier>" << separator;
	}

	if( (enabledFields & FIELD_FEATURE_POSITION) != 0 )
	{
		oss << Specifier::strFeature( feature , separator );
	}

	if( (enabledFields & FIELD_PSEUDOSTATE_POSITION) != 0 )
	{
		oss << Specifier::strPseudostateMoc( pseudostate , separator );
	}
	if( (enabledFields & FIELD_STATE_POSITION) != 0 )
	{
		oss << Specifier::strStateMoc( state , separator );
	}

	if( (enabledFields & FIELD_COMPUTATION_POSITION) != 0 )
	{
		oss << Specifier::strModelOfComputation( computation , separator );
	}

	if( (enabledFields & FIELD_DESIGN_POSITION) != 0 )
	{
		oss << Specifier::strDesign( design , separator);
	}

	if( (enabledFields & FIELD_GROUP_POSITION) != 0 )
	{
		oss << Specifier::strGroup   ( group , separator );
	}

	if( (enabledFields & FIELD_COMPONENT_POSITION) != 0 )
	{
		oss << Specifier::strComponent( component , separator );
	}

	return( oss.str() );
}


} /* namespace sep */
