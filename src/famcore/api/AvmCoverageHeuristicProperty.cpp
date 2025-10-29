/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include <famcore/api/AvmCoverageHeuristicProperty.h>
#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

namespace sep
{


/**
 *
 * strHeuristicWeight
 */
std::string IHeuristicContextWeight::strHeuristicWeight(std::uint8_t aWeight)
{
	switch( aWeight )
	{
		case WEIGHT_SELECTED_ACHIEVABLE  : return( "SELECTED_ACHIEVABLE"  );

		case WEIGHT_CERTAINLY_ACHIEVABLE : return( "CERTAINLY_ACHIEVABLE" );
		case WEIGHT_STRONGLY_ACHIEVABLE  : return( "STRONGLY_ACHIEVABLE"  );
		case WEIGHT_WEAKLY_ACHIEVABLE    : return( "WEAKLY_ACHIEVABLE"    );

		case WEIGHT_NON_PRIORITY         : return( "NON_PRIORITY"         );
		case WEIGHT_UNKNOWN_ACHIEVABLE   : return( "UNKNOWN_ACHIEVABLE"   );

		case WEIGHT_NON_ACHIEVABLE       : return( "UNACHIEVABLE"         );

		default: return( to_string( static_cast< int >(aWeight) ) );
	}
}


/**
 * SETTER
 * mHeuristicClass
 */
IHeuristicClass::ENUM_HEURISTIC_CLASS
IHeuristicClass::incrHeuristicClass(ENUM_HEURISTIC_CLASS anHeuristicClass)
{
	switch( anHeuristicClass )
	{
		case HEURISTIC_BASIC_CLASS:
		{
			return( HEURISTIC_NAIVE_CLASS );
		}

		case HEURISTIC_NAIVE_CLASS:
		{
			return( HEURISTIC_SMART_CLASS );
		}

		case HEURISTIC_SMART_CLASS:
		{
			return( HEURISTIC_AGRESSIVE_CLASS );
		}

		case HEURISTIC_AGRESSIVE_CLASS:
		{
			return( HEURISTIC_NOTHING_ELSE_CLASS );
		}

		case HEURISTIC_NOTHING_ELSE_CLASS:
		default:
		{
			return( HEURISTIC_NOTHING_ELSE_CLASS );
		}
	}
}


std::string IHeuristicClass::strHeuristicClass(
		ENUM_HEURISTIC_CLASS anHeuristicClass)
{
	switch( anHeuristicClass )
	{
		case HEURISTIC_BASIC_CLASS:
		{
			return( "HEURISTIC_BASIC_CLASS" );
		}

		case HEURISTIC_NAIVE_CLASS:
		{
			return( "HEURISTIC_NAIVE_CLASS" );
		}

		case HEURISTIC_SMART_CLASS:
		{
			return( "HEURISTIC_SMART_CLASS" );
		}

		case HEURISTIC_AGRESSIVE_CLASS:
		{
			return( "HEURISTIC_AGRESSIVE_CLASS" );
		}

		case HEURISTIC_NOTHING_ELSE_CLASS:
		{
			return( "HEURISTIC_NOTHING_ELSE_CLASS" );
		}

		default:
		{
			return( "UNKNOWN< HEURISTIC_CLASS >" );
		}
	}
}


IHeuristicClass::ENUM_HEURISTIC_CLASS
IHeuristicClass::toHeuristicClass(const std::string & strHeuristicClass)
{
	std::string aHeuristicClass = strHeuristicClass;
	StringTools::tolower(aHeuristicClass);

	if( aHeuristicClass == "basic" )
	{
		return( HEURISTIC_BASIC_CLASS );
	}
	else if( aHeuristicClass == "naive" )
	{
		return( HEURISTIC_NAIVE_CLASS );
	}
	else if( aHeuristicClass == "smart" )
	{
		return( HEURISTIC_SMART_CLASS );

	}
	else if( aHeuristicClass == "agressive" )
	{
		return( HEURISTIC_AGRESSIVE_CLASS );
	}

	return( HEURISTIC_BASIC_CLASS );
}

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

/*******************************************************************************
prototype process::processID as &avm::processor.PROCESSOR_TYPE_ID is
	section HEURISTIC
		// Active l'utilisation d'heuristique
		@heuristic = true;

		// choix de l'heuristique de départ
		// basic | naive | smart | agressive
		@heuristic#start = 'basic';

		// Nombre d'essais d'heuristiques
		@heuristic#trials = 7;

		// Critère de satisfaction du succès des heuristiques
		// taux de couverte / nombre d'élément restant...
		@objective#rate = 95;
		@objective#rest = 5;

		// Limitation de la taille des chemins/traces couvrants recherchés
		@directive#trace#heuristic = 'smart';
		@directive#trace#count#limit = 8;
		@directive#trace#size#limit  = 8;

		// Choix des contextes avec des transitions
		// [ fortement | faiblement | autre ] tirables

		// Limitations temporaire de la profondeur d'exploration
		@coverage#height = 7;

		// nombre de fois que la limite doit être atteint avant de l'augmenter
		@coverage#height#reached#limit = 42;

		@hit#strongly#random = false;
		@hit#strongly#count = 1;

		@hit#weakly#random = false;
		@hit#weakly#count = 1;

		@hit#other#random = false;
		@hit#other#count = 1;

		@scope = 'DETAILS'; 	// 'INSTANCE' | 'FORM' | 'DETAILS'
	endsection HEURISTIC
endprototype

*******************************************************************************/

bool AvmCoverageHeuristicProperty::configure(const WObject * wfParameterObject)
{
	long intAttribute = 0;

	const WObject * thePROPERTY  = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));
	if( thePROPERTY != WObject::_NULL_ )
	{
		mScope = Specifier::toDesignKind(
				Query::getWPropertyString(thePROPERTY, "scope", "MODEL") );

		mHeuristicEnabled = Query::getWPropertyBoolean(
				thePROPERTY, "heuristic", true);
	}


	const WObject * theHEURISTIC = Query::getRegexWSequence(wfParameterObject,
			OR_WID2("heuristic", "HEURISTIC"), thePROPERTY);
	if( theHEURISTIC != WObject::_NULL_ )
	{
		Specifier::DESIGN_KIND aScope = Specifier::toDesignKind(
				Query::getWPropertyString(theHEURISTIC, "scope", "UNDEFINED") );
		if( aScope != Specifier::DESIGN_UNDEFINED_KIND )
		{
			mScope = aScope;
		}

		// Heuristic enabling
		mHeuristicEnabled = Query::getWPropertyBoolean(
				theHEURISTIC, "heuristic", mHeuristicEnabled);

		// Heuristic start class : basic | naive | smart | agressive
		std::string strHeuristic = Query::getRegexWPropertyString(
				theHEURISTIC, CONS_WID2("heuristic", "start"), "basic");
		mHeuristicClass = toHeuristicClass(strHeuristic);

		// Trials limit
		mHeuristicTrialsLimit = Query::getRegexWPropertySizeT(
				theHEURISTIC, CONS_WID2("heuristic", "trials"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);
		mHeuristicTrialsCount = 0;

		// Objective & Goal
		intAttribute = Query::getRegexWPropertyInt(
				theHEURISTIC, CONS_WID2("objective", "rate"), 100);
		mCoverageRateGoal = ( (intAttribute > 0) &&
				(intAttribute <= 100) ) ?  intAttribute : 100;

		mCoverageRestGoal = Query::getRegexWPropertySizeT(
				theHEURISTIC, CONS_WID2("objective", "rest"), 0, 0);

		// Directive Heuristic
		strHeuristic = Query::getRegexWPropertyString(theHEURISTIC,
				CONS_WID3("directive", "trace", "heuristic"), "smart");
		mDirectiveTraceHeuristicClass = toHeuristicClass(strHeuristic);

		mDirectiveTraceCountLimit = Query::getRegexWPropertyPosSizeT(
				theHEURISTIC,
				CONS_WID4("directive", "trace", "count", "limit"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mDirectiveTraceSizeLimit = Query::getRegexWPropertyPosSizeT(
				theHEURISTIC,
				CONS_WID4("directive", "trace", "size", "limit"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);


		mCoverageHeight = mCoverageHeightPeriod =
				Query::getRegexWPropertySizeT(theHEURISTIC,
						CONS_WID2("lookahead", "depth") "|"
						CONS_WID2("coverage", "height"), 0);

		mCoverageHeightReachedLimit = Query::getRegexWPropertySizeT(
				theHEURISTIC, CONS_WID2("lookahead", "width") "|"
				CONS_WID4("coverage", "height", "reached", "limit"), 0);

		// Options pour les transitions fortement tirables
		mHitStronglyRandomFlag = Query::getRegexWPropertyBoolean(
			theHEURISTIC, CONS_WID3("hit", "strongly", "random"), false);

		mHitStronglyCount = Query::getRegexWPropertyPosSizeT(
				theHEURISTIC, CONS_WID3("hit", "strongly", "count"), 1);

		// Options pour les transitions faiblement tirables
		mHitWeaklyRandomFlag = Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID3("hit", "weakly", "random"), false);

		mHitWeaklyCount = Query::getRegexWPropertyPosSizeT(
				theHEURISTIC, CONS_WID3("hit", "weakly", "count"), 1);

		// Options pour les autres transitions tirables ?
		mHitOtherRandomFlag = Query::getRegexWPropertyBoolean(
				theHEURISTIC, CONS_WID3("hit", "other", "random"), false);

		mHitOtherCount = Query::getRegexWPropertyPosSizeT(
				theHEURISTIC, CONS_WID3("hit", "other", "count"), 1);
	}

	return( true );
}


} /* namespace sep */
