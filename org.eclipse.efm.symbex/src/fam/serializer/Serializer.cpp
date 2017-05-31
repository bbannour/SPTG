/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Serializer.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <boost/format.hpp>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

/**
prototype processor::serializer#graph "serialize graph" as avm::processor.SERIALIZER is
section PROPERTY
	@info#selection = 'ALL';    // ALL | MODIFIED
	@data#selection = 'ALL';	// ALL | MODIFIED
endsection PROPERTY

section FORMAT
	@line#wrap#width = 42;
	@line#wrap#separator = "\\l";
endsection FORMAT

endprototype
*/

bool Serializer::configureImpl()
{
	WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));
	if( thePROPERTY != WObject::_NULL_ )
	{
		mInfoAllFlags = (Query::getRegexWPropertyString(
				thePROPERTY, CONS_WID2("info", "selection"), "ALL") == "ALL");

		mDataSelectionModifiedFlags = (Query::getRegexWPropertyString(
			thePROPERTY, CONS_WID2("data", "selection"), "MODIFIED") == "MODIFIED");
	}

	WObject * theFORMAT = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("format", "FORMAT"), thePROPERTY);
	if( theFORMAT != WObject::_NULL_ )
	{
		mWrapData.LINE_WIDTH = Query::getRegexWPropertyPosSizeT(theFORMAT,
			CONS_WID3("line", "wrap", "width"), mDefaultLineWrapWidth);

		mWrapData.SEPARATOR = Query::getRegexWPropertyString(theFORMAT,
			CONS_WID3("line", "wrap", "separator"), mWrapData.SEPARATOR);
		StringTools::replaceAll(mWrapData.SEPARATOR, "\\t" , "\t");
		StringTools::replaceAll(mWrapData.SEPARATOR, "\\n" , "\n");

		mMultiValueArrayCSS.BEGIN = Query::getRegexWPropertyString(
				theFORMAT, CONS_WID3("value", "array", "begin"), "[ ");
		mMultiValueArrayCSS.SEPARATOR = Query::getRegexWPropertyString(
			theFORMAT, CONS_WID3("value", "array", "separator"), " , ");
		mMultiValueArrayCSS.END = Query::getRegexWPropertyString(
				theFORMAT, CONS_WID3("value", "array", "end"), " ]");

		mMultiValueParamsCSS.BEGIN = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("value", "param(eter)?s?", "begin"), "( ");
		mMultiValueParamsCSS.SEPARATOR = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("value", "param(eter)?s?", "separator"), " , ");
		mMultiValueParamsCSS.END = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("value", "param(eter)?s?", "end"), " )");

		mMultiValueStructCSS.BEGIN = Query::getRegexWPropertyString(
			theFORMAT, CONS_WID3("value", "struct", "begin"), "{ ");
		mMultiValueStructCSS.SEPARATOR = Query::getRegexWPropertyString(
			theFORMAT, CONS_WID3("value", "struct", "separator"), " , ");
		mMultiValueStructCSS.END = Query::getRegexWPropertyString(
				theFORMAT, CONS_WID3("value", "struct", "end"), " }");
	}

	return( true );
}


} /* namespace sep */
