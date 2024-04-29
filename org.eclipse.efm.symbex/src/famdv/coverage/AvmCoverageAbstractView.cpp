/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCoverageAbstractView.h"

#include "AvmCoverageProcessor.h"


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmCoverageAbstractView::AvmCoverageAbstractView(
		AvmCoverageProcessor & aCoverageProcessor,
		const WObject * wfParameterObject)
: RunnableElement( CLASS_KIND_T( AvmCoverageAbstractView ), wfParameterObject ),
IHeuristicContextWeight( ),

mCoverageProcessor( aCoverageProcessor ),
mCoverageStatistics( aCoverageProcessor.getCoverageStatistics() ),
mHeuristicProperty( aCoverageProcessor.mHeuristicProperty ),

// Computing drive variable
itQueue( ),
endQueue( ),

itEC( ),
endEC( )
{
	//!! NOTHING
}


} /* namespace sep */
