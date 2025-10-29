/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mai 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "FamCoreExposer.h"

#include  <famcore/api/ExtenderProcessorUnit.h>
#include  <famcore/api/MainProcessorUnit.h>

#include  <famcore/FormulaCoverageFilter.h>

#include  <famcore/debug/AvmDebugProcessor.h>

#include  <famcore/hitorjump/AvmHitOrJumpProcessor.h>

#include  <famcore/queue/ExecutionQueue.h>

#include  <famcore/redundancy/RedundancyFilter.h>

#include  <famcore/serializer/GraphicExecutionGraphSerializer.h>
#include  <famcore/serializer/GraphicStatemachineSerializer.h>
#include  <famcore/serializer/GraphVizExecutionGraphSerializer.h>
#include  <famcore/serializer/GraphVizStatemachineSerializer.h>

#include  <famcore/trace/AvmTraceGenerator.h>




namespace sep
{


////////////////////////////////////////////////////////////////////////////
// EXPORTED FAM LIST
////////////////////////////////////////////////////////////////////////////

void FamCoreExposer::toStreamExported(OutStream & out, const std::string & header)
{
#define PROCESSOR_FACTORY_SHOW_TYPE_ID( Processor )  \
	out << TAB2 << Processor::AUTO_REGISTER_TOOL.getTypeID() << EOL;

	out << TAB1 << header << "< exported > {" << EOL;

	PROCESSOR_FACTORY_SHOW_TYPE_ID( MainProcessorUnit        )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( ExecutionQueue           )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( RedundancyFilter         )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmTraceGenerator        )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmDebugProcessor        )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( FormulaCoverageFilter    )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( AvmHitOrJumpProcessor    )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( ExtenderProcessorUnit    )

	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphicExecutionGraphSerializer )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphicStatemachineSerializer   )


	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphVizExecutionGraphSerializer )
	PROCESSOR_FACTORY_SHOW_TYPE_ID( GraphVizStatemachineSerializer   )

	out << TAB1 << "}" << EOL_FLUSH;
}


} /* namespace sep */
