/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutableSystem.h"

#include <fml/common/ModifierElement.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * SETTER
 * updateFullyQualifiedNameID()
 */
void ExecutableSystem::updateFullyQualifiedNameID()
{
	if( hasAstElement() )
	{
		std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();

		setAllNameID("sys" + aFullyQualifiedNameID.substr(
					aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR) ) ,
				NamedElement::extractNameID( aFullyQualifiedNameID ));
	}
	else
	{
		setAllNameID( "sys#anonym" , "sys#anonym" );
	}
}


/**
 * Serialization
 */
void ExecutableSystem::strHeader(OutStream & os) const
{
	os << getModifier().toString() << "system";
	if( hasSystemInstance() )
	{
		os << TAB << "< moc: " << getSpecifier().str() << " >";
	}
	os << " " << getNameID();
}


void ExecutableSystem::toStream(OutStream & os) const
{
	os << TAB << "xfsp< executable , 1.0 >:" << EOL2;


	os << TAB << "// " << getModifier().toString()
			<< getSpecifier().toString( Specifier::ENABLE_FEATURE_DESIGN_FIELD )
			<< "system< moc: "
			<< getSpecifier().str( Specifier::DISABLE_FEATURE_DESIGN_FIELD )
			<< " > " << getNameID() << " {" << EOL;

	os << TAB << "header:" << EOL<< TAB2
			<< "fqn_id = " << getFullyQualifiedNameID()
			<< EOL_TAB2
			<< "description = \"the result of the system compilation\""
			<< EOL_TAB2
			<< "count = " << getMachineCount() << EOL;

	if( hasSystemInstance() )
	{
		os << EOL_TAB << "instance:"
				<< EOL_INCR_INDENT << TAB
				<< "// The Parameters Machine Instance" << EOL;
		mParametersInstance.toStream(os);

		os << EOL_TAB << "// The System Machine Instance" << EOL;
		rawSystemInstance()->toStream(os);
		os << DECR_INDENT;
	}

	os << EOL_TAB << "executable:" << EOL_INCR_INDENT;

	mParametersExecutable.toStream(os);

	TableOfExecutableForm::const_raw_iterator itExec = mExecutables.begin();
	for( ; itExec != mExecutables.end() ; ++itExec )
	{
		os << EOL;
		(itExec)->toStream(os);
	}

	os << EOL_DECR_INDENT << "// " << TAB << "}" << EOL_FLUSH;
}


}
