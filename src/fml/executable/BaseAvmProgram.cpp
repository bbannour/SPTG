/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 oct. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BaseAvmProgram.h"

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>

#include <fml/type/BaseSymbolTypeSpecifier.h>


namespace sep
{


/**
 * GETTER
 * any SYMBOL filtering by an optional type specifier family
 */
const BF & BaseAvmProgram::getSymbol(
		const std::string & aFullyQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol =
			getAllVariables().getByFQNameID( aFullyQualifiedNameID );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getVariableAlias().getByFQNameID( aFullyQualifiedNameID ) );
}


const BF & BaseAvmProgram::getSymbolByQualifiedNameID(
		const std::string & aQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol =
			getAllVariables().getByQualifiedNameID( aQualifiedNameID );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getVariableAlias().getByQualifiedNameID( aQualifiedNameID ) );
}


const BF & BaseAvmProgram::getSymbolByNameID(
		const std::string & aNameID, avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol = getAllVariables().getByNameID( aNameID );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getVariableAlias().getByNameID(aNameID) );
}


const BF & BaseAvmProgram::getSymbolByAstElement(
		const ObjectElement & astElement,
		avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol = getAllVariables().getByAstElement( astElement );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getVariableAlias().getByAstElement( astElement ) );
}


/**
 * GETTER
 * For AvmProgram - ExecutableForm Container
 */
const AvmProgram * BaseAvmProgram::getAvmProgramContainer() const
{
	BaseAvmProgram * aContainer = getContainer();

	while( (aContainer != nullptr) && (not aContainer->is< AvmProgram >()) )
	{
		aContainer = aContainer->getContainer();
	}

	return( static_cast< const AvmProgram * >( aContainer ) );
}

const AvmProgram * BaseAvmProgram::getAvmProgram() const
{
	if( this->is< AvmProgram >() )
	{
		return( static_cast< const AvmProgram * >( this ) );
	}

	return( getAvmProgramContainer() );
}



ExecutableForm * BaseAvmProgram::getExecutableContainer() const
{
	BaseAvmProgram * aContainer = getContainer();

	while( (aContainer != nullptr) && aContainer->isnot< ExecutableForm >() )
	{
		aContainer = aContainer->getContainer();
	}

	return( static_cast< ExecutableForm * >( aContainer ) );
}

ExecutableForm * BaseAvmProgram::getExecutable() const
{
	if( this->is< ExecutableForm >() )
	{
		return( static_cast< ExecutableForm * >(
				const_cast< BaseAvmProgram * >(this) ) );
	}

	return( getExecutableContainer() );
}


ExecutableForm & BaseAvmProgram::refExecutable() const
{
	ExecutableForm * anExecutable = getExecutable();

	return( (anExecutable != nullptr)
			? (*anExecutable) :ExecutableForm::nullref());
}


/**
 * UPDATE DATA TABLE
 * mBasicVariables
 * mallVariables
 */

void BaseAvmProgram::updateVariableTable()
{
	if( getVariables().empty() )
	{
		return;
	}

	TableOfInstanceOfData::raw_iterator itVariable = mVariables.begin();
	TableOfInstanceOfData::raw_iterator endVariable = mVariables.end();
	for( ; itVariable != endVariable ; ++itVariable )
	{
		if( (itVariable)->getTypeSpecifier().hasTypeArrayOrStructure()
			&& (not (itVariable)->getModifier().hasNatureReference()) )
		{
			break;
		}
	}

	if( itVariable == endVariable )
	{
		mBasicVariables = &mVariables;
		mAllVariables = &mVariables;

		return;
	}


	if( mBasicVariables != (& mVariables) )
	{
		sep::destroy( mBasicVariables );
	}
	if( mAllVariables != (& mVariables) )
	{
		sep::destroy( mAllVariables );
	}

//	InstanceOfData * aVariable = getVariables().last();

	TableOfInstanceOfData tableofAllVariables;
	TableOfInstanceOfData tableofBasicVariables;
	TableOfSymbol relativeVariablePath;

	// begin() --> it  is typed simple
	TableOfInstanceOfData::const_iterator it2 = mVariables.begin();
	for( ; it2 != itVariable ; ++it2 )
	{
		tableofAllVariables.append( (*it2) );
		tableofBasicVariables.append( (*it2) );
	}

	// Analyse for it --> end()
	for( ; itVariable != endVariable ; ++itVariable )
	{
		tableofAllVariables.append( (*itVariable) );

		const BaseTypeSpecifier & aTypeSpecifier =
				itVariable->referedTypeSpecifier();

		if( (itVariable)->getModifier().hasNatureReference() )
		{
			tableofBasicVariables.append( (*itVariable) );
		}
		else if( aTypeSpecifier.hasTypeArrayOrStructure() )
		{
			collectAllVariables(tableofAllVariables, tableofBasicVariables,
					(itVariable), relativeVariablePath, (itVariable) );
		}
		else
		{
			tableofBasicVariables.append( (*itVariable) );
		}
	}

	mAllVariables   = new TableOfInstanceOfData(tableofAllVariables);
	mBasicVariables = new TableOfInstanceOfData(tableofBasicVariables);
}


void BaseAvmProgram::collectAllVariables(
		TableOfInstanceOfData & tableofAllVariables,
		TableOfInstanceOfData & tableofBasicVariables,
		InstanceOfData * mainVariableInstance,
		TableOfSymbol & relativeDataPath, InstanceOfData * aVariable)
{
	std::string pefixID = aVariable->getNameID();
	std::ostringstream ossID;

	if( aVariable->getTypeSpecifier().hasTypeStructureOrChoiceOrUnion() )
	{
		TableOfSymbol::const_iterator itField = aVariable->getTypeSpecifier().
				to< BaseSymbolTypeSpecifier >().getSymbolData().begin();

		TableOfSymbol::iterator it = aVariable->getAttribute()->begin();
		TableOfSymbol::iterator itEnd = aVariable->getAttribute()->end();
		for( ; it != itEnd ; ++it , ++itField )
		{
			ossID.str( "" );
			ossID << pefixID << "."
					<< NamedElement::extractNameID(
							(*it).getFullyQualifiedNameID() );

			InstanceOfData * newInstance = new InstanceOfData(
					IPointerVariableNature::POINTER_UFI_OFFSET_NATURE,
					mainVariableInstance->getContainer(), (*it).variable());
			newInstance->setSharedVariable( mainVariableInstance );
			newInstance->setNameID( ossID.str() );
			relativeDataPath.append( *itField );
			newInstance->setDataPath( relativeDataPath );

			newInstance->setAliasTarget( (*it).variable() );
			(*it).setAliasTarget( * newInstance );

			const BF & saveInstance = tableofAllVariables.save( newInstance );
			if( newInstance->getTypeSpecifier().hasTypeSimpleOrCollection() )
			{
				tableofBasicVariables.append( saveInstance );
			}

			collectAllVariables(tableofAllVariables,
					tableofBasicVariables , mainVariableInstance,
					relativeDataPath, (*it).rawVariable());

			relativeDataPath.pop_last();
		}
	}

	else if( aVariable->getTypeSpecifier().isTypedArray() )
	{
		TableOfSymbol::iterator it = aVariable->getAttribute()->begin();
		TableOfSymbol::iterator itEnd = aVariable->getAttribute()->end();
		for( ; it != itEnd ; ++it )
		{
			ossID.str( "" );
			ossID << pefixID << "[" << (*it).getOffset() << "]";

			InstanceOfData * newInstance = new InstanceOfData(
					IPointerVariableNature::POINTER_UFI_OFFSET_NATURE,
					mainVariableInstance->getContainer(), (*it).variable());
			newInstance->setSharedVariable( mainVariableInstance );
			newInstance->setNameID( ossID.str() );
			relativeDataPath.append( *it );
			newInstance->setDataPath( relativeDataPath );

			(*it).setAliasTarget( * newInstance );

			const BF & saveInstance = tableofAllVariables.save( newInstance );
			if( newInstance->getTypeSpecifier().hasTypeSimpleOrCollection() )
			{
				tableofBasicVariables.append( saveInstance );
			}

			collectAllVariables(tableofAllVariables, tableofBasicVariables ,
					mainVariableInstance, relativeDataPath, (*it).rawVariable());

			relativeDataPath.pop_last();
		}
	}
}


/**
 * Serialization
 */
void BaseAvmProgram::toStream(OutStream & os) const
{
	os << TAB << getModifier().toString()
			<< "avmprogram " << getFullyQualifiedNameID();
	AVM_DEBUG_REF_COUNTER(os);
	os << " {" << EOL;

	if( hasVariableAlias() )
	{
		os << EOL << TAB << "alias:" << EOL_INCR_INDENT;

		getVariableAlias().toStream(os);

		os << DECR_INDENT;
	}

	if( hasVariable() )
	{
		os << EOL << TAB << "variable:" << EOL_INCR_INDENT;

		getVariables().toStream(os);

		os << DECR_INDENT;

AVM_IF_DEBUG_FLAG( DATA )
		if( mAllVariables != (& mVariables) )
		{
			os << EOL;
			os << TAB << "variable#all:" << EOL_INCR_INDENT;

			getAllVariables().toStream(os);

			os << DECR_INDENT;
		}
		if( mBasicVariables != (& mVariables) )
		{
			os << EOL;
			os << TAB << "variable#basic:" << EOL;

			TableOfInstanceOfData::const_raw_iterator itVariable =
					getBasicVariables().begin();
			TableOfInstanceOfData::const_raw_iterator endVariable =
					getBasicVariables().end();
			for( ; itVariable != endVariable ; ++itVariable )
			{
				os << TAB2 << str_header( *itVariable ) << ";" << EOL;
			}
		}
AVM_ENDIF_DEBUG_FLAG( DATA )
	}

	os << TAB << "}" << EOL << std::flush;
}


}
