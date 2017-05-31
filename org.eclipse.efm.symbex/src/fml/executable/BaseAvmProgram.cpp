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
			getAllData().getByFQNameID( aFullyQualifiedNameID );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getDataAlias().getByFQNameID( aFullyQualifiedNameID ) );
}


const BF & BaseAvmProgram::getSymbolByQualifiedNameID(
		const std::string & aQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol =
			getAllData().getByQualifiedNameID( aQualifiedNameID );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getDataAlias().getByQualifiedNameID( aQualifiedNameID ) );
}


const BF & BaseAvmProgram::getSymbolByNameID(
		const std::string & aNameID, avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol = getAllData().getByNameID( aNameID );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getDataAlias().getByNameID(aNameID) );
}


const BF & BaseAvmProgram::getSymbolByAstElement(
		const ObjectElement * astElement,
		avm_type_specifier_kind_t typeFamily) const
{
	const BF & foundSymbol = getAllData().getByAstElement( astElement );

	if( foundSymbol.valid() )
	{
		return( foundSymbol );
	}

	return( getDataAlias().getByAstElement( astElement ) );
}


/**
 * GETTER
 * For AvmProgram - ExecutableForm Container
 */
const AvmProgram * BaseAvmProgram::getAvmProgramContainer() const
{
	BaseAvmProgram * aContainer = getContainer();

	while( (aContainer != NULL) && (not aContainer->is< AvmProgram >()) )
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

	while( (aContainer != NULL) && aContainer->isnot< ExecutableForm >() )
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


/**
 * UPDATE DATA TABLE
 * mBasicData
 * mallData
 */

void BaseAvmProgram::updateDataTable()
{
	if( getData().empty() )
	{
		return;
	}

	TableOfInstanceOfData::raw_iterator itData = mData.begin();
	TableOfInstanceOfData::raw_iterator endData = mData.end();
	for( ; itData != endData ; ++itData )
	{
		if( (itData)->getTypeSpecifier()->hasTypeArrayOrStructure() &&
			(not (itData)->getModifier().hasNatureReference()) )
		{
			break;
		}
	}

	if( itData == endData )
	{
		mBasicData = &mData;
		mAllData = &mData;

		return;
	}


	if( mBasicData != &mData )
	{
		sep::destroy( mBasicData );
	}
	if( mAllData != &mData )
	{
		sep::destroy( mAllData );
	}

//	InstanceOfData * anInstance = getData().last();

	TableOfInstanceOfData tableofAllData;
	TableOfInstanceOfData tableofBasicData;
	TableOfSymbol relativeDataPath;

	// begin() --> it  is typed simple
	TableOfInstanceOfData::const_iterator it2 = mData.begin();
	for( ; it2 != itData ; ++it2 )
	{
		tableofAllData.append( (*it2) );
		tableofBasicData.append( (*it2) );
	}

	BaseTypeSpecifier * aTypeSpecifier = NULL;

	// Analyse for it --> end()
	for( ; itData != endData ; ++itData )
	{
		tableofAllData.append( (*itData) );

		aTypeSpecifier = (itData)->referedTypeSpecifier();

		if( (itData)->getModifier().hasNatureReference() )
		{
			tableofBasicData.append( (*itData) );
		}
		else if( aTypeSpecifier->hasTypeArrayOrStructure() )
		{
			collectAllData(tableofAllData, tableofBasicData,
					(itData), relativeDataPath, (itData) );
		}
		else
		{
			tableofBasicData.append( (*itData) );
		}
	}

	mAllData   = new TableOfInstanceOfData(tableofAllData);
	mBasicData = new TableOfInstanceOfData(tableofBasicData);
}


void BaseAvmProgram::collectAllData(TableOfInstanceOfData & tableofAllData,
		TableOfInstanceOfData & tableofBasicData, InstanceOfData * mainInstance,
		TableOfSymbol & relativeDataPath, InstanceOfData * anInstance)
{
	std::string pefixID = anInstance->getNameID();
	std::ostringstream ossID;

	if( anInstance->getTypeSpecifier()->hasTypeStructureOrChoiceOrUnion() )
	{
		TableOfSymbol::iterator itField = anInstance->getTypeSpecifier()->
				to< BaseSymbolTypeSpecifier >()->getSymbolData().begin();

		TableOfSymbol::iterator it = anInstance->getAttribute()->begin();
		TableOfSymbol::iterator itEnd = anInstance->getAttribute()->end();
		for( ; it != itEnd ; ++it , ++itField )
		{
			ossID.str( "" );
			ossID << pefixID << "."
					<< NamedElement::extractNameID(
							(*it).getFullyQualifiedNameID() );

			InstanceOfData * newInstance = new InstanceOfData(
					IPointerDataNature::POINTER_UFI_OFFSET_NATURE,
					mainInstance->getContainer(), (*it).rawData());
			newInstance->setSharedData( mainInstance );
			newInstance->setNameID( ossID.str() );
			relativeDataPath.append( *itField );
			newInstance->setDataPath( relativeDataPath );

			newInstance->setAliasTarget( (*it).rawData() );
			(*it).setAliasTarget( newInstance );

			const BF & saveInstance = tableofAllData.save( newInstance );
			if( newInstance->getTypeSpecifier()->hasTypeSimpleOrCollection() )
			{
				tableofBasicData.append( saveInstance );
			}

			collectAllData(tableofAllData, tableofBasicData , mainInstance,
					relativeDataPath, (*it).rawData());

			relativeDataPath.pop_last();
		}
	}

	else if( anInstance->getTypeSpecifier()->isTypedArray() )
	{
		TableOfSymbol::iterator it = anInstance->getAttribute()->begin();
		TableOfSymbol::iterator itEnd = anInstance->getAttribute()->end();
		for( ; it != itEnd ; ++it )
		{
			ossID.str( "" );
			ossID << pefixID << "[" << (*it).getOffset() << "]";

			InstanceOfData * newInstance = new InstanceOfData(
					IPointerDataNature::POINTER_UFI_OFFSET_NATURE,
					mainInstance->getContainer(), (*it).rawData());
			newInstance->setSharedData( mainInstance );
			newInstance->setNameID( ossID.str() );
			relativeDataPath.append( *it );
			newInstance->setDataPath( relativeDataPath );

			(*it).setAliasTarget( newInstance );

			const BF & saveInstance = tableofAllData.save( newInstance );
			if( newInstance->getTypeSpecifier()->hasTypeSimpleOrCollection() )
			{
				tableofBasicData.append( saveInstance );
			}

			collectAllData(tableofAllData, tableofBasicData ,
					mainInstance, relativeDataPath, (*it).rawData());

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

	if( hasDataAlias() )
	{
		os << EOL << TAB << "alias:" << EOL_INCR_INDENT;

		getDataAlias().toStream(os);

		os << DECR_INDENT;
	}

	if( hasData() )
	{
		os << EOL << TAB << "variable:" << EOL_INCR_INDENT;

		getData().toStream(os);

		os << DECR_INDENT;

AVM_IF_DEBUG_FLAG( DATA )
		if( mAllData != &mData )
		{
			os << EOL;
			os << TAB << "variable#all:" << EOL_INCR_INDENT;

			getAllData().toStream(os);

			os << DECR_INDENT;
		}
		if( mBasicData != &mData )
		{
			os << EOL;
			os << TAB << "variable#basic:" << EOL;

			TableOfInstanceOfData::const_raw_iterator itData =
					getBasicData().begin();
			TableOfInstanceOfData::const_raw_iterator endData =
					getBasicData().end();
			for( ; itData != endData ; ++itData )
			{
				os << TAB2 << str_header( *itData ) << ";" << EOL;
			}
		}
AVM_ENDIF_DEBUG_FLAG( DATA )
	}

	os << TAB << "}" << EOL << std::flush;
}


}
