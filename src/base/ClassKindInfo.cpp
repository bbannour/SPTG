/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 déc. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ClassKindInfo.h"

#include <util/avm_assert.h>

#include <boost/core/demangle.hpp>

namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CLASS KIND INFO
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ClassKindInfo * ClassKindInfo::TYPE_UNDEFINED_INFO = nullptr;

/**
 * CONSTRUCTOR
 * Default
 */
ClassKindInfo::ClassKindInfo(class_kind_t aClassKind,
		const std::string & tname, const std::string & aName)
: mKIND( aClassKind ),
mTNAME( boost::core::demangle(tname.c_str()) ),
mNAME ( boost::core::demangle(aName.c_str()) )
{
	ClassKindInfoInitializer::CKI_TABLE->push_back( this );
}


std::string ClassKindInfo::info() const
{
	return( OSS() << "typeinfo< " << std::setw(3) << ((std::size_t) mKIND)
			<< " , " << mNAME << ( ( mNAME != mTNAME ) ? " , " + mTNAME : "")
			<< " >" );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CLASS KIND INFO INITIALIZER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

std::uint16_t ClassKindInfoInitializer::NIFTY_COUNTER = 0;

std::vector< ClassKindInfo * > * ClassKindInfoInitializer::CKI_TABLE;



/**
 * CONSTRUCTOR
 * Default
 * Ensures equality between ENUM_CLASS_KIND literal
 * and ClassKindInfo::mKIND of base classes !
 * Due to dependencies, implementation in main/StaticInitializer
 */
//ClassKindInfoInitializer::ClassKindInfoInitializer()


/**
 * DESTRUCTOR
 */
ClassKindInfoInitializer::~ClassKindInfoInitializer()
{
	if( 0 == --NIFTY_COUNTER )
	{
//		toStreamTable(std::cout, ~ClassKindInfoInitializer);
//
//		ClassKindInfoInitializer::CKI_TABLE->clear();

		delete( CKI_TABLE );
		delete( ClassKindInfo::TYPE_UNDEFINED_INFO );
	}
}


/**
 * Loader
 * Checking equality between ENUM_CLASS_KIND literal
 * and ClassKindInfo::mKIND of base classes !
 * Mandatory, call by load()
 * Due to dependencies, implementation in main/StaticInitializer
 */
// void ClassKindInfoInitializer::checkingAssertions()


////////////////////////////////////////////////////////////////////////////////
// LOADER / DISPOSER  API
////////////////////////////////////////////////////////////////////////////////

void ClassKindInfoInitializer::load()
{
	// Ensures equality between ENUM_CLASS_KIND literal
	// and ClassKindInfo::mKIND of base classes !
	checkingAssertions();

AVM_IF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
	toStreamTable(AVM_OS_COUT, "ClassKindInfoInitializer::load");
AVM_ENDIF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
}


void ClassKindInfoInitializer::dispose()
{
AVM_IF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
	toStreamTable(AVM_OS_COUT, "ClassKindInfoInitializer::dispose");
AVM_ENDIF_DEBUG_LEVEL_FLAG( ULTRA , COMPILING )
}


// For debug trace
void ClassKindInfoInitializer::toStreamTable(
		OutStream & out, const std::string & msg)
{
	out << TAB << msg << ":>" << std::endl;
	for( const auto & itCKI : *CKI_TABLE )
	{
		out << TAB2 << itCKI->info() << EOL;
	}

	out << TAB << "CKI_TABLE.size: " << CKI_TABLE->size() << EOL
		<< TAB << "NIFTY_COUNTER : " << NIFTY_COUNTER << EOL

		<< TAB << "end" << EOL_FLUSH;
}

// Mandatory for debug trace in constructor ClassKindInfoInitializer()
void ClassKindInfoInitializer::toStreamTable(const std::string & msg)
{
	std::cout << msg << ":>" << std::endl;
	for( const auto & itCKI : *CKI_TABLE )
	{
		std::cout << " " << itCKI->info() << std::endl;
	}

	std::cout << "CKI_TABLE.size: " << CKI_TABLE->size() << std::endl
			<< "NIFTY_COUNTER : " << NIFTY_COUNTER << std::endl
			<< "end" << std::endl << std::flush;
}




} /* namespace sep */
