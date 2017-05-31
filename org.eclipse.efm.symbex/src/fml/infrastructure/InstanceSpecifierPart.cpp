/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 avr. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "InstanceSpecifierPart.h"

#include <fml/infrastructure/Machine.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
InstanceSpecifierPart::InstanceSpecifierPart(
		Machine * aContainer, const std::string & aNameID)
: ObjectClassifier( CLASS_KIND_T( InstanceSpecifierPart ) ,
		aContainer , aNameID),
mModel( ),

mInitialInstanceCount( 1 ),
mMaximalInstanceCount( AVM_NUMERIC_MAX_SIZE_T ),

mPossibleDynamicInstanciationCount( 0 ),

mModifierAutoStart( true )
{
	//!! NOTHING
}

InstanceSpecifierPart::InstanceSpecifierPart(Machine * aContainer,
		const BF & aModel, avm_size_t anInitialInstanceCount,
		avm_size_t aMaximalInstanceCount, const std::string & aNameID)
: ObjectClassifier( CLASS_KIND_T( InstanceSpecifierPart ) ,
		aContainer , aNameID),
mModel( aModel ),

mInitialInstanceCount( anInitialInstanceCount ),
mMaximalInstanceCount( aMaximalInstanceCount ),

mPossibleDynamicInstanciationCount( 0 ),

mModifierAutoStart( true )
{
	//!! NOTHING
}


/**
 * Serialization
 */
void InstanceSpecifierPart::strMultiplicity(OutStream & os,
		avm_size_t anInitialCount, avm_size_t aMaximalCount,
		const std::string & leftSeparator, const std::string & rightSeparator)
{
	if( aMaximalCount == AVM_NUMERIC_MAX_SIZE_T )
	{
		if( anInitialCount == 0 )
		{
			os << leftSeparator << "*" << rightSeparator;
		}
		else if( anInitialCount == 1 )
		{
			os << leftSeparator << "+" << rightSeparator;
		}
		else
		{
			os << leftSeparator << anInitialCount << ", +" << rightSeparator;
		}
	}
	else if( anInitialCount != aMaximalCount )
	{
		os << leftSeparator << anInitialCount
				<< ", " << aMaximalCount << rightSeparator;
	}
	else
	{
		os << leftSeparator << anInitialCount << rightSeparator;
	}
}


void InstanceSpecifierPart::strMultiplicity(
		OutStream & os, avm_size_t anInitialCount,
		avm_size_t aPossibleDynamicCount, avm_size_t aMaximalCount,
		const std::string & leftSeparator, const std::string & rightSeparator)
{
	if( aPossibleDynamicCount > 0 )
	{
		os << leftSeparator << anInitialCount
				<< ", " << aPossibleDynamicCount << ", ";

		if( aMaximalCount != AVM_NUMERIC_MAX_SIZE_T )
		{
			os << aMaximalCount << rightSeparator;
		}
		else
		{
			os << "+" << rightSeparator;
		}
	}
	else
	{
		InstanceSpecifierPart::strMultiplicity(os, anInitialCount,
				aMaximalCount, leftSeparator, rightSeparator);
	}
}


inline static bool showMultiplicity(
		const Machine * aMachine, avm_size_t anInitialCount,
		avm_size_t aPossibleDynamicCount, avm_size_t aMaximalCount)
{
	return( ( aMachine->getSpecifier().isFamilyComponentState()
			&& (anInitialCount == 1) && (aPossibleDynamicCount == 0)
			&& (aMaximalCount == AVM_NUMERIC_MAX_SIZE_T) ) ? false : true );
}

void InstanceSpecifierPart::header(OutStream & os, bool & hasChevron) const
{
	if( hasModel() )
	{
		if( hasChevron ) { os << " , "; }
		else { os << "< "; hasChevron = true; }

		os << "model: " << ((getModel().is< Machine >()) ?
				getModel().to_ptr< Machine >()->getNameID() : getModel().str());
	}

	if( showMultiplicity(getContainerMachine(), mInitialInstanceCount,
			mPossibleDynamicInstanciationCount, mMaximalInstanceCount) )
	{
		if( hasChevron ) { os << " , "; }
		else { os << "< "; hasChevron = true; }

		InstanceSpecifierPart::strMultiplicity(
				os, mInitialInstanceCount,
				mPossibleDynamicInstanciationCount,
				mMaximalInstanceCount, "instance: [ ", " ]");
	}

	if( not isAutoStart() )
	{
		if( hasChevron ) { os << " , "; }
		else { os << "< "; hasChevron = true; }
		os << "autostart = false";
	}
}


void InstanceSpecifierPart::toStream(OutStream & os) const
{
	os << TAB << "@" << getNameID() << ":" << EOL;
}



} /* namespace sep */
