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
		const BF & aModel, std::size_t anInitialInstanceCount,
		std::size_t aMaximalInstanceCount, const std::string & aNameID)
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
void InstanceSpecifierPart::strMultiplicity(OutStream & out,
		std::size_t anInitialCount, std::size_t aMaximalCount,
		const std::string & leftSeparator, const std::string & rightSeparator)
{
	if( aMaximalCount == AVM_NUMERIC_MAX_SIZE_T )
	{
		if( anInitialCount == 0 )
		{
			out << leftSeparator << "*" << rightSeparator;
		}
		else if( anInitialCount == 1 )
		{
			out << leftSeparator << "+" << rightSeparator;
		}
		else
		{
			out << leftSeparator << anInitialCount << ", +" << rightSeparator;
		}
	}
	else if( anInitialCount != aMaximalCount )
	{
		out << leftSeparator << anInitialCount
				<< ", " << aMaximalCount << rightSeparator;
	}
	else
	{
		out << leftSeparator << anInitialCount << rightSeparator;
	}
}


void InstanceSpecifierPart::strMultiplicity(
		OutStream & out, std::size_t anInitialCount,
		std::size_t aPossibleDynamicCount, std::size_t aMaximalCount,
		const std::string & leftSeparator, const std::string & rightSeparator)
{
	if( aPossibleDynamicCount > 0 )
	{
		out << leftSeparator << anInitialCount
				<< ", " << aPossibleDynamicCount << ", ";

		if( aMaximalCount != AVM_NUMERIC_MAX_SIZE_T )
		{
			out << aMaximalCount << rightSeparator;
		}
		else
		{
			out << "+" << rightSeparator;
		}
	}
	else
	{
		InstanceSpecifierPart::strMultiplicity(out, anInitialCount,
				aMaximalCount, leftSeparator, rightSeparator);
	}
}


inline static bool showMultiplicity(
		const Machine * aMachine, std::size_t anInitialCount,
		std::size_t aPossibleDynamicCount, std::size_t aMaximalCount)
{
	return( ( ( aMachine->getSpecifier().isFamilyComponentState()
				|| aMachine->getSpecifier().isFamilyComponentStatemachine()
				|| aMachine->getSpecifier().isComponentSystem() )
			&& (anInitialCount == 1) && (aPossibleDynamicCount == 0)
			&& (aMaximalCount == AVM_NUMERIC_MAX_SIZE_T) ) ? false : true );
}

void InstanceSpecifierPart::header(OutStream & out, bool & hasChevron) const
{
	if( hasModel() )
	{
		if( hasChevron ) { out << " , "; }
		else { out << "< "; hasChevron = true; }

		out << "model: " << ((getModel().is< Machine >()) ?
				getModel().to< Machine >().getNameID() : getModel().str());
	}

	if( showMultiplicity(getContainerMachine(), mInitialInstanceCount,
			mPossibleDynamicInstanciationCount, mMaximalInstanceCount) )
	{
		if( hasChevron ) { out << " , "; }
		else { out << "< "; hasChevron = true; }

		InstanceSpecifierPart::strMultiplicity(
				out, mInitialInstanceCount,
				mPossibleDynamicInstanciationCount,
				mMaximalInstanceCount, "instance: [ ", " ]");
	}

	if( not isAutoStart() )
	{
		if( hasChevron ) { out << " , "; }
		else { out << "< "; hasChevron = true; }
		out << "autostart = false";
	}
}


void InstanceSpecifierPart::toStream(OutStream & out) const
{
	out << TAB << "@" << getNameID() << ":" << EOL;
}



} /* namespace sep */
