/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Transition.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
/**
 * CONSTRUCTOR
 * Default
 */
Transition::Transition(Machine * aContainer)
: BehavioralElement( CLASS_KIND_T( Transition ), aContainer),
SpecifierImpl( ),

mMocKind( MOC_SIMPLE_KIND ),

mPriority( 0 ),
mProbability( 0.0 ),
mTokenCount( 0 ),

mSource( aContainer ),
mTarget( ),

mDeclaration( NULL ),
mStatement( )
{
	//!! NOTHING
}

Transition::Transition(Machine * aContainer,
		const std::string & aNameID, MOC_KIND aKind)
: BehavioralElement( CLASS_KIND_T( Transition ), aContainer, aNameID),
SpecifierImpl( ),

mMocKind( aKind ),

mPriority( 0 ),
mProbability( 0.0 ),
mTokenCount( 0 ),

mSource( aContainer ),
mTarget( ),

mDeclaration( NULL ),
mStatement( )
{
	//!! NOTHING
}

Transition::Transition(Machine * aContainer, const Transition * aTransPattern)
: BehavioralElement(CLASS_KIND_T( Transition ), aContainer, (*aTransPattern)),
 SpecifierImpl( aTransPattern ),

mMocKind( aTransPattern->mMocKind ),

mPriority( aTransPattern->mPriority ),
mProbability( aTransPattern->mProbability ),
mTokenCount( aTransPattern->mTokenCount ),

mSource( aContainer ),
mTarget( aTransPattern->mTarget ),

mDeclaration( (aTransPattern->mDeclaration == NULL) ? NULL :
		new PropertyPart( *(aTransPattern->mDeclaration) ) ),
mStatement( aTransPattern->mStatement )
{

}


/**
 * DESTRUCTOR
 */
Transition::~Transition()
{
	delete mDeclaration;
}


/**
 * GETTER - SETTER
 * mDeclaration
 */

bool Transition::hasDeclaration() const
{
	return( (mDeclaration != NULL) && mDeclaration->nonempty() );
}



/**
  * GETTER - SETTER
 * UFI , ID
 */
void Transition::updateNameID(const std::string & aNameID)
{
	setFullyQualifiedNameID(
			ObjectElement::makeFullyQualifiedNameID(
					getContainer()->as< Machine >(), aNameID) );

	setNameID(aNameID);

	setUnrestrictedName(aNameID);
}


/**
 * GETTER - SETTER
 * mSource
 */
Machine * Transition::getSourceContainer() const
{
	return( mSource->getContainerMachine() );
}


/**
 * Serialization
 */
Transition::MOC_KIND Transition::toMocKind(const std::string & id)
{
	if( id == "simple"   ) return MOC_SIMPLE_KIND;

	if( id == "abort"    ) return MOC_ABORT_KIND;

	if( id == "final"    ) return MOC_FINAL_KIND;

	if( id == "else"     ) return MOC_ELSE_KIND;

	if( id == "internal" ) return MOC_INTERNAL_KIND;

	if( id == "auto"     ) return MOC_AUTO_KIND;

	if( id == "flow"     ) return MOC_FLOW_KIND;

	return MOC_UNDEFINED_KIND;
}


std::string Transition::strMocKind(
		moc_kind_t mask, const std::string & SEPARATOR) const
{
	moc_kind_t kind = mMocKind & mask;

	switch( kind )
	{
		case MOC_SIMPLE_KIND    : return( "simple"  );
		case MOC_ABORT_KIND     : return( "abort"   );
		case MOC_FINAL_KIND     : return( "final"   );

		case MOC_ELSE_KIND      : return( "else"    );

		case MOC_INTERNAL_KIND  : return( "internal");

		case MOC_AUTO_KIND      : return( "auto"    );

		case MOC_FLOW_KIND      : return( "flow"    );

		case MOC_UNDEFINED_KIND : return( "undefined<transition#kind>" );

		default                 :
		{
			std::string strKind = "";
			std::string sep = "";

			if( kind & MOC_SIMPLE_KIND )
			{
				strKind = "simple";
				sep = SEPARATOR;
			}
			else if( kind & MOC_ABORT_KIND )
			{
				strKind = "abort";
				sep = SEPARATOR;
			}
			else if( kind & MOC_FINAL_KIND )
			{
				strKind = "final";
				sep = SEPARATOR;
			}

			if( kind & MOC_ELSE_KIND )
			{
				strKind = strKind + sep + "else";
			}

			if( strKind.empty() )
			{
				return( "unknown<transition#kind>" );
			}
			else
			{
				return( strKind );
			}

		}
	}
}


void Transition::strHeader(OutStream & os) const
{
	os << getModifier().toString() << "transition";
	if( not isMocSimple() )
	{
		os << "< " << strMocKind( ~ MOC_SIMPLE_KIND );
		if( mPriority != 0 )
		{
			os << " , " << mPriority;
		}
		if( mProbability != 0 )
		{
			os << " , " << mProbability;
		}
		os << " >";
	}
	else if( mPriority != 0 )
	{
		os << "< " << mPriority;
		if( mProbability != 0 )
		{
			os << " , " << mProbability;
		}
		os << " >";
	}
	else if( mProbability != 0 )
	{
		os << "< " << mProbability << " >";
	}

	os << " " << getNameID();

	if( mTarget.valid() )
	{
		if( mTokenCount != 0 )
		{
			os << "(" << mTokenCount << ")";
		}

		os << " : " << str_header( getContainer()->as< Machine >() ) << " --> "
				<< (mTarget.is< Machine >() ?
					mTarget.to_ptr< Machine >()->getNameID() : mTarget.str());
	}
}


void Transition::toStreamHeader(OutStream & os) const
{
	os << getModifier().toString()
			<< "transition " << getNameID() << " : "
			<< getSource()->getNameID();

	if( mTarget.is< Machine >() || mTarget.is< Variable >() )
	{
		os << " --> " << mTarget.to_ptr< ObjectElement >()->getNameID();
	}
	else if( mTarget.valid() )
	{
		os << " --> " << mTarget.str();
	}

	os << std::flush;
}


void Transition::toStream(OutStream & os) const
{
	os << TAB << "transition";
	if( not isMocSimple() )
	{
		os << "< " << strMocKind( ~ MOC_SIMPLE_KIND );
		if( mPriority != 0 )
		{
			os << " , " << mPriority;
		}
		if( mProbability != 0 )
		{
			os << " , " << mProbability;
		}
		os << " >";
	}
	else if( mPriority != 0 )
	{
		os << "< " << mPriority;
		if( mProbability != 0 )
		{
			os << " , " << mProbability;
		}
		os << " >";
	}
	else if( mProbability != 0 )
	{
		os << "< " << mProbability << " >";
	}

	if( mTokenCount != 0 )
	{
		os << "(" << mTokenCount << ")";
	}

	os << " " << getNameID();

	if( mTarget.valid() )
	{
		os << " --> " << mTarget.str();
	}

	if( hasDeclaration() )
	{
		os << " {" << EOL;

		mDeclaration->toStream(os);
		os << EOL;

		if( mStatement.valid() )
		{
			os << TAB << "moe:" << EOL;

			os << TAB2 << "@run{" << INCR2_INDENT;
			mStatement->toStreamRoutine( os );
			os << DECR2_INDENT_TAB2 << "}" << EOL;
		}

		os << TAB << "}" << EOL;
	}

	else if( mStatement.valid() )
	{
		mStatement->toStreamRoutine( os << " {" << INCR_INDENT )
				<< DECR_INDENT_TAB << "}";
	}
	else
	{
		os << ";";
	}

	os << EOL << std::flush;
}


}
