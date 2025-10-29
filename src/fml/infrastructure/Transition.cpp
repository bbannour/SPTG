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

#include <fml/expression/ExpressionParser.h>

#include <fml/expression/StatementTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementParser.h>

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Transition::Transition(Machine & aContainer)
: BehavioralElement( CLASS_KIND_T( Transition ), aContainer),
SpecifierImpl( ),

mMocKind( MOC_SIMPLE_KIND ),

mPriority( 0 ),
mProbability( 0.0 ),
mTokenCount( 0 ),

mSource( aContainer ),
mTarget( ),

mPropertyDeclaration( nullptr ),
mStatement( )
{
	//!! NOTHING
}

Transition::Transition(Machine & aContainer,
		const std::string & aNameID, MOC_KIND aKind)
: BehavioralElement( CLASS_KIND_T( Transition ), (& aContainer), aNameID),
SpecifierImpl( ),

mMocKind( aKind ),

mPriority( 0 ),
mProbability( 0.0 ),
mTokenCount( 0 ),

mSource( aContainer ),
mTarget( ),

mPropertyDeclaration( nullptr ),
mStatement( )
{
	//!! NOTHING
}

Transition::Transition(Machine & aContainer, const Transition & aTransPattern)
: BehavioralElement(CLASS_KIND_T( Transition ), aContainer, aTransPattern),
 SpecifierImpl( aTransPattern ),

mMocKind( aTransPattern.mMocKind ),

mPriority( aTransPattern.mPriority ),
mProbability( aTransPattern.mProbability ),
mTokenCount( aTransPattern.mTokenCount ),

mSource( aContainer ),
mTarget( aTransPattern.mTarget ),

mPropertyDeclaration( (aTransPattern.mPropertyDeclaration == nullptr)
		? nullptr : new PropertyPart( *(aTransPattern.mPropertyDeclaration) ) ),
mStatement( aTransPattern.mStatement )
{

}


// For Python Binding
Transition::Transition(Machine & aContainer, const std::string & aNameID)
: BehavioralElement( CLASS_KIND_T( Transition ), (& aContainer), aNameID),
SpecifierImpl( ),

mMocKind( MOC_SIMPLE_KIND ),

mPriority( 0 ),
mProbability( 0.0 ),
mTokenCount( 0 ),

mSource( aContainer ),
mTarget( ),

mPropertyDeclaration( nullptr ),
mStatement( )
{
	//!! NOTHING
}

Transition::Transition(Machine & aSource,
		const std::string & aNameID, Machine & aTarget)
: BehavioralElement( CLASS_KIND_T( Transition ), (& aSource), aNameID),
SpecifierImpl( ),

mMocKind( MOC_SIMPLE_KIND ),

mPriority( 0 ),
mProbability( 0.0 ),
mTokenCount( 0 ),

mSource( aSource ),
mTarget( INCR_BF(& aTarget) ),

mPropertyDeclaration( nullptr ),
mStatement( )
{
	//!! NOTHING
}


/**
 * DESTRUCTOR
 */
Transition::~Transition()
{
	delete mPropertyDeclaration;
}


/**
 * GETTER - SETTER
 * mPropertyDeclaration
 */
const PropertyPart & Transition::getPropertyPart() const
{
	return( * mPropertyDeclaration );
}

bool Transition::hasPropertyPart() const
{
	return( (mPropertyDeclaration != nullptr)
			&& mPropertyDeclaration->nonempty() );
}



/**
  * GETTER - SETTER
 * UFI , ID
 */
void Transition::updateNameID(const std::string & aNameID)
{
	setFullyQualifiedNameID(
			ObjectElement::makeFullyQualifiedNameID(
					getContainer()->as_ptr< Machine >(), aNameID) );

	setNameID(aNameID);

	setUnrestrictedName(aNameID);
}


/**
 * GETTER - SETTER
 * mSource
 */
Machine * Transition::getSourceContainer() const
{
	return( mSource.getContainerMachine() );
}

/**
 * SETTER
 * mTarget
 */
void Transition::setTarget(Machine & aTarget)
{
	mTarget = INCR_BF(& aTarget);
}


/**
 * GETTER - SETTER
 * mStatement
 */
inline void Transition::addStatement(const BFCode & aStatement)
{
	if( mStatement.valid() )
	{
		if( StatementTypeChecker::isSchedule(mStatement) )
		{
			mStatement.append( aStatement );
		}
		else
		{
			mStatement = StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE, mStatement, aStatement);
		}
	}
	else
	{
		mStatement = aStatement;
	}
}

inline void Transition::seqStatement(const BFCode & aStatement)
{
	if( mStatement.valid() )
	{
		mStatement = StatementConstructor::newCodeFlat(
				OperatorManager::OPERATOR_SEQUENCE, mStatement, aStatement);
	}
	else
	{
		mStatement = aStatement;
	}
}


// For Python Binding
bool Transition::addStatement(const std::string & rawStatement)
{
	const Machine & machineCtx = getSource();
	BFCode aStatement = StatementParser::parse(machineCtx, rawStatement);
	if( aStatement.valid() )
	{
		addStatement( aStatement );

		return true;

	}
	else
	{
		return false;
	}
}

bool Transition::setStatement(const std::string & rawStatement)
{
	const Machine & machineCtx = getSource();
	BFCode aStatement = StatementParser::parse(machineCtx, rawStatement);
	if( aStatement.valid() )
	{
		setStatement( aStatement );

		return true;

	}
	else
	{
		return false;
	}
}


bool Transition::addOutput(Port & outPort, std::vector< std::string > & rvalues)
{
	BFCode outputStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_OUTPUT, INCR_BF(& outPort) );

	const Machine & machineCtx = getSource();
	for( const auto & rvalue : rvalues )
	{
		const BF & rvalueExpr = ExpressionParser::parse(machineCtx, rvalue);
		if( rvalueExpr.valid() )
		{
			outputStatement.append( rvalueExpr );
		}
		else
		{
			return false;
		}
	}

	addStatement( outputStatement );

	return true;
}

bool Transition::addInput(Port & inPort, std::vector< std::string > & lvalues)
{
	BFCode inputStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, INCR_BF(& inPort));

	const Machine & machineCtx = getSource();
	for( const auto & lvalue : lvalues )
	{
		const BF & lvalueVar = ExpressionParser::parseVariable(machineCtx, lvalue);
		if( lvalueVar.valid() )
		{
			inputStatement.append( lvalueVar );
		}
		else
		{
			return false;
		}
	}

	addStatement( inputStatement );

	return true;
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

			if( kind & MOC_ABORT_KIND )
			{
				strKind = "abort";
				sep = SEPARATOR;
			}

			if( kind & MOC_FINAL_KIND )
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


void Transition::strHeader(OutStream & out) const
{
	out << getModifier().toString() << "transition";
	if( not isMocSimple() )
	{
		out << "< " << strMocKind( ~ MOC_SIMPLE_KIND );
		if( mPriority != 0 )
		{
			out << " , " << mPriority;
		}
		if( mProbability != 0 )
		{
			out << " , " << mProbability;
		}
		out << " >";
	}
	else if( mPriority != 0 )
	{
		out << "< " << mPriority;
		if( mProbability != 0 )
		{
			out << " , " << mProbability;
		}
		out << " >";
	}
	else if( mProbability != 0 )
	{
		out << "< " << mProbability << " >";
	}

	out << " " << getNameID();

	if( mTarget.valid() )
	{
		if( mTokenCount != 0 )
		{
			out << "(" << mTokenCount << ")";
		}

		out << " : " << str_header( getContainer()->as_ptr< Machine >() ) << " --> "
				<< (mTarget.is< Machine >() ?
					mTarget.to< Machine >().getNameID() : mTarget.str());
	}
}


void Transition::toStreamHeader(OutStream & out) const
{
	out << getModifier().toString()
			<< "transition " << getNameID() << " : "
			<< getSource().getNameID();

	if( mTarget.is< Machine >() || mTarget.is< Variable >() )
	{
		out << " --> " << mTarget.to< ObjectElement >().getNameID();
	}
	else if( mTarget.valid() )
	{
		out << " --> " << mTarget.str();
	}

	out << std::flush;
}


void Transition::toStream(OutStream & out) const
{
	out << TAB << "transition";
	if( not isMocSimple() )
	{
		out << "< " << strMocKind( ~ MOC_SIMPLE_KIND );
		if( mPriority != 0 )
		{
			out << " , " << mPriority;
		}
		if( mProbability != 0 )
		{
			out << " , " << mProbability;
		}
		out << " >";
	}
	else if( mPriority != 0 )
	{
		out << "< " << mPriority;
		if( mProbability != 0 )
		{
			out << " , " << mProbability;
		}
		out << " >";
	}
	else if( mProbability != 0 )
	{
		out << "< " << mProbability << " >";
	}

	if( mTokenCount != 0 )
	{
		out << "(" << mTokenCount << ")";
	}

	out << " " << getNameID();

	if( hasReallyUnrestrictedName() )
	{
		out << " \"" << getUnrestrictedName() << "\"";
	}

	if( mTarget.valid() )
	{
		out << " --> ";

		if( mTarget.is< Machine >() )
		{
AVM_IF_DEBUG_FLAG( TRANSITION )
			out << mTarget.to< Machine >().getFullyQualifiedNameID();
AVM_ELSE
			out << mTarget.to< Machine >().getNameID();
AVM_ENDIF_DEBUG_FLAG( TRANSITION )
		}
		else
		{
			out << mTarget.str();
		}
	}

	if( hasPropertyPart() )
	{
		out << " {" << EOL;

		mPropertyDeclaration->toStream(out);
		out << EOL;

		if( mStatement.valid() )
		{
			out << TAB << "moe:" << EOL;

			out << TAB2 << "@run{" << INCR2_INDENT;
			mStatement->toStreamRoutine( out );
			out << DECR2_INDENT_TAB2 << "}" << EOL;
		}

		out << TAB << "}" << EOL;
	}

	else if( mStatement.valid()
			&& (not StatementTypeChecker::isEmptySequence(* mStatement)) )
	{
		mStatement->toStreamRoutine( out << " {" << INCR_INDENT )
				<< DECR_INDENT_TAB << "}";
	}
	else
	{
		out << ";";
	}

	out << EOL << std::flush;
}


}
