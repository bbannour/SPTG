/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 déc. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Routine.h"

#include <fml/common/BehavioralElement.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Variable.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/operator/OperatorManager.h>
#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Routine::Routine(Machine * aContainer,
		const std::string & aNameID, const Modifier & aModifier,
		const Specifier & aSpecifier, const BF & aModel)
: BehavioralElement( CLASS_KIND_T( Routine ) ,
		aContainer, aModifier , aNameID ),
SpecifierImpl( aSpecifier ),

mModel( aModel ),

mParameters( ),
mReturns( ),
mCode( )
{
	//!! NOTHING
}


Routine::Routine(const BehavioralPart & aBehavioralPart,
		const std::string & aNameID, const Specifier & aSpecifier)
: BehavioralElement( CLASS_KIND_T( Routine ),
		aBehavioralPart.getContainer(), aNameID ),
SpecifierImpl( aSpecifier ),

mModel( BF::REF_NULL ),

mParameters( ),
mReturns( ),
mCode( )
{
	//!! NOTHING
}


Routine * Routine::newDefine(Machine * aContainer, const std::string & aNameID)
{
	return( new Routine(aContainer, aNameID,
			Specifier::DESIGN_MODEL_SPECIFIER) );
}

Routine * Routine::newInvoke(Machine * aContainer, const BF & aModel)
{
	return( new Routine(aContainer,
			aModel.as_ptr< Routine >()->getNameID(),
			Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER, aModel) );
}


/**
 * GETTER
 * from vector of parameters / returns
 */
const BF & Routine::getByNameID(
		const BFVector & params, const std::string & aNameID)
{
	BFVector::const_iterator it = params.begin();
	BFVector::const_iterator endIt = params.end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).is< Variable >() &&
				((*it).to_ptr< Variable >()->getNameID() == aNameID) )
		{
			return( *it );
		}
	}

	return( BF::REF_NULL );
}


avm_offset_t Routine::getOffsetByNameID(
		const BFVector & params, const std::string & label)
{
	BFVector::const_iterator it = params.begin();
	BFVector::const_iterator endIt = params.end();
	for( avm_offset_t offset ; it != endIt ; ++it , ++offset )
	{
		if( (*it).is< Variable >() &&
				((*it).to_ptr< Variable >()->getNameID() == label) )
		{
			return( offset );
		}
	}

	return( AVM_NO_OFFSET );
}


/**
 * TESTER
 * mParameters
 * mReturns
 */
//!! Warning: Unused static function
//static bool isContained(const BFVector & params, Variable * aParam)
//{
//	BFVector::const_iterator it = params.begin();
//	BFVector::const_iterator endIt = params.end();
//	for( avm_offset_t offset ; it != endIt ; ++it , ++offset )
//	{
//		if( (*it).isTEQ(aParam) )
//		{
//			return( true );
//		}
//	}
//
//	return( false );
//}


bool Routine::hasParameterOffset(Variable * aParameter) const
{
	return( (aParameter->getOffset() < mParameters.size()) &&
		mParameters[ aParameter->getOffset() ].isTEQ(aParameter) );
}

void Routine::saveParameter(Variable * anInput)
{
	mParameters.append( BF(anInput) );
}


bool Routine::hasReturnOffset(Variable * aReturn) const
{
	return( (aReturn->getOffset() < mReturns.size()) &&
		mReturns[ aReturn->getOffset() ].isTEQ(aReturn) );
}

void Routine::saveReturn(Variable * anOutput)
{
	mReturns.append( BF(anOutput) );
}


/**
 * MACRO
 * INLINING
 */
BFCode Routine::inlineCode(const BFCode & aCode) const
{
	if( aCode->isOpCode( AVM_OPCODE_RETURN ) )
	{
		return( BFCode::REF_NULL );
	}
	else
	{
		BFCode newCode( aCode->getOperator() );
		BF substArg;

		AvmCode::const_iterator itArg = aCode->begin();
		AvmCode::const_iterator itEndArg = aCode->end();
		for( ; itArg != itEndArg ; ++itArg )
		{
			if( (substArg = inlineCode(*itArg)).valid() )
			{
				newCode->append( substArg );
			}
			else
			{
				return( BFCode::REF_NULL );
			}
		}

		return( newCode );
	}
}


BF Routine::inlineCode(const BF & aCode) const
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( inlineCode( aCode.bfCode() ) );
		}

		case FORM_XFSP_VARIABLE_KIND:
		{
			Variable * aVar = aCode.to_ptr< Variable >();

			if( getModel()->hasParameterOffset( aVar ) )
			{
				if( (aVar->getOffset() < mParameters.size()) &&
					mParameters[ aVar->getOffset() ].valid() )
				{
					return( mParameters[ aVar->getOffset() ] );
				}
				else if( aVar->hasValue() )
				{
					return( aVar->getValue() );
				}
				else if( aVar->getModifier().hasNatureMacro()
						&& aVar->hasBinding() )
				{
					return( aVar->getBinding() );
				}

				return( BFCode::REF_NULL );
			}
			else if( getModel()->hasReturnOffset( aVar ) )
			{
				if( (aVar->getOffset() < mReturns.size()) &&
						mReturns[ aVar->getOffset() ].valid() )
				{
					return( mReturns[ aVar->getOffset() ] );
				}
				else if( aVar->hasValue() )
				{
					return( aVar->getValue() );
				}
				else if( aVar->getModifier().hasNatureMacro()
						&& aVar->hasBinding() )
				{
					return( aVar->getBinding() );
				}

				return( BFCode::REF_NULL );
			}

			return( aCode );
		}

		case FORM_UFI_KIND:
		{
			UniFormIdentifier * anUFI = aCode.to_ptr< UniFormIdentifier >();

			UniFormIdentifier::ListOfField::const_iterator itField = anUFI->begin();
			UniFormIdentifier::ListOfField::const_iterator endField = anUFI->end();

			BF newCode;
			BF substArg;

			if( (substArg = inlineCode(*itField)).valid() )
			{
				if( substArg.is< UniFormIdentifier >() )
				{
					newCode = anUFI = new UniFormIdentifier(
							substArg.to_ref< UniFormIdentifier >() );
				}
				else
				{
					newCode = anUFI = new UniFormIdentifier(anUFI->getLocator());

					anUFI->appendField( substArg , (*itField).getScheme() );
				}

				for( ++itField ; itField != endField ; ++itField )
				{
					if( (substArg = inlineCode(*itField)).valid() )
					{
						anUFI->appendField( substArg , (*itField).getScheme() );
					}
					else
					{
						return( BFCode::REF_NULL );
					}
				}

				return( newCode );
			}
			else
			{
				return( BFCode::REF_NULL );
			}
		}

		case FORM_ARRAY_BF_KIND:
		{
			ArrayBF * arrayIn = aCode.to_ptr< ArrayBF >();

			ArrayBF * arrayOut = new ArrayBF(
					arrayIn->getTypeSpecifier(), arrayIn->size());

			BF newCode( arrayOut );
			BF substArg;

			for( avm_size_t idx = 0 ; idx < arrayIn->size() ; ++idx )
			{
				if( (substArg = inlineCode(arrayIn->at(idx))).valid() )
				{
					arrayOut->set(idx, substArg);
				}
				else
				{
					return( BFCode::REF_NULL );
				}
			}

			return( newCode );
		}

		default:
		{
			return( aCode );
		}
	}

	return( aCode );
}


/**
 * Serialization
 */
void Routine::strParameters(OutStream & os, const std::string & sep) const
{
	BFVector::const_iterator it = mParameters.begin();
	BFVector::const_iterator endIt = mParameters.end();

	os << "(";
	if( (*it).is< Variable >() )
	{
		os << "$" << (*it).to_ptr< Variable >()->getOffset() << ": ";
		(*it).to_ptr< Variable >()->strParameter(os);
	}
	else
	{
		os << (*it).str();
	}
	for( ++it ; it != endIt ; ++it )
	{
		os << ", ";
		if( (*it).is< Variable >() )
		{
			os << "$" << (*it).to_ptr< Variable >()->getOffset() << ": ";
			(*it).to_ptr< Variable >()->strParameter(os);
		}
		else
		{
			os << (*it).str();
		}
	}
	os << ")";
}

void Routine::strReturns(OutStream & os, const std::string & sep) const
{
	BFVector::const_iterator it = mReturns.begin();
	BFVector::const_iterator endIt = mReturns.end();

	os << "(";
	if( (*it).is< Variable >() )
	{
		os << "$" << (*it).to_ptr< Variable >()->getOffset() << ": ";
		(*it).to_ptr< Variable >()->strReturn(os);
	}
	else
	{
		os << (*it).str();
	}
	for( ++it ; it != endIt ; ++it )
	{
		os << ", ";
		if( (*it).is< Variable >() )
		{
			os << "$" << (*it).to_ptr< Variable >()->getOffset() << ": ";
			(*it).to_ptr< Variable >()->strReturn(os);
		}
		else
		{
			os << (*it).str();
		}
	}
	os << ")";
}


void Routine::strHeader(OutStream & os) const
{
	os << getModifier().toString();

	if( getSpecifier().isDesignPrototypeStatic() )
	{
		os << getSpecifier().toString_not(
				Specifier::DESIGN_PROTOTYPE_STATIC_KIND) << "@";
	}
	else
	{
		os << getSpecifier().toString() << "routine ";
	}

	os << getNameID();

	if( mParameters.nonempty() )
	{
		strParameters(os);
	}
	if( mReturns.nonempty() )
	{
		os << " --> ";

		strReturns(os);
	}
}


void Routine::toStream(OutStream & os) const
{
	strHeader( os << TAB );

	os << "{";
	if( mCode.valid() )
	{
		mCode->toStreamRoutine( os << INCR_INDENT ) << DECR_INDENT_TAB;
	}
	os << "}" << EOL_FLUSH;
}



void Routine::strInvokeParameters(OutStream & os, const std::string & sep) const
{
	BFVector::const_iterator it = mParameters.begin();
	BFVector::const_iterator endIt = mParameters.end();

	os << "(";
	AvmCode::toStream(os, *it);
	for( ++it ; it != endIt ; ++it )
	{
		os << ", ";
		AvmCode::toStream(os, *it);
	}
	os << ")";
}

void Routine::strInvokeReturns(OutStream & os, const std::string & sep) const
{
	BFVector::const_iterator it = mReturns.begin();
	BFVector::const_iterator endIt = mReturns.end();

	os << "(";
	AvmCode::toStream(os, *it);
	for( ++it ; it != endIt ; ++it )
	{
		os << ", ";
		AvmCode::toStream(os, *it);
	}
	os << ")";
}


void Routine::toStreamInvoke(OutStream & os, const std::string & sep) const
{
	os << TAB << getNameID() << AVM_NO_INDENT;

	if( mParameters.nonempty() )
	{
		strInvokeParameters(os, sep);
	}
	else
	{
		os << "()";
	}

	if( mReturns.nonempty() )
	{
		os << " --> ";
		strInvokeReturns(os, sep);
	}

	AVM_DEBUG_REF_COUNTER(os);

	os << END_INDENT << EOL_FLUSH;
}


} /* namespace sep */
