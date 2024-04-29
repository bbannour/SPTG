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

#include <fml/expression/BuiltinArray.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Variable.h>

#include <fml/lib/AvmOperationFactory.h>

#include <fml/operator/OperatorManager.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Routine::Routine(Machine & aContainer,
		const std::string & aNameID, const Modifier & aModifier,
		const Specifier & aSpecifier, const BF & aModel)
: BehavioralElement( CLASS_KIND_T( Routine ), aContainer, aModifier, aNameID ),
SpecifierImpl( aSpecifier ),

mModel( aModel ),

mPropertyDeclaration( this , "property" ),

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

mPropertyDeclaration( this , "property" ),

mCode( )
{
	//!! NOTHING
}


Routine * Routine::newDefine(Machine & aContainer, const std::string & aNameID)
{
	return( new Routine(aContainer, aNameID,
			Specifier::DESIGN_MODEL_SPECIFIER) );
}

Routine * Routine::newInvoke(Machine & aContainer, const BF & aModel)
{
	return( new Routine(aContainer,
			aModel.as_ptr< Routine >()->getNameID(),
			Specifier::DESIGN_INSTANCE_DYNAMIC_SPECIFIER, aModel) );
}


/**
 * GETTER
 * Unique Null Reference
 */
Routine & Routine::nullref()
{
	static Routine _NULL_(Machine::nullref(), "$null<Routine>",
			Specifier::OBJECT_NULL_SPECIFIER);
	_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );

	return( _NULL_ );
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

		for( const auto & itOperand : aCode.getOperands() )
		{
			if( (substArg = inlineCode(itOperand)).valid() )
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

			if( getModel()->getPropertyPart().
					getVariableParameters().contains(aVar) )
			{
				if( (aVar->getRuntimeOffset() <
						getPropertyPart().getVariableParametersCount())
					&& getPropertyPart().getVariableParameter(
							aVar->getRuntimeOffset() ).valid() )
				{
					return( getPropertyPart().getVariableParameter(
							aVar->getRuntimeOffset() ) );
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
			else if( getModel()->getPropertyPart().
						getVariableReturns().contains(aVar) )
			{
				if( (aVar->getRuntimeOffset() <
						getPropertyPart().getVariableReturnsCount())
					&& getPropertyPart().getVariableReturn(
							aVar->getRuntimeOffset() ).valid() )
				{
					return( getPropertyPart().getVariableReturn(
							aVar->getRuntimeOffset() ) );
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
							substArg.to< UniFormIdentifier >() );
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

			for( std::size_t idx = 0 ; idx < arrayIn->size() ; ++idx )
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


////////////////////////////////////////////////////////////////////////////////
// ROUTINE INVOKATION
BFCode Routine::invokeRoutine(Routine * aRoutineInstance)
{
	const PropertyPart & aPropertyPart = aRoutineInstance->getPropertyPart();
	if( aPropertyPart.hasVariableParameter() )
	{
		BF bfOP;
		if( aRoutineInstance->hasModelOperator() )
		{
			bfOP = aRoutineInstance->getType();
		}
		else
		{
			const Operator * op = AvmOperationFactory::get(
					aPropertyPart.getVariableParameter(0),
					aRoutineInstance->getType().str() );
			if( op != nullptr )
			{
				bfOP = INCR_BF( const_cast< Operator * >(op) );
			}
		}

		if( bfOP.valid() )
		{
			BFVector::const_iterator it =
					aPropertyPart.getVariableParameters().begin();
			BFVector::const_iterator endIt =
					aPropertyPart.getVariableParameters().end();

			BFCode invokeCode(
					OperatorManager::OPERATOR_INVOKE_METHOD, (*it), bfOP );

			for( ++it ; it != endIt ; ++it )
			{
				invokeCode->append(*it );
			}

			return( invokeCode );
		}
	}

	return( StatementConstructor::newCode(
			OperatorManager::OPERATOR_INVOKE_ROUTINE,
			sep::BF(aRoutineInstance) ) );
}


BFCode Routine::invokeRoutineStatement(Routine * aRoutineInstance)
{
	if( aRoutineInstance->hasModel() )
	{
//		AVM_OS_COUT << str_header(aRoutineInstance) << std::endl;
//		AVM_OS_COUT << str_header(aRoutineInstance->getModel()) << std::endl;
		if( aRoutineInstance->isInlinableStatement() )
		{
			BFCode substCode = aRoutineInstance->inlineStatement();
			if( substCode.valid() )
			{
				return( substCode );
			}
		}

		return( StatementConstructor::newCode(
				OperatorManager::OPERATOR_INVOKE_ROUTINE,
				sep::BF(aRoutineInstance) ) );
	}

	return( invokeRoutine(aRoutineInstance) );
}


BF Routine::invokeRoutineExpression(Routine * aRoutineInstance)
{
	if( aRoutineInstance->hasModel() )
	{
		if( aRoutineInstance->isInlinableExpression() )
		{
			BF substCode = aRoutineInstance->inlineExpression();
			if( substCode.valid() )
			{
				return( substCode );
			}
		}

		return( StatementConstructor::newCode(
				OperatorManager::OPERATOR_INVOKE_ROUTINE,
				sep::BF(aRoutineInstance) ) );
	}

	return( invokeRoutine(aRoutineInstance) );
}



/**
 * Serialization
 */
void Routine::strParameters(OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator itVarParam =
			getPropertyPart().getVariableParameters().begin();
	BFVector::const_iterator endVarParam =
			getPropertyPart().getVariableParameters().end();

	out << "(";
	if( (*itVarParam).is< Variable >() )
	{
		out << "$" << (*itVarParam).to< Variable >().getRuntimeOffset()
			<< ": ";
		(*itVarParam).to< Variable >().strParameter(out);
	}
	else
	{
		out << (*itVarParam).str();
	}
	for( ++itVarParam ; itVarParam != endVarParam ; ++itVarParam )
	{
		out << ", ";
		if( (*itVarParam).is< Variable >() )
		{
			out << "$" << (*itVarParam).to< Variable >().getRuntimeOffset()
				<< ": ";
			(*itVarParam).to< Variable >().strParameter(out);
		}
		else
		{
			out << (*itVarParam).str();
		}
	}
	out << ")";
}

void Routine::strReturns(OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator itVarReturn =
			getPropertyPart().getVariableReturns().begin();
	BFVector::const_iterator endVarReturn =
			getPropertyPart().getVariableReturns().end();

	out << "(";
	if( (*itVarReturn).is< Variable >() )
	{
		out << "$" << (*itVarReturn).to< Variable >().getRuntimeOffset()
			<< ": ";
		(*itVarReturn).to< Variable >().strReturn(out);
	}
	else
	{
		out << (*itVarReturn).str();
	}
	for( ++itVarReturn ; itVarReturn != endVarReturn ; ++itVarReturn )
	{
		out << ", ";
		if( (*itVarReturn).is< Variable >() )
		{
			out << "$" << (*itVarReturn).to< Variable >().getRuntimeOffset()
				<< ": ";
			(*itVarReturn).to< Variable >().strReturn(out);
		}
		else
		{
			out << (*itVarReturn).str();
		}
	}
	out << ")";
}


void Routine::strHeader(OutStream & out) const
{
	out << getModifier().toString();

	if( getSpecifier().isDesignPrototypeStatic() )
	{
		out << getSpecifier().toString_not(
				Specifier::DESIGN_PROTOTYPE_STATIC_KIND) << "@";
	}
	else
	{
		out << getSpecifier().toString() << "routine ";
	}

	out << getNameID();

	if( getPropertyPart().hasVariableParameter() )
	{
		strParameters(out);
	}
	if( getPropertyPart().hasVariableReturn() )
	{
		out << " --> ";

		strReturns(out);
	}
}


void Routine::toStream(OutStream & out) const
{
	strHeader( out << TAB );

	out << "{";
	if( mCode.valid() )
	{
		mCode->toStreamRoutine( out << INCR_INDENT ) << DECR_INDENT_TAB;
	}
	out << "}" << EOL_FLUSH;
}



void Routine::strInvokeParameters(
		OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator it =
			getPropertyPart().getVariableParameters().begin();
	BFVector::const_iterator endIt =
			getPropertyPart().getVariableParameters().end();

	out << "(";
	AvmCode::toStream(out, *it);
	for( ++it ; it != endIt ; ++it )
	{
		out << ", ";
		AvmCode::toStream(out, *it);
	}
	out << ")";
}

void Routine::strInvokeReturns(OutStream & out, const std::string & sep) const
{
	BFVector::const_iterator it = getPropertyPart().getVariableReturns().begin();
	BFVector::const_iterator endIt = getPropertyPart().getVariableReturns().end();

	out << "(";
	AvmCode::toStream(out, *it);
	for( ++it ; it != endIt ; ++it )
	{
		out << ", ";
		AvmCode::toStream(out, *it);
	}
	out << ")";
}


void Routine::toStreamInvoke(OutStream & out, const std::string & sep) const
{
	out << TAB << getNameID() << AVM_NO_INDENT;

	if( getPropertyPart().hasVariableParameter() )
	{
		strInvokeParameters(out, sep);
	}
	else
	{
		out << "()";
	}

	if( getPropertyPart().hasVariableReturn() )
	{
		out << " --> ";
		strInvokeReturns(out, sep);
	}

	AVM_DEBUG_REF_COUNTER(out);

	out << END_INDENT << EOL_FLUSH;
}


} /* namespace sep */
