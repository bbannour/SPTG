/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmTransition.h"

#include <fml/executable/ExecutableForm.h>


namespace sep
{


/**
 * GETTER - SETTER
 * mTarget machine
 */
InstanceOfMachine * AvmTransition::getTargetMarchine() const
{
	if( getTarget().is< InstanceOfMachine >() )
	{
		return( getTarget().to_ptr< InstanceOfMachine >() );
	}
	else if( getTarget().is< RuntimeID >() )
	{
		return( getTarget().bfRID().getInstance() );
	}
	else
	{
		return( nullptr );
	}
}


std::string AvmTransition::strTargetId() const
{
	if( getTarget().is< InstanceOfMachine >() )
	{
		return( getTarget().to< InstanceOfMachine >().getNameID() );
	}
	else if( getTarget().is< RuntimeID >() )
	{
		return( getTarget().bfRID().strUniqId() );
	}
	else
	{
		return( "[-]" );
	}
}


/**
 * Control flow analysis
 * source & targets Executable<machine> for Transition
 */
ExecutableForm * AvmTransition::getTransitionSource() const
{
	return( getContainer()->is< ExecutableForm >() ?
			getContainer()->to_ptr< ExecutableForm >() : nullptr );
}


InstanceOfMachine * AvmTransition::getrecTargetMachine(const AvmCode & aCode)
{
	switch( aCode.getAvmOpCode() )
	{
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:
		case AVM_OPCODE_GOTO:
		{
			const BF & targetMachine = aCode.first();

			if( targetMachine.is< InstanceOfMachine >() )
			{
				return( targetMachine.to_ptr< InstanceOfMachine >() );
			}
			else if( targetMachine.is< RuntimeID >() )
			{
				return( targetMachine.bfRID().getInstance() );
			}

			break;
		}
		default:
		{
			InstanceOfMachine * targetMachine = nullptr;

			for( const auto & itOperand : aCode.getOperands() )
			{
				if( itOperand.is< AvmCode >() )
				{
					targetMachine =	getrecTargetMachine(
							itOperand.to< AvmCode >() );
					if( targetMachine != nullptr )
					{
						return( targetMachine );
					}
				}
			}
			break;
		}
	}

	return( nullptr );
}


void AvmTransition::getrecTargetMachine(
		ListOfInstanceOfMachine & listOfTargets, const AvmCode & aCode)
{
	switch( aCode.getAvmOpCode() )
	{
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:
		case AVM_OPCODE_GOTO:
		{
			const BF & targetMachine = aCode.first();

			if( targetMachine.is< InstanceOfMachine >() )
			{
				listOfTargets.add_unique(
						targetMachine.to_ptr< InstanceOfMachine >() );
			}
			else if( targetMachine.is< RuntimeID >() )
			{
				listOfTargets.add_unique( targetMachine.bfRID().getInstance() );
			}

			break;
		}
		default:
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( itOperand.is< AvmCode >() )
				{
					getrecTargetMachine(listOfTargets,
							itOperand.to< AvmCode >() );
				}
			}

			break;
		}
	}
}


/**
 * TEST
 * the source/target machine
 */
bool AvmTransition::isUnstableSource() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( getTransitionSource() )
			<< "Transition Source !!!"
			<< SEND_EXIT;

	return( getTransitionSource()->getSpecifier().isPseudostate() );
}


bool AvmTransition::isUnstableTarget() const
{
	if( getTarget().is< InstanceOfMachine >() )
	{
		return( getTarget().to< InstanceOfMachine >().
				getSpecifier().isPseudostate() );
	}
	else if( getTarget().is< RuntimeID >() )
	{
		return( getTarget().bfRID().getSpecifier().isPseudostate() );
	}
	else
	{
		return( false );
	}
}


/**
 * Serialization
 */
void AvmTransition::strHeader(OutStream & out) const
{
	out << getModifier().toString()
		<< Specifier::strScope( mScope )
		<< "< id:" << getOffset() << " > ";

AVM_IF_DEBUG_FLAG_AND( COMPILING ,  hasAstElement() )
	out << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	out << /* getNameID() */ getFullyQualifiedNameID();
}


void AvmTransition::toStream(OutStream & out) const
{
	// REFERENCE PROGRAM
	if( out.preferablyFQN() )
	{
		out << TAB << getNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << getModifier().toString()
		<< Specifier::strScope( mScope )
		<< "< id:" << getOffset();
	if( isAstTransition() && (not getAstTransition().isMocSimple()) )
	{
		out << ", " << getAstTransition().strMocKind(
				~ Transition::MOC_SIMPLE_KIND );
	}
	out << " > ";

AVM_IF_DEBUG_FLAG_AND( COMPILING , hasAstElement() )
	out << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	out << getNameID();
	if( hasTarget() )
	{
		out << " --> " << ( getTarget().is< ObjectElement >()
				? getTarget().to< ObjectElement >().getNameID()
				: getTarget().str() );
	}
	out << " {";
	AVM_DEBUG_REF_COUNTER(out);
	out << EOL;

AVM_IF_DEBUG_FLAG( COMPILING )
	if( hasContainer() )
	{
		out << TAB2 << "//container = "
				<< str_header( getContainer()->as_ptr< AvmProgram >() )
				<< ";" << EOL;
	}
AVM_ENDIF_DEBUG_FLAG( COMPILING )

//	out << TAB2 << "offset = " << getOffset() << ";" << EOL;


	// All program variables
	toStreamVariables(out);


	out << TAB << "moe:" << EOL;

	if( hasCode() )
	{
		out << TAB2 << "@run{" << INCR2_INDENT;

		getCode()->toStreamRoutine( out );

		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasStatementFamily() )
	{
		out << TAB2 << "opcode#family = " << strStatementFamily() << ";" << EOL;
	}

	// static class of Port/Message/Signal in communicated transition
	out << INCR_INDENT;
	toStreamStaticCom(out);
	out << DECR_INDENT;

	out << TAB << "}" << EOL << std::flush;
}


void AvmTransition::toStream(OutStream & out,
		const ListOfAvmTransition & listofTransition)
{
	for( const auto & itTransition : listofTransition )
	{
		out << TAB;
		itTransition->toStreamHeader( out );
		out << ";" << EOL;
	}
}



} /* namespace sep */
