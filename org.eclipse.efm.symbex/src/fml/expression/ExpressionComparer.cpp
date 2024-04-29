/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 déc. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionComparer.h"

#include <fml/common/ObjectElement.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/runtime/ExecutionConfiguration.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{

/**
 * USUAL COMPARISON
 */
int ExpressionComparer::compare(const BF & frst, const BF & snd)
{
	if( frst.raw_pointer() == snd.raw_pointer() )
	{
		return( 0 );
	}
	else if( frst.valid() && snd.valid() )
	{
		if( frst.classKind() == snd.classKind() )
		{
			switch( frst.classKind() )
			{
				case FORM_INSTANCE_BUFFER_KIND:
				case FORM_INSTANCE_CONNECTOR_KIND:
				case FORM_INSTANCE_DATA_KIND:
				case FORM_INSTANCE_MACHINE_KIND:
				case FORM_INSTANCE_PORT_KIND:

				case FORM_EXECUTABLE_MACHINE_KIND:
				case FORM_AVMTRANSITION_KIND:
				case FORM_AVMPROGRAM_KIND:
				case FORM_AVMLAMBDA_KIND:
				{
					return( frst.to< ObjectElement >().compareFQN(
							snd.to< ObjectElement >() ) );
				}


				case FORM_BUILTIN_BOOLEAN_KIND:
				{
					return( frst.to< Boolean >().compare(
							snd.to< Boolean >() ) );
				}
				case FORM_BUILTIN_CHARACTER_KIND:
				{
					return( frst.to< Character >().compare(
							snd.to< Character >() ) );
				}
				case FORM_BUILTIN_INTEGER_KIND:
				{
					return( frst.to< Integer >().compare(
							snd.to< Integer >() ) );
				}

				case FORM_BUILTIN_RATIONAL_KIND:
				{
					return( frst.to< Rational >().compare(
							snd.to< Rational >() ) );
				}

				case FORM_BUILTIN_FLOAT_KIND:
				{
					return( frst.to< Float >().compare(
							snd.to< Float >() ) );
				}

				case FORM_BUILTIN_STRING_KIND:
				{
					return( frst.to< String >().compare(
							snd.to< String >() ) );
				}
				case FORM_BUILTIN_IDENTIFIER_KIND:
				{
					return( frst.to< Identifier >().compare(
							snd.to< Identifier >() ) );
				}
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				{
					return( frst.to< QualifiedIdentifier >().compare(
							snd.to< QualifiedIdentifier >() ) );
				}

				case FORM_RUNTIME_ID_KIND:
				{
					return( frst.bfRID().compare( snd.bfRID() ) );
				}

				case FORM_EXECUTION_CONFIGURATION_KIND:
				{
					return( frst.to< ExecutionConfiguration >().compare(
							snd.to< ExecutionConfiguration >() ) );
				}

				case FORM_UFI_KIND:
				{
					return( frst.to< UniFormIdentifier >().compare(
							snd.to< UniFormIdentifier >() ) );
				}


				case FORM_AVMCODE_KIND:
				{
					return( frst.to< AvmCode >().compare(
							snd.to< AvmCode >() ) );
				}

				case FORM_ARRAY_BF_KIND:
				{
					return( frst.to< ArrayBF >().compare(
							snd.to< ArrayBF >() ) );
				}

				default:
				{
					return( frst.is< AvmCode >() ? 1 : (
							snd.is< AvmCode >() ? -1 :
									frst.str().compare( snd.str() ) ) );
				}
			}
		}
		else if( frst.is< Number >() && snd.is< Number >() )
		{
			return( Numeric::acquire( frst.to_ptr< Number >() ).compare(
					Numeric::acquire( snd.to_ptr< Number >() ) ) );
		}
		else
		{
			return( ( frst.classKind() < snd.classKind() ) ? -1 : 1 );
		}
	}
	else
	{
		return( frst.valid() ? 1 : -1 );
	}
}



/**
 * USUAL EQUALITY
 */
bool ExpressionComparer::isEQ(const BF & frst, const BF & snd)
{
	if( frst.raw_pointer() == snd.raw_pointer() )
	{
		return( true );
	}
	else if( frst.valid() && snd.valid() )
	{
		if( frst.classKind() == snd.classKind() )
		{
			switch( frst.classKind() )
			{
				case FORM_INSTANCE_BUFFER_KIND:
				case FORM_INSTANCE_CONNECTOR_KIND:
				case FORM_INSTANCE_DATA_KIND:
				case FORM_INSTANCE_MACHINE_KIND:
				case FORM_INSTANCE_PORT_KIND:

				case FORM_EXECUTABLE_MACHINE_KIND:
				case FORM_AVMTRANSITION_KIND:
				case FORM_AVMPROGRAM_KIND:
				case FORM_AVMLAMBDA_KIND:
				{
					return( frst.isTEQ( snd ) );
				}

				case FORM_BUILTIN_BOOLEAN_KIND:
				{
					return( frst.to< Boolean >().operator==(
							snd.to< Boolean >() ) );
				}
				case FORM_BUILTIN_CHARACTER_KIND:
				{
					return( frst.to< Character >().operator==(
							snd.to< Character >() ) );
				}
				case FORM_BUILTIN_INTEGER_KIND:
				{
					return( frst.to< Integer >().operator==(
							snd.to< Integer >() ) );
				}

				case FORM_BUILTIN_RATIONAL_KIND:
				{
					return( frst.to< Rational >().operator==(
							snd.to< Rational >() ) );
				}

				case FORM_BUILTIN_FLOAT_KIND:
				{
					return( frst.to< Float >().operator==(
							snd.to< Float >() ) );
				}

				case FORM_BUILTIN_STRING_KIND:
				{
					return( frst.to< String >().operator==(
							snd.to< String >() ) );
				}
				case FORM_BUILTIN_IDENTIFIER_KIND:
				{
					return( frst.to< Identifier >().operator==(
							snd.to< Identifier >() ) );
				}
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				{
					return( frst.to< QualifiedIdentifier >().operator==(
							snd.to< QualifiedIdentifier >() ) );
				}

				case FORM_RUNTIME_ID_KIND:
				{
					return( frst.bfRID() == snd.bfRID() );
				}

				case FORM_EXECUTION_CONFIGURATION_KIND:
				{
					return( frst.to< ExecutionConfiguration >().
								getRuntimeID().isTEQ( snd.to<
									ExecutionConfiguration >().getRuntimeID()) &&
							frst.to< ExecutionConfiguration >().getCode().isEQ(
								snd.to< ExecutionConfiguration >().getCode()) );
				}

				case FORM_UFI_KIND:
				{
					return( frst.to< UniFormIdentifier >().isEQ(
							snd.to< UniFormIdentifier >() ) );
				}


				case FORM_AVMCODE_KIND:
				{
					return( frst.to< AvmCode >().isEQ(
							snd.to< AvmCode >() ) );
				}

				case FORM_ARRAY_BF_KIND:
				{
					return( frst.to< ArrayBF >().isEQ(
							snd.to< ArrayBF >() ) );
				}

				default:
				{
					return( frst.str() == snd.str() );
				}
			}
		}
		else if( frst.is< Number >() && snd.is< Number >() )
		{
			return( Numeric::acquire( frst.to_ptr< Number >() ).eq(
					Numeric::acquire( snd.to_ptr< Number >() ) ) );
		}
		else
		{
			return( false );
		}
	}
	else
	{
		return( false );
	}
}


} /* namespace sep */

