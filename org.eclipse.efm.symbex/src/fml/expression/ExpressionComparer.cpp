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
					return( frst.to_ref< ObjectElement >().compareFQN(
							snd.to_ref< ObjectElement >() ) );
				}


				case FORM_BUILTIN_BOOLEAN_KIND:
				{
					return( frst.to_ref< Boolean >().compare(
							snd.to_ref< Boolean >() ) );
				}
				case FORM_BUILTIN_CHARACTER_KIND:
				{
					return( frst.to_ref< Character >().compare(
							snd.to_ref< Character >() ) );
				}
				case FORM_BUILTIN_INTEGER_KIND:
				{
					return( frst.to_ref< Integer >().compare(
							snd.to_ref< Integer >() ) );
				}

				case FORM_BUILTIN_RATIONAL_KIND:
				{
					return( frst.to_ref< Rational >().compare(
							snd.to_ref< Rational >() ) );
				}

				case FORM_BUILTIN_FLOAT_KIND:
				{
					return( frst.to_ref< Float >().compare(
							snd.to_ref< Float >() ) );
				}

				case FORM_BUILTIN_STRING_KIND:
				{
					return( frst.to_ref< String >().compare(
							snd.to_ref< String >() ) );
				}
				case FORM_BUILTIN_IDENTIFIER_KIND:
				{
					return( frst.to_ref< Identifier >().compare(
							snd.to_ref< Identifier >() ) );
				}
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				{
					return( frst.to_ref< QualifiedIdentifier >().compare(
							snd.to_ref< QualifiedIdentifier >() ) );
				}

				case FORM_RUNTIME_ID_KIND:
				{
					return( frst.bfRID().compare( snd.bfRID() ) );
				}

				case FORM_EXECUTION_CONFIGURATION_KIND:
				{
					return( frst.to_ptr< ExecutionConfiguration >()->compare(
							snd.to_ref< ExecutionConfiguration >() ) );
				}

				case FORM_UFI_KIND:
				{
					return( frst.to_ref< UniFormIdentifier >().compare(
							snd.to_ref< UniFormIdentifier >() ) );
				}


				case FORM_AVMCODE_KIND:
				{
					return( frst.to_ref< AvmCode >().compare(
							snd.to_ref< AvmCode >() ) );
				}

				case FORM_ARRAY_BF_KIND:
				{
					return( frst.to_ref< ArrayBF >().compare(
							snd.to_ref< ArrayBF >() ) );
				}

				default:
				{
					return( frst.is< AvmCode >() ? 1 : (
							snd.is< AvmCode >() ? -1 :
									frst.str().compare( snd.str() ) ) );
				}
			}
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
					return( frst.to_ref< Boolean >().operator==(
							snd.to_ref< Boolean >() ) );
				}
				case FORM_BUILTIN_CHARACTER_KIND:
				{
					return( frst.to_ref< Character >().operator==(
							snd.to_ref< Character >() ) );
				}
				case FORM_BUILTIN_INTEGER_KIND:
				{
					return( frst.to_ref< Integer >().operator==(
							snd.to_ref< Integer >() ) );
				}

				case FORM_BUILTIN_RATIONAL_KIND:
				{
					return( frst.to_ref< Rational >().operator==(
							snd.to_ref< Rational >() ) );
				}

				case FORM_BUILTIN_FLOAT_KIND:
				{
					return( frst.to_ref< Float >().operator==(
							snd.to_ref< Float >() ) );
				}

				case FORM_BUILTIN_STRING_KIND:
				{
					return( frst.to_ref< String >().operator==(
							snd.to_ref< String >() ) );
				}
				case FORM_BUILTIN_IDENTIFIER_KIND:
				{
					return( frst.to_ref< Identifier >().operator==(
							snd.to_ref< Identifier >() ) );
				}
				case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
				{
					return( frst.to_ref< QualifiedIdentifier >().operator==(
							snd.to_ref< QualifiedIdentifier >() ) );
				}

				case FORM_RUNTIME_ID_KIND:
				{
					return( frst.bfRID() == snd.bfRID() );
				}

				case FORM_EXECUTION_CONFIGURATION_KIND:
				{
					return( frst.to_ptr< ExecutionConfiguration >()->
								getRuntimeID().isTEQ( snd.to_ptr<
									ExecutionConfiguration >()->getRuntimeID()) &&
							frst.to_ptr< ExecutionConfiguration >()->getCode().isEQ(
								snd.to_ptr< ExecutionConfiguration >()->getCode()) );
				}

				case FORM_UFI_KIND:
				{
					return( frst.to_ref< UniFormIdentifier >().isEQ(
							snd.to_ref< UniFormIdentifier >() ) );
				}


				case FORM_AVMCODE_KIND:
				{
					return( frst.to_ref< AvmCode >().isEQ(
							snd.to_ref< AvmCode >() ) );
				}

				case FORM_ARRAY_BF_KIND:
				{
					return( frst.to_ref< ArrayBF >().isEQ(
							snd.to_ref< ArrayBF >() ) );
				}

				default:
				{
					return( frst.str() == snd.str() );
				}
			}
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

