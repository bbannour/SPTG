/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 oct. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmLambda.h"

#include <fml/common/SpecifierElement.h>

#include <fml/executable/AvmProgram.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


std::string AvmLambda::ANONYM_UFI = "lambda#anonym";

std::string AvmLambda::APP_UFI = "lambda::app";

std::string AvmLambda::FUN_UFI = "lambda::fun";

std::string AvmLambda::LET_UFI = "lambda::let";



/**
 * SETTER
 * updateFullyQualifiedNameID()
 */
void AvmLambda::updateFullyQualifiedNameID()
{
	switch( mLambdaNature )
	{
		case AVM_LAMBDA_APP_NATURE:
		{
			setFullyQualifiedNameID( APP_UFI );
			break;
		}

		case AVM_LAMBDA_LET_NATURE:
		{
			setFullyQualifiedNameID( LET_UFI );
			break;
		}

		case AVM_LAMBDA_FUN_NATURE:
		default:
		{
			if( hasAstElement() )
			{
				std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();
				setFullyQualifiedNameID( "program" +
					aFullyQualifiedNameID.substr(
						aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR)) );
			}
			else
			{
				setAllNameID( ANONYM_UFI , "lambda#anonym" );
			}

			break;
		}
	}
}


/**
 * Serialization
 */
void AvmLambda::toStream(OutStream & os) const
{
	switch( mLambdaNature )
	{
		case AVM_LAMBDA_APP_NATURE:
		{
			toStreamApp(os);

			break;
		}

		case AVM_LAMBDA_LET_NATURE:
		{
			toStreamLet(os);

			break;
		}

		case AVM_LAMBDA_FUN_NATURE:
		default:
		{
			toStreamLambda(os);

			break;
		}
	}
}


void AvmLambda::toStreamApp(OutStream & os) const
{
	//os << TAB << "apply ( ";
	os << TAB << "${ app " << AVM_STR_INDENT;
	toStreamLambda(os);
	os << END_INDENT;
	//os << " )( ";

	TableOfInstanceOfData::const_raw_iterator itVar = getVariables().begin();
	TableOfInstanceOfData::const_raw_iterator endVar = getVariables().end();
	for( ; itVar != endVar ; ++itVar )
	{
		if( (itVar)->hasValue() )
		{
			os << TAB << " ${ := " << (itVar)->str() << " "
					<< (itVar)->strValue() << " }";
		}
	}
	//os << " )" << EOL;
	os << " }" << EOL << std::flush;
}


void AvmLambda::toStreamLambda(OutStream & os) const
{
	TableOfInstanceOfData::const_raw_iterator itVar = getVariables().begin();
	TableOfInstanceOfData::const_raw_iterator endVar = getVariables().end();

	//os << TAB << "lambda ";
	os << TAB << "${ lambda ";

	for( ; itVar != endVar ; ++itVar )
	{
		os << (itVar)->str() << " ";
	}
	os << std::flush;

	//os << "->";

	os << str_indent( getExpression() );

	//os << EOL;
	os << " }" << EOL_FLUSH;
}


void AvmLambda::toStreamLet(OutStream & os) const
{
	TableOfInstanceOfData::const_raw_iterator itVar = getVariables().begin();
	TableOfInstanceOfData::const_raw_iterator endVar = getVariables().end();

	if( os.INDENT.TABS.empty() )
	{
		//os << "let ";
		os << "${ let ";
		for( ; itVar != endVar ; ++itVar )
		{
			if( (itVar)->hasValue() )
			{
				os << "${ "
						<< OperatorManager::OPERATOR_ASSIGN->strOp() << " "
						<< (itVar)->str() << " " << (itVar)->strValue()
						<< " } ";
			}
			else
			{
				os << (itVar)->str() << " ";
			}
		}
		os << std::flush;

		//os << "in";

		os << str_indent( getExpression() ) << " }";
	}
	else
	{
		//os << TAB << "let " << EOL;
		os << TAB << "${ let " << EOL;

		for( ; itVar != endVar ; ++itVar )
		{
			if( (itVar)->hasValue() )
			{
				os << TAB2 << "${ "
					<< OperatorManager::OPERATOR_ASSIGN->strOp() << " "
					<< (itVar)->str() << " " << (itVar)->strValue()
					<< " }";
			}
			else
			{
				os << TAB2 << (itVar)->str();
			}

			os << EOL;
		}
		os << std::flush;

		//os << TAB << "in" << EOL;

		os << incr_stream( getExpression() ) << TAB << "}" << EOL;
	}

	os << std::flush;
}




/*
 * Convert to AvmProgram
 */
BF AvmLambda::convertToProgram(const std::string & id)
{
	AvmProgram * aProgram = new AvmProgram(Specifier::SCOPE_ROUTINE_KIND,
			getContainer()->as_ptr< AvmProgram >(), getAstElement(), getVariablesSize());

	aProgram->setAllNameID( aProgram->getFullyQualifiedNameID() + "." + id , id );
	aProgram->setParamOffsetCount(0, getVariablesSize());

	std::size_t endOffset = getVariables().size();
	for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
	{
		aProgram->setVariable(offset, getVariables().get(offset));
	}

	aProgram->setCode( getExpression().bfCode() );

	return( BF(aProgram) );
}



}
