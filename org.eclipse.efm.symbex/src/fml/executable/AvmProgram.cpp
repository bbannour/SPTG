/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "AvmProgram.h"

#include <fml/executable/ExecutableForm.h>



namespace sep
{


std::string AvmProgram::ANONYM_UFI = "prog#anonym";



/**
 * SETTER
 * updateFullyQualifiedNameID()
 */
void AvmProgram::updateFullyQualifiedNameID()
{
	std::string schema = Specifier::strScope( mScope );

	if( hasAstElement() )
	{
		std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();
		std::string aNameID  =
				NamedElement::extractNameID( aFullyQualifiedNameID );

		setFullyQualifiedNameID(schema + aFullyQualifiedNameID.substr(
						aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR)) );

		setNameID( aNameID );
	}
	else if( hasFullyQualifiedNameID() )
	{
		if( not hasNameID() )
		{
			setNameID( NamedElement::extractNameID(
					getFullyQualifiedNameID() ) );
		}
	}
	else if( hasNameID() )
	{
		if( hasContainer() )
		{
			std::string aFullyQualifiedNameID =
					getContainer()->getFullyQualifiedNameID();

			std::string::size_type pos =
					aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
			setFullyQualifiedNameID( (pos != std::string::npos) ?
					schema + aFullyQualifiedNameID.substr() : getNameID() );
		}
		else
		{
			setFullyQualifiedNameID( getNameID() );
		}
	}
	else
	{
		setAllNameID( ANONYM_UFI , schema + "#anonym" );
	}
}



/**
 * GETTER
 * any SYMBOL filtering by an optional type specifier family
 */
const BF & AvmProgram::getSymbol(
		const std::string & aFullyQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	{
		const BF & foundSymbol = BaseAvmProgram::
				getSymbol(aFullyQualifiedNameID, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol =
				getConstData().getByFQNameID(aFullyQualifiedNameID);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol = getSymbolData(aFullyQualifiedNameID);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	return( BF::REF_NULL );
}


const BF & AvmProgram::getSymbolByQualifiedNameID(
		const std::string & aQualifiedNameID,
		avm_type_specifier_kind_t typeFamily) const
{
	{
		const BF & foundSymbol =
				BaseAvmProgram::getSymbolByQualifiedNameID(
						aQualifiedNameID, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol =
				getConstData().getByQualifiedNameID(aQualifiedNameID);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol =
				getSymbolDataByQualifiedNameID(aQualifiedNameID);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	return( BF::REF_NULL );
}


const BF & AvmProgram::getSymbolByNameID(
		const std::string & id, avm_type_specifier_kind_t typeFamily) const
{
	{
		const BF & foundSymbol =
				BaseAvmProgram::getSymbolByNameID(id, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol = getConstData().getByNameID(id);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol = getSymbolDataByNameID(id);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	return( BF::REF_NULL );
}


const BF & AvmProgram::getymbolByAstElement(const ObjectElement * astElement,
		avm_type_specifier_kind_t typeFamily) const
{
	{
		const BF & foundSymbol =
				BaseAvmProgram::getSymbolByAstElement(astElement, typeFamily);
		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol = getConstData().getByAstElement(astElement);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	{
		const BF & foundSymbol = getSymbolDataByAstElement(astElement);

		if( foundSymbol.valid() )
		{
			return( foundSymbol );
		}
	}

	return( BF::REF_NULL );
}


/**
 * Serialization
 */
void AvmProgram::strHeader(OutStream & out) const
{
	out << getModifier().toString()
		<< Specifier::strScope( mScope )
		<< "< id:" << getOffset() << " > ";

AVM_IF_DEBUG_FLAG_AND( COMPILING ,  hasAstElement() )
	out << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	out << /*(isScopeTransition() ? getNameID() :*/ getFullyQualifiedNameID();
}


void AvmProgram::toStreamData(OutStream & out) const
{
	TableOfInstanceOfData::const_raw_iterator itData  = getData().begin();
	TableOfInstanceOfData::const_raw_iterator endData = getData().end();

	if( hasParam() )
	{
		out << TAB << "parameter:" << EOL_INCR_INDENT;
		avm_size_t param = getParamCount();
		for( ; param > 0 ; --param , ++itData )
		{
			(itData)->toStream(out);
		}
		out << DECR_INDENT;
	}

	if( hasReturn() )
	{
		out << TAB << "returns:" << EOL_INCR_INDENT;
		for( avm_size_t ret = getReturnCount() ; ret > 0 ; --ret , ++itData )
		{
			(itData)->toStream(out);
		}
		out << DECR_INDENT;
	}

	if( hasTypeSpecifier() )
	{
		out << TAB << "type:" << EOL_INCR_INDENT;

		getTypeSpecifier().toStream(out);

		out << DECR_INDENT;
	}


	if( (hasData() && (getData().size() > getParamReturnCount()))
			|| hasConstData() || hasTypeSpecifier() )
	{
		out << TAB << "variable:" << EOL_INCR_INDENT;

		if( hasConstData() )
		{
			getConstData().toStream(out);

			out << EOL;
		}

		for( ; itData != endData ; ++itData )
		{
			(itData)->toStream(out);
		}

		out << DECR_INDENT;

AVM_IF_DEBUG_FLAG( DATA )
		if( mAllData != &mData )
		{
			out << TAB << "variable#all:" << EOL_INCR_INDENT;
			itData = getAllData().begin();
			endData = getAllData().end();
			for( ; itData != endData ; ++itData )
			{
				(itData)->toStream(out);
			}
			out << DECR_INDENT;

		}
		if( mBasicData != &mData )
		{
			out << TAB << "variable#basic:" << EOL_INCR_INDENT;
			itData = getBasicData().begin();
			endData = getBasicData().end();

AVM_IF_DEBUG_LEVEL_GTE_HIGH
			for( ; itData != endData ; ++itData )
			{
				(itData)->toStream(out);
			}
AVM_ELSE
			for( ; itData != endData ; ++itData )
			{
				out << TAB2 << str_header( *itData )
						<< ";" << EOL;
			}
AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH

			out << DECR_INDENT;
		}
AVM_ENDIF_DEBUG_FLAG( DATA )
	}

	if( getDataAlias().nonempty() )
	{
		out << TAB << "alias:" << EOL_INCR_INDENT;

		TableOfInstanceOfData::const_raw_iterator itAlias = getDataAlias().begin();
		TableOfInstanceOfData::const_raw_iterator endAlias = getDataAlias().end();
		for( ; itAlias != endAlias ; ++itAlias )
		{
			(itAlias)->toStream(out);
		}
		out << DECR_INDENT;
	}
}


void AvmProgram::toStreamStaticCom(OutStream & out) const
{
//AVM_IF_DEBUG_FLAG( COMMUNICATION )
	if ( hasCommunicationCode() )
	{
		out << TAB << "communication"
				<< (isMutableCommunication() ? "" : "<final>");
		BaseCompiledForm::toStreamStaticCom(out, getCommunicationCode());
	}

	if ( hasInternalCommunicationCode() )
	{
		out << TAB << "com#internal";
		BaseCompiledForm::toStreamStaticCom(out, getInternalCommunicationCode());
	}


	if ( hasInputCom() )
	{
		out << TAB << "com#input{" << EOL;
		BaseCompiledForm::toStreamStaticCom(out, getInputCom());
		out << TAB << "}" << EOL;
	}

	if ( hasOutputCom() )
	{
		out << TAB << "com#output{" << EOL;
		BaseCompiledForm::toStreamStaticCom(out, getOutputCom());
		out << TAB << "}" << EOL;
	}


	if ( hasInputEnabledBuffer() )
	{
		out << TAB << "buffer#input_enabled{" << EOL;
		BaseCompiledForm::toStreamStaticCom(out, getInputEnabledBuffer());
		out << TAB << "}" << EOL;
	}

	if ( hasInputEnabledCom() )
	{
		out << TAB << "com#input_enabled{" << EOL;
		BaseCompiledForm::toStreamStaticCom(out, getInputEnabledCom());
		out << TAB << "}" << EOL;
	}

	if ( hasInputEnabledSave() )
	{
		out << TAB << "com#input_enabled#save{" << EOL;
		BaseCompiledForm::toStreamStaticCom(out, getInputEnabledSave());
		out << TAB << "}" << EOL;
	}


	if ( hasEnvironmentCom() )
	{
		out << TAB << "com#env";
		BaseCompiledForm::toStreamStaticCom(out, getEnvironmentCom());
	}

	if ( hasEnvironmentInputCom() )
	{
		out << TAB << "com#input#env";
		BaseCompiledForm::toStreamStaticCom(out, getEnvironmentInputCom());
	}

	if ( hasEnvironmentOutputCom() )
	{
		out << TAB << "com#output#env";
		BaseCompiledForm::toStreamStaticCom(out, getEnvironmentOutputCom());
	}
//AVM_ENDIF_DEBUG_FLAG( COMMUNICATION )
}


void AvmProgram::toStream(OutStream & out) const
{
	// REFERENCE PROGRAM
	if( out.preferablyFQN() )
	{
		out << TAB << ( isScopeTransition() ?
				getNameID() : getFullyQualifiedNameID() );

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << getModifier().toString()
		<< Specifier::strScope( mScope )
		<< "< id:" << getOffset() << " > ";

AVM_IF_DEBUG_FLAG_AND( COMPILING , hasAstElement() )
	out << "&" << getAstFullyQualifiedNameID() << " ";
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )

	out << ( isScopeTransition() ?
			getNameID() : getFullyQualifiedNameID() ) << " {";
	AVM_DEBUG_REF_COUNTER(out);
	out << EOL;

AVM_IF_DEBUG_FLAG( COMPILING )
	if( hasContainer() )
	{
		out << TAB2 << "//container = "
				<< str_header( getContainer()->as< AvmProgram >() )
				<< ";" << EOL;
	}
AVM_ENDIF_DEBUG_FLAG( COMPILING )

//	out << TAB2 << "offset = " << getOffset() << ";" << EOL;


	// Any program data
	toStreamData(out);


	out << TAB << "moe:" << EOL;

	if( hasCode() )
	{
		out << TAB2 << "@run{" << INCR2_INDENT;

		getCode()->toStreamRoutine( out );

		out<< DECR2_INDENT_TAB2 << " }" << EOL;
	}

	if( hasStatementFamily() )
	{
		out << TAB << "opcode#family = " << strStatementFamily() << ";" << EOL;
	}

	// static class of Port/Message/Signal in communicated transition
	out << INCR_INDENT;
	toStreamStaticCom(out);
	out << DECR_INDENT;

	out << TAB << "}" << EOL << std::flush;
}


}
