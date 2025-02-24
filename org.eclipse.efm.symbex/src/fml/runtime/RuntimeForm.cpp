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

#include "RuntimeForm.h"

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/ExpressionFactory.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// RUNTIME FORM
////////////////////////////////////////////////////////////////////////////////

/**
 * GETTER - SETTER
 * mChildTable
 */
const RuntimeID & RuntimeForm::getChild(
		const std::string & aFullyQualifiedNameID) const
{
	if( hasChildTable() )
	{
		TableOfRuntimeID::const_iterator it = mChildTable->begin();
		TableOfRuntimeID::const_iterator itEnd = mChildTable->end();
		for( ; it != itEnd ; ++it)
		{
			// false?:- else only LOCATION
			if( (*it).getInstance()->fqnEquals(
					aFullyQualifiedNameID /* false */ ) )
			{
				return( *it );
			}
		}
	}

	return( RuntimeID::REF_NULL );
}


/**
 * GETTER
* Timestamp SymbeX value
 */
const BF & RuntimeForm::getTimeValue() const
{
	const InstanceOfData * timeVar = getExecutable()->getTimeVariable();

	if( timeVar != nullptr )
	{
		return( getData( timeVar ) );
	}
	else
	{
		return( BF::REF_NULL );
	}
}

const BF & RuntimeForm::getDeltaTimeValue() const
{
	const InstanceOfData * deltaTimeVar = getExecutable()->getDeltaTimeVariable();

	if( deltaTimeVar != nullptr )
	{
		return( getData( deltaTimeVar ) );
	}
	else
	{
		return( BF::REF_NULL );
	}
}

/**
 * SYNC-SETTER
 * Synchronization of Time Values
 */
void RuntimeForm::syncTimeValues(const ExecutionData & refED)
{
	makeWritableDataTable();

	const InstanceOfData * timeVar = getExecutable()->getTimeVariable();

	if( timeVar != nullptr )
	{
		assign(timeVar->getOffset(), refED.getTimeValue(getRID()));
	}

	const InstanceOfData * deltaTimeVar = getExecutable()->getDeltaTimeVariable();

	if( deltaTimeVar != nullptr )
	{
		assign(deltaTimeVar->getOffset(), refED.getDeltaTimeValue(getRID()));
	}
}


/**
 * Serialization
 */
void RuntimeForm::toStream(OutStream & out) const
{
	toStream(ExecutionData::_NULL_, out);
}


void RuntimeForm::toStream(const ExecutionData & anED, OutStream & out) const
{
	if( out.preferablyFQN() )
	{
//		out << TAB << "rid#" << getRID().getRid();
		out << TAB << getRID().str();

		return;
	}

	out << TAB << "runtime";
	if( getInstanciationCount() != 1 )
	{
		out << "< count:" << getInstanciationCount() << " >";
	}
	out << " " << RuntimeID::BASENAME_PARENT
		<< ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
		<< "." << getRID().strPid()
		<< " " << getFullyQualifiedNameID()
		<< " as &" << getRID().getInstance()->getFullyQualifiedNameID();

	if( hasChild() || hasOnSchedule() || hasOnDefer() || isInputEnabled() ||
		(not isEnvironmentEnabledCommunication()) ||
		hasData() || hasRouter() || hasBuffer() )
	{
		out << " {";
	}
	else
	{
		out << ";";
		AVM_DEBUG_REF_COUNTER(out);
		out << EOL_FLUSH;

		return;
	}


	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_FLUSH;

//	out << INCR_INDENT;
//	getRID().toStream(out);
//	out << DECR_INDENT;

AVM_IF_DEBUG_ENABLED_AND( hasChild() )

	out << incr_stream( getChildTable() );

AVM_ENDIF_DEBUG_ENABLED_AND

	if( hasOnSchedule() )
	{
		out << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnDefer() )
	{
		out << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	// the Input Enabled Flag
	// MOC Attribute for Communication
	if( isInputEnabled() )
	{
		out << TAB2 << "input_enabled = true;" << EOL_FLUSH;
	}

	if( not isEnvironmentEnabledCommunication() )
	{
		out << TAB2 << "environment_enabled = false;" << EOL_FLUSH;
	}

	if( hasData() )
	{
		out << EOL_TAB << "variable:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(out);
		out << EOL;

		avm_offset_t offset = 0;
		TableOfData::iterator it = getDataTable()->begin();
		for( ; it != getDataTable()->end() ; ++it , ++offset )
		{
//			out << TAB2 << getVariables().rawAt(i)->getFullyQualifiedNameID();
			out << TAB2 << getVariables().rawAt(offset)->getNameID() << std::flush;

//AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//	(offset == getVariables().rawAt(offset)->getOffset()) )
//		<< "Invalid variable offset in data table!\n\t"
//		<< str_header( getVariables().rawAt(offset) )
//		<< SEND_EXIT;

			out << ( (anED.isnotNull()
//					&& isAssigned(offset)) ? " :=" : " =" );
					&& anED.isAssigned(getRID(), offset))? " :=" : " =" );

			if( (*it).valid() )
			{
				out << (*it).AVM_DEBUG_REF_COUNTER();

				getVariables().rawAt(offset)->strValue(out, (*it));
			}
			else
			{
				out << "  null<value >";
			}

			out << ";" << EOL_FLUSH;
		}
	}

AVM_IF_DEBUG_ENABLED
	if( hasRouter() )
	{
		out << EOL_TAB << "router:" << EOL_INCR_INDENT;
		getRouter().toStream(out);
		out << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_ENABLED

	if( hasBuffer() )
	{
		out << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(out);

		out << EOL_INCR_INDENT;
		getBufferTable().toStream(out);
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}


void RuntimeForm::toStreamData(const ExecutionData & anED, OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << "rid" << NamedElement::NAME_ID_SEPARATOR
			<< getRID().getRid();
		return;
	}

	out << TAB << "runtime";
	if( getInstanciationCount() != 1 )
	{
		out << "< count:" << getInstanciationCount() << " >";
	}
	out << " " << RuntimeID::BASENAME_PARENT
		<< ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
		<< "." << getRID().strPid()
		<< " \"" << getFullyQualifiedNameID() << "\" as &"
		<< getRID().getInstance()->getFullyQualifiedNameID() << " is";

	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_FLUSH;

	if( hasOnSchedule() )
	{
		out << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnDefer() )
	{
		out << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasData() )
	{
		out << EOL_TAB << "variable:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(out);
		out << EOL;

		avm_offset_t offset = 0;
		TableOfData::iterator it = getDataTable()->begin();
		for( ; it != getDataTable()->end() ; ++it , ++offset )
		{
//			out << TAB2 << getVariables().rawAt(i)->getFullyQualifiedNameID();
			out << TAB2 << getVariables().rawAt(offset)->getNameID() << std::flush;

//AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//	(offset == getVariables().rawAt(offset)->getOffset()) )
//		<< "Invalid variable offset in data table!\n\t"
//		<< str_header( getVariables().rawAt(offset) )
//		<< SEND_EXIT;

			out << ( (anED.isnotNull()
//					&& isAssigned(offset)) ? " :=" : " =" );
					&& anED.isAssigned(getRID(), offset))? " :=" : " =" );

			if( (*it).valid() )
			{
				out << (*it).AVM_DEBUG_REF_COUNTER();

				getVariables().rawAt(offset)->strValue(out, (*it));
			}
			else
			{
				out << "  null<value >";
			}

			out << ";" << EOL_FLUSH;
		}
	}

AVM_IF_DEBUG_LEVEL_GT_MEDIUM
	if( hasRouter() )
	{
		out << EOL_TAB << "router:" << EOL_INCR_INDENT;
		getRouter().toStream(out);
		out << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

	if( hasBuffer() )
	{
		out << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(out);

		out << EOL_INCR_INDENT;
		getBufferTable().toStream(out);
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}


void RuntimeForm::toFscnData(OutStream & out,
		const ExecutionData & anED, const RuntimeForm & aPreviousRF) const
{
	TableOfInstanceOfData::const_raw_iterator itVar =
			refExecutable().getBasicVariables().begin();
	TableOfInstanceOfData::const_raw_iterator endVar =
			refExecutable().getBasicVariables().end();
	for( avm_offset_t offset = 0 ; itVar != endVar ; ++itVar , ++offset)
	{
		const BF & aValue = (itVar)->getModifier().hasNatureReference() ?
				getData( (itVar)->getOffset() ) : getData( (itVar) );

		if( aPreviousRF.isNullref()
			|| (aValue != ( (itVar)->getModifier().hasNatureReference()
							? aPreviousRF.getData((itVar)->getOffset())
							: aPreviousRF.getData((itVar)) )) )
//			|| ((anED != nullptr) && anED.isAssigned(getRID(), i)) )
		{
			out << TAB << ":" << getRID().strPid()<< ":";

//AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//	(offset == (itVar)->getOffset()) || (not (itVar)->isStandardPointer()) )
//		<< "Invalid variable offset< " << offset << " > in data table of "
//		<< getRID().getFullyQualifiedNameID() << "!\n\t"
//		<< str_header( *itVar ) << " = " << aValue.str() << std::endl
//		<< SEND_EXIT;

			out << (itVar)->getNameID() << " =";

			if( aValue.valid() )
			{
				(itVar)->strValue(out, aValue);
			}
			else
			{
				out << "  null<value >";
			}

			out << ";" << EOL_FLUSH;
		}
	}
}


void RuntimeForm::toFscnBuffer(OutStream & out,
		const ExecutionData & anED, const RuntimeForm & aPreviousRF) const
{
	if( aPreviousRF.isnotNullref() )
	{
		TableOfBufferT::
		const_iterator itPrev = aPreviousRF.getBufferTable().begin();
		TableOfBufferT::
		const_iterator itPrevEnd = aPreviousRF.getBufferTable().end();
		TableOfBufferT::const_iterator it = getBufferTable().begin();
		TableOfBufferT::const_iterator itEnd = getBufferTable().end();
		for(; (it != itEnd) && (itPrev != itPrevEnd) ; ++it , ++itPrev )
		{
			(*it)->toFscn(out, getRID(), (*itPrev));
		}
	}
	else
	{
		for( const auto & itBuffer : getBufferTable() )
		{
			itBuffer->toFscn(out, getRID(), nullptr);
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
// PARAMETERS RUNTIME FORM
////////////////////////////////////////////////////////////////////////////////

/**
 * GETTER - SETTER
 * mParameters
 */
const BF & ParametersRuntimeForm::saveParameter(InstanceOfData * anInstance)
{
	std::size_t offset = mDataTable->size();

	anInstance->setContainer( getExecutable() );
	anInstance->setOffset( offset );
	const BF & bfInbstance = mParameters.save(anInstance);

	mDataTable.makeWritable();
	mDataTable->resize( offset + 1 );

	mDataTable->set(offset, bfInbstance);

	anInstance->setRuntimeContainerRID( mRID );

	return( bfInbstance );
}

void ParametersRuntimeForm::appendParameter(
		const BF & anInstance, const BF & rvalue )
{
	std::size_t offset = mDataTable->size();

	anInstance.to_ptr< InstanceOfData >()->setOffset( offset );
	mParameters.append(anInstance);

	mDataTable.makeWritable();
	mDataTable->resize( offset + 1 );

	mDataTable->set(offset, rvalue);
}

void ParametersRuntimeForm::appendParameters(const BFList & paramsList)
{
	std::size_t offset = mDataTable->size();
	mDataTable.makeWritable();
	mDataTable->resize( offset + paramsList.size() );

	BFList::const_iterator itParam = paramsList.begin();
	BFList::const_iterator endParam = paramsList.end();
	for( InstanceOfData * pParam; itParam != endParam ; ++itParam , ++offset )
	{
		pParam = (*itParam).to_ptr< InstanceOfData >();

		pParam->setContainer( getExecutable() );
		mParameters.append( *itParam );

		pParam->setOffset( offset );
		mDataTable->set(offset, *itParam);

		pParam->setRuntimeContainerRID( mRID );
	}
}

void ParametersRuntimeForm::appendParameters(
		const InstanceOfData::Table & paramsVector)
{
	std::size_t offset = mDataTable->size();
	mDataTable.makeWritable();
	mDataTable->resize( offset + paramsVector.size() );

	InstanceOfData::Table::const_raw_iterator itParam = paramsVector.begin();
	InstanceOfData::Table::const_raw_iterator endParam = paramsVector.end();
	for( ; itParam != endParam ; ++itParam , ++offset )
	{
		(itParam)->setContainer( getExecutable() );
		mParameters.append( *itParam );

		(itParam)->setOffset( offset );
		mDataTable->set(offset, *itParam);

		(itParam)->setRuntimeContainerRID( mRID );
	}
}

void ParametersRuntimeForm::appendConstParameters(
		const InstanceOfData::Table & paramsVector)
{
	std::size_t offset = mDataTable->size();
	mDataTable.makeWritable();
	mDataTable->resize( offset + paramsVector.size() );

	InstanceOfData::Table::const_raw_iterator itParam = paramsVector.begin();
	InstanceOfData::Table::const_raw_iterator endParam = paramsVector.end();
	for( ; itParam != endParam ; ++itParam , ++offset )
	{
		(itParam)->setContainer( getExecutable() );
		mParameters.append( *itParam );

		(itParam)->setOffset( offset );
		mDataTable->set(offset,
				(itParam)->hasValue() ? (itParam)->getValue() : *itParam);

		(itParam)->setRuntimeContainerRID( mRID );
	}
}


/**
 * RUNTIME UPDATE
 */
void ParametersRuntimeForm::update(const BF & paramExpr)
{
	InstanceOfData::Table tableOfParams;
	ExpressionFactory::collectVariable(paramExpr, tableOfParams);

	std::size_t actualParametersSize = mParameters.size();
	std::size_t endParam = tableOfParams.size();
	std::size_t offset = 0;
	for( InstanceOfData * pParam ; offset < endParam ; ++offset )
	{
		pParam = tableOfParams[offset].to_ptr< InstanceOfData >();

		if( pParam->getOffset() >= actualParametersSize )
		{
			mParameters.append( tableOfParams[offset] );
		}
		else if( mParameters[pParam->getOffset()] != pParam )
		{
			if( mParameters.contains( tableOfParams[offset] ) )
			{
AVM_IF_DEBUG_FLAG( COMPUTING )

	AVM_OS_WARNING_ALERT
			<< "Unexpected parameter << "
			<< str_header( tableOfParams[offset] ) << " >> in <<\n"
			<< str_header( mParameters ) << " >> !!!"
			<< SEND_ALERT;

AVM_ENDIF_DEBUG_FLAG( COMPUTING )
			}
			else
			{
				mParameters.append( tableOfParams[offset] );
			}
		}
	}

	endParam = mParameters.size();
	if( actualParametersSize < endParam )
	{
		mDataTable.makeWritable();
		mDataTable->resize( endParam );

		for( offset = actualParametersSize ; offset < endParam ; ++offset )
		{
			mDataTable->set(offset, mParameters[offset]);
		}
	}
}

void ParametersRuntimeForm::update(TableOfInstanceOfData potentialNewParameters)
{

	std::size_t actualParametersSize = mParameters.size();
	std::size_t newParametersSize = potentialNewParameters.size();
	std::size_t offset = 0;
	for( InstanceOfData * pParam ; offset < newParametersSize ; ++offset )
	{
		pParam = potentialNewParameters[offset].to_ptr< InstanceOfData >();

		if( pParam->getOffset() >= actualParametersSize )
		{
			mParameters.append( potentialNewParameters[offset] );
		}
		else if( mParameters[pParam->getOffset()] != pParam )
		{
			if( mParameters.contains( potentialNewParameters[offset] ) )
			{
AVM_IF_DEBUG_FLAG( COMPUTING )

	AVM_OS_WARNING_ALERT
			<< "Unexpected parameter << "
			<< str_header( potentialNewParameters[offset] ) << " >> in <<\n"
			<< str_header( mParameters ) << " >> !!!"
			<< SEND_ALERT;

AVM_ENDIF_DEBUG_FLAG( COMPUTING )
			}
			else
			{
				mParameters.append( potentialNewParameters[offset] );
			}
		}
	}

	newParametersSize = mParameters.size();
	if( actualParametersSize < newParametersSize )
	{
		mDataTable.makeWritable();
		mDataTable->resize( newParametersSize );

		for( offset = actualParametersSize ; offset < newParametersSize ; ++offset )
		{
			mDataTable->set(offset, mParameters[offset]);
		}
	}
}


/**
 * Serialization
 */
void ParametersRuntimeForm::toStream(OutStream & out) const
{
	toStream(ExecutionData::_NULL_, out);
}

void ParametersRuntimeForm::toStream(
		const ExecutionData & anED, OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getRID().str();
		return;
	}

	out << TAB << "runtime" << " " << RuntimeID::BASENAME_PARENT
			<< ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
			<< "." << getRID().strPid()
			<< " " << getFullyQualifiedNameID()
			<< " as &" << getRID().getInstance()->getFullyQualifiedNameID() << " {";

	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_FLUSH;

//	out << INCR_INDENT;
//	getRID().toStream(out);
//	out << DECR_INDENT;

AVM_IF_DEBUG_ENABLED_AND( hasChild() )

	out << incr_stream( getChildTable() );

AVM_ENDIF_DEBUG_ENABLED_AND

	if( hasOnSchedule() )
	{
		out << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}";
	}

	if( hasOnDefer() )
	{
		out << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}";
	}

	// the Input Enabled Flag
	// MOC Attribute for Communication
	if( isInputEnabled() )
	{
		out << TAB2 << "input_enabled = true;" << EOL_FLUSH;
	}

	if( not isEnvironmentEnabledCommunication() )
	{
		out << TAB2 << "environment_enabled = false;" << EOL_FLUSH;
	}


AVM_IF_DEBUG_FLAG( DATA )
	if( hasParameter() )
	{
		resetOffset();

		out << TAB << "params:" << EOL_INCR_INDENT;

//		getParameters().strHeader(out);
		getParameters().toStream(out);

		out << DECR_INDENT;
	}

	if( hasData() )
	{
		out << TAB << "variable:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(out);
		out << EOL;

		TableOfInstanceOfData::const_raw_iterator itParam = getParameters().begin();
		TableOfData::const_iterator itValue = getDataTable()->begin();
		TableOfData::const_iterator endValue = getDataTable()->end();
		avm_offset_t offset = 0;
		for( ; itValue != endValue ; ++itValue , ++offset , ++itParam )
		{
//AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset == (itParam)->getOffset() )
//		<< "Invalid parameter offset in parameters data table !\n\t"
//		<< str_header( *itParam )
//		<< SEND_EXIT;

			//if( (*itValue) != (itParam) )
			{
				out << TAB2 << "//*@param<" << offset << ">*/ "
						<< (itParam)->getNameID() << " =";

				if( (*itValue).valid() )
				{
					out << (*itValue).AVM_DEBUG_REF_COUNTER();
					(itParam)->strValue(out, (*itValue));
					//					out << str_indent( *itValue );
				}
				else
				{
					out << "  null<value >";
				}

				out << EOL_FLUSH;
			}
		}
	}
AVM_ENDIF_DEBUG_FLAG( DATA )

AVM_IF_DEBUG_LEVEL_GT_MEDIUM
	if( hasRouter() )
	{
		out << EOL_TAB << "router:" << EOL_INCR_INDENT;
		getRouter().toStream(out);
		out << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

	if( hasBuffer() )
	{
		out << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(out);

		out << EOL_INCR_INDENT;
		getBufferTable().toStream(out);
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}


void ParametersRuntimeForm::toStreamData(
		const ExecutionData & anED, OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << "rid#" << getRID().getRid();
		return;
	}

	out << TAB << "runtime" << " " << RuntimeID::BASENAME_PARENT
		<< ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
		<< "." << getRID().strPid()
		<< " \"" << getFullyQualifiedNameID()
		<< "\" as &" << getRID().getInstance()->getFullyQualifiedNameID()
		<< " {";

	AVM_DEBUG_REF_COUNTER(out);
	out << EOL_FLUSH;

	if( hasOnSchedule() )
	{
		out << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}";
	}

	if( hasOnDefer() )
	{
		out << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}";
	}

	if( hasData() )
	{
		resetOffset();

		out << TAB << "variable:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(out);
		out << EOL;

		TableOfInstanceOfData::const_raw_iterator itParam = getParameters().begin();
		TableOfData::const_iterator itValue = getDataTable()->begin();
		TableOfData::const_iterator endValue = getDataTable()->end();
		avm_offset_t offset = 0;
		for( ; itValue != endValue ; ++itValue , ++offset , ++itParam )
		{
//AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset == (itParam)->getOffset() )
//		<< "Invalid parameter offset in parameters data table !\n\t"
//		<< str_header( *itParam )
//		<< SEND_EXIT;

//			if( (*itValue) != (itParam) )
			{
				out << TAB2 << "//*@param<" << offset << ">*/ "
					<< (itParam)->getNameID() << " =";

				if( (*itValue).valid() )
				{
					out << (*itValue).AVM_DEBUG_REF_COUNTER();
					(itParam)->strValue(out, (*itValue));
//					out << str_indent( *itValue );
				}
				else
				{
					out << " null<value >";
				}

				out << EOL_FLUSH;
			}
		}
	}

	if( hasBuffer() )
	{
		out << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(out);

		out << EOL_INCR_INDENT;
		getBufferTable().toStream(out);
		out << DECR_INDENT;
	}

	out << TAB << "}" << EOL_FLUSH;
}


void ParametersRuntimeForm::toFscnData(OutStream & out,
		const ExecutionData & anED, const RuntimeForm & aPreviousRF) const
{
AVM_IF_DEBUG_FLAG( DATA )

	resetOffset();

	TableOfInstanceOfData::const_raw_iterator itParam = getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endParam = getParameters().end();

//	for( ; itParam != endParam ; ++itParam )
//	{
//		out << TAB << str_header( *itParam ) << ";" << EOL;
//	}
//	itParam = getParameters().begin();

	std::size_t previousParamsSize = aPreviousRF.isNullref() ? 0 :
			aPreviousRF.getDataTable()->size();
	for( avm_offset_t offset = 0 ; itParam != endParam ; ++itParam , ++offset)
	{
		const BF & aValue = getData( (itParam) );

		if( aPreviousRF.isNullref() || (offset >= previousParamsSize)
			|| (aValue != aPreviousRF.getData( (itParam) )) )
//			|| (anED.isNotNull() && anED.isAssigned(getRID(), i)) )
		{
//AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset == (itParam)->getOffset() )
//		<< "Invalid parameter offset in parameters data table !\n\t"
//		<< str_header( *itParam )
//		<< SEND_EXIT;

			out << TAB << "//*@param<" << offset << ">*/ ";

//			out << ":" << getRID().strPid() << ":" << (itParam)->getNameID();
			out << (itParam)->getFullyQualifiedNameID() << " =";

			if( aValue.valid() )
			{
				(itParam)->strValue(out, aValue);
			}
			else
			{
				out << "  null<value >";
			}

			out << ";" << EOL_FLUSH;
		}
	}

AVM_ENDIF_DEBUG_FLAG( DATA )
}


}
