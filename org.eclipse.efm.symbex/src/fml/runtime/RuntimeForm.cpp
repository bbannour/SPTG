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
 * Serialization
 */
void RuntimeForm::toStream(const ExecutionData * anED, OutStream & os) const
{
	if( os.preferablyFQN() )
	{
//		os << TAB << "rid#" << getRID().getRid();
		os << TAB << getRID().str();

		return;
	}

	os << TAB << "runtime";
	if( getInstanciationCount() != 1 )
	{
		os << "< count:" << getInstanciationCount() << " >";
	}
	os << " ppid#" << ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
			<< ".pid#" << getRID().getRid() << " " << getFullyQualifiedNameID()
			<< " as &" << getRID().getInstance()->getFullyQualifiedNameID();

	if( hasChild() || hasOnSchedule() || hasOnDefer() || isInputEnabled() ||
		(not isEnvironmentEnabledCommunication()) ||
		hasData() || hasRouter() || hasBuffer() )
	{
		os << " {";
	}
	else
	{
		os << ";";
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;

		return;
	}


	AVM_DEBUG_REF_COUNTER(os);
	os << EOL_FLUSH;

//	os << INCR_INDENT;
//	getRID().toStream(os);
//	os << DECR_INDENT;

AVM_IF_DEBUG_ENABLED_AND( hasChild() )

	os << incr_stream( getChildTable() );

AVM_ENDIF_DEBUG_ENABLED_AND

	if( hasOnSchedule() )
	{
		os << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnDefer() )
	{
		os << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	// the Input Enabled Flag
	// MOC Attribute for Communication
	if( isInputEnabled() )
	{
		os << TAB2 << "input_enabled = true;" << EOL_FLUSH;
	}

	if( not isEnvironmentEnabledCommunication() )
	{
		os << TAB2 << "environment_enabled = false;" << EOL_FLUSH;
	}

	if( hasData() )
	{
		os << EOL_TAB << "data:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(os);
		os << EOL;

		avm_offset_t offset = 0;
		TableOfData::iterator it = getDataTable()->begin();
		for( ; it != getDataTable()->end() ; ++it , ++offset )
		{
//			os << TAB2 << getVariables().rawAt(i)->getFullyQualifiedNameID();
			os << TAB2 << getVariables().rawAt(offset)->getNameID() << std::flush;

//AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//	(offset == getVariables().rawAt(offset)->getOffset()) )
//		<< "Invalid variable offset in data table!\n\t"
//		<< str_header( getVariables().rawAt(offset) )
//		<< SEND_EXIT;

			os << ( ((anED != NULL) &&
					anED->isAssigned(getRID(), offset))? " :=" : " =" );

			if( (*it).valid() )
			{
				os << (*it).AVM_DEBUG_REF_COUNTER();

				getVariables().rawAt(offset)->strValue(os, (*it));
			}
			else
			{
				os << " null< value >";
			}

			os << ";" << EOL_FLUSH;
		}
	}

AVM_IF_DEBUG_LEVEL_GT_MEDIUM
	if( hasRouter() )
	{
		os << EOL_TAB << "router:" << EOL_INCR_INDENT;
		getRouter().toStream(os);
		os << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

	if( hasBuffer() )
	{
		os << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(os);

		os << EOL_INCR_INDENT;
		getBufferTable().toStream(os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}


void RuntimeForm::toStreamData(const ExecutionData * anED, OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << "rid#" << getRID().getRid();
		return;
	}

	os << TAB << "runtime";
	if( getInstanciationCount() != 1 )
	{
		os << "< count:" << getInstanciationCount() << " >";
	}
	os << " ppid#" << ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
			<< ".pid#" << getRID().getRid()
			<< " \"" << getFullyQualifiedNameID() << "\" as &"
			<< getRID().getInstance()->getFullyQualifiedNameID() << " is";

	AVM_DEBUG_REF_COUNTER(os);
	os << EOL_FLUSH;

	if( hasOnSchedule() )
	{
		os << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnDefer() )
	{
		os << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasData() )
	{
		os << EOL_TAB << "data:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(os);
		os << EOL;

		avm_offset_t offset = 0;
		TableOfData::iterator it = getDataTable()->begin();
		for( ; it != getDataTable()->end() ; ++it , ++offset )
		{
//			os << TAB2 << getVariables().rawAt(i)->getFullyQualifiedNameID();
			os << TAB2 << getVariables().rawAt(offset)->getNameID() << std::flush;

//AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//	(offset == getVariables().rawAt(offset)->getOffset()) )
//		<< "Invalid variable offset in data table!\n\t"
//		<< str_header( getVariables().rawAt(offset) )
//		<< SEND_EXIT;

			os << ( ((anED != NULL) &&
						anED->isAssigned(getRID(), offset))? " :=" : " =" );

			if( (*it).valid() )
			{
				os << (*it).AVM_DEBUG_REF_COUNTER();

				getVariables().rawAt(offset)->strValue(os, (*it));
			}
			else
			{
				os << " null< value >";
			}

			os << ";" << EOL_FLUSH;
		}
	}

AVM_IF_DEBUG_LEVEL_GT_MEDIUM
	if( hasRouter() )
	{
		os << EOL_TAB << "router:" << EOL_INCR_INDENT;
		getRouter().toStream(os);
		os << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

	if( hasBuffer() )
	{
		os << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(os);

		os << EOL_INCR_INDENT;
		getBufferTable().toStream(os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}


void RuntimeForm::toFscnData(OutStream & os,
		const ExecutionData * anED, const RuntimeForm * aPreviousRF) const
{
	TableOfInstanceOfData::
	const_raw_iterator itData = getExecutable()->getBasicData().begin();
	TableOfInstanceOfData::
	const_raw_iterator endData = getExecutable()->getBasicData().end();
	for( avm_offset_t offset = 0 ; itData != endData ; ++itData , ++offset)
	{
		const BF & aValue = (itData)->getModifier().hasNatureReference() ?
				getData( (itData)->getOffset() ) : getData( (itData) );

		if( (aPreviousRF == NULL)
			|| (aValue != ( (itData)->getModifier().hasNatureReference()
							? aPreviousRF->getData((itData)->getOffset())
							: aPreviousRF->getData((itData)) ))
			/*|| ((anED != NULL) && anED->isAssigned(getRID(), i))*/ )
		{
			os << TAB << ":pid#" << getRID().getRid()<< ":";

//AVM_OS_ASSERT_FATAL_ERROR_EXIT(
//	(offset == (itData)->getOffset()) || (not (itData)->isStandardPointer()) )
//		<< "Invalid variable offset< " << offset << " > in data table of "
//		<< getRID().getFullyQualifiedNameID() << "!\n\t"
//		<< str_header( *itData ) << " = " << aValue.str() << std::endl
//		<< SEND_EXIT;

			os << (itData)->getNameID() << " =";

			if( aValue.valid() )
			{
				(itData)->strValue(os, aValue);
			}
			else
			{
				os << " null< value >";
			}

			os << ";" << EOL_FLUSH;
		}
	}
}


void RuntimeForm::toFscnBuffer(OutStream & os,
		const ExecutionData * anED, const RuntimeForm * aPreviousRF) const
{
	if( aPreviousRF != NULL )
	{
		TableOfBufferT::
		const_iterator itPrev = aPreviousRF->getBufferTable().begin();
		TableOfBufferT::
		const_iterator itPrevEnd = aPreviousRF->getBufferTable().end();
		TableOfBufferT::const_iterator it = getBufferTable().begin();
		TableOfBufferT::const_iterator itEnd = getBufferTable().end();
		for(; (it != itEnd) && (itPrev != itPrevEnd) ; ++it , ++itPrev )
		{
			(*it)->toFscn(os, getRID(), (*itPrev));
		}
	}
	else
	{
		TableOfBufferT::const_iterator it = getBufferTable().begin();
		TableOfBufferT::const_iterator itEnd = getBufferTable().end();
		for( ; it != itEnd ; ++it )
		{
			(*it)->toFscn(os, getRID(), NULL);
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
	avm_size_t offset = mDataTable->size();

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
	avm_size_t offset = mDataTable->size();

//	anInstance->setContainer( getExecutable() );
	anInstance.to_ptr< InstanceOfData >()->setOffset( offset );
	mParameters.append(anInstance);

	mDataTable.makeWritable();
	mDataTable->resize( offset + 1 );

	mDataTable->set(offset, rvalue);

//	anInstance->setRuntimeContainerRID( mRID );
}


void ParametersRuntimeForm::appendParameters(const BFList & paramsList)
{
	avm_size_t offset = mDataTable->size();
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


void ParametersRuntimeForm::appendParameters(const BFVector & paramsVector)
{
	avm_size_t offset = mDataTable->size();
	mDataTable.makeWritable();
	mDataTable->resize( offset + paramsVector.size() );

	BFVector::const_raw_iterator< InstanceOfData > itParam = paramsVector.begin();
	BFVector::const_raw_iterator< InstanceOfData > endParam = paramsVector.end();
	for( ; itParam != endParam ; ++itParam , ++offset )
	{
		(itParam)->setContainer( getExecutable() );
		mParameters.append( *itParam );

		(itParam)->setOffset( offset );
		mDataTable->set(offset, *itParam);

		(itParam)->setRuntimeContainerRID( mRID );
	}
}


/**
 * RUNTIME UPDATE
 */
void ParametersRuntimeForm::update(const BF & paramExpr)
{
	BFVector tableOfParams;
	ExpressionFactory::collectVariable(paramExpr, tableOfParams);

	avm_size_t endThisParam = mParameters.size();
	avm_size_t endParam = tableOfParams.size();
	avm_size_t offset = 0;
	for( InstanceOfData * pParam ; offset < endParam ; ++offset )
	{
		pParam = tableOfParams[offset].to_ptr< InstanceOfData >();

		if( pParam->getOffset() >= endThisParam )
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
	if( endThisParam < endParam )
	{
		mDataTable.makeWritable();
		mDataTable->resize( endParam );

		for( offset = endThisParam ; offset < endParam ; ++offset )
		{
			mDataTable->set(offset, mParameters[offset]);
		}
	}
}


/**
 * Serialization
 */
void ParametersRuntimeForm::toStream(
		const ExecutionData * anED, OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << getRID().str();
		return;
	}

	os << TAB << "runtime" << " ppid#"
			<< ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
			<< ".pid#" << getRID().getRid() << " " << getFullyQualifiedNameID()
			<< " as &" << getRID().getInstance()->getFullyQualifiedNameID() << " {";

	AVM_DEBUG_REF_COUNTER(os);
	os << EOL_FLUSH;

//	os << INCR_INDENT;
//	getRID().toStream(os);
//	os << DECR_INDENT;

AVM_IF_DEBUG_ENABLED_AND( hasChild() )

	os << incr_stream( getChildTable() );

AVM_ENDIF_DEBUG_ENABLED_AND

	if( hasOnSchedule() )
	{
		os << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}";
	}

	if( hasOnDefer() )
	{
		os << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}";
	}

	// the Input Enabled Flag
	// MOC Attribute for Communication
	if( isInputEnabled() )
	{
		os << TAB2 << "input_enabled = true;" << EOL_FLUSH;
	}

	if( not isEnvironmentEnabledCommunication() )
	{
		os << TAB2 << "environment_enabled = false;" << EOL_FLUSH;
	}


AVM_IF_DEBUG_FLAG( DATA )
	if( hasParameter() )
	{
		resetOffset();

		os << TAB << "params:" << EOL_INCR_INDENT;

//		getParameters().strHeader(os);
		getParameters().toStream(os);

		os << DECR_INDENT;
	}

	if( hasData() )
	{
		os << TAB << "data:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(os);
		os << EOL;

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
				os << TAB2 << "//*@param<" << offset << ">*/ "
						<< (itParam)->getNameID() << " =";

				if( (*itValue).valid() )
				{
					os << (*itValue).AVM_DEBUG_REF_COUNTER();
					(itParam)->strValue(os, (*itValue));
					//					os << str_indent( *itValue );
				}
				else
				{
					os << " null< value >";
				}

				os << EOL_FLUSH;
			}
		}
	}
AVM_ENDIF_DEBUG_FLAG( DATA )

AVM_IF_DEBUG_LEVEL_GT_MEDIUM
	if( hasRouter() )
	{
		os << EOL_TAB << "router:" << EOL_INCR_INDENT;
		getRouter().toStream(os);
		os << DECR_INDENT;
	}
AVM_ENDIF_DEBUG_LEVEL_GT_MEDIUM

	if( hasBuffer() )
	{
		os << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(os);

		os << EOL_INCR_INDENT;
		getBufferTable().toStream(os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}


void ParametersRuntimeForm::toStreamData(
		const ExecutionData * anED, OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << "rid#" << getRID().getRid();
		return;
	}

	os << TAB << "runtime" << " ppid#"
			<< ((getRID().getPRid() >= 0)? getRID().getPRid() : 0 )
			<< ".pid#" << getRID().getRid() << " \"" << getFullyQualifiedNameID()
			<< "\" as &" << getRID().getInstance()->getFullyQualifiedNameID() << " {";

	AVM_DEBUG_REF_COUNTER(os);
	os << EOL_FLUSH;

	if( hasOnSchedule() )
	{
		os << TAB2 << "@schedule{" << INCR2_INDENT;
		getOnSchedule()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}";
	}

	if( hasOnDefer() )
	{
		os << TAB2 << "@defer{" << INCR2_INDENT;
		getOnDefer()->toStreamRoutine( os );
		os << DECR2_INDENT_TAB2 << "}";
	}

	if( hasData() )
	{
		resetOffset();

		os << TAB << "data:";
		getDataTable()->AVM_DEBUG_REF_COUNTER(os);
		os << EOL;

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
				os << TAB2 << "//*@param<" << offset << ">*/ "
						<< (itParam)->getNameID() << " =";

				if( (*itValue).valid() )
				{
					os << (*itValue).AVM_DEBUG_REF_COUNTER();
					(itParam)->strValue(os, (*itValue));
//					os << str_indent( *itValue );
				}
				else
				{
					os << " null< value >";
				}

				os << EOL_FLUSH;
			}
		}
	}

	if( hasBuffer() )
	{
		os << EOL_TAB << "buffer:";
		getBufferTable().AVM_DEBUG_REF_COUNTER(os);

		os << EOL_INCR_INDENT;
		getBufferTable().toStream(os);
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}


void ParametersRuntimeForm::toFscnData(OutStream & os,
		const ExecutionData * anED, const RuntimeForm * aPreviousRF) const
{
AVM_IF_DEBUG_FLAG( DATA )

	resetOffset();

	TableOfInstanceOfData::const_raw_iterator itData = getParameters().begin();
	TableOfInstanceOfData::const_raw_iterator endData = getParameters().end();

//	for( ; itData != endData ; ++itData )
//	{
//		os << TAB << str_header( *itData ) << ";" << EOL;
//	}
//	itData = getParameters().begin();

	avm_size_t previousParamsSize = (aPreviousRF == NULL) ? 0 :
			aPreviousRF->getDataTable()->size();
	for( avm_offset_t offset = 0 ; itData != endData ; ++itData , ++offset)
	{
		const BF & aValue = getData( (itData) );

		if( (aPreviousRF == NULL) || (offset >= previousParamsSize) ||
			(aValue != aPreviousRF->getData( (itData) )) /*||
			((anED != NULL) && anED->isAssigned(getRID(), i))*/ )
		{
//AVM_OS_ASSERT_FATAL_ERROR_EXIT( offset == (itData)->getOffset() )
//		<< "Invalid parameter offset in parameters data table !\n\t"
//		<< str_header( *itData )
//		<< SEND_EXIT;

			os << TAB << "//*@param<" << offset << ">*/ ";

//			os << ":pid#" << getRID().getRid()<< ":" << (itData)->getNameID();
			os << (itData)->getFullyQualifiedNameID() << " =";

			if( aValue.valid() )
			{
				(itData)->strValue(os, aValue);
			}
			else
			{
				os << " null< value >";
			}

			os << ";" << EOL_FLUSH;
		}
	}

AVM_ENDIF_DEBUG_FLAG( DATA )
}


}
