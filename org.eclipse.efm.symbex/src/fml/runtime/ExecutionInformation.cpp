/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 oct. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutionInformation.h"

#include <fam/api/AbstractProcessorUnit.h>

#include <fam/coverage/FormulaCoverageFilter.h>

#include <fam/hitorjump/AvmHitOrJumpProcessor.h>

#include <fam/testing/OfflineTestProcessor.h>

#include <fml/trace/TracePoint.h>


namespace sep
{


/**
 * GETTER - SETTER
 * mProcessorRegisterTool
 */
bool GenericInfoData::isInfo(const AbstractProcessorUnit & aProcessor) const
{
	return( isInfo(aProcessor.REGISTER_TOOL()) || /*TODO &&*/
			isID(aProcessor.getParameterWObject()) );
}

bool GenericInfoData::isInfo(
		const AbstractProcessorUnit & aProcessor, const BF & anID) const
{
	return( isInfo(aProcessor.REGISTER_TOOL()) && isID(anID) );
}


/**
 * Serialization
 */

std::string GenericInfoData::strUID() const
{
	return( mID.valid()
			? ( mID.isBuiltinString() ? mID.toBuiltinString() : mID.str() )
			: "" );
}

void GenericInfoData::toStream(OutStream & out) const
{
	out << TAB << "info ";

	if ( hasID() )
	{
		out << "\"" << getID().str() << "\" {" << EOL;
	}

	if ( hasData() )
	{
		if( getData().is< ExecutionContextHeader >() )
		{
			ExecutionContextHeader * ech =
					getData().to_ptr< ExecutionContextHeader >();

			out << TAB2 << "EC< "
				<< "Id:" << ech->getIdNumber()   << " , "
				<< "Ev:" << ech->getEvalNumber() << " , "
				<<  "H:" << ech->getHeight()     << " , "
				<<  "W:" << ech->getWidth()      << " >;" << EOL;
		}
		else if( getData().isBuiltinString() )
		{
			out << TAB2 << getData().toBuiltinString() << EOL;
		}
		else
		{
			out << TAB2 << getData().str() << EOL;
		}
	}

	out << TAB << "}" << EOL_FLUSH;
}


void GenericInfoData::toFscn(OutStream & out) const
{
	out << TAB << "<ID:";
	if ( hasID() )
	{
		out  << "\"";
		if( getID().is< AbstractProcessorUnit >() )
		{
			AbstractProcessorUnit * anAPU =
					getID().to_ptr< AbstractProcessorUnit >();
			out << anAPU->getParameterWObject()->getFullyQualifiedNameID();
		}
		else
		{
			out << getID().str();
		}
		out << "\"";
	}
	else
	{
		out << "\"NULL\"";
	}

	if ( hasData() )
	{
		out  << ",";

		if( getData().is< ExecutionContextHeader >() )
		{
			ExecutionContextHeader * ech =
					getData().to_ptr< ExecutionContextHeader >();

			out << "Id=\"" << ech->getIdNumber()   << "\", "
				<< "Ev=\"" << ech->getEvalNumber() << "\", "
				<<  "H=\"" << ech->getHeight()     << "\", "
				<<  "W=\"" << ech->getWidth()      << "\"";
		}
		else if( getData().is< String >() )
		{
			out << "kind=\"" << getData().to_ptr< String >()->getValue()
					<< "\"";
		}
		else if( getData().is< AvmCode >() )
		{
			out << "avmcode= \"" << getData().str() << "\"";
		}
		else if( getData().isInteger() )
		{
			out << "value=\"" << getData().toInteger() << "\"";
		}
		else if( getData().is< TracePoint >() )
		{
			out << "hoj=\"" << getData().to_ptr< TracePoint >()->str() << "\"";
		}
		else
		{
			out << "kind=\"" << getData()._str() <<  "\"";
		}
	}

	out << ">" << EOL_FLUSH;
}



/**
 * DESTRUCTOR
 */
ExecutionInformation::~ExecutionInformation()
{
	sep::destroyElement( mFormulaCoverageFilterInfo );

	sep::destroyElement( mHitOrJumpObjectiveInfo );

	sep::destroyElement( mOfflineTestProcessorInfo );
}


////////////////////////////////////////////////////////////////////////////////
// GenericInfoData
////////////////////////////////////////////////////////////////////////////////

/**
 * APPEND
 * mGenericInfos
 */
void ExecutionInformation::addInfo(const AbstractProcessorUnit & aProcessor,
		const BF & anID, const BF & aData)
{
	mGenericInfos.append( BF( new GenericInfoData(
			aProcessor.REGISTER_TOOL(), anID, aData) ) );
}

void ExecutionInformation::addInfo(
		const AbstractProcessorUnit & aProcessor, const BF & aData)
{
	mGenericInfos.append( BF( new GenericInfoData(aProcessor.REGISTER_TOOL(),
			WObjectManager::toBF(aProcessor.getParameterWObject()), aData) ) );
}


/**
 * GETTER
 * mGenericInfos
 */
GenericInfoData * ExecutionInformation::getInfo(
		const IProcessorUnitRegistration & aRegisterTool) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aRegisterTool) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfo(
		const AbstractProcessorUnit & aProcessor) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aProcessor) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfo(
		const AbstractProcessorUnit & aProcessor, const BF & anID) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aProcessor, anID) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}


GenericInfoData * ExecutionInformation::getInfoWithData(
		const AbstractProcessorUnit & aProcessor, const BF & aData) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aProcessor) && itInfo->isData(aData) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfo(const BF & anID) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isID(anID) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfo(Element * anID) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isID(anID) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfo(
		Element * anID, const BF & aData) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isID(anID) && itInfo->isData(aData) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfo(
		const std::string & anID, AVM_OPCODE aPredicate) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isID(anID, aPredicate) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}


GenericInfoData * ExecutionInformation::getInfoByData(const BF & aData) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isData(aData) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}

GenericInfoData * ExecutionInformation::getInfoByData(
		const std::string & aData, AVM_OPCODE aPredicate) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isData(aData, aPredicate) )
		{
			return( itInfo );
		}
	}

	return( NULL );
}


/**
 * REMOVE
 * mGenericInfos
 */
void ExecutionInformation::removeInfo(
		const IProcessorUnitRegistration & aRegisterTool)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isInfo(aRegisterTool) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}

void ExecutionInformation::removeInfo(const AbstractProcessorUnit & aProcessor)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isInfo(aProcessor) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}


void ExecutionInformation::removeInfo(const BF & anID)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isID(anID) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}

void ExecutionInformation::removeInfo(Element * anID)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isID(anID) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}

void ExecutionInformation::removeInfo(
		const std::string & anID, AVM_OPCODE aPredicate)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isID(anID, aPredicate) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}


void ExecutionInformation::removeInfoByData(const BF & aData)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isData(aData) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}

void ExecutionInformation::removeInfoByData(
		const std::string & aData, AVM_OPCODE aPredicate)
{
	BFList::raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; )
	{
		if( itInfo->isData(aData, aPredicate) )
		{
			itInfo = mGenericInfos.erase( itInfo );
		}
		else
		{
			++itInfo;
		}
	}
}



/**
 * GETTER
 * Info Data
 */
const BF & ExecutionInformation::getInfoData(
		const IProcessorUnitRegistration & aRegisterTool) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aRegisterTool) )
		{
			return( itInfo->getData() );
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutionInformation::getInfoData(
		const AbstractProcessorUnit & aProcessor) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aProcessor) )
		{
			return( itInfo->getData() );
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutionInformation::getInfoData(
		const AbstractProcessorUnit & aProcessor, const BF & anID) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isInfo(aProcessor, anID) )
		{
			return( itInfo->getData() );
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutionInformation::getInfoData(const BF & anID) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isID(anID) )
		{
			return( itInfo->getData() );
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutionInformation::getInfoData(Element * anID) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		if( itInfo->isID(anID) )
		{
			return( itInfo->getData() );
		}
	}

	return( BF::REF_NULL );
}


/**
 * Serialization
 */
void ExecutionInformation::toStreamInfo(OutStream & out) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		itInfo->toStream(out);
	}
}

void ExecutionInformation::toFscnInfo(OutStream & out) const
{
	BFList::const_raw_iterator< GenericInfoData > itInfo = mGenericInfos.begin();
	BFList::const_raw_iterator< GenericInfoData > endInfo = mGenericInfos.end();
	for( ; itInfo != endInfo ; ++itInfo )
	{
		itInfo->toFscn(out);
	}
}


////////////////////////////////////////////////////////////////////////////////
// FormulaCoverageFilter Information
////////////////////////////////////////////////////////////////////////////////

FormulaCoverageFilterInfo *
ExecutionInformation::getUniqFormulaCoverageFilterInfo()
{
	if( mFormulaCoverageFilterInfo == NULL )
	{
		mFormulaCoverageFilterInfo = new FormulaCoverageFilterInfo();
	}
	return( mFormulaCoverageFilterInfo );
}


////////////////////////////////////////////////////////////////////////////////
// AvmHitOrJumpObjective Information
////////////////////////////////////////////////////////////////////////////////

HitOrJumpObjectiveInfo * ExecutionInformation::getUniqHitOrJumpObjectiveInfo()
{
	if( mHitOrJumpObjectiveInfo == NULL )
	{
		mHitOrJumpObjectiveInfo = new HitOrJumpObjectiveInfo();
	}
	return( mHitOrJumpObjectiveInfo );
}


////////////////////////////////////////////////////////////////////////////////
// OfflineTestProcessor Information
////////////////////////////////////////////////////////////////////////////////

OfflineTestProcessorInfo *
ExecutionInformation::getUniqOfflineTestProcessorInfo()
{
	if( mOfflineTestProcessorInfo == NULL )
	{
		mOfflineTestProcessorInfo = new OfflineTestProcessorInfo();
	}
	return( mOfflineTestProcessorInfo );
}


/**
 * Serialization
 */
void ExecutionInformation::toStream(OutStream & out) const
{
	toStreamInfo(out);

	if( mFormulaCoverageFilterInfo != NULL )
	{
		mFormulaCoverageFilterInfo->toStream(out);
	}
}

void ExecutionInformation::toFscn(OutStream & out) const
{
	if( mFormulaCoverageFilterInfo != NULL )
	{
		mFormulaCoverageFilterInfo->toFscn(out);
	}
}


}
