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

#ifndef EXECUTIONINFORMATION_H_
#define EXECUTIONINFORMATION_H_

#include <common/Element.h>

#include <common/BF.h>

#include <collection/BFContainer.h>

#include <fml/operator/OperatorLib.h>


namespace sep
{

class AbstractProcessorUnit;
class IProcessorUnitRegistration;


/**
 * Generic Info < id , data >
 * @property id   : have to be a Processor Register Tool
 * @property data : anything
 */
class GenericInfoData final : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( GenericInfoData )
{

	AVM_DECLARE_CLONABLE_CLASS( GenericInfoData )


protected:
	/**
	 * ATTRIBUTES
	 */
	const IProcessorUnitRegistration & mProcessorRegisterTool;
	BF mID;
	BF mData;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	GenericInfoData(const IProcessorUnitRegistration & aProcessorRegisterTool,
			const BF & anID, const BF & aData)
	: Element( CLASS_KIND_T( GenericInfoData ) ),
	mProcessorRegisterTool( aProcessorRegisterTool ),
	mID( anID ),
	mData( aData )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	GenericInfoData(const GenericInfoData & anInfoData)
	: Element( anInfoData ),
	mProcessorRegisterTool( anInfoData.mProcessorRegisterTool ),
	mID( anInfoData.mID ),
	mData( anInfoData.mData )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~GenericInfoData()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mProcessorRegisterTool
	 */
	inline const IProcessorUnitRegistration & getProcessorRegisterTool() const
	{
		return( mProcessorRegisterTool );
	}

	inline bool isInfo(
			const IProcessorUnitRegistration & aProcessorRegisterTool) const
	{
		return( (& mProcessorRegisterTool) == (& aProcessorRegisterTool) );
	}

	bool isInfo(const AbstractProcessorUnit & aProcessor) const;
	bool isInfo(const AbstractProcessorUnit & aProcessor, const BF & anID) const;


	/**
	 * GETTER - SETTER
	 * mID
	 */
	inline const BF & getID() const
	{
		return( mID );
	}

	inline bool hasID() const
	{
		return( mID.valid() );
	}

	inline bool isID(const BF & anID) const
	{
		return( mID.isTEQ(anID) || (mID.str() == anID.str()) );
	}

	inline bool isID(const Element * anID) const
	{
		return( mID.isTEQ(anID) );
	}

	inline bool isID(const std::string & anID,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ) const
	{
		switch( aPredicate )
		{
			case AVM_OPCODE_EQ:
			case AVM_OPCODE_SEQ:
			{
				return( strID() == anID );
			}
			case AVM_OPCODE_STARTS_WITH:
			case AVM_OPCODE_GTE:
			{
				return( strID().find(anID) == 0 );
			}
			case AVM_OPCODE_CONTAINS:
			{
				return( strID().find(anID) != std::string::npos );
			}

			default:
			{
				return( strID() == anID );
			}
		}
	}


	inline std::string strID() const
	{
		return( mID.invalid() ? ""
				: ( mID.isBuiltinString() ?
						mID.toBuiltinString() : mID.str() ) );
	}

	std::string strUID() const;

	/**
	 * GETTER - SETTER
	 * mData
	 */
	inline const BF & getData() const
	{
		return( mData );
	}


	inline bool hasData() const
	{
		return( mData.valid() );
	}

	inline bool isData(const BF & aData) const
	{
		return( mData.isEQ(aData) );
	}

	inline bool isData(const std::string & aData,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ) const
	{
		switch( aPredicate )
		{
			case AVM_OPCODE_EQ:
			case AVM_OPCODE_SEQ:
			{
				return( strData() == aData );
			}
			case AVM_OPCODE_STARTS_WITH:
			case AVM_OPCODE_GTE:
			{
				return( strData().find(aData) == 0 );
			}
			case AVM_OPCODE_CONTAINS:
			{
				return( strData().find(aData) != std::string::npos );
			}

			default:
			{
				return( strData() == aData );
			}
		}
	}


	inline std::string strData() const
	{
		return( mData.invalid() ? ""
				: ( mData.isBuiltinString() ?
						mData.toBuiltinString() : mData.str() ) );
	}

	inline void setData(const BF & aData)
	{
		mData = aData;
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & out) const override;

	virtual void toFscn(OutStream & out) const;

};


/**
 * ExecutionInformation
 */
class ExecutionInformation final : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionInformation )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionInformation )


protected:
	/**
	 * ATTRIBUTES
	 */
	BFList mGenericInfos;

	Element * mSpecificInfo;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionInformation()
	: Element( CLASS_KIND_T( ExecutionInformation ) ),
	mGenericInfos(),
	mSpecificInfo( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionInformation(const ExecutionInformation & anExecInfo)
	: Element( anExecInfo ),
	mGenericInfos( anExecInfo.mGenericInfos ),
	mSpecificInfo( anExecInfo.mSpecificInfo )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionInformation()
	{
		sep::destroyElement( mSpecificInfo );
	}



	////////////////////////////////////////////////////////////////////////////
	// GenericInfoData
	////////////////////////////////////////////////////////////////////////////
	/**
	 * APPEND
	 * mGenericInfos
	 */
	void addInfo(const IProcessorUnitRegistration & aRegisterTool,
			const BF & anID, const BF & aData)
	{
		mGenericInfos.append( BF(
				new GenericInfoData(aRegisterTool, anID, aData) ) );
	}

	void addInfo(const AbstractProcessorUnit & aProcessor,
			const BF & anID, const BF & aData);

	void addInfo(const AbstractProcessorUnit & aProcessor, const BF & aData);


	/**
	 * GETTER
	 * mGenericInfos
	 */
	inline const BFList & getInfos() const
	{
		return( mGenericInfos );
	}

	inline BFList & getInfos()
	{
		return( mGenericInfos );
	}


	GenericInfoData * getInfo(
			const IProcessorUnitRegistration & aRegisterTool) const;

	GenericInfoData * getInfo(const AbstractProcessorUnit & aProcessor) const;
	GenericInfoData * getInfo(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const;
	GenericInfoData * getInfoWithData(
			const AbstractProcessorUnit & aProcessor, const BF & aData) const;

	GenericInfoData * getInfo(const BF & anID) const;
	GenericInfoData * getInfo(Element * anID) const;
	GenericInfoData * getInfo(Element * anID, const BF & aData) const;
	GenericInfoData * getInfo(const std::string & anID,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ) const;

	GenericInfoData * getInfoByData(const BF & aData) const;
	GenericInfoData * getInfoByData(const std::string & aData,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ) const;

	/**
	 * TESTER
	 * mGenericInfos
	 */
	inline bool hasInfo() const
	{
		return( mGenericInfos.nonempty() );
	}

	inline bool noneInfo() const
	{
		return( mGenericInfos.empty() );
	}


	inline bool hasInfo(const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( getInfo(aRegisterTool) != nullptr );
	}

	bool hasInfo(const AbstractProcessorUnit & aProcessor) const
	{
		return( getInfo(aProcessor) != nullptr );
	}

	bool noneInfo(const AbstractProcessorUnit & aProcessor) const
	{
		return( getInfo(aProcessor) == nullptr );
	}

	bool hasInfo(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const
	{
		return( getInfo(aProcessor, anID) != nullptr );
	}

	bool hasInfoWithData(
			const AbstractProcessorUnit & aProcessor, const BF & aData) const
	{
		return( getInfoWithData(aProcessor, aData) != nullptr );
	}


	inline bool hasInfo(const BF & anID) const
	{
		return( getInfo(anID) != nullptr );
	}

	inline bool hasInfo(Element * anID) const
	{
		return( getInfo(anID) != nullptr );
	}

	inline bool hasInfo(const std::string & anID,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ) const
	{
		return( getInfo(anID, aPredicate) != nullptr );
	}


	inline bool hasInfoByData(const BF & aData) const
	{
		return( getInfoByData(aData) != nullptr );
	}

	inline bool hasInfoByData(const std::string & aData,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ) const
	{
		return( getInfoByData(aData, aPredicate) != nullptr );
	}


	/**
	 * REMOVE
	 * mGenericInfos
	 */
	void removeInfo(const IProcessorUnitRegistration & aRegisterTool);
	void removeInfo(const AbstractProcessorUnit & aProcessor);

	void removeInfo(const BF & anID);
	void removeInfo(Element * anID);
	void removeInfo(const std::string & anID,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ);

	void removeInfoByData(const BF & aData);
	void removeInfoByData(const std::string & aData,
			AVM_OPCODE aPredicate = AVM_OPCODE_EQ);


	/**
	 * GETTER
	 * Data
	 */
	const BF & getInfoData(
			const IProcessorUnitRegistration & aRegisterTool) const;

	const BF & getInfoData(const AbstractProcessorUnit & aProcessor) const;
	const BF & getInfoData(
			const AbstractProcessorUnit & aProcessor, const BF & anID) const;

	const BF & getInfoData(const BF & anID) const;
	const BF & getInfoData(Element * anID) const;


	/**
	 * GETTER - SETTER
	 */
	template< class T >
	T * getUniqSpecificInfo()
	{
		if( mSpecificInfo == nullptr )
		{
			mSpecificInfo = new T();
		}
		return( static_cast< T * >( mSpecificInfo ) );
	}


	inline bool hasSpecificInfo() const
	{
		return(	(mSpecificInfo != nullptr) );
	}

	inline void getSpecificInfo(Element * anInfo)
	{
		mSpecificInfo = anInfo ;
	}


	/**
	 * Serialization
	 * toStream
	 */
	virtual void toStream(OutStream & out) const override
	{
		toStreamInfo(out);

		if( mSpecificInfo != nullptr )
		{
			mSpecificInfo->toStream(out);
		}
	}

	virtual void toStreamInfo(OutStream & out) const;


	/**
	 * Serialization
	 * toFscn
	 */
	virtual void toFscn(OutStream & out) const
	{
		if( mSpecificInfo != nullptr )
		{
			mSpecificInfo->toFscn(out);
		}
	}

	virtual void toFscnInfo(OutStream & out) const;


};


}

#endif /* EXECUTIONINFORMATION_H_ */
