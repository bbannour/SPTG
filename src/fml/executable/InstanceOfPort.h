/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef INSTANCEOFPORT_H_
#define INSTANCEOFPORT_H_

#include <fml/executable/BaseInstanceForm.h>

#include <fml/lib/IComPoint.h>

#include <fml/executable/InstanceOfData.h>
#include <fml/executable/RoutingData.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/Port.h>


namespace sep
{

class ArrayBF;
class BaseAvmProgram;
class RoutingData;


class InstanceOfPort final :
		public BaseInstanceForm,
		public IComPoint,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceOfPort )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceOfPort )


protected:
	/*
	 * ATTRIBUTES
	 */
	std::size_t mRouteOffset;

	// the nature
	ENUM_IO_NATURE mComPointNature;

	// the Parameter Type Specifier
	ArrayOfBF mParameters;

	// the Contents of the port as channel
	TableOfSymbol mContents;

	InstanceOfPort * mRoutingChannel;

	// The routing data access optimization
	RoutingData mInputRoutingData;
	RoutingData mOutputRoutingData;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfPort(BaseAvmProgram * aContainer,
			const PropertyElement & astPort, avm_offset_t anOffset,
			std::size_t aParameterCount, ENUM_IO_NATURE aNature);


	/**
	 * CONSTRUCTOR
	 * copy
	 */
	InstanceOfPort(const InstanceOfPort & aPort)
	: BaseInstanceForm( aPort ),
	mRouteOffset( aPort.mRouteOffset ),
	mComPointNature( aPort.mComPointNature ),

	mParameters( aPort.mParameters ),
	mContents( aPort.mContents ),

	mRoutingChannel( aPort.mRoutingChannel ),

	mInputRoutingData( aPort.mInputRoutingData ),
	mOutputRoutingData( aPort.mOutputRoutingData )
	{
		//!! NOTHING
//		AVM_OS_TRACE << "port::new :> " << getFullyQualifiedNameID() << std::endl;
	}


	/**
	 * CONSTRUCTOR
	 * via Channel
	 */
	InstanceOfPort(BaseAvmProgram * aContainer, const Port & astChannelPort,
			InstanceOfPort * aChannel, const InstanceOfPort & aTarget)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfPort ),
			aContainer, astChannelPort, aTarget),
	mRouteOffset( aTarget.mRouteOffset ),
	mComPointNature( aTarget.mComPointNature ),

	mParameters( aTarget.mParameters ),
	mContents( aTarget.mContents ),

	mRoutingChannel( aChannel ),

	mInputRoutingData( ),
	mOutputRoutingData( )

	{
		setAliasTarget( aTarget );
//		AVM_OS_TRACE << "port::new :> " << getFullyQualifiedNameID() << std::endl;
	}


	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfPort(BaseAvmProgram * aContainer, const InstanceOfPort & aTarget,
			const VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfPort ), aContainer, aTarget,
			aRelativeMachinePath),
	mRouteOffset( aTarget.mRouteOffset ),
	mComPointNature( aTarget.mComPointNature ),

	mParameters( aTarget.mParameters ),
	mContents( aTarget.mContents ),

	mRoutingChannel( aTarget.mRoutingChannel ),

	mInputRoutingData( ),
	mOutputRoutingData( )

	{
		//!! NOTHING
//		AVM_OS_TRACE << "port::new :> " << getFullyQualifiedNameID() << std::endl;
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceOfPort()
	{
//		AVM_OS_TRACE << "port::delete :> " << getFullyQualifiedNameID() << std::endl;
		//!! NOTHING
	}

	/**
	 * DUE TO CIRCULAR REFERENCES
	 */
	void disposeRoutingData()
	{
		mInputRoutingData = RoutingData::nullref();
		mOutputRoutingData = RoutingData::nullref();
	}


	/**
	 * Factory
	 * new Port à Channel
	 */
	static InstanceOfPort * newChannel(BaseAvmProgram * aContainer,
			const Channel & astChannel, avm_offset_t anOffset)
	{
		return( new InstanceOfPort(aContainer, astChannel,
				anOffset, 0, IO_CHANNEL_NATURE) );
	}

	/**
	 * GETTER - SETTER
	 * mRouteOffset
	 */
	inline std::size_t getRouteOffset() const
	{
		return( mRouteOffset );
	}

	inline void setRouteOffset(std::size_t aRouteOffset)
	{
		mRouteOffset = aRouteOffset;
	}


	/**
	 * API
	 * IComPoint
	 * mComPointNature
	 * mComPointDirection
	 */
	inline virtual ENUM_IO_NATURE getComPointNature() const override
	{
		return( mComPointNature );
	}


	/**
	 * GETTER - SETTER
	 * mParameters
	 */
	inline ArrayOfBF & getParameters()
	{
		return( mParameters );
	}

	inline const ArrayOfBF & getParameters() const
	{
		return( mParameters );
	}


	inline const BF & getParameter(std::size_t offset) const
	{
		return( mParameters[offset] );
	}

	inline const BaseTypeSpecifier & getParameterType(std::size_t offset) const
	{
		if( mParameters[offset].is< BaseTypeSpecifier >() )
		{
			return( mParameters[offset].to< BaseTypeSpecifier >() );
		}
		else if( mParameters[offset].is< BaseInstanceForm >() )
		{
			return( mParameters[offset].
					to< BaseInstanceForm >().getTypeSpecifier() );
		}
		return( BaseTypeSpecifier::nullref() );
	}


	inline std::size_t getParameterCount() const
	{
		return( mParameters.size() );
	}


	inline bool hasParameter() const
	{
		return( getParameterCount() > 0 );
	}

	inline bool hasParameterType(std::size_t offset) const
	{
		if( offset < getParameterCount() )
		{
			if( mParameters[offset].is< BaseTypeSpecifier >() )
			{
				return( true );
			}
			else if( mParameters[offset].is< BaseInstanceForm >() )
			{
				return( mParameters[offset].
						to< BaseInstanceForm >().hasTypeSpecifier() );
			}
		}
		return( false );
	}

	inline bool isParameterData(std::size_t offset) const
	{
		return( mParameters[offset].is< InstanceOfData >() );
	}


	inline void setParameter(std::size_t index, const BF & aParam)
	{
		mParameters[index]= aParam;
	}


	/**
	 * GETTER - SETTER
	 * mContents
	 */
	inline void appendContent(const Symbol & aSymbol)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aSymbol )
				<< "Symbol as Channel content !!!"
				<< SEND_EXIT;

		mContents.append(aSymbol);
	}

	inline TableOfSymbol & getContents()
	{
		return( mContents );
	}

	inline const TableOfSymbol & getContents() const
	{
		return( mContents );
	}


	inline const BF & getContent(std::size_t offset) const
	{
		return( mContents[offset] );
	}


	inline std::size_t getContentCount() const
	{
		return( mContents.size() );
	}


	inline bool hasContent() const
	{
		return( getContentCount() > 0 );
	}


	inline bool isContentData(std::size_t offset) const
	{
		return( mContents[offset].is< InstanceOfData >() );
	}

	inline bool isContentPort(std::size_t offset) const
	{
		return( mContents[offset].is< InstanceOfPort >() );
	}


	inline void setContent(std::size_t index, const Symbol & aSymbol)
	{
		mContents[index]= aSymbol;
	}


	/**
	 * GETTER - SETTER
	 * mRoutingChannel
	 */
	inline InstanceOfPort * getRoutingChannel() const
	{
		return( mRoutingChannel );
	}

	inline bool hasRoutingChannel() const
	{
		return( mRoutingChannel != nullptr );
	}

	inline void setRoutingChannel(InstanceOfPort * aRoutingChannel)
	{
		mRoutingChannel = aRoutingChannel;
	}


	/**
	 * GETTER - SETTER
	 * mInputRoutingData
	 */
	inline const RoutingData & getInputRoutingData() const
	{
		return( mInputRoutingData );
	}

	inline bool hasInputRoutingData() const
	{
		return( mInputRoutingData != nullptr );
	}

	inline void setInputRoutingData(const RoutingData & anInputRoutingData)
	{
		mInputRoutingData = anInputRoutingData;
	}


	/**
	 * GETTER - SETTER
	 * mOutputRoutingData
	 */
	inline const RoutingData & getOutputRoutingData() const
	{
		return( mOutputRoutingData );
	}

	inline bool hasOutputRoutingData() const
	{
		return( mOutputRoutingData != nullptr );
	}

	inline void setOutputRoutingData(const RoutingData & anOutputRoutingData)
	{
		mOutputRoutingData = anOutputRoutingData;
	}


	/**
	 * Format a value w.r.t. its type
	 */
	virtual void formatStream(OutStream & out, const BF & bfValue) const;

	virtual void formatStream(OutStream & out, const ArrayBF & arrayValue) const;


	/**
	 * Serialization
	 */
	void strParameter(OutStream & out, const BF & aParameter) const;
	void strParameter(OutStream & out) const;

	virtual void strHeader(OutStream & out) const override;

	std::string strArg() const;

	virtual void toStream(OutStream & out) const override;

	static void toStream(OutStream & out,
			const ListOfInstanceOfPort & iePorts);

};


}

#endif /* INSTANCEOFPORT_H_ */
