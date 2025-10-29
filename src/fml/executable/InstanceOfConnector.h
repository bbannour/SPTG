/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef INSTANCEOFCONNECTOR_H_
#define INSTANCEOFCONNECTOR_H_

#include <fml/executable/BaseInstanceForm.h>

#include <collection/Typedef.h>

#include <fml/lib/IComPoint.h>

#include <fml/executable/RoutingData.h>

#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/Connector.h>


namespace sep
{


class BaseAvmProgram;
class Connector;


class InstanceOfConnector final :
		public BaseInstanceForm ,
		AVM_INJECT_STATIC_NULL_REFERENCE( InstanceOfConnector ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceOfConnector )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceOfConnector )


protected:
	/*
	 * ATTRIBUTES
	 */
	// The Transfert Flag
	bool mTransfertFlag;

	// The Message IDentifier
	std::size_t mMID;

	// global ComRoute protocol & cast
	ComProtocol::PROTOCOL_KIND mProtocol;

	ComProtocol::PROTOCOL_KIND mGlobalCast;

	ComProtocol::PROTOCOL_KIND mOutputProtocolCast;
	ComProtocol::PROTOCOL_KIND mInputProtocolCast;

	TableOfRoutingData mOutputRoutingDataTable;
	TableOfRoutingData mInputRoutingDataTable;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfConnector(BaseAvmProgram * aContainer,
			const Connector & astConnector, avm_offset_t anOffset,
			ComProtocol::PROTOCOL_KIND aProtocol,
			ComProtocol::PROTOCOL_KIND aGlobalCast);


	/**
	 * CONSTRUCTOR
	 * copy
	 */
	InstanceOfConnector(const InstanceOfConnector & aConnector)
	: BaseInstanceForm( aConnector ),
	mTransfertFlag( aConnector.mTransfertFlag ),

	mMID( aConnector.mMID ),

	mProtocol( aConnector.mProtocol ),

	mGlobalCast( aConnector.mGlobalCast ),

	mOutputProtocolCast( aConnector.mOutputProtocolCast ),
	mInputProtocolCast ( aConnector.mInputProtocolCast  ),

	mOutputRoutingDataTable( aConnector.mOutputRoutingDataTable ),
	mInputRoutingDataTable( aConnector.mInputRoutingDataTable )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfConnector(BaseAvmProgram * aContainer,
			const InstanceOfConnector & aTarget,
			const VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfConnector ),
			aContainer, aTarget, aRelativeMachinePath),
	mTransfertFlag( aTarget.mTransfertFlag ),

	mMID( aTarget.mMID ),

	mProtocol( aTarget.mProtocol ),

	mGlobalCast( aTarget.mGlobalCast ),

	mOutputProtocolCast( aTarget.mOutputProtocolCast ),
	mInputProtocolCast ( aTarget.mInputProtocolCast  ),

	mOutputRoutingDataTable( aTarget.mOutputRoutingDataTable ),
	mInputRoutingDataTable ( aTarget.mInputRoutingDataTable  )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceOfConnector()
	{
		//!! NOTHING
	}

	/**
	 * DUE TO CIRCULAR REFERENCES
	 */
	void disposeRoutingData()
	{
		mOutputRoutingDataTable.clear();
		mInputRoutingDataTable.clear();
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static InstanceOfConnector & nullref()
	{
		static InstanceOfConnector _NULL_(
				nullptr, Connector::nullref(), 0,
				ComProtocol::PROTOCOL_UNDEFINED_KIND,
				ComProtocol::PROTOCOL_UNDEFINED_KIND );
		_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
		_NULL_.setAllName( Connector::nullref() );

		return( _NULL_ );
	}


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled COnnector
	 */
	inline const Connector & getAstConnector() const
	{
		return( safeAstElement().as< Connector >() );
	}


	/**
	 * GETTER - SETTER
	 * mMID
	 */
	inline std::size_t getMID() const
	{
		return( mMID );
	}

	inline void setMID(std::size_t mid)
	{
		mMID = mid;
	}


	/**
	 * GETTER - SETTER
	 * mProtocol
	 */
	inline ComProtocol::PROTOCOL_KIND getProtocol() const
	{
		return( mProtocol );
	}

	inline bool hasProtocol() const
	{
		return( mProtocol != ComProtocol::PROTOCOL_UNDEFINED_KIND );
	}

	/**
	 * GETTER - SETTER
	 * mGlobalCast
	 */
	inline ComProtocol::PROTOCOL_KIND getGlobalCast() const
	{
		return( mGlobalCast );
	}

	inline bool hasGlobalCast() const
	{
		return( mGlobalCast != ComProtocol::PROTOCOL_UNDEFINED_KIND );
	}


	/**
	 * GETTER - SETTER
	 * mOutputProtocolCast
	 */
	inline ComProtocol::PROTOCOL_KIND getOutputProtocolCast() const
	{
		return( mOutputProtocolCast );
	}

	inline bool hasOutputProtocolCast() const
	{
		return( mOutputProtocolCast != ComProtocol::PROTOCOL_UNDEFINED_KIND );
	}

	inline void setOutputProtocolCast(
			ComProtocol::PROTOCOL_KIND anOutputProtocolCast)
	{
		mOutputProtocolCast = anOutputProtocolCast;
	}

	/**
	 * GETTER - SETTER
	 * mInputProtocolCast
	 */
	inline ComProtocol::PROTOCOL_KIND getInputProtocolCast() const
	{
		return( mInputProtocolCast );
	}

	inline bool hasInputProtocolCast() const
	{
		return( mInputProtocolCast != ComProtocol::PROTOCOL_UNDEFINED_KIND );
	}

	inline void setInputProtocolCast(
			ComProtocol::PROTOCOL_KIND aInputProtocolCast)
	{
		mInputProtocolCast = aInputProtocolCast;
	}


	/**
	 * GETTER - SETTER
	 * mOutputRoutingDataTable
	 */
	inline const TableOfRoutingData & getOutputRoutingDataTable() const
	{
		return( mOutputRoutingDataTable );
	}

	inline std::size_t sizeOutputMachinePort() const
	{
		return( mOutputRoutingDataTable.size() );
	}

	inline bool singletonOutputMachinePort() const
	{
		return( mOutputRoutingDataTable.singleton() );
	}


	inline bool hasOutputRoutingData() const
	{
		return( mOutputRoutingDataTable.nonempty() );
	}

	inline void appendOutputRoutingData(const RoutingData & aRoutingData)
	{
		mOutputRoutingDataTable.append( aRoutingData );
	}


	/**
	 * GETTER - SETTER
	 * mInputRoutingDataTable
	 */
	inline const TableOfRoutingData & getInputRoutingDataTable() const
	{
		return( mInputRoutingDataTable );
	}

	inline void getInputMachinePort(
			VectorOfPairMachinePort & machinePorts) const
	{
		for( const auto & itRoutingData : getInputRoutingDataTable() )
		{
			machinePorts.append( &(itRoutingData.getMachinePort()) );
		}
	}

	inline std::size_t sizeInputMachinePort() const
	{
		return( mInputRoutingDataTable.size() );
	}

	inline bool singletonInputMachinePort() const
	{
		return( mInputRoutingDataTable.singleton() );
	}


	inline bool hasInputRoutingData() const
	{
		return( mInputRoutingDataTable.nonempty() );
	}

	inline void appendInputRoutingData(const RoutingData & aRoutingData)
	{
		mInputRoutingDataTable.append( aRoutingData );
	}


	/**
	 * Serialization
	 */
	void strHeader(OutStream & out) const override;

	void toStream(OutStream & out) const override;

};


}

#endif /* INSTANCEOFCONNECTOR_H_ */
