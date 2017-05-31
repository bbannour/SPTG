/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_PROPERTYPART_H_
#define FML_INFRASTRUCTURE_PROPERTYPART_H_

#include <fml/common/ObjectClassifier.h>
#include <fml/common/ObjectElement.h>

#include <collection/BFContainer.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Variable.h>


namespace sep
{


class PropertyPart : public ObjectClassifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( PropertyPart )
{

	AVM_DECLARE_CLONABLE_CLASS( PropertyPart )


public:
	/**
	 * TYPEDEF
	 */
	typedef TableOfBF_T< Buffer        >  TableOfBuffer;

	typedef TableOfBF_T< Port          >  TableOfPort;

	typedef TableOfBF_T< Signal        >  TableOfSignal;

	typedef TableOfBF_T< Channel       >  TableOfChannel;

	typedef TableOfBF_T< DataType      >  TableOfDataType;

	typedef TableOfBF_T< Variable      >  TableOfVariable;

	typedef TableOfBF_T< ObjectElement >  TableOfOwnedElement;

	/**
	 * ITERATORS
	 */

	typedef TableOfOwnedElement::const_raw_iterator  const_owned_iterator;

	typedef TableOfDataType::const_raw_iterator      const_type_iterator;

	typedef TableOfVariable::const_raw_iterator      const_variable_iterator;


protected:
	/**
	 * ATTRIBUTES
	 */
	TableOfOwnedElement mOwnedElements;

	TableOfBuffer       mBuffers;

	TableOfPort         mPorts;

	TableOfSignal       mSignals;

	TableOfChannel      mChannels;

	TableOfDataType     mDataTypes;

	TableOfVariable     mVariables;

	TableOfVariable     mVariableParameters;

	TableOfVariable     mVariableReturns;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	PropertyPart(ObjectElement * aContainer, const std::string & aNameID)
	: ObjectClassifier( CLASS_KIND_T( PropertyPart ) , aContainer , aNameID ),
	mOwnedElements( ),
	mBuffers( ),
	mPorts( ),
	mSignals( ),
	mChannels( ),
	mDataTypes( ),
	mVariables( ),
	mVariableParameters( ),
	mVariableReturns( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	PropertyPart(const PropertyPart & aPart)
	: ObjectClassifier( aPart ),
	mOwnedElements( aPart.mOwnedElements ),
	mBuffers( aPart.mBuffers ),
	mPorts( aPart.mPorts ),
	mSignals( aPart.mSignals ),
	mChannels( aPart.mChannels ),
	mDataTypes( aPart.mDataTypes ),
	mVariables( aPart.mVariables ),
	mVariableParameters( aPart.mVariableParameters ),
	mVariableReturns( aPart.mVariableReturns )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~PropertyPart()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - DISPATCH - SAVE
	 * mOwnedElements
	 */
	inline const TableOfOwnedElement & getOwnedElements() const
	{
		return( mOwnedElements );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_owned_iterator owned_begin() const
	{
		return( mOwnedElements.begin() );
	}

	inline const_owned_iterator owned_end() const
	{
		return( mOwnedElements.end() );
	}


	/**
	 * DISPATCH - SAVE
	 * mOwnedElements
	 */
	void dispatchOwnedElement(const BF & anElement);

	inline const BF & saveOwnedElement(ObjectElement * ptrElement)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( ptrElement )
				<< "Property owned element !!!"
				<< SEND_EXIT;

		// Should be set by the executable machine container !
		ptrElement->setOffset( mOwnedElements.size() );

		mOwnedElements.append( INCR_BF( ptrElement ) );

		dispatchOwnedElement( mOwnedElements.last() );

		return( mOwnedElements.last() );
	}


	/**
	 * GETTER - SETTER
	 * mBuffers
	 */
	inline void appendBuffer(const BF & aBuffer)
	{
		mBuffers.append( aBuffer );

		mOwnedElements.append( aBuffer );
	}

	inline const TableOfBuffer & getBuffers() const
	{
		return( mBuffers );
	}

	inline const BF & getBuffer(const std::string & aQualifiedNameID) const
	{
		return( mBuffers.getByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * GETTER - SETTER
	 * mPorts
	 */
	inline void appendPort(const BF & aPort)
	{
		mPorts.append( aPort );

		mOwnedElements.append( aPort );
	}

	inline const TableOfPort & getPorts() const
	{
		return( mPorts );
	}

	inline const BF & getPort(const std::string & aQualifiedNameID) const
	{
		return( mPorts.getByQualifiedNameID(aQualifiedNameID) );
	}

	inline bool hasPort() const
	{
		return( mPorts.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mSignals
	 */
	inline void appendSignal(const BF & aSignal)
	{
		mSignals.append( aSignal );

		mOwnedElements.append( aSignal );
	}

	inline const TableOfSignal & getSignals() const
	{
		return( mSignals );
	}

	inline const BF & getSignal(const std::string & aQualifiedNameID) const
	{
		return( mSignals.getByQualifiedNameID(aQualifiedNameID) );
	}

	inline bool hasSignal() const
	{
		return( mSignals.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mPorts / mSignals
	 */
	inline const BF & getPortSignal(const std::string & aQualifiedNameID) const
	{
		const BF & port = mPorts.getByQualifiedNameID(aQualifiedNameID);
		if( port.valid() )
		{
			return( port );
		}
		else
		{
			return( mSignals.getByQualifiedNameID(aQualifiedNameID) );
		}
	}


	/**
	 * GETTER - SETTER
	 * mBuffers
	 */
	inline void appendChannel(const BF & aChannel)
	{
		mChannels.append( aChannel );

		mOwnedElements.append( aChannel );
	}

	inline const TableOfChannel & getChannels() const
	{
		return( mChannels );
	}

	inline const BF & getChannel(const std::string & aQualifiedNameID) const
	{
		return( mChannels.getByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * GETTER - SETTER
	 * mDataTypes
	 */
	inline void appendDataType(const BF & aDataType)
	{
		mDataTypes.append( aDataType );

		mOwnedElements.append( aDataType );
	}

	inline const TableOfDataType & getDataTypes() const
	{
		return( mDataTypes );
	}

	inline const BF & getDataType(const std::string & aQualifiedNameID) const
	{
		return( mDataTypes.getByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_type_iterator type_begin() const
	{
		return( mDataTypes.begin() );
	}

	inline const_type_iterator type_end() const
	{
		return( mDataTypes.end() );
	}


	/**
	 * GETTER - SETTER
	 * mVariables
	 */
	inline void appendVariable(const BF & aVariable)
	{
		mVariables.append( aVariable );

		mOwnedElements.append( aVariable );
	}

	inline const TableOfVariable & getVariables() const
	{
		return( mVariables );
	}

	inline const BF & getVariable(const std::string & aQualifiedNameID) const
	{
		return( mVariables.getByQualifiedNameID(aQualifiedNameID) );
	}

	inline bool hasVariable() const
	{
		return( mVariables.nonempty() );
	}

//	inline void saveVariable(Variable * aVariable)
//	{
//		appendVariable( BF(aVariable) );
//	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_variable_iterator variable_begin() const
	{
		return( mVariables.begin() );
	}

	inline const_variable_iterator variable_end() const
	{
		return( mVariables.end() );
	}


	/**
	 * GETTER - SETTER
	 * mVariableParameters
	 */
	inline void appendVariableParameter(const BF & aVariable)
	{
		mVariableParameters.append( aVariable );

		mOwnedElements.append( aVariable );
	}

	inline const TableOfVariable & getVariableParameters() const
	{
		return( mVariableParameters );
	}

	inline const BF & getVariableParameter(
			const std::string & aQualifiedNameID) const
	{
		return( mVariableParameters.getByQualifiedNameID(aQualifiedNameID) );
	}

	inline bool hasVariableParameter() const
	{
		return( mVariableParameters.nonempty() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_variable_iterator var_parameter_begin() const
	{
		return( mVariableParameters.begin() );
	}

	inline const_variable_iterator var_parameter_end() const
	{
		return( mVariableParameters.end() );
	}


	/**
	 * UTIL
	 * mVariables as Parameters
	 */
	inline const BF & getVariableParameter(avm_size_t offset) const
	{
		return( mVariableParameters.get( offset ) );
	}

	inline avm_offset_t getVariableParametersCount() const
	{
		return( mVariableParameters.size() );
	}

	inline avm_offset_t getVariableParameterOffsetByNameID(
			const std::string & aNameID) const
	{
		return( mVariableParameters.getOffsetByNameID( aNameID ) );
	}


	/**
	 * GETTER - SETTER
	 * mVariableReturns
	 */
	inline void appendVariableReturn(const BF & aVariable)
	{
		mVariableReturns.append( aVariable );

		mOwnedElements.append( aVariable );
	}

	inline const TableOfVariable & getVariableReturns() const
	{
		return( mVariableReturns );
	}

	inline const BF & getVariableReturn(
			const std::string & aQualifiedNameID) const
	{
		return( mVariableReturns.getByQualifiedNameID(aQualifiedNameID) );
	}

	inline bool hasVariableReturn() const
	{
		return( mVariableReturns.nonempty() );
	}


	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_variable_iterator var_return_begin() const
	{
		return( mVariableReturns.begin() );
	}

	inline const_variable_iterator var_return_end() const
	{
		return( mVariableReturns.end() );
	}


	/**
	 * UTIL
	 * mVariables as Returns
	 */
	inline const BF & getVariableReturn(avm_size_t offset) const
	{
		return( mVariableReturns.get( offset ) );
	}

	inline avm_offset_t getVariableReturnsCount() const
	{
		return( mVariableReturns.size() );
	}

	inline avm_offset_t getVariableReturnOffsetByNameID(
			const std::string & aNameID) const
	{
		return( mVariableReturns.getOffsetByNameID( aNameID ) );
	}


	/**
	 * DISPATCH - SAVE
	 * using Variable::Modifier
	 * mVariables
	 * mVariableParameters
	 * mVariableReturns
	 * mVariableInternals
	 */
	void dispatchOwnedVariable(const BF & aVariable);

	inline const BF & saveOwnedVariable(Variable * aVariable)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
				<< "Property Variable owned element !!!"
				<< SEND_EXIT;

		// Should be set by the executable machine container !
		aVariable->setOffset( mOwnedElements.size() );

		mOwnedElements.append( INCR_BF( aVariable ) );

		dispatchOwnedVariable( mOwnedElements.last() );

		return( mOwnedElements.last() );
	}


	/**
	 * GETTER
	 * general
	 */
	inline bool empty() const
	{
		return( mOwnedElements.empty() );
	}

	inline bool nonempty() const
	{
		return( mOwnedElements.nonempty() );
	}


	/**
	 * GETTER for
	 * PARSER
	 * COMPILER
	 */
	inline const BF & getPropertyByNameID(const std::string & aNameID) const
	{
		return( mOwnedElements.getByNameID(aNameID) );
	}

	inline const BF & getPropertyByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( mOwnedElements.getByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * Serialization
	 */
	void strVariableParameters(OutStream & os,
			const std::string & begin = " [ ",
			const std::string & end = " ]",
			const std::string & sep = ", ") const;

	void strVariableReturns(OutStream & os,
			const std::string & begin = " returns: [ ",
			const std::string & end = " ]",
			const std::string & sep = ", ") const;

	void toStream(OutStream & os) const;

};


}

#endif /* FML_INFRASTRUCTURE_PROPERTYPART_H_ */


