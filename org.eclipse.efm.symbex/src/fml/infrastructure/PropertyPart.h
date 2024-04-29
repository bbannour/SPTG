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

#include <collection/BFContainer.h>

#include <common/BF.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Function.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Variable.h>


namespace sep
{

class ObjectElement;

class TypeSpecifier;


class PropertyPart : public ObjectClassifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( PropertyPart )
{

	AVM_DECLARE_CLONABLE_CLASS( PropertyPart )


public:
	/**
	 * TIME CONSTANT
	 */
	static std::string VAR_ID_TIME;
	static std::string VAR_ID_TIME_INITIAL;
	static BF VAR_TIME_INITIAL_VALUE;

	static std::string VAR_ID_DELTA_TIME;
	static std::string VAR_ID_DELTA_TIME_INITIAL;
	static BF VAR_DELTA_TIME_INITIAL_VALUE;

	/**
	 * TYPEDEF
	 */
	typedef TableOfBF_T< Buffer        >  TableOfBuffer;

	typedef TableOfBF_T< Port          >  TableOfPort;

	typedef TableOfBF_T< Signal        >  TableOfSignal;

	typedef TableOfBF_T< Channel       >  TableOfChannel;

	typedef TableOfBF_T< DataType      >  TableOfDataType;

	typedef TableOfBF_T< Function      >  TableOfFunction;

	typedef TableOfBF_T< Variable      >  TableOfVariable;

	/**
	 * ITERATORS
	 */
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

	TableOfFunction     mFunctions;

	TableOfVariable     mVariables;

	TableOfVariable     mVariableParameters;

	TableOfVariable     mVariableReturns;


	Variable * mTimeVariable;
	Variable * mDeltaTimeVariable;

	BF mExprTimeVariable;
	BF mExprDeltaTimeVariable;

	BF mExprTimeInitialConstant;
	BF mExprDeltaTimeInitialConstant;


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
	mFunctions( ),

	mVariables( ),
	mVariableParameters( ),
	mVariableReturns( ),

	mTimeVariable( nullptr ),
	mDeltaTimeVariable( nullptr ),

	mExprTimeVariable( ),
	mExprDeltaTimeVariable( ),

	mExprTimeInitialConstant( ),
	mExprDeltaTimeInitialConstant( )
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
	mFunctions( aPart.mFunctions ),

	mVariables( aPart.mVariables ),
	mVariableParameters( aPart.mVariableParameters ),
	mVariableReturns( aPart.mVariableReturns ),

	mTimeVariable( aPart.mTimeVariable ),
	mDeltaTimeVariable( aPart.mDeltaTimeVariable ),

	mExprTimeVariable( aPart.mExprTimeVariable ),
	mExprDeltaTimeVariable( aPart.mExprDeltaTimeVariable ),

	mExprTimeInitialConstant( aPart.mExprTimeInitialConstant ),
	mExprDeltaTimeInitialConstant( aPart.mExprDeltaTimeInitialConstant )
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

	inline bool hasOwnedElement() const
	{
		return( mOwnedElements.nonempty() );
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
	void dispatchOwnedElement(BF & anElement);

	inline const BF & saveOwnedElement(ObjectElement * ptrElement)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( ptrElement )
				<< "Property owned element !!!"
				<< SEND_EXIT;

		// Should be set by the executable machine container !
		ptrElement->setOwnedOffset( mOwnedElements.size() );

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

	const BF & getEnumDataType(const std::string & aQualifiedNameID) const;
	const BF & getSemEnumDataType(const std::string & aQualifiedNameID) const;


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
	 * mFunctions
	 */
	inline void appendFunction(const BF & aFunction)
	{
		mFunctions.append( aFunction );

		mOwnedElements.append( aFunction );
	}

	inline const TableOfFunction & getFunctions() const
	{
		return( mFunctions );
	}

	inline const BF & getFunction(const std::string & aQualifiedNameID) const
	{
		return( mFunctions.getByQualifiedNameID(aQualifiedNameID) );
	}

	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_type_iterator fuction_begin() const
	{
		return( mFunctions.begin() );
	}

	inline const_type_iterator function_end() const
	{
		return( mFunctions.end() );
	}


	/**
	 * ADD
	 * [ delta ] time property
	 */
	Variable * addTimeSupport(const TypeSpecifier & timeType);

	Variable * addDeltaTimeSupport(const TypeSpecifier & deltaType);


	/**
	 * GETTER
	 * Time Variable
	 */
	inline Variable * getTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTimeVariable )
				<< "Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mTimeVariable );
	}

	inline const BF & getTimeType() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTimeVariable )
				<< "Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mTimeVariable->getType() );
	}

	inline const BF & exprTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTimeVariable )
				<< "Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mExprTimeVariable );
	}

	inline const BF & exprTimeInitialConstant() const
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( mExprTimeInitialConstant )
				<< "Time Initial Constant in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mExprTimeInitialConstant );
	}


	inline bool hasTimeVariable() const
	{
		return( mTimeVariable != nullptr );
	}


	/**
	 * GETTER
	 * Delta Time Variable
	 */
	inline Variable * getDeltaTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mDeltaTimeVariable )
				<< "Delta Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mDeltaTimeVariable );
	}

	inline const BF & getDeltaTimeType() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mDeltaTimeVariable )
				<< "Delta Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mDeltaTimeVariable->getType() );
	}

	inline const BF & exprDeltaTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mDeltaTimeVariable )
				<< "Delta Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mExprDeltaTimeVariable );
	}

	inline const BF & exprDeltaTimeInitialConstant() const
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT(
				mExprDeltaTimeInitialConstant )
				<< "Delta Time Initial Constant in "
				<< str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mExprDeltaTimeInitialConstant );
	}


	inline bool hasDeltaTimeVariable() const
	{
		return( mDeltaTimeVariable != nullptr );
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

	inline void appendVariable(const TableOfVariable & variables)
	{
		mVariables.append( variables );

		mOwnedElements.append( variables );
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

	inline void appendVariableParameter(
			const std::string & label, const BF & aParameter)
	{
		mVariableParameters.append( aParameter );
	}

	inline const TableOfVariable & getVariableParameters() const
	{
		return( mVariableParameters );
	}

	inline TableOfVariable & getVariableParameters()
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
	inline const BF & getVariableParameter(std::size_t offset) const
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

	inline void appendVariableReturn(
			const std::string & label, const BF & aParameter)
	{
		mVariableReturns.append( aParameter );
	}

	inline const TableOfVariable & getVariableReturns() const
	{
		return( mVariableReturns );
	}

	inline TableOfVariable & getVariableReturns()
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
	inline const BF & getVariableReturn(std::size_t offset) const
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
	 * GETTER
	 * the parameters / returns
	 */
	inline const BF & getVariableParameterReturn(
			const std::string & aNameID) const
	{
		const BF & bfParam = mVariableParameters.getByNameID(aNameID);

		return( bfParam.valid() ? bfParam
				: mVariableReturns.getByNameID(aNameID)  );

	}


	/**
	 * DISPATCH - SAVE
	 * using Variable::Modifier
	 * mVariables
	 * mVariableParameters
	 * mVariableReturns
	 * mVariableInternals
	 */
	void dispatchOwnedVariable(BF & bfVariable);

	const BF & saveOwnedVariable(Variable * aVariable);

	/**
	 * SAVE
	 * mVariableParameters
	 * mVariableReturns
	 */
	const BF & saveOwnedVariableParameter(Variable * aVariable);

	const BF & saveOwnedVariableReturn(Variable * aVariable);


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
	inline const BF & getObjectByNameID(const std::string & aNameID) const
	{
		return( mOwnedElements.getByNameID(aNameID) );
	}

	inline const BF & getObjectByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( mOwnedElements.getByQualifiedNameID(aQualifiedNameID) );
	}


	/**
	 * Serialization
	 */
	void strVariableParameters(OutStream & out,
			const std::string & begin = " [ ",
			const std::string & end = " ]",
			const std::string & sep = ", ") const;

	void strVariableReturns(OutStream & out,
			const std::string & begin = " returns: [ ",
			const std::string & end = " ]",
			const std::string & sep = ", ") const;

	void strHeader(OutStream & out) const;

	void toStream(OutStream & out) const override;

};


}

#endif /* FML_INFRASTRUCTURE_PROPERTYPART_H_ */


