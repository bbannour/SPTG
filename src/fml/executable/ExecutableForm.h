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
#ifndef EXECUTABLEFORM_H_
#define EXECUTABLEFORM_H_

#include <fml/executable/AvmProgram.h>
#include <fml/common/SpecifierElement.h>

#include <base/SmartTable.h>

#include <collection/Typedef.h>
#include <collection/Vector.h>

#include <fml/expression/AvmCode.h>

#include <fml/executable/AvmTransition.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnector.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/executable/Router.h>

#include <fml/symbol/Symbol.h>
#include <fml/symbol/TableOfSymbol.h>

#include <fml/infrastructure/InstanceSpecifierPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/System.h>


namespace sep
{

class AvmCode;
class ExecutableSystem;
class ObjectElement;
class Specifier;


// TYPE DEFINITION for TABLE , SMART POINTER and CONTAINER
typedef  TableOfBF_T< ExecutableForm >  TableOfExecutableForm;

typedef SmartTable< InstanceOfBuffer  , DestroyElementPolicy > TableOfBuffer;
typedef SmartTable< InstanceOfConnector , DestroyElementPolicy > TableOfConnectorT;
typedef SmartTable< InstanceOfData    , DestroyElementPolicy > TableOfVariableT;
typedef SmartTable< InstanceOfMachine , DestroyElementPolicy > TableOfMachineT;
typedef SmartTable< InstanceOfPort    , DestroyElementPolicy > TableOfPortT;


class ExecutableForm final :
		public AvmProgram ,
		public SpecifierImpl,
		AVM_INJECT_STATIC_NULL_REFERENCE( ExecutableForm ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutableForm )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutableForm )

protected:
	/*
	 * ATTRIBUTES
	 */
	ExecutableSystem & mExecutableSystem;

	std::size_t mInitialInstanceCount;
	std::size_t mMaximalInstanceCount;

	std::size_t mPossibleStaticInstanciationCount;
	std::size_t mPossibleDynamicInstanciationCount;

	TableOfSymbol mTableOfChannel;

	TableOfSymbol mTableOfPort;
	std::size_t mMessageSignalCount;

	TableOfSymbol mTableOfBuffer;
	TableOfSymbol mTableOfConnector;

	TableOfSymbol mTableOfInstanceModel;

	TableOfSymbol mTableOfInstanceStatic;
	InstanceOfMachine * mPrototypeInstance;

	TableOfSymbol mTableOfInstanceDynamic;

	TableOfTransition mTableOfTransition;

	TableOfAvmProgram mTableOfProgram;

	TableOfAvmProgram mTableOfAnonymousInnerRoutine;

	TableOfExecutableForm mTableOfExecutable;

	TableOfSymbol mTableOfAlias;

	// Time & Delta Variable
	const InstanceOfData * mTimeVariable;
	const InstanceOfData * mDeltaTimeVariable;

	BF mExprTimeVariable;
	BF mExprDeltaTimeVariable;

	// Predefined routines
	AvmProgram onCreateRoutine;
	AvmProgram onInitRoutine;
	AvmProgram onFinalRoutine;

	AvmProgram onReturnRoutine;

	AvmProgram onStartRoutine;
	AvmProgram onStopRoutine;

	AvmProgram onIEnableRoutine;
	AvmProgram onEnableRoutine;

	AvmProgram onIDisableRoutine;
	AvmProgram onDisableRoutine;

	AvmProgram onIAbortRoutine;
	AvmProgram onAbortRoutine;

	AvmProgram onIRunRoutine;
	AvmProgram onRunRoutine;
	AvmProgram onRtcRoutine;

	AvmProgram onScheduleRoutine;
	AvmProgram onConcurrencyRoutine;

	AvmProgram onSynchronizeRoutine;


	// Structural decompositon
	bool mMainComponentFlag;

	// MOC Attribute for mutable Schedule
	bool mMutableScheduleFlag;


	// Communication routing
	TableOfRouter mTableOfRouter4Instance;

	TableOfRouter mTableOfRouter4Model;

	bool mRdvCommunicationFlag;

	// MOC Attribute for Communication
	bool mInputEnabledCommunicationFlag;


	////////////////////////////////////////////////////////////////////////////
	// Static Analysis Information
	////////////////////////////////////////////////////////////////////////////

	TableOfInstanceOfData mRequiredData;
	TableOfInstanceOfData mUselessData;


	// The list of backward reachable machine
	ListOfInstanceOfMachine mBackwardReachableMachine;

	// The list of backward reachable transition
	ListOfAvmTransition mBackwardReachableTransition;


	// The list of forward reachable machine
	ListOfInstanceOfMachine mForwardReachableMachine;

	// The list of forward reachable transition
	ListOfAvmTransition mForwardReachableTransition;

	// Default is << true >>
	bool isReachableStateFlag;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutableForm(ExecutableSystem & aExecutableSystem,
			ExecutableForm * aContainer,
			const Machine & astMachine, std::size_t aDataSize = 0)
	: AvmProgram(CLASS_KIND_T( ExecutableForm ),
			Specifier::SCOPE_MACHINE_KIND, aContainer, astMachine, aDataSize),
	SpecifierImpl( astMachine ),

	mExecutableSystem( aExecutableSystem ),

	mInitialInstanceCount(
		(astMachine.isnotNullref() && astMachine.hasInstanceSpecifier()) ?
			astMachine.getInstanceSpecifier()->getInitialInstanceCount() : 1 ),
	mMaximalInstanceCount(
		(astMachine.isnotNullref() && astMachine.hasInstanceSpecifier()) ?
			astMachine.getInstanceSpecifier()->getMaximalInstanceCount() : 1 ),

	mPossibleStaticInstanciationCount( 0 ),
	mPossibleDynamicInstanciationCount( 0 ),

	mTableOfChannel( ),

	mTableOfPort( ),
	mMessageSignalCount( 0 ),

	mTableOfBuffer( ),
	mTableOfConnector( ),

	mTableOfInstanceModel( ),

	mTableOfInstanceStatic( ),
	mPrototypeInstance( ),

	mTableOfInstanceDynamic( ),

	mTableOfTransition( ),
	mTableOfProgram( ),
	mTableOfAnonymousInnerRoutine( ),

	mTableOfExecutable( ),

	mTableOfAlias( ),

	mTimeVariable( nullptr ),
	mDeltaTimeVariable( nullptr ),

	mExprTimeVariable( ),
	mExprDeltaTimeVariable( ),

	onCreateRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "create" , 0 ),

	onInitRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "init"  , 0 ),
	onFinalRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "final" , 0 ),

	onReturnRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "return" , 0 ),

	onStartRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "start" , 0 ),
	onStopRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "stop"  , 0 ),

	onIEnableRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "ienable" , 0 ),
	onEnableRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "enable"  , 0 ),

	onIDisableRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "idisable" , 0 ),
	onDisableRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "disable"  , 0 ),

	onIAbortRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "iabort" , 0 ),
	onAbortRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "abort"  , 0 ),

	onIRunRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "irun" , 0 ),
	onRunRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "run"  , 0 ),
	onRtcRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "rtc"  , 0 ),

	onScheduleRoutine   ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "schedule"    , 0  ),
	onConcurrencyRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "concurrency" , 0 ),

	onSynchronizeRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "synchronize" , 0 ),

	mMainComponentFlag( ( astMachine.isNullref() ||
			astMachine.getModifier().hasFeatureTransient() ) ? false : true ),

	mMutableScheduleFlag( false ),

	mTableOfRouter4Instance( ),

	mTableOfRouter4Model( ),

	mRdvCommunicationFlag( false ),

	mInputEnabledCommunicationFlag( false ),

	mRequiredData( ),
	mUselessData( ),

	mBackwardReachableMachine( ),
	mBackwardReachableTransition( ),

	mForwardReachableMachine( ),
	mForwardReachableTransition( ),

	isReachableStateFlag( true )
	{
		updateFullyQualifiedNameID();
	}

	ExecutableForm(ExecutableSystem & aExecutableSystem, std::size_t aDataSize)
	: AvmProgram(CLASS_KIND_T( ExecutableForm ), Specifier::SCOPE_MACHINE_KIND,
			nullptr, Machine::nullref(), aDataSize),
	SpecifierImpl( Specifier::COMPONENT_EXECUTABLE_SPECIFIER ),

	mExecutableSystem( aExecutableSystem ),

	mInitialInstanceCount( 1 ),
	mMaximalInstanceCount( 1 ),

	mPossibleStaticInstanciationCount( 0 ),
	mPossibleDynamicInstanciationCount( 0 ),

	mTableOfChannel( ),

	mTableOfPort( ),
	mMessageSignalCount( 0 ),

	mTableOfBuffer( ),
	mTableOfConnector( ),

	mTableOfInstanceModel( ),

	mTableOfInstanceStatic( ),
	mPrototypeInstance( ),

	mTableOfInstanceDynamic( ),

	mTableOfTransition( ),
	mTableOfProgram( ),
	mTableOfAnonymousInnerRoutine( ),

	mTableOfExecutable( ),

	mTableOfAlias( ),

	mTimeVariable( nullptr ),
	mDeltaTimeVariable( nullptr ),

	mExprTimeVariable( ),
	mExprDeltaTimeVariable( ),

	onCreateRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "create" , 0 ),

	onInitRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "init"  , 0 ),
	onFinalRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "final" , 0 ),

	onReturnRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "return" , 0 ),

	onStartRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "start" , 0 ),
	onStopRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "stop"  , 0 ),

	onIEnableRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "ienable" , 0 ),
	onEnableRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "enable"  , 0 ),

	onIDisableRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "idisable" , 0 ),
	onDisableRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "disable"  , 0 ),

	onIAbortRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "iabort" , 0 ),
	onAbortRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "abort"  , 0 ),

	onIRunRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "irun" , 0 ),
	onRunRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "run"  , 0 ),
	onRtcRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "rtc"  , 0 ),

	onScheduleRoutine   ( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "schedule"    , 0  ),
	onConcurrencyRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "concurrency" , 0 ),

	onSynchronizeRoutine( Specifier::SCOPE_ROUTINE_KIND ,
			(* this) , Routine::nullref() , "synchronize" , 0 ),

	mMainComponentFlag( false ),

	mMutableScheduleFlag( false ),

	mTableOfRouter4Instance( ),

	mTableOfRouter4Model( ),

	mRdvCommunicationFlag( false ),

	mInputEnabledCommunicationFlag( false ),

	mRequiredData( ),
	mUselessData( ),

	mBackwardReachableMachine( ),
	mBackwardReachableTransition( ),

	mForwardReachableMachine( ),
	mForwardReachableTransition( ),

	isReachableStateFlag( true )
	{
		updateFullyQualifiedNameID();
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutableForm()
	{
		mRequiredData.clear();
		mUselessData.clear();

		disposeRoutingData();
	}

	/**
	 * DUE TO CIRCULAR REFERENCES
	 * InstanceOfConnector --> RoutingData --> & InstanceOfConnector
	 * InstanceOfPort --> RoutingData --> & InstanceOfPort
	 */
	void disposeRoutingData()
	{
		for( auto & connector : mTableOfConnector )
		{
			connector.to< InstanceOfConnector >().disposeRoutingData();
		}

		for( auto & port : mTableOfPort )
		{
			port.to< InstanceOfPort >().disposeRoutingData();
		}

		mTableOfRouter4Instance.clear();
//		for( auto & router : mTableOfRouter4Instance )
//		{
//			router.disposeRoutingData();
//		}

		mTableOfRouter4Model.clear();
//		for( auto & router : mTableOfRouter4Model )
//		{
//			router.disposeRoutingData();
//		}
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static ExecutableForm & nullref();


	/**
	 * GETTER - SETTER
	 * is in SCOPE
	 */
	inline bool isAncestorOf(const ExecutableForm * anExecutable)
	{
		while( (anExecutable != nullptr) && (anExecutable != this) )
		{
			anExecutable = anExecutable->getExecutableContainer();
		}
		return( anExecutable == this );
	}


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID(
			const std::string & aFullyQualifiedNameID);

	inline virtual void updateFullyQualifiedNameID() override
	{
		if( hasAstElement() )
		{
			updateFullyQualifiedNameID( getAstFullyQualifiedNameID() );

			setUnrestrictedName( getAstElement().hasUnrestrictedName() ?
					getAstElement().getUnrestrictedName() : getNameID() );
		}
		else
		{
			setAllNameID( "exec#anonym" , "exec#anonym" );
		}
	}


	/**
	 * LCA -LCRA
	 */
	const ExecutableForm * LCA(
			const ExecutableForm * anExecutable) const;

	inline const ExecutableForm * LCRA(
			const ExecutableForm * anExecutable) const
	{
		return( (this == anExecutable) ? this : LCA( anExecutable ) );
	}


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled Machine
	 */
	inline const Machine & getAstMachine() const
	{
		return( safeAstElement().as< Machine >() );
	}

	inline const System & getAstSystem() const
	{
		return( safeAstElement().as< System >() );
	}

//!@?UNUSED
//	inline bool isCompiledSystem() const
//	{
//		return( getSpecifier().isComponentSystem()
//				&& hasAstElement() && getAstElement().is< System >() );
//	}



	/**
	 * Primitive inlining
	 */
	bool isInlinableEnable() const
	{
		return( hasAstElement() && getAstElement().is< Machine >() &&
				getAstMachine().isInlinableEnable() );
	}

	bool isInlinableProcedure() const
	{
		return( hasAstElement() && getAstElement().is< Machine >() &&
				getAstMachine().isInlinableProcedure() );
	}


	/**
	 * GETTER - SETTER
	 * mInitialInstanceCount
	 */
	inline std::size_t getInitialInstanceCount() const
	{
		return( mInitialInstanceCount );
	}

	inline bool hasInitialInstance() const
	{
		return( mInitialInstanceCount > 0 );
	}

	inline void setInitialInstanceCount(std::size_t anInitialInstanceCount)
	{
		mInitialInstanceCount = anInitialInstanceCount;
	}


	/**
	 * GETTER - SETTER
	 * mMaximalInstanceCount
	 */
	inline std::size_t getMaximalInstanceCount() const
	{
		return( mMaximalInstanceCount );
	}

	inline bool hasMaximalInstance() const
	{
		return( mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T );
	}

	inline bool hasMaximalNewInstance() const
	{
		return( (mMaximalInstanceCount > mInitialInstanceCount) &&
				(mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T) );
	}

	inline void setMaximalInstanceCount(std::size_t aMaximalInstanceCount)
	{
		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	/**
	 * SETTER
	 * mInitialInstanceCount
	 * mMaximalInstanceCount
	 */
	inline void setInstanceCount(std::size_t anInitialInstanceCount,
			std::size_t aMaximalInstanceCount)
	{
		mInitialInstanceCount = anInitialInstanceCount;

		mMaximalInstanceCount = aMaximalInstanceCount;
	}

	inline std::size_t getCreatedInstanceCount() const
	{
		return( mInitialInstanceCount );

//		return( (mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T) ?
//				mMaximalInstanceCount : mInitialInstanceCount );
	}


	/*
	 * GETTER - SETTER
	 * mPossibleStaticInstanciationCount
	 * mPossibleDynamicInstanciationCount
	 * Single or Multiple
	 * Instanciation Information
	 * for Data Access optimisation
	 */
	inline std::size_t getPossibleStaticInstanciationCount() const
	{
		return( mPossibleStaticInstanciationCount );
	}

	inline bool hasPossibleStaticInstanciation() const
	{
		return( mPossibleStaticInstanciationCount > 0 );
	}

	void incrPossibleStaticInstanciationCount(avm_offset_t offset = 1);


	inline std::size_t getPossibleDynamicInstanciationCount() const
	{
		return( mPossibleDynamicInstanciationCount );
	}

	inline bool hasPossibleDynamicInstanciation() const
	{
		return( mPossibleDynamicInstanciationCount > 0 );
	}

	void incrPossibleDynamicInstanciationCount(std::size_t offset = 1);


	bool hasSingleRuntimeInstance() const;


	/**
	 * GETTER - SETTER
	 * mTableOfChannel
	 */
	inline const Symbol & saveChannel(InstanceOfPort * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfPort !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfChannel.save(anInstance) );
	}

	inline TableOfSymbol & getChannel()
	{
		return( mTableOfChannel );
	}

	inline const TableOfSymbol & getChannel() const
	{
		return( mTableOfChannel );
	}

	inline bool hasChannel() const
	{
		return( mTableOfChannel.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfPort
	 */
	inline const Symbol & savePort(InstanceOfPort * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfPort !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfPort.save(anInstance) );
	}

	inline TableOfSymbol & getPort()
	{
		return( mTableOfPort );
	}

	inline const TableOfSymbol & getPort() const
	{
		return( mTableOfPort );
	}


	inline bool hasPort() const
	{
		return( mTableOfPort.nonempty() );
	}

	/**
	 * GETTER - SETTER
	 * mMessageSignalCount
	 */
	inline std::size_t getMessageSignalCount() const
	{
		return( mMessageSignalCount );
	}

	inline bool hasMessageSignalCount() const
	{
		return( mMessageSignalCount > 0 );
	}

	inline void setMessageSignalCount(std::size_t count)
	{
		mMessageSignalCount = count;
	}


	/**
	 * GETTER - SETTER
	 * mTableOfBuffer
	 */

	inline const Symbol & saveBuffer(InstanceOfBuffer * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "BaseInstanceForm !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfBuffer.save(anInstance) );
	}

	inline TableOfSymbol & getBuffer()
	{
		return( mTableOfBuffer );
	}

	inline const TableOfSymbol & getBuffer() const
	{
		return( mTableOfBuffer );
	}


	inline bool hasBuffer() const
	{
		return( mTableOfBuffer.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfConnector
	 */

	inline const Symbol & saveConnector(InstanceOfConnector * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "BaseInstanceForm !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfConnector.save(anInstance) );
	}

	inline TableOfSymbol & getConnector()
	{
		return( mTableOfConnector );
	}

	inline const TableOfSymbol & getConnector() const
	{
		return( mTableOfConnector );
	}


	inline bool hasConnector() const
	{
		return( mTableOfConnector.nonempty() );
	}


	/**
	 * GETTER
	 * Communicated or Lifeline
	 */
	inline ExecutableForm * getExcutableCommunicator() const
	{
		ExecutableForm * anExecutable = getExecutableContainer();
		while( anExecutable != nullptr )
		{
			if( anExecutable->isCommunicator() )
			{
				return( anExecutable );
			}
			anExecutable = getExecutableContainer();
		}

		return( nullptr );
	}

	inline ExecutableForm * getExcutableSystem() const
	{
		ExecutableForm * anExecutable = getExecutableContainer();
		while( anExecutable != nullptr )
		{
			if( anExecutable->getSpecifier().isComponentSystem() )
			{
				return( anExecutable );
			}
			anExecutable = getExecutableContainer();
		}

		return( nullptr );
	}


	inline bool isCommunicator() const
	{
		return( hasPort() || hasRouter4This() || hasConnector() );
	}

	inline bool isCommunicatorWith(const InstanceOfPort & aPort) const
	{
		return( mTableOfPort.contains(& aPort)
			|| (hasRouter4This() && getRouter4This().hasRouting(aPort)) );
	}

	inline bool isLifeline() const
	{
		return( getSpecifier().hasFeatureLifeline() );
	}

	inline bool isWeakLifeline() const
	{
		return( isLifeline() || isCommunicator()
				|| (hasStatementComFamily()
					&& getSpecifier().isFamilyCompositeComponent()) );
	}


	/**
	 * GETTER - SETTER
	 * mDefault instance for using machine model
	 */
	inline const Symbol & saveInstanceModel(InstanceOfMachine * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfMachine !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfInstanceModel.save( anInstance ) );
	}

	inline void appendInstanceModel(Symbol & aMachine)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aMachine )
				<< "InstanceOfMachine !!!"
				<< SEND_EXIT;

		aMachine.setContainer(this);

		mTableOfInstanceModel.append( aMachine );
	}


	inline TableOfSymbol & getInstanceModel()
	{
		return( mTableOfInstanceModel );
	}

	inline const TableOfSymbol & getInstanceModel() const
	{
		return( mTableOfInstanceModel );
	}

	inline const Symbol & getByAstInstanceModel(
			const ObjectElement & astElement) const
	{
		const Symbol & aModel =
				mTableOfInstanceModel.getByAstElement(astElement);

		// To ignore the THIS instance at offset 0 !!!
		return( ( aModel.invalid() || aModel.isnotThis(this) ) ?
						aModel : Symbol::REF_NULL );
	}

	inline bool hasInstanceModel() const
	{
		return( mTableOfInstanceModel.nonempty() );
	}

	inline bool hasInstanceModelThis() const
	{
		return( mTableOfInstanceModel.nonempty() &&
				mTableOfInstanceModel.first().isThis() );
	}


	inline const Symbol & firstInstanceModel() const
	{
		return( hasInstanceModelThis() ?
				mTableOfInstanceModel.second() :
				mTableOfInstanceModel.first() );
	}

	inline bool hasOneInstanceModel() const
	{
		return( hasInstanceStaticThis()
				&& (mTableOfInstanceModel.size() == 2) );
	}

	inline std::size_t sizeInstanceModel() const
	{
		// don't forget the instance THIS at offset 0 !!!
		return( mTableOfInstanceModel.size()
				- (hasInstanceStaticThis() ? 1 : 0) );
	}



	/**
	 * GETTER
	 * begin -- end
	 * iterator
	 */
	inline TableOfSymbol::const_iterator instance_model_begin() const
	{
		// don't forget the instance THIS at offset 0 !!!
		return( hasInstanceStaticThis() ?
				++(mTableOfInstanceModel.begin()) :
				mTableOfInstanceModel.begin() );
	}

	inline TableOfSymbol::const_iterator instance_model_end() const
	{
		return( mTableOfInstanceModel.end() );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfInstanceStatic
	 */
	inline const Symbol & saveInstanceStatic(InstanceOfMachine * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfMachine !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfInstanceStatic.save(anInstance) );
	}

	inline TableOfSymbol & getInstanceStatic()
	{
		return( mTableOfInstanceStatic );
	}

	inline const TableOfSymbol & getInstanceStatic() const
	{
		return( mTableOfInstanceStatic );
	}


	inline const Symbol & getByAstInstanceStatic(
			const ObjectElement & astElement) const
	{
		const Symbol & anInstance =
				mTableOfInstanceStatic.getByAstElement(astElement);

		// To ignore the THIS instance at offset 0 !!!
		return( ( anInstance.invalid() || anInstance.isnotThis(this) ) ?
						anInstance : Symbol::REF_NULL );
	}


	inline bool hasInstanceStatic() const
	{
		return( mTableOfInstanceStatic.nonempty() );
	}

	inline bool hasInstanceStaticThis() const
	{
		return( mTableOfInstanceStatic.nonempty() &&
				mTableOfInstanceStatic.first().isThis() );
	}

	inline const Symbol & getInstanceStaticThis() const
	{
		return( mTableOfInstanceStatic.first() );
	}

	inline const Symbol & firstInstanceStatic() const
	{
		return( hasInstanceStaticThis() ?
				mTableOfInstanceStatic.second() :
				mTableOfInstanceStatic.first() );
	}


	inline bool hasOneInstanceStatic() const
	{
		return( hasInstanceStaticThis()
				&& (mTableOfInstanceStatic.size() == 2) );
	}

	inline std::size_t sizeInstanceStatic() const
	{
		// don't forget the instance THIS at offset 0 !!!
		return( mTableOfInstanceStatic.size()
				- (hasInstanceStaticThis() ? 1 : 0) );
	}


	/**
	 * GETTER
	 * begin -- end
	 * iterator
	 */
	inline TableOfSymbol::const_iterator instance_static_begin() const
	{
		// don't forget the instance THIS at offset 0 !!!
		return( hasInstanceStaticThis() ?
				++(mTableOfInstanceStatic.begin()) :
				mTableOfInstanceStatic.begin() );
	}


	inline TableOfSymbol::const_iterator instance_static_end() const
	{
		return( mTableOfInstanceStatic.end() );
	}


	/**
	 * GETTER - SETTER
	 * Machine Count
	 */
	std::size_t getrecMachineCount() const;


	/**
	 * GETTER
	 * mPrototypeInstance
	 */
	inline InstanceOfMachine * getPrototypeInstance() const
	{
		return( mPrototypeInstance );
	}

	inline bool hasPrototypeInstance() const
	{
		return( mPrototypeInstance != nullptr );
	}

	inline void setPrototypeInstance(InstanceOfMachine * anInstance)
	{
		mPrototypeInstance = anInstance;
	}


	/**
	 * GETTER - SETTER
	 * mTableOfInstanceStatic
	 * mTableOfInstanceModel
	 * mTableOfInstanceDynamic
	 */
	inline const TableOfSymbol & getInstanceByDesign(
			Specifier::DESIGN_KIND aDesign) const
	{
		switch( aDesign )
		{
			case Specifier::DESIGN_INSTANCE_KIND:
				return( mTableOfInstanceStatic );

			case Specifier::DESIGN_MODEL_KIND:
				return( mTableOfInstanceModel );

			case Specifier::DESIGN_DYNAMIC_KIND:
				return( mTableOfInstanceDynamic );

			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected instance design << "
						<< Specifier::strDesign(aDesign, "") << " >> !!!"
						<< SEND_EXIT;

				return( mTableOfInstanceStatic );
			}
		}
	}


	/**
	 * GETTER - SETTER
	 * mDefault instance for using machine model
	 */
	inline const Symbol & saveInstanceDynamic(InstanceOfMachine * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfMachine !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mTableOfInstanceDynamic.save( anInstance ) );
	}

	inline void appendInstanceDynamic(Symbol & aMachine)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aMachine )
				<< "InstanceOfMachine !!!"
				<< SEND_EXIT;

		aMachine.setContainer(this);

		mTableOfInstanceDynamic.append( aMachine );
	}


	inline TableOfSymbol & getInstanceDynamic()
	{
		return( mTableOfInstanceDynamic );
	}

	inline const TableOfSymbol & getInstanceDynamic() const
	{
		return( mTableOfInstanceDynamic );
	}

	inline const Symbol & getByAstInstanceDynamic(
			const ObjectElement & astElement) const
	{
		return( mTableOfInstanceDynamic.getByAstElement(astElement) );
	}

	inline bool hasInstanceDynamic() const
	{
		return( mTableOfInstanceDynamic.nonempty() );
	}


	/**
	 * GETTER
	 * begin -- end
	 * iterator
	 */
	inline TableOfSymbol::const_iterator instance_dynamic_begin() const
	{
		// don't forget the instance THIS at offset 0 !!!
		return( mTableOfInstanceDynamic.begin() );
	}

	inline TableOfSymbol::const_iterator instance_dynamic_end() const
	{
		return( mTableOfInstanceDynamic.end() );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfTransition
	 */
	inline const BF & saveTransition(AvmTransition * aTransition)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTransition )
				<< "AvmTransition !!!"
				<< SEND_EXIT;

		aTransition->setContainer(this);
		aTransition->setOffset( mTableOfTransition.size() );

		return( mTableOfTransition.save(aTransition) );
	}

	inline TableOfTransition & getTransition()
	{
		return( mTableOfTransition );
	}

	inline const TableOfTransition & getTransition() const
	{
		return( mTableOfTransition );
	}

	inline AvmTransition * rawTransition(avm_offset_t offset) const
	{
		return( mTableOfTransition.rawAt(offset) );
	}


	inline const BF & getTransition(const std::string & aFullyQualifiedNameID,
			bool enabledOnlyLocationComparisonElse = false) const
	{
		return( mTableOfTransition.getByFQNameID(
				aFullyQualifiedNameID, enabledOnlyLocationComparisonElse ) );
	}

	inline const BF & getTransitionByID(const std::string & anID) const
	{
		return( mTableOfTransition.getByID( anID ) );
	}

	inline const BF & getTransitionByNameID(const std::string & aNameID) const
	{
		return( mTableOfTransition.getByNameID( aNameID ) );
	}

	inline const BF & getTransitionByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( mTableOfTransition.getByQualifiedNameID( aQualifiedNameID ) );
	}


	inline const BF & getTransitionByAstElement(
			const ObjectElement & astElement) const
	{
		return( mTableOfTransition.getByAstElement(astElement) );
	}


	inline bool hasTransition() const
	{
		return( mTableOfTransition.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfProgram
	 */
	inline void appendProgram(const BF & anAvmProgram)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anAvmProgram )
				<< "AvmProgram !!!"
				<< SEND_EXIT;

		anAvmProgram.to_ptr< AvmProgram >()->setContainer(this);
		anAvmProgram.to_ptr< AvmProgram >()->setOffset( mTableOfProgram.size() );

		mTableOfProgram.append(anAvmProgram);
	}

	inline const BF & saveProgram(AvmProgram * anAvmProgram)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anAvmProgram )
				<< "AvmProgram !!!"
				<< SEND_EXIT;

		anAvmProgram->setContainer(this);
		anAvmProgram->setOffset( mTableOfProgram.size() );

		return( mTableOfProgram.save(anAvmProgram) );
	}

	inline TableOfAvmProgram & getProgram()
	{
		return( mTableOfProgram );
	}

	inline const TableOfAvmProgram & getProgram() const
	{
		return( mTableOfProgram );
	}

	inline AvmProgram * rawProgram(avm_offset_t offset) const
	{
		return( mTableOfProgram.rawAt(offset) );
	}


	inline const BF & getProgram(const std::string & aFullyQualifiedNameID,
			Specifier::SCOPE_KIND aScope =
					Specifier::SCOPE_UNDEFINED_KIND) const
	{
		return( mTableOfProgram.getByFQNameID(aFullyQualifiedNameID, aScope) );
	}

	inline const BF & getProgramByNameID(const std::string & id,
			Specifier::SCOPE_KIND aScope =
					Specifier::SCOPE_UNDEFINED_KIND) const
	{
		return( mTableOfProgram.getByNameID(id, aScope) );
	}

	inline const BF & getProgramByQualifiedNameID(
			const std::string & aQualifiedNameID,
			Specifier::SCOPE_KIND aScope =
					Specifier::SCOPE_UNDEFINED_KIND) const
	{
		return( mTableOfProgram.
				getByQualifiedNameID(aQualifiedNameID, aScope) );
	}


	inline const BF & getProgramByAstElement(
			const ObjectElement & astElement) const
	{
		return( mTableOfProgram.getByAstElement(astElement) );
	}

	inline bool hasProgram() const
	{
		return( mTableOfProgram.nonempty() );
	}

	/**
	 * GETTER - SETTER
	 * mTableOfAnonymousInnerRoutine
	 * like << variable::on_write >> or << type::constraint >> routines
	 */
	inline const BF & saveAnonymousInnerRoutine(AvmProgram * aRoutine)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aRoutine )
				<< "Anonymous Inner Routine as Program !!!"
				<< SEND_EXIT;

		aRoutine->setContainer(this);
		aRoutine->setOffset( mTableOfAnonymousInnerRoutine.size() );

		return( mTableOfAnonymousInnerRoutine.save(aRoutine) );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfExecutable
	 */
	inline const BF & saveExecutable(ExecutableForm * anExecutable)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anExecutable )
				<< "ExecutableForm !!!"
				<< SEND_EXIT;

		anExecutable->setContainer(this);
		anExecutable->setOffset( mTableOfExecutable.size() );

		return( mTableOfExecutable.save(anExecutable) );
	}

	inline const TableOfExecutableForm & getExecutables() const
	{
		return( mTableOfExecutable );
	}

	inline bool hasExecutable() const
	{
		return( mTableOfExecutable.nonempty() );
	}


	/*
	 * contains DATA
	 */
	inline bool containsVariable(InstanceOfData * anInstance) const
	{
		return( AvmProgram::containsVariable(anInstance) );
//				|| mTableOfAlias.contains(anInstance) );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfAlias
	 */
	inline void appendAlias(const Symbol & anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		mTableOfAlias.append(anInstance);
	}

	inline const Symbol & saveAlias(BaseInstanceForm * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		return( mTableOfAlias.save(anInstance) );
	}

	inline TableOfSymbol & getAlias()
	{
		return( mTableOfAlias );
	}

	inline const TableOfSymbol & getAlias() const
	{
		return( mTableOfAlias );
	}


	inline bool hasAlias() const
	{
		return( mTableOfAlias.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mTimeVariable
	 * mExprTimeVariable
	 */
	const InstanceOfData * getTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTimeVariable )
				<< "Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mTimeVariable );
	}

	const BF & exprTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mTimeVariable )
				<< "Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mExprTimeVariable );
	}

	bool hasTimeVariable() const
	{
		return( mTimeVariable != nullptr );
	}

	void setTimeVariable(const BF & timeVariable)
	{
		mTimeVariable = timeVariable.to_ptr< InstanceOfData >();

		mExprTimeVariable = timeVariable;
	}


	/**
	 * GETTER - SETTER
	 * mDeltaTimeVariable
	 * mExprDeltaTimeVariable
	 */
	const InstanceOfData * getDeltaTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mDeltaTimeVariable )
				<< "Delta Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mDeltaTimeVariable );
	}

	const BF & exprDeltaTimeVariable() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mDeltaTimeVariable )
				<< "Delta Time Variable in " << str_header( *this ) << " !!!"
				<< SEND_EXIT;

		return( mExprDeltaTimeVariable );
	}

	bool hasDeltaTimeVariable() const
	{
		return( mDeltaTimeVariable != nullptr );
	}

	void setDeltaTimeVariable(const BF & deltaTimeVariable)
	{
		mDeltaTimeVariable = deltaTimeVariable.to_ptr< InstanceOfData >();

		mExprDeltaTimeVariable = deltaTimeVariable;
	}


	void setDeltaTimeVariable();


	/**
	 * GETTER
	 * any SYMBOL filtering by an optional type specifier family
	 */
	virtual const BF & getSymbol(
			const std::string & aFullyQualifiedNameID,
			avm_type_specifier_kind_t typeFamily) const override;

	virtual const BF & getSymbolByQualifiedNameID(
			const std::string & aQualifiedNameID,
			avm_type_specifier_kind_t typeFamily) const override;

	virtual const BF & getSymbolByNameID(const std::string & aNameID,
			avm_type_specifier_kind_t typeFamily) const override;

	virtual const BF & getSymbolByAstElement(const ObjectElement & astElement,
			avm_type_specifier_kind_t typeFamily) const override;


	/**
	 * GETTER - SETTER
	 * onCreateRoutine
	 */
	inline const AvmProgram & getOnCreateRoutine() const
	{
		return( onCreateRoutine );
	}

	inline const BFCode & getOnCreate() const
	{
		return( onCreateRoutine.getCode() );
	}

	inline bool hasOnCreate() const
	{
		return( onCreateRoutine.hasCode() );
	}

	inline void setOnCreate(const BFCode & aProgram)
	{
		onCreateRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onInitRoutine
	 */
	inline const AvmProgram & getOnInitRoutine() const
	{
		return( onInitRoutine );
	}

	inline const BFCode & getOnInit() const
	{
		return( onInitRoutine.getCode() );
	}

	inline bool hasOnInit() const
	{
		return( onInitRoutine.hasCode() );
	}

	bool hasOnInitMachine() const
	{
		return( hasOnInit() && getOnInit()->isOpCode(AVM_OPCODE_INIT)
				&& getOnInit()->getOperands().singleton()
				&& getOnInit()->first().is< InstanceOfMachine >() );
	}

	inline void setOnInit(const BFCode & aProgram)
	{
		onInitRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onFinalRoutine
	 */
	inline const AvmProgram & getOnFinalRoutine() const
	{
		return( onFinalRoutine );
	}

	inline const BFCode & getOnFinal() const
	{
		return( onFinalRoutine.getCode() );
	}

	inline bool hasOnFinal() const
	{
		return( onFinalRoutine.hasCode() );
	}

	inline void setOnFinal(const BFCode & aProgram)
	{
		onFinalRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onReturnRoutine
	 */
	inline const AvmProgram & getOnReturnRoutine() const
	{
		return( onReturnRoutine );
	}

	inline const BFCode & getOnReturn() const
	{
		return( onReturnRoutine.getCode() );
	}

	inline bool hasOnReturn() const
	{
		return( onReturnRoutine.hasCode() );
	}

	inline void setOnReturn(const BFCode & aProgram)
	{
		onReturnRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onStartRoutine
	 */
	inline const AvmProgram & getOnStartRoutine() const
	{
		return( onStartRoutine );
	}

	inline const BFCode & getOnStart() const
	{
		return( onStartRoutine.getCode() );
	}

	inline bool hasOnStart() const
	{
		return( onStartRoutine.hasCode() );
	}

	inline void setOnStart(const BFCode & aProgram)
	{
		onStartRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onStopRoutine
	 */
	inline const AvmProgram & getOnStopRoutine() const
	{
		return( onStopRoutine );
	}

	inline const BFCode & getOnStop() const
	{
		return( onStopRoutine.getCode() );
	}

	inline bool hasOnStop() const
	{
		return( onStopRoutine.hasCode() );
	}

	inline void setOnStop(const BFCode & aProgram)
	{
		onStopRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onIEnableRoutine
	 */
	inline const AvmProgram & getOnIEnableRoutine() const
	{
		return( onIEnableRoutine );
	}

	inline const BFCode & getOnIEnable() const
	{
		return( onIEnableRoutine.getCode() );
	}

	inline bool hasOnIEnable() const
	{
		return( onIEnableRoutine.hasCode() );
	}

	inline void setOnIEnable(const BFCode & aProgram)
	{
		onIEnableRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onEnableRoutine
	 */
	inline const AvmProgram & getOnEnableRoutine() const
	{
		return( onEnableRoutine );
	}

	inline const BFCode & getOnEnable() const
	{
		return( onEnableRoutine.getCode() );
	}

	inline bool hasOnEnable() const
	{
		return( onEnableRoutine.hasCode() );
	}

	inline void setOnEnable(const BFCode & aProgram)
	{
		onEnableRoutine.setCode( aProgram );
	}

	/**
	 * GETTER - SETTER
	 * onIDisableRoutine
	 */
	inline const AvmProgram & getOnIDisableRoutine() const
	{
		return( onIDisableRoutine );
	}

	inline const BFCode & getOnIDisable() const
	{
		return( onIDisableRoutine.getCode() );
	}

	inline bool hasOnIDisable() const
	{
		return( onIDisableRoutine.hasCode() );
	}

	inline void setOnIDisable(const BFCode & aProgram)
	{
		onIDisableRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onDisableRoutine
	 */
	inline const AvmProgram & getOnDisableRoutine() const
	{
		return( onDisableRoutine );
	}

	inline const BFCode & getOnDisable() const
	{
		return( onDisableRoutine.getCode() );
	}

	inline bool hasOnDisable() const
	{
		return( onDisableRoutine.hasCode() );
	}

	inline void setOnDisable(const BFCode & aProgram)
	{
		onDisableRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onIAbortRoutine
	 */
	inline const AvmProgram & getOnIAbortRoutine() const
	{
		return( onIAbortRoutine );
	}

	inline const BFCode & getOnIAbort() const
	{
		return( onIAbortRoutine.getCode() );
	}

	inline bool hasOnIAbort() const
	{
		return( onIAbortRoutine.hasCode() );
	}

	inline void setOnIAbort(const BFCode & aProgram)
	{
		onIAbortRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onAbortRoutine
	 */
	inline const AvmProgram & getOnAbortRoutine() const
	{
		return( onAbortRoutine );
	}

	inline const BFCode & getOnAbort() const
	{
		return( onAbortRoutine.getCode() );
	}

	inline bool hasOnAbort() const
	{
		return( onAbortRoutine.hasCode() );
	}

	inline void setOnAbort(const BFCode & aProgram)
	{
		onAbortRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onIRunRoutine
	 */
	inline const AvmProgram & getOnIRunRoutine() const
	{
		return( onIRunRoutine );
	}


	inline const BFCode & getOnIRun() const
	{
		return( onIRunRoutine.getCode() );
	}

	inline bool hasOnIRun() const
	{
		return( onIRunRoutine.hasCode() );
	}

	inline void setOnIRun(const BFCode & aProgram)
	{
		onIRunRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * onRunRoutine
	 */
	inline const AvmProgram & getOnRunRoutine() const
	{
		return( onRunRoutine );
	}

	inline const BFCode & getOnRun() const
	{
		return( onRunRoutine.getCode() );
	}

	inline bool hasOnRun() const
	{
		return( onRunRoutine.hasCode() );
	}

	inline void setOnRun(const BFCode & aProgram)
	{
		onRunRoutine.setCode( aProgram );
	}

	/**
	 * GETTER - SETTER
	 * onRtcRoutine
	 */
	inline const AvmProgram & getOnRtcRoutine() const
	{
		return( onRtcRoutine );
	}

	inline const BFCode & getOnRtc() const
	{
		return( onRtcRoutine.getCode() );
	}

	inline bool hasOnRtc() const
	{
		return( onRtcRoutine.hasCode() );
	}

	inline void setOnRtc(const BFCode & aProgram)
	{
		onRtcRoutine.setCode( aProgram );
	}


	/**
	 * GETTER - SETTER
	 * mSchedule
	 */
	inline const AvmProgram & getOnScheduleRoutine() const
	{
		return( onScheduleRoutine );
	}

	inline const BFCode & getOnSchedule() const
	{
		return( onScheduleRoutine.getCode() );
	}

	inline BFCode & getOnSchedule()
	{
		return( onScheduleRoutine.getCode() );
	}

	inline bool hasOnSchedule() const
	{
		return( onScheduleRoutine.hasCode() );
	}

	inline void setOnSchedule(const BFCode & aProgram)
	{
		onScheduleRoutine.setCode( aProgram );
	}

	inline bool hasUserRunningCode() const
	{
		return( hasOnRun() || hasOnRtc() || hasOnSchedule() );
	}


	/**
	 * GETTER
	 * mInitRoutine
	 * mEnableRoutine
	 * mRunRoutine
	 */
	inline bool hasInitOrRun() const
	{
		return( hasOnInit() || hasOnRun() );
	}

	inline bool hasOnInitOrEnableOrRun() const
	{
		return( hasOnInit() || hasOnEnable() || hasOnRun() );
	}


	/**
	 * GETTER
	 * on activity by opcode
	 */
	const AvmProgram & getOnActivityRoutine(AVM_OPCODE opCode) const;

	const BFCode & getOnActivity(AVM_OPCODE opCode) const;


	/**
	 * GETTER - SETTER
	 * mComponentFlag
	 * Structural decompositon
	 */
	bool isMainComponent() const
	{
		return( mMainComponentFlag );
	}

	void setMainComponent(bool isMainComponent = true)
	{
		mMainComponentFlag = isMainComponent;
	}

	bool isCompositeComponent() const
	{
		return( hasOnConcurrency() || getSpecifier().isComponentSystem() );
	}



	/**
	 * GETTER - SETTER
	 * mMutableScheduleFlag
	 * MOC Attribute for mutable Schedule
	 */
	bool isMutableSchedule() const
	{
		return( mMutableScheduleFlag );
	}

	void setMutableSchedule(bool isMutableSchedule = true)
	{
		mMutableScheduleFlag = isMutableSchedule;
	}

	/**
	 * TESTER
	 */
	bool isInlinableSchedule() const;


	/**
	 * GETTER - SETTER
	 * mConcurrency
	 */
	inline const AvmProgram & getOnConcurrencyRoutine() const
	{
		return( onConcurrencyRoutine );
	}

	inline const BFCode & getOnConcurrency() const
	{
		return( onConcurrencyRoutine.getCode() );
	}

	inline bool hasOnConcurrency() const
	{
		return( onConcurrencyRoutine.hasCode() );
	}

	inline void setOnConcurrency(const BFCode & aProgram)
	{
		onConcurrencyRoutine.setCode( aProgram );
	}

	inline const Operator * getOnConcurrencyOperator() const
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT(
				onConcurrencyRoutine.getCode() )
				<< " Concurrency Operator for "
				<< str_header( this ) << " !!!"
				<< SEND_EXIT;

		return( onConcurrencyRoutine.getCode()->getOperator() );
	}


	/**
	 * GETTER - SETTER
	 * mSynchronize
	 */
	inline const AvmProgram & getOnSynchronizeRoutine() const
	{
		return( onSynchronizeRoutine );
	}

	inline const BFCode & getOnSynchronize() const
	{
		return( onSynchronizeRoutine.getCode() );
	}

	inline bool hasOnSynchronize() const
	{
		return( onSynchronizeRoutine.hasCode() );
	}

	inline void setOnSynchronize(const BFCode & aProgram)
	{
		onSynchronizeRoutine.setCode( aProgram );
	}


	/**
	 * GETTER
	 * the Schedulability property
	 */
	inline bool isSchedulable() const
	{
		return( hasOnInit() && hasOnRun() );
	}


	/**
	 * GETTER - SETTER
	 * IOpcodeFamily
	 */
	virtual void updateOpcodeFamily() override;


	/**
	 * GETTER - SETTER
	 * mTableOfRouter4Instance
	 */
	inline TableOfRouter & getRouters4Instance()
	{
		return( mTableOfRouter4Instance );
	}

	inline const TableOfRouter & getRouters4Instance() const
	{
		return( mTableOfRouter4Instance );
	}

	inline bool hasRouter4Instance() const
	{
		return( mTableOfRouter4Instance.nonempty() );
	}

	inline void setRouters4Instance(const TableOfRouter & aRouterTable)
	{
		mTableOfRouter4Instance = aRouterTable;
	}


	inline void appendRouter4Instance(const Router & aRouter)
	{
		mTableOfRouter4Instance.append( aRouter );
	}


	inline Router & getRouter4Instance(std::size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(
				offset , mTableOfRouter4Instance.size() )
				<< SEND_EXIT;


		return( mTableOfRouter4Instance.get(offset) );
	}

	inline const Router & getRouter4Instance(std::size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(
				offset , mTableOfRouter4Instance.size() )
				<< SEND_EXIT;


		return( mTableOfRouter4Instance.get(offset) );
	}


	inline Router & getRouter4This()
	{
		AVM_OS_ASSERT_FATAL_EMPTY_COLLECTION_EXIT( mTableOfRouter4Instance )
				<< "Table of Router for Instance !!!"
				<< SEND_EXIT;
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasInstanceStaticThis() )
				<< "Unexpected an executable without machine< this > !!!"
				<< SEND_EXIT;

		return( mTableOfRouter4Instance.get(
				getInstanceStaticThis().getOffset() ) );
	}

	inline const Router & getRouter4This() const
	{
		AVM_OS_ASSERT_FATAL_EMPTY_COLLECTION_EXIT( mTableOfRouter4Instance )
				<< "Table of Router for Instance !!!"
				<< SEND_EXIT;
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasInstanceStaticThis() )
				<< "Unexpected an executable without machine< this > !!!"
				<< SEND_EXIT;

		return( mTableOfRouter4Instance.get(
				getInstanceStaticThis().getOffset() ) );
	}


	inline bool hasRouter4This() const
	{
		return( mTableOfRouter4Instance.nonempty()
				&& hasInstanceStaticThis()
				&& mTableOfRouter4Instance.get(
						getInstanceStaticThis().getOffset() ).valid() );
	}


	/**
	 * GETTER - SETTER
	 * mRouterTable4Prototype
	 */
	inline const Router & getRouter4Prototype(
			const ExecutableForm * aModel) const
	{
		if( mTableOfRouter4Instance.nonempty() )
		{
			for( const auto & itRouter : mTableOfRouter4Instance )
			{
				if( itRouter.valid()
					&& (itRouter.getMachine().getExecutable() == aModel)
					&& itRouter.getMachine().
							getSpecifier().isDesignPrototypeStatic() )
				{
					return( itRouter );
				}
			}
		}

		return( Router::nullref() );
	}

	inline const Router & getRouter4Prototype(
			const InstanceOfMachine & aMachine) const
	{
		return( getRouter4Prototype(aMachine.getExecutable()) );
	}


	/**
	 * GETTER - SETTER
	 * mTableOfRouter4Model
	 */
	inline TableOfRouter & getRouters4Model()
	{
		return( mTableOfRouter4Model );
	}

	inline const TableOfRouter & getRouters4Model() const
	{
		return( mTableOfRouter4Model );
	}

	inline bool hasRouter4Model() const
	{
		return( mTableOfRouter4Model.nonempty() );
	}

	inline void setRouters4Model(const TableOfRouter & aRouterTable)
	{
		mTableOfRouter4Model = aRouterTable;
	}


	inline void appendRouter4Model(const Router & aRouter)
	{
		mTableOfRouter4Model.append( aRouter );
	}


	inline Router & getRouter4Model(std::size_t offset)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(
				offset , mTableOfRouter4Model.size() )
				<< SEND_EXIT;

		return( mTableOfRouter4Model.get(offset) );
	}

	inline const Router & getRouter4Model(std::size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(
				offset , mTableOfRouter4Model.size() )
				<< SEND_EXIT;

		return( mTableOfRouter4Model.get(offset) );
	}


	inline const Router & getRouter4Model(const ExecutableForm * aModel) const
	{
		if( mTableOfRouter4Model.nonempty() )
		{
			for( const auto & itRouter : mTableOfRouter4Model )
			{
				if( itRouter.valid()
					&& (itRouter.getMachine().getExecutable() == aModel) )
				{
					return( itRouter );
				}
			}

		}

		return( Router::nullref() );
	}

	inline const Router & getRouter4Model(
			const InstanceOfMachine & aMachine) const
	{
		return( getRouter4Model(aMachine.getExecutable()) );
	}


	/**
	 * GETTER - SETTER
	 * mRdvCommunicationFlag
	 */
	inline bool hasRdvCommunication() const
	{
		return( mRdvCommunicationFlag );
	}

	void setRdvCommunication(bool aFlag = true)
	{
		mRdvCommunicationFlag = aFlag;
	}


	/**
	 * GETTER - SETTER
	 * mInputEnabledCommunicationFlag
	 * MOC Attribute for Communication
	 */
	bool isInputEnabledCommunication() const
	{
		return( mInputEnabledCommunicationFlag );
	}

	void setInputEnabledCommunication(bool isInputEnabled = true)
	{
		mInputEnabledCommunicationFlag = isInputEnabled;
	}



	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// STATIC ANALYSIS ATTRIBUTE
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * mRequiredData
	 */
	inline const TableOfInstanceOfData & getRequiredData() const
	{
		return( mRequiredData );
	}


	/**
	 * GETTER - SETTER
	 * mUselessData
	 */
	inline const TableOfInstanceOfData & getUselessData() const
	{
		return( mUselessData );
	}


	/**
	 * Control flow analysis
	 * source & targets Executable< [state]machine > for Transition
	 */
	inline void getOutgoingMachine(
			ListOfInstanceOfMachine & listOfMachine) const
	{
		for( std::size_t offset = 0 ; offset < getTransition().size() ; ++offset )
		{
			getTransition().rawAt(offset)->getTransitionTarget( listOfMachine );
		}
	}

	inline void getOutgoingTransition(
			ListOfAvmTransition & listOfTransition) const
	{
		AvmTransition * aTransition;

		for( std::size_t offset = 0 ; offset < getTransition().size() ; ++offset )
		{
			aTransition = getTransition().rawAt(offset);

			listOfTransition.append( aTransition );
		}
	}


	/**
	 * GETTER - SETTER
	 * mListOfBackwardReachableMachine
	 */
	inline void addBackwardReachableMachine(InstanceOfMachine * aMachine)
	{
		mBackwardReachableMachine.add_unique( aMachine );
	}

	inline void addBackwardReachableMachine(
			ListOfInstanceOfMachine & reachableMachines)
	{
		mBackwardReachableMachine.add_unique( reachableMachines );
	}


	inline ListOfInstanceOfMachine & getBackwardReachableMachine()
	{
		return( mBackwardReachableMachine );
	}

	inline const ListOfInstanceOfMachine & getBackwardReachableMachine() const
	{
		return( mBackwardReachableMachine );
	}


	bool containsBackwardReachableMachine(InstanceOfMachine * aMachine) const
	{
		return( mBackwardReachableMachine.contains(aMachine) );
	}

	inline bool hasBackwardReachableMachine() const
	{
		return( mBackwardReachableMachine.nonempty() );
	}


	inline void removeBackwardReachableMachine(InstanceOfMachine * aMachine)
	{
		if( mBackwardReachableMachine.nonempty() )
		{
			mBackwardReachableMachine.remove( aMachine );
		}
	}


	/**
	 * GETTER - SETTER
	 * mListOfBackwardReachableMachine
	 */
	inline void addBackwardReachableTransition(AvmTransition * aTransition)
	{
		mBackwardReachableTransition.add_unique( aTransition );
	}

	inline void addBackwardReachableTransition(
			ListOfAvmTransition & reachableTransitions)
	{
		mBackwardReachableTransition.add_unique( reachableTransitions );
	}


	inline ListOfAvmTransition & getBackwardReachableTransition()
	{
		return( mBackwardReachableTransition );
	}

	inline const ListOfAvmTransition & getBackwardReachableTransition() const
	{
		return( mBackwardReachableTransition );
	}


	bool containsBackwardReachableTransition(AvmTransition * aTransition) const
	{
		return( mBackwardReachableTransition.contains(aTransition) );
	}

	inline bool hasBackwardReachableTransition() const
	{
		return( mBackwardReachableTransition.nonempty() );
	}


	inline void removeBackwardReachableTransition(AvmTransition * aTransition)
	{
		if( mBackwardReachableTransition.nonempty() )
		{
			mBackwardReachableTransition.remove( aTransition );
		}
	}


	/**
	 * GETTER - SETTER
	 * mListOfForwardReachableMachine
	 */
	inline void addForwardReachableMachine(InstanceOfMachine * aMachine)
	{
		mForwardReachableMachine.add_unique( aMachine );
	}

	inline void addForwardReachableMachine(
			ListOfInstanceOfMachine & reachableMachines)
	{
		mForwardReachableMachine.add_unique( reachableMachines );
	}


	inline ListOfInstanceOfMachine & getForwardReachableMachine()
	{
		return( mForwardReachableMachine );
	}

	inline const ListOfInstanceOfMachine & getForwardReachableMachine() const
	{
		return( mForwardReachableMachine );
	}


	bool containsForwardReachableMachine(InstanceOfMachine * aMachine) const
	{
		return( mForwardReachableMachine.contains(aMachine) );
	}

	inline bool hasForwardReachableMachine() const
	{
		return( mForwardReachableMachine.nonempty() );
	}


	inline void removeForwardReachableMachine(InstanceOfMachine * aMachine)
	{
		if( mForwardReachableMachine.nonempty() )
		{
			mForwardReachableMachine.remove( aMachine );
		}
	}


	/**
	 * GETTER - SETTER
	 * mListOfForwardReachableMachine
	 */
	inline void addForwardReachableTransition(const AvmTransition * aTransition)
	{
		mForwardReachableTransition.add_unique( aTransition );
	}

	inline void addForwardReachableTransition(
			ListOfAvmTransition & reachableTransitions)
	{
		mForwardReachableTransition.add_unique( reachableTransitions );
	}


	inline ListOfAvmTransition & getForwardReachableTransition()
	{
		return( mForwardReachableTransition );
	}

	inline const ListOfAvmTransition & getForwardReachableTransition() const
	{
		return( mForwardReachableTransition );
	}


	bool containsForwardReachableTransition(
			const AvmTransition * aTransition) const
	{
		return( mForwardReachableTransition.contains(aTransition) );
	}

	inline bool hasForwardReachableTransition() const
	{
		return( mForwardReachableTransition.nonempty() );
	}


	inline void removeForwardReachableTransition(
			const AvmTransition * aTransition)
	{
		if( mForwardReachableTransition.nonempty() )
		{
			mForwardReachableTransition.remove( aTransition );
		}
	}


	/**
	 * GETTER - SETTER
	 * isReachableStateFlag
	 */
	bool isReachableState() const
	{
		return( isReachableStateFlag );
	}

	void setReachableState(bool aReachableStateFlag)
	{
		isReachableStateFlag = aReachableStateFlag;
	}


	/**
	 * Serialization
	 */
	void header(OutStream & out) const;

	void strHeader(OutStream & out) const override;

	static void toStream(OutStream & out, const TableOfRouter & aTableOfRouter,
			const std::string & sectionName = "router:");

	void toStream(OutStream & out) const override;

};


}

#endif /*EXECUTABLEFORM_H_*/
