/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 sept. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRANSITIONMOC_H_
#define TRANSITIONMOC_H_


namespace sep
{


class WObject;

class OutStream;


class TransitionMoc
{

public:
	enum MOE_RUN_MOC
	{
		// RUN DISABLE ENABLE
		MOE_UNDEFINED_RUN,

		MOE_RDE_RUN,
		MOE_DRE_RUN,
		MOE_DER_RUN,
	};


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TransitionMoc()
	: theMoeRun( MOE_UNDEFINED_RUN ),

	theUserPriorityEnabledFlag( false ),
	theUserPriorityMinFirstFlag( true ),

	theLcaEnabledFlag( false ),
	theLcaMinFirstFlag( false ),

	theSourceEnabledFlag( false ),
	theSourceMinFirstFlag( false ),

	theTargetEnabledFlag( false ),
	theTargetMinFirstFlag( false )
	{
		//!!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	TransitionMoc(MOE_RUN_MOC moeRun)
	: theMoeRun( moeRun ),

	theUserPriorityEnabledFlag( false ),
	theUserPriorityMinFirstFlag( true ),

	theLcaEnabledFlag( false ),
	theLcaMinFirstFlag( false ),

	theSourceEnabledFlag( false ),
	theSourceMinFirstFlag( false ),

	theTargetEnabledFlag( false ),
	theTargetMinFirstFlag( false )
	{
		//!!! NOTHING
	}

	TransitionMoc(MOE_RUN_MOC moeRun, bool user)
	: theMoeRun( moeRun ),

	theUserPriorityEnabledFlag( true ),
	theUserPriorityMinFirstFlag( user ),

	theLcaEnabledFlag( false ),
	theLcaMinFirstFlag( false ),

	theSourceEnabledFlag( false ),
	theSourceMinFirstFlag( false ),

	theTargetEnabledFlag( false ),
	theTargetMinFirstFlag( false )
	{
		//!!! NOTHING
	}

	TransitionMoc(MOE_RUN_MOC moeRun, bool user, bool lca)
	: theMoeRun( moeRun ),

	theUserPriorityEnabledFlag( true ),
	theUserPriorityMinFirstFlag( user ),

	theLcaEnabledFlag( true ),
	theLcaMinFirstFlag( lca ),

	theSourceEnabledFlag( false ),
	theSourceMinFirstFlag( false ),

	theTargetEnabledFlag( false ),
	theTargetMinFirstFlag( false )
	{
		//!!! NOTHING
	}

	TransitionMoc(MOE_RUN_MOC moeRun, bool user, bool lca, bool source)
	: theMoeRun( moeRun ),

	theUserPriorityEnabledFlag( true ),
	theUserPriorityMinFirstFlag( user ),

	theLcaEnabledFlag( true ),
	theLcaMinFirstFlag( lca ),

	theSourceEnabledFlag( true ),
	theSourceMinFirstFlag( source ),

	theTargetEnabledFlag( false ),
	theTargetMinFirstFlag( false )
	{
		//!!! NOTHING
	}

	TransitionMoc(MOE_RUN_MOC moeRun, bool user, bool lca, bool source, bool target)
	: theMoeRun( moeRun ),

	theUserPriorityEnabledFlag( true ),
	theUserPriorityMinFirstFlag( user ),

	theLcaEnabledFlag( true ),
	theLcaMinFirstFlag( lca ),

	theSourceEnabledFlag( true ),
	theSourceMinFirstFlag( source ),

	theTargetEnabledFlag( true ),
	theTargetMinFirstFlag( target )
	{
		//!!! NOTHING
	}


	TransitionMoc(WObject * moc)
	{
		setFlags(moc);
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TransitionMoc()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * Set all flags using old FSP form
	 */
	void setFlags(WObject * moc);


	/**
	 * GETTER - SETTER
	 * theMoeRun
	 */
	inline MOE_RUN_MOC getMoeRun() const
	{
		return( theMoeRun );
	}

	inline void setMoeRun(MOE_RUN_MOC aMocKind)
	{
		theMoeRun = aMocKind;
	}


	/**
	 * GETTER - SETTER
	 * theUserPriorityEnabledFlag
	 * theUserPriorityMinFirstFlag
	 */
	inline bool isUserPriorityEnabled() const
	{
		return( theUserPriorityEnabledFlag );
	}

	inline bool isUserPriorityMinFirst() const
	{
		return( theUserPriorityMinFirstFlag );
	}

	inline void setUserPriorityMinFirst(bool minFirst)
	{
		theUserPriorityEnabledFlag = true;
		theUserPriorityMinFirstFlag = minFirst;
	}


	/**
	 * GETTER - SETTER
	 * theLcaEnabledFlag
	 * theLcaMinFirstFlag
	 */
	inline bool isLcaEnabled() const
	{
		return( theLcaEnabledFlag );
	}

	inline bool isLcaMinFirst() const
	{
		return( theLcaMinFirstFlag );
	}

	inline void setLcaMinFirst(bool minFirst)
	{
		theLcaEnabledFlag = true;
		theLcaMinFirstFlag = minFirst;
	}


	/**
	 * GETTER - SETTER
	 * theSourceEnabledFlag
	 * theSourceMinFirstFlag
	 */
	inline bool isSourceEnabled() const
	{
		return( theSourceEnabledFlag );
	}

	inline bool isSourceMinFirst() const
	{
		return( theSourceMinFirstFlag );
	}

	inline void setSourceMinFirst(bool minFirst)
	{
		theSourceEnabledFlag = true;
		theSourceMinFirstFlag = minFirst;
	}


	/**
	 * GETTER - SETTER
	 * theTargetEnabledFlag
	 * theTargetMinFirstFlag
	 */
	inline bool isTargetEnabled() const
	{
		return( theTargetEnabledFlag );
	}

	inline bool isTargetMinFirst() const
	{
		return( theTargetMinFirstFlag );
	}

	inline void setTargetMinFirst(bool minFirst)
	{
		theTargetEnabledFlag = true;
		theTargetMinFirstFlag = minFirst;
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & out) const;


protected:
	/**
	 * ATTRIBUTE
	 */

	// TRANSITION ACTIVITY SCHEDULER
	MOE_RUN_MOC theMoeRun;


	// MULTI TRANSITION SCHEDULING
	// User specific priority number
	bool theUserPriorityEnabledFlag;
	bool theUserPriorityMinFirstFlag;

	// Implicit formalism priority
	bool theLcaEnabledFlag;
	bool theLcaMinFirstFlag;

	bool theSourceEnabledFlag;
	bool theSourceMinFirstFlag;

	bool theTargetEnabledFlag;
	bool theTargetMinFirstFlag;


};

} /* namespace sep */
#endif /* TRANSITIONMOC_H_ */
