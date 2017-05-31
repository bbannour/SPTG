/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef REFERENCECOUNTER_H_
#define REFERENCECOUNTER_H_

#include <util/avm_assert.h>
#include <util/avm_debug.h>
#include <util/avm_injector.h>

#include <base/ReferenceCounter.h>

#include <printer/OutStream.h>


namespace sep
{


class AvmObject :
		public ReferenceCounter,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AvmObject )
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmObject( )
	: ReferenceCounter( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmObject(const AvmObject & anObject)
	: ReferenceCounter( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmObject()
	{
		//!! NOTHING
	}


	/**
	 * AVM DEBUG REF COUNTER
	 */
	inline void AVM_DEBUG_REF_COUNTER(OutStream & os) const
	{
AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )
		os << " /* < ref: " << getRefCount() << " > */" << std::flush;
AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )
	}

	inline std::string AVM_DEBUG_REF_COUNTER() const
	{
		StringOutStream oss;

		AVM_DEBUG_REF_COUNTER(oss);

		return( oss.str() );
	}

	inline std::string strRefCount() const
	{
		return( OSS() << " /* < ref: " << getRefCount() << " > */" );
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

//	template< class OS_T >
//	OS_T & osStream(OS_T & os) const
//	{
//		toStream( os );
//
//		return( os );
//	}


	inline virtual OutStream & osStream(OutStream & os) const
	{
		toStream( os );

		return( os );
	}

	inline virtual StringOutStream & osStream(StringOutStream & os) const
	{
		toStream( os );

		return( os );
	}

	inline virtual PairOutStream & osStream(PairOutStream & os) const
	{
		toStream( os );

		return( os );
	}

	inline virtual TripleOutStream & osStream(TripleOutStream & os) const
	{
		toStream( os );

		return( os );
	}


	inline virtual void toStream(OutStream & os) const
	{
		//!! NOTHING
	}

	inline virtual void toStream(PairOutStream & os) const
	{
		toStream( os.OS1);
		toStream(os.OS2 );
	}

	inline virtual void toStream(TripleOutStream & os) const
	{
		toStream( os.OS1);
		toStream(os.OS2);
		toStream(os.OS3 );
	}


	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream( oss );

		return( oss.str() );
	}


	/**
	 * TRACE on DESTROY
	 * dbgDestroy
	 */
	inline void dbgDestroy() const
	{
		AVM_OS_WARN << "destroy< @ " << avm_address_t( this )
				<< " , " << std::setw(16) << "AvmObject" << " > :"
				<< std::flush << str_indent( this ) << std::endl;
	}

};


}

#endif /* REFERENCECOUNTER_H_ */
