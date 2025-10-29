/*
 * StaticNullReference.h
 *
 *  Created on: 18 janv. 2018
 *      Author: lapitre_is148245
 */

#ifndef BASE_STATICNULLREFERENCE_H_
#define BASE_STATICNULLREFERENCE_H_

namespace sep
{

template< class T >
class StaticNullReference
{

public:
	/**
	 * DEFAULT NULL REFERENCE
	 */
//	static T _NULL_;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	StaticNullReference()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~StaticNullReference()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static T * nullref_ptr()
	{
		return( & T::nullref() );
	}


	/**
	 * VALIDITY TEST
	 * _NULL_
	 */
	inline bool isNullref() const
	{
		return( this == (& T::nullref()) );
	}

	inline bool isnotNullref() const
	{
		return( this != (& T::nullref()) );
	}


	/**
	 * cast to reference
	 */
	inline static const T & REF(const T * aPtr)
	{
		return( (aPtr != nullptr) ?  (* aPtr)  :  T::nullref() );
	}

};


} /* namespace sep */

#endif /* BASE_STATICNULLREFERENCE_H_ */
