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
#include "TableOfData.h"

#include <fml/executable/InstanceOfData.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinContainer.h>

#include <fml/symbol/TableOfSymbol.h>


namespace sep
{


/**
 * GETTER - SETTER
 * mTable
 */
const BF & TableOfData::get(const InstanceOfData * anInstance) const
{
	switch( anInstance->getPointerNature() )
	{
		case IPointerDataNature::POINTER_STANDARD_NATURE:
		{
			return( mTable[ anInstance->getOffset() ] );
		}

		case IPointerDataNature::POINTER_UFI_OFFSET_NATURE:
		case IPointerDataNature::POINTER_UFI_RUNTIME_NATURE:
		{
			BF rvalue = mTable[ anInstance->getOffset() ];

			// NO +1 for << this >> which is the root of the path
			avm_size_t pathLength = anInstance->getDataPath()->size();
			avm_size_t * theOffsetPath = anInstance->getOffsetPath();
			for( avm_size_t k = 1 ; k < pathLength ; ++k )
			{
				rvalue.moveAt( theOffsetPath[k] );
			}

			return( rvalue[ theOffsetPath[pathLength] ] );
		}

		case IPointerDataNature::POINTER_UFI_MIXED_NATURE:
		{
			BF rvalue = mTable[ anInstance->getOffset() ];

			TableOfSymbol::iterator it = anInstance->getDataPath()->begin();
			TableOfSymbol::iterator itEnd = anInstance->getDataPath()->pred_end();
			for( ; it != itEnd ; ++it )
			{
				switch( (*it).getPointerNature() )
				{
					case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
					case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
					{
						rvalue.moveAt( (*it).getOffset() );

						break;
					}
					case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
					{
						if( (*it).getValue().isInteger() )
						{
							rvalue.moveAt( (*it).getValue().toInteger() );
						}
						else if( (*it).getValue().isFloat() )
						{
							rvalue.moveAt( (*it).getValue().toFloat() );
						}
						else
						{
							AVM_OS_FATAL_ERROR_EXIT
									<< "TableOfData::get:> unexpected "
										"NON-INTEGER ARRAY INDEX << "
									<< (*it).strValue()
									<< " >> in instance FQN-ID :>\n"
									<< (*it).toString( AVM_TAB1_INDENT )
									<< SEND_EXIT;

							return( BF::REF_NULL );
						}

						break;
					}
					default:
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "TableOfData::get:> Unexpected "
								"POINTER NATURE for the instance of data :>\n"
								<< anInstance->toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return( BF::REF_NULL );
					}
				}
			}

			switch( (*it).getPointerNature() )
			{
				case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
				case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
				{
					return( rvalue[ (*it).getOffset() ] );
				}
				case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
				{
					if( (*it).getValue().isInteger() )
					{
						return( rvalue[ (*it).getValue().toInteger() ] );
					}
					else if( (*it).getValue().isFloat() )
					{
						return( rvalue[ (*it).getValue().toFloat() ] );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "TableOfData::get:> unexpected "
									"NON-INTEGER ARRAY INDEX << "
								<< (*it).strValue()
								<< " >> in instance FQN-ID :>\n"
								<< (*it).toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return( BF::REF_NULL );
					}
				}
				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "TableOfData::get:> Unexpected "
								"POINTER NATURE for the instance of data :>\n"
							<< anInstance->toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return( BF::REF_NULL );
				}
			}
			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "TableOfData::get:> Unexpected "
					"POINTER NATURE for the instance of data :>\n"
					<< anInstance->toString( AVM_TAB1_INDENT )
					<< SEND_EXIT;
			return( BF::REF_NULL );
		}
	}

	return( BF::REF_NULL );
}


void TableOfData::set(const InstanceOfData * anInstance, const BF & aData) const
{
	switch( anInstance->getPointerNature() )
	{
		case IPointerDataNature::POINTER_STANDARD_NATURE:
		{
			mTable[ anInstance->getOffset() ] = aData;

			break;
		}
		case IPointerDataNature::POINTER_UFI_OFFSET_NATURE:
		case IPointerDataNature::POINTER_UFI_RUNTIME_NATURE:
		{
			BF rvalue = mTable[ anInstance->getOffset() ].getWritable();

			// NO +1 for << this >> which is the root of the path
			avm_size_t pathLength = anInstance->getDataPath()->size();
			avm_size_t * theOffsetPath = anInstance->getOffsetPath();
			for( avm_size_t k = 1 ; k < pathLength ; ++k )
			{
				rvalue.moveAtWritable( theOffsetPath[k] );
			}

			rvalue.set( theOffsetPath[pathLength] , aData);

			break;
		}
		case IPointerDataNature::POINTER_UFI_MIXED_NATURE:
		{
			BF rvalue = mTable[ anInstance->getOffset() ].getWritable();

			TableOfSymbol::iterator it = anInstance->getDataPath()->begin();
			TableOfSymbol::iterator itEnd = anInstance->getDataPath()->pred_end();
			for( ; it != itEnd ; ++it )
			{
				switch( (*it).getPointerNature() )
				{
					case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
					case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
					{
						rvalue.moveAtWritable( (*it).getOffset() );

						break;
					}
					case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
					{
						if( (*it).getValue().isInteger() )
						{
							rvalue.moveAtWritable( (*it).getValue().toInteger() );
						}
						else if( (*it).getValue().isFloat() )
						{
							rvalue.moveAtWritable( (*it).getValue().toFloat() );
						}
						else
						{
							AVM_OS_FATAL_ERROR_EXIT
									<< "TableOfData::set:> unexpected "
										"NON-INTEGER ARRAY INDEX << "
									<< (*it).strValue()
									<< " >> in instance FQN-ID :>\n"
									<< (*it).toString( AVM_TAB1_INDENT )
									<< SEND_EXIT;

							return;
						}

						break;
					}
					default:
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "TableOfData::set:> Unexpected "
								"POINTER NATURE for the instance of data :>\n"
								<< anInstance->toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return;
					}
				}
			}

			switch( (*it).getPointerNature() )
			{
				case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
				case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
				{
					//rvalue[ (*it).getOffset() ].makeWritable();
					rvalue.set( (*it).getOffset() , aData );

					break;
				}
				case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
				{
					if( (*it).getValue().isInteger() )
					{
						//rvalue[ (*it).getValue().toInteger() ].makeWritable();
						rvalue.set( (*it).getValue().toInteger() , aData );
					}
					else if( (*it).getValue().isFloat() )
					{
						//rvalue[ (*it).getValue().toFloat() ].makeWritable();
						rvalue.set( (*it).getValue().toFloat() , aData );
					}
					else
					{
						AVM_OS_FATAL_ERROR_EXIT
								<< "TableOfData::set:> unexpected "
									"NON-INTEGER ARRAY INDEX << "
								<< (*it).strValue()
								<< " >> in instance FQN-ID :>\n"
								<< (*it).toString( AVM_TAB1_INDENT )
								<< SEND_EXIT;

						return;
					}

					break;
				}
				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "TableOfData::set:> Unexpected "
								"POINTER NATURE for the instance of data :>\n"
							<< anInstance->toString( AVM_TAB1_INDENT )
							<< SEND_EXIT;

					return;
				}
			}
			break;
		}
		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "TableOfData::set:> Unexpected "
						"POINTER NATURE for the instance of data :>\n"
					<< anInstance->toString( AVM_TAB1_INDENT )
					<< SEND_EXIT;

			break;
		}
	}
}


/**
 * Serialization
 */
void TableOfData::toStream(OutStream & os) const
{
	os << TAB << "$[";
	for( const_iterator it = begin() ; it != end() ; ++it )
	{
		os << TAB2 << (*it).AVM_DEBUG_REF_COUNTER()
				<< " " << (*it).str() << EOL;
	}
	os << TAB << "]" << EOL_FLUSH;
}

void TableOfData::toStream(OutStream & os, const BFVector & vars) const
{
	avm_offset_t offset = 0;
	for( const_iterator it = begin() ; it != end() ; ++it, ++offset )
	{
		os << TAB << vars[offset].to_ptr< InstanceOfData >()->getNameID()
				<< " := " << (*it).AVM_DEBUG_REF_COUNTER()
				<< vars[offset].to_ptr< InstanceOfData >()->strValue()
				<< ";" << EOL_FLUSH;
	}
}


}
