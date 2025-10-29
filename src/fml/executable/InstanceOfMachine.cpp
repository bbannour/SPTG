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

#include "InstanceOfMachine.h"

#include <fml/common/SpecifierElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/ExecutableForm.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/TypeManager.h>


namespace sep
{

/**
 * GETTER
 * Unique Null Reference
 */
InstanceOfMachine & InstanceOfMachine::nullref()
{
	static InstanceOfMachine _NULL_(ExecutableForm::nullref_ptr(),
			Machine::nullref(), ExecutableForm::nullref(), nullptr, 0 );
	_NULL_.setModifier( Modifier::OBJECT_NULL_MODIFIER );
	_NULL_.setSpecifier( Specifier::OBJECT_NULL_SPECIFIER );

	return( _NULL_ );
}


std::string InstanceOfMachine::THIS_FQN_SUFFIX = ".$this";
std::string InstanceOfMachine::THIS_ID  = "$this";


/**
 * CONSTRUCTOR
 * Default
 */
InstanceOfMachine::InstanceOfMachine(ExecutableForm * aContainer,
		const Machine & astMachine, ExecutableForm & anExecutable,
		InstanceOfMachine * anInstanceModel, avm_offset_t anOffset)
: BaseInstanceForm(CLASS_KIND_T( InstanceOfMachine ),
		aContainer, astMachine, TypeManager::MACHINE, anOffset),
SpecifierImpl( astMachine ),

mExecutable( & anExecutable ),

mThisFlag( false ),

onCreateRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
		anExecutable , Routine::nullref() , "create"  , 0 ),
onStartRoutine( Specifier::SCOPE_ROUTINE_KIND ,
		anExecutable , Routine::nullref() , "init" , 0 ),

mPossibleDynamicInstanciationCount( 0 ),
mMaximalInstanceCount( 1 ),
mParamReturnTable( ),
mReturnOffset( 0 ),
mInstanceModel( anInstanceModel ),
mRuntimeRID( ),
mModifierAutoStart( true )
{
	updateFullyQualifiedNameID();
}


InstanceOfMachine::InstanceOfMachine(ExecutableForm * aContainer,
		const Machine & astMachine, ExecutableForm & anExecutable,
		InstanceOfMachine * anInstanceModel,
		avm_offset_t anOffset, const Specifier & aSpecifier)
: BaseInstanceForm(CLASS_KIND_T( InstanceOfMachine ),
		aContainer, astMachine, TypeManager::MACHINE, anOffset),
SpecifierImpl( aSpecifier ),

mExecutable( & anExecutable ),

mThisFlag( false ),

onCreateRoutine ( Specifier::SCOPE_ROUTINE_KIND ,
		anExecutable , Routine::nullref() , "create"  , 0 ),
onStartRoutine( Specifier::SCOPE_ROUTINE_KIND ,
		anExecutable , Routine::nullref() , "init" , 0 ),

mPossibleDynamicInstanciationCount( 0 ),
mMaximalInstanceCount( 1 ),
mParamReturnTable( ),
mReturnOffset( 0 ),
mInstanceModel( anInstanceModel ),
mRuntimeRID( ),
mModifierAutoStart( true )
{
	updateFullyQualifiedNameID();
}


/**
 * CONSTRUCTOR
 * for the instance << this >>
 */
InstanceOfMachine * InstanceOfMachine::newThis(ExecutableForm & anExecutable,
			InstanceOfMachine * anInstanceModel, avm_offset_t anOffset)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( anOffset == 0 )
			<< "Unexpected a non-zero offset< " << anOffset
			<< " > for the instance << this >> !!!" << std::endl
			<< str_header( anExecutable.getInstanceStatic() )
			<< str_header( anInstanceModel )
			<< SEND_EXIT;

	InstanceOfMachine * thisInstance = new InstanceOfMachine((& anExecutable),
			anExecutable.getAstMachine(), anExecutable, anInstanceModel, 0);

	thisInstance->getwSpecifier().setDesignInstanceStatic();
	thisInstance->setInstanciationCount(1);

	anInstanceModel->incrInstanciationCount();

	thisInstance->setAllNameID(
			thisInstance->getFullyQualifiedNameID() + THIS_FQN_SUFFIX,
			THIS_ID );

	thisInstance->setThis( true );

	return( thisInstance );
}


InstanceOfMachine * InstanceOfMachine::newInstanceModelThis(
		ExecutableForm * aContainer, const Machine & astMachine,
		ExecutableForm & anExecutable, InstanceOfMachine * anInstanceModel,
		avm_offset_t anOffset, const Specifier & aSpecifier)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( anOffset == 0 )
			<< "Unexpected a non-zero offset< " << anOffset
			<< " > for the instance << this >> !!!" << std::endl
			<< str_header( anExecutable.getInstanceStatic() )
			<< str_header( anInstanceModel )
			<< SEND_EXIT;

	InstanceOfMachine * thisInstance = new InstanceOfMachine(aContainer,
			astMachine, anExecutable, nullptr, anOffset, aSpecifier );

	thisInstance->setAllNameID(
			thisInstance->getFullyQualifiedNameID() + THIS_FQN_SUFFIX,
			THIS_ID );

	thisInstance->setThis( true );

	return( thisInstance );
}


/**
 * GETTER - SETTER
 * mParamReturnTable
 * mReturnOffset
 */
const BaseTypeSpecifier & InstanceOfMachine::getParamType(std::size_t offset) const
{
	return( hasExecutable()
			? refExecutable().rawParamVariable(offset)->getTypeSpecifier()
			: BaseTypeSpecifier::nullref() );
}


/**
 * SETTER
 * mFullyQualifiedNameID
 */
void InstanceOfMachine::updateFullyQualifiedNameID()
{
	std::string::size_type pos =
			mFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
	if( pos != std::string::npos )
	{
		setFullyQualifiedNameID( ( getSpecifier().isDesignModel() ? "model" :
				( getSpecifier().isDesignPrototypeStatic() ? "prot" : "inst" ) )
				+ mFullyQualifiedNameID.substr(pos) );
	}
}


/**
 * TESTER
 * mExecutable
 */
bool InstanceOfMachine::hasnotNullExecutable() const
{
	return( (mExecutable != nullptr) && mExecutable->isnotNullref() );
}



/**
 * GETTER - SETTER
 * mPossibleDynamicInstanciationCount
 */
void InstanceOfMachine::incrPossibleDynamicInstanciationCount(std::size_t offset)
{
	if( mInstanceModel != nullptr )
	{
		mInstanceModel->mPossibleDynamicInstanciationCount += offset;
	}
//	else
	{
		mPossibleDynamicInstanciationCount += offset;
	}

	if( mExecutable != nullptr )
	{
		mExecutable->incrPossibleDynamicInstanciationCount(offset);
	}
}


/**
 * Serialization
 */
void InstanceOfMachine::header(OutStream & out) const
{
	out << getModifier().toString() << getSpecifier().strFeature()
		<< getSpecifier().strDesign_not( Specifier::DESIGN_INSTANCE_KIND )
		<< "instance< id:" << getOffset();

	InstanceSpecifierPart::strMultiplicity(
			out, mInstanciationCount,
			mPossibleDynamicInstanciationCount,
			mMaximalInstanceCount, ", multiplicity: [ ", " ]");

//	if( mInstanciationCount != 1 )
//	{
//		out << ", init:" << mInstanciationCount;
//	}
//	if( mPossibleDynamicInstanciationCount > 0 )
//	{
//		out << ", dyna:" << mPossibleDynamicInstanciationCount;
//	}
//	if( hasMaximalNewInstance() )
//	{
//		out << ", max:" << getMaximalInstanceCount();
//	}

	if( isThis() )
	{
		out << ", this";
	}
	if( not isAutoStart() )
	{
		out << ", autostart = false";
	}

	out << " >";

AVM_IF_DEBUG_FLAG_OR( COMPILING , getSpecifier().isDesignInstanceStatic() )

	out << " &" << ( hasExecutable() ?
		refExecutable().getFullyQualifiedNameID() : "null< executable >" );

AVM_ENDIF_DEBUG_FLAG( COMPILING )

	out << " " << getFullyQualifiedNameID();
}

void InstanceOfMachine::strHeader(OutStream & out) const
{
	header( out );

	if( hasParam() )
	{
		out << "( ";
		TableOfData::const_iterator it = getParamReturnTable()->begin();
		out << (*it).str();

		TableOfData::const_iterator endIt = getParamReturnTable()->end();
		for( ++it ; it != endIt ; ++it )
		{
			out << ", " << (*it).str();
		}
		out << " )";
	}
}


void InstanceOfMachine::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	bool isEmpty = true;

	header( out << TAB );

	AVM_DEBUG_REF_COUNTER(out);

AVM_IF_DEBUG_FLAG( COMPILING )
	out << " {" << EOL; isEmpty = false;

	out << TAB << "//property:" << EOL;

	if( hasAstElement() )
	{
		out << TAB2 << "//compiled = "
			<< getAstFullyQualifiedNameID() << ";" << EOL;
	}

	out << TAB2 << "//container = "
		<< (hasContainer() ? getContainer()->getFullyQualifiedNameID() : "null")
		<< ";" << EOL;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	if( hasInstanceModel() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB2 << "//model = "
			<< getInstanceModel()->getFullyQualifiedNameID() << ";" << EOL;
	}

	if( hasAliasTarget() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "target = "
			<< str_header( getAliasTarget()->as_ptr< InstanceOfMachine >() )
			<< ";" << EOL;
	}

	if( hasCreatorContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#creator = " << getCreatorContainerRID().str()
			<< ";" << EOL;
	}

	if( hasRuntimeContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#container = " << getRuntimeContainerRID().str()
			<< ";" << EOL;
	}

	if( hasRuntimeRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#runtime = " << getRuntimeRID().str() << ";" << EOL;
	}

	if( hasMachinePath() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "path#machine:" << EOL;
		ArrayOfInstanceOfMachine::const_iterator it = getMachinePath()->begin();
		ArrayOfInstanceOfMachine::const_iterator endIt = getMachinePath()->end();
		for( ; it != endIt ; ++it )
		{
			out << TAB2 << (*it)->getFullyQualifiedNameID() << EOL;
		}
	}

	if( hasParamReturnTable() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		TableOfData::const_iterator it = getParamReturnTable()->begin();
		avm_offset_t offset = 0;
		avm_offset_t endOffset = 0;

		if( hasParam() )
		{
			out << TAB << "parameter:" << EOL;
			endOffset = getParamCount();
			for( offset = 0 ; offset < endOffset ; ++it , ++offset )
			{
				out << TAB2;
				if( hasExecutable() )
				{
					out << str_header( refExecutable().rawParamVariable(offset) );
				}
				else
				{
					out << "$" << offset;
				}

				if( (*it).valid() )
				{
					if( (*it).is< BaseInstanceForm >() )
					{
						out << " = &" << (*it).to<
							BaseInstanceForm >().getFullyQualifiedNameID();
					}
					else
					{
						out << " = " << (*it).str();
					}
				}
				out << ";" << EOL;
			}
		}

		if( hasReturn() )
		{
			out << TAB << "returns:" << EOL;
			endOffset = getReturnCount();
			for( offset = 0 ; offset < endOffset ; ++it , ++offset )
			{
				out << TAB2;
				if( hasExecutable() )
				{
					out << str_header( refExecutable().rawReturnVariable(offset) );
				}
				else
				{
					out << "$" << offset;
				}

				if( (*it).valid() )
				{
					if( (*it).is< BaseInstanceForm >() )
					{
						out << " = &" << (*it).to<
							BaseInstanceForm >().getFullyQualifiedNameID();
					}
					else
					{
						out << " = " << (*it).str();
					}
				}
				out << ";" << EOL;
			}
		}
	}

	if( hasParamReturn() && (hasOnCreate() || hasOnStart()) )
	{
		out << TAB << "moe:" << EOL;

	}
	if( hasOnCreate() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "@create{" << INCR2_INDENT;
		getOnCreate()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	if( hasOnStart() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "@start{" << INCR2_INDENT;
		getOnStart()->toStreamRoutine( out );
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}


	( isEmpty ? (out << ";") : (out << TAB << "}") ) << EOL_FLUSH;
}



}
