/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FORMULACOVERAGEFILTER_H_
#define FORMULACOVERAGEFILTER_H_

#include <fam/coverage/BaseCoverageFilter.h>

#include <common/AvmPointer.h>
#include <common/Element.h>
#include <common/BF.h>

#include <collection/Bitset.h>
#include <collection/Typedef.h>

#include <fml/executable/ExecutableForm.h>

#include <sew/Configuration.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class AvmCode;
class ExecutionContext;
class WObject;
class SatSolver;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// FormulaData
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


class FormulaData  :  public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( FormulaData )
{

	AVM_DECLARE_CLONABLE_CLASS( FormulaData )


public:
	/**
	 * ATTRIBUTES
	 */
	BF formula;
	std::string label;
	avm_offset_t offset;

	Element * compiled;

	ListOfExecutionContext satEC;


public:
	FormulaData(const BF & aFormula, const std::string & aLabel,
			avm_offset_t anOffset, Element * favmFormula)
	: Element( CLASS_KIND_T( FormulaData ) ),
	formula( aFormula ),
	label( aLabel ),
	offset( anOffset ),

	compiled( favmFormula ),
	satEC( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~FormulaData()
	{
		//!! NOTHING
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */

	virtual void report(OutStream & os) const;


	inline std::string str() const
	{
		StringOutStream oss( AVM_NO_INDENT );

		toStream(oss);

		return( oss.str() );
	}

	inline void toStream(OutStream & os) const
	{
		os << TAB << "<< " << offset << ":" << label << ": "
				<< formula.str() << " >>" << EOL_FLUSH;
	}

	inline void toFscn(OutStream & os) const
	{
		os << TAB << str() << EOL << std::flush;
	}

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// FormulaCoverageFilter
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


class FormulaCoverageFilter :
		public AutoRegisteredCoverageProcessorUnit< FormulaCoverageFilter >
{

	AVM_DECLARE_CLONABLE_CLASS( FormulaCoverageFilter )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"avm::processor.FORMULA_COVERAGE",
			"avm::core.filter.FORMULA_COVERAGE" )
	// end registration


protected:
	/**
	 * ATTRIBUTES
	 */
	SolverDef::SOLVER_KIND mSolverKind;

	ExecutableForm mLocalExecutableForm;

	BF mTrigger;


	BFVector mFormulaTable;
	BFList mListOfUncoveredFormula;

	Bitset mFormulaTruthTable;
	VectorOfInt mFormulaLinkTable;


	BFVector mMocTable;
	BFList mListOfUnCoveredMoc;

	Bitset mMocTruthTable;
	VectorOfInt mMocLinkTable;

	AvmCoverageStatistics mMocCoverageStatistics;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	FormulaCoverageFilter(
			SymbexControllerUnitManager & aManager, WObject * wfParameterObject)
	: RegisteredCoverageProcessorUnit(aManager, wfParameterObject,
			AVM_PREPOST_FILTERING_STAGE, PRECEDENCE_OF_FORMULA_COVERAGE),
	mSolverKind( SolverDef::SOLVER_UNDEFINED_KIND ),
	mLocalExecutableForm( getConfiguration().getExecutableSystem() , 0 ),
	mTrigger( ),

	mFormulaTable( ),
	mListOfUncoveredFormula(),
	mFormulaTruthTable(),
	mFormulaLinkTable( ),

	mMocTable( ),
	mListOfUnCoveredMoc(),
	mMocTruthTable(),
	mMocLinkTable( ),
	mMocCoverageStatistics( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~FormulaCoverageFilter()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	virtual bool configureImpl();


	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const;


	/**
	 * postEval Filter
	 */
	virtual bool postfilter(ExecutionContext & anEC);


	////////////////////////////////////////////////////////////////////////////
	// CHECK FORMULA
	////////////////////////////////////////////////////////////////////////////
	bool checksatFormula(ExecutionContext * anEC,
			const BF & aFormula, FormulaData * aFD);

	void checkFormula(ExecutionContext * anEC);
	bool checkFormula(ExecutionContext * anEC, FormulaData * aFD);

	void checkFormulaAfter(ExecutionContext * anEC);
	bool checkFormulaAfter(ExecutionContext * anEC, FormulaData * aFD);


	////////////////////////////////////////////////////////////////////////////
	// CHECK MOC
	////////////////////////////////////////////////////////////////////////////

	bool checksatMoc(const BF & aMoc);

	void mocAppendFormulaLink(const BF & aMoc);
	void mocRemoveFormulaLink(const BF & aMoc);
	void mocUpdateUncoveredFormula();

	void checkMoc(ExecutionContext * anEC);


	/*
	 * GETTER
	 * mTrigger
	 */
	inline void setTrigger(const BF & aTrigger)
	{
		mTrigger = aTrigger;
	}

	inline BF & getTrigger()
	{
		return( mTrigger);
	}

	/*
	 * GETTER
	 * mVectorOfFormula
	 */
	BF appendFormula(const BF & aFormula,
			const std::string & label, Element * favmFormula = NULL);

	inline BF & getFormula(const std::string & label)
	{
		BFVector::iterator itForm = mFormulaTable.begin();
		BFVector::iterator endForm = mFormulaTable.end();
		for( ; itForm != endForm ; ++itForm )
		{
			if( (*itForm).to_ptr< FormulaData >()->label == label )
			{
				return( *itForm );
			}
		}

		return( BF::REF_NULL );
	}


	inline BFVector & getFormulaTable()
	{
		return( mFormulaTable );
	}


	/*
	 * GETTER
	 * mListOfUncoveredFormula
	 */
	inline const BFList & getListOfUnCoveredFormula() const
	{
		return( mListOfUncoveredFormula );
	}


	/*
	 * GETTER
	 * mVectorOfMoc
	 */
	BF appendMoc(const BF & aMoc,
			const std::string & label, Element * favmFormula = NULL);

	inline BFVector & getMocTable()
	{
		return( mMocTable );
	}

	BF buildMoc(const BF & aMoc);

};




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// FormulaCoverageFilter Information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class FormulaCoverageFilterInfo :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( FormulaCoverageFilterInfo )
{

	AVM_DECLARE_CLONABLE_CLASS( FormulaCoverageFilterInfo )


protected:
	/**
	 * ATTRIBUTES
	 */
	BFList mFormulaTable;

	BFList mMocTable;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	FormulaCoverageFilterInfo()
	: Element( CLASS_KIND_T( FormulaCoverageFilterInfo ) ),
	mFormulaTable( ),
	mMocTable( )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	FormulaCoverageFilterInfo(const FormulaCoverageFilterInfo & anInfo)
	: Element( anInfo ),
	mFormulaTable(anInfo.mFormulaTable),
	mMocTable( anInfo.mMocTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~FormulaCoverageFilterInfo()
	{
		//!! NOTHING
	}

	/*
	 * GETTER -- SETTER
	 * mFormulaTable
	 */
	inline void appendFormula(const BF & aFD)
	{
		mFormulaTable.append( aFD );
	}

	inline BFList & getFormulaTable()
	{
		return( mFormulaTable );
	}


	/*
	 * GETTER -- SETTER
	 * mMocTable
	 */
	inline void appendMoc(BF & aFD)
	{
		mMocTable.append( aFD );
	}

	inline void appendMoc(BFList & aTable)
	{
		mMocTable.append( aTable );
	}

	inline void appendMoc(BFVector & aTable)
	{
		mMocTable.append( aTable );
	}

	inline BFList & getMocTable()
	{
		return( mMocTable );
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & os) const;

	void toFscn(OutStream & os) const;

};



}

#endif /* FORMULACOVERAGEFILTER_H_ */
