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

#include "FormulaCoverageFilter.h"

#include <builder/Builder.h>

#include <collection/Bitset.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/type/TypeSpecifier.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>

#include <fam/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>

#include <util/ExecutionTime.h>



namespace sep
{


/**
 ***************************************************************************
prototype filter::formula_coverage as avm::core.filter.FORMULA_COVERAGE is
	section PROPERTY
		// Nombre de pas de calcul "cumulés" avant de débuter
		// la vérification de la couverture
		@begin_step = 0;

		// Arrète l'exécution dès que la couverture est complète
		@stop = true;

		// Arrète l'exécution au plutôt
		@minimize = true;

		// Arrète l'exécution du chemin courant dès qu'un objectif est atteint
		@break = true;

		// Elagage du graphe des scénarios à la fin de la vérification
		@slice = true;

		// Active l'utilisation d'heuristique
		@heuristic = true;

		// choix de l'heuristique de départ
		// basic | naive | smart | agressive
		@heuristic#start = 'basic';

		// Nombre d'essais d'heuristiques
		@heuristic#trials = 7;

		// Critère de satisfaction du succès des heuristiques
		// taux de couverte / nombre d'élément restant...
		@objective#rate = 95;
		@objective#rest = 5;


		@solver = 'CVC4';	// OMEGA | CVC4 | Z3 | YICES

	endsection PROPERTY

	section DATA
		( < Local Variable declaration >; )*
	endsection DATA

	section FORMULA
		( @label = < AvmCode >; )+
	endsection FORMULA

	section MOC
		( @moc = < AvmCode< label > >; )+
	endsection MOC
endprototype
 ***************************************************************************
 */

void printLinkTable(OutStream & os, const BFVector & aFormulaTable,
		VectorOfInt & aLinkTable, const std::string & title)
{
	os << title << "\n";

	avm_size_t endIdx = aFormulaTable.size();
	for( avm_size_t idx = 0; idx < endIdx ; ++idx )
	{
		os << "\t" << aLinkTable[idx] << ":> "
				<< aFormulaTable[idx].to_ptr< FormulaData >()->label << "\n"
				<< std::flush;
	}
}

void printTruthTable(OutStream & os, const BFVector & aFormulaTable,
		Bitset & aTruthTable, const std::string & title)
{
	os << title << "\n";

	avm_size_t endIdx = aFormulaTable.size();
	for( avm_size_t idx = 0; idx < endIdx ; ++idx )
	{
		os << "\t" << aTruthTable[idx] << ":> "
				<< aFormulaTable[idx].to_ptr< FormulaData >()->label << "\n"
				<< std::flush;
	}
}

void reportTable(OutStream & os, const BFVector & aFormulaTable,
		const std::string & title)
{
	os << TAB << title << EOL;

	avm_size_t endIdx = aFormulaTable.size();
	for( avm_size_t idx = 0; idx < endIdx ; ++idx )
	{
		if( aFormulaTable[idx].to_ptr< FormulaData >()->satEC.nonempty() )
		{
			aFormulaTable[idx].to_ptr< FormulaData >()->report(os);
		}
	}
}



bool FormulaCoverageFilter::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();

	mMocCoverageStatistics.resetCounter();

	WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));
	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string theSolverName = Query::getWPropertyString(thePROPERTY,
				"solver", SolverDef::strSolver(SolverDef::SOLVER_CVC4_KIND));
		if( theSolverName.empty() )
		{
			thePROPERTY->warningLocation(AVM_OS_WARN)
					<< "Unexpected empty solver engine kind !" << std::endl;
		}
		mSolverKind = SolverDef::toSolver(
				theSolverName, SolverDef::DEFAULT_SOLVER_KIND);
	}
	else
	{
		mConfigFlag = false;
	}


	WObject * theDATA = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("data", "DATA"));
	if( theDATA != WObject::_NULL_ )
	{
		getConfiguration().getExecutableSystem().initProcessExecutableForm(
				mLocalExecutableForm, theDATA->ownedSize());

		List< WObject * > listOfLocalVar;
		Query::getListWObject(theDATA, listOfLocalVar);

		TypeSpecifier aTypeSpecifier;

		List< WObject * >::iterator it = listOfLocalVar.begin();
		List< WObject * >::iterator itEnd = listOfLocalVar.end();
		for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
		{
			aTypeSpecifier = ENV.getBuilder().getCompiler().compileTypeSpecifier(
					&mLocalExecutableForm, (*it)->getQualifiedTypeNameID() );

//!![MIGRATION]
			BF anInstance( new InstanceOfData(
					IPointerDataNature::POINTER_STANDARD_NATURE,
					&mLocalExecutableForm, /*(*it)*/ NULL, aTypeSpecifier, offset) );
			mLocalExecutableForm.setData( offset , anInstance );
		}
	}
	else
	{
		getConfiguration().getExecutableSystem().
				initProcessExecutableForm(mLocalExecutableForm, 0);
	}


	avm_size_t errorCount = 0;

	WObject * theFORMULA = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("formula", "FORMULA"));

	if( theFORMULA != WObject::_NULL_ )
	{
		const BF & aTrigger = Query::getWPropertyValue(
				thePROPERTY, "trigger", BF::REF_NULL);
		if( aTrigger.valid() )
		{
//			mTrigger = ENV.getBuilder().build(
//					getConfiguration()->getMainExecutionData(),
//					mLocalExecutableForm, aTrigger);

			mTrigger = ENV.getBuilder().
					compileExpression(&mLocalExecutableForm, aTrigger);

AVM_IF_DEBUG_FLAG( CONFIGURING )
	AVM_OS_LOG << TAB << " --> trigger : " << aTrigger.str() << " <-- " << EOL
			<< TAB << " --> build trigger : " << mTrigger.str() << " <-- "
			<< EOL << EOL << std::flush;
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )
		}

		WObject::const_iterator itWfO = theFORMULA->owned_begin();
		WObject::const_iterator endWfO = theFORMULA->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( appendFormula((*itWfO)->getValue(),
						(*itWfO)->getNameID(), (*itWfO)).invalid() )
				{
					++errorCount;
				}
			}
		}
	}
	else
	{
		thePROPERTY->warningLocation(AVM_OS_WARN)
				<< "FORMULA section not found in filter< " +
				getParameterWObject()->getFullyQualifiedNameID() + " > !" << std::endl;

		mConfigFlag = false;
	}


	WObject * theMOC = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("moc", "MOC"));

	if( theMOC != WObject::_NULL_ )
	{
		WObject::const_iterator itWfO = theMOC->owned_begin();
		WObject::const_iterator endWfO = theMOC->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				if( appendMoc((*itWfO)->getValue(),
						(*itWfO)->getNameID(), (*itWfO)).invalid() )
				{
					++errorCount;
				}
			}
		}
	}

	mConfigFlag = (errorCount == 0) && mConfigFlag;

	return( mConfigFlag );
}



/*
 * GETTER
 * mVectorOfFormula
 */
BF FormulaCoverageFilter::appendFormula(const BF & aFormula,
		const std::string & label, Element * favmFormula)
{
//	BF aBuildFormula = ENV.getBuilder().build(
//			MainDataConfiguration::getInstance()->getMainExecutionContext()
//					->getAPExecutionData(), mLocalExecutableForm, aFormula);

	ENV.getBuilder().getAvmcodeCompiler().getSymbolTable().resetError();

	BF aBuildFormula = ENV.getBuilder().
			compileExpression(&mLocalExecutableForm, aFormula);

	if( ENV.getBuilder().getAvmcodeCompiler().getSymbolTable().hasZeroError()
			&& aBuildFormula.valid() )
	{
		BF aFD( new FormulaData(aBuildFormula, label,
				mFormulaTable.size(), favmFormula) );
		mFormulaTable.append( aFD );
		mListOfUncoveredFormula.append( aFD );


		mCoverageStatistics.mNumberOfElements = mFormulaTable.size();

		mFormulaTruthTable.resize(mCoverageStatistics.mNumberOfElements, false);
		mFormulaLinkTable.resize(mCoverageStatistics.mNumberOfElements, 0);

AVM_IF_DEBUG_FLAG( CONFIGURING )
	AVM_OS_LOG << TAB << " --> formula " << label << " : "
			<< aFormula.str() << " <-- " << EOL
			<< TAB << " --> build formula " << label << " : "
			<< aBuildFormula.str() << " <-- "
			<< EOL << EOL << std::flush;
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )

		return( aFD );
	}
	else
	{
		if( ENV.getBuilder().getAvmcodeCompiler().getSymbolTable().hasErrorMessage() )
		{
			AVM_OS_LOG << TAB << ENV.getBuilder().getAvmcodeCompiler().
					getSymbolTable().getErrorMessage() << EOL << std::flush;
		}

		AVM_OS_COUT << TAB << " --> build formula FAILED :> " << label
				<< " : " << aFormula.str() << " <-- " << EOL << std::flush;
		AVM_OS_LOG << TAB << " --> build formula FAILED :> " << label
				<< " : " << aFormula.str() << " <-- " << EOL << std::flush;


		return( BF::REF_NULL );
	}
}



/*
 * GETTER
 * mVectorOfMoc
 */
BF FormulaCoverageFilter::appendMoc(const BF & aMoc,
		const std::string & label, Element * favmFormula)
{
	BF aBuildMoc = buildMoc( aMoc );

	if( aBuildMoc.valid() )
	{
		BF aFD( new FormulaData(aBuildMoc, label,
				mMocTable.size(), favmFormula) );
		mMocTable.append( aFD );
		mListOfUnCoveredMoc.append( mMocTable.last() );


		mMocCoverageStatistics.mNumberOfElements = mMocTable.size();

		mMocTruthTable.resize( mMocCoverageStatistics.mNumberOfElements , false );
		mMocLinkTable.resize( mMocCoverageStatistics.mNumberOfElements , 0 );


		mocAppendFormulaLink( aBuildMoc );

AVM_IF_DEBUG_FLAG( CONFIGURING )
	AVM_OS_LOG << TAB << " --> moc " << label
			<< " : " << aMoc.str() << " <-- " << EOL
			<< TAB << " --> build moc " << label
			<< " : " << aBuildMoc.str() << " <-- "
			<< EOL << EOL << std::flush;
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )


		printLinkTable(AVM_OS_TRACE, mFormulaTable, mFormulaLinkTable,
				"Configuration of the Formula Link Table");

		return( aFD );
	}
	else
	{
		AVM_OS_LOG << TAB << " --> build moc FAILED :> " << label
				<< " : " << aMoc.str() << " <-- " << EOL << std::flush;

		return( BF::REF_NULL );
	}
}


BF FormulaCoverageFilter::buildMoc(const BF & aMoc)
{
	switch( aMoc.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			BFCode newMoc( aMoc.to_ptr< AvmCode >()->getOperator() );

			BF bfMoc;

			AvmCode::iterator itForm = aMoc.to_ptr< AvmCode >()->begin();
			AvmCode::iterator endForm = aMoc.to_ptr< AvmCode >()->end();
			for( ; itForm != endForm ; ++itForm )
			{
				if( (bfMoc = buildMoc(*itForm)).valid() )
				{
					newMoc->append( bfMoc );
				}
				else
				{
					return( BF::REF_NULL );
				}
			}

			return( newMoc );
		}

		case FORM_UFI_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			BF aFormula = getFormula(aMoc.str()) ;
			if( aFormula.valid() )
			{
				return( aFormula );
			}
			else
			{
				return( BF::REF_NULL );
			}
		}

		case FORM_EXEC_FILTER_FORMULA_DATA_KIND:
		default:
		{
			return( aMoc );
		}
	}
}


/*
 * REPORT
 */
void FormulaData::report(OutStream & os) const
{
	os << TAB << str() << EOL;

	ListOfExecutionContext::const_iterator it = satEC.begin();
	ListOfExecutionContext::const_iterator endIt = satEC.end();
	for( ; it != endIt ; ++it )
	{
		os << TAB2 << "==>E[?] " << (*it)->str_min() << EOL;
	}
	os << std::flush;
}


void FormulaCoverageFilter::reportDefault(OutStream & os) const
{
	reportHeader(os, "FORMULA COVERAGE ");


	if( mFormulaTable.nonempty() )
	{
		if( mCoverageStatistics.goalAchieved() )
		{
			os << TAB2 << "All the << " << mCoverageStatistics.mNumberOfElements
					<< " >> formulas are covered !" << EOL;
		}
		else
		{
			os << TAB2 << "Warning: all formulas are not covered !" << EOL;
			mCoverageStatistics.toStreamCoverageRate( os << TAB2,
					"Results: << ", " on "," >> are covered !\n" );

			if( isReportDetails() && mListOfUncoveredFormula.nonempty() )
			{
				os << TAB2 << "List of the << "
						<< mCoverageStatistics.getNumberOfUncovered()
						<<  " >> formulas non covered:" << EOL;

				BFList::const_iterator itForm = mListOfUncoveredFormula.begin();
				BFList::const_iterator endForm = mListOfUncoveredFormula.end();
				for( ; itForm != endForm ; ++itForm )
				{
					os << TAB2 << " ==>  " << (*itForm).str() << " <== " << EOL;
				}

				mCoverageStatistics.toStreamCoverageRate( os << TAB2,
						"Results: << ", " on "," >> are covered !\n" );
			}
		}

		if( mSliceFlag )
		{
			os << TAB2 << "Number of nodes cut back: " << mSliceCount << EOL;
		}

	}


	if( mMocTable.nonempty() )
	{
		os << EOL;
		if( mMocCoverageStatistics.goalAchieved() )
		{
			os << TAB2 << "All of the " << mMocTable.size()
					<< " MOCs are covered !" << EOL;
		}
		else
		{
			os << TAB2 << "Warning: all MOCs are not covered !" << EOL;
			mMocCoverageStatistics.toStreamCoverageRate( os << TAB2,
					"Results: << ", " on "," >> are covered !\n" );

			if( isReportDetails() && mListOfUnCoveredMoc.nonempty() )
			{
				os << TAB2 << "List of the << "
						<< mMocCoverageStatistics.getNumberOfUncovered()
						<<  " >> MOCs non covered:" << EOL;

				BFList::const_iterator itForm = mListOfUnCoveredMoc.begin();
				BFList::const_iterator endForm = mListOfUnCoveredMoc.end();
				for( ; itForm != endForm ; ++itForm )
				{
					os << TAB2 << " ==>  " << (*itForm).str() << " <== " << EOL;
				}

				mMocCoverageStatistics.toStreamCoverageRate( os << TAB2,
						"Results: << ", " on "," >> are covered !\n" );
			}
		}
	}

	if( isReportDetails() )
	{
		os << EOL_INCR_INDENT;
		reportTable(os, mFormulaTable, "FORMULA TABLE");
		os << EOL;
		reportTable(os, mMocTable, "MOC TABLE");
		os << DECR_INDENT;
	}

	////////////////////////////////////////////////////////////////////////////
	// SET EXIT CODE
	mCoverageStatistics.setExitCode();
}


bool FormulaCoverageFilter::postfilter(ExecutionContext & anEC)
{
	if( mCoverageStatistics.hasUncovered() )
	{
		ExecutionTime mExecutionTimeManager(false);
AVM_IF_DEBUG_FLAG( TIME )
	mExecutionTimeManager.start_time();
AVM_ENDIF_DEBUG_FLAG( TIME )


		if( mTrigger.valid() )
		{
			if( ENV.eval(anEC.getAPExecutionData(),
					anEC.getAPExecutionData()->getSystemRID(), mTrigger) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )
	AVM_OS_COUT << "mTrigger:> " << ENV.outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )
				if( ENV.outVAL.isEqualFalse() )
				{
					return( true );
				}
			}
		}

		checkFormula( & anEC );

AVM_IF_DEBUG_FLAG( TIME )
	AVM_OS_TRACE << "checkFormula< EC::id "
			<< anEC.getIdNumber() << " >" << std::endl;
	mExecutionTimeManager.finish_time();
	AVM_OS_TRACE << mExecutionTimeManager.time_stat();// << std::endl;
AVM_ENDIF_DEBUG_FLAG( TIME )
	}

	else if( not mStopFlag )
	{
		if( mTrigger.valid() )
		{
			if( ENV.eval(anEC.getAPExecutionData(),
					anEC.getAPExecutionData()->getSystemRID(), mTrigger) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )
	AVM_OS_COUT << "mTrigger:> " << ENV.outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )
				if( ENV.outVAL.isEqualFalse() )
				{
					return( true );
				}
			}
		}

		checkFormulaAfter( & anEC );
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CHECK FORMULA
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool FormulaCoverageFilter::checksatFormula(ExecutionContext * anEC,
		const BF & aFormula, FormulaData * aFD)
{
	BF condition = ExpressionConstructor::andExpr(
			anEC->refExecutionData().getPathCondition(), aFormula);

	if( SolverFactory::isStrongSatisfiable(mSolverKind, condition) )
	{
AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << TAB2 << "EC<" << anEC->getIdNumber()
			<< ">  |=  <" << aFD->label << "> " << aFormula.str()
			<< std::endl;

	AVM_OS_COUT << TAB2 << "EC<" << anEC->getIdNumber()
			<< ">  |=  <" << aFD->label << "> " << aFormula.str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

		anEC->getwFlags().addCoverageElementTrace();

		anEC->addInfo(*this, ExpressionConstructor::newString( aFD->label ));

		anEC->getUniqInformation()->getUniqFormulaCoverageFilterInfo()->
				appendFormula( INCR_BF(aFD) );

		aFD->satEC.append( anEC );

		mListOfPositiveEC.append( anEC );

		if( mBreakFlag && mMocTable.empty() )
		{
			anEC->getExecutionData()->setAEES( AEES_STMNT_EXIT );
		}

		return( true );
	}
	else
	{
		return( false );
	}
}




void FormulaCoverageFilter::checkFormula(ExecutionContext * anEC)
{
	bool needCheckMoc = false;

	FormulaData * itFD;
	BFList::iterator itForm = mListOfUncoveredFormula.begin();
	for( ; itForm != mListOfUncoveredFormula.end() ; )
	{
		itFD = (*itForm).to_ptr< FormulaData >();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> checkFormula " << itFD->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

		if( ((not mFormulaTruthTable[ itFD->offset ]) || (not mMinimizationFlag))
				&& checkFormula(anEC, itFD) )
		{
			mFormulaTruthTable[ itFD->offset ] = true;

			itForm = mListOfUncoveredFormula.erase(itForm);

			mCoverageStatistics.addCoveredElement();

			needCheckMoc = true;


AVM_IF_DEBUG_FLAG( PROCESSOR )
	mCoverageStatistics.toStreamCoverageRate(AVM_OS_TRACE << TAB,
			"Formula Coverage: " , "\n");
	AVM_OS_TRACE << REPEAT("********", 10) << std::endl;

	mCoverageStatistics.toStreamCoverageRate(AVM_OS_COUT << TAB,
			"Formula Coverage: " , "\n");
	AVM_OS_COUT << REPEAT("********", 10) << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
		}
		else
		{
			++itForm;
		}
	}


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	printTruthTable(AVM_OS_TRACE, mFormulaTable, mFormulaTruthTable,
			"Update of the Formula Truth Table");
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

	if( needCheckMoc )
	{
		if( mMocCoverageStatistics.hasUncovered() )
		{
			checkMoc( anEC );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	printTruthTable(AVM_OS_TRACE, mMocTable, mMocTruthTable,
			"Update of the MOC Truth Table");
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	printLinkTable(AVM_OS_TRACE, mFormulaTable, mFormulaLinkTable,
			"Update of the Formula Link Table");
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
}


bool FormulaCoverageFilter::checkFormula(
		ExecutionContext * anEC, FormulaData * aFD)
{
	avm_size_t succesCount = 0;

	ExecutionContext::child_iterator itEC = anEC->begin();
	ExecutionContext::child_iterator endEC = anEC->end();
	for( ; itEC != endEC ; ++itEC )
	{
		if( ENV.evalFormula(*(*itEC), &mLocalExecutableForm, aFD->formula) )
		{
			if( checksatFormula(*itEC, ENV.outVAL, aFD) )
			{
				++succesCount;

				if( mMinimizationFlag )
				{
					break;
				}
			}
		}
	}

	return( succesCount > 0 );
}



void FormulaCoverageFilter::checkFormulaAfter(ExecutionContext * anEC)
{
	FormulaData * itFD;
	BFVector::iterator itForm = mFormulaTable.begin();
	BFVector::iterator endForm = mFormulaTable.end();
	for( ; itForm != endForm ; ++itForm )
	{
		itFD = (*itForm).to_ptr< FormulaData >();

		if( checkFormulaAfter(anEC, itFD) )
		{
			mFormulaTruthTable[ itFD->offset ] = true;

			// OK
		}
	}
}


bool FormulaCoverageFilter::checkFormulaAfter(
		ExecutionContext * anEC, FormulaData * aFD)
{
	APExecutionData apED;
	avm_size_t succesCount = 0;

	// Recherche des formules couvertes par les fils de anEC
	ExecutionContext::child_iterator endEC = anEC->end();

	switch( aFD->formula.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const BFCode & aFormula = aFD->formula.bfCode();

			switch( aFormula->getAvmOpCode() )
			{
				case AVM_OPCODE_OBS :
				{
					const BFCode & evtFormula = aFormula->first().bfCode();

					const BF & constraintFormula = aFormula->second();

					switch( evtFormula->getAvmOpCode() )
					{
						case AVM_OPCODE_INPUT :
						case AVM_OPCODE_OUTPUT :
						{
							if( evtFormula->first().is< BaseInstanceForm >() )
							{
								BaseInstanceForm * ioInstance =
										evtFormula->first().to_ptr< BaseInstanceForm >();

								if( ioInstance->is< InstanceOfPort >() )
								{
									BF anExecFormula;

									ExecutionContext::child_iterator itEC = anEC->begin();
									for( ; itEC != endEC ; ++itEC )
									{
										apED = (*itEC)->getAPExecutionData();

										BFCode ioTrace = ENV.searchTraceIO(
												(*itEC)->getIOElementTrace(), evtFormula);

										if( ioTrace.valid() )
										{
											anExecFormula = ENV.ioSubst( apED,
													&mLocalExecutableForm, evtFormula,
													ioTrace, constraintFormula );

											if( checksatFormula(*itEC, anExecFormula, aFD) )
											{
												++succesCount;
												// OK
											}
										}
									}
								}
								else if( ioInstance->is< InstanceOfData >() )
								{
									ExecutionContext::child_iterator itEC = anEC->begin();
									for( ; itEC != endEC ; ++itEC )
									{
										apED = (*itEC)->getAPExecutionData();

										if( ENV.isAssigned(apED, apED->getSystemRID(),
												ioInstance->to< InstanceOfData >()) )
										{
											ENV.eval(apED, apED->getSystemRID(), constraintFormula);

											if( checksatFormula(*itEC, ENV.outVAL, aFD) )
											{
												++succesCount;
												// OK
											}
										}
									}
								}
								else
								{
									++succesCount;
									// OK
								}
							}

							break;
						}


						default:
						{
							ExecutionContext::child_iterator itEC = anEC->begin();
							for( ; itEC != endEC ; ++itEC )
							{
								apED = (*itEC)->getAPExecutionData();

								ENV.eval(apED, apED->getSystemRID(), evtFormula);

								if( ENV.outVAL.isEqualTrue() )
								{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> Constraint Formula:> " << constraintFormula.str()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

									ENV.evalCondition(constraintFormula);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << " ==> EC<" << (*itEC)->getIdNumber()
			<< "> |=?= anExecFormula:> " << ENV.outVAL.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

									if( checksatFormula(*itEC, ENV.outVAL, aFD) )
									{
										++succesCount;
										// OK
									}
								}
							}
							break;
						}

						break;
					}
				}
				default:
				{
					ExecutionContext::child_iterator itEC = anEC->begin();
					for( ; itEC != endEC ; ++itEC )
					{
						apED = (*itEC)->getAPExecutionData();

						ENV.eval(apED, apED->getSystemRID(), aFormula);

						if( checksatFormula(*itEC, ENV.outVAL, aFD) )
						{
							++succesCount;
							// OK
						}
					}

					break;
				}
			}

			break;
		}

		default:
		{
			ExecutionContext::child_iterator itEC = anEC->begin();
			for( ; itEC != endEC ; ++itEC )
			{
				apED = (*itEC)->getAPExecutionData();

				ENV.eval(apED, apED->getSystemRID(), aFD->formula);

				if( checksatFormula(*itEC, ENV.outVAL, aFD) )
				{
					++succesCount;
					// OK
				}
			}

			break;
		}
	}

	return( succesCount > 0 );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CHECK MOC
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool FormulaCoverageFilter::checksatMoc(const BF & aMoc)
{
	switch( aMoc.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const BFCode & aCode = aMoc.bfCode();

			switch ( aCode->getAvmOpCode() )
			{
				case AVM_OPCODE_NOT:
				{
					return( not checksatMoc(aCode->first()) );
				}

				case AVM_OPCODE_AND:
				case AVM_OPCODE_STRONG_SYNCHRONOUS:
				{
					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( not checksatMoc(*itForm) )
						{
							return( false );
						}
					}
					return( true );
				}

				case AVM_OPCODE_OR:
				case AVM_OPCODE_WEAK_SYNCHRONOUS:
				{
					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( checksatMoc(*itForm) )
						{
							return( true );
						}
					}
					return( false );
				}

				case AVM_OPCODE_XOR:
				case AVM_OPCODE_EXCLUSIVE:
				{
					avm_size_t nbTrue = 0;

					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( checksatMoc(*itForm) )
						{
							++nbTrue;
						}
					}
					return( nbTrue == 1 );
				}

				case AVM_OPCODE_NAND:
				{
					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( not checksatMoc(*itForm) )
						{
							return( true );
						}
					}
					return( false );
				}

				case AVM_OPCODE_NOR:
				{
					AvmCode::iterator itForm = aCode->begin();
					AvmCode::iterator endForm = aCode->end();
					for( ; itForm != endForm ; ++itForm )
					{
						if( checksatMoc(*itForm) )
						{
							return( false );
						}
					}
					return( true );
				}

				default:
				{
					return( false );
				}
			}
			return( false );
		}

		case FORM_EXEC_FILTER_FORMULA_DATA_KIND:
		{
			return( mFormulaTruthTable[ aMoc.to_ptr< FormulaData >()->offset ] );
		}

		default:
		{
			return( false );
		}
	}
}


void FormulaCoverageFilter::mocAppendFormulaLink(const BF & aMoc)
{
	switch( aMoc.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode::iterator itForm = aMoc.to_ptr< AvmCode >()->begin();
			AvmCode::iterator endForm = aMoc.to_ptr< AvmCode >()->end();
			for( ; itForm != endForm ; ++itForm )
			{
				mocAppendFormulaLink( *itForm );
			}
			break;
		}

		case FORM_EXEC_FILTER_FORMULA_DATA_KIND:
		{
			(mFormulaLinkTable[ aMoc.to_ptr< FormulaData >()->offset ])++;
			break;
		}

		default:
		{
			//!!! NOTHING
			break;
		}
	}
}

void FormulaCoverageFilter::mocRemoveFormulaLink(const BF & aMoc)
{
	switch( aMoc.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			AvmCode::iterator itForm = aMoc.to_ptr< AvmCode >()->begin();
			AvmCode::iterator endForm = aMoc.to_ptr< AvmCode >()->end();
			for( ; itForm != endForm ; ++itForm )
			{
				mocRemoveFormulaLink( *itForm );
			}
			break;
		}

		case FORM_EXEC_FILTER_FORMULA_DATA_KIND:
		{
			(mFormulaLinkTable[ aMoc.to_ptr< FormulaData >()->offset ])--;
			break;
		}

		default:
		{
			//!!! NOTHING
			break;
		}
	}
}

void FormulaCoverageFilter::mocUpdateUncoveredFormula()
{
	BFList::iterator itForm = mListOfUncoveredFormula.begin();
	for( ; itForm != mListOfUncoveredFormula.end() ; )
	{
		if( mFormulaLinkTable[ (*itForm).to_ptr< FormulaData >()->offset ] < 0 )
		{
			itForm = mListOfUncoveredFormula.erase(itForm);
		}
		else
		{
			++itForm;
		}
	}
}


void FormulaCoverageFilter::checkMoc(ExecutionContext * anEC)
{
	FormulaData * itFD;
	BFList::iterator itForm = mListOfUnCoveredMoc.begin();
	for( ; itForm != mListOfUnCoveredMoc.end() ; )
	{
		itFD = (*itForm).to_ptr< FormulaData >();

//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
		AVM_OS_TRACE << " ==> checkMoc " << itFD->str() << std::endl;
//AVM_ANDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

		if( ((not mMocTruthTable[ itFD->offset ]) || (not mMinimizationFlag))
				&& checksatMoc(itFD->formula) )
		{
			mMocCoverageStatistics.addCoveredElement();

AVM_IF_DEBUG_FLAG( PROCESSOR )
	mMocCoverageStatistics.toStreamCoverageRate(AVM_OS_TRACE,
			"Moc Coverage: ", " / ", " :> ");
	AVM_OS_TRACE << itFD->str() << std::endl;
	AVM_OS_TRACE << REPEAT("********", 10) << std::endl;

	mMocCoverageStatistics.toStreamCoverageRate(AVM_OS_TRACE,
			"Moc Coverage: ", " / ", " :> ");
	AVM_OS_COUT << itFD->str() << std::endl;
	AVM_OS_COUT << REPEAT("********", 10) << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )


			mMocTruthTable[ itFD->offset ] = true;

			mocRemoveFormulaLink( itFD->formula );


			anEC->getwFlags().addCoverageElementTrace();

			anEC->addInfo(*this, ExpressionConstructor::newString( itFD->label ));

			anEC->getUniqInformation()->
					getUniqFormulaCoverageFilterInfo()->appendMoc( *itForm );

			itFD->satEC.append( anEC );

			if( mBreakFlag )
			{
				anEC->getExecutionData()->setAEES( AEES_STMNT_EXIT );
			}

			itForm = mListOfUnCoveredMoc.erase(itForm);
		}
		else
		{
			++itForm;
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// FormulaCoverageFilter Information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * Serialization
 */
void FormulaCoverageFilterInfo::toStream(OutStream & os)  const
{
	if( mFormulaTable.nonempty() )
	{
		os << TAB << "FORMULA{" << EOL_INCR_INDENT;

		BFList::const_iterator itForm = mFormulaTable.begin();
		BFList::const_iterator endForm = mFormulaTable.end();
		for( ; itForm != endForm ; ++itForm )
		{
			(*itForm).to_ptr< FormulaData >()->toStream(os);
		}
		os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
	}

	if( mFormulaTable.nonempty() )
	{
		os << TAB << "FORMULA_MOC{" << EOL_INCR_INDENT;

		BFList::const_iterator itForm = mMocTable.begin();
		BFList::const_iterator endForm = mMocTable.end();
		for( ; itForm != endForm ; ++itForm )
		{
			(*itForm).to_ptr< FormulaData >()->toStream(os);
		}
		os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
	}
}

void FormulaCoverageFilterInfo::toFscn(OutStream & os) const
{
	if( mFormulaTable.nonempty() )
	{
		os << TAB << "FORMULA{" << EOL_INCR_INDENT;

		BFList::const_iterator itForm = mFormulaTable.begin();
		BFList::const_iterator endForm = mFormulaTable.end();
		for( ; itForm != endForm ; ++itForm )
		{
			(*itForm).to_ptr< FormulaData >()->toFscn(os);
		}
		os << DECR_INDENT_TAB << "}" << EOL << std::flush;
	}

	if( mMocTable.nonempty() )
	{
		os << TAB << "FORMULA_MOC{" << EOL_INCR_INDENT;

		BFList::const_iterator itForm = mMocTable.begin();
		BFList::const_iterator endForm = mMocTable.end();
		for( ; itForm != endForm ; ++itForm )
		{
			(*itForm).to_ptr< FormulaData >()->toFscn(os);
		}
		os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
	}
}





}
