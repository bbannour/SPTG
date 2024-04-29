/******************************************************************************
 * ConstraintsInferenceModule.h
 *
 *  Created on: 29 sept. 2017
 *  Author: IB252693
 *
 *  Imen Boudhiba (CEA LIST) imen.boudhiba@cea.fr
 *
 ******************************************************************************/

#ifndef FAM_CONTRIB_CONSTRAINTSINFERENCEMODULE_H_
#define FAM_CONTRIB_CONSTRAINTSINFERENCEMODULE_H_

#include  <famcore/api/AbstractProcessorUnit.h>

#include <common/BF.h>
#include <collection/BFContainer.h>
#include <collection/Typedef.h>
#include <fml/numeric/Integer.h>
#include <fml/builtin/String.h>
#include <fml/expression/AvmCode.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/workflow/WObject.h>



#include <sew/Workflow.h>


namespace sep{



class ConstraintsInferenceModule : public AutoRegisteredProcessorUnit < ConstraintsInferenceModule >
{

	AVM_DECLARE_CLONABLE_CLASS( ConstraintsInferenceModule )


		/**
		 * PROCESSOR FACTORY
		 * for automatic registration in the processor repository
		 * the [ [ FULLY ] QUALIFIED ] NAME ID
		 */
		AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
				"Functions_Contracts_Inference",
				CONS_WID2("constraints", "inference") )
		// end registration

protected:
    /**
     * ATTRIBUTE
     */

	avm_integer_t mCallIndex;

	String mFunctionCalls;

	String mFunctionSigs;

	List< ExecutionContext * > mCurrentPathECs;

	BFVector mAllDependancyVariables;

	VectorOfString mAllReturnVariables;

	VectorOfString mAllCalledFunNames;

	VectorOfString mAllxLIAtypes;

	VectorOfString mAllCtypes;


public:
    /**
     * CONSTRUCTOR
     */
	ConstraintsInferenceModule(SymbexControllerUnitManager & aManager, const WObject * aParameterForm)
    : AutoRegisteredProcessorUnit(aManager, aParameterForm, AVM_POST_PROCESSING_STAGE ),
	mCallIndex( -1 ),
	mFunctionCalls( "" ),
	mFunctionSigs( "" ),
	mCurrentPathECs( ),
	mAllDependancyVariables( ),
	mAllReturnVariables( ),
	mAllCalledFunNames( ),
	mAllxLIAtypes( ),
	mAllCtypes( )

	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ConstraintsInferenceModule()
	{

	}

	/**
	 * CONFIGURE allows to take into account user's parameters: at the moment, it takes as input ... a completer
	 */
	bool configureImpl() override;

	/**
	 * REPORT TRACE
	 */
	virtual void reportDefault(OutStream & os) const override;

	////////////////////////////////////////////////////////////////////////////
	// PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preProcessing
	 */
	//virtual bool preprocess();

	/**
	 * postprocessing
	 */
	virtual bool postprocess() override;

	virtual bool postprocessLeaf(ExecutionContext & leafEC,
			//OutStream & out1File,
			OutStream & out2File);

	//void ProgramVars(ArrayBF * prog, BFVector & progvars);

	void normalizeSigsStack(BuiltinVector & sigsStack);

	void normalizeCallStack(BuiltinVector & callStack);

	void normalizeExpression(std::string & expression);

	void normalizeArgumentCall(const BuiltinVector & callStack, std::string & callArg);

	void collectAllProgsVars(const BuiltinVector & Programs, BFVector & AllVars);
	void collectDependancyProgramVariables(const BF & PC, const BuiltinVector & Programs, BFVector & AllDepVars);

	void collectReturnVariables(
			const BuiltinVector & Programs, VectorOfString & allReturnVars);

	void inOutCallsFormula(const BuiltinVector & Programs, BF &ProgramsinOutEquality);

	void ToACSL( OutStream & out2File,
			const BuiltinVector & callStack, const BF & pathCondition,
			const ExecutionContext & leafEC );

	void toAcsl_header(OutStream & out2File, const ExecutionContext & leafEC);

	void toAcsl_variableDeclaration( OutStream & out2File,
			const BuiltinVector & callStack, const BF & pathCondition);

	void toAcsl_callset(OutStream & out2File,
			const BuiltinVector & callStack);


	void toAcsl_pathCondition(OutStream & out2File,
			const BF & pathCondition, const BuiltinVector & callStack);

	void toAcsl_preImpliesPost( OutStream & out2File,
			const BuiltinVector & callStack);

	BF toAcsl_clean( const BF & constraint,
			const BFVector & variables);

	BF builtHypothesis( const ArrayBF & currentCallTrace,
				const BF & pathCondition);
	BF builtRequirement( const ArrayBF & currentCallTrace,
					const BF & pathCondition);
	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preFiltering
	 */
	// virtual bool prefilter(ExecutionContext & anEC);

	/**
	 * postFiltering
	 * Every post filter has to implement this method
	 */
	//  virtual bool postfilter();

	// virtual bool postfilter(ExecutionContext & anEC);



  };



}
#endif /* FAM_CONTRIB_CONSTRAINTSINFERENCEMODULE_H_ */
