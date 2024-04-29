
#include <filesystem>

using namespace std;
#include <base/ClassKindInfo.h>
#include <builder/Builder.h>
#include <builder/Loader.h>
#include <computer/EnvironmentFactory.h>
#include  <famcore/api/ProcessorUnitRepository.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/runtime/RuntimeLib.h>
#include <util/avm_vfs.h>
#include <fml/lib/AvmLang.h>
#include "fml/infrastructure/facades/Py_System.h"
#include "fml/infrastructure/facades/Py_StateMachine.h"
#include "fml/infrastructure/facades/Py_State.h"
#include "fml/infrastructure/facades/Py_Transition.h"

#include "sew/facades/Py_Engine.h"
#include "sew/facades/Py_Result.h"
#include "sew/facades/Py_WorkflowParameter.h"

using namespace std;
using namespace sep;

static void initializetmp(){
	VFS::LaunchPath = std::filesystem::current_path().string();
	ClassKindInfoInitializer::load();
	OutStream::load();
	XLIA_SYNTAX::load();
	ExpressionFactory::load();
	TypeManager::load();
	EnvironmentFactory::load();
	Builder::load();
	ExecutableLib::load();
	RuntimeLib::load();
}

string workflowstring = "workflow {\n"
		"	workspace [\n"
		"		root = './'\n"
		"		launch = './'\n"
		"		output = './'\n"
		"	]\n"
		"	director exploration {\n"
		"		manifest [\n"
		"			autoconf = true\n"
		"			autostart = true\n"
		"		]\n"
		"		project [\n"
		"			source = './'\n"
		"		]\n"
		"		supervisor {\n"
		"			limit [\n"
		"				step = 42\n"
		"			]\n"
		"			queue [\n"
		"				strategy = 'BREADTH_FIRST_SEARCH'\n"
		"			]\n"
		"			redundancy [\n"
		"				loop#detection#trivial = true\n"
		"			]\n"
		"			console [\n"
		"			]\n"
		"		}\n"
		"		worker [\n"
		"		]\n"
		"	}\n"
		"	symbex [\n"
		"		constraint_solver = 'Z3'\n"
		"	]\n"
		"	console [\n"
		"		verbose = 'SILENT'\n"
		"	]\n"
		"	developer [\n"
		"		log = 'monLog.log'\n"
		"		debug = 'myDebug.dbg'\n"
		"		level = 'HIGH'\n"
		"		flag = 'GOD_MODE'\n"
		"	]\n"
		"}\n"
		;

int main( int argc , char * argv[] )
{
	cout << "pyversity debug launch"<< endl;
	initializetmp();

	Py_System mySystem ("mysystem", "not_timed");
	cout << mySystem << endl;

	//Py_StateMachine sm1 ("Hello1");
	//Py_StateMachine sm2 ("Hello2");

	Py_StateMachine sm1 = mySystem.addStateMachine("Hello1");
	Py_StateMachine sm2 = mySystem.addStateMachine("Hello2");

	Py_InitialState& s10= sm1.addInitialState("Begin");
	Py_BaseState& s11 = sm1.addState("Middle");
	Py_FinalState& s12 = sm1.addFinalState("End");

	Py_InitialState& s20 = sm2.addInitialState("One");
	Py_BaseState& s21= sm2.addState("Two");
	Py_FinalState& s22 = sm2.addFinalState("Three");

	s10.addTransition("T01", s11);
	s11.addTransition("T12", s12);

	Py_WorkflowParameter myWorkflowParam = Py_WorkflowParameter();
	myWorkflowParam.load("workflow {\n workspace [\n root = \"./\"\n launch = \"./\"\n output = \"./\"\n ]\n director exploration {\n manifest [\n autoconf = true\n autostart = true\n ]\n project [\n source = \".\"\n ]\n supervisor {\n limit [\n step = 42\n ]\n queue [\n strategy = 'BREADTH_FIRST_SEARCH'\n ]\n redundancy [\n loop#detection#trivial\n = true\n ]\n console [\n ]\n }\n worker [\n ]\n }\nsymbex [\n constraint_solver = 'Z3'\n]\n console [\n verbose = 'SILENT'\n]\n developer [\n log = \"monLog.log\"\n debug = \"myDebug.dbg\"\n level = 'HIGH'\n flag = 'GOD_MODE'\n]\n}");

	Py_Engine myEngine= Py_Engine(myWorkflowParam);

	myEngine.setSystem(mySystem);
	myEngine.startEngine();
	return( 0);
}
