/*******************************************************************************
 * Copyright (c) 2020 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mai 2020
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include "SymbexServerWorkflowUtils.h"

#include <filesystem>
#include <fstream>

#include <util/avm_vfs.h>
#include <util/avm_string.h>

#include "SymbexServices.pb.h"

namespace sep
{

const std::string & SymbexServerWorkflowUtils::WORKSPACE_FOLDER_NAME = "tmp_grpc";
//		VFS::native_path(std::filesystem::temp_directory_path(), "tmp_grpc");

const std::string & SymbexServerWorkflowUtils::RAW_TEXT_SEW_FILE_PATH = "_tmp_raw_text_.sew";

const std::string & SymbexServerWorkflowUtils::RAW_TEXT_MODEL_FILE_PATH = "_tmp_raw_text_.xlia";

const std::string & SymbexServerWorkflowUtils::PATTERN_FILE_PATH = "${FILE_PATH}";

const std::string & SymbexServerWorkflowUtils::PATTERN_FILE_BASENAME = "${FILE_BASENAME}";

const std::string & SymbexServerWorkflowUtils::DEFAULT_GENERIC_SEW =
	"@sew< workflow , 1.0 >:"
	"\nworkflow {"
	"\n	workspace ["
	"\n		root   = '${WORKSPACE_FOLDER}'"
	"\n		launch = '${LAUNCH_FOLDER}'"
	"\n		output = 'output'"
	"\n		log    = 'log'"
	"\n		debug  = 'debug'"
	"\n	]"
	"\n	director default#symbex#engine 'as main execution objective' {"
	"\n		manifest ["
	"\n			autoconf  = true"
	"\n			autostart = true"
	"\n		]"
	"\n		project 'path of input model' ["
	"\n			ignore  = true"
	"\n			source = './'"
	"\n			model  = '" + PATTERN_FILE_PATH + "'"
	"\n		]"
	"\n		supervisor {"
	"\n			limit 'of graph exploration' ["
	"\n				step = -1"
	"\n				eval = -1"
	"\n			]"
	"\n			queue 'defining the exploration/search strategy' ["
	"\n				strategy = 'BFS'"
//	"\n				strategy = 'WEIGHT#BREADTH_FIRST_SEARCH'"
//	"\n				weight = 8"
//	"\n				heuristic = true"
	"\n			]"
	"\n			redundancy 'detection strategy' ["
	"\n				loop#detection#trivial = false"
	"\n			]"
	"\n			console ["
	"\n				format = '\\nstep:%1% , context:%2% , height:%3% , width:%4%%5%\\n'"
	"\n				report = '\\nstop:%1% , context:%2% , height:%3% , width:%4%%5%\\n'"
	"\n				spider#init = '\\n<$spider(%1%:%2%:%3%:%4%)%5%\\n'"
	"\n				spider#step = '\\n$spider(%1%:%2%:%3%:%4%)%5%\\n'"
	"\n				spider#stop = '\\n>$spider(%1%:%2%:%3%:%4%)%5%\\n'"
	"\n			]"
	"\n		}"
	"\n		worker ["
	"\n			serializer#symbex#trace#sequencediagram sequence_diagram_trace_generator {"
	"\n				property ["
	"\n					solver = 'CVC4'"
	"\n					format = 'SEQUENCE_DIAGRAM'"
	"\n					info#selection = 'ALL'"
	"\n					data#selection = 'MODIFIED'"
	"\n					numerizer = 'NONE '"
	"\n					normalize = true"
	"\n					print#initial#values = false"
	"\n					print#lifelines = false"
	"\n					trace#count = 42"
	"\n					one#trace#per#file = false"
	"\n				]"
	"\n				trace ["
	"\n					time = '[*]'"
	"\n					input#env = '[*]'"
	"\n					output#env = '[*]'"
	"\n					input = '[*]'"
	"\n					output = '[*]'"
	"\n					variable = '[*]'"
	"\n					machine = '[*]'"
	"\n					state = '[*]'"
	"\n					transition = '[*]'"
	"\n				]"
	"\n				format ["
	"\n					line#wrap#width = 80"
	"\n					line#wrap#separator = \"\\n\""
	"\n					execution#context#id = 'ec_%1%'"
	"\n					testcase#header = '== TRACE PATH %1% %2% ==\\n'"
	"\n					comment = '== %1% ==\\n'"
	"\n					participant = 'participant %1%\\n'"
	"\n					machine = 'hnote over of %2% #cyan : run %4%\\n'"
	"\n					statemachine = 'hnote over of %2% #teal : %4%\\n'"
	"\n					state = 'hnote over of %2% #gray : %4%\\n'"
	"\n					time = \"'hnote right of timestamp : time elapse %5%\\n\\n\""
	"\n					assign = 'note over %2% #yellow %3%%4%\\nend note\\n'"
	"\n					newfresh = 'hnote over of %2% newfresh(%3%) <- %4%\\n'"
	"\n					input#env = '-[#black]> %6% : %3%%4%\\n'"
	"\n					input#rdv = \"\""
	"\n					input#rdv = '%6% -[%8%]> %6% : <font color = %8%> %3% ? %4%\\n'"
	"\n					input = '%6% -[%8%]> %6% : <font color = %8%> %3% ? %4%\\n'"
	"\n					output#env = '<[#black]- %5% : %3%%4%\\n'"
	"\n					output#rdv = '%5% -[%8%]> %6% : <font color = %8%> %3%%4%\\n'"
	"\n					output = '%5% -[%8%]> %6% : <font color = %8%> %3%%4%\\n'"
	"\n					routine = 'hnote over of %2% #yellow : invoke %2%:%3%\\n'"
	"\n					transition = 'hnote over of %2% #yellow : fired %2%.%4%\\n'"
	"\n					node#condition = '\\nnote over of %2% #pink : NC : %1%\\n'"
	"\n					node#timed#condition = '\\nnote over of %2% #9ACD32 : NtC : %1%\\n'"
	"\n					path#condition = '\\nnote over %3%, %4% #pink : PC : %1%\\n'"
	"\n					path#timed#condition = '\\nnote over %3%, %4% #9ACD32 : PtC : %1%\\n'"
	"\n					value#parameter#begin = \"(\""
	"\n					value#parameter#separator = ' , '"
	"\n					value#parameter#end = \")\""
	"\n				]"
	"\n				vfs ["
	"\n					folder = 'basic'"
	"\n					file   = 'sd_trace.puml'"
	"\n				]"
	"\n			}"
	"\n			serializer#model#graphic model2graphic {"
	"\n				statemachine ["
	"\n					transition = true"
	"\n				]"
	"\n				transition ["
	"\n					statement = true"
	"\n				]"
	"\n				statement ["
	"\n					statement = true"
	"\n				]"
	"\n				vfs ["
	"\n					file = '" + PATTERN_FILE_BASENAME + ".puml'"
	"\n				]"
	"\n			}"
	"\n			serializer#model#graphviz model2graphviz {"
	"\n				vfs ["
	"\n					file = '" + PATTERN_FILE_BASENAME + "_graph.gv'"
	"\n				]"
	"\n			}"
	"\n			serializer#symbex#graphviz symbex2graphviz {"
	"\n				property ["
	"\n					info#selection = 'ALL'"
	"\n					data#selection = 'MODIFIED'"
	"\n				]"
	"\n				trace ["
	"\n					machine = '[*]'"
	"\n					com = '[*]'"
//	"\n					variable = '[*]'"
	"\n					path#condition = '[*]'"
	"\n					path#timed#condition = '[*]'"
	"\n				]"
	"\n				format ["
	"\n					node = '\\nEC%1% [%2%%3%\\n]'"
	"\n					node#label = '\\n\\tlabel=\"%2%%3%%4%\"'"
	"\n					node#header = 'ec_%1%< ev:%2% , h:%3% , w:%4% >\\n%6%'"
	"\n					node#data = '\\n\\n%3%%4%%5%%6%%2%%7%'"
	"\n					lifeline#state = '%2%:%4%'"
	"\n					path#condition = 'PC: %1%'"
	"\n					path#timed#condition = 'PtC: %1%'"
	"\n					node#condition = 'NC: %1%'"
	"\n					node#timed#condition = 'NtC: %1%'"
	"\n					assign = '%2%.%3% = %4%'"
	"\n					newfresh = 'newfresh(%2%:%3%) <- %4%'"
	"\n					input#env = 'INPUT %2%:%3%%4%'"
	"\n					input#rdv = 'input %2%:%3%%4%'"
	"\n					input = 'input %2%:%3%%4%'"
	"\n					output#env = 'OUTPUT %2%:%3%%4%'"
	"\n					output#rdv = 'output %2%:%3%%4%'"
	"\n					output = 'output %2%:%3%%4%'"
	"\n					routine = 'invoke %2%:%3%'"
	"\n					transition = 'fired %1%.%3%'"
	"\n					machine = 'run %2%:%3%'"
	"\n				]"
	"\n				css ["
	"\n					node#color = 'lightblue'"
	"\n					node#shape = 'ellipse'"
	"\n					node#style = 'filled'"
	"\n					node#passed#color = 'yellow'"
	"\n					node#passed#shape = 'ellipse'"
	"\n					node#passed#style = 'filled'"
	"\n					node#failed#color = 'red'"
	"\n					node#failed#shape = 'doubleoctagon'"
	"\n					node#failed#style = 'filled'"
	"\n					node#inconclusive#color = 'orange'"
	"\n					node#inconclusive#shape = 'octagon'"
	"\n					node#inconclusive#style = 'filled'"
	"\n					node#aborted#color = 'red'"
	"\n					node#aborted#shape = 'octagon'"
	"\n					node#aborted#style = 'filled'"
	"\n					node#warning#color = 'orange'"
	"\n					node#warning#shape = 'ellipse'"
	"\n					node#warning#style = 'filled'"
	"\n					node#error#color = 'red'"
	"\n					node#error#shape = 'ellipse'"
	"\n					node#error#style = 'filled'"
	"\n					node#alert#color = 'red'"
	"\n					node#alert#shape = 'ellipse'"
	"\n					node#alert#style = 'filled'"
	"\n					node#exit#color = 'orange'"
	"\n					node#exit#shape = 'tripleoctagon'"
	"\n					node#exit#style = 'filled'"
	"\n					node#redundancy#source#color = 'green'"
	"\n					node#redundancy#source#shape = 'cds'"
	"\n					node#redundancy#source#style = 'filled'"
	"\n					node#redundancy#target#color = 'greenyellow'"
	"\n					node#redundancy#target#shape = 'septagon'"
	"\n					node#redundancy#target#style = 'filled'"
	"\n					path#passed#color = 'lawngreen'"
	"\n					path#passed#shape = 'tripleoctagon'"
	"\n					path#passed#style = 'filled'"
	"\n					path#failed#color = 'red'"
	"\n					path#failed#shape = 'doubleoctagon'"
	"\n					path#failed#style = 'filled'"
	"\n					path#inconclusive#color = 'orange'"
	"\n					path#inconclusive#shape = 'octagon'"
	"\n					path#inconclusive#style = 'filled'"
	"\n					path#aborted#color = 'red'"
	"\n					path#aborted#shape = 'octagon'"
	"\n					path#aborted#style = 'filled'"
	"\n				]"
	"\n				vfs ["
	"\n					file = 'symbex_output.gv'"
	"\n				]"
	"\n			}"
	"\n		]"
	"\n		output 'standard analysis file' ["
	"\n			filename       = '" + PATTERN_FILE_BASENAME + "_%1%'"
	"\n			specification  = '" + PATTERN_FILE_BASENAME + ".xlia'"
	"\n			executable     = '" + PATTERN_FILE_BASENAME + ".fexe'"
	"\n			initialization = '" + PATTERN_FILE_BASENAME + "_init.fet'"
	"\n			scenarii       = '" + PATTERN_FILE_BASENAME + ".fscn'"
	"\n		]"
	"\n	}"
	"\n	symbex 'option' ["
	"\n		name_id_separator = \"_\""
	"\n		newfresh_param_name_pid = true"
	"\n		pretty_printer_var_name = true"
	"\n		time_name_id = '$time'"
	"\n		time_initial_value = 0"
	"\n		delta_name_id = '$delay'"
	"\n		delta_initial_value = 0"
	"\n		node_condition_enabled = false  "
	"\n		separation_of_pc_disjunction = false"
	"\n		check_pathcondition_satisfiability = true"
	"\n		//strongly_check_pathcondition_satisfiability = true"
	"\n		constraint_solver = 'CVC4'"  // Z3
	"\n	]"
	"\n	console ["
	"\n		verbose = 'MEDIUM'"
	"\n	]"
	"\n	shell ["
	"\n		stop = 'symbex.stop'"
	"\n	]"
	"\n	developer 'tuning options' ["
	"\n		log   = 'symbex.log'"
	"\n		debug = 'symbex.dbg'"
	"\n		level = 'MEDIUM'"
//	"\n		flag  = 'PARSING'"
//	"\n		flag  = 'COMPILING'"
//	"\n		flag  = 'COMPUTING'"
//	"\n		flag  = 'STATEMENT'"
//	"\n		flag  = 'STATEMENT_ASSIGNMENT'"
	"\n	]"
	"\n}";


std::string SymbexServerWorkflowUtils::prepareSEW(
		const std::string & textualSEW, const std::string & sewPath)
{
	std::string basename = VFS::basename(sewPath);

	std::string preparedSEW = textualSEW;

	StringTools::replaceAll(preparedSEW,
			"${WORKSPACE_FOLDER}", VFS::WorkspaceRootPath);

	StringTools::replaceAll(preparedSEW, "${LAUNCH_FOLDER}", VFS::ProjectPath);

	StringTools::replaceAll(preparedSEW, "${FILE_BASENAME}", basename);

	StringTools::replaceAll(preparedSEW, "${FILE_PATH}"    , sewPath);


	VFS::WorkflowPath = VFS::native_path(RAW_TEXT_SEW_FILE_PATH, VFS::ProjectPath);

	std::ofstream modelStream;
	modelStream.open(VFS::WorkflowPath, std::ios_base::out);
	if( modelStream.good() )
	{
		modelStream << preparedSEW;

		modelStream.close();
	}


	return preparedSEW;
}



bool SymbexServerWorkflowUtils::prepareWorkspaceFolder()
{
	VFS::ProjectPath = VFS::WorkspaceRootPath =
			VFS::native_path(WORKSPACE_FOLDER_NAME, VFS::LaunchPath);

	return( VFS::checkWritingFolder(VFS::WorkspaceRootPath) );
}


std::string SymbexServerWorkflowUtils::saveRawTextModel(
		const std::string & rawTextModel)
{
	std::string rawTextModelFilePatth =
			VFS::native_path(RAW_TEXT_MODEL_FILE_PATH, VFS::ProjectPath);

	std::ofstream modelStream;
	modelStream.open(rawTextModelFilePatth, std::ios_base::out);
	if( modelStream.good() )
	{
		modelStream << rawTextModel;

		modelStream.close();

		return rawTextModelFilePatth;
	}
	else
	{
		return "";
	}
}


std::string SymbexServerWorkflowUtils::getSEW(
		const grpc::ModelDefinitionRequest * request,
		const std::string & modelFileLocation)
{
	std::string workflowRawText;

	if( request->workflow_alt_case()
		== ::sep::grpc::ModelDefinitionRequest::kWorkflowRawText )
	{
		workflowRawText = request->workflow_raw_text();
	}
	else
	{
		std::string workflowFileLocation = request->workflow_raw_text();

		if( (not workflowFileLocation.empty())
			&& VFS::checkReadingFile( workflowFileLocation ) )
		{
			VFS::WorkflowPath = workflowFileLocation;
		}
	}

	if( workflowRawText.empty() )
	{
		if( VFS::checkReadingFile( VFS::WorkflowPath ) )
		{
			std::ifstream sewStream;
			sewStream.open(VFS::WorkflowPath);
			if( sewStream.good() )
			{
				std::stringstream buffer;
				buffer << sewStream.rdbuf();

				workflowRawText = buffer.str();

				sewStream.close();
			}
		}
	}

	if( workflowRawText.empty() )
	{
		workflowRawText = SymbexServerWorkflowUtils::DEFAULT_GENERIC_SEW;
	}

	if( not workflowRawText.empty() )
	{
		return prepareSEW(workflowRawText, modelFileLocation);
	}

	return( "" );
}


} /* namespace sep */

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */
