/*
 * CommunicationGraphSerializer.cpp
 *
 *  Created on: 2 mai 2019
 *      Author: xavier
 */

#include  <famcore/serializer/CommunicationGraphSerializer.h>
#include "fml/infrastructure/System.h"
#include "fml/infrastructure/CompositePart.h"
#include "fml/infrastructure/InteractionPart.h"
#include "collection/BFContainer.h"
#include "fml/infrastructure/ComProtocol.h"
#include "fml/infrastructure/ComRoute.h"

using namespace std;
namespace sep {

string CommunicationGraphSerializer::format(const System & aSystem){
	//format :
	//header
	//submachine compositions
	//connectors
	string resultString="";
	resultString+=CommunicationGraphSerializer::FILE_HEADER;
	resultString+=formatComposition(aSystem);
	resultString+="\n";

	resultString+=CommunicationGraphSerializer::FILE_FOOTER;
	return resultString;
}

string CommunicationGraphSerializer::formatInteractions(const Machine& aMachine){
	string resultString ="";
	if(aMachine.hasInteraction()){
		InteractionPart::CollectionOfConnector_t connectors = aMachine.getInteraction()->getConnectors();
		for(const auto & it:connectors){
			resultString+=formatConnector(it);
		}
	}
	return resultString;
}

string CommunicationGraphSerializer::formatConnector(const Connector& aConnector ){
	//TODO hypothesis : rdv connector, generalize connector
	//TODO : rationalize port plantuml id computing
	string resultString ="";
	if(aConnector.getProtocol()==ComProtocol::PROTOCOL_RDV_KIND){
		//for first com route : nameMachine + 0+
		//for second com route :
		bool isFirstCommRoute = true;
		for (auto comRoute: aConnector.getComRoutes()){
			if(isFirstCommRoute){
				//TODO machine1.NormalName+"port1.normalName"+"#-0)-#"+"port2.normalName"+machine2.normalName
				isFirstCommRoute = false;
				resultString+="\n"+comRoute.getComPoints().front().getMachine().getPortableNameID()+"."+comRoute.getComPoints().front().getPort().getPortableNameID();
				resultString+=" ---. ";
			}
			else{
				resultString+=comRoute.getComPoints().front().getMachine().getPortableNameID()+"."+comRoute.getComPoints().front().getPort().getPortableNameID();
			}
		}
	}
	return resultString;
}


string CommunicationGraphSerializer::formatComposition(const Machine & aMachine){
	string resultString ="";
	resultString +="\ncomponent \""+aMachine.getNameID()+"\" as "+aMachine.getPortableNameID();
	if(hasCommunicatingSubMachineaMachine(aMachine)){
		resultString+=" {";
		const TableOfBF_T<Machine>& machines = aMachine.getCompositePart()->getMachines();
		BFVector::const_ref_iterator<Machine > machineEnd = machines.end();
		for(  BFVector::const_ref_iterator<Machine > it = machines.begin(); it != machineEnd; ++it ){
			resultString +=formatComposition(it);
		}
		resultString+=formatInteractions(aMachine);
		resultString+="\n}";
	}

	for(auto portName: aMachine.getPortNames()){
		resultString+="\ninterface \""+portName+"\" as "+aMachine.getPortableNameID()+"."+portName+"\n";
		resultString+=aMachine.getPortableNameID()+" #-[bold] "+aMachine.getPortableNameID()+"."+portName;
	}
	return resultString;
}

bool CommunicationGraphSerializer::hasCommunicatingSubMachineaMachine(const Machine & aMachine){
	if(aMachine.hasCompositePart()&& aMachine.getCompositePart()->getMachines().size()>0){
		const TableOfBF_T<Machine>& machines = aMachine.getCompositePart()->getMachines();
		BFVector::const_ref_iterator<Machine > machineEnd = machines.end();
		for(  BFVector::const_ref_iterator<Machine > it = machines.begin(); it != machineEnd; ++it ){
			if(it->getSpecifier().getComponentKind()==Specifier::COMPONENT_SYSTEM_KIND||it->getSpecifier().getComponentKind()==Specifier::COMPONENT_STATEMACHINE_KIND){
				return true;
			}
		}
	}
	return false;
}


} /* namespace sep */
