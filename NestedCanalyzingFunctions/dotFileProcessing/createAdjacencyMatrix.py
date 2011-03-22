#!/usr/bin/python
# -*- coding: utf-8 -*-

import time
import sys
import os
import pydot
from time import gmtime, strftime	

from pydot import *

g_unnamedSubgraphCount = int(0);

def getNameFromNode(node):
	#print  "node type:", node.__class__.__name__ ;
	name="";
	try:
		if (node.get_label() != None ):
			name = node.get_label();
	except:
		name =  node.get_name();
	#print "name", name;
	return name;


def getLabelFromNode(node):
	#print  "node type:", node.__class__.__name__ ;
	try:
		if (node.get_label() != None ):
			return node.get_label();
	except:
		return node.get_name();

def myGetName(graph, srcNodeName):
	global g_unnamedSubgraphCount;
	#print "srcNodeName", srcNodeName.__class__.__name__;
	#print  "graph type:", graph.__class__.__name__ ;
	try:
		srcNode = graph.get_node(srcNodeName);
		keyName = getNameFromNode(srcNode);
	except:
		if  srcNodeName.__class__.__name__=="str":
			keyName = srcNodeName;
		else: 
			keyName = "unnamedStructure"+str(g_unnamedSubgraphCount);
			g_unnamedSubgraphCount = g_unnamedSubgraphCount + 1;
	#print "keyName " ,keyName
	return keyName;

		
def createDependencyDict(graph):
	global g_unnamedSubgraphCount;
	dependencyLists=dict();
	nodeList=graph.get_node_list();

	for node in nodeList:
		#print  "createDependencyDict: node type:", node.__class__.__name__ ;
		keyName = getNameFromNode(node);
		#print "keyName: ", keyName
		if keyName in dependencyLists:
			raise Exception("dublicate label for nodes");
		dependencyLists[str(keyName)] = dict();

	edgeList = graph.get_edge_list();


	g_unnamedSubgraphCount = int(0);

	for edge in edgeList:
		#print "edge in edgelist";
		srcNodeName = edge.get_source();
		keyName = myGetName(graph, srcNodeName);
		#print "srckeyName: ", keyName
		dependencyLists[keyName] = dict();
		dstNodeName = edge.get_destination();
		keyName = myGetName(graph, dstNodeName);
		#print "dstkeyName: ", keyName
		dependencyLists[str(keyName)] = dict();
		
	g_unnamedSubgraphCount = int(0);
		
	for edge in edgeList:
		#print "edge:", edge.to_string();
		srcNodeName = edge.get_source();
		keyName = myGetName(graph, srcNodeName);
		#print "srcName",keyName;
		dstNodeName = edge.get_destination();
		dstName = myGetName(graph, dstNodeName);
		#print "dstName",dstName;
		dependencyLists[str(keyName)][str(dstName)]=1;
	return dependencyLists;


def printNodeList(nlist):

	first=True;	
	for node in nodeList:
		res="";
		if (not first):
			res=res + ", ";
		res=res+"\""+node.get_name()++"\"";
		first=False;
		
		
def addQuotes(nodename):
	tmpNodename = nodename.strip();
	if len(tmpNodename)>0 and tmpNodename[0]!='\"' and tmpNodename[len(tmpNodename)-1]!='\"':
		tmpNodename='"'+tmpNodename+'"';
	return tmpNodename


def getNodeListString(dependencyDict):
	res="nodelist = {";
	first = True;
	
	for node in dependencyDict:
		if not first:
			res=res+", ";
		res=res + addQuotes(node);
		first = False;
	res = res + " } ; \n" ;
	return res;

def createAdjacencyMatrixString(graph):

	assert(graph.get_type()=='digraph');
	if graph.get_type()!='digraph' :
		raise Exception("error: only directional graphs are supported !" );

	if  len(graph.get_subgraph_list() )>0 :
		raise Exception("error: currently subgraphs are not supported !" );
	
	resstr="adjacencyMatrix = matrix ";
	nodeList=graph.get_node_list();

	edgeList = graph.get_edge_list();


	dependencyDict = createDependencyDict(graph);

	firstx = True;

	resstr=resstr + " { ";
	#for node in nodeList:
	for node in dependencyDict:
		if (not firstx):
			resstr = resstr+" , \n"
		firstx	= False;
		resstr = resstr + " { "
		keyName = node;
		#keyName = myGetName(graph,node);
		#print keyName
		depList = dependencyDict[keyName];
		firsty = True;

		for nodey in dependencyDict:
			if (not firsty):
				resstr = resstr + ", ";
			firsty = False;
			keyName = nodey;
			#keyName = myGetName(graph,nodey);
			if keyName in depList:
			 	resstr = resstr + "1 ";
			else:
				resstr = resstr + "0 ";
		resstr=resstr+" } ";
	resstr = resstr+"\n } ; ";
	resstr = getNodeListString(dependencyDict)+ resstr;
	return resstr;



#def sandbox(graph):


# call: ./createAdjacencyMatrix.py inputDotFile.dot
# the function returns  a Macaulay2 input string with variable list and adjacencyMatrix
if __name__ == "__main__":
	inputDotFileName = sys.argv[1];
	graph = graph_from_dot_file( inputDotFileName );

	#sandbox(graph);	
		
	matrixStr = createAdjacencyMatrixString(graph);
	print matrixStr ;
	#	
	
	sys.exit(0)







# one alternative is to use the graphviz lib itself and export the graph to 'svg' and from s
# pros: the export function will behave exactly like it was intended by the graphviz developers, even if some language grammar details are not precisely documented.
# cons: 











