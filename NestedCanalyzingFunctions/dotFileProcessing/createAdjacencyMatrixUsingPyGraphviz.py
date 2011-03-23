#!/usr/bin/python
# -*- coding: utf-8 -*-

import sys
import pygraphviz as pgv

from pygraphviz import *



def getNameFromNode(node):
	name=str(node);
	if 'label' in node.attr:
		if len(node.attr['label'])>0:
			name = node.attr['label'];
	return name;
	

def createDependencyDict(graph):
	#global g_unnamedSubgraphCount;
	dependencyLists=dict();
	nodeList=graph.nodes();

	for node in nodeList:
		#print  "createDependencyDict: node type:", node.__class__.__name__ ;
		nodeName = getNameFromNode(node);
		#print "keyName: ", keyName
		if nodeName in dependencyLists:
			raise Exception("dublicate name for nodes");
		dependencyLists[str(nodeName)] = dict();

	edgeList = graph.edges();
		
	for edge in edgeList:
		srcName = getNameFromNode(edge[0]);
		dstName = getNameFromNode(edge[1]);
		dependencyLists[str(srcName)][str(dstName)]=1;
	return dependencyLists;

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

	if not graph.is_directed():
		raise Exception("-- Error: only directional graphs are allowed !" );

	if  len(graph.subgraphs() )>0 :
		sys.stderr.write('\n-- subgraphs detected...\n')
		sys.stderr.write('-- Warning: cannot detect and handle inlined subgraphs properly!\n')
		sys.stderr.write('-- \t\t inlined subgraph example : " digraph ok  { node d; d->subgraph {b->c} ;} "\n')
		sys.stderr.write('-- \t\t regular subgraph example : " digraph bad { node d; subgraph cluster1 {b->c}; d->cluster1 ;} "\n\n')
		
		#raise Exception("error: currently subgraphs are not supported !" );
	
	resstr="adjacencyMatrix = matrix ";
	nodeList=graph.nodes();

	edgeList = graph.edges();

	dependencyDict = createDependencyDict(graph);

	firstx = True;

	resstr=resstr + " { ";

	for nodeName in dependencyDict:
		if (not firstx):
			resstr = resstr+" , \n"
		firstx	= False;
		resstr = resstr + " { "
		depList = dependencyDict[nodeName];
		firsty = True;

		for dsNodeName in dependencyDict:
			if (not firsty):
				resstr = resstr + ", ";
			firsty = False;
			if dsNodeName in depList:
			 	resstr = resstr + "1 ";
			else:
				resstr = resstr + "0 ";
		resstr=resstr+" } ";
	resstr = resstr+"\n } ; ";
	resstr = getNodeListString(dependencyDict)+ resstr;
	return resstr;


def gsandbox(graph):
	print "#edges:" ,graph.size()
	
	nodelist =graph.nodes();
	
	subgraphList=graph.subgraphs();
	print " #subgraphList=", len(subgraphList);
	
	for node in nodelist:
		print "node type: ", node.__class__.__name__
		for attr in node.attr:
			print "attribute  ", attr;
		if len(node.attr['label'])>0:
			print node.attr['label']
		else:
			print str(node)
	
	edges=graph.edges();
	for edge in edges:
		print "len(edge)=",len(edge)
		print "edge type: ", edge.__class__.__name__
		for attr in edge[0].attr:
			print "attribute  ", attr;
		for attr in edge[1].attr:
			print "attribute  ", attr;
		if len(edge.attr['label'])>0:
			print edge.attr['label']
		else:
			print str(edge)


def sandbox(inputDotFileName):
	graph=AGraph(inputDotFileName);
	gsandbox(graph);
	
	gsandbox(graph.subgraphs()[0]);

# call: ./createAdjacencyMatrixUsingPyGraphviz.py inputDotFile.dot
# the function returns  a Macaulay2 input string with variable list and adjacencyMatrix
if __name__ == "__main__":
	inputDotFileName = sys.argv[1];
	
	#sandbox(inputDotFileName);
	
	graph=AGraph(inputDotFileName);
		
	adjStr=createAdjacencyMatrixString(graph);
	print adjStr
	
	sys.exit(0)







# one alternative is to use the graphviz lib itself and export the graph to 'svg' and from s
# pros: the export function will behave exactly like it was intended by the graphviz developers, even if some language grammar details are not precisely documented.
# cons: 











