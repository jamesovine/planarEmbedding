#Shift Grid Embedding Algorithm for use with SAGE

import sys
import operator

from sage.graphs.schnyder import _triangulate

#Point class. Stores x offest and y coordinate for each vertex
class Point():

	def __init__(self,x,y):
		self.x=x
		self.y=y

#Tree node class. Struct to store graph.
class TreeNode():

	def __init__(self,point,vertex):
		self.parent= None	
		self.left = None
		self.right = None
		self.vertex = vertex
		self.point = point	
	
	def getLeftChild(self):
		return self.left

	def getRightChild(self):
		return self.right

	def getParent(self):
		return self.parent

	def setNodeValue(self,value):
		self.point=value

	def getNodeValue(self,value):
		return self.point

	def addLeftChild(self,child):
		child.parent=self
		self.left=child

	def addRightChild(self,child):
		child.parent=self
		self.right=child

	def deleteRightChild(self):
		self.right=None

	def deleteLeftChild(self):
		self.left=None


#Construct a canonical ordering of vertices.
#embedding is a combinatorial embedding returned by is_planar(set_embedding=True). i.e clockwise ordering of edges about each vertex
#returns ordering, a dict containing a canonical ordering of vertices in g
def canonicalOrdering(g,embedding):

	#get faces from embedding to determine two starting vertices
	faces=g.faces(embedding)
	for i in faces:
		i.sort()

	faces.sort()
	face=faces[0]

	initVert=[face[0][0], face[1][0]]
	initVert.sort()
	v1=initVert[0]
	v2=initVert[1]
	
	#get number of vertices and a sorted list
	order=g.order()
	vertices=g.vertices()
	vertices.sort()

	#Dictionary containing canonical ordering of vertices in g
	ordering={}
	ordering[v1]=0
	ordering[v2]=1
	pos=2

	#Dictionary of vertices and corresponding labels in form, for a vertex v labels[v]={v:label}
	labels={}

	#set these labels to anything
	labels[v1]= -100
	labels[v2]= -100

	#Dictionary to keep track of processed vertices
	processed={}
	processed[v1]=0
	processed[v2]=0

	#all labels -1 apart from v1 and v2
	for i in vertices:
		if i!=v1 and i!=v2:
			labels[i]=-1
			processed[i]=0
			ordering[i]=order-1

	#process v1 and v2
	processVertex(g,v1,labels,processed,embedding)
	processVertex(g,v2,labels,processed,embedding)
	
	# for k=3:no of vertices, chose vertex v with label =1 to process
	tempV=0
	while pos<order-1:
		for v in vertices:
			if labels[v]==1 and processed[v]==0:
				tempV=v
		ordering[tempV]=pos
		processVertex(g,tempV,labels,processed,embedding)
		pos+=1

	return ordering


#Helper function for canonicalOrdering()
#Updates labels for neighbours of current processing vertex
def processVertex(g,v,labels,processed,embedding):

	#Create list of unprocessed nodes
	notprocessed = []
	for w in g.neighbors(v):
		if processed[w]==0:
			notprocessed.append(w)

	for w in notprocessed:

		#Case: w has no processed neighbors
		if labels[w]==-1:
			labels[w]=0

		#Case: w has one processed neighbour u	
		elif labels[w]==0:
			for u in g.neighbors(w):
				if processed[u]==1:

					#if v is next in circular order to u
					for i,j in enumerate(embedding[w],start=0):

						if j==u:
							if i!=0 and i!=len(embedding[w])-1:

								if embedding[w][i+1]==v or embedding[w][i-1]==v:
									labels[w]=1
								else:
									labels[w]=2

							#Take care of case when w is first vertex in list
							elif i==0:

								if embedding[w][1]==v or embedding[w][len(embedding[w])-1]==v:
									labels[w]=1
								else: 
									labels[w]=2

							#Take care of case when w is last vertex in list
							elif i==len(embedding[w])-1:

								if embedding[w][0]==v or embedding[w][i-1]==v:
									labels[w]=1
								else: 
									labels[w]=2
		
		#Case: labels[w]=i>0
		else:
			for i,j in enumerate(embedding[w], start=0):

				if j==v:

					#if vetices next in circ order to v around w have both been processed:
					if i!=0 and i!=len(embedding[w])-1:
						
						if processed[embedding[w][i-1]]==1 and processed[embedding[w][i+1]]==1:
							labels[w]-=1
						#if neither have been processed	
						elif processed[embedding[w][i-1]]==0 and processed[embedding[w][i+1]]==0:
							labels[w]+=1

					#Take care of case when v is first vertex in list		
					elif i==0:
						if processed[embedding[w][len(embedding[w])-1]]==1 and processed[embedding[w][1]]==1:
							labels[w]-=1
						elif processed[embedding[w][len(embedding[w])-1]]==0 and processed[embedding[w][1]]==0:
							labels[w]+=1

					#Take care of case when v is last vertex in list
					elif i==len(embedding[w])-1:
						if processed[embedding[w][0]]==1 and processed[embedding[w][i-1]]==1:
								labels[w]-=1
						elif processed[embedding[w][0]]==0 and processed[embedding[w][i-1]]==0:
								labels[w]+=1
								
	processed[v]=1


#Shift Algorithm. Computes y coordinates and x offsets for each vertex in graph. Constructs a binary tree and computes final coordinates.
def shiftAlgo(g,embedding,ordering):

	#Initialise for all vertices
	points=[]
	nodes=[]
	
	orderedVertices = sorted(ordering, key=ordering.get)

	points.append(Point(0,0))
	points.append(Point(1,0))
	points.append(Point(1,1))

	#Add the first 3 vertices to binary tree.
	nodes.append(TreeNode(points[0],orderedVertices[0]))
	nodes.append(TreeNode(points[1],orderedVertices[1]))
	nodes.append(TreeNode(points[2],orderedVertices[2]))
	nodes[0].addRightChild(nodes[2])
	nodes[2].addRightChild(nodes[1])

	#keep track of current vertex position
	current = 3
	
	#4 vertices or more
	for count, v in enumerate(orderedVertices,start=0):

		if count>=3:

			vertex=v
			externalVertices=[]
			getOuterVertices(nodes[0],externalVertices)

			#create node for current vertex
			nodes.append(TreeNode(Point(0,0),vertex))

			#neighbours of current vertex k on outer cycle of graph k-1
			cycleNeighbors=[w for w in externalVertices if w in embedding[vertex]]

			#update externalVertices for next iteration
			for i,v in enumerate(cycleNeighbors,start=0):
				if i==0 or i == len(cycleNeighbors)-1:
					continue
				else:
					externalVertices.remove(v)
			externalVertices.append(vertex)

			#get an equivalent list of nodes
			cycleNeighborNodes=[]

			for v in cycleNeighbors:
				for w in nodes:
					if w.vertex==v:
						cycleNeighborNodes.append(w)				

			cycleNeighborNodes[1].point.x+=1
			cycleNeighborNodes[len(cycleNeighbors)-1].point.x+=1

			#compute x offsets from parent rather than actual x coordinates
			parentOffset=0
			for w in cycleNeighborNodes:
				parentOffset += w.point.x
			
			parentOffset-=cycleNeighborNodes[0].point.x

			#calculate x offest for current vertex
			# parent offset + Last neighbour y coord - First neighbour y coord
			nodes[current].point.x = (parentOffset + cycleNeighborNodes[len(cycleNeighborNodes)-1].point.y - cycleNeighborNodes[0].point.y)*0.5

			#calculate x offest for current vertex
			nodes[current].point.y = (parentOffset + cycleNeighborNodes[len(cycleNeighborNodes)-1].point.y + cycleNeighborNodes[0].point.y)*0.5

			#update x offest of final neighbour. total parent offset - current node offset
			cycleNeighborNodes[len(cycleNeighborNodes)-1].point.x = parentOffset - nodes[current].point.x

			#Update the tree. insert current vertex
			cycleNeighborNodes[0].addRightChild(nodes[current])
			nodes[current].addRightChild(cycleNeighborNodes[len(cycleNeighborNodes)-1])

			#if current vertex has more than 2 neighbours on outer cycle. ie if it 'covers' any vertices on the outer cycle
			if len(cycleNeighborNodes)>2:

				cycleNeighborNodes[1].point.x -= nodes[current].point.x
				nodes[current].addLeftChild(cycleNeighborNodes[1])
				cycleNeighborNodes[len(cycleNeighborNodes)-2].deleteRightChild()

			else: nodes[current].deleteLeftChild()
			current+=1
	
	accumulateOffset(nodes[0],0)
	setCoords(g,nodes)

#Helper function for shiftAlgo. Get outercycles of graph at each step, by traversing right children
def getOuterVertices(node,outerVertices):

	if isinstance(node, TreeNode):
		outerVertices.append(node.vertex)
		getOuterVertices(node.getRightChild(),outerVertices)

# Helper function for shiftAlgo. Computes x offset for node
def accumulateOffset(node,delta):

	if isinstance(node, TreeNode):
		node.point.x+=delta
		accumulateOffset(node.getLeftChild() , node.point.x)
		accumulateOffset(node.getRightChild() , node.point.x)

#Helper function for shiftAlgo. Sets final coordinates
def setCoords(g, nodes):

	coordinates={}

	for v in nodes:
		coordinates[v.vertex]=([v.point.x,v.point.y])

	g.set_pos(coordinates)


#Embed graph onto grid using Shift method
def shiftEmbed(g):
	isPlan=g.is_planar(set_embedding=True)
	if g.order() < 3:
		raise ValueError("Graph must have at least 3 vertices")
	if g.is_connected() == False:
		raise NotImplementedError("Graph must be connected.")
	if isPlan==False:
		raise NotImplementedError("Graph must be planar.")
	_triangulate(g,g._embedding)
	g.is_planar(set_embedding=True)
	ordering=canonicalOrdering(g,g._embedding)
	shiftAlgo(g,g._embedding,ordering)

