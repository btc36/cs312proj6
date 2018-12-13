#!/usr/bin/python3
import copy
from which_pyqt import PYQT_VER
if PYQT_VER == 'PYQT5':
	from PyQt5.QtCore import QLineF, QPointF

else:
	raise Exception('Unsupported Version of PyQt: {}'.format(PYQT_VER))



import time
import numpy as np
from TSPClasses import *
import heapq
import itertools
import math
import heapq

	#////////////////////////////BRANCH AND BOUND CLASSES////////////////////////////////////
class node:
	def __init__( self, _city, _cost, _matrix, _parent, _children, _depth ): #space: O(n^2)
		self.city = _city
		self.cost = _cost
		self.matrix = _matrix #space: O(n^2)
		self.parent = _parent #index of parent in tree (array)
		self.children = _children #array of children indexes. Space: O(n)
		self.depth = _depth

	def __lt__(self, other):
		#sorting by depth, then by cost so we get an answer fast
		if self.depth == other.depth: return self.cost < other.cost
		return self.depth > other.depth

	def __str__(self):
		return("city:" + str(self.city) + " cost:" + str(self.cost) + " parentInd:"
		+ str(self.parent) + " numChildren:" + str(len(self.children)) + " depth:" + str(self.depth))


class MinHeap(object):
   def __init__(self, initial=None, key=lambda x:x): #time: O(n) space:O(n)
       self.key = key
       if initial:
           self._data = [(key(item), item) for item in initial] #O(n)
           heapq.heapify(self._data) #O(logn)
       else:
           self._data = []

   def push(self, item): #time: O(logn)
       heapq.heappush(self._data, (self.key(item), item)) #assuming this is O(logn)

   def pop(self): #time: O(logn)
	   return heapq.heappop(self._data)[1] #assuming this is O(logn)

   def __len__(self):
	   return len(self._data)

class TSPSolver:
	def __init__( self, gui_view ):
		self._scenario = None
		self.maxHeap = 0
		self.bssf = None

	def setupWithScenario( self, scenario ):
		self._scenario = scenario

	''' <summary>
		This is the entry point for the default solver
		which just finds a valid random tour.  Note this could be used to find your
		initial BSSF.
		</summary>
		<returns>results dictionary for GUI that contains three ints: cost of solution,
		time spent to find solution, number of permutations tried during search, the
		solution found, and three null values for fields not used for this
		algorithm</returns>
	'''
	#////////////////////////////BRANCH AND BOUND CLASSES////////////////////////////////////
	class nodeObject:
		def __init__(self,position,tour=[],cost=0,lowerBound=0,costMatrix=[],tourIndex = []):
		    self.tour = tour
		    self.cost = cost
		    self.lowerBound = lowerBound
		    self.costMatrix = costMatrix
		    self.position = position
		    self.tourIndex = tourIndex
		def getTour(self):
		    return self.tour
		def getTourIndex(self):
		    return self.tourIndex
		def getCost(self):
		    return self.cost
		def setCost(self,newCost):
		    self.cost = newCost
		def getLowerBound(self):
		    return self.lowerBound
		def setLowerBound(self,newLB):
		    self.lowerBound = newLB
		def getMatrix(self):
		    return self.costMatrix
		def setMatrix(self,newMatrix):
		    self.costMatrix = newMatrix
		def createChild(self,index,city,cities,origin):
		    #Add distance to existing cost
		    newDistance = cities[origin].costTo(city)
		    newCost = self.cost + newDistance
		    #Use deep copy to avoid changing parent
		    newMatrix = copy.deepcopy(self.costMatrix)
		    newTour = copy.deepcopy(self.tour)
		    tourIndex = copy.deepcopy(self.tourIndex)
		    #Keep track of where I have been, objects for GUI,
		    #And index for matrix and determining available neighbors
		    tourIndex.append(index)
		    newTour.append(city)
		    #Keep track of which city this child is at
		    curPosition = newMatrix[self.position]
		    #Set certain values to infinity
		    newMatrix[index][self.position] = float('inf')
		    for i in range(len(curPosition)):
		        curPosition[i] = float('inf')
		        newMatrix[i][index] = float('inf')
		    newMatrix = self.transformMatrix(newMatrix)
		    child = self.__class__(index,tour= newTour,cost= newCost,lowerBound = newMatrix[1],costMatrix = newMatrix[0],tourIndex = tourIndex)
		    return child
		def createParentMatrix(self,cities):
		    nCities = len(cities)
		    for i in range(nCities):
		        self.costMatrix.append([])
		        currRow = self.costMatrix[i]
		        for j in range(nCities):
		            currRow.append(cities[i].costTo(cities[j]))
		    matrixInfo = self.transformMatrix(self.costMatrix)
		    self.costMatrix = matrixInfo[0]
		    self.lowerBound = matrixInfo[1]
		def transformMatrix(self,costMatrix):
		    #Don't want to override old bound
		    newBound = copy.deepcopy(self.lowerBound)
		    #Check rows, and then I check columns
		    #If there is already a 0, nothing will change
		    for row in costMatrix:
		        lowestRowValue = float('inf')
		        for value in row:
		            if value < lowestRowValue:
		                lowestRowValue = value
		        k = 0
		        if(lowestRowValue != float('inf')):
		            newBound += lowestRowValue
		            for value in row:
		                row[k] = value - lowestRowValue
		                k +=1
		    for col in range(len(costMatrix)):
		        lowestColValue = float('inf')
		        for c in range(len(costMatrix)):
		            colValue = costMatrix[c][col]
		            if colValue < lowestColValue:
		                lowestColValue = colValue
		        if(lowestColValue != float('inf')):
		            newBound += lowestColValue
		            for c in range(len(costMatrix)):
		                costMatrix[c][col] = costMatrix[c][col] - lowestColValue
		    return [costMatrix,newBound]

	class priorityQueue:
		def __init__(self):
		    self.queue = []
		def getNextNode(self,numCities):
		    #I scan the array, and return a node based on lowerBound/(progress*2)
		    nextNode = None
		    nextNodeValue = float('inf')
		    for node in self.queue:
		        curScore = node.getLowerBound()
		        curProgress = len(node.getTour())
		        priorityScore = curScore/curProgress*4
		        if(priorityScore < nextNodeValue):
		            nextNode = node
		            nextNodeValue = priorityScore
		    self.queue.remove(nextNode)
		    return nextNode
		    #Performs a search and returns the result based on the priority
		def checkNewBSSF(self,newBSSF):
		    count = 0
		    for node in self.queue:
		        if node.getLowerBound() > newBSSF:
		            self.queue.remove(node)
		            count += 1
		    return count
		    #Removes nodes no longer to be considered
		def insert(self,newNode):
		    self.queue.append(newNode)
		def getLength(self):
		    return len(self.queue)





	def defaultRandomTour( self, time_allowance=60.0 ):
		results = {}
		cities = self._scenario.getCities()
		ncities = len(cities)
		foundTour = False
		count = 0
		bssf = None
		start_time = time.time()
		while not foundTour and time.time()-start_time < time_allowance:
			# create a random permutation
			perm = np.random.permutation( ncities )
			route = []
			# Now build the route using the random permutation
			for i in range( ncities ):
				route.append( cities[ perm[i] ] )
			bssf = TSPSolution(route)
			count += 1
			if bssf.cost < np.inf:
				# Found a valid route
				foundTour = True
		end_time = time.time()
		results['cost'] = bssf.cost if foundTour else math.inf
		results['time'] = end_time - start_time
		results['count'] = count
		results['soln'] = bssf
		results['max'] = None
		results['total'] = None
		results['pruned'] = None
		self._bssf = bssf
		return results

	''' <summary>
		This is the entry point for the greedy solver, which you must implement for
		the group project (but it is probably a good idea to just do it for the branch-and
		bound project as a way to get your feet wet).  Note this could be used to find your
		initial BSSF.
		</summary>
		<returns>results dictionary for GUI that contains three ints: cost of best solution,
		time spent to find best solution, total number of solutions found, the best
		solution found, and three null values for fields not used for this
		algorithm</returns>
	'''

	def greedy( self,time_allowance=60.0 ):
		results = {}
		cities = self._scenario.getCities()
		ncities = len(cities)
		foundTour = False
		count = 0
		bssf = None
		start_time = time.time()
		while not foundTour and time.time() - start_time < time_allowance:
			bestRoute = None
			minScore = float('inf')
			#Tries greedy from every startpoint
			for i in range(ncities):
				route = []
				#Start with the first node
				citiesLeft = list(range(0,ncities))
				currentCity = i
				route.append(cities[currentCity])
				citiesLeft.remove(currentCity)
				while(len(route) != ncities):
					minCost = float('inf')
					nextCity = None
					#Picks the closest available city
					for city in citiesLeft:
						newCost = cities[currentCity].costTo(cities[city])
						if(newCost < minCost):
							minCost = newCost
							nextCity = city
					if nextCity == None:
						#Just take the first element, if there are multiple,
						#They are both infinite so it doesn't matter
						nextCity = citiesLeft[0]
					route.append(cities[nextCity])
					citiesLeft.remove(nextCity)
					currentCity = nextCity
				newRoute = TSPSolution(route)
				newScore = newRoute.cost
				if(newScore < minScore):
					minScore = newScore
					bestRoute = newRoute
			bssf = bestRoute
			count += 1
			if bssf.cost < np.inf:
				# Found a valid route
				foundTour = True
		end_time = time.time()
		results['cost'] = bssf.cost if foundTour else math.inf
		results['time'] = end_time - start_time
		results['count'] = count
		results['soln'] = bssf
		results['max'] = None
		results['total'] = None
		results['pruned'] = None
		results['bssf'] = bssf
		return results

	def branchAndBound( self, time_allowance=60.0 ):
		#Use these to keep track of stats
		maxQueue = 0
		totalSolutions = 0
		numPruned = 0
		statesCreated = 1
		results = {}
		cities = self._scenario.getCities()
		ncities = len(cities)
		#Determines if I found atleast one solution
		foundTour = False
		#Don't want to end the loop till all nodes have been tried
		foundAllTours = False
		#I used my greedy algorithm to get my original BSSF
		greedyResult = self.greedy()
		BRSF = greedyResult
		bssfCost = greedyResult['cost']
		nodeQueue = self.priorityQueue()
		#I always start the tour on the first Node
		firstNode = self.nodeObject(0,tour=[cities[0]],tourIndex=[0])
		firstNode.createParentMatrix(cities)
		#My queue starts empty, so I use this boolean to
		# not check for an empty queue till after the first node
		endResult = False
		start_time = time.time()
		while not foundAllTours and time.time() - start_time < time_allowance:
			numNodes = nodeQueue.getLength()
			#Keep track of the biggest queue size
			if numNodes > maxQueue:
			    maxQueue = numNodes
			if(numNodes >= 1):
			    currentNode = nodeQueue.getNextNode(ncities)
			else:
				currentNode = firstNode
				if(endResult):
					#My queue is empty, I am done
					foundAllTours = True
					print("DONE")
					print(time.time() - start_time)
					continue
				endResult = True
			alreadyUsed = currentNode.getTourIndex()
			citiesLeft = []
			#Get a list of options that this node can visit
			for j in range(ncities):
			    if not j in alreadyUsed:
			        citiesLeft.append(cities[j])
			if len(citiesLeft) == 0:
                #I have reached a leaf node, and a possible solution
				totalSolutions += 1
				foundTour = True
				totalCost = currentNode.getCost()
				if totalCost < bssfCost:
				    print(bssfCost)
				    bssfCost = totalCost
				    BRSF = TSPSolution(currentNode.getTour())
				    #Counts how many nodes were pruned with new BSSF
				    numPruned += nodeQueue.checkNewBSSF(bssfCost)
				print("BSSF COST IS:")
				print(bssfCost)
				print(time.time() - start_time)
			else:
			    for city in citiesLeft:
			        #Expand the node, creating a child for every possible neighbor
			        index = cities.index(city)
			        child = currentNode.createChild(index,city,cities,currentNode.position)
			        statesCreated += 1
			        childBound = child.getLowerBound()
			        childCost = child.getCost()
			        #I prune if the bound is above the limit, or there is no connecting path
			        if(childBound < bssfCost and childCost < bssfCost):
			            nodeQueue.insert(child)
			        else:
			            numPruned += 1
		end_time = time.time()
		#Adds all nodes left without being processed
		numPruned += nodeQueue.getLength()
		results['cost'] = BRSF.cost if foundTour else math.inf
		results['time'] = end_time - start_time
		results['count'] = statesCreated
		results['soln'] = BRSF
		results['max'] = maxQueue
		results['total'] = totalSolutions
		results['pruned'] = numPruned
		return results


	''' <summary>
		This is the entry point for the algorithm you'll write for your group project.
		</summary>
		<returns>results dictionary for GUI that contains three ints: cost of best solution,
		time spent to find best solution, total number of solutions found during search, the
		best solution found.  You may use the other three field however you like.
		algorithm</returns>
	'''


	def fancy( self,time_allowance=60.0 ):
		results = self.greedy()
		bssf = results['soln']
		nCities = len(bssf.route)
		cities = self._scenario.getCities()
		ourTabuList = self.tabuList(nCities)
		temp = copy.deepcopy(bssf)
		start_time = time.time()
		nSolutions = 0;

		print("---init bssf: " + str(bssf.cost))
		temp = copy.deepcopy(bssf) #start with our init bssf
		bestOption = copy.deepcopy(bssf)
		while time.time()-start_time < time_allowance:
			bestOption.cost = math.inf
			index1 = 0
			index2 = 0
			'''check neighbors'''
			for i in range(nCities):
				for j in range(nCities):
					'''skip when i == j bc that switch would be pointless'''
					'''skip wheb j < i because we've already tried those combos'''
					if i == j or j < i:
						continue

					'''To Make Sure we don't exceed the time limit'''
					if time.time()-start_time >= time_allowance:
						break

					'''check to see if the new route is in the tabu list'''
					if not ourTabuList.isTabu(i,j):
						'''altering the route paths'''
						city = copy.deepcopy(temp.route[i])
						temp.route[i] = copy.deepcopy(temp.route[j])
						temp.route[j] = city

						'''recalibrating path costs (the easy way)'''
						temp.cost = TSPSolution(temp.route).cost

						'''check to see if the cost has improved'''
						'''hold on to the best option, even if it's not better than the bssf'''
						if temp.cost < bestOption.cost:
							bestOption = copy.deepcopy(temp)
							index1 = i
							index2 = j
						if temp.cost < bssf.cost:
							bssf = copy.deepcopy(temp)
							print(bssf.cost)
							print(time.time() - start_time)
							nSolutions += 1;

						'''revert list back so we can continue the algorithm'''
						temp.route[j] = copy.deepcopy(temp.route[i])
						temp.route[i]= city
			ourTabuList.addSwitch(index1,index2)
			ourTabuList.decrementTabuList()
			'''use the best result'''
			temp = copy.copy(bestOption)

		end_time = time.time()
		solution = TSPSolution(bssf.route)
		results['cost'] = solution.cost
		results['time'] = end_time - start_time
		results['soln'] = solution
		results['count'] = nSolutions

		print("end bssf: " + str(bssf.cost))
		return results


	class tabuList:
		def __init__(self,nCities):
			#init matrix to size ncities X ncities with 0's
			self.tabuMatrix = np.zeros((nCities, nCities), dtype=int)
			self.limit = nCities # math.floor(nCities/2) This can be whatever
			self.nCities = nCities
		def addSwitch(self,index1,index2):
			self.tabuMatrix[index1][index2] = self.limit
			self.tabuMatrix[index2][index1] = self.limit
		def isTabu(self,index1,index2):
			if self.tabuMatrix[index1][index2] == 0:
				return False
			else:
				return True
		def decrementTabuList(self):
			#decrement all non-zero entries
			self.tabuMatrix[self.tabuMatrix > 0] -=1
