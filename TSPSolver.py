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



class TSPSolver:
	def __init__( self, gui_view ):
		self._scenario = None

	def setupWithScenario( self, scenario ):
		self._scenario = scenario
		self._bssf = math.inf
		self.boundCost = 0
		self.PQ = []
		self.maxQueueSize = 0
		self.pruned = 0
		self.total = 0


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
		return results
	
	
	'''This is to separate work and reduce rows for branching and bounding'''
	def MinimizeBySmallestInRow(self, list, row):
		smallest =list[row][0]
		for i in range(len(list[row])):
			if list[row][i] < smallest:
				smallest = list[row][i]
		for i in range(len(list[row])):
			list[row][i] -= smallest
		self.boundCost += smallest
		return smallest

	'''This is to separate work and reduce cols for branching and bounding'''

	def MinimizeBySmallestInCol(self, list, col):
		smallest = list[0][col]
		for i in range(len(list)):
			if list[i][col] < smallest:
				smallest = list[i][col]
		for i in range(len(list)):
			list[i][col] -= smallest
		self.boundCost += smallest
		return smallest

	'''this infinitizes the appropriate rows and columns'''


	'''the row is also the entry city in this case and this function should be recursive'''
	def partials(self, list, row, col, bssf):
		if(len(self.PQ) == 0):
			return bssf
		partial = []
		for i in range(len(list)):
			partial.append([])
			for j in range(len(list[i])):
				if(i == row or j == col):
					partial[i].append(math.inf)
				else:
					partial[i].append(list[i][j])
		partial[col][row] = math.inf
		for i in range(len(list)):
			if not i == row:
				bssf += self.MinimizeBySmallestInRow(partial, i)
		for i in range(len(list)):
			if not i == col:
				bssf += self.MinimizeBySmallestInCol(partial, i)
		return bssf

	'''find function so no repeats'''
	def find(self, city, usedCities):
		for i in range(len(usedCities)):
			if city._index == usedCities[i]._index:
				return i
		return -1

	'''this is to add routes if we should continue with our partials'''
	def addRoutes(self, usedCities, allCities, cost):
		for i in range(len(allCities)):
			if self.find(allCities[i], usedCities) == -1:
				temp= []
				temp.append([])
				temp[0]= copy.deepcopy(usedCities)
				temp[0].append(allCities[i])
				temp.append(copy.deepcopy(cost))
				self.PQ.insert(0, temp)
				self.total += 1
		if(len(self.PQ) > self.maxQueueSize):
			self.maxQueueSize = len(self.PQ)

	''' <summary>
			This is the entry point for the branch-and-bound algorithm that you will implement
			</summary>
			<returns>results dictionary for GUI that contains three ints: cost of best solution, 
			time spent to find best solution, total number solutions found during search (does
			not include the initial BSSF), the best solution found, and three more ints: 
			max queue size, total number of states created, and number of pruned states.</returns> 
		'''
	def branchAndBound( self, time_allowance=60.0 ):
		results = {}
		results =self.greedy()
		list= []
		cities = self._scenario.getCities()
		ncities = len(cities)
		bssf = self._bssf
		cost = 0

		'''creating the initial reduced cost matrix'''
		for i in range(ncities):
			list.append([])
			for j in range(ncities):
				list[i].append(City.costTo(cities[i], cities[j]))
		'''reducing all the row costs by the smallest'''
		for i in range(ncities):
			cost += self.MinimizeBySmallestInRow(list, i)
			'''reducing all the col cost by smallest ... also dimensions are the same for both'''
		for i in range(ncities):
			cost += self.MinimizeBySmallestInCol(list, i)
		self.PQ = []
		for i in range(ncities):
			self.PQ.append([])
			self.PQ[i].append([])
			self.PQ[i][0].append(cities[i])
			self.PQ[i].append(copy.deepcopy(cost))
		cur = self.PQ.pop(0)[0][0]
		self.maxQueueSize = len(self.PQ)
		self.total = len(self.PQ)
		nextBssf = []
		nextBssf.append([])
		nextBssf[0].append(cur)
		nextBssf.append(cost)
		count = 0
		start_time = time.time()
		while len(self.PQ) > 1 and time.time()-start_time < time_allowance:
			count += 1
			nextBssf[1] = self.partials(list, cur._index, self.PQ[0][0][len(self.PQ[0][0]) - 1]._index, self.PQ[0][1])
			'''if the next bssf is better than our current we choose to go further down these paths'''
			if nextBssf[1] < bssf.cost:
				'''add the next code we found the cost to, to our list'''
				nextBssf[0].append(self.PQ[0][0][len(self.PQ[0][0]) - 1])
				'''remove the top of the queue'''
				self.PQ.pop(0)
				self.pruned +=1
				'''add all its child routes; ie if a->b is good we add a->b->c and a->b->d to the top of our pq'''
				self.addRoutes(nextBssf[0], cities, nextBssf[1])
				''' our new head is the head is the last cite we visited'''
				cur = self.PQ[0][0][len(self.PQ[0][0])-1]
				'''this is in case we are about to reach the end of a route'''
				if len(self.PQ[0][0]) == ncities: # should check if we've reached the max length of a route
					'''check the cost of the the last two cities'''
					nextBssf[1] = self.partials(list, cur._index, self.PQ[0][0][len(self.PQ[0][0]) - 1]._index, self.PQ[0][1])
					nextBssf[0].append(self.PQ[0][0][len(self.PQ[0][0]) - 1])
					'''then check the cost of going back to the first city'''
					nextBssf[1] = self.partials(list, self.PQ[0][0][len(self.PQ[0]) - 1]._index, self.PQ[0][0][0]._index, nextBssf[1])

					if nextBssf[1] < bssf.cost:
						end_time = time.time()
						results['cost'] = nextBssf[1]
						results['time'] = end_time - start_time
						results['count'] = count
						results['soln'] = TSPSolution(nextBssf[0])
						results['max'] = self.maxQueueSize
						results['total'] = self.total
						results['pruned'] = self.pruned
						bssf.cost = nextBssf[1]
					'''no matter what we have to pop the last thing off'''
					self.PQ.pop(0)
					self.pruned += 1
					cur = self.PQ[0][0][len(self.PQ[0][0]) - 1]
					nextBssf[1] = self.PQ[0][1]
			else:
				self.PQ.pop(0)
				self.pruned += 1
				cur = self.PQ[0][0][len(self.PQ[0][0])-1]
				nextBssf[1] = self.PQ[0][1]
		return results


	''' <summary>
		This is the entry point for the algorithm you'll write for your group project.
		</summary>
		<returns>results dictionary for GUI that contains three ints: cost of best solution, 
		time spent to find best solution, total number of solutions found during search, the 
		best solution found.  You may use the other three field however you like.
		algorithm</returns> 
	'''

	def tabuList (self, route):
		return True

	def fancy( self,time_allowance=60.0 ):
		results = self.greedy()
		bssf = results['soln']
		nCities = len(bssf.route)
		temp = copy.deepcopy(bssf)
		start_time = time.time()
		for i in range(nCities):
			for j in range(nCities):
				'''To Make Sure we don't exceed the time limit'''
				if time.time()-start_time >= time_allowance:
					break
				'''Recalibrating path costs for replacing an individual city'''
				temp.cost -= City.costTo(bssf.route[i], bssf.route[(i + 1)%nCities])
				temp.cost -= City.costTo(bssf.route[(i - 1)%nCities], bssf.route[i])
				temp.cost += City.costTo(bssf.route[j], bssf.route[i + 1])
				temp.cost += City.costTo(bssf.route[i - 1], bssf.route[j])

				'''altering the route paths'''
				city = copy.deepcopy(temp.route[i])
				temp.route[i] = copy.deepcopy(temp.route[j])
				temp.route[j] = city

				'''check to see if the new route is in the tabu list'''
				if (temp.route != self.tabuList(temp.route)):
					'''check to see if the cost has improved'''
					if (temp.cost < bssf.cost):
						bssf = copy.deepcopy(temp)
				'''revert list back so we can continue the algorithm'''
				temp.route[j] = copy.deepcopy(temp.route[i])
				temp.route[i]= city
		


      	class tabuList:
		def __init__(self):
			self.usedSolutions = {}
		def addSolution(self,solution):
			self.usedSolutions[solution] = True #This value could be anything
		def isTabu(self,solution):
			if solution in self.usedSolutions:
				return True
			else:
				return False 
