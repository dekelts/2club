#!/usr/bin/python3
import sys
import scipy.optimize
from math import ceil

# Compute the branching number of a vector V.
def compute(V, init = 10):
	if V == [1]*len(V):
		return len(V)
	if len(V) <= 1:
		return 0
	def h(x):
		return sum([x**(-v) for v in V])-1
	X = scipy.optimize.brenth(h,1, init)
	return X

class Graph:
	def __init__(self, edges):
		if edges == []:
			self.n = 0
		else:
			self.n = 1 + max([max(x) for x in edges])
		self.adj = [[] for i in range(self.n)]
		for u,v in edges:
			self.adj[u].append(v)
			self.adj[v].append(u)

	def degree(self, v):
		return len(self.adj[v])

	# Return a list of vertices with distance exactly k from s.
	def get_dist_k_vertices(self, s, k):
		dist = [None]*self.n
		dist[s] = 0
		Q = [s]
		while Q != []:
			u = Q[0]
			del Q[0]
			for v in self.adj[u]:
				if dist[v] == None:
					dist[v] = dist[u]+1
					Q.append(v)
		return [i for i in range(self.n) if dist[i] == k]

	# Return all pairs a,b of vertices such that δ(a,b)=3 and a < b.
	def get_dist3_pairs(self):
		R = []
		for b in range(3, self.n):
			R += [(a,b) for a in self.get_dist_k_vertices(b,3) if a < b]
		return R

# Graph with annotated vertices.
# For a vertex v, annotations[v] = 0 means that v was chosen to be in the deletion set S.
# annotations[v] = 2 means that v was chosen to be not in S.
# annotations[v] = 1 means that the membership of v in S was not determined.
class Graph_v(Graph):
	def __init__(self, edges):
		Graph.__init__(self, edges)
		self.m = self.n

	def DFS_visit(self, u, cc, current_cc, annotations, t):
		cc[u] = current_cc
		for v in self.adj[u]:
			if annotations[v] >= t and cc[v] == 0:
				self.DFS_visit(v, cc, current_cc, annotations, t)

	# Return a vector cc where cc[v] is the number of the connected component of v
	def calc_cc(self, annotations, t):
		cc = [0]*self.n
		current_cc = 0
		for u in range(self.n):
			if annotations[u] >= t and cc[u] == 0:
				current_cc += 1
				self.DFS_visit(u, cc, current_cc, annotations, t)
		return cc

#	Check if every pair of vertices in dist3_pairs is in different connected component of the graph
#	after removing vertices with anotation value < t.
	def is_2club(self, dist3_pairs, annotations, t = 1):
		cc = self.calc_cc(annotations, t)
		for u,v in dist3_pairs:
			if u < self.n and v < self.n and annotations[u] >= t and annotations[v] >= t and cc[u] == cc[v]:
				return False
		return True

# Graph with annotated edges
class Graph_e(Graph):
	def __init__(self, edges):
		Graph.__init__(self, edges)
		self.m = len(edges)
		self.edges = [[] for i in range(self.n)]
		e = 0
		for u,v in edges:
			self.edges[u].append(e)
			self.edges[v].append(e)
			e += 1

	def DFS_visit(self, u, cc, current_cc, annotations, t):
		cc[u] = current_cc
		for i,v in enumerate(self.adj[u]):
			if annotations[self.edges[u][i]] >= t and cc[v] == 0:
				self.DFS_visit(v, cc, current_cc, annotations, t)

	def calc_cc(self, annotations, t):
		cc = [0]*self.n
		current_cc = 0
		for u in range(self.n):
			if cc[u] == 0:
				current_cc += 1
				self.DFS_visit(u, cc, current_cc, annotations, t)
		return cc

#	check if every pair of vertices in dist3_pairs is in different connected component of the graph
	def is_2club(self, dist3_pairs, annotations, t = 1):
		cc = self.calc_cc(annotations, t)
		for u,v in dist3_pairs:
			if u < self.n and v < self.n and cc[u] == cc[v]:
				return False
		return True

##########################################################################################

# Create a branching rule for the graph H
# This method is faster than compute_br1, but may give a larger branching number
def compute_branching_number(H, dist3_pairs):
	if vertex_deletion:
		L = minimal_vertex_deletion_sets(H, dist3_pairs)
	else:
		L = minimal_edge_deletion_sets(H, dist3_pairs)
	return compute([len(x) for x in L]),L

def minimal_vertex_deletion_sets(H, dist3_pairs):
	if H.is_2club(dist3_pairs,[1]*H.n):
		return []
	L = []
	for k in range(1, (H.n-1)+1):
		for Del in choose(range(H.n), k):
			if check(L, Del):
				continue
			annotations = [1]*H.n
			for x in Del:
				annotations[x] = 0
			if H.is_2club(dist3_pairs, annotations):
				L.append(set(Del))

	return L

def minimal_edge_deletion_sets(H, dist3_pairs):
	if H.is_2club(dist3_pairs,[1]*H.m):
		return []

	L = []
	Eind = range(H.m)
	for k in range(1, H.m+1):
		for Del in choose(Eind, k):
			if check(L, Del):
				continue
			annotations = [1]*H.m
			for x in Del:
				annotations[x] = 0
			if H.is_2club(dist3_pairs, annotations):
				L.append(set(Del))
	return L

def choose(L, k, n = None):
	if n == None:
		n = len(L)
	if k == 0:
		return [[]]
	R = []
	for i in range(k-1,n):
		for S in choose(L, k-1, i):
			R.append(S+[L[i]])
	return R

def all_subsets(L):
	R = []
	for i in range(len(L)+1):
		R += choose(L, i)
	return R

def check(L, D):
	D1 = set(D)
	for X in L:
		if X.issubset(D1):
			return True
	return False

##########################################################################################

# Find an "optimal" branching rule for a graph (using the algorithm of Gramm et al)
def compute_br1(H, dist3_pairs):
	annotations = [1]*H.m
	X = 1000
	Cache = {}
	best_L = None
	for R in compute_br(H, dist3_pairs, annotations, Cache):
		L = []
		for F in R:
			if check(L, F):
				continue
			L.append(set(F))
		X1 = compute([len(x) for x in L])
		if X1 < X:
			X = X1
			best_L = L
	return X,best_L

def compute_br(H, dist3_pairs, annotations, Cache, d = 0):
	annotations_t = tuple(annotations)
	if annotations_t in Cache:
		return Cache[annotations_t]

##	if not H.is_2club(dist3_pairs, annotations, 2):
##		return []
	reduce(H, dist3_pairs, annotations)

	L = []
	c = [i for i in range(H.m) if annotations[i] == 0]
	if len(c) > 0:
		L = [[c]]
	if H.is_2club(dist3_pairs, annotations):
		return L

	for e in range(H.m):
		if annotations[e] == 1:

			annotations1 = annotations[:]
			annotations1[e] = 2
			L1 = compute_br(H, dist3_pairs, annotations1, Cache, d+1)

			annotations2 = annotations[:]
			annotations2[e] = 0
			L2 = compute_br(H, dist3_pairs, annotations2, Cache, d+1)

			for X in L1:
				for Y in L2:
					L.append(X+Y)

			L = remove_subsumed(L)

	Cache[annotations_t] = L
	return L

# Find elements of the annotations vector that are 1 and cannot be changed to 2
def reduce(H, dist3_pairs, annotations):
	while 1:
		flag = False
		for x in range(H.m):
			if annotations[x] == 1:
				annotations[x] = 2
				if not H.is_2club(dist3_pairs, annotations, 2):
					annotations[x] = 0
					flag = True
					break
				annotations[x] = 1
		if not flag:
			break

# test if X1[i] >= X2[i] for all i
def subsumed(X1,X2):
	if len(X1) > len(X2):
		return False
	if X1 ==  X2: return False
	for i in range(len(X1)):
		if len(X1[i]) < len(X2[i]):
			return False
	return True

def list_subsumed(L, X2):
	for X1 in L:
		if subsumed(X1, X2):
			return True
	return False

def remove_subsumed(L):
	L2 = []
	for i in range(len(L)):
		L[i].sort(key=lambda x: len(x))
	for X2 in L:
		if not list_subsumed(L2, X2):
			L2 = [X1 for X1 in L2 if not subsumed(X2, X1)]+[X2]
	return L2

##########################################################################################

def make_pair(x,y):
	return (min(x,y),max(x,y))

def bn(X):
	return ceil(X*1000)/1000

def vstr(i):
	return f"v{i+1}"

def estr(e):
	return vstr(e[0])+vstr(e[1])

def lstr(L,E):
	if vertex_deletion:
		L2 = ['{'+','.join([vstr(x) for x in X])+'}' for X in L]
	else:
		L2 = ['{'+','.join([estr(E[x]) for x in X])+'}' for X in L]
	return ' '.join(L2)

def generate_rule(E, dist3_pairs, forbidden_edges, forbidden_vertices, Cache, depth = 0):
	key = (tuple(E), tuple(forbidden_edges), tuple(forbidden_vertices), tuple(dist3_pairs))
	if key in Cache:
		return Cache[key]
	indent = " "*(depth*2)

	H = Graph_v(E) if vertex_deletion else Graph_e(E)
	if gramm:
		X,L = compute_br1(H, dist3_pairs)
	else:
		X,L = compute_branching_number(H, dist3_pairs)
	output = indent+f"Branch on {lstr(L,E)} ({bn(X)})\n"
	if X < stop_value:
		output = indent+f"Branch on {lstr(L,E)} ({bn(X)})\n"
		Cache[key] = X,output
		return X,output
	if depth == max_depth:
		output = indent+f"Branch on {lstr(L,E)} ({bn(X)})\n"
		Cache[key] = X,output
		return X,output

	all_pairs = H.get_dist3_pairs()
	potential_pairs = [x for x in all_pairs if x not in dist3_pairs]

	if potential_pairs == []:
		output = indent+f"Branch on {lstr(L,E)} ({bn(X)})\n"
		Cache[key] = X,output
		return X,output

	forbidden_edges = forbidden_edges.copy()
	for pair in dist3_pairs:
		# Find edges that are forbidden when δ(pair)=3
		if pair not in forbidden_edges:
			forbidden_edges.append(pair)
		for v in H.adj[pair[0]]:
			if make_pair(v,pair[1]) not in forbidden_edges:
				forbidden_edges.append(make_pair(v,pair[1]))
		for v in H.adj[pair[1]]:
			if make_pair(v,pair[0]) not in forbidden_edges:
				forbidden_edges.append(make_pair(v,pair[0]))

	# Go over all potential pairs and generate a rule for each pair. Then select the best rule.
	for pair in potential_pairs:
		output2 = ""
		X1 = 0
		output2 += indent+f"If δ({vstr(pair[0])},{vstr(pair[1])}) = 3\n"
		X1,O = generate_rule(E, dist3_pairs+[pair], forbidden_edges, forbidden_vertices, Cache, depth+1)
		output2 += O

		X2 = 0
		forbidden_edges3 = forbidden_edges[:]
		if pair not in forbidden_edges and pair[0] not in forbidden_vertices and pair[0] not in forbidden_vertices:
			output2 += indent+f"If δ({vstr(pair[0])},{vstr(pair[1])}) = 1\n"
			X2,O = generate_rule(E+[pair], dist3_pairs, forbidden_edges, forbidden_vertices, Cache, depth+1)
			output2 += O
			forbidden_edges3.append(pair)

		# Look for paths pair[0],x,pair[1] where x is a vertex of H
		X3 = 0
		for v in H.adj[pair[0]]:
			edge = make_pair(v,pair[1])
			if edge not in forbidden_edges3 and edge[0] not in forbidden_vertices and edge[1] not in forbidden_vertices:
				output2 += indent+f"If δ({vstr(pair[0])},{vstr(pair[1])}) = 2 and {vstr(edge[0])},{vstr(edge[1])} are adjacent\n"
				X3b,O = generate_rule(E+[edge], dist3_pairs, forbidden_edges3, forbidden_vertices, Cache, depth+1)
				X3 = max(X3, X3b)
				output2 += O

				# A simple optimization that does not appear in the paper:
				# since we check the case that 'edge' is an edge in G in the recursive call above,
				# we can assume in the followng recursive calls that 'edge' is not an edge in G
				forbidden_edges3.append(edge)

		for v in H.adj[pair[1]]:
			edge = make_pair(v,pair[0])
			if edge not in forbidden_edges3 and edge[0] not in forbidden_vertices and edge[1] not in forbidden_vertices:
				output2 += indent+f"If δ({vstr(pair[0])},{vstr(pair[1])}) = 2 and {vstr(edge[0])},{vstr(edge[1])} are adjacent\n"
				X3b,O = generate_rule(E+[edge], dist3_pairs, forbidden_edges3, forbidden_vertices, Cache, depth+1)
				X3 = max(X3, X3b)
				output2 += O
				forbidden_edges3.append(edge)

		if pair[0] not in forbidden_vertices and pair[1] not in forbidden_vertices:
			for v in range(H.n):
				if v in forbidden_vertices or v in pair: continue
				if v in H.adj[pair[0]] or v in H.adj[pair[1]]: continue
				edge1 = make_pair(pair[0],v)
				edge2 = make_pair(pair[1],v)
				if edge1 not in forbidden_edges3 and edge2 not in forbidden_edges3:
					output2 += indent+f"If δ({vstr(pair[0])},{vstr(pair[1])}) = 2 and {vstr(v)} is adjacent to {vstr(pair[0])},{vstr(pair[1])}\n"
					X3b,O = generate_rule(E+[edge1,edge2], dist3_pairs, forbidden_edges3, forbidden_vertices, Cache, depth+1)
					X3 = max(X3, X3b)
					output2 += O

		# A path pair[0],v,pair[1] using a new vertex v
		X4 = 0
		v = H.n
		e1 = make_pair(pair[0],v)
		e2 = make_pair(pair[1],v)
		if e1 not in forbidden_edges3 and e2 not in forbidden_edges3 and pair[0] not in forbidden_vertices and pair[1] not in forbidden_vertices:
			output2 += indent+f"Otherwise, there is a vertex {vstr(v)} which is adjacent to {vstr(pair[0])},{vstr(pair[1])}\n"
			X4,O = generate_rule(E+[e1,e2], dist3_pairs, forbidden_edges3, forbidden_vertices, Cache, depth+1)
			output2 += O

		Y = max(X1,X2,X3,X4)
		if Y < X:
			X = Y
			output = output2
		if X < stop_value:
			break

	Cache[key] = X,output
	return X,output

def generate_rule1(E, dist3_pairs, forbidden_edges, forbidden_vertices):
	E = [(min(x),max(x)) for x in E]
	forbidden_edges = [(min(x),max(x)) for x in forbidden_edges]
	X,O = generate_rule(E, dist3_pairs, forbidden_edges, forbidden_vertices, {})
	print(O)
	return X,O.count("Branch")

max_depth = 10
vertex_deletion = True
gramm = False

for x in sys.argv[1:]:
	if x == "-e":
		vertex_deletion = False
	elif x == "-g":
		gramm = True

E0 = [(0,1),(1,2),(2,3)]
E1 = E0+[(3,4)]
E2 = E1+[(0,5)]

if vertex_deletion:
	stop_value = 3.1
	X = []

	print("Rule",len(X)+1)
	E = E1 + [(3,5)]
	X.append(generate_rule1(E, [(0,3)], [], []))

# Case 1: deg(0)=deg(3)=2

# 5 is adjacent to 2
	print("Rule",len(X)+1)
	E = E2 + [(5,2)]
	X.append(generate_rule1(E, [(0,3)], [], [0,3]))

# a vertex 6 that is adjacent to 2 and not to 1
	print("Rule",len(X)+1)
	E = E2 + [(2,6)]
	X.append(generate_rule1(E, [(0,3)], [(1,6)], [0,3]))

# The next rules handle the case that there is no vertex that is adjacent to 2 and 3.

# no edges 51 or 42.
	print("Rule",len(X)+1)
	E = E2
	X.append(generate_rule1(E, [(0,3)], [], [0,1,2,3]))

# an edge 51 exists but not 42.
# We check the two possible connections of these vertices to the rest of the graph
# Either there is an edge 46 or an edge 56
# (if neither edge exists than we can use a reduction rule)
	print("Rule",len(X)+1)
	E = E2 + [(5,1),(5,6)]
	X.append(generate_rule1(E, [(0,3)], [], [0,1,2,3]))

	print("Rule",len(X)+1)
	E = E2 + [(5,1),(4,6)]
	X.append(generate_rule1(E, [(0,3)], [], [0,1,2,3]))

# The next rules handle the case that there is at least one vertex that is adjacent to 2 and 3.

	print("Rule",len(X)+1)
	E = E2 + [(1,6),(2,6)]
	X.append(generate_rule1(E, [(0,3)], [(5,1)], [0,3]))

	print("Rule",len(X)+1)
	E = E2 + [(1,5),(2,4),(1,6),(2,6),(5,6)]
	X.append(generate_rule1(E, [(0,3)], [], [0,3]))

	print("Rule",len(X)+1)
	E = E2 + [(1,5),(2,4),(1,6),(2,6),(5,7)]
	X.append(generate_rule1(E, [(0,3)], [], [0,3]))

# Case 2: deg(0)=1, deg(3)=1

	print("Rule",len(X)+1)
	E = E0 + [(1,4),(4,5)]
	X.append(generate_rule1(E, [(0,3)], [(2,4)], [0,3]))

# Case 3: deg(0)=1, deg(3)=2

	print("Rule",len(X)+1)
	E = E1 + [(2,5)]
	X.append(generate_rule1(E, [(0,3)], [(1,5)], [0,3]))

	print("Rule",len(X)+1)
	E = E1 + [(4,5)]
	X.append(generate_rule1(E, [(0,3)], [(1,5)], [0,3]))

	print("Rule",len(X)+1)
	E = E1 + [(1,5),(5,6)]
	X.append(generate_rule1(E, [(0,3)], [(1,6)], [0,3]))

else:
	stop_value = 2.55
	X = []

	print("Rule",len(X)+1)
	E = [(0,1),(1,2),(2,3),(3,4)]
	X.append(generate_rule1(E, [(0,3)], [], []))

	print("Rule",len(X)+1)
	E = [(0,1),(1,2),(2,3),(2,4)]
	X.append(generate_rule1(E, [(0,3)], [(1,4)], [0,3]))


for i in range(len(X)):
	print(f"Rule {i+1} BN = {bn(X[i][0])} cases = {X[i][1]}")
print(f"max BN = {bn(max(x[0] for x in X))}")
