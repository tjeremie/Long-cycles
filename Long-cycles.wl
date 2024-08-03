(* ::Package:: *)

(* ::Title:: *)
(*Longer cycles and larger intersections - Code complement*)


(* ::Subtitle:: *)
(*Code used in the paper "Longer cycles and larger intersections" by Carla Groenland, Sean Longbrake, Raphael Steiner, J\[EAcute]r\[EAcute]mie Turcotte and Liana Yepremyan*)
(**)
(*This script implements the computer search described in Section 3 of the paper.*)


(* ::Chapter:: *)
(*Code*)


(* 
General implementation considerations

Ordered bipartite graphs are implemented here as an association with three keys :
 - leftVertices and rightVertices are (ordered) lists of vertices, corresponding to the vertices of 
   X and Y with the orders sigma_X and sigma_Y, respectfully, in the paper.
 - edges is a list of pairs of vertices, where for each pair the first vertex is in leftVertices 
   and the second is in rightVertices.

Configurations are implemented here slightly differently than in the paper: the orders tau_h are implicit.
Here, configurations are an association with three keys :
 - leftVerticesGrouped and rightVerticesGrouped are list of lists. Each sublist constains a list of 
   vertices. The order of the groups follows to the order of leftVertices and rightVertices, respectfully 
   (sigma_X and sigma_Y, in the paper). The order within the groups corresponds to the orders tau_h in 
   the paper. 
 - crossEdges is a list of pairs of vertices, where for each pair the first vertex is in one of the lists 
   in leftVerticesGrouped, and the second vertex is in one of the lists in rightVerticesGroups.
In other words, instead of encoding configurations as a list of orderings, we encode then as something very
close to the configuration graph itself. This will be easier to work with when extending configurations in
the main iterative search (described in Lemma 3.4).

For simplicity, for the empty configuration leftVerticesGrouped and rightVerticesGrouped will be a list
containing, for each vertex in leftVertices and in rightVertices respectively, an empty list. In other
words, the sequence H_0,H_1,\dots, described in the proof of Lemma 3.4, will be obtained by always keeping
the same vertex set, and only adding edges.

Configuration graphs are implemented as associations with many keys, containing all the information
necessary to find good cycles, etc. (see makeConfigurationGraph below). For a configuration tau, left 
vertices are those in C_1^tau and the right vertices are those in C_2^tau. 

Note: Working with Mathematica edge objects is somewhat delicate. For example, a\[UndirectedEdge]b and b\[UndirectedEdge]a are not 
considered to be same when checking for equality, say. We thus often use Sort to order the two vertices.
*)


(* ::Section:: *)
(*Considering all configurations up to isomorphism*)


(*
	In this section, we implement the procedure described in Lemma 3.1 to check if two ordered 
	bipartite graphs should be considered equivalent, that is the configurations which arise from
	them would be the same up to relabelling.
*)


(* Given an ordered bipartite graph h, converts it to a Mathematica graph object. *)
orderedBipartiteToGraph[h_] := Graph[Join[h["leftVertices"], h["rightVertices"]], 
   Apply[UndirectedEdge, h["edges"], {1}], VertexLabels -> "Name", 
   GraphLayout -> "BipartiteEmbedding"]


(* Given an ordered bipartite graph h, lists all possible pairs of orderings on leftVertices and 
rightVertices. *)
permutationPairs[h_]:=Tuples[{Permutations[h["leftVertices"]],Permutations[h["rightVertices"]]}];


(* Given a list of length n and a formal variable label, it adds objects label_i (for i between 1 and n)
at every 2nd position in the list. *)
listAdd[list_,label_]:=Riffle[list,Subscript[label,#]&/@Range[Length[list]]]


(* Given a list of vertices, and a formal variable label, we create a cycle, which is a list of edges, 
which follows the cyclic order inherited from list, but adding a new distinct vertex at every 2nd position. *)
makeCycle[list_,label_]:=UndirectedEdge@@@(Sort/@Subsequences[Join[listAdd[list,label],{list[[1]]}],{2}])


(* Given a Mathematica graph h which is bipartite, and leftVertexOrder and rightVertexOrder which are
orderings on the vertices of each part of h, we add cycles on each side using the makeCycle function.*)
addCycles[h_,{leftVertexOrder_,rightVertexOrder_}]:=
Graph[VertexList[h],Join[EdgeList[h],makeCycle[leftVertexOrder,label1],makeCycle[rightVertexOrder,label2]]]


(* Given an ordered bipartite graph h, returns the list of pairs of orderings on the vertices of h, 
up to equivalence. Uses permutationPairsTo generate all the possible pairs of orderings. Then, we use
makeCycle to add cycles to each side (part) of the graph. Then, we delete isomorphic graphs. For 
efficiency, isomorphism is checked by looking at graph equality on the canonical version 
(see CanonicalGraph) of each graph. To ensure that in this isomorphism edges of the original graphs are
mapped to other such edges, when we add the cycles we do not simply add edges, we add paths of length 2:
vertices of degree 2 (which can necessarily only be new vertices) must be mapped to other such vertices.
*)
distinctVertexOrderings[h_]:=
DeleteDuplicatesBy[permutationPairs[h],CanonicalGraph[addCycles[orderedBipartiteToGraph[h],#]]&]


(* Returns in ordered bipartite graphs format what was obtained by distinctVertexOrderings. *)
distinctOrderedBipartiteOnH[h_]:=Association["leftVertices" -> #[[1]], "rightVertices" -> #[[2]], 
    "edges" -> h["edges"]]&/@distinctVertexOrderings[h]


(* ::Section:: *)
(*Graph creation from configuration*)


(*
	In this section, we create the configuration graph for a given configuration.
*)


(* Given a path as a list of vertices, returns the list of edges in this path. *)
pathToEdges[path_] := Apply[UndirectedEdge, Sort /@ Subsequences[path, {2}], {1}]


(* Given a configuration, creates the associated configuration graph. This is an an association 
containing most information about the configuration graph. See below for more details about each key.
If finishCycles is true, we add the edge between the first and last vertex on each side, i.e. we do 
construct C_1^tau, C_2^tau: this is the version as presented in the paper, which we will use when 
building the linear program to find good long cycles. If finishCycles is False, we do not add this edge 
to the graph; in the next section we will see that when we use Lemma 3.1 to find good long cycles, we 
can use path finding. Note that when a bag in the configuration is empty (this would correspond to a 
vertex of degree zero in h), it is simply ignored, no vertices are created in the configuration graph 
for this. *)
makeConfigurationGraph[configuration_, finishCycles_] :=
	Module[
		{leftVerticesGrouped, rightVerticesGrouped, leftVertices, rightVertices, leftEdges, 
		 rightEdges, graph, leftSafeEdges, rightSafeEdges, leftDangerousEdges, rightDangerousEdges, 
		 sideEdges, crossEdges},
		
		(* Extract groups of vertices from the configuration *)
		leftVerticesGrouped = configuration["leftVerticesGrouped"];
		rightVerticesGrouped = configuration["rightVerticesGrouped"];
		
		(* Flatten these lists to obtain all the vertices on each side, in order*)
		leftVertices = Flatten[leftVerticesGrouped];
		rightVertices = Flatten[rightVerticesGrouped];
		
		(* From those, then obtain the lists of edges on each side *)
		leftEdges = pathToEdges[Flatten[leftVertices]];
		rightEdges = pathToEdges[Flatten[rightVertices]];
        
		(* If finishCycles is True we add the edges edges between first and last vertices to 
		make each side of the graph a cycle. *)
		If[finishCycles,
			leftEdges = Append[leftEdges, UndirectedEdge[leftVertices[[1]], leftVertices[[-1]]]];
			rightEdges = Append[rightEdges, UndirectedEdge[rightVertices[[1]], rightVertices[[-1]]]];
		];
		
		(* We create the lists of safe edges on each side as the pairs for which both ends are consecutive
		and in the same bag *)
		leftSafeEdges = Flatten[pathToEdges /@ leftVerticesGrouped];
		rightSafeEdges = Flatten[pathToEdges /@ rightVerticesGrouped];
        
        (* And from those, we can compute which edges are dangerous. *)
		leftDangerousEdges = Complement[leftEdges, leftSafeEdges];
		rightDangerousEdges = Complement[rightEdges, rightSafeEdges];
        
        (* This is the list of all edges in the configuration graph that aren't cross edges, i.e. all the
        edges of the main cycles. *)
		sideEdges = Join[leftEdges, rightEdges];
		
		(* Cross edges are converted to Mathematica edge format. *)
		crossEdges = Apply[UndirectedEdge, configuration["crossEdges"], {1}];
		
		(* This is configuration graph in Mathematica graph format. We cannot only return this however,
		as we need further information about "types" of edges, for instance. *)
		graph = Graph[Join[leftVertices, rightVertices], Join[sideEdges, crossEdges]];
		
		(* We return an association with all this information. *)
		Association[
			"leftVertices" -> leftVertices, 
			"rightVertices" -> rightVertices,
			"leftDangerousEdges" -> leftDangerousEdges,
			"rightDangerousEdges" -> rightDangerousEdges, 
			"leftEdges"->leftEdges, 
			"rightEdges"->rightEdges,
			"sideEdges" -> sideEdges,
			"crossEdges" -> crossEdges,
			"graph" -> graph
		]
    ]


(* ::Section:: *)
(*Path finding*)


(* 
	In this section, we implement the test for finding good long cycles from Lemma 3.1. Considering that
	we wish to find two good cycles which cover all side edges of the configuration graph, and at least
	one cross edge, it is sufficient to find two paths, one from the first vertex on the left side to the 
	last vertex on the left side, and a second one analogously for the right side, such that they cover 
	all the side edges as well as at least one cross edge, in the graph generated above with finishCycles
	being False. Indeed, any such pair of paths directly extends to cycles in the actual configuration
	graph.
*)


(* Given a graph configuration g and two paths, checks if all the edges of the main cycles are covered
by the paths, which is one of the main conditions in Lemma 3.1. *)
coversAllSideEdges[g_, path1_, path2_] := 
	ContainsAll[Join[pathToEdges[path1], pathToEdges[path2]], g["sideEdges"]]


(* The other condition in Lemma 3.1 is that this pair of paths intersects at least one cross edge. *)
intersectsCrossEdges[g_, path1_, path2_] := 
	IntersectingQ[Join[pathToEdges[path1],pathToEdges[path2]], g["crossEdges"]]


(* Given a configuration graph, returns the list of all good paths for the left side, i.e. paths in the
configuration graph between the first and last vertices on the main cycle C_1^tau which do not contain
any dangerous edges on the right side. Given that the pair of paths we will later find must cover all
side edges, but that good paths on the right side cannot contain left dangerous edges, we enforce here that
the left side good paths contain all left dangerous edges. *)
findPathsLeft[g_] :=
	Select[
		FindPath[
			EdgeDelete[g["graph"], g["rightDangerousEdges"]], 
			g["leftVertices"][[1]], 
			g["leftVertices"][[-1]], 
			Infinity, 
			All
		], 
		ContainsAll[pathToEdges[#1], g["leftDangerousEdges"]] &
     ]


(* Similar function for good paths on the right side. However, to reduce computation time, we run this
function after choosing good paths on the left side, adding some extra conditions (see comments below).
This function also checks the requirement that the pair of paths must contain all side edges and at least
one cross edge. *)
rightPathExists[g_, leftPath_] :=
	AnyTrue[
		FindPath[
			EdgeDelete[
				g["graph"], 
				Union[
					g["leftDangerousEdges"],
					(* We add a very strong condition, that the two paths never intersect on side edges (
					they can however intersect on cross edges). This reduces computation time, and appears
					to not remove too many possibly interesting paths. *)
					Intersection[pathToEdges[leftPath], g["sideEdges"]]
				]
			],
			g["rightVertices"][[1]], 
			g["rightVertices"][[-1]], 
			Infinity, 
			All
        ], 
        (* Verifies that this pair of paths covers all side edges, and at least one cross edge. *)
        coversAllSideEdges[g,leftPath, #1] && 
        intersectsCrossEdges[g,leftPath,#1]&
    ]


(* First generates all good left paths, then checks if for at least one of them there exists a good 
right path such that together they cover all side edges and at least one cross edge. *)
pathsExist[g_] := AnyTrue[findPathsLeft[g], rightPathExists[g, #1]&]


(* ::Section:: *)
(*Iterative process*)


(*
	In this section, we implement the algorithm described in paths (1)-(2)-(3) of the proof of Lemma 3.4.
*)


(* For an ordered bipartite graph h, an edge e of h, and a configuration of a subgraph h' of h not containing
this new edge, results the list of configurations of on h'+e that can be obtained by adding a new cross edge (and
its end vertices on each side)*)
extendConfiguration[h_, edgeInH_, configuration_] := 
	Module[
		{newLeftVertex, newRightVertex, posLeft, posRight},
		
		(* We choose names for the new vertices to be added to each side for this new edge. Here, 
		they will be of the form l_{e,i} or r_{e,i}, where l,r is chosen depending on which side the 
		vertex is added, e is the edge in h corresponding to the edge we are adding to the configuration
		graph, and i is the iteration in the algorithm (here obtained by looking at how many cross edges
		are already in the configuration graph). *)
		newLeftVertex = Subscript[l, {edgeInH[[1]], Length[configuration["crossEdges"]] + 1}]; 
		newRightVertex = Subscript[r, {edgeInH[[2]], Length[configuration["crossEdges"]] + 1}];
		
		(* The indexes in the vertex lists of h of both endpoints of the new edge. This will tell us
		the indexes of the bags in the configuration where we must add the new vertices for the new cross
		edge. *)
		posLeft = FirstPosition[h["leftVertices"], edgeInH[[1]]][[1]]; 
		posRight = FirstPosition[h["rightVertices"], edgeInH[[2]]][[1]]; 
		
		Flatten[
			Table[
				(* We define the new configuration if we add the new vertex on the left at position i
				inside the appropriate bag of leftVerticesGrouped (the bag at index posLeft), and
				analogously on the right with j. We also append the new cross edge to crossEdges.*)
				Association[
					"leftVerticesGrouped" -> Insert[configuration["leftVerticesGrouped"], 
						newLeftVertex, {posLeft, i}], 
					"rightVerticesGrouped" -> Insert[configuration["rightVerticesGrouped"], 
						newRightVertex, {posRight, j}],
					"crossEdges" -> Append[configuration["crossEdges"], {newLeftVertex, newRightVertex}]]
				
				(* We iterate over all possible pairs i,j: if there are currently x vertices in the bag,
				we can insert the new vertex at x+1 possible positions.*)
				,{i, 1, Length[configuration["leftVerticesGrouped"][[posLeft]]] + 1}
				,{j, 1, Length[configuration["rightVerticesGrouped"][[posRight]]] + 1}
			]
		(* Given that the table has two indexes, we must flatten the list by one dimension, as we simply
		want a list of configurations, and not a matrix (or list of lists). *)
		, 1]
	]


(* This function applies the previous function to a list of configurations, and flattens the result to obtain
a single list. *)
nextConfigurations[h_, edgeInH_, currentConfigurations_] :=
    Flatten[(extendConfiguration[h, edgeInH, #1]&) /@ currentConfigurations, 1]


pathFindingComputation[h_] :=
	Module[
		{currentConfigurations},
		
		(* We initialize the list of configurations with only the empty configuration (the number of bags
		depends on the number of vertices of h, but they are all empty). This is part (2) of the 
		algorithm as described in the paper. *)
		currentConfigurations = {
			<|
				"leftVerticesGrouped" -> ConstantArray[{}, Length[h["leftVertices"]]],
				"rightVerticesGrouped" -> ConstantArray[{}, Length[h["rightVertices"]]],
				"crossEdges" -> {}
			|>
		};
		
		(* We repeatedly iterate through the edges of h, extend the configurations, and remove the ones
		for which Lemma 3.1 guarantees the presence of a good long cycle in the configuration graph.
		This is part (3) of the algorithm described in the paper. *)
		Do[
			Print["Iteration : ", it];
			
			(* Given the configurations from the previous step, we find all new configurations obtained by 
			extension corresponding to adding the next edge of h. *)
			currentConfigurations = nextConfigurations[h, h["edges"][[it]], currentConfigurations];
			
			Print["Number of configurations extending configurations from previous iteration: ", Length[currentConfigurations]];
			
			(* We then filter the configurations, which is done by first looking at the configuration
			graph corresponding to the configuration and applying the path-finding method defined above.
			We only keep configurations for which we cannot guarantee the presence of good long cycles. *)
			currentConfigurations = 
				Select[currentConfigurations,!pathsExist[makeConfigurationGraph[#,False]]&];
				
			Print["Number of configurations after filtering using criterion of Lemma 3.1: ", Length[currentConfigurations]]
			
			,{it, 1, Length[h["edges"]]}
		];
		
		(* We return all surviving configurations. These will be tested using the linear program. *)
		currentConfigurations
	]


(* ::Section:: *)
(*Linear program version*)


(*
	In this section, we implement the linear program described in Section 3 of the paper.
*)


(* Given a Mathematica undirected edge, sorts it (to guarantee uniformity, as we wish to create 
exactly one variable per edge.) *)
sortEdge[a_\[UndirectedEdge]b_]:=Sort[{a,b}][[1]]\[UndirectedEdge]Sort[{a,b}][[2]]


(* Given an edge, creates the formal variable (w_e) for use in the linear program. *)
toVar[edge_]:=Subscript[w,sortEdge[edge]]


(* For a (good) cycle and a main cycle (either C_1^tau or C_2^tau), creates the inequality 
representing that the main cycle must have a larger weight. *)
cycleSumLeq[cycle_,mainCycle_]:=Total[toVar/@cycle]<=Total[toVar/@mainCycle]


(* For both main cycles (C_1^tau and C_2^tau), equality representing that their weight 
must be the same. *)
equalCycles[mainCycle1_,mainCycle2_]:=Total[toVar/@mainCycle1]==Total[toVar/@mainCycle2]


(* Given a configuration, creates the linear program and returns True if it is unfeasible, i.e. indicating
that no weight assignment is such that there is no good long cycle. *)
linearProgramCheck[configuration_]:=
	Module[
		{configurationGraph,allEdges,goodCycles1,goodCycles2,goodCycles,leftMainCycle,rightMainCycle,solution},
		
		(* We first create the configuration graph from the configuration. Here, we use finishCycles=True,
		since we want all cycles to be present. *)
		configurationGraph=makeConfigurationGraph[configuration, True];
		
		(* We extract the list of edges in the configuration graph. *)
		allEdges=sortEdge/@Join[configurationGraph["sideEdges"],configurationGraph["crossEdges"]];
		
		(* The list of cycles not including any dangerous edges on the left side. *)
		goodCycles1=FindCycle[
			(* We apply the FindCycle function on the subgraph obtained by removing the dangerous edges. *)
			EdgeDelete[configurationGraph["graph"],configurationGraph["leftDangerousEdges"]],
			
			(* Option to select all cycles of any length. *)
			Infinity,
			
			(* Option to find All cycles. *)
			All
		];
		
		(* Similarly, the list of cycles not including any dangerous edges on the right side. *)
		goodCycles2=FindCycle[
			EdgeDelete[configurationGraph["graph"],configurationGraph["rightDangerousEdges"]],
			Infinity,
			All
		];
		
		(* Joining these, we obtain the list of all good cycles in the configuration graph. *)
		goodCycles=Map[sortEdge,Join[goodCycles1,goodCycles2],{2}];
		
		(* We also obtain the two main cycles. *)
		leftMainCycle=sortEdge/@configurationGraph["leftEdges"];
		rightMainCycle=sortEdge/@configurationGraph["rightEdges"];
		
		(* Creating and solving the linear program*)
		solution=LinearOptimization[
			(* As mentioned in the paper, we are only concerned with feasability, so we choose 1 
			as the objective function. *)
			1,
			
			(* The list of equalities and inequalities. *)
			{
				(* As per the definition of the linear program in the paper, the main cycles must have 
				the same weight. *)
				equalCycles[leftMainCycle,rightMainCycle],
				
				(* Also, for every good cycle its total weight is at most the total weight
				for of one of the main cycles. *)
				cycleSumLeq[#,leftMainCycle]&/@goodCycles,
				
				(* As described in the paper, all cross edges must have a weight of at least 1. *)
				#>=1&/@(toVar/@configurationGraph["crossEdges"]),
				
				(* Otherwise, the edges must have a weight of at least 0. *)
				#>=0&/@(toVar/@configurationGraph["sideEdges"])
			},
			
			(* The list of variables, there is one for each edge of the configuration graph. *)
			toVar/@allEdges,
			
			(* We return the minimum value of the objective function. If this is Infinity, this means
			the linear program is not feasible. *)
			"PrimalMinimumValue"
		];
		
		solution==Infinity
]


(* For a list of configuration, returns True if for every configuration the linear program indicates
that there always exists a good long cycle. The Quiet function removes the warning stating that 
the program is not feasible. *)
linearProgramCheckAll[configurationList_]:=Quiet[AllTrue[configurationList,linearProgramCheck]]


(* ::Chapter:: *)
(*Computation*)


(*
	In this chapter, we run the computation (first the path finding method, and the linear program) 
	for both K_{3,3} and Q_3^+.
*)


(* ::Section:: *)
(*K_{3,3}*)


(* Definition of K_{3,3} as an ordered bipartite graph .*)
k33=<|
	"leftVertices"->{a1,a2,a3},
	"rightVertices"->{b1,b2,b3},
	"edges"->{{a1,b1},{a1,b2},{a1,b3},{a2,b1},{a2,b2},{a2,b3},{a3,b1},{a3,b2},{a3,b3}}
|>;


(* We display the graph. *)
orderedBipartiteToGraph[k33]


(* We confirm there is, up to equivalence, only one ordered bipartite graph on K_{3,3}. *)
Length[distinctOrderedBipartiteOnH[k33]]


(* Path finding method (Lemma 3.1) applied to K_{3,3}. *)
(pathFindingResultsk33=pathFindingComputation[k33];)//AbsoluteTiming


(* For the 72 configurations for which Lemma 3.1 cannot guarantee there will always be a good
long cycles, we use the linear program. *)
linearProgramCheckAll[pathFindingResultsk33]//AbsoluteTiming


(* ::Section:: *)
(*Hypercube+edge*)


(* Definition of Q_3^+ as an ordered bipartite graph. *)
hypercubePlusEdge=<|
	"leftVertices"->{a1,a2,a3,a4},
	"rightVertices"->{b1,b2,b3,b4},
	"edges"->{{a1,b2},{a1,b3},{a2,b2},{a2,b3},{a3,b2},{a3,b3},
			 {a1,b4},{a2,b4},{a4,b4},{a2,b1},{a3,b1},{a4,b1},{a4,b2}}
|>;


(* There are exactly two ordered bipartite graphs on Q_3^+. *)
{hypercubePlusEdge1,hypercubePlusEdge2}=distinctOrderedBipartiteOnH[hypercubePlusEdge]


(* ::Subsection:: *)
(*First ordered bipartite graph on Q_3^+*)


(* We display the graph. *)
orderedBipartiteToGraph[hypercubePlusEdge1]


(* Path finding method (Lemma 3.1) applied to K_{3,3}. *)
(pathFindingResultsHypercubePlusEdge1=pathFindingComputation[hypercubePlusEdge1];)//AbsoluteTiming


(* For the 12 configuration for which Lemma 3.1 cannot guarantee there will always be a good
long cycles, we use the linear program. *)
linearProgramCheckAll[pathFindingResultsHypercubePlusEdge1]//AbsoluteTiming


(* ::Subsection:: *)
(*Second ordered bipartite graph on Q_3^+*)


(* We display the graph. *)
orderedBipartiteToGraph[hypercubePlusEdge2]


(* Path finding method (Lemma 3.1) applied to K_{3,3}. *)
(pathFindingResultsHypercubePlusEdge2=pathFindingComputation[hypercubePlusEdge2];)//AbsoluteTiming


(* There are no configurations that need to be checked with the linear program in this case. *)
Length[pathFindingResultsHypercubePlusEdge2]
