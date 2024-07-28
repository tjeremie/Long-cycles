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
makeCycle[list_,label_]:=UndirectedEdge@@@(Sort/@Subsequences[Join[listAdd[path,label],{path[[1]]}],{2}])


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
        
        (* This is the list of all edges in the configuration graph that aren't cross edges.*)
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


coversAllEdges[g_, {path1_, path2_}] := 
	ContainsAll[Join[pathToEdges[path1], pathToEdges[path2]], g["sideEdges"]]


findPathsLeft[g_] :=
	Select[
		FindPath[
			EdgeDelete[g["graph"], g["rightDangerousEdges"]], 
			g["leftVertices"][[1]], 
			g["leftVertices"][[-1]], 
			{1, Infinity}, 
			All
		], 
		ContainsAll[pathToEdges[#1], g["leftDangerousEdges"]] && 
		IntersectingQ[pathToEdges[#1], g["crossEdges"]] &
     ]


rightPathExists[g_, leftPath_] :=
	AnyTrue[
		FindPath[
			EdgeDelete[
				g["graph"], 
				Union[
					g["leftDangerousEdges"],
					Intersection[pathToEdges[leftPath], g["sideEdges"]](*Somehow this works, the cycles never overlap on the sides*)
				]
			],
			g["rightVertices"][[1]], 
			g["rightVertices"][[-1]], 
			{1, Infinity}, 
			All
        ], 
        coversAllEdges[g,{leftPath, #1}] && 
        ContainsAll[pathToEdges[#1], g["rightDangerousEdges"]] && 
        IntersectingQ[pathToEdges[#1], g["crossEdges"]]&
    ]


pathsExist[g_] := AnyTrue[findPathsLeft[g], rightPathExists[g, #1]&]


(* ::Section:: *)
(*Path finding algorithm*)


possibleNewEdgesJoined[h_, newEdge_, layout_] := 
	Module[{newLeftVertex, newRightVertex, posLeft, posRight},
		newLeftVertex = Subscript[l, {newEdge[[1]], Length[layout["crossEdges"]] + 1}]; 
		newRightVertex = Subscript[r, {newEdge[[2]], Length[layout["crossEdges"]] + 1}]; 
		posLeft = FirstPosition[h["leftVertices"], newEdge[[1]]][[1]]; 
		posRight = FirstPosition[h["rightVertices"], newEdge[[2]]][[1]]; 

		Flatten[
			Table[
				Association[
					"leftVerticesGrouped" -> Insert[layout["leftVerticesGrouped"], 
						newLeftVertex, {posLeft, i}], 
					"rightVerticesGrouped" -> Insert[layout["rightVerticesGrouped"], 
						newRightVertex, {posRight, j}],
					"crossEdges" -> Append[layout["crossEdges"], {newLeftVertex, newRightVertex}]]
				,{i, 1, Length[layout["leftVerticesGrouped"][[posLeft]]] + 1}
			,{j, 1, Length[layout["rightVerticesGrouped"][[posRight]]] + 1}
			]
		, 1]
	]


iterate[h_, edgeInH_, currentLayouts_] :=
    Flatten[(possibleNewEdgesJoined[h, edgeInH, #1]&) /@ currentLayouts,
         1]


pathFindingComputation[h_] :=
    AbsoluteTiming[
        Monitor[
            Module[{currentLayouts},
                Print[h];
                currentLayouts = {Association["leftVerticesGrouped" ->
                     ConstantArray[{}, Length[h["leftVertices"]]], "rightVerticesGrouped"
                     -> ConstantArray[{}, Length[h["rightVertices"]]], "crossEdges" -> {}
                    ]};
                Do[
                    Print["Iteration : ", it];
                    currentLayouts = iterate[h, h["edges"][[it]], currentLayouts
                        ];
                    Print["Number of layouts before filtering for paths : ",
                         Length[currentLayouts]];
                    currentLayouts = Reap[
                            Do[
                                If[!pathsExist[makeGraph[currentLayouts[[j]],False]],
                                    Sow[currentLayouts[[j]]]
                                ];
                                ,
                                {j, Length[currentLayouts]}
                            ]
                        ][[2]];
                    If[Length[currentLayouts]>0,currentLayouts=currentLayouts[[1]]];
                    
                    Print["Number of layouts after filtering for paths : ",
                         Length[currentLayouts]];
                ,{it, 1, Length[h["edges"]]}];
           currentLayouts
           ]
        , {it, j}]
    ]


(* ::Section:: *)
(*Linear program version*)


sortEdge[a_\[UndirectedEdge]b_]:=Sort[{a,b}][[1]]\[UndirectedEdge]Sort[{a,b}][[2]]


toVar[edge_]:=Subscript[var,sortEdge[edge]]


cycleSumLeq[cycle_,longestCycle_]:=Total[toVar/@cycle]<=Total[toVar/@longestCycle]


equalCycles[longestCycle1_,longestCycle2_]:=Total[toVar/@longestCycle1]==Total[toVar/@longestCycle2]


singleLinearProgramCheck[configuration_]:=Module[{configurationGraph,allEdges,cycleList,leftMainCycle,rightMainCycle,solution},
	configurationGraph=makeGraph[configuration, True];
	allEdges=sortEdge/@Join[configurationGraph["sideEdges"],configurationGraph["crossEdges"]];
	cycleList=Map[sortEdge,Join[FindCycle[EdgeDelete[configurationGraph["graph"],configurationGraph["leftDangerousEdges"]],Infinity,All],FindCycle[EdgeDelete[configurationGraph["graph"],configurationGraph["rightDangerousEdges"]],Infinity,All]],{2}];
	leftMainCycle=sortEdge/@configurationGraph["leftEdges"];
	rightMainCycle=sortEdge/@configurationGraph["rightEdges"];
	solution=LinearOptimization[
			1,
			{
				cycleSumLeq[#,leftMainCycle]&/@cycleList,
				cycleSumLeq[#,rightMainCycle]&/@cycleList,
				equalCycles[leftMainCycle,rightMainCycle],
				#>=1&/@(toVar/@allEdges)
			},
			toVar/@allEdges
		,"PrimalMinimumValue"]==Infinity
]


linearProgramCheckAll[configurationList_]:=Quiet[AllTrue[configurationList,singleLinearProgramCheck]]


(* ::Chapter:: *)
(*Computation*)


(* ::Section:: *)
(*K_{3,3}*)


k33=<|"leftVertices"->{a1,a2,a3},"rightVertices"->{b1,b2,b3},"edges"->{{a1,b1},{a1,b2},{a1,b3},{a2,b1},{a2,b2},{a2,b3},{a3,b1},{a3,b2},{a3,b3}}|>;


toGraph[k33]


isomorphismClasses[k33]


{timek33,pathFindingResultsk33}=pathFindingComputation[k33]


linearProgramCheckAll[pathFindingResultsk33]


(* ::Section:: *)
(*Hypercube+edge*)


hypercubePlusEdge=<|"leftVertices"->{a1,a2,a3,a4},"rightVertices"->{b1,b2,b3,b4},"edges"->{{a1,b2},{a1,b3},{a2,b2},{a2,b3},{a3,b2},{a3,b3},{a1,b4},{a2,b4},{a4,b4},{a2,b1},{a3,b1},{a4,b1},{a4,b2}}|>


{hypercubePlusEdge1,hypercubePlusEdge2}=isomorphismClasses[hypercubePlusEdge]


{timehypercubePlusEdge1,pathFindingResultshypercubePlusEdge1}=pathFindingComputation[hypercubePlusEdge1]


linearProgramCheckAll[pathFindingResultshypercubePlusEdge1]


{timehypercubePlusEdge2,pathFindingResultshypercubePlusEdge2}=pathFindingComputation[hypercubePlusEdge2]


linearProgramCheckAll[pathFindingResultshypercubePlusEdge2]
