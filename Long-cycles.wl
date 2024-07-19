(* ::Package:: *)

(* ::Title:: *)
(*Title*)


(* ::Subtitle:: *)
(*Code used in the paper "" by *)
(**)
(*Description*)


(* ::Chapter:: *)
(*Code*)


(* ::Section:: *)
(*Considering all configurations up to isomorphism*)


toGraph[h_] := Graph[Join[h["leftVertices"], h["rightVertices"]], 
   Apply[UndirectedEdge, h["edges"], {1}], VertexLabels -> "Name", 
   GraphLayout -> "BipartiteEmbedding"]


permutationPairs[h_]:=Tuples[{Permutations[h["leftVertices"]],Permutations[h["rightVertices"]]}];


listAdd[list_,label_]:=Riffle[list,Subscript[label,#]&/@Range[Length[list]]]


makeCycle[path_,label_]:=UndirectedEdge@@@(Sort/@Subsequences[Join[listAdd[path,label],{path[[1]]}],{2}])


addCycles[h_,{leftVertexOrder_,rightVertexOrder_}]:=Graph[VertexList[h],Join[EdgeList[h],makeCycle[leftVertexOrder,v1],makeCycle[rightVertexOrder,v2]]]


vertexOrderings[h_]:=DeleteDuplicatesBy[permutationPairs[h],CanonicalGraph[addCycles[toGraph[h],#]]&]


isomorphismClasses[h_]:=Association["leftVertices" -> #[[1]], "rightVertices" -> #[[2]], 
    "edges" -> h["edges"]]&/@vertexOrderings[h]


(* ::Section:: *)
(*Optimizing the ordering of edges*)


edgeToVertices[a_\[UndirectedEdge]b_]:={a,b}


cycleToVertices[cycle_]:=DeleteDuplicates[Flatten[edgeToVertices/@cycle,1]]


optimalEdgeOrder[h_]:=Module[{maxNumVerticesWith2Cycles,partialEdgeOrder},
	maxNumVerticesWith2Cycles=Max[Union[Length[DeleteDuplicates[Flatten[cycleToVertices/@#,1]]]&/@Tuples[FindCycle[toGraph[h],{4},All],{2}]]];
	partialEdgeOrder=DeleteDuplicates[Sort/@edgeToVertices/@Flatten[Select[Tuples[FindCycle[toGraph[h],{4},All],{2}],Length[DeleteDuplicates[Flatten[cycleToVertices/@#,1]]]==maxNumVerticesWith2Cycles&][[1]],1]];
	<|"leftVertices"->h["leftVertices"],"rightVertices"->h["rightVertices"],"edges"->Join[partialEdgeOrder,Complement[h["edges"],partialEdgeOrder]]|>
]


(* ::Section:: *)
(*Graph creation from configuration*)


pathToEdges[path_] := Apply[UndirectedEdge, Sort /@ Subsequences[path, {2}], {1}]


toColorEdge[intervalEdges_,edge_] := If[MemberQ[intervalEdges, edge], 
   Style[edge, Green], edge]


makeGraph[layout_, finishCycles_] :=
    Module[{leftVerticesGrouped, rightVerticesGrouped, leftVertices, 
        rightVertices, leftEdges, rightEdges, graph, leftIntervalEdges, rightIntervalEdges,
         leftNonIntervalEdges, rightNonIntervalEdges, sideEdges, crossEdges},
        
        leftVerticesGrouped = layout["leftVerticesGrouped"];
        rightVerticesGrouped = layout["rightVerticesGrouped"];
        leftVertices = Flatten[leftVerticesGrouped];
        rightVertices = Flatten[rightVerticesGrouped];
        leftEdges = pathToEdges[Flatten[leftVertices]];
        rightEdges = pathToEdges[Flatten[rightVertices]];
        If[finishCycles,
            leftEdges = Append[leftEdges, UndirectedEdge[leftVertices
                [[1]], leftVertices[[-1]]]];
            rightEdges = Append[rightEdges, UndirectedEdge[rightVertices
                [[1]], rightVertices[[-1]]]];
        ];
        leftIntervalEdges = Flatten[pathToEdges /@ leftVerticesGrouped];
        rightIntervalEdges = Flatten[pathToEdges /@ rightVerticesGrouped];
        leftNonIntervalEdges = Complement[leftEdges, leftIntervalEdges];
        rightNonIntervalEdges = Complement[rightEdges, rightIntervalEdges];
        sideEdges = Join[leftEdges, rightEdges];
        crossEdges = Apply[UndirectedEdge, layout["crossEdges"], {1}];
        graph = Graph[
                Join[leftVertices, rightVertices],
                Join[toColorEdge[Join[leftIntervalEdges,rightIntervalEdges],#]& /@ Join[leftEdges, rightEdges], crossEdges],
                VertexLabels -> "Name",
                VertexCoordinates -> Join[Table[{x, 0}, {x, 1, Length[
                    leftVertices]}], Table[{x, 1}, {x, 1, Length[rightVertices]}]]
                    ,
                EdgeShapeFunction -> If[finishCycles,{leftEdges[[-1]] -> "CurvedEdge",
                     rightEdges[[-1]] -> "CurvedEdge"}
                    ,
                    {}
                ]
            ];
        Association["leftVertices" -> leftVertices, "rightVertices" ->
             rightVertices, "leftIntervalEdges" -> leftIntervalEdges, "rightIntervalEdges"
             -> rightIntervalEdges, "leftNonIntervalEdges" -> leftNonIntervalEdges,
             "rightNonIntervalEdges" -> rightNonIntervalEdges, "leftEdges"->leftEdges, "rightEdges"->rightEdges, "sideEdges" -> sideEdges,
             "crossEdges" -> crossEdges, "graph" -> graph]
    ]


(* ::Section:: *)
(*Path finding*)


coversAllEdges[g_, {path1_, path2_}] := 
	ContainsAll[Join[pathToEdges[path1], pathToEdges[path2]], g["sideEdges"]]


containsIntervalLeft[g_, path_] := IntersectingQ[pathToEdges[path], g["leftIntervalEdges"]]
containsIntervalRight[g_, path_] := IntersectingQ[pathToEdges[path], g["rightIntervalEdges"]]
containsNonIntervalLeft[g_, path_] := IntersectingQ[pathToEdges[path], g["leftNonIntervals"]]
containsNonIntervalRight[g_, path_] := IntersectingQ[pathToEdges[path], g["rightNonIntervals"]]


findPathsLeft[g_] := (*Lists all potentially useful left paths*)
	Select[
		FindPath[
			EdgeDelete[g["graph"], g["rightNonIntervalEdges"]], 
			g["leftVertices"][[1]], 
			g["leftVertices"][[-1]], 
			{1, Infinity}, 
			All
		], 
		ContainsAll[pathToEdges[#1], g["leftNonIntervalEdges"]] && 
		IntersectingQ[pathToEdges[#1], g["crossEdges"]] &
     ]


rightPathExists[g_, leftPath_] := (*For given left path, tries to find a compatible right path*)
	AnyTrue[
		FindPath[
			EdgeDelete[
				g["graph"], 
				Union[
					g["leftNonIntervalEdges"],
					Intersection[pathToEdges[leftPath], g["sideEdges"]](*Somehow this works, the cycles never overlap on the sides*)
				]
			],
			g["rightVertices"][[1]], 
			g["rightVertices"][[-1]], 
			{1, Infinity}, 
			All
        ], 
        coversAllEdges[g,{leftPath, #1}] && (*Check to see if the cycles are entirely covered*)
        ContainsAll[pathToEdges[#1], g["rightNonIntervalEdges"]] && 
        IntersectingQ[pathToEdges[#1], g["crossEdges"]]& (*Check to ensure that at least one cross edge is covered*)
    ]


pathsExist[g_] := AnyTrue[findPathsLeft[g], rightPathExists[g, #1]&] 
(*Looks for pairs of a left path and a right path that cover all the edges of the cycles, returns true if successful, false otherwise
Note that this is sufficient as there is an edge between the first and last vertex on the right, completing the path to a cycle (Something like this should be said, I'm not very happy with the current phrasing)*)


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
	](*Given a new edge to be added and a current layout, checks each possible way of adding the new edge while respecting the current order on h*)


iterate[h_, edgeInH_, currentLayouts_] :=
    Flatten[(possibleNewEdgesJoined[h, edgeInH, #1]&) /@ currentLayouts,
         1]
(*Iterates over all current layouts adding a new edge*)

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
	cycleList=Map[sortEdge,Join[FindCycle[EdgeDelete[configurationGraph["graph"],configurationGraph["leftNonIntervalEdges"]],Infinity,All],FindCycle[EdgeDelete[configurationGraph["graph"],configurationGraph["rightNonIntervalEdges"]],Infinity,All]],{2}];
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
