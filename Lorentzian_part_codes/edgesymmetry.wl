(* ::Package:: *)

loopsymmetry[{i_Integer,si_Integer,j_Integer,sj_Integer,k_Integer,sk_Integer}]:={j,sj,i,si,k,sk}
loopsymmetry[{v1_List,e1_List,v2_List,e2_List}]:={{v1,e1,v2,e2},{v1,loopsymmetry[e1],v2,e2},{v1,e1,v2,loopsymmetry[e2]},{v1,loopsymmetry[e1],v2,loopsymmetry[e2]}}//Sort


rotation[{{v1_,v2_},e1_,{v3_,v4_},e2_}]:=Block[{allV,alle,ForReplacepart,replacedV,repladedE,allEqualentVE},
allV={v1[[1]],v2[[1]],v3[[1]],v4[[1]]};
alle={e1,e2};
ForReplacepart=Subsets[{1,2,3},{0,2,2}];
replacedV=myreplace[allV,#]&/@ForReplacepart;
replacedV=Map[vertex,replacedV,{2}];
repladedE=myreplaceEdge[alle,#]&/@ForReplacepart;
allEqualentVE=MapThread[{#1[[1;;2]],#2[[1]],#1[[{3,4}]],#2[[2]]}&,{replacedV,repladedE}];
allEqualentVE=ReplacePart[#,{{2,6}->Abs[#[[2,6]]],{4,6}->Abs[#[[4,6]]]}]&/@allEqualentVE;
Sort[allEqualentVE]
]
myreplace[list:{__Integer},pos_]:=Block[{allpos,remained,unsortlist,oripos},allpos=Range[Length[list]];remained=Complement[allpos,pos];unsortlist=Join[-list[[pos]],list[[remained]]];
oripos=Join[pos,remained];
SortBy[{oripos,unsortlist}//Transpose,First]//Transpose//Last
]
myreplace[list:{__List},pos_]:=myreplace[#,pos]&/@list
myreplaceEdge[edge:{__Integer},pos_]:=Block[{direction,sgn,pos0},{direction,sgn}=Partition[edge,2]//Transpose;pos0=Position[direction,x_/;MemberQ[pos,x]]//Flatten;{direction,myreplace[sgn,pos0]}//Transpose//Flatten]
myreplaceEdge[edge:{__List},pos_]:=myreplaceEdge[#,pos]&/@edge


rotationExtra[{{v1_,v2_},e1_,{v3_,v4_},e2_}]:=Block[{allV,rotationMatrix,alle,vec,rotatedVE,r},
allV={v1[[1]],v2[[1]],v3[[1]],v4[[1]]};
rotationMatrix={{0,1,0},{1,0,0},{0,0,-1}};
allV=Dot[rotationMatrix,#]&/@allV;
alle={e1,e2};
alle=Partition[#,2]&/@alle;
vec=alle/.{dir_Integer,sgn_Integer}:>ReplacePart[{0,0,0},dir->sgn];
vec=Map[Dot[rotationMatrix,#]&,vec,{2}];
alle=vec/.{x_Integer,y_Integer,z_Integer}:>Flatten[{Position[{x,y,z},xx_/;Abs[xx]==1],Cases[{x,y,z},xx_/;Abs[xx]==1]}];
rotatedVE={vertex/@allV[[{3,4}]],Flatten[alle[[2]]],vertex/@allV[[{1,2}]],Flatten[alle[[1]]]};
alle=ReplacePart[#,{{3,2}->Abs[#[[3,2]]]}]&/@alle;
rotatedVE={vertex/@allV[[{3,4}]],Flatten[alle[[2]]],vertex/@allV[[{1,2}]],Flatten[alle[[1]]]};
r=loopsymmetry/@{{{v1,v2},e1,{v3,v4},e2},rotatedVE};
r=r[[All,1]]//Sort
]


(*rotationExtra1[{{v1_,v2_},e1_,{v3_,v4_},e2_},ForReplacepart_]:=Block[{allV,alle,replacedV,repladedE,allEqualentVE},
allV={v1[[1]],v2[[1]],v3[[1]],v4[[1]]};
alle={e1,e2};
replacedV=myreplace[allV,#]&/@ForReplacepart;
replacedV=Map[vertex,replacedV,{2}];
repladedE=myreplaceEdge[alle,#]&/@ForReplacepart;
allEqualentVE=MapThread[{#1[[1;;2]],#2[[1]],#1[[{3,4}]],#2[[2]]}&,{replacedV,repladedE}];
allEqualentVE=ReplacePart[#,{{2,6}->Abs[#[[2,6]]],{4,6}->Abs[#[[4,6]]]}]&/@allEqualentVE
]
(***============================================================================================================================================***)
rotationExtra1[{{v1_,v2_},e1_,{v3_,v4_},e2_}]/;MatchQ[{v1,v2},{vertex[{0,0,0}]..}]:=Block[{allV,rotationMatrix,alle,vec,rotatedVE1,ForReplacepart,rotatedVE2,rotatedVE3},
allV={v1[[1]],v2[[1]],v3[[1]],v4[[1]]};
rotationMatrix={{0,1,0},{1,0,0},{0,0,-1}};
allV=Dot[rotationMatrix,#]&/@allV;
alle={e1,e2};
alle=Partition[#,2]&/@alle;
vec=alle/.{dir_Integer,sgn_Integer}:>ReplacePart[{0,0,0},dir->sgn];
vec=Map[Dot[rotationMatrix,#]&,vec,{2}];
alle=vec/.{x_Integer,y_Integer,z_Integer}:>Flatten[{Position[{x,y,z},xx_/;Abs[xx]==1],Cases[{x,y,z},xx_/;Abs[xx]==1]}];
alle=ReplacePart[#,{{3,2}->Abs[#[[3,2]]]}]&/@alle;
rotatedVE1={vertex/@allV[[{3,4}]],Flatten[alle[[2]]],vertex/@allV[[{1,2}]],Flatten[alle[[1]]]};
(*************)
ForReplacepart={{1,3}};
rotatedVE2=rotationExtra1[{{v1,v2},e1,{v3,v4},e2},ForReplacepart];
ForReplacepart={{2,3}};
rotatedVE3=rotationExtra1[rotatedVE1,ForReplacepart];
Join[{{{v1,v2},e1,{v3,v4},e2},rotatedVE1},rotatedVE2,rotatedVE3]//Sort
]
rotationExtra1[{{v1_,v2_},e1_,{v3_,v4_},e2_}]/;MatchQ[{v3,v4},{vertex[{0,0,0}]..}]:=Block[{allV,rotationMatrix,alle,vec,rotatedVE1,ForReplacepart,rotatedVE2,rotatedVE3},
allV={v1[[1]],v2[[1]],v3[[1]],v4[[1]]};
rotationMatrix={{0,1,0},{1,0,0},{0,0,-1}};
allV=Dot[rotationMatrix,#]&/@allV;
alle={e1,e2};
alle=Partition[#,2]&/@alle;
vec=alle/.{dir_Integer,sgn_Integer}:>ReplacePart[{0,0,0},dir->sgn];
vec=Map[Dot[rotationMatrix,#]&,vec,{2}];
alle=vec/.{x_Integer,y_Integer,z_Integer}:>Flatten[{Position[{x,y,z},xx_/;Abs[xx]==1],Cases[{x,y,z},xx_/;Abs[xx]==1]}];
alle=ReplacePart[#,{{3,2}->Abs[#[[3,2]]]}]&/@alle;
rotatedVE1={vertex/@allV[[{3,4}]],Flatten[alle[[2]]],vertex/@allV[[{1,2}]],Flatten[alle[[1]]]};
(*************)
ForReplacepart={{2,3}};
rotatedVE2=rotationExtra1[{{v1,v2},e1,{v3,v4},e2},ForReplacepart];
ForReplacepart={{1,3}};
rotatedVE3=rotationExtra1[rotatedVE1,ForReplacepart];
Join[{{{v1,v2},e1,{v3,v4},e2},rotatedVE1},rotatedVE2,rotatedVE3]//Sort
]
rotationExtra1[{{v1_,v2_},e1_,{v3_,v4_},e2_}]:={{{v1,v2},e1,{v3,v4},e2}}*)



extraSymmetryQ[{{v1_,v2_},{i2_,si2_,j2_,sj2_,k2_,sk2_},{v3_,v4_},{i4_,si4_,j4_,sj4_,k4_,sk4_}}]:=
Block[{v20,v21,v22,v23,EdgePoints4holoK1holo,comQ1,v40,v41,v42,v43,EdgePoints4holoK2holo,comQ2},
v20=v2[[1]];
v21=vertex[v20+ReplacePart[{0,0,0},i2->si2]];
v22=vertex[v21[[1]]+ReplacePart[{0,0,0},j2->sj2]];
v23=vertex[v22[[1]]+ReplacePart[{0,0,0},i2->-si2]];
EdgePoints4holoK1holo={v2,v21,v22,v23,vertex[{0,0,0}],vertex[{1,0,0}]};
comQ1=!IntersectingQ[EdgePoints4holoK1holo,{v3,v4}];
v40=v4[[1]];
v41=vertex[v40+ReplacePart[{0,0,0},i4->si4]];
v42=vertex[v41[[1]]+ReplacePart[{0,0,0},j4->sj4]];
v43=vertex[v42[[1]]+ReplacePart[{0,0,0},i4->-si4]];
EdgePoints4holoK2holo={v4,v41,v42,v43,vertex[{0,0,0}],vertex[{0,1,0}]};
comQ2=!IntersectingQ[EdgePoints4holoK2holo,{v1,v2}];
And[comQ1,comQ2]
]
