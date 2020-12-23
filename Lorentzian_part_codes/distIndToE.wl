(* ::Package:: *)

(* ::Input:: *)
(*(*A vertex is given by                    vetex[{x,y,z}] *)
(*A edge is given by                       DirectedEdge[{x,y,z},{xp,yp,zp}]        where its orientation is {x,y,z} ------> {xp,yp,zp}*)
(*Holonomy operator is then given by      holonomy[edge,a,b]  *)
(**)*)


(*only valid for operator in which flux indices are all 0*)
P2FluxAndSplitHolo[operator0_]:=Block[{operator,splitholo,replaceP,result},
operator=operator0//.x___**P[v_,e_,{}]**y___:>x**y;
splitholo=operator/. holonomy[vs_\[DirectedEdge]vt_,a_,b_]:>lholo[vertex[vs],vs\[DirectedEdge]vt,a]**rholo[vertex[vt],vs\[DirectedEdge]vt,b];
replaceP=splitholo/. {P[v_,i_,{z:Longest[(ind:0)..]}]:>P[v,i,ind]^Length[{z}],P[v_,i_,{z:Longest[(ind:0)..]},1]:>P[v,i,ind,1]^Length[{z}]};
result=replaceP/. {P[v_,i_,alpha_]:>flux[v,vs2edge[v,i,1],alpha]-flux[v,Sort[vs2edge[v,i,-1]],alpha],P[v_,i_,alpha_,1]:>flux[v,vs2edge[v,i,1],alpha]+flux[v,Sort[vs2edge[v,i,-1]],alpha]}
]


(*To get a list of facind[__]. in each facind[__], the information of edge and the flux and holonomy indices located on the edge are stored.*)
distIndsToEdge[operator_]:=Block[{epndFacInd,mergePowerFacInd,expandNMC0,expandNMC1},
epndFacInd=( distind[operator]/.(x_+y_)^n_:>Expand[(x+y)^n]);
mergePowerFacInd=epndFacInd/.{facind[fac_,e_,{},indr_]^m_:>facind[fac^m,e,{},ConstantArray[indr[[1]],m]],facind[fac_,e_,indl_,{}]^m_:>facind[fac^m,e,ConstantArray[indl[[1]],m],{}]};
expandNMC0=mergePowerFacInd/.{Times[fac0_,facind[fac1_,others__],y:facind[__]]:>facind[fac0 fac1,others]**y};
expandNMC0=expandNMC0/.Times[fac0_Integer,facind[fac1_,others__]]:>facind[fac0 fac1,others];
expandNMC1=expandNMC0//Distribute;
expandNMC1=expandNMC1/.(h:NonCommutativeMultiply)[inds__facind]:>joinFacInd[h[inds]];
expandNMC1//.Times[fac0_,NonCommutativeMultiply[facind[fac1_,others__],y__]]:>NonCommutativeMultiply[facind[fac0 fac1,others],y]
]


NotNum={holonomy,flux,lholo,rholo}
allheads[x__]:=Map[Head,Level[{x},Infinity]]

distind[NonCommutativeMultiply[op2_]]:=distind[op2]
distind[NonCommutativeMultiply[op1_,op2__]]:=NonCommutativeMultiply[distind[op1],distind[NonCommutativeMultiply[op2]]]
distind[Plus[x_,y__]]:=Plus[distind[Plus[x]],distind[Plus[y]]]
distind[Power[x__,a_]]:=Power[distind[x],a]
distind[Times[x___,Longest[a__/;!IntersectingQ[allheads[a],NotNum]],y___]]:=Times[a distind[Times[x,y]]]

distind[holonomy[edge_,a_,b_]]:=If[Sort[edge]===edge,facind[1,edge,{a},{b}],facind[(-1)^(a-b),Reverse[edge],{-b},{-a}]]
distind[lholo[v_,edge_,a_]]:=If[Sort[edge]===edge,facind[1,edge,{a},{}],facind[(-1)^(a),Reverse[edge],{},{-a}]]
distind[rholo[v_,edge_,b_]]:=If[Sort[edge]===edge,facind[1,edge,{},{b}],facind[(-1)^(-b),Reverse[edge],{-b},{}]]
distind[flux[v_,e1_,alpha_]]:=If[v[[1]]===Sort[e1][[1]],facind[1,Sort[e1],{alpha},{}],facind[1,Sort[e1],{},{alpha}]]
distind[{}]:=facind[1,DirectedEdge[{},{}],{},{}]


joinFacInd[NonCommutativeMultiply[inds__facind]]:=Block[{fac,gatherInd,indls,indrs,edges},
gatherInd=GatherBy[{inds},#[[2]]&];  
fac=Times@@#[[All,1]]&/@gatherInd;
indls=Join@@#[[All,3]]&/@gatherInd;indrs=Join@@#[[All,4]]&/@gatherInd;
edges= #[[1,2]]&/@gatherInd;
 NonCommutativeMultiply@@Thread[facind[fac,edges,indls,indrs]]
 ]
