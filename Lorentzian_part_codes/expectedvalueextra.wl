(* ::Package:: *)

changefacWDinnrule={
{factorWDinn[{inn[{1,2}]},{{},{a_,b_}}],factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}]},{alpha_,{c_,d_}}]}:>factorWDinn[{0},{alpha,{a,b,c,d}}],
 {factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}]},{alpha_,{c_,d_}}],factorWDinn[{inn[{1,2}]},{{},{a_,b_}}]}:>factorWDinn[{0},{alpha,{a,b,c,d}}],
(**)
{factorWDinn[{inn[{1,2}],WD[indP[{1}]]},{{alpha_},{a_,b_}}],factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}]},{{beta_},{c_,d_}} ] }:>factorWDinn[{1},{{alpha,beta},{a,b,c,d}}],
{factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}]},{{beta_},{c_,d_}} ],factorWDinn[{inn[{1,2}],WD[indP[{1}]]},{{alpha_},{a_,b_}}] }:>factorWDinn[{1},{{alpha,beta},{a,b,c,d}}],
(**)
{factorWDinn[{inn[{1,2}]},{{},{a_,b_}}],factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}],WD[indP[{1}]]},{{alpha_,beta_},{c_,d_}} ] }:>factorWDinn[{2},{{alpha,beta},{a,b,c,d}}],
{factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}],WD[indP[{1}]]},{{alpha_,beta_},{c_,d_}} ] ,factorWDinn[{inn[{1,2}]},{{},{a_,b_}}]}:>factorWDinn[{2},{{alpha,beta},{a,b,c,d}}],
 (**)
 {factorWDinn[{inn[{1,2}],__WD,inn[{2,3}],__WD,inn[{3,1}]},x_]}:>factorWDinn[{3},x],
(**)
 {factorWDinn[{inn[{2,3}],__WD,inn[{3,1}],__WD,inn[{1,2}]},x_]}:>factorWDinn[{4},x],
(**)
{factorWDinn[{inn[{2,3}],WD[indP[{1}]],inn[{3,1}],WD[indP[{1}]],inn[{1,2}],WD[indP[{1}]]},x_]}:>factorWDinn[{5},x],
(**)
{factorWDinn[{inn[{1,2}],WD[indP[{1}]],inn[{2,3}],WD[indP[{1}]],inn[{3,1}],WD[indP[{1}]]},x_]}:>factorWDinn[{6},x]
};


(*computate the sum of expectation values of HL with respect to 2 groups of edges and vertices
which are different by a rotation with respect to axis for 180 degree*)
expectedValueExtra[allvAnde4HlEach_,sgns_,comQ_]:=Block[{sgn1,sgn2,i1,operatorList1,operatorList2,operatorList,factorlist,operatorpurelist,decoupleOperatorlist,WDs,orderedWDs,inns,AllWDsinns,ToGraph,Graphs,connectinglist,connectingRule,connectedOps,AllbasicWDinn,basicWDinn,thesgn,NewWDinnfactor,ForNewWDinnfactorExtra,NewWDinnfactorp,NewWDinnfactorExtra,otherfactor,Newfactorlist,final1,summationp1,operator0,final2,summationp2,result},
sgn1=sgns[[1]];
sgn2=sgns[[2]];
i1=1;
operatorList1=(Hl[indh[1,#]&,{allvAnde4HlEach[[i1,1,1]],2m[1],indP[1,#]&,allvAnde4HlEach[[i1,1,2]],allvAnde4HlEach[[i1,2]],indh[2,#]&,indP[2,#]&,2m[2]},{allvAnde4HlEach[[i1,3,1]],2m[3],indP[3,#]&,allvAnde4HlEach[[i1,3,2]],allvAnde4HlEach[[i1,4]],indh[3,#]&,indP[4,#]&,2m[4]},indP[5,#]&,2m[5],indP[6,#]&,indP[7,#]&,indP[8,#]&,indP[9,#]&,indP[10,#]&,indP[11,#]&,indh[4,#]&,indh[5,#]&,indh[6,#]&,indh[7,#]&,True])//Expand;
operatorList2=(Hl[indh[1,#]&,{allvAnde4HlEach[[i1,1,1]],2m[1],indP[1,#]&,allvAnde4HlEach[[i1,1,2]],allvAnde4HlEach[[i1,2]],indh[2,#]&,indP[2,#]&,2m[2]},{allvAnde4HlEach[[i1,3,1]],2m[3],indP[3,#]&,allvAnde4HlEach[[i1,3,2]],allvAnde4HlEach[[i1,4]],indh[3,#]&,indP[4,#]&,2m[4]},indP[5,#]&,2m[5],indP[6,#]&,indP[7,#]&,indP[8,#]&,indP[9,#]&,indP[10,#]&,indP[11,#]&,indh[4,#]&,indh[5,#]&,indh[6,#]&,indh[7,#]&,False])//Expand;
operatorList=Complement[operatorList2,operatorList1];
factorlist=Times@@#&/@(Cases[#,Except[_NonCommutativeMultiply]]&/@operatorList);
operatorpurelist=NonCommutativeMultiply@@#&/@(Cases[#,_NonCommutativeMultiply]&/@operatorList);
decoupleOperatorlist=ToDecoupleOps/@operatorpurelist;
WDs=Cases[#,_WD|_WDt]&/@factorlist;
orderedWDs=Map[orderWDindP,WDs];
inns=Cases[#,_inn]&/@factorlist;
AllWDsinns=MapThread[Join,{orderedWDs,inns}];
ToGraph=AllWDsinns/.{WD[v_,e_,z_,x_,y_]:>UndirectedEdge[x,y],WDt[v_,e_,z_,x_,y_]:>UndirectedEdge[x,y],inn[ij_,x_,y_]:>UndirectedEdge[x,y]};
Graphs=Map[Graph,ToGraph];
connectinglist=Map[ConnectedComponents,Graphs];
connectingRule=Map[(Thread/@Thread[Rule[#,Range[Length[#]]]])&,connectinglist];
connectingRule=Flatten/@connectingRule;
connectedOps=MapThread[GatherBy[#1,Function[u,Last[u]/.#2]]&,{AllWDsinns,connectingRule}];
AllbasicWDinn=Map[uniformWDinn,connectedOps,{2}];
basicWDinn=Flatten[AllbasicWDinn[[All,All,1;;2]],1]//DeleteDuplicates;
creatfacs/@basicWDinn;
(******************************)
thesgn=-Abs[sgn2];
Do[factorWDinn[{0},{{{alpha}},{a,b,c,d}}]=factorWDinnExtra[0,thesgn,{{alpha},{a,b,c,d}}],{alpha,-1,1},{a,-1/2,1/2},{b,-1/2,1/2},{c,-1/2,1/2},{d,-1/2,1/2}];
Do[factorWDinn[{i},{{{alpha},{beta}},{a,b,c,d}}]=factorWDinnExtra[i,thesgn,{{alpha,beta},{a,b,c,d}}],{alpha,-1,1},{beta,-1,1},{a,-1/2,1/2},{b,-1/2,1/2},{c,-1/2,1/2},{d,-1/2,1/2},{i,1,2}];
Do[factorWDinn[{i},{{{alpha},{beta}},{a,b}}]=factorWDinnExtra[i,thesgn,{{alpha,beta},{a,b}}],{alpha,-1,1},{beta,-1,1},{a,-1/2,1/2},{b,-1/2,1/2},{i,3,4}];
Do[factorWDinn[{i},{{{alpha},{beta},{gamma}},{a,b}}]=factorWDinnExtra[i,thesgn,{{alpha,beta,gamma},{a,b}}],{alpha,-1,1},{beta,-1,1},{gamma,-1,1},{a,-1/2,1/2},{b,-1/2,1/2},{i,3,6}];
(***********************************)
NewWDinnfactor=Times@@@Apply[factorWDinn,AllbasicWDinn[[All,All,2;;3]],{2}];
ForNewWDinnfactorExtra=Cases[#,x_/;IntersectingQ[Flatten[List@@x],{indh[1,2],indh[1,3],indh[1,4],indh[1,5],indh[1,6],indh[1,1]}]]&/@NewWDinnfactor;
(*here indh[1,2] and indh[1,5] are because of the case when we need to calculate [[h_e,p_s],p_t] in the function orderPH4HL*)
NewWDinnfactorp=MapThread[DeleteCases[#1,x_/;MemberQ[#2,x]]&,{NewWDinnfactor,ForNewWDinnfactorExtra}];
NewWDinnfactorExtra=ForNewWDinnfactorExtra/.changefacWDinnrule;
NewWDinnfactor=Times[NewWDinnfactorExtra, NewWDinnfactorp];
(***********************************)
otherfactor=Times@@@(Cases[#,Except[_WD|_inn]]&/@factorlist);
Newfactorlist=NewWDinnfactor otherfactor;
final1=Table[expectedValueOneTerm[decoupleOperatorlist[[i]],Newfactorlist[[i]],rule0List,7],{i,1,Length[decoupleOperatorlist]}];
summationp1=Total[final1]//Expand;
(***************************************************************************************************************************************)
If[sgn2==0||comQ,Return[sgn1 summationp1]];
i1=2;
operator0=(commutatorK1K2[indh[1,#]&,{allvAnde4HlEach[[i1,1,1]],2m[1],indP[1,#]&,allvAnde4HlEach[[i1,1,2]],allvAnde4HlEach[[i1,2]],indh[2,#]&,indP[2,#]&,2m[2]},{allvAnde4HlEach[[i1,3,1]],2m[3],indP[3,#]&,allvAnde4HlEach[[i1,3,2]],allvAnde4HlEach[[i1,4]],indh[3,#]&,indP[4,#]&,2m[4]},indP[5,#]&,2m[5],indP[6,#]&,indP[7,#]&,indP[8,#]&,indP[9,#]&,indP[10,#]&,indP[11,#]&,indh[4,#]&,indh[5,#]&,indh[6,#]&,indh[7,#]&,indh[8,1]]);
(*Just for safetay. Actually the same function as If[comQ,Return[summationp1]]*)
If[operator0==0,Return[sgn1 summationp1]];
(**********)
operatorList=(List@@operator0);
factorlist=Times@@#&/@(Cases[#,Except[_NonCommutativeMultiply]]&/@operatorList);
operatorpurelist=NonCommutativeMultiply@@#&/@(Cases[#,_NonCommutativeMultiply]&/@operatorList);
decoupleOperatorlist=ToDecoupleOps/@operatorpurelist;
WDs=Cases[#,_WD]&/@factorlist;
orderedWDs=Map[orderWDindP,WDs];
inns=Cases[#,_inn]&/@factorlist;
AllWDsinns=MapThread[Join,{orderedWDs,inns}];
ToGraph=AllWDsinns/.{WD[v_,e_,z_,x_,y_]:>UndirectedEdge[x,y],inn[ij_,x_,y_]:>UndirectedEdge[x,y]};
Graphs=Map[Graph,ToGraph];
connectinglist=Map[ConnectedComponents,Graphs];
connectingRule=Map[(Thread/@Thread[Rule[#,Range[Length[#]]]])&,connectinglist];
connectingRule=Flatten/@connectingRule;
connectedOps=MapThread[GatherBy[#1,Function[u,Last[u]/.#2]]&,{AllWDsinns,connectingRule}];
AllbasicWDinn=Map[uniformWDinn,connectedOps,{2}];
basicWDinn=Flatten[AllbasicWDinn[[All,All,1;;2]],1]//DeleteDuplicates;
creatfacs/@basicWDinn;
NewWDinnfactor=Times@@@Apply[factorWDinn,AllbasicWDinn[[All,All,2;;3]],{2}];
otherfactor=Times@@@(Cases[#,Except[_WD|_inn]]&/@factorlist);
Newfactorlist=NewWDinnfactor otherfactor;
final2=Table[expectedValueOneTerm[decoupleOperatorlist[[i]],Newfactorlist[[i]],rule0List,7],{i,1,Length[decoupleOperatorlist]}];
summationp2=Total[final2]//Expand;
Clear[factorWDinn];
result=sgn1 summationp1+sgn2 summationp2]


operatorHead={holonomy,P};
ToCommutate[(h:NonCommutativeMultiply)[x1_,x2__],(h:NonCommutativeMultiply)[y__]]:=h[ToCommutate[x1,h[y]],x2]+h[x1,ToCommutate[h[x2],h[y]]]
ToCommutate[x_,(h:NonCommutativeMultiply)[y1_,y2__]]:=h[ToCommutate[x,y1],y2]+h[y1,ToCommutate[x,h[y2]]]
ToCommutate[NonCommutativeMultiply[x_],y_]/;MemberQ[operatorHead,Head[x]]:=ToCommutate[x,y]
ToCommutate[x_,NonCommutativeMultiply[y_]]/;MemberQ[operatorHead,Head[y]]:=ToCommutate[x,y]
ToCommutate[x_holonomy,y_holonomy]:=0
ToCommutate[holonomy[DirectedEdge[v1_,v2_],x__],P[vertex[v3_],i_,y_]]/;!MemberQ[{v1,v2},v3]:=0
ToCommutate[P[vertex[v3_],i_,y_],holonomy[DirectedEdge[v1_,v2_],x__]]/;!MemberQ[{v1,v2},v3]:=0
ToCommutate[holonomy[e_,x__],P[v3_,i_,y_]]/;!MemberQ[{Sort[vs2edge[v3,i,1]],Sort[vs2edge[v3,i,-1]]},Sort[e]]:=0
ToCommutate[P[v3_,i_,y_],holonomy[e_,x__]]/;!MemberQ[{Sort[vs2edge[v3,i,1]],Sort[vs2edge[v3,i,-1]]},Sort[e]]:=0
(***commutator Between P***)
ToCommutate[P[vertex[v1_],i_,_],P[vertex[v2_],j_,_]]/;v1=!=v2||i=!=j:=0
ToCommutate[P[vertex[v_],i_,indP[__]],P[vertex[v_],i_,indP[__]]]:=0
ToCommutate[P[vertex[v_],i_,fluxCom[__]],P[vertex[v_],i_,fluxCom[__]]]:=0


commutatorK1K2[indh0_,{vQ1_,lQoperator1_,qind1_,vHe1_,{i1_,si1_,j1_,sj1_,k1_,sk1_},holoind1_,holoqind1_,lQholo1_},{vQ2_,lQoperator2_,qind2_,vHe2_,{i2_,si2_,j2_,sj2_,k2_,sk2_},holoind2_,holoqind2_,lQholo2_},qind3_,lq3_,extraH1x_,extraH2x_,extraH3x_,extraH1y_,extraH2y_,extraH3y_,indhextrxl_,indhextrxr_,indhextryl_,indhextryr_,dummyind_]:=
Block[{KO1,KO2,hKO1h0,hKO1h,hKO1hp,hKO2h0,hKO2h,hKO2hp,innfactors,hQh,otherO,holok12,holok12p,factork12,pureholok12,commutatorK12,r},
      If[!IntersectingQ[{vertex[{0,0,0}],vertex[{1,0,0}]},{vQ1,vHe1}]||!IntersectingQ[{vertex[{0,0,0}],vertex[{0,1,0}]},{vQ2,vHe2}],Return[0]];
KO1=Koperator[vQ1,lQoperator1,qind1,vHe1,{i1,si1,j1,sj1,k1,sk1},holoind1,holoqind1,lQholo1,extraH1x,extraH2x,extraH3x];
If[KO1===0,Return[0]];
KO2=Koperator[vQ2,lQoperator2,qind2,vHe2,{i2,si2,j2,sj2,k2,sk2},holoind2,holoqind2,lQholo2,extraH1y,extraH2y,extraH3y];
If[KO2===0,Return[0]];
(*========================*)
(*========================*)
hKO1h0=holonomy[DirectedEdge[{0,0,0},{1,0,0}],indh0[1],indh0[2]]**KO1**holonomy[DirectedEdge[{1,0,0},{0,0,0}],indh0[2],indh0[3]]//epdNCM//Expand;
hKO1h=orderPH4HL[hKO1h0,indhextrxl,indhextrxr,False];
hKO1hp=orderPH4HL[hKO1h0,indhextrxl,indhextrxr,True];
hKO1h=hKO1h//epdNCM//Expand//Function[u,Normal[u+O[t]^4]]//Expand;
hKO1hp=hKO1hp//epdNCM//Expand//Function[u,Normal[u+O[t]^4]]//Expand;
hKO1h=List@@hKO1h;
hKO1hp=List@@hKO1hp;
(*========================*)
hKO2h0=holonomy[DirectedEdge[{0,0,0},{0,1,0}],indh0[4],indh0[5]]**KO2**holonomy[DirectedEdge[{0,1,0},{0,0,0}],indh0[5],indh0[6]]//epdNCM//Expand;
hKO2h=orderPH4HL[hKO2h0,indhextryl,indhextryr,False];
hKO2hp=orderPH4HL[hKO2h0,indhextryl,indhextryr,True];
hKO2h=hKO2h//epdNCM//Function[u,Normal[u+O[t]^4]]//Expand;
hKO2hp=hKO2hp//epdNCM//Function[u,Normal[u+O[t]^4]]//Expand;
hKO2h=List@@hKO2h;
hKO2hp=List@@hKO2hp;
(*========================*)
innfactors=inn[{1,2} ,indh0[3],indh0[4]]inn[{2,3},indh0[6],indh0[7]]inn[{3,1},indh0[9],indh0[1]];
hQh=holonomy[DirectedEdge[{0,0,0},{0,0,1}],indh0[7],indh0[8]]**Q[vertex[{0,0,0}],qind3,lq3]**holonomy[DirectedEdge[{0,0,1},{0,0,0}],indh0[8],indh0[9]];
hQh=hQh//epdNCM//Expand//orderPH;
otherO=innfactors hQh//epdNCM;
(*========================*)
holok12=Distribute[{hKO1h,hKO2h},List];
holok12p=Distribute[{hKO1hp,hKO2hp},List];
holok12=DeleteCases[holok12,xx_/;MemberQ[holok12p,xx]];(*we care ony the commutator [holoK1,holoK2]-[holoK1p,holoK2p]*)
factork12=Map[Times@@Cases[#,Except[_NonCommutativeMultiply]]&,holok12,{2}];
factork12=Times@@@factork12;
pureholok12=Map[Cases[#,_NonCommutativeMultiply]&,holok12,{2}];
pureholok12=Flatten/@pureholok12;
(***********We have divided the commutator into pure-factor parts and pure-operator part**************)
(****************we now compute the commutator*******************)
pureholok12=((ToCommutate@@#//epdNCM)/.___**0**___:>0)&/@pureholok12;
pureholok12=pureholok12/.(h:ToCommutate)[P[v_,ii_,indP[nth_,{ii_,l_}]],holonomy[DirectedEdge[vs_,vt_],a_,b_]]:>P[v,ii,indP[nth,{ii,l-1}]]**commutatorPholo[v,holonomy[DirectedEdge[vs,vt],a,b],indP[nth,#]&,dummyind,1];
pureholok12=pureholok12/.(h:ToCommutate)[holonomy[DirectedEdge[vs_,vt_],a_,b_],P[v_,ii_,indP[nth_,{ii_,l_}]]]:>-P[v,ii,indP[nth,{ii,l-1}]]**commutatorPholo[v,holonomy[DirectedEdge[vs,vt],a,b],indP[nth,#]&,dummyind,1];
pureholok12=pureholok12/.(h:ToCommutate)[P[v_,ii_,indP[nth_,{ii_,l_}]],P[v_,ii_,fluxCom[(x:indP[__]),(y:indP[__])]]]:> t P[v,ii,indP[nth,{ii,l-1}]]**P[v,ii,fluxCom[indP[nth,{ii,1}],fluxCom[x,y]]];
pureholok12=pureholok12/.(h:ToCommutate)[P[v_,ii_,fluxCom[(x:indP[__]),(y:indP[__])]],P[v_,ii_,indP[nth_,{ii_,l_}]]]:> -t P[v,ii,indP[nth,{ii,l-1}]]**P[v,ii,fluxCom[indP[nth,{ii,1}],fluxCom[x,y]]];
(******)
pureholok12=pureholok12/.(h:ToCommutate)[P[vertex[vs_],ii_,y_fluxCom ],holonomy[DirectedEdge[vs_,vt_],a_,b_]]:>I t WD[vertex[vs],ii,y,a,dummyind]holonomy[DirectedEdge[vs,vt],dummyind,b];
pureholok12=pureholok12/.(h:ToCommutate)[holonomy[DirectedEdge[vs_,vt_],a_,b_],P[vertex[vs_],ii_,y_fluxCom]]:>-I t WD[vertex[vs],ii,y,a,dummyind]holonomy[DirectedEdge[vs,vt],dummyind,b];
pureholok12=pureholok12/.(h:ToCommutate)[P[vertex[vt_],ii_,y_fluxCom],holonomy[DirectedEdge[vs_,vt_],a_,b_]]:>-I t WD[vertex[vt],ii,y,dummyind,b]holonomy[DirectedEdge[vs,vt],a,dummyind];
pureholok12=pureholok12/.(h:ToCommutate)[holonomy[DirectedEdge[vs_,vt_],a_,b_],P[vertex[vt_],ii_,y_fluxCom]]:>I t WD[vertex[vt],ii,y,dummyind,b]holonomy[DirectedEdge[vs,vt],a,dummyind];
commutatorK12=factork12 pureholok12;
r=NonCommutativeMultiply[#,otherO]&/@commutatorK12;
r=r/.___**0**___:>0;
(Plus@@r)//epdNCM//Expand
]
