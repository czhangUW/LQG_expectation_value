(* ::Package:: *)

(*order the operator taking the form h_e Q h_e^{-1} such that h and h^{-1} cancel *)
orderPH[(h:NonCommutativeMultiply)[x1___,holonomy[DirectedEdge[vs_,vt_],a_,b_],x2__, holonomy[DirectedEdge[vt_,vs_],b_,c_],x4___] ]:=
Block[{mid,PNC,nPNC,sgn},
mid=List[x2];PNC=Cases[mid,P[vertex[vs],i_,indP[n__]]/;MemberQ[{vs2edge[vertex[vs],i,1],vs2edge[vertex[vs],i,-1]},DirectedEdge[vs,vt] ] ];
nPNC=ReplacePart[#,3->indP[#[[3,1]],{#[[3,2,1]],#[[3,2,2]]-1}]]&/@PNC;
sgn=First@Cases[vt-vs,x_/;Abs[x]==1];
Plus@@MapThread[(-I t)sgn WD[#1[[1]],#1[[2]],indP[#1[[3,1]],{#1[[3,2,1]],1}],a,c] orderPH[h[x1,x2,x4]/.#1->#2]&,{PNC,nPNC}]
]
orderPH[(h:Plus)[x__,y__]]:=h[orderPH[h[x]],orderPH[h[y]]]
orderPH[(h:Times)[x__,y__]]:=h[orderPH[h[x]],orderPH[h[y]]]
orderPH[x_]:=ExpandAll[x]


Q[v_,indPhead_,m_]:=Qfactor[indPhead[{1,m}],indPhead[{2,m}],indPhead[{3,m}]]P[v,1,indPhead[{1,m}]]**P[v,2,indPhead[{2,m}]]**P[v,3,indPhead[{3,m}]] 


He[v_,i_,si_,j_,sj_,k_,sk_,a_,indP_,m_]:=Block[{v0,op},v0=v[[1]]+ReplacePart[{0,0,0},i->si]+ReplacePart[{0,0,0},j->sj];
op=holonomy[vs2edge[v,i,si],a[1],a[2]]**holonomy[DirectedEdge[v[[1]]+ReplacePart[{0,0,0},i->si],v0],a[3],a[4]]
**holonomy[DirectedEdge[v0,v[[1]]+ReplacePart[{0,0,0},j->sj]],a[5],a[6] ]**holonomy[Reverse[vs2edge[v,j,sj]],a[7],a[8]]**
holonomy[vs2edge[v,k,sk],a[9],a[10]]**Q[v,indP,m]**holonomy[Reverse[vs2edge[v,k,sk]],a[10],a[11]](inn[{i,j},a[2],a[3]]
inn[{j,i},a[4],a[5]]inn[{i,j},a[6],a[7]]inn[{j,k},a[8],a[9]]inn[{k,i},a[11],a[1]]);
orderPH[epdNCM[op]]//Expand
]


judgeKoperator[{vQ_,vHe_},{i_,si_,j_,sj_,k_,sk_}]:=Block[
{v0,loopvertex,ifcontainvQ},
v0=vHe[[1]]+ReplacePart[{0,0,0},i->si]+ReplacePart[{0,0,0},j->sj];
loopvertex={vHe[[1]],vHe[[1]]+ReplacePart[{0,0,0},i->si],v0,vHe[[1]]+ReplacePart[{0,0,0},j->sj]};
ifcontainvQ=MemberQ[loopvertex,vQ[[1]]]
]


commutatorPholo[Pv_,holonomy[DirectedEdge[vs_,vt_],a_,b_],indPhead_,dummyind_,times_]:=Block[{iholoe,sgn,r},
iholoe=Flatten[Position[vt-vs,x_/;Abs[x]===1,{1},Heads->False]];
sgn=First@Cases[vt-vs,x_/;Abs[x]===1];
r=Which[Pv[[1]]===vs,(sgn I t)^times WD[Pv,iholoe[[1]],indPhead[{iholoe[[1]],times}],a,dummyind]holonomy[DirectedEdge[vs,vt],dummyind,b],Pv[[1]]===vt,
(sgn I t)^times holonomy[DirectedEdge[vs,vt],a,dummyind] WD[Pv,iholoe[[1]],indPhead[{iholoe[[1]],times}],dummyind,b] ]
]


operatorHead={P};
ToCommutate4K[(h:NonCommutativeMultiply)[x1_,x2__],(h:NonCommutativeMultiply)[y__]]:=h[ToCommutate4K[x1,h[y]],x2]+h[x1,ToCommutate4K[h[x2],h[y]]]
ToCommutate4K[x_,(h:NonCommutativeMultiply)[y1_,y2__]]:=h[ToCommutate4K[x,y1],y2]+h[y1,ToCommutate4K[x,h[y2]]]
ToCommutate4K[NonCommutativeMultiply[x_],y_]/;MemberQ[operatorHead,Head[x]]:=ToCommutate4K[x,y]
ToCommutate4K[x_,NonCommutativeMultiply[y_]]/;MemberQ[operatorHead,Head[y]]:=ToCommutate4K[x,y]
ToCommutate4K[(h:Plus)[x_,y_],z_]:=h[ToCommutate4K[x,z],ToCommutate4K[y,z]]
ToCommutate4K[z_,(h:Plus)[x_,y_]]:=h[ToCommutate4K[z,x],ToCommutate4K[z,y]]
ToCommutate4K[z_,(h:Times)[x1___,y_NonCommutativeMultiply,x2___]]:=h[x1,x2,ToCommutate4K[z,y]]
ToCommutate4K[(h:Times)[x1___,y_NonCommutativeMultiply,x2___],z_]:=h[x1,x2,ToCommutate4K[y,z]]
ToCommutate4K[P[vertex[v_],i_,x__],P[vertex[v_],j_,y__]]/;i=!=j:=0
ToCommutate4K[P[vertex[v_],i_,indP[x__]],P[vertex[v_],i_,indP[y__]]]:=t P[vertex[v],i,fluxCom[indP[x],indP[y]]]
ToCommutate4K[P[vertex[v_],i_,fluxCom[indP[x__],indP[y__]]],P[vertex[v_],i_,indP[z__]]]:=t P[vertex[v],i,fluxCom[fluxCom[indP[x],indP[y]],indP[z]]]
ToCommutate4K[P[vertex[v_],i_,indP[z__]],P[vertex[v_],i_,fluxCom[indP[x__],indP[y__]]]]:=t P[vertex[v],i,fluxCom[indP[z],fluxCom[indP[x],indP[y]]]]


Koperator[vQ_,lQoperator_,qind_,vHe_,{i_,si_,j_,sj_,k_,sk_},holoind_,holoqind_,lQholo_,___]/;vQ=!=vHe:=Block[{judgeFirst,Heoperator,pureHeO,factorHeO,holHeO,indHe,holoedge,dirEdge,Qleft1,ruleQleft1,Qleft2,ruleQleft2,commutator,commutatorrule,KO},
judgeFirst=judgeKoperator[{vQ,vHe},{i,si,j,sj,k,sk}];
If[!judgeFirst,Return[0]];
Heoperator=He[vHe,i,si,j,sj,k,sk,holoind,holoqind,lQholo];
pureHeO=Cases[Heoperator,_NonCommutativeMultiply];
factorHeO=Times@@Cases[Heoperator,Except[_NonCommutativeMultiply]];
holHeO=Cases[Heoperator,x_holonomy/;MemberQ[x[[1]],vQ[[1]]],Infinity];
indHe=indhp@@@holHeO[[All,3]];
holoedge=holHeO[[All,1]];
dirEdge=Flatten[Position[#[[2]]-#[[1]],x_/;Abs[x]==1,{1},Heads->False]&/@holoedge];
ruleQleft1=(P[vQ,#,qind[{#,lQoperator}]]->P[vQ,#,qind[{#,lQoperator-1}]])&/@dirEdge;
Qleft1= Q[vQ,qind,lQoperator]/.#&/@ruleQleft1;
ruleQleft2=(P[vQ,#,qind[{#,lQoperator}]]->P[vQ,#,qind[{#,lQoperator-2}]])&/@dirEdge;
Qleft2= Q[vQ,qind,lQoperator]/.#&/@ruleQleft2;
commutator=MapThread[commutatorPholo[vQ,#1,qind,#2,1]**#3+commutatorPholo[vQ,#1,qind,#2,2]**#4&,{holHeO,indHe,Qleft1,Qleft2}];
commutatorrule=Thread[Rule[holHeO,commutator]];
KO=Plus@@(Heoperator/.#&/@commutatorrule);
epdNCM[KO]//Expand
]


Koperator[vQ_,lQoperator_,qind_,vHe_,{i_,si_,j_,sj_,k_,sk_},holoind_,holoqind_,lQholo_,extH1_,extH2_,extH3_]/;vQ===vHe:=Block[{Heoperator,holHeO,indHe,holoedge,dirEdge,Qleft1,ruleQleft1,Qleft2,ruleQleft2,commutator,commutatorrule,KO1,inns,WDs,pureHeO,factorHeO,Op1,Q1,extrafac1,commutator1,opextra1,extrafac2,Op2,opextra2,Q2,commutator2},
Heoperator=He[vHe,i,si,j,sj,k,sk,holoind,holoqind,lQholo];
(*Heoperator=orderPH[Heoperator]//Expand;*)
(*Deal with commutator involing loop holonomies *)
holHeO=Cases[Heoperator,x_holonomy/;MemberQ[{vs2edge[vHe,i,si],Reverse[vs2edge[vHe,j,sj]]},x[[1]]],Infinity];
indHe=indhp@@@holHeO[[All,3]];
holoedge=holHeO[[All,1]];
dirEdge=Flatten[Position[#[[2]]-#[[1]],x_/;Abs[x]==1,{1},Heads->False]&/@holoedge];
ruleQleft1=(P[vQ,#,qind[{#,lQoperator}]]->P[vQ,#,qind[{#,lQoperator-1}]])&/@dirEdge;
Qleft1= Q[vQ,qind,lQoperator]/.#&/@ruleQleft1;
ruleQleft2=(P[vQ,#,qind[{#,lQoperator}]]->P[vQ,#,qind[{#,lQoperator-2}]])&/@dirEdge;
Qleft2= Q[vQ,qind,lQoperator]/.#&/@ruleQleft2;
commutator=MapThread[commutatorPholo[vQ,#1,qind,#2,1]**#3+commutatorPholo[vQ,#1,qind,#2,2]**#4&,{holHeO,indHe,Qleft1,Qleft2}];
commutatorrule=Thread[Rule[holHeO,commutator]];
KO1=Plus@@(Heoperator/.#&/@commutatorrule)//epdNCM;
(*Deal with commutator involing Q, the 2-fold commutator case*)
Op1=(-I t)lQholo NonCommutativeMultiply@@Cases[Heoperator,_holonomy,Infinity];
inns=Times@@Cases[Heoperator,_inn,Infinity];
WDs=Times@@Cases[Heoperator,_WD,Infinity]//ReplacePart[#,3->extH1[{k,1}]]&; 
Op1=inns WDs Qfactor[extH1[{1,1}],extH1[{2,1}],extH1[{3,1}]] Op1**Q[vHe,holoqind,lQholo]//epdNCM;
(************)
extrafac1=Qfactor[extH2[{1,1}],extH2[{2,1}],extH2[{3,1}]];
opextra1=extrafac1 Op1;
(********************)
Q1= lQoperator Q[vQ,qind,lQoperator-2]//epdNCM;
commutator1=ToCommutate4K[P[vHe,1,extH2[{1,1}]]**P[vHe,2,extH2[{2,1}]]**P[vHe,3,extH2[{3,1}]],P[vQ,i,extH1[{i,1}]]**P[vQ,j,extH1[{j,1}]]];
commutator1=(commutator1//epdNCM)/.___**0**___:>0;
opextra1=opextra1**commutator1**Q1//epdNCM;
(******************************************************)
extrafac2=Qfactor[extH2[{1,1}],extH2[{2,1}],extH2[{3,1}]]Qfactor[extH3[{1,1}],extH3[{2,1}],extH3[{3,1}]];
(*********)
Op2=(-I t)lQholo NonCommutativeMultiply@@Cases[Heoperator,_holonomy,Infinity];
Op2=inns WDs Qfactor[extH1[{1,1}],extH1[{2,1}],extH1[{3,1}]] Op2**Q[vHe,holoqind,lQholo-1]//epdNCM;
opextra2=extrafac2 Op2;
Q2= binomial[lQoperator,lQholo] Q[vQ,qind,lQoperator-2];
commutator2=ToCommutate4K[P[vHe,1,extH3[{1,1}]]**P[vHe,2,extH3[{2,1}]]**P[vHe,3,extH3[{3,1}]],commutator1];
commutator2=(commutator2//epdNCM)/.___**0**___:>0;
opextra2=opextra2**commutator2**Q2//epdNCM;
KO1+opextra1+opextra2
]


P2WDs[(x:P[__]),0]:=Function[{a,b},1]
P2WDs[(x:P[__,indP[__]]),times_]:=Function[{a,b},WD[x[[1]],x[[2]],indP[x[[3,1]],{x[[3,2,1]],times}],a,b]]
P2WDs[(x:P[__,fluxCom[__]]),1]:=Function[{a,b},WD[x[[1]],x[[2]],x[[3]],a,b]]
P2WDs[(x:P[__,fluxCom[__]]),2]:=Function[{a,b},0]
(*****************************)
P2WDst[(x:P[__]),0]:=Function[{a,b},1]
P2WDst[(x:P[__,indP[__]]),times_]:=Function[{a,b},WDt[x[[1]],x[[2]],indP[x[[3,1]],{x[[3,2,1]],times}],a,b]]
P2WDst[(x:P[__,fluxCom[__]]),1]:=Function[{a,b},WDt[x[[1]],x[[2]],x[[3]],a,b]]
P2WDst[(x:P[__,fluxCom[__]]),2]:=Function[{a,b},0]
(*****************************)
P2nPNC[(x:P[__,indP[__]]),times_]:=ReplacePart[x,3->indP[x[[3,1]],{x[[3,2,1]],x[[3,2,2]]-times}]]
P2nPNC[(x:P[__,fluxCom[__]]),1]:=1
P2nPNC[(x:P[__,fluxCom[__]]),2]:=0


(*order the operator taking the form h P h^{-1}, ifPtHoloCommttv=True means we do NOT consider [h_e,P_t(e)]*)
orderPH4HL[(h:NonCommutativeMultiply)[x1___,holonomy[DirectedEdge[vs_,vt_],a_,b_],x2__, holonomy[DirectedEdge[vt_,vs_],b_,c_],x4___],dummyheadl_,dummyheadr_,ifPtHoloCommttv_]:=
Block[{mid,PNC,nPNC,PNC0,posCom2,posNonCom,sgn,r1,r10,PNCt,lPNCt,nPNCt,sgnofWD,sgnofWD1,r2,r20,r21,posOfOne,WDs,rules,opleft,r4},
mid=List[x2];
(*******************************Consider [h_e,p_s(e)]****************************************************************)
sgn=First@Cases[vt-vs,x_/;Abs[x]==1];
PNC=Cases[mid,P[vertex[vs],i_,indP[__]]/;MemberQ[{vs2edge[vertex[vs],i,1],vs2edge[vertex[vs],i,-1]},DirectedEdge[vs,vt] ] ];
nPNC=Map[ReplacePart[#,3->indP[#[[3,1]],{#[[3,2,1]],#[[3,2,2]]-1}]]&,PNC];
r1=Plus@@MapThread[(-I t)sgn WD[#1[[1]],#1[[2]],indP[#1[[3,1]],{#1[[3,2,1]],1}],a,c] h[x1,x2,x4]/.#1->#2&,{PNC,nPNC}];
PNC=Cases[mid,P[vertex[vs],i_,fluxCom[__,fluxCom[__]]]/;MemberQ[{vs2edge[vertex[vs],i,1],vs2edge[vertex[vs],i,-1]},DirectedEdge[vs,vt] ] ];
nPNC=ConstantArray[1,Length[PNC]];
r10=If[PNC=!={},Plus@@MapThread[(-I t)sgn WD[#1[[1]],#1[[2]],#1[[3]],a,c] h[x1,x2,x4]/.#1->#2&,{PNC,nPNC} ],0];
r10=r10//.x___**1**y___:>x**y;
r1=r1+r10;
(**************************************************************************************************************************************)
PNC=Cases[mid,P[vertex[vs],i_,__]/;MemberQ[{vs2edge[vertex[vs],i,1],vs2edge[vertex[vs],i,-1]},DirectedEdge[vs,vt] ] ];
PNC0=Cases[PNC, P[__,fluxCom[_indP,_indP] ] ];
PNC=DeleteCases[PNC,P[__,fluxCom[_indP,_indP]]];
PNC=Tuples[{PNC,PNC0}];
If[PNC=={},Goto[jumphere]];
PNC=SortBy[#,Position[mid,#]&]&/@PNC;
WDs=Map[P2WDs[#,1]&,PNC,{2}];
WDs=MapIndexed[MapThread[Apply[#1,#2]&,{#,{{a,dummyheadl[{First[#2],2}]},{dummyheadl[{First[#2],2}],c}}}]&,WDs];
WDs=Times@@@WDs;
WDs=sgn (-I t)^2 WDs;
nPNC=Map[P2nPNC[#,1]&,PNC,{2}];
rules=MapThread[Rule,{PNC,nPNC},2];
r10=h[x1,x2,x4]/.rules;
r10=Times[WDs,r10];
r10=Plus@@r10;
r10=r10//.x___**1**y___:>x**y;
r1=r1+r10;
Label[jumphere];
(**************************************************************************************************************************************)
If[ifPtHoloCommttv,Return[r1]];
(*******************************Consider [h_e,p_t(e)]****************************************************************)
PNCt=Cases[mid,P[vertex[vt],i_,__]/;MemberQ[{vs2edge[vertex[vt],i,1],vs2edge[vertex[vt],i,-1]},DirectedEdge[vt,vs] ] ];
lPNCt=Length[PNCt];
If[PNCt=={},Return[r1]];
(*=============================================\[Equal]select one p_t(e), do commutator for one time===================================================================*)
nPNCt=P2nPNC[#,1]&/@PNCt;
WDs=MapIndexed[P2WDs[#1,1][dummyheadl[First[#2]],dummyheadr[First[#2]]]&,PNCt];
sgnofWD=If[MatchQ[#,WD[__,fluxCom[_indP,_indP],__]],-1,sgn]&/@WDs;
WDs=(-I t) Times[sgnofWD,WDs];
opleft=Table[h[x1,x2,holonomy[DirectedEdge[vs,vt],a,dummyheadl[i]],holonomy[DirectedEdge[vt,vs],dummyheadr[i],c],x4]/.PNCt[[i]]->nPNCt[[i]],{i,1,Length[nPNCt]}];
opleft=opleft//.x___**1**y___:>x**y;
r2=Times[WDs,opleft];
r2=Plus@@r2;
(*=============================================\[Equal]select one p_t(e), do commutator for two times===================================================================*)
nPNCt=P2nPNC[#,2]&/@PNCt;
WDs=MapIndexed[P2WDst[#1,2][dummyheadl[First[#2]],dummyheadr[First[#2]]]&,PNCt];
WDs= -t^2 WDs;
opleft=Table[h[x1,x2,holonomy[DirectedEdge[vs,vt],a,dummyheadl[i]],holonomy[DirectedEdge[vt,vs],dummyheadr[i],c],x4]/.PNCt[[i]]->nPNCt[[i]],{i,1,Length[nPNCt]}];
r21=Times[WDs,opleft];
r21=Plus@@r21;
r2=r2+r21;
(*=============================================\[Equal]select one p_t(e) and one p_s(e), do commutator for two times===================================================================*)
PNC=Cases[mid,P[vertex[vs],i_,__]/;MemberQ[{vs2edge[vertex[vs],i,1],vs2edge[vertex[vs],i,-1]},DirectedEdge[vs,vt] ] ];
If[PNC=={},Goto[jumphere0]];
PNC=Tuples[{PNC,PNCt}];
WDs=Map[P2WDs[#,1]&,PNC,{2}];
WDs=MapIndexed[MapThread[Apply[#1,#2]&,{#,{{a,b},{dummyheadl[{First[#2],2}],dummyheadr[{First[#2],1}]}}}]&,WDs];
(*Here the index in WD is chosen to be {a,b} so that in the function expectedValueExtra we could find out all of those ForNewWDinnfactorExtra*)
sgnofWD=If[MatchQ[#,WD[__,fluxCom[_indP,_indP],__]],1,sgn]&/@(Transpose[WDs][[1]]);
sgnofWD1=If[MatchQ[#,WD[__,fluxCom[_indP,_indP],__]],-1,sgn]&/@(Transpose[WDs][[2]]);
sgnofWD=Times[sgnofWD,sgnofWD1];
WDs=Times@@@WDs;
WDs=(-I t)^2 Times[sgnofWD,WDs];
nPNC=Map[P2nPNC[#,1]&,PNC,{2}];
rules=MapThread[Rule,{PNC,nPNC},2];
opleft=MapIndexed[h[x1,x2,holonomy[DirectedEdge[vs,vt],b,dummyheadl[{First[#2],2}]],holonomy[DirectedEdge[vt,vs],dummyheadr[{First[#2],1}],c],x4]/.#1&,rules];
opleft=opleft//.x___**1**y___:>x**y;
r21=Times[WDs,opleft];
r21=Plus@@r21;
r2=r2+r21;
Label[jumphere0];
If[lPNCt==1,Return[r1+r2]];
(*************************************************************************************************************************************)
posOfOne=Permutations[PadRight[{1,1},lPNCt]];
nPNCt=Table[MapAt[P2nPNC[#,1]&,PNCt,Position[posOfOne[[i]],1]],{i,1,Length[posOfOne]}];
WDs=MapThread[P2WDs[#1,#2]&,{PNCt,#}]&/@posOfOne;
WDs=DeleteCases[WDs,x_/;x[_,_]===1,{2}];
WDs=Table[MapThread[Apply[#1,#2]&,{WDs[[i]],{{dummyheadl[{i,2}],dummyheadr[{i,1}]},{dummyheadl[{i,1}],dummyheadl[{i,2}]} }}],{i,1,Length[WDs]}];(*Notice the order of the two WDs*)
sgnofWD=Map[If[MatchQ[#,WD[__,fluxCom[_indP,_indP],__]],-1,sgn]&,WDs,{2}];
sgnofWD=Times@@@sgnofWD;
WDs=Times@@@WDs;
WDs=-t^2 WDs;
rules=MapThread[Rule,{PNCt,#}]&/@nPNCt;
opleft=MapIndexed[h[x1,x2,holonomy[DirectedEdge[vs,vt],a,dummyheadl[Append[#2,1]]],holonomy[DirectedEdge[vt,vs],dummyheadr[Append[#2,1]],c],x4]/.#1&,rules];
opleft=opleft//.x___**1**y___:>x**y;
r4=Times[WDs,opleft];
r4=(Plus@@r4);
(r1+r2+r4)
]
orderPH4HL[(h:Plus)[x_,y__],dummyheadl_,dummyheadr_,ifPtHoloCommttv_]:=h[orderPH4HL[x,dummyheadl,dummyheadr,ifPtHoloCommttv],orderPH4HL[h[y],dummyheadl,dummyheadr,ifPtHoloCommttv]]
orderPH4HL[(h:Times)[x___,y_NonCommutativeMultiply,z___],dummyheadl_,dummyheadr_,ifPtHoloCommttv_]:=h[x,z,orderPH4HL[h[y],dummyheadl,dummyheadr,ifPtHoloCommttv]]
orderPH4HL[x_,dummyheadl_,dummyheadr_]:=ExpandAll[x]


 (*ifPtHoloCommttv=True means we do NOT consider [h_e,P_t(e)],i.e. the segment-version*)
Hl[indh0_,{vQ1_,lQoperator1_,qind1_,vHe1_,{i1_,si1_,j1_,sj1_,k1_,sk1_},holoind1_,holoqind1_,lQholo1_},{vQ2_,lQoperator2_,qind2_,vHe2_,{i2_,si2_,j2_,sj2_,k2_,sk2_},holoind2_,holoqind2_,lQholo2_},qind3_,lq3_,extraH1x_,extraH2x_,extraH3x_,extraH1y_,extraH2y_,extraH3y_,indhextrxl_,indhextrxr_,indhextryl_,indhextryr_,ifPtHoloCommttv_]:=
Block[{KO1,KO2,innfactors,hQh,hKO1h,power1,hKO2h,power2,power,Non0pos,result},
If[!IntersectingQ[{vertex[{0,0,0}],vertex[{1,0,0}]},{vQ1,vHe1}]||!IntersectingQ[{vertex[{0,0,0}],vertex[{0,1,0}]},{vQ2,vHe2}],Return[{0}]];
KO1=Koperator[vQ1,lQoperator1,qind1,vHe1,{i1,si1,j1,sj1,k1,sk1},holoind1,holoqind1,lQholo1,extraH1x,extraH2x,extraH3x];
If[KO1===0,Return[{0}]];
KO2=Koperator[vQ2,lQoperator2,qind2,vHe2,{i2,si2,j2,sj2,k2,sk2},holoind2,holoqind2,lQholo2,extraH1y,extraH2y,extraH3y];
If[KO2===0,Return[{0}]];
(*========================*)
innfactors=inn[{1,2} ,indh0[3],indh0[4]]inn[{2,3},indh0[6],indh0[7]]inn[{3,1},indh0[9],indh0[1]];
(*========================*)
hKO1h=holonomy[DirectedEdge[{0,0,0},{1,0,0}],indh0[1],indh0[2]]**KO1**holonomy[DirectedEdge[{1,0,0},{0,0,0}],indh0[2],indh0[3]]//epdNCM//Expand;
hKO1h=orderPH4HL[hKO1h,indhextrxl,indhextrxr,ifPtHoloCommttv];
If[hKO1h==0,Return[{0}]];
hKO1h=hKO1h//epdNCM//Expand//Function[u,Normal[u+O[t]^5]]//Expand;
hKO1h=List@@hKO1h;
(*========================*)
hKO2h=holonomy[DirectedEdge[{0,0,0},{0,1,0}],indh0[4],indh0[5]]**KO2**holonomy[DirectedEdge[{0,1,0},{0,0,0}],indh0[5],indh0[6]]//epdNCM//Expand;
hKO2h=orderPH4HL[hKO2h,indhextryl,indhextryr,ifPtHoloCommttv];
If[hKO2h==0,Return[{0}]];
hKO2h=hKO2h//epdNCM//Function[u,Normal[u+O[t]^5]]//Expand;
hKO2h=List@@hKO2h;
(*========================*)
hQh=holonomy[DirectedEdge[{0,0,0},{0,0,1}],indh0[7],indh0[8]]**Q[vertex[{0,0,0}],qind3,lq3]**holonomy[DirectedEdge[{0,0,1},{0,0,0}],indh0[8],indh0[9]];
hQh=hQh//epdNCM//Expand//orderPH;
(*========================*)
power1=Cases[#,t^_,Infinity]&/@hKO1h//Flatten;
power2=Cases[#,t^_,Infinity]&/@hKO2h//Flatten;
power=Times@@@Tuples[{power1,power2}]/.t^n_/;n>=8->0;
Non0pos=Position[power,x_/;x=!=0,{1},Heads->False]//Flatten;
Non0pos=Tuples[{Range[Length[power1]],Range[Length[power2]]}][[Non0pos]];
result=(innfactors hKO1h[[#[[1]]]]**hKO2h[[#[[2]]]]**hQh)&/@Non0pos;
result=epdNCM/@result
]
