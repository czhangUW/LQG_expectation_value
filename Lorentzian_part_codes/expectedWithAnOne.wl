(* ::Package:: *)

(*myDot[overallfactor_,expectedvaluesWRTholorule_,holorule_]/;overallfactor==0:=0
myDot[overallfactor_,expectedvaluesWRTholorule_,holorule_]/;Total[Abs[expectedvaluesWRTholorule]]==0:=0
myDot[overallfactor_,expectedvaluesWRTholorule_,holorule_]:=Block[{Without0},
Without0={expectedvaluesWRTholorule,holorule}//Transpose;
Without0=DeleteCases[Without0,{0,_}];
Plus@@(Times[#[[1]],overallfactor/.#[[2]]]&/@Without0)
]*)


expectedWithOne[anoperatorExtra_,anoperatorLeft_,overallfactor_,anruleForExtraOp_,SpecialRulesWRTrule0list_,fac4SPR_,rule0List_,basicpower_,sumofpm1_:1]:=
Block[{valuedoverallfactor,pos4Noncompute,ruleForExtraOpArray,Lefthololist,ruleLeftholoind,Extrahololist,indExtrahololist,indExtrahololistV,
ruleExtraholoind,ruledExtraOps,distEdgeExtraOps,expectedVExtra,indPruledLeftOps,expectedValueLeft,allexpectedvalues,ruleAllholoind,allfactorWDinn,allfactorWDinnrule,result},
If[MemberQ[anoperatorLeft,P[__,fluxCom[_indP,_indP]],Infinity],Return[ConstantArray[0,Length[rule0List]]]];
(*here we used that <P[__,fluxCom[_indP,_indP]]> = 0 for fluxCom[_indP,_indP]={0}.*)
(*data structure*)
(*level 1: various rule0*)
(*level 2: various rule for operatorExtra*)
(*level 3: various special rules*)
valuedoverallfactor=Function[u,MapThread[factorValue[Prepend[anoperatorLeft,anoperatorExtra],overallfactor,u,#1,#2]&,{SpecialRulesWRTrule0list,fac4SPR}]]/@rule0List;
If[(Abs[Flatten[valuedoverallfactor]]//Total)==0,Return[ConstantArray[0,Length[rule0List]] ]];
pos4Noncompute=Position[valuedoverallfactor,x_/;x==0,{2},Heads->False];
ruleForExtraOpArray=ConstantArray[anruleForExtraOp,Length[rule0List]];
(*ruleForExtraOp, rule0Listp have the same shape as overvaltorExtraV1*)
(*===============\[Equal]Get the rules for holonomy indices and calculate the expectation values =========================\[Equal]*)
(*holonomy is divided into two parts, one is in anoperatorLeft_, the other is in anoperatorExtra_*)
Lefthololist=Cases[anoperatorLeft,_holonomy,Infinity];
Lefthololist=GatherBy[Lefthololist,Sort[First[#]]&];
ruleLeftholoind=getHoloindrule/@Lefthololist;
Extrahololist=Cases[anoperatorExtra,_holonomy,Infinity];
indExtrahololist=List@@@Extrahololist[[All,2;;3]]//Flatten;
(*******)
indExtrahololistV=Tuples[{-1/2,1/2},Length[indExtrahololist]];
indExtrahololistV=Partition[#,2]&/@indExtrahololistV;
indExtrahololistV=DeleteCases[indExtrahololistV,x_/;(Count[Abs[#[[1]]-#[[2]]]&/@x,1]!=sumofpm1)];
indExtrahololistV=Flatten/@indExtrahololistV;
ruleExtraholoind=Map[Thread[Rule[indExtrahololist,#]]&,indExtrahololistV];
ruleExtraholoind=DeleteCases[ruleExtraholoind,{___,Rule[x_,y_],___,Rule[x_,z_],___}/;z!=y];
ruleExtraholoind=DeleteDuplicates/@ruleExtraholoind;
(*======================================================\[Equal]*)
(*Calculate the expected value of the left operator*)
indPruledLeftOps=anoperatorLeft/.{fluxCom[___,fluxCom[__],___]:>{0},P[x__,fluxCom[_indP,_indP]]:>P[x,{0},1]};
indPruledLeftOps=(indPruledLeftOps/.indP[i_,{j_,len_}]:>ConstantArray[0,len/.#])&/@rule0List;
{expectedValueLeft,ruleLeftholoind}=expectedDeOps[indPruledLeftOps,ruleLeftholoind,0];
If[expectedValueLeft=={},Return[ConstantArray[0,Length[rule0List]] ]];
expectedValueLeft=ConstantArray[#,Length[anruleForExtraOp]]&/@expectedValueLeft;
(*======================================================\[Equal]*)
(*Calculate the expected value of the extra operator*)
(*data structure now*)
(*level 1: various rule0*)
(*level 2: various rules for operatorExtra*)
(*level 3: various holonomy rule*)
(*********)
ruleForExtraOpArray=Fold[ReplacePart[#1,#2->{_:>ConstantArray[0,Length[ruleExtraholoind]]}]&,ruleForExtraOpArray,pos4Noncompute];
(*********)
ruledExtraOps=anoperatorExtra/.P[x__,y:fluxCom[_indP,_indP]]:>P[x,y,1];
ruledExtraOps=ruledExtraOps/.ruleExtraholoind;
ruledExtraOps=ruledExtraOps/.ruleForExtraOpArray;
ruledExtraOps=ruledExtraOps/.{P[v_,i_,alpha_]:>flux[v,vs2edge[v,i,1],alpha]-flux[v,Sort[vs2edge[v,i,-1]],alpha],P[v_,i_,alpha_,1]:>flux[v,vs2edge[v,i,1],alpha]+flux[v,Sort[vs2edge[v,i,-1]],alpha]};
ruledExtraOps=Map[epdNCM,ruledExtraOps,{3}];
distEdgeExtraOps=(Map[distIndsToEdge,ruledExtraOps,{3}])/.{NonCommutativeMultiply->Times,distind[0]->0}//Simplify;
expectedVExtra=distEdgeExtraOps/.facind[fac_,edges_,indl_,indr_]:>fac hpspth[Flatten[indl],Flatten[indr],1];
expectedVExtra=(expectedVExtra/.t->0)+t( D[expectedVExtra,t]/.t->0);
(************)
allexpectedvalues=Apply[Times,MapThread[Tuples[{#1,#2}]&,{expectedVExtra,expectedValueLeft},2],{3}];
ruleAllholoind=Dispatch/@Tuples[{ruleExtraholoind,ruleLeftholoind}];
(*Now the data structure*)
(*1) For allexpectedvalues: level 1\[Rule] various rule0list, level 2\[Rule]various rules in anruleForExtraOp, level 3\[Rule] various rules in total holonomy rule*)
(*2) For ruleAllholoind: level 1\[Rule]  various rules in ruleAllholoind*)
allfactorWDinn=valuedoverallfactor//Flatten;
allfactorWDinn=If[Head[#]===Plus,List@@#,{#}]&/@allfactorWDinn;
allfactorWDinn=Flatten[allfactorWDinn];
allfactorWDinn=MapAt[Times@@Cases[#,_factorWDinn|_Plus]&,allfactorWDinn,Position[allfactorWDinn,_Times,{1},Heads->False]];
allfactorWDinn=allfactorWDinn//DeleteDuplicates;
allfactorWDinnrule=(allfactorWDinn/.ruleAllholoind);
allfactorWDinnrule=Transpose[allfactorWDinnrule];
allfactorWDinnrule=Thread[Rule[allfactorWDinn,allfactorWDinnrule]];
valuedoverallfactor=valuedoverallfactor/.allfactorWDinnrule;
(***********************)
(*Because of the overall factor binomial[] in front of factor value, 
some elements of overallfactorValueAb maight be 0, which is the reason why we use myDot*)
result=MapThread[Dot[#1,#2]&,{ valuedoverallfactor,allexpectedvalues},2];
result=t^(-basicpower) result;
result= Total/@result//Expand
]
