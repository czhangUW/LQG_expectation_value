(* ::Package:: *)

expectedValueOneTerm[decoupleOperator_,overallfactor_,rule0list0_,basicpower_,nt_:1]:=
Block[{resultlist0,tpower,rule0List,pos4resultlist,specialPs,fac4SPR,specialrules,overallfactorValueAb,ComptExpectedQ,expectedValues,holoindrule,overallfactorValue,indhruleMatchOp,allfactorWDinn,
allfactorWDinnrule,r0,indPsinWD,valueOfWD,Ps,holoOps,holoToPs,PAndholoToPs,ToSortPholo,orderedPAndholoToPs,allExtraOps,switch,operatorLeft,operatorExtra,rule0List1,resultlist11,
pos4resultlist1,ruleForExtraOp,SpecialRule,r11,resultlist12,r12,r},
(*Compute the result when all flux indices vanishes*)
(*==================\[Equal]Basic judge to deal with the singular cases==========================*)
resultlist0=ConstantArray[0,Length[rule0list0]];
tpower=First@Cases[overallfactor t^2,Power[t,x_]:>x];
tpower=tpower-2;
If[tpower-basicpower>nt,Return[resultlist0]];
(*tpower-basicpower is the order of the expression.*)
rule0List=DeleteCases[rule0list0,x_/;judgelenindP[decoupleOperator,x]];
If[rule0List=={},Return[resultlist0]];
pos4resultlist=Position[rule0list0,x_/;MemberQ[rule0List,x],{1},Heads->False]//Flatten;
(****************)
    (*in such case we need only calculate the zeroth order of the expectation value and P[__,fluxCom[_indP,_indP]] gives 0*)
If[MemberQ[decoupleOperator,P[__,fluxCom[_indP,_indP]],Infinity]&& nt-(tpower-basicpower)==0,Return[resultlist0] ];
(******evaluate the result of overall factor******)
specialPs=Cases[decoupleOperator,P[__,fluxCom[__]],Infinity];
{fac4SPR,specialrules}=If[specialPs==={},{{},{}},GetfluxComSpRule[#,0]&/@specialPs//Transpose];
fac4SPR=Times@@@Tuples[fac4SPR];
specialrules=Flatten/@Tuples[specialrules];
overallfactorValueAb=t^(-basicpower)factorValue[decoupleOperator,overallfactor,#,specialrules,fac4SPR]&/@rule0List;
(*Because of the overall factor binomial[] in front of factor value, some elements of overallfactorValueAb maight be 0.*)
(*here the holonomy indices in overallfactorValue haven't been replaced by holoindrule*)
(*overallfactorValueAb is a list in which each element corresponds to a rule0 in rule0list*)
ComptExpectedQ=(MatchQ[overallfactorValueAb,{0..}]||overallfactorValueAb==={0});
If[ComptExpectedQ,Goto[jumphere0]];
{expectedValues,holoindrule}=expectedValueFluxAll0[decoupleOperator,rule0List,nt-(tpower-basicpower)];
If[expectedValues=={},Goto[jumphere0]];
(********use holonomy index law to replace holonomy indices inside *****) 
allfactorWDinn=If[Head[#]===Plus,List@@#,{#}]&/@overallfactorValueAb;
allfactorWDinn=Flatten[allfactorWDinn];
(*Because of the overall factor binomial[] in front of factor value, some elements of overallfactorValueAb maight be 0*)
allfactorWDinn=MapAt[Times@@Cases[#,_factorWDinn|_Plus,{1},Heads->False]&,allfactorWDinn,Position[allfactorWDinn,_Times,{1},Heads->False]];
allfactorWDinn=allfactorWDinn//DeleteDuplicates;
allfactorWDinnrule=(allfactorWDinn/.holoindrule);
allfactorWDinnrule=Transpose[allfactorWDinnrule];
allfactorWDinnrule=Thread[Rule[allfactorWDinn,allfactorWDinnrule]];
overallfactorValue=overallfactorValueAb/.allfactorWDinnrule;
(***************************************)
r0=MapThread[Dot,{overallfactorValue,expectedValues}]//Expand;
pos4resultlist=MapThread[Rule,{pos4resultlist,r0}]//Dispatch;
resultlist0=ReplacePart[resultlist0,pos4resultlist];
Label[jumphere0];
If[nt==tpower-basicpower,Return[resultlist0]];
(***********************************************************************************************************************)
(*The idea is as follows. We first set a flux index to be +1/-1.*)
(*According to the non-vanishing condition of Qfactor, there must another +1/-1 for other direction appearing in the same Qfactor*)
(*For instance, in alpha in Qfactor[alpha,beta,gamma] is set to be +1/-1, then either beta or gamma must be +1/-1*)
(*The flux indices appear only in WD[__] or P[__].*)
(*Because all other indices in P[__] are 0, for the flux indices in P[__], only the case P[__, fluxCom[_inP,_inP]] are needed to be considered. *)
(*However, now we will only consider the leading order of the expectation value, the term, in which P[__, fluxCom[_inP,_inP]] is a factor and it's *)
(* flux fluxCom[__] is set to be 0, vanishes.*)
(*Therefore, only indP[__] in WD[__] can give us the other +1/-1*)
(*Taking advantage of the function assignvalue[__], thoese P with affilicated WD[__] can be picked out.*)
indPsinWD=Cases[overallfactor,_factorWDinn,Infinity];
indPsinWD=Cases[indPsinWD[[All,2]],_indP,Infinity];
valueOfWD=assignvalue/@indPsinWD;
Ps=Cases[decoupleOperator,_P,{2}];
Ps=Cases[Ps,x_/;IntersectingQ[First[assignvalue[x]],First[#1]]&&Last[assignvalue[x]]=!=Last[#1]]&/@valueOfWD;
Ps=Flatten[Ps]//DeleteDuplicates;
(*Duplications of Ps are from two cases 1) Duplications of indPsinWD; 2) in indPsinWD, there may exists indP[i,{1,len}],indP[i,{2,len}], where P[v,3,indP[i,{3,len}]] will be obtained twice*)
(*each Ps is the P operator one of whose indices can be 1 or -1*)
holoOps=Cases[decoupleOperator,_holonomy,{2}];
holoToPs=Cases[holoOps,x_/;MemberQ[{vs2edge[#[[1]],#[[2]],1]//Sort,vs2edge[#[[1]],#[[2]],-1]//Sort},Sort[x[[1]] ] ] ]&/@Ps;
PAndholoToPs=MapThread[Insert[#1,#2,1]&,{holoToPs,Ps}];
ToSortPholo=Flatten[List@@@decoupleOperator];
orderedPAndholoToPs=SortBy[#,Position[ToSortPholo,#]& ]&/@PAndholoToPs;
orderedPAndholoToPs=epdNCM/@(NonCommutativeMultiply@@@orderedPAndholoToPs);
allExtraOps=DeleteCases[orderedPAndholoToPs,_P];
(*Because of the non-vanishing condition of the expectation value of an operator*)
(*otherwise, we will calculate the expectation value of such operator p^0\cdots p^0p^1p^0...*)
switch=(allExtraOps==={});
If[switch,Goto[jumphere1]];
{operatorLeft,operatorExtra}=Transpose[seperateOps[decoupleOperator,#]&/@allExtraOps];
rule0List1=ConstantArray[rule0list0,Length[operatorLeft]];
rule0List1=MapThread[DeleteCases[#1,x_/;judgelenindP[#2,x]]&,{rule0List1,operatorLeft}];
(*Each sublist in rule0List1 corresponds to a pair of operatorleft and operatorExtra*)
(*In principle, there exist the case where rule0List[[i]]={} for some operatorLeft[[i]],operatorExtra[[i]]*)
{rule0List1,operatorLeft,operatorExtra}=Map[Delete[#,Position[rule0List1,{}]]&,{rule0List1,operatorLeft,operatorExtra}];
switch=operatorLeft==={};
If[switch,Goto[jumphere1]];
(*****Create array to store result****)
resultlist11=ConstantArray[0,{Length[operatorLeft],Length[rule0list0]}];
pos4resultlist1=Position[rule0list0,xx_/;MemberQ[#,xx],{1},Heads->False]&/@rule0List1;
pos4resultlist1=Flatten/@pos4resultlist1;(*It tells us 0 in which position should be replaced finally*)
(*************************************)
{ruleForExtraOp,fac4SPR,SpecialRule}=Transpose[MapThread[creatSpecialRule,{operatorExtra,operatorLeft,rule0List1}]];
r11=Table[expectedWithOne[operatorExtra[[i]],operatorLeft[[i]],overallfactor,ruleForExtraOp[[i]],SpecialRule[[i]],fac4SPR[[i]],rule0List1[[i]],basicpower],{i,1,Length[ruleForExtraOp]}];
pos4resultlist1=MapThread[Rule[#1,#2]&,{pos4resultlist1,r11},2];
pos4resultlist1=Dispatch[pos4resultlist1];
resultlist11=MapThread[ReplacePart[#1,#2]&,{resultlist11,pos4resultlist1}];
Label[jumphere1];
resultlist11=If[switch, ConstantArray[0,Length[rule0list0]],Total[resultlist11]];
indPsinWD=Cases[overallfactor,_factorWDinn,Infinity];
indPsinWD=Cases[indPsinWD[[All,2]],_indP,Infinity];
(******)
indPsinWD=indPsinWD/.indP[ith_,{dir_,len_/;len>=2},___]:>ConstantArray[indP[ith,{dir,1}],len];
(*Then, in latter codes, we only consider the P operator with at least 2 affilicated WD[__]*)
indPsinWD=indPsinWD//Flatten;
(*******)
valueOfWD=assignvalue/@indPsinWD;
Ps=Cases[decoupleOperator,_P,{2}];
Ps=Cases[Ps,x_/;IntersectingQ[First[assignvalue[x]],First[#1]]&&Last[assignvalue[x]]=!=Last[#1]]&/@valueOfWD;
Ps=Flatten[Ps];
Ps=GatherBy[Ps,#[[1;;2]]&];
Ps=DeleteDuplicatesBy[Subsets[#,{2}],Sort]&/@Ps;
(*We consider those P with at least 2 affilicated WD[__] whose flux indices are +1 and -1 respectively*)
Ps=DeleteDuplicatesBy[Flatten[Ps,1],Sort];
(*DeleteDuplicatesBy is because, saying, Subsets[{1,2,1,3},{2}]={{1,2},{1,1},{1,3},{2,1},{2,3},{1,3}}. However here, for such case, we only need {1,2} for once*)
(*Here there are the cases in Ps of {x,x}, which means that the +1/-1 indices are from the same indP[__]*)
(*in such case, the length of indP[__] in x will finally become its origional length minusing 2 *)
(*however, the following deleted cases will not allowed*)
Ps=DeleteCases[Ps,{P[x__,y_fluxCom],P[x__,y_fluxCom]}];
(******)
holoOps=Cases[decoupleOperator,_holonomy,{2}];
holoToPs=Cases[holoOps,x_/;MemberQ[{vs2edge[#[[1,1]],#[[1,2]],1]//Sort,vs2edge[#[[1,1]],#[[1,2]],-1]//Sort},Sort[x[[1]] ] ] ]&/@Ps;
PAndholoToPs=Flatten/@MapThread[Insert[#1,#2,1]&,{holoToPs,Ps}];
ToSortPholo=Thread[Rule[#,Range[Length[#]]]&@Flatten[List@@@decoupleOperator]];
orderedPAndholoToPs=SortBy[#,#/.ToSortPholo&]&/@PAndholoToPs;
allExtraOps=epdNCM/@(NonCommutativeMultiply@@@orderedPAndholoToPs);
If[allExtraOps=={},Return[Expand[resultlist0+resultlist11]]];
{operatorLeft,operatorExtra}=Transpose[seperateOps[decoupleOperator,#]&/@allExtraOps];
rule0List1=ConstantArray[rule0list0,Length[operatorLeft]];
rule0List1=MapThread[DeleteCases[#1,x_/;judgelenindP[#2,x]]&,{rule0List1,operatorLeft}];
(*In principle, there exist the case where rule0List[[i]]={} for some operatorLeft[[i]],operatorExtra[[i]]*)
{rule0List1,operatorLeft,operatorExtra}=Map[Delete[#,Position[rule0List1,{}]]&,{rule0List1,operatorLeft,operatorExtra}];
If[operatorLeft==={},Return[Expand[resultlist0+resultlist11]]];
(*****Create array to store result****)
resultlist12=ConstantArray[0,{Length[operatorLeft],Length[rule0list0]}];
pos4resultlist1=Position[rule0list0,xx_/;MemberQ[#,xx],{1},Heads->False]&/@rule0List1;
pos4resultlist1=Flatten/@pos4resultlist1;
(************************************)
{ruleForExtraOp,fac4SPR,SpecialRule}=Transpose[MapThread[creatSpecialRule,{operatorExtra,operatorLeft,rule0List1}]];
r12=Table[expectedWithOne[operatorExtra[[i]],operatorLeft[[i]],overallfactor,ruleForExtraOp[[i]],SpecialRule[[i]],fac4SPR[[i]],rule0List1[[i]],basicpower,0],{i,1,Length[ruleForExtraOp]}];
pos4resultlist1=MapThread[Rule[#1,#2]&,{pos4resultlist1,r12},2];
pos4resultlist1=Dispatch[pos4resultlist1];
resultlist12=MapThread[ReplacePart[#1,#2]&,{resultlist12,pos4resultlist1}];
resultlist12=Total[resultlist12];
r=resultlist0+resultlist11+resultlist12//Expand;
r/.t^n_/;n>=2->0
]


fluxStructureC[f__]/;AnyTrue[Flatten[{f}],Abs[#]>1&]:=0
fluxStructureC[{alpha_,beta_},gamma_]:=fluxStructureC[{alpha,beta},gamma]=(-1)^gamma LeviCivitaTensor[3][[-gamma+2,alpha+2,beta+2]]
Do[fluxStructureC[{a,b},c],{a,-1,1},{b,-1,1},{c,-1,1}]
fluxStructureC[{alpha_,beta_,gamma_},phi_]:=Sum[fluxStructureC[{alpha,theta},phi]fluxStructureC[{beta,gamma},theta],{theta,-1,1}]
Do[fluxStructureC[{a,b,c},d],{a,-1,1},{b,-1,1},{c,-1,1},{d,-1,1}]

GetfluxComSpRule[P[v_,i_,fluxCom[indP[ith_,aa__],indP[jth_,bb__]]],value_]/;ith=!=jth:=Block[{allpssblt,rule,SCvalue},
allpssblt=Tuples[{-1,0,1},2];allpssblt=Cases[allpssblt,x_/;Total[x]==value&&DuplicateFreeQ[x] ] ;
allpssblt=TakeList[#,{1,1}]&/@allpssblt;
rule=Thread[Rule[{P[v,i,fluxCom[indP[ith,aa],indP[jth,bb]],ith ],P[v,i,fluxCom[indP[ith,aa],indP[jth,bb]],jth ]},#]]&/@allpssblt;
SCvalue=fluxStructureC[Flatten[#],value]&/@allpssblt;
{SCvalue,rule}
]
GetfluxComSpRule[P[v_,i_,fluxCom[indP[kth_,aa__],fluxCom[indP[ith_,bb__],indP[jth_,cc__]  ]]],value_]:=Block[{allpssblt,rule,SCvalue},
allpssblt=Tuples[{-1,0,1},3];allpssblt=Cases[allpssblt,x_/;Total[x]==value&&DuplicateFreeQ[x[[2;;3]]]&&x[[1]]=!=Total[x[[2;;3]] ]];
allpssblt=TakeList[#,{1,1,1}]&/@allpssblt;(*indP[ith,bb,__] and indP[jth,cc,__] recouple at first, then result recouple with indP[kth aa].*)
rule=Thread[Rule[{P[v,i,fluxCom[indP[kth,aa],fluxCom[indP[ith,bb],indP[jth,cc]  ]],kth],P[v,i,fluxCom[indP[kth,aa],fluxCom[indP[ith,bb],indP[jth,cc]  ]],ith],
P[v,i,fluxCom[indP[kth,aa],fluxCom[indP[ith,bb],indP[jth,cc]  ]],jth]},#]]&/@allpssblt;
SCvalue=fluxStructureC[Flatten[#],value]&/@allpssblt;
{SCvalue,rule}
]
