(* ::Package:: *)

orderWD[{x__}]:=Block[{indPs,pos,posInd},
indPs=Cases[{x},_indP,Infinity]//DeleteDuplicates;
pos=Position[{x},#,Infinity]&/@indPs;
posInd=MapIndexed[{#1,First[#2]}&,#]&/@pos;
posInd=Flatten[posInd,1];
Fold[Function[{w,u},MapAt[Append[#,u[[2]]]&,w,u[[1]]]],{x},posInd]
]
(*orderWD[{x__P}]:={x}*)


(*some indP[__] may appear twice in all of the WDs. We ordered those indP[] to distinguish them*)
orderWDindP[WDs_]:=Block[{gatherWD},
gatherWD=GatherBy[WDs,List@@#[[1;;2]]&];
gatherWD=Map[GatherBy[#,#[[3,0]]&]&,gatherWD];
gatherWD=Map[GatherBy[#,#[[3,1]]&]&,gatherWD,{2}];(*in WD[v,i,fluxCom[x,__]], x must be different for various WDs of this kinds*)
gatherWD=Flatten[gatherWD,2];
gatherWD=Map[orderWD,gatherWD];
Flatten[gatherWD]
]


(*partition of list to be {list1,list2} such that Length[list1]=n and the ordering of elements in list1 and list2 are the same as that in list*)
myPartition[{list0___,list_},{n_}]:=Block[{sublist,partitionlist},
sublist=Subsets[list,{n}];
partitionlist=NestList[Complement[list,#]&,#,1]&/@sublist;
Function[u,Fold[Prepend,u,Reverse[{list0}]]]/@partitionlist
]


(*For instance, x={{f1,f3,f5,f7},{f3,f2},{f1}}. We want to find all possible combinatin of {0,1,0,1}, {xx,yy},{zz} such that in each of them *)
(*the order of fi and fj, which are in the same sublist of x, saying f1, f7, are kept as theirs in the sublist. *)
(*in other words, we want to find the origional list xo, which contains those fi, such that xo can be parted into a sublist of x*)
AllIndPVinQ[x_]:=Block[{lx,alllist,ablist,f,partitionN,r1},
lx=Length[x//Flatten];
ablist=f/@Range[lx];
partitionN=Length/@x;
alllist=Fold[Function[{u,v},Flatten[myPartition[#,{v}]&/@u,1]],{{ablist}},partitionN](*partitions of ablist which have the same shape as x*);
alllist=DeleteCases[alllist,{},Infinity];
r1=(ablist/.(Thread/@Thread[Rule[#,x]]//Flatten))&/@alllist(*the partition must the same as x so that we can reconstruct the origional list*)]


indPruleInWD[QfactorTitle_,indPsValue_,fac_:1]:=Block[{indPs,leneachindP,abind,ablist,abrule,indPsabValue,abindV,abindRule,indVinQfactor,resultOfQfactor0,resultOfQfactor,indPruleValue,Qfactorrule,result},
indPs=Cases[indPsValue,_indP,Infinity];
leneachindP=#[[2,2]]&/@indPs;
ablist=TakeList[abind/@Range[Total[leneachindP]],leneachindP];
abrule=Thread[Rule[indPs,ablist]];(*Here is the rule of indPs in WD given with abind[i]*)
indPsabValue=indPsValue/.abrule;
indPsabValue=AllIndPVinQ/@indPsabValue;
indPsabValue=Tuples[indPsabValue];(*Here we get the indices in Qfactor with abstract indices*)
abindV=Tuples[{-1,0,1},Total[leneachindP]];
abindRule=Thread[Rule[ablist//Flatten,#]]&/@abindV;
abindRule=Dispatch[abindRule];
indVinQfactor=indPsabValue/.abindRule;
resultOfQfactor0=Plus@@@Apply[Qfactor,indVinQfactor,{2}];
resultOfQfactor=DeleteCases[resultOfQfactor0,0,{1},Heads->False];
resultOfQfactor=fac resultOfQfactor;
If[resultOfQfactor=={},Return[{}]];
abindRule=Delete[abindRule,Position[resultOfQfactor0,0,{1},Heads->False]];
indPruleValue=abrule/.abindRule;
Qfactorrule=List/@Thread[Rule[QfactorTitle,resultOfQfactor]];
result=Flatten/@({indPruleValue,Qfactorrule}//Transpose)]


(*ruleFromWD[WD[v_,i_,alpha_,lind:Except[_indh|_indhp],rind:_indh|_indhp]]:={Rule[rind,-Total[alpha]+lind]}
ruleFromWD[WD[v_,i_,alpha_,lind:_indh|_indhp,rind:Except[_indh|_indhp]]]:={Rule[lind,Total[alpha]+rind]}
ruleFromWD[WD[v_,i_,alpha_,lind:_indh|_indhp,rind:_indh|_indhp]]:=
Which[Total[alpha]===0,{{Rule[lind,1/2],Rule[rind,1/2]},{Rule[lind,-1/2],Rule[rind,-1/2]}},
Total[alpha]===1,{{Rule[lind,1/2],Rule[rind,-1/2]}},Total[alpha]===-1,{{Rule[lind,-1/2],Rule[rind,1/2]}},Abs[Total[alpha]]>1,{{Rule[lind,3/2],Rule[rind,3/2]}}]*)


(*creat the Special rule for firther calculation*)
(*ruleindP1 is the rule for computing the expectation value*)
(*fac4SPRFinal and specialruleFinal are for factor value*)
(*Because of P[__,fluxcom[]], each special rule is a combination of that from operatorLeft and operatorExtra*)
(*For each ruleindP1, there correspond to several special rules as well as fac4SPR*)
creatSpecialRule[operatorExtra_,operatorLeft_,rule0list_]:=Block[{PsExtra,indP1,
lenindP,ruleindPv,ruleindP1,special1,fac4SPR,specialrules,specialPsLeft,fac4SPRLeft,specialrulesLeft,specialruleFinal,fac4SPRFinal},
(*level 1: various rule for operatorExtra*)
(*level 2: various special rules*)
PsExtra=Cases[operatorExtra,_P];
indP1=PsExtra[[All,3]];
(*the cases of indP1 are: {indP[_,{_,1}]},{indP[_,{_,1}],indP[_,{_,1}]},{indP[_,{_,2}]}*)
lenindP=Total[DeleteDuplicates[(indP1/.fluxCom[__]:>1)/.indP[___,{_,l_}]:>l]];
ruleindPv=Tuples[{-1,1},lenindP];
ruleindPv=Tuples[ruleindPv,Length[indP1]];
ruleindPv=DeleteCases[ruleindPv,{xx_,xx_}|{{xx_,xx_}}];
ruleindP1=Thread/@Map[Rule[indP1,#]&,ruleindPv];(*The rule to replace the flux indices for operatorExtra*)
(*We will use Join[operatorExtra,operatorLeft] for computing the factor which is the same as we use the origional decouple operator*)
special1=Thread/@Map[Rule[PsExtra,#]&,ruleindPv];
{fac4SPR,specialrules}=Transpose[Transpose/@Map[basicSpecialRule,special1,{2}]];
fac4SPR=Tuples/@fac4SPR;
fac4SPR=Apply[Times,fac4SPR,{2}];
specialrules=Map[Flatten,Tuples/@specialrules,{2}];
(*****Special rule for operator left****)
specialPsLeft=Cases[operatorLeft,P[__,fluxCom[__]],Infinity];
{fac4SPRLeft,specialrulesLeft}=If[specialPsLeft=={},{{{}},{{}}},Transpose[Transpose/@{GetfluxComSpRule[#,0]&/@specialPsLeft}]];
fac4SPRLeft=Apply[Times,Tuples/@fac4SPRLeft,{2}];  
specialrulesLeft=Map[Flatten,Tuples/@specialrulesLeft,{2}];
specialruleFinal=Map[Flatten,Tuples/@Tuples[{specialrules,specialrulesLeft}],{2}];
fac4SPRFinal=Apply[Times,Tuples/@Tuples[{fac4SPR,fac4SPRLeft}],{2}];
{ruleindP1,fac4SPRFinal,specialruleFinal}
]
basicSpecialRule[P[v_,i_,y:indP[__]]->values_]:={{1},{P[v,i,y]->values}}
basicSpecialRule[(h:P[v_,i_,fluxCom[__]])->values_]:=GetfluxComSpRule[h,values[[1]]]


(*To get the replacement rule for holonomy indices when all flux indices vanish. The argument holoops0_List is of holonomies along the same edge*)
getHoloindrule[holoops0_List]:=Block[{holol,holor,commonholoind,
postosortedge,holoops,hololForjudge,holorForjudge,holoV,holorulel,holoruler,holorulecom,allrules,
gatherbytitle},
holol=holoops0[[All,2]];
holor=holoops0[[All,3]];
commonholoind=Intersection[holol,holor];
(*this is to deal with the case saying D_{ab}(h_e)D_{bc}(h_e), where b is assigned with values only once*)
(*otherwise, b will be assigned with some value once by holol and the other time by holor*)
holol=Complement[holol,commonholoind];
holor=Complement[holor,commonholoind];
postosortedge=Position[holoops0,x_/;x[[1]]=!=Sort[x[[1]]],{1},Heads->False];
holoops=MapAt[ReplacePart[#,{2->-#[[3]],3->-#[[2]]}]&,holoops0,postosortedge];
hololForjudge=holoops[[All,2]];
holorForjudge=holoops[[All,3]];
holoV=Tuples[{-1/2,1/2},Length[holol]];
holorulel=Thread/@Map[Rule[holol,#]&,holoV];
holoruler=Thread/@Map[Rule[holor,#]&,holoV];
holoV=Tuples[{-1/2,1/2},Length[commonholoind]];
holorulecom=Thread/@Map[Rule[commonholoind,#]&,holoV];
allrules=Flatten/@Tuples[{holorulel,holoruler,holorulecom}];
allrules=DeleteCases[allrules,x_/;((Total[hololForjudge]-Total[holorForjudge]/.x)!=0)]
] 
