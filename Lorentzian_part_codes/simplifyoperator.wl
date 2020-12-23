(* ::Package:: *)

(*extract the operator whose indices will be set as +1/-1 and get the operator left at the same time*)
(*once P[__,fluxCom[__]] appears in anextraOp, we only need to delete this operator from decoupulOperator to get the operator left*)
(*this is because fluxCom[__] is a index set with length 1, and P[__,fluxCom[__]] can appear in anextraOp only once*)
(*the later assumption is guaranteed by the code to prepare anextraOp*)
seperateOps[decoupleOperator_,anextraOp_]:=Block[{listEO,operatorLeft,Ps,PsDeteDup,NumPs,NPs,NPs1,rule,rule1,Nextra},
listEO=(anextraOp/.NonCommutativeMultiply->List)//Flatten;
operatorLeft=DeleteCases[decoupleOperator,x_holonomy/;MemberQ[listEO,x],{2}];
operatorLeft=DeleteCases[operatorLeft,(x:P[__,fluxCom[__]])/;MemberQ[listEO,x],{2}];
Ps=Cases[listEO,P[__,indP[__]]];
PsDeteDup=DeleteDuplicates[Ps];
NumPs=Count[Ps,#]&/@PsDeteDup;
NPs=MapThread[ReplacePart[#,{3,2,2}->#[[3,2,2]]-#2]&,{PsDeteDup,NumPs}];
NPs1=MapThread[ReplacePart[#,{3,2,2}->#2]&,{PsDeteDup,NumPs}];
rule=Thread[Rule[PsDeteDup,NPs]];
rule1=Thread[Rule[PsDeteDup,NPs1]];
operatorLeft=operatorLeft/.rule;
Nextra=anextraOp/.rule1;
Nextra=Nextra//DeleteDuplicates;
Nextra=ReplacePart[Nextra,1->DeleteDuplicates[Nextra[[1]]]];
{operatorLeft,Nextra}
]


(*an edge associtaing with the operator*)
edgeHP[x_holonomy]:=Sort[x[[1]]]
edgeHP[x_P]:=Sort[vs2edge[x[[1]],x[[2]],-1]]


(*to decouple operators so that the operators on various sbuset commutates*)
ToDecoupleOps[operator_]:=Block[{edgeList,connectinglist,conectingrules,decoupleOperator},
edgeList=List@@operator/.{holonomy[e_,__]:>{e},P[v_,i_,__]:>{Sort[vs2edge[v,i,-1]],vs2edge[v,i,1]}};
connectinglist=ConnectedComponents[Graph[Apply[UndirectedEdge,Partition[#,2,1]&/@edgeList,{2}]//Flatten]];
conectingrules=Thread/@Thread[Rule[connectinglist,Range[Length[connectinglist]]]]//Flatten;
decoupleOperator=(NonCommutativeMultiply@@@GatherBy[List@@operator,edgeHP[#]/.conectingrules&])]
