(* ::Package:: *)

(*op is a list*)
uniformWDinn[op_]:=Block[{ifconnected,edgedOp,graphop,indhAsvertex,distanceM,distance,ruleBydis,orderedVertex,orderededge,orderedOp,WDs,WDV,lenindP,indWDRule,result,indPs,extraindices},
(*for, saying, WD[__,a,b]inn[b,c]WD[__,c,d], the useful information is only the order of those tensors WD and inn and that if we trace the tensor*)
(*This is to extract such information*)
(*The problem is how two get the order of the tensor from the expression with indices.*)
(*For a tensor expressed B_{b c}A_{ab}, how can we get that this is (A B)_{ac}? order by RuleBydis is the solution*)
edgedOp=op/.{WD[v_,e_,z_,x_,y_]:>DirectedEdge[x,y],WDt[v_,e_,z_,x_,y_]:>DirectedEdge[x,y],inn[ij_,x_,y_]:>DirectedEdge[x,y]};
graphop=Graph[edgedOp];
ifconnected=ConnectedGraphQ[graphop];
indhAsvertex=VertexList[graphop];
distanceM=GraphDistanceMatrix[graphop];
distance=If[ifconnected,distanceM[[1]],DeleteCases[distanceM,x_/;MemberQ[x,Infinity]][[1]]];
ruleBydis=Thread[Rule[indhAsvertex,distance]];
orderedVertex=SortBy[indhAsvertex,#/.ruleBydis&];
orderededge=If[!ifconnected,DirectedEdge@@@Partition[orderedVertex,2,1],DirectedEdge@@@Partition[Append[orderedVertex,orderedVertex[[1]]],2,1]];
orderedOp=orderededge/.Thread[Rule[edgedOp,op]];
WDs=Cases[orderedOp,_WD|_WDt,Infinity];
WDs=SortBy[WDs,Position[orderedOp,#]&];
WDV=WDs/.{WD[v_,e_,indP[i_,{e_,len_},___],indh1_,indh2_]:>WD[indP[{len}],indh1,indh2],WD[__,fluxCom[__],indh1_,indh2_]:>WD[indP[{1}],indh1,indh2],
 WDt[v_,e_,indP[i_,{e_,len_},___],indh1_,indh2_]:>WDt[indP[{len}],indh1,indh2],WDt[__,fluxCom[__],indh1_,indh2_]:>WDt[indP[{1}],indh1,indh2]};
indWDRule=Thread[Rule[WDs,WDV]];
result=orderedOp/.indWDRule;
indPs=WDs[[All,3]];
extraindices=If[ifconnected,{indPs,{}},{indPs,{orderedVertex[[1]],orderedVertex[[-1]]}}];
{ifconnected,result[[All,{1}]],extraindices}
]


creatfacs[{TF_,ops_}]/;TF:=Block[{lenop,dummyind,dummy,allind,partedallind,fullops,WDs,orderedWDs,indPs,lenindP,indPV,ruleindP,dummyindV,ruledummyind,dummyruledOps,ruledOps,values},
lenop=Length[ops];
dummyind=Thread[dummy[Range[lenop]]];
allind=Insert[dummyind,dummy[1],-1];
partedallind=Partition[allind,2,1];
fullops=MapThread[Insert[#1,#2,-1]&,{ops,partedallind}];
fullops=fullops/.{inn[{i_,j_},{x_,y_}]:>inn[{i,j},x,y],WD[x_,{y_,z_}]:>WD[x,y,z],WDt[x_,{y_,z_}]:>WDt[x,y,z]};
WDs=Cases[fullops,_WD|_WDt,Infinity];
orderedWDs=MapIndexed[Insert[#1,First[#2],{1,1}]&,WDs];(*to order these indP[{i}] with the same i in WDs*)
fullops=fullops/.Thread[Rule[WDs,orderedWDs]];
indPs=Cases[fullops,_indP,Infinity];
(*Order of each term will be resorted after applying Times*)
fullops=Times@@fullops;
lenindP=indPs[[All,2,1]];
indPV=TakeList[#,lenindP]&/@Tuples[{-1,0,1},Total[lenindP]];
ruleindP=Thread/@Map[Rule[indPs,#]&,indPV];
dummyindV=Tuples[{-1/2,1/2},Length[dummyind]];
ruledummyind=Thread/@Map[Rule[dummyind,#]&,dummyindV];
dummyruledOps=fullops/.ruledummyind;
ruledOps=Map[(dummyruledOps/.#)&,ruleindP];
values=Total/@(ruledOps/.{WD[{indp_},wda_,wdb_]:>tau[indp,wda,wdb],WD[{indp1_,indp2_},wda_,wdb_]:>Sum[tau[indp1,wda,dummy]tau[indp2,dummy,wdb],{dummy,-1/2,1/2}],
WDt[{indp1_,indp2_},wda_,wdb_]:>Sum[tau[indp2,wda,dummy]tau[indp1,dummy,wdb],{dummy,-1/2,1/2}]});
Do[factorWDinn[ops,{indPs/.ruleindP[[i]],{}}]=values[[i]],{i,1,Length[ruleindP]}];]



creatfacs[{TF_,ops_}]/;!TF:=Block[{lenop,dummy,indh,dummyind,allind,partedallind,fullops,WDs,orderedWDs,indPs,lenindP,indPV,ruleindP,allrules,ruleholoind,dummyindV,ruledummyind,dummyruledOps,ruledOps,values},
lenop=Length[ops];
dummyind=Thread[dummy[Range[lenop-1]]];
allind=Insert[dummyind,indh[1],1];
allind=Insert[allind,indh[2],-1];
partedallind=Partition[allind,2,1];
fullops=MapThread[Insert[#1,#2,-1]&,{ops,partedallind}];
fullops=fullops/.{inn[{i_,j_},{x_,y_}]:>inn[{i,j},x,y],WD[x_,{y_,z_}]:>WD[x,y,z],WDt[x_,{y_,z_}]:>WDt[x,y,z]};
WDs=Cases[fullops,_WD|_WDt,Infinity];
orderedWDs=MapIndexed[Insert[#1,First[#2],{1,1}]&,WDs];(*to order these indP[{i}] with the same i in WDs*)
fullops=fullops/.Thread[Rule[WDs,orderedWDs]];
indPs=Cases[fullops,_indP,Infinity];
(*Order of each term will be resorted after applying Times*)
fullops=Times@@fullops;
lenindP=indPs[[All,2,1]];
indPV=TakeList[#,lenindP]&/@Tuples[{-1,0,1},Total[lenindP]];
ruleindP=Thread/@Map[Rule[indPs,#]&,indPV];
ruleholoind=Thread/@Map[Rule[{indh[1],indh[2]},#]&,Tuples[{-1/2,1/2},2]];
allrules=Flatten/@(Tuples[{ruleindP,ruleholoind}]);
dummyindV=Tuples[{-1/2,1/2},Length[dummyind]];
ruledummyind=Thread/@Map[Rule[dummyind,#]&,dummyindV];
dummyruledOps=fullops/.ruledummyind;
ruledOps=Map[(dummyruledOps/.#)&,allrules];
values=Total/@(ruledOps/.{WD[{indp_},wda_,wdb_]:>tau[indp,wda,wdb],WD[{indp1_,indp2_},wda_,wdb_]:>Sum[tau[indp1,wda,dummy]tau[indp2,dummy,wdb],{dummy,-1/2,1/2}],WDt[{indp1_,indp2_},wda_,wdb_]:>Sum[tau[indp2,wda,dummy]tau[indp1,dummy,wdb],{dummy,-1/2,1/2}]});
Do[factorWDinn[ops,{indPs,{indh[1],indh[2]}}/.allrules[[i]]]=values[[i]],{i,1,Length[allrules]}];]
