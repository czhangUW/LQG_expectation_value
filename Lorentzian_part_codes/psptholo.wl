(* ::Package:: *)

allspins[jlist_List,n_]:=Thread[ReplacePart[jlist,n->Last/@allspins[jlist[[{n-1,n}]]] ] ]
allspins[jlist_]/;Length[jlist]==2:=Table[{jlist[[1]],J},{J,Abs[jlist[[1]]-jlist[[2]]],jlist[[1]]+jlist[[2]]}]
allspins[jlist_]/;Length[jlist]>2:=Block[{jlist1},jlist1=allspins[jlist,2];Do[jlist1=Flatten[allspins[#,n]&/@jlist1,1],{n,3,Length[jlist]}];jlist1]


comhols[0,{},{}]=1;
comhols[J_,{},{}]/;J=!=0:=0;
comhols[1/2,{x_},{y_}]:=1
comhols[J_,x_,y_]:=comhols[J,x,y]=Block[{midspins,leftindx,rightindx,leftindy,rightindy,r},
midspins=Cases[allspins[ConstantArray[1/2,Length[x]]],{___,J}]; 
If[midspins=={},Return[0]];
leftindx=Table[Total[x[[1;;i]]],{i,1,Length[x]-1}];
rightindx=Table[-Total[x[[1;;i]]],{i,2,Length[x]}];
leftindy=Table[Total[y[[1;;i]]],{i,1,Length[y]-1}];
rightindy=Table[-Total[y[[1;;i]]],{i,2,Length[y]}];
r=Product[(-1)^(rightindx[[i]]-rightindy[[i]])(2 #[[i+1]]+1)ThreeJSymbol[{#[[i]],leftindx[[i]]},{1/2,x[[i+1]]},{#[[i+1]],rightindx[[i]]}]
ThreeJSymbol[{#[[i]],leftindy[[i]]},{1/2,y[[i+1]]},{#[[i+1]],rightindy[[i]]}],{i,1,Length[leftindx]}]&/@midspins;
Plus@@r
]
Do[comhols[J,{m1,m2},{n1,n2}],{J,0,1},{m1,-1/2,1/2},{m2,-1/2,1/2},{n1,-1/2,1/2},{n2,-1/2,1/2}]
Do[comhols[J,{m1,m2,m3},{n1,n2,n3}],{J,1/2,3/2},{m1,-1/2,1/2},{m2,-1/2,1/2},{m3,-1/2,1/2},{n1,-1/2,1/2},{n2,-1/2,1/2},{n3,-1/2,1/2}]
Do[comhols[J,{m1,m2,m3,m4},{n1,n2,n3,m4}],{J,0,2},{m1,-1/2,1/2},{m2,-1/2,1/2},{m3,-1/2,1/2},{m4,-1/2,1/2},{n1,-1/2,1/2},{n2,-1/2,1/2},{n3,-1/2,1/2},{n4,-1/2,1/2}]


(*To calculate ...p_s^\[Alpha](e)p_t^\[Beta](e))D^iota_{ab}(h_e)*)
psptholo[alpha_,beta_,iotae_,nt_,\[Eta]_,\[Xi]_]/;Total[alpha]+Total[beta]-iotae[[2]]+iotae[[3]]===0:=psptholo[alpha,beta,iotae,nt,\[Eta],\[Xi]]=Block[{n,factor,combineab,result},n=Length[beta];factor=(-1)^n Exp[-Total[beta] (\[Eta]-I \[Xi])];combineab=Join[Reverse[beta],alpha];
result=psh[combineab,iotae[[1]],iotae[[2]],iotae[[3]],nt,\[Eta],\[Xi]];
result factor
]
psptholo[alpha_,beta_,iotae_,nt_,\[Eta]_,\[Xi]_]/;Total[alpha]+Total[beta]-iotae[[2]]+iotae[[3]]=!=0:=0


hpspthJoin[x_,y_]:={{Cases[x[[1]],z_/;Abs[z]=!=1/2],Cases[y[[1]],z_/;Abs[z]=!=1/2]},x[[2]]+y[[2]],x[[3]] y[[3]]}


(*To reorder the indices of the ...p_s^\[Alpha](e)p_t^\[Beta](e))D^iota_{ab}(h_e)p_s^\[Alpha](e)p_t^\[Beta](e)).... Calculate the expected value*)
(*indl stores alpha and the indices a of the holonomy operaor*)
(*ncom is the times of doing commutator. It can be {n} or an integer. ncom=n: doing \[LessEqual]n times commutator.*)
(*An example of the the argument indl={0,0,-1/2,0,1/2};
indr={0,-1/2,1/2};*)
hpspth[indl_,indr_,nt_]/;Count[indl,x_/;Abs[x]===1/2]=!=0:=hpspth[indl,indr,nt]=
Block[{hl,hr,n12,reorderindl,indrp,reorderindr,reorderindall,fluxindAndfacAndorder,holoind,combholoind,addspin,J,spinAndfac,allindsAndfac,result},
n12=Count[indl,x_/;Abs[x]===1/2];
reorderindl=Nest[Flatten[Map[orderinds@@#&,#],1]&,{{indl,0,1,nt,1}},n12];
n12=Count[indr,x_/;Abs[x]===1/2];
indrp=ConstantArray[indr,Length[reorderindl]];
reorderindr=MapThread[Nest[Flatten[Map[orderinds@@#&,#],1]&,{{#1,0,1,nt-#2[[2]],-1}},n12]&,{indrp,reorderindl}];
reorderindall=Tuples/@(MapThread[{{#1},#2}&,{reorderindl,reorderindr}]);
reorderindall=Flatten[reorderindall,1];
fluxindAndfacAndorder=hpspthJoin@@@reorderindall;
holoind=Map[Cases[#,x_/;Abs[x]==1/2]&,reorderindall[[All,All,1]],{2}];
combholoind=Map[Total,holoind,{2}];
addspin=Function[u,Prepend[u,#]&/@Table[n12/2-i,{i,0,n12/2}]]/@holoind;
spinAndfac=DeleteCases[#,{0,_}]&/@Map[{comhols@@#,#[[1]]}&,addspin,{2}];
allindsAndfac=Tuples/@(MapThread[{{#1},#2,{#3}}&,{fluxindAndfacAndorder,spinAndfac,combholoind}]);
allindsAndfac=Flatten[#,2]&/@Flatten[allindsAndfac,1];
result=Times[#[[4]],#[[5]],psptholo[#[[1]],#[[2]],#[[6;;8]],nt-#[[3]],\[Eta],\[Xi]],(-I t)^#[[3]]]&/@allindsAndfac;
result=Total[result]//Expand//Simplify
]
hpspth[indl_,indr_,nt_]/;Count[indl,x_/;Abs[x]===1/2]===0:=hpspth[indl,indr,nt]=psptholo[indl,indr,{0,0,0},nt,\[Eta],\[Xi]]


(*By using the commutator of p_s/p_t and holonomy to re-order the indices at the source/target point*)
(*if nt is a number, the function returns results by doing n\[LessEqual]nt times commutator*)
(*sgn=-1 corresponding to p_t-case and sgn=1 corresponding to p_s-case*)
orderinds[inds_,orderin_,factorin_,nt_,sgn_]/;MemberQ[NestWhile[Most,inds,#=!={}&&Abs[Last[#]]===1/2&],x_/;Abs[x]===1/2]&&sgn==1:=
Block[{indp,lasthalf,aorb,pos,subinds,allsubsubinds,purefluxind,tauind,indleft,dummyind,Tleft,ltau,rtau,holoind,factorout,ordertout,ordercurrent,indordered},
indp=NestWhile[Most,inds,#=!={}&&Abs[Last[#]]===1/2&];
lasthalf=Take[inds,Length[indp]-Length[inds]];
aorb=Last@Cases[indp,x_/;Abs[x]===1/2];
pos=Last@Position[indp,x_/;Abs[x]===1/2,{1},Heads->False];
subinds=Range[Length[indp]]//Drop[#,pos[[1]]]&;
allsubsubinds=Subsets[subinds,nt-orderin];
purefluxind=Range[Length[indp]]//Drop[#,pos]&;
tauind=indp[[#]]&/@allsubsubinds;
indleft=indp[[Complement[purefluxind,#]]]&/@allsubsubinds;
dummyind=Map[Table[aorb- Total[#[[1;;i]]],{i,1,Length[#]}]&,tauind];
Tleft=Position[dummyind,x_/;!MemberQ[x,y_/;Abs[y]>1/2],{1},Heads->False]//Flatten;
tauind=tauind[[Tleft]];
dummyind=dummyind[[Tleft]];
ltau=MapAt[Join[{aorb},Most[#]]&,dummyind,Position[dummyind,x_/;x=!={},{1},Heads->False]];
rtau=dummyind;
holoind=Map[If[#==={},Prepend[lasthalf,aorb],Prepend[lasthalf,Last[#]] ]&,dummyind];
ordercurrent=Map[Length[#]&,tauind];
ordertout=ordercurrent+orderin;
factorout=MapThread[Times@@MapThread[tau[#1,#2,#3]&,{#1,#2,#3}]&,{tauind,ltau,rtau}];
factorout=factorout factorin;
indordered=Join[indleft[[Tleft]],holoind,2];
{indordered,ordertout,factorout,ConstantArray[nt,Length[Tleft]],ConstantArray[sgn,Length[Tleft]]}//Transpose
]


orderinds[inds_,orderin_,factorin_,nt_,sgn_]/;MemberQ[NestWhile[Most,inds,#=!={}&&Abs[Last[#]]===1/2&],x_/;Abs[x]===1/2]&&sgn==-1:=
Block[{indp,lasthalf,aorb,pos,subinds,allsubsubinds,purefluxind,tauind,indleft,dummyind,Tleft,ltau,rtau,holoind,factorout,ordertout,ordercurrent,indordered},
indp=NestWhile[Most,inds,#=!={}&&Abs[Last[#]]===1/2&];
lasthalf=Take[inds,Length[indp]-Length[inds]];
aorb=Last@Cases[indp,x_/;Abs[x]===1/2];
pos=Last@Position[indp,x_/;Abs[x]===1/2,{1},Heads->False];
subinds=Range[Length[indp]]//Drop[#,pos[[1]]]&;
allsubsubinds=Subsets[subinds,nt-orderin];
purefluxind=Range[Length[indp]]//Drop[#,pos]&;
tauind=Reverse[indp[[#]]]&/@allsubsubinds;
indleft=indp[[Complement[purefluxind,#]]]&/@allsubsubinds;
dummyind=Map[Table[aorb+ Total[#[[i;;Length[#]]]],{i,1,Length[#]}]&,tauind];
Tleft=Position[dummyind,x_/;!MemberQ[x,y_/;Abs[y]>1/2],{1},Heads->False]//Flatten;
tauind=tauind[[Tleft]];
dummyind=dummyind[[Tleft]];
ltau=dummyind;
rtau=MapAt[Join[Rest[#],{aorb}]&,dummyind,Position[dummyind,x_/;x=!={},{1},Heads->False]];
holoind=Map[If[#==={},Prepend[lasthalf,aorb],Prepend[lasthalf,First[#]] ]&,dummyind];
ordercurrent=Map[Length[#]&,tauind];
ordertout=ordercurrent+orderin;
factorout=MapThread[Times@@MapThread[-tau[#1,#2,#3]&,{#1,#2,#3}]&,{tauind,ltau,rtau}];
factorout=factorout factorin;
indordered=Join[indleft[[Tleft]],holoind,2];
{indordered,ordertout,factorout,ConstantArray[nt,Length[Tleft]],ConstantArray[sgn,Length[Tleft]]}//Transpose
]
