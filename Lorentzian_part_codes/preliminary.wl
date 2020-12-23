(* ::Package:: *)

Off[ClebschGordan::phy]
Do[tau[\[Alpha],m,n]=I Sqrt[3/2] (-1)^(1/2+m) ThreeJSymbol[{1/2,-m},{1/2,n},{1,\[Alpha]}],{\[Alpha],-1,1},{m,-1/2,1/2},{n,-1/2,1/2} ]
tau[\[Alpha]_,m_,n_]/;Abs[m]>=1/2||Abs[n]>=1/2:=0


Get["operator.wl"]
Get["expandNCM.wl"]
Get["simplifyoperator.wl"]
Get["DealWithInds.wl"]
Get["psh.wl"]
Get["psh0.wl"]
Get["psptholo.wl"]
Get["hpspthValue.mx"]
Get["evaluatefacind.wl"]
Get["distIndToE.wl"]
Get["expectedDecouple.wl"]
Get["factorValue.wl"]
Get["simplifyfactor.wl"]
Get["expectedWithoutOne.wl"]
Get["expectedWithAnOne.wl"]
Get["expectedvalueoneterm.wl"]
Get["edgesymmetry.wl"]
Get["expectedvalueextra.wl"]



nx[j_, m_, n_] :=nx[j,m,n]= WignerD[{j, m, n}, 0, -(\[Pi]/2), 0]
inx[j_, m_, n_] :=inx[j,m,n]= WignerD[{j, m, n}, 0, \[Pi]/2, 0]
ny[j_, m_, n_] :=ny[j,m,n]= WignerD[{j, m, n}, -\[Pi]/2, -\[Pi]/2, \[Pi]/2]
iny[j_, m_, n_] :=iny[j,m,n]= WignerD[{j, m, n}, -\[Pi]/2, \[Pi]/2, \[Pi]/2]
(*Here this epsilon is epsilon_{ijk}dx^i dx^j dx^k=-I epsilon_{abc}dx^a dx^b dx^c where x^a/b/c is the spherical coordinate*)
epsilon[a_, b_, c_] /;a + b + c == 0 := epsilon[a, b, c]=-I Sqrt[6] ThreeJSymbol[{1, a}, {1, b}, {1, c}]
epsilon[a_, b_, c_] /; a + b + c != 0 :=epsilon[a,b,c]= 0
Do[nb[1,m,n] = nx[1/2, m, n], {m, -1/2, 1/2}, {n, -(1/2), 1/2}];
Do[nb[2,m,n] = ny[1/2, m, n], {m, -1/2, 1/2}, {n, -(1/2), 1/2}];
Do[inb[1,m,n] = inx[1/2, m, n], {m, -1/2, 1/2}, {n, -(1/2), 1/2}];
Do[inb[2,m,n] = iny[1/2, m, n], {m, -1/2, 1/2}, {n, -(1/2), 1/2}];
Do[nb[3,m,n]=KroneckerDelta[m,n], {m, -1/2, 1/2}, {n, -(1/2), 1/2}];
Do[inb[3,m,n]=KroneckerDelta[m,n], {m, -1/2, 1/2}, {n, -(1/2), 1/2}];


inn[{i_Integer,j_Integer},a:1/2|-1/2,b:1/2|-1/2]:=inn[{i,j},a,b]=Sum[inb[i,a,c]nb[j,c,b],{c,-1/2,1/2}]
Do[inn[{i,j},a,b],{i,1,3},{j,1,3},{a,-1/2,1/2},{b,-1/2,1/2}]


aQfactor[alpha_,beta_,gamma_]:=aQfactor[alpha,beta,gamma]=Block[{n,indb,alphapbetap,alphapbetapgamma,epapbpg,dnxny},
indb={-1,0,1};
alphapbetapgamma=Tuples[{indb,indb,{gamma}}]//DeleteCases[#,x_/;!DuplicateFreeQ[x]]&;
epapbpg=Map[epsilon@@#&,alphapbetapgamma];
alphapbetap=alphapbetapgamma[[All,1;;2]];
dnxny=Map[inx[1,alpha,#[[1]]]iny[1,beta,#[[2]]]&,alphapbetap];
Total[MapThread[Times@@Times[#1 #2]&,{epapbpg,dnxny}]]
(*The last line is equivalent Total[Times[epapbpg,dnxny]]*)
]
Do[aQfactor[a,b,c],{a,-1,1},{b,-1,1},{c,-1,1}]
Qfactor[alpha_List,beta_List,gamma_List]:=Qfactor[alpha,beta,gamma]=Times@@MapThread[aQfactor[#1,#2,#3]&,{alpha,beta,gamma}]
judgevanishfactor[abg_]:=Block[{reshapeabg,n},n=Length[abg]/3;reshapeabg={abg[[1;;n]],
    abg[[n+1;;2n]],abg[[2n+1;;3n]]};MemberQ[Total[reshapeabg^2],1]]
(*judgevanishfactor[abg_] is used to judge if factor[{\[Alpha],\[Beta],\[Gamma]}] is 0. We use the fact that
 factor[{a,b,c}]\[Equal]0 iff a^2+b^2+c^2\[Equal]1*)


vs2edge[v_, i_, s_] := 
 Block[{direction}, direction = {0, 0, 0}; direction[[i]] = s; 
  DirectedEdge[v[[1]], v[[1]] + direction]]


judgelenindP[decoupleOperator_,rule0_]:=Block[{Ps,len},
Ps=Cases[decoupleOperator,_P,Infinity];
len=Ps/.{P[__,indP[___,{_,x_}]]:>(x/.rule0),P[__,fluxCom[__]]:>1};
AnyTrue[len,#<0&]]


(*Prepare hpspthValue.mx to store the results of hpspth[__,1] in which there are one 1 index or one -1 index.*)
(*Off[ClebschGordan::phy]
allinds4hpspth=Block[{fluxind,holoind,fluxAndholoind},fluxind={{},{1},{-1},{1,-1},{1,1},{-1,-1}};
holoind=Sort/@Tuples[{-1/2,1/2},#]//DeleteDuplicates;
fluxAndholoind=Flatten/@Tuples[{fluxind,holoind}];
fluxAndholoind=Permutations/@fluxAndholoind//Flatten[#,1]&;
fluxAndholoind=Tuples[fluxAndholoind,2];
fluxAndholoind=DeleteCases[fluxAndholoind,x_/;Count[x,z_/;Abs[z]==1,{2}]>2]
]&/@{0,1,2,3,4};
allinds4hpspth=Flatten[allinds4hpspth,1];
Map[ hpspth[#[[1]],#[[2]],1]&,allinds4hpspth];
DumpSave["hpspthValue.mx",hpspth];*)


ToorienteEdges[{{v1_,v2_},{i1_,si1_,j1_,sj1_,k1_,sk1_},{v3_,v4_},{i2_,si2_,j2_,sj2_,k2_,sk2_}}]:=LeviCivitaTensor[3][[i1,j1,k1]]si1 sj1 sk1 LeviCivitaTensor[3][[i2,j2,k2]]si2 sj2 sk2


Do[factorWDinnExtra[0,sgn,{{alpha},{a,b,c,d}}]=inn[{1,2},a,b]Sum[inn[{2,3},c,ee]tau[alpha,ee,ff]inn[{3,1},ff,d],{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn inn[{2,1},c,d]Sum[inn[{1,3},a,ee]tau[alpha,ee,ff]inn[{3,2},ff,b],{ee,-1/2,1/2},{ff,-1/2,1/2}],{sgn,-1,1},{alpha,-1,1},{a,-1/2,1/2},{b,-1/2,1/2},{c,-1/2,1/2},{d,-1/2,1/2}]
(**)
Do[factorWDinnExtra[1,sgn,{{alpha,beta},{a,b,c,d}}]=Sum[inn[{1,2},a,bb]tau[alpha,bb,b]inn[{2,3},c,cc]tau[beta,cc,dd]inn[{3,1},dd,d],{bb,-1/2,1/2},{cc,-1/2,1/2},{dd,-1/2,1/2}]+
sgn Sum[inn[{1,3},a,aa]tau[beta,aa,bb]inn[{3,2},bb,cc]tau[alpha,cc,b]inn[{2,1},c,d],{aa,-1/2,1/2},{bb,-1/2,1/2},{cc,-1/2,1/2}],{a,-1/2,1/2},{b,-1/2,1/2},{c,-1/2,1/2},{d,-1/2,1/2},{alpha,-1,1},
{beta,-1,1},{sgn,-1,1}]
(**)
Do[factorWDinnExtra[2,sgn,{{alpha,beta},{a,b,c,d}}]=Sum[inn[{1,2},a,b]inn[{2,3},c,cc]tau[alpha,cc,dd]inn[{3,1},dd,ee]tau[beta,ee,d],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2}]+
sgn Sum[inn[{1,3},a,aa]tau[alpha,aa,bb]inn[{3,2},bb,b]inn[{2,1},c,cc]tau[beta,cc,d],{aa,-1/2,1/2},{bb,-1/2,1/2},{cc,-1/2,1/2}],{a,-1/2,1/2},{b,-1/2,1/2},{c,-1/2,1/2},{d,-1/2,1/2},{alpha,-1,1},
{beta,-1,1},{sgn,-1,1}]
(**)
Do[factorWDinnExtra[3,sgn,{{alpha,beta},{a,b}}]=Sum[inn[{1,2},a,cc]tau[alpha,cc,dd]inn[{2,3},dd,ee]tau[beta,ee,ff]inn[{3,1},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn Sum[inn[{1,3},a,cc]tau[beta,cc,dd]inn[{3,2},dd,ee]tau[alpha,ee,ff]inn[{2,1},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}],
 {sgn,-1,1},{alpha,-1,1},{beta,-1,1},{a,-1/2,1/2},{b,-1/2,1/2}]
Do[factorWDinnExtra[3,sgn,{{alpha,gamma,beta},{a,b}}]=Sum[inn[{1,2},a,cc]tau[alpha,cc,ddp]tau[gamma,ddp,dd]inn[{2,3},dd,ee]tau[beta,ee,ff]inn[{3,1},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},
{ddp,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn Sum[inn[{1,3},a,cc]tau[beta,cc,dd]inn[{3,2},dd,ee]tau[alpha,ee,ffp]tau[gamma,ffp,ff]inn[{2,1},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2},{ffp,-1/2,1/2}],
 {sgn,-1,1},{alpha,-1,1},{gamma,-1,1},{beta,-1,1},{a,-1/2,1/2},{b,-1/2,1/2}]
(**)
Do[factorWDinnExtra[4,sgn,{{alpha,beta},{a,b}}]=Sum[inn[{2,3},a,cc]tau[alpha,cc,dd]inn[{3,1},dd,ee]tau[beta,ee,ff]inn[{1,2},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn Sum[inn[{2,1},a,cc]tau[beta,cc,dd]inn[{1,3},dd,ee]tau[alpha,ee,ff]inn[{3,2},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}],
{sgn,-1,1},{alpha,-1,1},{beta,-1,1},{a,-1/2,1/2},{b,-1/2,1/2}]
Do[factorWDinnExtra[4,sgn,{{alpha,gamma,beta},{a,b}}]=Sum[inn[{2,3},a,cc]tau[alpha,cc,ddp]tau[gamma,ddp,dd]inn[{3,1},dd,ee]tau[beta,ee,ff]inn[{1,2},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},
{ddp,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn Sum[inn[{2,1},a,cc]tau[beta,cc,dd]inn[{1,3},dd,ee]tau[alpha,ee,ffp]tau[gamma,ffp,ff]inn[{3,2},ff,b],{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2},{ffp,-1/2,1/2}],
{sgn,-1,1},{alpha,-1,1},{gamma,-1,1},{beta,-1,1},{a,-1/2,1/2},{b,-1/2,1/2}]
(**)
Do[factorWDinnExtra[5,sgn,{{alpha,beta,gamma},{a,b}}]=Sum[inn[{2,3},a,bb]tau[alpha,bb,cc]inn[{3,1},cc,dd]tau[beta,dd,ee]inn[{1,2},ee,ff]tau[gamma,ff,b],{aa,-1/2,1/2},{bb,-1/2,1/2},{cc,-1/2,1/2},
{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn Sum[inn[{2,1},a,bb]tau[beta,bb,cc]inn[{1,3},cc,dd]tau[alpha,dd,ee]inn[{3,2},ee,ff]tau[gamma,ff,b],{bb,-1/2,1/2},{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}],
{a,-1/2,1/2},{b,-1/2,1/2},{alpha,-1,1},{beta,-1,1},{gamma,-1,1},{sgn,-1,1}]
(**)
Do[factorWDinnExtra[6,sgn,{{alpha,beta,gamma},{a,b}}]=Sum[inn[{1,2},a,bb]tau[alpha,bb,cc]inn[{2,3},cc,dd]tau[beta,dd,ee]inn[{3,1},ee,ff]tau[gamma,ff,b],{aa,-1/2,1/2},{bb,-1/2,1/2},{cc,-1/2,1/2},
{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}]+
sgn Sum[inn[{1,3},a,bb]tau[beta,bb,cc]inn[{3,2},cc,dd]tau[alpha,dd,ee]inn[{2,1},ee,ff]tau[gamma,ff,b],{bb,-1/2,1/2},{cc,-1/2,1/2},{dd,-1/2,1/2},{ee,-1/2,1/2},{ff,-1/2,1/2}],
{a,-1/2,1/2},{b,-1/2,1/2},{alpha,-1,1},{beta,-1,1},{gamma,-1,1},{sgn,-1,1}]
