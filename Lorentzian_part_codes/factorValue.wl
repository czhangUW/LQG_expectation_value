(* ::Package:: *)

(*Calculate the factor for the case when all flux indices are 0. Get the rule to evaluate the holonomy indices at the same time*)
(*indP in Qfactor is the total set and the indP in P[__] and WD[] are partition of the total set.*)
(*For each Qfactor, we need to find all P[__] and WD[__] belong it by using the function assignvalue.*)
(*specicalindPrule={{P[vertex[{1,0,0}],1,indP[2,{1,2 m[2]}]]\[Rule]{{0,0},{-1,0},{1}}},{...}}. Specially, if there is no special rule, it should be {{}}*)
(*so that the data structure are the same*)
(*where the order of elements inside each {__} are preserved when we do permutation for the elements*)
factorValue[decoupleOperator_,overallfactor_,rule0_,specialindPrule_,fac4SPR_]:=
Block[{POps,ForIndPsInWd,indPsInWD,AllQfactors,gatherPindPWD,indPsValue,indPWDQfactorrule0,indPWDQfactorrule,Qfactorrule,indPWDrule,indPruledfactor},
POps=Cases[decoupleOperator,_P,Infinity];
ForIndPsInWd=Cases[overallfactor,_factorWDinn,Infinity];
indPsInWD=Cases[ForIndPsInWd[[All,2,1]],_indP,Infinity];
AllQfactors=Cases[overallfactor,_Qfactor];
gatherPindPWD=collectPindP[#,indPsInWD,POps]&/@AllQfactors;
gatherPindPWD=MapThread[#1/.P[x__,fluxCom[y__]]:>P[x,fluxCom[y],assignvalue[First[#2]][[1,1]]]&,{gatherPindPWD,AllQfactors}];
(*This is step is because of the exitense of P[__,fluxCom[indP[i,__],indP[j,__]]]*)
indPsValue=(gatherPindPWD/.specialindPrule)/.{P[v_,i_,indP[j_,{k_,len_}],___]:>ConstantArray[0,len/.rule0]};
indPsValue=DeleteCases[indPsValue,{},Infinity];
(*evaluate the indPs in WD[__]*)
AllQfactors=ConstantArray[AllQfactors,Length[fac4SPR]];
indPWDQfactorrule0=MapThread[Function[{u,v,w},MapThread[indPruleInWD[#1,#2,u]&,{v,w}] ],{fac4SPR,AllQfactors,indPsValue}];
(*Here, it is because of the special rule which makes indPsValue like {{__}_a,{__}_b,...}. *)
(*Each {__}_a corresponds to a special rule and stores the data wrt all Qfactors*)
(*indPruleInWD should be indPruleInWD[one Qfactor, indPsValue wrt this Qfactor,fac4SPR of a spcecial rule ]*)
(*The result is the following, {{}_1,{}_2,...}. In each {}_i are the data for each special rule*)
(*For each {}_i, it looks like {{{},{},{}}_11,{{},{},{}}_22,...}_i*)
(*{{},{},{}}_1i are {all possibilities for Qfactori}_1i*)
indPWDQfactorrule0=DeleteCases[indPWDQfactorrule0,xx_/;xx=={}||MemberQ[xx,{}]];
If[indPWDQfactorrule0=={},Return[0]];
indPWDQfactorrule=Flatten[Map[Flatten,Tuples/@indPWDQfactorrule0,{2}],1];
indPWDQfactorrule=Dispatch[indPWDQfactorrule];
indPruledfactor=overallfactor/.indPWDQfactorrule;
indPruledfactor=((indPruledfactor//Total)/.rule0);
indPruledfactor=indPruledfactor/.binomial[x_,y_]:>x y (x-y-2)/2;
indPruledfactor=indPruledfactor//.{factorWDinn[x_,{{x1___,fluxCom[{a_Integer},{b_Integer}],x2___},y__}]:> fluxStructureC[{a,b},a+b]factorWDinn[x,{{x1,{a+b},x2},y}],
factorWDinn[x_,{{x1___,fluxCom[{a_Integer},fluxCom[{b_Integer},{c_Integer}]],x2___},y__}]:> fluxStructureC[{a,b,c},a+b+c]factorWDinn[x,{{x1,{a+b+c},x2},y}]};
(*Here we use //. because there might be the cases of facWDinn[_,{{_fluxCom,_fluxCom}}]. However, it will never appear in our Hamiltonian expectation value calculation*)
indPruledfactor=indPruledfactor/.{factorWDinn[_,{{___,{xx_},___},___}]/;Abs[xx]>=2->0};
indPruledfactor//Simplify]


(*given each P[__] and indP[__] a specific value such that P[] and indP[] match if their values are the same*)
assignvalue[P[v_,i_,indP[ith_,{i_,len_},___]]]:={{ith},i}
assignvalue[P[v_,i_,fluxCom[indP[ith_,{i_,len_},___],indP[jth_,{i_,lenp_},___]]]]:={{ith,jth}//DeleteDuplicates,i}
assignvalue[P[v_,i_,fluxCom[fluxCom[indP[ith_,{i_,len_},___],indP[jth_,{i_,lenp_},___]],indP[kth_,{i_,lenpp_},___]   ]  ]   ]:={{ith,jth,kth}//DeleteDuplicates,i}
assignvalue[P[v_,i_,fluxCom[indP[kth_,{i_,lenpp_},___]  ,fluxCom[indP[ith_,{i_,len_},___],indP[jth_,{i_,lenp_},___]] ]  ]   ]:={{ith,jth,kth}//DeleteDuplicates,i}
assignvalue[indP[ith_,{i_,len_},___]]:={{ith},i}


(*collect P and indP in WD based on Qfactor*)
collectPindP[Qfactor[indP[ith_,{1,len_}],indP[ith_,{2,len_}],indP[ith_,{3,len_}]],AllindPinWD_,Pops_]:=Block[{standardvalue,WDAndP,collectWDsPs,nonEmptyDir},
standardvalue=ith;
WDAndP=Join[AllindPinWD,Pops]//Flatten;
collectWDsPs=Cases[WDAndP,xx_/;MemberQ[First[assignvalue[xx]],ith]];
collectWDsPs=GatherBy[collectWDsPs,Last[assignvalue[#]]&];
collectWDsPs=SortBy[collectWDsPs,Last[assignvalue[First[#]]]&]
]
