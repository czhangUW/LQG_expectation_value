(* ::Package:: *)

(*===get the rules for holonomy indices for further replacement and calculate the expected value==========================*)
expectedValueFluxAll0[decoupleOperator_,rule0List_,powert_]:=Block[{hololist,holoindrule,indPruledDeOps},
hololist=Cases[decoupleOperator,_holonomy,Infinity];
hololist=GatherBy[hololist,Sort[First[#]]&];
holoindrule=getHoloindrule/@hololist;
indPruledDeOps=decoupleOperator/.{fluxCom[___,fluxCom[__],___]:>{0},P[x__,fluxCom[_indP,_indP]]:>P[x,{0},1]};
(*fluxCom[__] is actually a set of flux indices with length 1. However, P[__,fluxCom[_indP,_indP]]=p_s(e+)+p_t(e-)*)
indPruledDeOps=(indPruledDeOps/.indP[i_,{j_,len_}]:>ConstantArray[0,len/.#])&/@rule0List;
(******evaluate the result of expectation value and get holonomy index rule for further replacement******)
expectedDeOps[indPruledDeOps,holoindrule,powert]]
