(* ::Package:: *)

expectedDeOps[indPruledoperators_,holoindrule_,nt_]/;nt==1:=Block[{operator1,resultOfdistIndToEdge,indhinOp,indhinrule,match2indhs,
indhruleMatchOp,UseHolorule,lops,pos4Map,SETt20,finalHoloRule,finaexp,finaexpNonDup,finaexpNonDupValue},
operator1=Map[P2FluxAndSplitHolo,indPruledoperators,{2}];
resultOfdistIndToEdge=Map[distIndsToEdge[#]&,operator1,{2}];
resultOfdistIndToEdge=resultOfdistIndToEdge/.NonCommutativeMultiply->Times;
resultOfdistIndToEdge=(resultOfdistIndToEdge/.facind[fac_,e_,indl_,indr_]:>fac evaluatefacind[indl,indr,nt]);
(****various subset in indPruledoperators corresponds to different element in rule0list****)
indhinOp=Cases[#,_indh|_indhp,Infinity]&/@(indPruledoperators[[1]]);
indhinrule=DeleteDuplicates/@(Cases[#,_indh|_indhp,Infinity]&/@holoindrule);
match2indhs=Flatten/@(Position[indhinrule,x_/;SubsetQ[#,x],{1},Heads->False]&/@indhinOp);
indhruleMatchOp=holoindrule[[#]]&/@match2indhs;
indhruleMatchOp=Tuples/@indhruleMatchOp;
indhruleMatchOp=Map[Flatten,indhruleMatchOp,{2}];
finalHoloRule=Flatten/@(Tuples[indhruleMatchOp]);
UseHolorule=MapThread[#1/.#2&,{#,indhruleMatchOp}]&/@resultOfdistIndToEdge;
(**********************************)
UseHolorule=Map[(#/.t->0)+t (D[#,t]/.t->0)&,UseHolorule,{2}];(*Faster than use only the latter one*)
UseHolorule=Map[Expand,UseHolorule,{2}];
(**********************************)
lops=Length[indPruledoperators[[1]]];
pos4Map=Tuples[{Range[Length[resultOfdistIndToEdge]],#}]&/@Subsets[Range[lops],{lops-1}];
SETt20=MapAt[(#/.t->0)&,UseHolorule,#]&/@pos4Map;
SETt20=SETt20/.t^n_/;n>=2->0;
finaexp=Map[Tuples,SETt20,{2}];
finaexpNonDup=Level[finaexp,{3}]//DeleteDuplicates;
finaexpNonDupValue=Times@@@finaexpNonDup;
finaexpNonDupValue=Dispatch[MapThread[Rule,{finaexpNonDup,finaexpNonDupValue}]];
finaexp=finaexp/.finaexpNonDupValue;
finaexp=Total[finaexp](*//Expand*);
(*=================================\[Equal]*)
(*Here the reason is the following: (a+b t)(c+ dt)=a c+ (a d+ b c)t+O(t^2)=((a+b (2 t))c+a(c+d (2 t)))/2*)
finaexp=((finaexp/.t->0)/lops)+D[finaexp,t] t;
(*=================================\[Equal]*)
finaexp=finaexp//Transpose;
{finaexp,finalHoloRule}=Map[Delete[#,Position[finaexp,{0..}|{0}]]&,{finaexp,finalHoloRule}];
If[finaexp=={},{{},{}},{finaexp//Transpose,Dispatch[finalHoloRule]}]
]


expectedDeOps[indPruledoperators_,holoindrule_,nt_]/;nt==0:=Block[{operator1,indhinOp,indhinrule,match2indhs,
indhruleMatchOp,finalHoloRule,UseHolorule,finaexp},
operator1=(indPruledoperators/.NonCommutativeMultiply->Times)/.{P[v_,e_,alpha_]:>(-\[Eta]/\[Delta])^Length[alpha],P[v_,e_,alpha_,1]:>0};
indhinOp=Cases[#,_indh|_indhp,Infinity]&/@(indPruledoperators[[1]]);
indhinrule=DeleteDuplicates/@(Cases[#,_indh|_indhp,Infinity]&/@holoindrule);
match2indhs=Flatten/@(Position[indhinrule,x_/;SubsetQ[#,x],{1},Heads->False]&/@indhinOp);
indhruleMatchOp=holoindrule[[#]]&/@match2indhs;
indhruleMatchOp=Tuples/@indhruleMatchOp;
indhruleMatchOp=Map[Flatten,indhruleMatchOp,{2}];
finalHoloRule=Flatten/@(Tuples[indhruleMatchOp]);
UseHolorule=MapThread[#1/.#2&,{#,indhruleMatchOp}]&/@operator1;
UseHolorule=UseHolorule/.{holonomy[e_,a_,a_]/;e===Sort[e]:>Exp[I a \[Xi]],holonomy[e_,a_,a_]/;e=!=Sort[e]:>Exp[-I a \[Xi]],holonomy[e_,a_,b_]/;a!=b:>0};
finaexp=Map[Tuples,UseHolorule];
finaexp=Apply[Times,finaexp,{2}];
finaexp=finaexp//Transpose;
{finaexp,finalHoloRule}=Map[Delete[#,Position[finaexp,{0..}|{0}]]&,{finaexp,finalHoloRule}];
If[finaexp=={},{{},{}},{finaexp//Transpose,Dispatch[finalHoloRule]}]
]
