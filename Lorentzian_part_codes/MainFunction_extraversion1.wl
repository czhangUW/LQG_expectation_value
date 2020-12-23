(* ::Package:: *)

Get["preliminary.wl"]
LaunchKernels[96]
f[n_,x_]:=1/2 Abs[x-n]+1/2 (x-n)
rule0ListV0=Tuples[{1,2,3,4,5},5];
rule0ListV0=Cases[rule0ListV0,x_/;f[3,x[[1]]+x[[2]]]+f[3,x[[3]]+x[[4]]]+x[[5]]<=3];
rule0List={m[1]->#[[1]],m[2]->#[[2]],m[3]->#[[3]],m[4]->#[[4]],m[5]->#[[5]]}&/@rule0ListV0;
rule0List=rule0List[[1;;50]];
v=vertex[{0,0,0}];
vlist=Table[vertex[{i,j,k}],{i,-2,2},{j,-2,2},{k,-2,2}]//Flatten;
elist=Table[{i,si,j,sj,k,sk},{i,1,3},{si,-1,1,2},{j,1,3},{sj,-1,1,2},{k,1,3},{sk,-1,1,2}]//Flatten[#,5]&;
elist=DeleteCases[elist,{x_,_,x_,_,z_,_}|{z_,_,x_,_,x_,_}|{x_,_,z_,_,x_,_}];
allv1=Join[Tuples[{{v,vertex[{1,0,0}]},vlist}],Tuples[{vlist,{v,vertex[{1,0,0}]}}]]//DeleteDuplicates;
allvAnde1=Tuples[{allv1,elist}];
allvAnde1=DeleteCases[allvAnde1,x_/;!judgeKoperator@@x];
allvAnde1=ReplacePart[#,{2,6}->Abs[#[[2,6]]]]&/@allvAnde1//DeleteDuplicates;
allv2=Join[Tuples[{{v,vertex[{0,1,0}]},vlist}],Tuples[{vlist,{v,vertex[{0,1,0}]}}]]//DeleteDuplicates;
allvAnde2=Tuples[{allv2,elist}];
allvAnde2=DeleteCases[allvAnde2,x_/;!judgeKoperator@@x];
allvAnde2=ReplacePart[#,{2,6}->Abs[#[[2,6]]]]&/@allvAnde2//DeleteDuplicates;
allvAnde4Hl1=Flatten[#,1]&/@Tuples[{allvAnde1,allvAnde2}];
allvAnde4Hl=DeleteCases[allvAnde4Hl1,x_/;!MemberQ[x[[1]],vertex[{1,0,0}]]&&!MemberQ[x[[3]],vertex[{0,1,0}]]];
allvAnde4Hl=ParallelMap[rotationExtra,allvAnde4Hl];(*loopsymmetry has been considered in rotationExtra*)
allvAnde4Hl=allvAnde4Hl//DeleteDuplicates;
allvAnde4Hl=ParallelMap[DeleteDuplicates,allvAnde4Hl];
comQ=ParallelMap[extraSymmetryQ,allvAnde4Hl[[All,1]]];
allsgns=ParallelMap[ToorienteEdges,allvAnde4Hl,{2}];
allsgns=PadRight[allsgns];
(**************)
filesName=Table[StringJoin[{"./result/result",ToString[i1],".txt"}],{i1,1,Length[allvAnde4Hl]}];
Print[Length[allvAnde4Hl]];
i0list=Position[FileExistsQ/@filesName,False]//Flatten;
Print[Length[i0list]];
SetSharedVariable[allvAnde4Hl,allsgns,comQ];
ParallelDo[
Block[{time,summation},Print[i0];
{time,summation}=expectedValueExtra[allvAnde4Hl[[i0]],allsgns[[i0]],comQ[[i0]]]//AbsoluteTiming;
Export[filesName[[i0]],InputForm[{i0,summation}]];
Print[{i0,time}];
ClearSystemCache[];
],{i0,i0list},Method->"FinestGrained"]
(*******============================================================*********)
rtable=ParallelMap[ToExpression[Import[#]]&,filesName];
rtable=Flatten[#,1]&/@(List@@@rtable);
totalresult=Total[rtable[[All,2]]];
totalresult=Expand/@totalresult;
Export["finalResultExtra.txt",InputForm[totalresult]]
