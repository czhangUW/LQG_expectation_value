(* ::Package:: *)

(*deal with the case where all flux indices are 0*)
evaluatefacind[indl_,indr_,nt_]/;AllTrue[Join[indl,indr],NumberQ]:=Block[{holoindl,holoindr,Form,Forn,mv,nv,lenholo,mfactor,nfactor,factor1,\[Eta],\[Xi],combholol,combholor,r0,iota,prefactor,iotaT,result},
holoindl=Cases[indl,x_/;x=!=0];
holoindr=Cases[indr,x_/;x=!=0];
Form=Position[indl,x_/;x=!=0,{1},Heads->False]//Flatten;
(*To calculate the length of each piece of 0 indices by assuming there is a non-0 index at position 0*)
mv=Append[Form-1,Length[indl]]-Prepend[Form,0];
Forn=Position[indr,x_/;x=!=0,{1},Heads->False]//Flatten;
nv=Append[Forn-1,Length[indr]]-Prepend[Forn,0];
lenholo=-Range[Length[holoindl]]//Reverse;
mfactor=Total/@(Take[mv,#]&/@lenholo);
mfactor=mfactor.holoindl;
nfactor=Total/@(Take[nv,#]&/@lenholo);
nfactor=nfactor.holoindr;
factor1=t (mfactor+nfactor);
combholol=Total[holoindl];
combholor=Total[holoindr];
iota=Table[Length[holoindl]/2-i,{i,0,Length[holoindl]/2}];
prefactor=comhols[#,holoindl,holoindr]&/@iota;
iotaT=DeleteCases[Thread[List[prefactor,iota]],{0,_}];
result=If[nt==0,Total[Times[#[[1]],psh0[Total[mv]+Total[nv],#[[2]],combholol,combholor,0,\[Eta],\[Xi]]]&/@iotaT],
Block[{r10,r11},r10=Times[#[[1]],psh0[Total[mv]+Total[nv],#[[2]],combholol,combholor,1,\[Eta],\[Xi]]]&/@iotaT ;
r11=Times[#[[1]],psh0[Total[mv]+Total[nv]-1,#[[2]],combholol,combholor,0,\[Eta],\[Xi]]]&/@iotaT;r11=-factor1 r11;(r10+r11)//Total]
];
result=Times[(-1)^Count[indr,0],result]
]
