(* ::Package:: *)

(*integral[...] calculate :t^m \[ExponentialE]^extrapow Integrate[ e^(-constant \[Delta] t (x^2+b x +c)) pol[x,partial_eta] exp[sgn eta x]/f[eta], where the power t^m comes from 
the flux operator p_s^alpha=i t R^\alpha. extrapow is independent of t. maxpower = m + 1 always. 
*)
integral[pol0_, gauspower0_, f_, sgn_, x_Symbol, dy_Symbol, nt0_,maxpower0_, extrapow_] /; f =!= 0 :=Block[{pol, gauspower,\[Eta]0,coex0,maxpower,orderOfFirstTerm,nt, coex, n, rule, y, intgd, intgdnv, tlist, result, prefactor, coet},
  pol = pol0 /. {dy -> dy + sgn x};
  gauspower = CoefficientList[gauspower0 + sgn \[Eta]0 x, x];
  (*Sometime the replacement dy\[Rule]dy +/- x was done outside the function. In this case sgn can be set to be 0 with redefining gauspower0*)
coex0=CoefficientList[pol, x];
coex0=If[Length[coex0]<=maxpower0 + 1,PadRight[coex0,maxpower0+1],coex0 ];
maxpower=Length[coex0]-1;(*maxpower = maxpower0 if degree of pol0 \[LessEqual] maxpower0. otherwise, maxpower is the degree of pol*)
orderOfFirstTerm=maxpower0-maxpower;
nt=nt0-orderOfFirstTerm;(*nt = nt0 if degree of pol \[LessEqual] maxpower0. otherwise, nt is larger than nt0*)
(*There are the case where the degree of pol is larger than than maxpower0. This case can be treated as the case when degree of pol \[LessEqual] maxpower0
once nt0 and maxpower0 are changed to nt can maxpower. Then we just need to multiply the result with t^orderOfFirstTerm*)
  coex = Take[ Reverse[coex0],Min[nt + 1, maxpower + 1]];
  coex = Map[ReplaceAll[Expand[# dy^2], dy^n_ -> D[f, {\[Eta]0, n - 2}]] &,coex];
  rule = x ->y/Sqrt[-gauspower[[3]]] - gauspower[[2]]/(2 gauspower[[3]]);
  intgd =  CoefficientList[  coex.Table[x^(maxpower - i), {i, 0, Min[nt, maxpower]}] /. rule,y];
  intgdnv = \[Delta] t^maxpower intgd[[1 ;; Length[intgd] ;; 2]];
  prefactor = gauspower[[1]] -  gauspower[[2]]^2/(4 gauspower[[3]]) - \[Delta] t/2 - \[Eta]0^2/(2 \[Delta] t) // FullSimplify;
  (*In principle, prefactor=coet t+constant*)
  coet = D[prefactor, t];
  prefactor = prefactor - coet t + extrapow // FullSimplify;
  prefactor = Exp[prefactor]  Sinh[\[Eta]0]/(Sqrt[2 \[Pi]] \[Eta]0);
  prefactor = 2 prefactor/Sqrt[-gauspower[[3]]] /. {\[Delta] -> 1, t -> 1};
  (* We actually calculate prefactor 2 (\[Delta] t)^(3/2)/(Sqrt[-gauspower[[3]]](\[Delta] t)) here, 
  where we used the fact that gauspower[[3]]=-constant \[Delta] t*)
  (*The second factor is from the taylor series of Exp[-coet t] which is from the prefactor*)
  tlist = Join[{(1 + Sum[(coet t)^k/k!, {k, 1, nt}])},Table[(1 + Sum[(coet t)^k/k!, {k, 1, nt - i}]) t^i , {i, 1,nt}]];
  result =Map[PadRight[CoefficientList[#, t], nt + 1].tlist &,intgdnv].Table[Gamma[1/2 + k], {k, 0, Length[intgdnv] - 1}];
 result = If[orderOfFirstTerm=!=0,FullSimplify[result prefactor t^orderOfFirstTerm],FullSimplify[result prefactor ]]]
  integral[pol0_, gauspower0_, f_, sgn_, x_Symbol, dy_Symbol, nt_, maxpower_, extrapow_] /; f === 0 := 0


(*Several functions which will be used to calculate psh[....] with iota\[GreaterEqual]3/2. F[...] is to calculate the polynomials*)
(*removeDenominator is to remove the Denominator to get pure polynomial term*)
(*termDenominator is to get the term constant/y. However termDenominator returns only the constant*)
(*solveCoe[...] get the coefficient a,b,c,..... such that, saying, 1/((n-1)(n-2))=a/(n-1)+b/(n-2) *)
F[d_,alpha_,\[Iota]_,a_,b_,x_Symbol,dy_Symbol]:=Block[{m,factor,pol},
m=Length[alpha];
factor=Product[1/Sqrt[1+Abs[alpha[[i]]]],{i,1,m}];
factor=factor 1/Sqrt[(\[Iota]+a)!(\[Iota]-a)!(\[Iota]+b)!(\[Iota]-b)!];
pol= ((-1)^(d-2a+b) x(x-2d))/Product[x-d+\[Iota]-z,{z,0,2 \[Iota]}] Product[alpha[[i]] (x - 1)/2 - dy/2 + Total[alpha[[1 ;; i]]], {i, 1, m}];
pol=pol Sum[1/z! (-1)^z Product[\[Iota]+d-i,{i,0,z-1}]Product[(x-1)/2+dy/2+b-z+\[Iota]-i,{i,0,\[Iota]+a-1}]
  Product[(x-1)/2-dy/2-d-b+z-i,{i,0,\[Iota]-a-1}],{z,0,\[Iota]+d}]Sum[1/z! (-1)^z Product[\[Iota]-d-i,{i,0,z-1}]
  Product[(x-1)/2+dy/2-d-z+\[Iota]-i,{i,0,\[Iota]-b-1}]Product[(x-1)/2-dy/2+z-i,{i,0,\[Iota]+b-1}],{z,0,\[Iota]-d}];pol=pol factor]
(************)
removeDenominator[f_,x_Symbol,dy_Symbol]:=Block[ {fp,coe},fp={f/.dy->dy-x,f/.dy->dy+x};coe=Rest/@CoefficientList[fp x,x];#.x^(Range[Length[#]]-1)&/@coe]
termDenominator[f_,x_Symbol,dy_Symbol]:=Block[ {fp,coe},fp={f/.dy->dy-x,f/.dy->dy+x};coe=First/@CoefficientList[fp x,x]]
(***************)
solveCoe[poles_]:=Block[{x,func,f,var,coefunc,s},
func=(1/(x-#)&/@poles)Times@@(x-#&/@poles);
var=f/@Range[Length[poles]];coefunc=CoefficientList[var.func,x];
s=Solve[coefunc==PadRight[{1},Length[poles]],var];var/.s//Flatten]


(*ForPsh[...] is to calculate t^m e^{b z} e^{-t/2 delta t(2 d^2-1)}int[e^gaussianpower pol(x,d,partial_eta)sinh(x eta)/sinh(eta)]*)
ForPsh[d_,alpha_,iota_,a_,b_,nt_,\[Eta]_,\[Xi]_]:=Block[{pol0,x,dy,num,denom,prefactorlist,prefactor,poles,numatpole,krule,evaluek,posExtra,extraTerm,posExtraNDup,posExtraN,
extraTermPowerLeft,powerrule,leftTerm,leftPol,extraPol,extraPolonSinh,pols,polsDenominatorRemoved,expcoefficient,gauspower0,maxpower,r0,r1,\[Eta]0,polsextra,expcoefficientExtra,gauspowerExtra,bb,cc,SinhyOyTerm0,SinhyOyTerm,constant,r2},
pol0=F[d,alpha,iota,a,b,x,dy];
num=Numerator[pol0]//FactorList;
denom=Denominator[pol0]//FactorList;
prefactorlist=Cases[denom,xx_/;!MemberQ[xx,x,Infinity]];
prefactor=Times@@Map[#[[1]]^(-#[[2]])&,prefactorlist];
poles=x/.Solve[Denominator[pol0]==0,x];
numatpole=num[[All,1]]/.x->#&/@poles;
krule=Table[{dy->i},{i,-Abs[#]+1,Abs[#]-1,2}]&/@poles;
evaluek=MapThread[#1/.#2&,{numatpole,krule}];
posExtra=Flatten/@(Map[FirstPosition[#,0]&,evaluek,{2}]);
extraTerm=num[[#,1]]&/@posExtra;
posExtraNDup=DeleteDuplicates/@posExtra;
posExtraN=MapThread[Function[{u,v},Count[u,#]&/@v],{posExtra,posExtraNDup}];
extraTermPowerLeft=MapThread[num[[#1,2]]-#2&,{posExtraNDup,posExtraN}];
powerrule=Thread/@Thread[Rule[Thread[{#,2}]&/@posExtraNDup,extraTermPowerLeft]];
leftTerm=(ReplacePart[num,#]&/@powerrule)/.{xx_,0}:>{1,1};
leftPol=Times@@@Map[#[[1]]^#[[2]]&,leftTerm,{2}];
leftPol=leftPol prefactor;
extraPol=Times@@@extraTerm;
extraPol=Expand[extraPol dy^2]/.dy^m_:>D[Sinh[x \[Eta]0]/Sinh[\[Eta]0],{\[Eta]0,m-2}]//Simplify;
extraPolonSinh=MapThread[#1/.x->x+#2&,{extraPol,poles}];
extraPolonSinh=extraPolonSinh/.{Sinh[y_]:>TrigExpand[Sinh[Expand[y]]],Cosh[y_]:>TrigExpand[Cosh[Expand[y]]]};
extraPolonSinh=(CoefficientList[#,x]&/@extraPolonSinh//FullSimplify);
pols=MapThread[ConstantArray[#1,Length[#2]]&,{leftPol,extraPolonSinh}];
pols=MapThread[#1/.x->x+#2&,{pols,poles}];
pols=Times[#,x^(Range[Length[#]]-2)]&/@pols;
polsDenominatorRemoved=Map[removeDenominator[#,x,dy]&,pols,{2}];
expcoefficient=CoefficientList[Times[(extraPolonSinh//TrigToExp),E^(x \[Eta]0)]/.E^y_:>E^Expand[y],E^(x \[Eta]0)];
expcoefficient=Map[PadRight[#,3]&,expcoefficient,{2}];
expcoefficient=Map[Drop[#,{2}]&,expcoefficient,{2}]//Simplify;
gauspower0=-t/2 \[Delta] (2 d^2-1)-1/2 \[Delta] t (x^2-2 d x);
gauspower0=Map[gauspower0/.x->x+#&,poles];
gauspower0=Map[#+{-x \[Eta]0,x \[Eta]0}&,gauspower0];
gauspower0=MapThread[#1/.x_:>ConstantArray[x,Length[#2]]&,{gauspower0,expcoefficient}]//Simplify;
maxpower=Length[alpha]+1;
r0=Table[MapThread[integral[#1,#2,#3,0,  x, dy, nt,maxpower,b (\[Eta]0+I \[Xi])]&,{polsDenominatorRemoved[[i]],gauspower0[[i]],expcoefficient[[i]]},2],{i,1,Length[polsDenominatorRemoved]}];
r1=Plus@@@(Flatten/@r0);
r1=r1.(solveCoe[poles]);
If[nt<Length[alpha]+2,Return[r1/.\[Eta]0->\[Eta]]];
polsextra=Map[termDenominator[#,x,dy]&,pols,{2}][[All,1,1]];
expcoefficientExtra=2expcoefficient[[All,1,2]];
gauspowerExtra=-1/2 (2 d^2-1)-1/2 (x^2-2 d x);
gauspowerExtra=Map[gauspowerExtra/.x->x+#&,poles];
bb=Coefficient[#,x]&/@gauspowerExtra;
cc=gauspowerExtra/.x->0;
SinhyOyTerm0=E^((cc-1/2+bb^2/2)\[Delta] t) Sinh[\[Eta]0]/\[Eta]0 (\[Delta] t)^2;
SinhyOyTerm=E^(bb \[Eta]0) 1/(\[Eta]0+bb \[Delta] t) Sum[Gamma[i+1/2]/Sqrt[\[Pi]] ((2 \[Delta] t)/(\[Eta]0+bb \[Delta] t))^i,{i,0,nt-Length[alpha]}];
SinhyOyTerm=E^(-bb \[Eta]0) 1/(\[Eta]0-bb \[Delta] t) Sum[Gamma[i+1/2]/Sqrt[\[Pi]] ((2 \[Delta] t)/(\[Eta]0-bb \[Delta] t))^i,{i,0,nt-Length[alpha]}]+SinhyOyTerm;
SinhyOyTerm=Times[t^Length[alpha],SinhyOyTerm ,SinhyOyTerm0]//Series[#,{t,0,nt}]&//Normal;
constant=MapThread[Expand[#1 dy^2]/.dy^n_:>D[#2,{\[Eta]0,n-2}]&,{polsextra,expcoefficientExtra}];
r2=Times[E^(b (\[Eta]0+I \[Xi])),constant,SinhyOyTerm].(solveCoe[poles]);
(r1+r2)/.\[Eta]0->\[Eta]
]


(*For iota=0,1/2,1, we didn't use the function ForPsh. The code are written independently.*)


psh[alpha_, iota_, a_, b_, nt_, \[Eta]_, \[Xi]_] /;Total[alpha] - a + b =!= 0 := 0


psh[alpha_, iota_, a_, b_, nt_, \[Eta]_, \[Xi]_] /; iota === 0 && Total[alpha] === 0 := psh[alpha, iota, a, b, nt, \[Eta], \[Xi]]=
 Block[{m, maxpower, pol, x, dy, gauspower, result},
  m = Length[alpha];
  maxpower = m + 1;
  pol = Product[alpha[[i]] (x - 1)/2 - dy/2 + Total[alpha[[1 ;; i]]], {i, 1, m}];
  pol = pol x;
  gauspower = -\[Delta] t/2 x^2 + t \[Delta]/2;
  result = integral[pol, gauspower, 1/(2 Sinh[\[Eta]0]), 1, x, dy, nt, maxpower, 0];
  result = Product[1/Sqrt[1 + Abs[alpha[[i]]]], {i, 1, m}] result;
  FullSimplify[result] /. \[Eta]0 -> \[Eta]]


psh[alpha_, iota_, a_, b_, nt_, \[Eta]_, \[Xi]_] /;iota === 1/2 && Total[alpha] - a + b === 0 := psh[alpha, iota, a, b, nt, \[Eta], \[Xi]]=
 Block[{m, maxpower, pol, x, dy, gauspower, prefactor, result},
  m = Length[alpha];
  maxpower = m + 1;
  pol = Product[ alpha[[i]] (x - 1)/2 - dy/2 + Total[alpha[[1 ;; i]]], {i, 1,Length[alpha]}];
  pol = pol ((x - 1)/2 - b dy);
  gauspower = -\[Delta] t x (x - 1)/2 + \[Delta] t/4;
  prefactor = (-1)^(a - b)  Product[1/Sqrt[1 + Abs[alpha[[i]]]], {i, 1, Length[alpha]}];
  result =Total[Map[integral[pol, gauspower, #/(2 Sinh[\[Eta]0]), #, x, dy, nt,  maxpower, b (\[Eta]0 + I \[Xi])] &, {-1, 1}]];
  result = FullSimplify[result prefactor]; result /. \[Eta]0 -> \[Eta]
  ]


psh[alpha_, iota_, a_, b_, nt_, \[Eta]_, \[Xi]_] /; iota === 1 && Total[alpha] - a + b === 0 :=(*psh[alpha, iota, a, b, nt, \[Eta], \[Xi]]=*)
Block[
{m, maxpower, sgn, x, dy, pol, gauspower, prefactor, result11, polp, polm, y, extraterm, n,gauspowerp, gauspowerm, result12, result120,result1, alpha1, expfactor, f, int21, int221, int222, int22, int231, int232, int23, int2, result2, result},
  m = Length[alpha];
  maxpower = m + 1;
  (*The second term I_2 in our script*)
  sgn = -(1 - Abs[b] - b);
  pol = Product[-alpha[[i]] (x + 1)/2 - dy/2 +Total[alpha[[1 ;; i]]], {i, 1, Length[alpha]}];
  pol = sgn pol ((x + 1)/2 - (Abs[b] - 1 - b) dy/2 + Abs[b]);
  gauspower = -((\[Delta] t)/2) (x + 1)^2;
  prefactor = (-1)^(a - b) 1/(Sqrt[1 + Abs[a]] Sqrt[1 + Abs[b]])Product[1/Sqrt[1 + Abs[alpha[[i]]]], {i, 1, Length[alpha]}];
  result11 = integral[pol, -((\[Delta] t)/2) (x + 1)^2, 1/Sinh[\[Eta]0], sgn, x,dy, nt, maxpower, b (\[Eta]0 + I \[Xi])];
  result11 = result11 prefactor;
  polp = Product[-alpha[[i]] y/2 - (y + dy)/2 + Total[alpha[[1 ;; i]]], {i, 1, Length[alpha]}];
  polp = polp (y/2 - (Abs[b] - 1 - b) (y + dy)/2 + Abs[b]);
  polm = Product[-alpha[[i]] y/2 - (-y + dy)/2 +  Total[alpha[[1 ;; i]]], {i, 1, Length[alpha]}];
  polm = polm (y/2 - (Abs[b] - 1 - b) (-y + dy)/2 + Abs[b]);
  extraterm = Product[Total[alpha[[1 ;; i]]] - dy/2, {i, 1,Length[alpha]}] (Abs[b] - (Abs[b] - 1 - b) dy/2);
  polp = (polp - extraterm)/y;
  polm = (polm - extraterm)/y;
  gauspowerp = -\[Delta] t y^2/2 + \[Eta]0 y;
  gauspowerm = -\[Delta] t y^2/2 - \[Eta]0 y;
result12 = Total[MapThread[integral[#1, #2, (1 - Abs[b] - b)/(2 Sinh[\[Eta]0]^2), 0, y, dy,nt, maxpower, b (\[Eta]0 + I \[Xi])] &, {{polp, -polm}, {gauspowerp, gauspowerm}}]];
  result12 = result12  prefactor;
  extraterm = If[nt>=m+2,  ReplaceAll[Expand[dy^2 extraterm, dy], dy^n_ -> D[(1 - Abs[b] - b)/Sinh[\[Eta]0]^2, {\[Eta]0, n - 2}]],0];
  result120 = t^m extraterm  Sinh[\[Eta]0]/(2 Sqrt[\[Pi]] \[Eta]0^2)Sum[Gamma[1/2 + n] (2 \[Delta] t)^(n + 2)/\[Eta]0^(2 n) Sum[(-\[Delta] t/2)^k/k!, {k, 0, nt - n - 2}], {n, 0, nt - 2}];
  result120 = result120  Exp[+b (I \[Xi] + \[Eta]0)] (-1)^(a - b) Product[1/Sqrt[1 + Abs[alpha[[i]]]], {i, 1, Length[alpha]}] 1/Sqrt[(1 + Abs[a]) (1 + Abs[b])];
  result1 = result11 + result12 + result120;
  (****************************************************************************************************************)  
  (*The first term I_1 in the script*)
pol = If[alpha === {}, -x, Block[{pol1}, pol1 = Product[alpha[[i]] (x - 1)/2 - dy/2 + Total[alpha[[1 ;; i]]], {i, 2,Length[alpha]}];pol1 (a (x - 1)/2 + dy/2 + b) x]];
  gauspower = -((\[Delta] t)/2) (x^2 - 1);
  alpha1 = If[alpha === {}, -a, alpha[[1]]];
  expfactor = (b alpha1 + 1) Sinh[x \[Eta]0] - (alpha1 + b) Cosh[\[Eta]0 x];
  f = {Coefficient[expfactor // TrigToExp, E^(x \[Eta]0)]/Sinh[\[Eta]0],Coefficient[expfactor // TrigToExp, E^(-x \[Eta]0)]/Sinh[\[Eta]0]};
  sgn = {1, -1};
  int21 =  Total[MapThread[integral[pol, gauspower, #1, #2, x, dy, nt, maxpower,b (I \[Xi] + \[Eta]0)] &, {f, sgn}]];
polp = If[alpha === {}, -(y + 1),Block[{pol1}, pol1 = Product[ alpha[[i]] y/2 - (dy + y)/2 + Total[alpha[[1 ;; i]]], {i, 2,Length[alpha]}]; pol1 (a y/2 + (dy + y)/2 + b) (y + 1)]];
  polm = If[alpha === {}, -(y + 1),  Block[{pol1}, pol1 = Product[alpha[[i]] y/2 - (dy - y)/2 + Total[alpha[[1 ;; i]]], {i, 2, 
        Length[alpha]}]; pol1 (a y/2 + (dy - y)/2 + b) (y + 1)]];
  extraterm = If[alpha === {}, -1,  Block[{pol1},pol1 = Product[-(dy/2) + Total[alpha[[1 ;; i]]], {i, 2, Length[alpha]}]; pol1 (dy/2 + b) ]];
  polp = (polp - extraterm)/y;
  polm = (polm - extraterm)/y;
  gauspowerp = -((\[Delta] t)/2) (y^2 + 2 y) + \[Eta]0 y;
  gauspowerm = -((\[Delta] t)/2) (y^2 + 2 y) - \[Eta]0 y;
  f = (alpha1 Sinh[\[Eta]0] + Cosh[\[Eta]0])/(2 Sinh[\[Eta]0]^3);
  int221 =  Total[MapThread[integral[#1, #2, f, 0, y, dy, nt, maxpower, b (I \[Xi] + \[Eta]0)] &, {{polp, -polm}, {gauspowerp, gauspowerm}}]];
  extraterm = If[nt>=m+2, ReplaceAll[Expand[dy^2 extraterm, dy],  dy^n_ -> D[2 f, {\[Eta]0, n - 2}]],0];
  int222 =t^m extraterm Sinh[\[Eta]0]/\[Eta]0^2 Sum[ Sum[1/Sqrt[\[Pi]] Gamma[1/2 + n] 2^n/\[Eta]0^(n + mm) Binomial[n + mm,n - mm] (E^-\[Eta]0 + (-1)^(mm - n) E^\[Eta]0) 
(\[Delta] t)^( mm + 2), {n, 0, mm}], {mm, 0, nt - 2}];
  int222 = int222 E^(b (I \[Xi] + \[Eta]0));
  int22 = int221 + int222;
  polp = If[alpha === {}, -(y - 1),Block[{pol1}, pol1 = Product[alpha[[i]] y/2 - (dy + y)/2 + Total[alpha[[1 ;; i - 1]]], {i,   2, Length[alpha]}]; 
     pol1 (a y/2 + (dy + y)/2 + b - a) (y - 1)]];
  polm = If[alpha === {}, -(y - 1), Block[{pol1}, pol1 = Product[alpha[[i]] y/2 - (dy - y)/2 + Total[alpha[[1 ;; i - 1]]], {i, 2, Length[alpha]}]; 
     pol1 (a y/2 + (dy - y)/2 + b - a) (y - 1)]];
  extraterm = If[alpha === {}, 1, Block[{pol1}, pol1 = Product[-(dy/2) + Total[alpha[[1 ;; i - 1]]], {i, 2,  Length[alpha]}]; pol1 (dy/2 + b - a) (-1) ]];
  polp = (polp - extraterm)/y;
  polm = (polm - extraterm)/y;
  gauspowerp = -((\[Delta] t)/2) (y^2 - 2 y) + \[Eta]0 y;
  gauspowerm = -((\[Delta] t)/2) (y^2 - 2 y) - \[Eta]0 y;
  f = (-b Sinh[\[Eta]0] + Cosh[\[Eta]0])/(2 Sinh[\[Eta]0]^3);
  int231 = Total[MapThread[integral[#1, #2, f, 0, y, dy, nt, maxpower,  b (I \[Xi] + \[Eta]0)] &, {{polp, -polm}, {gauspowerp,gauspowerm}}]];
  extraterm = If[nt>=m+2, ReplaceAll[Expand[dy^2 extraterm, dy], dy^n_ -> D[2 f, {\[Eta]0, n - 2}]],0];
  int232 = t^m extraterm Sinh[\[Eta]0]/\[Eta]0^2 Sum[Sum[1/Sqrt[\[Pi]] Gamma[1/2 + n] 2^n/\[Eta]0^(n + mm)Binomial[n + mm, n - mm] (E^-\[Eta]0 + (-1)^(mm - n) E^\[Eta]0) 
(\[Delta] t)^( mm + 2), {n, 0, mm}], {mm, 0, nt - 2}];
  int232 = int232 E^(b (I \[Xi] + \[Eta]0));
  int23 = int231 + int232;
  int2 = int21 + int22 - int23;
  result2 = - ((-1)^a/2) Product[1/Sqrt[  1 + Abs[alpha[[i]]]], {i, 1, Length[alpha]}] 1/ Sqrt[(1 + Abs[a]) (1 + Abs[b])] int2;
  result = FullSimplify[result1 + result2];
  result /. \[Eta]0 -> \[Eta]
  ]


psh[alpha_,iota_,a_,b_,nt_,\[Eta]_,\[Xi]_]/;Total[alpha]-a+b==0:=psh[alpha,iota,a,b,nt,\[Eta],\[Xi]]=Block[{ds},
ds=Table[iota-i,{i,0,iota}];Sum[(2-KroneckerDelta[d,0])/2 ForPsh[d,alpha,iota,a,b,nt,\[Eta],\[Xi]],{d,ds}]]
psh[alpha_,iota_,a_,b_,nt_,\[Eta]_,\[Xi]_]/;Total[alpha]-a+b!=0:=psh[alpha,iota,a,b,nt,\[Eta],\[Xi]]=0
