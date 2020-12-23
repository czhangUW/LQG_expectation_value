(* ::Package:: *)

(* ::Input:: *)
(**)


Forpsh0[0,0,0]=1
Forpsh0[1/2,-(1/2),-(1/2)]=-((E^(-((I \[Xi])/2)) ((-8+t \[Delta]) \[Eta]+4 t \[Delta] Tanh[\[Eta]/2]))/(8 \[Eta]))
Forpsh0[1/2,1/2,1/2]=(E^((I \[Xi])/2) (8 \[Eta]-t \[Delta] (\[Eta]+4 Tanh[\[Eta]/2])))/(8 \[Eta])
Forpsh0[1,-1,-1]=(E^(-I \[Xi]) (2 \[Eta]-t \[Delta] (\[Eta]+2 Tanh[\[Eta]/2])))/(2 \[Eta])
Forpsh0[1,0,0]=1-(2 t \[Delta] Tanh[\[Eta]/2])/\[Eta]
Forpsh0[1,1,1]=-((E^(I \[Xi]) ((-2+t \[Delta]) \[Eta]+2 t \[Delta] Tanh[\[Eta]/2]))/(2 \[Eta]))
Forpsh0[3/2,-(3/2),-(3/2)]=-((E^(-((3 I \[Xi])/2)) ((-8+9 t \[Delta]) \[Eta]+12 t \[Delta] Tanh[\[Eta]/2]))/(8 \[Eta]))
Forpsh0[3/2,-(1/2),-(1/2)]=(E^(-((I \[Xi])/2)) (8 (1+E^\[Eta]) \[Eta]-t \[Delta] (-28+\[Eta]+E^\[Eta] (28+\[Eta]))))/(8 (1+E^\[Eta]) \[Eta])
Forpsh0[3/2,1/2,1/2]=-((E^((I \[Xi])/2) ((-8+t \[Delta]) \[Eta]+28 t \[Delta] Tanh[\[Eta]/2]))/(8 \[Eta]))
Forpsh0[3/2,3/2,3/2]=-((E^((3 I \[Xi])/2) ((-8+9 t \[Delta]) \[Eta]+12 t \[Delta] Tanh[\[Eta]/2]))/(8 \[Eta]))
Forpsh0[2,-2,-2]=(E^(-2 I \[Xi]) (\[Eta]+E^\[Eta] \[Eta]-2 t \[Delta] (-1+\[Eta]+E^\[Eta] (1+\[Eta]))))/((1+E^\[Eta]) \[Eta])
Forpsh0[2,-1,-1]=1/2 E^(-I \[Xi]) (2-(t \[Delta] (\[Eta]+10 Tanh[\[Eta]/2]))/\[Eta])
Forpsh0[2,0,0]=1-(6 t \[Delta] Tanh[\[Eta]/2])/\[Eta]
Forpsh0[2,1,1]=1/2 E^(I \[Xi]) (2-(t \[Delta] (\[Eta]+10 Tanh[\[Eta]/2]))/\[Eta])
Forpsh0[2,2,2]=(E^(2 I \[Xi]) (\[Eta]-2 t \[Delta] \[Eta]-2 t \[Delta] Tanh[\[Eta]/2]))/\[Eta]
(*************)
Forpsh0[iota_,a_,b_]/;a==b:=psh[{},iota,a,b,1,\[Eta],\[Xi]]
Forpsh0[iota_,a_,b_]/;a=!=b:=0


(*expected value of p_s^0(e)...p_s^0(e) D^iota_{ab}(h_e)*)
(*For iota=0,1/2,1, the codes are written independently*)
psh0[alpha_List,0,0,0,nt_,eta_,xi_]/;Total[Abs[alpha]]==0:=Block[{m,r0},
m=Length[alpha];
r0=(-1/2)^m eta^m \[Delta]^(-m);
If[nt==0,Return[r0]];
r0(1+(m+1)m/(2 eta^2) \[Delta] t-m Coth[eta]/eta  \[Delta] t)
]
psh0[alpha_List,0,a_,b_,nt_,eta_,xi_]/;Total[Abs[alpha]]==0:=0
(********************************************************************************)
psh0[m_,0,0,0,nt_,eta_,xi_]:=Block[{r0},
r0=(-1/2)^m eta^m \[Delta]^(-m);
If[nt==0,Return[r0]];
r0(1+(m+1)m/(2 eta^2) \[Delta] t-m Coth[eta]/eta  \[Delta] t)
]
psh0[m_,0,a_,b_,nt_,eta_,xi_]:=0


psh0[alpha_List,1/2,1/2,1/2,nt_,eta_,xi_]/;Total[Abs[alpha]]==0:=Block[
{m,r0,r1},m=Length[alpha];r0=Exp[I xi/2]\[Delta]^(-m)eta^m(-1/2)^m;
If[nt==0,Return[r0]];
r1=Exp[I xi/2+eta]\[Delta]^(-m)eta^m(-1/2)^m (Coth[eta]-1)/(2eta) \[Delta] t+r0 (-\[Delta] t/8+(-m/(2 eta)+m (m+1)/(2eta^2)-Coth[eta]/(2eta)-m Coth[eta]/eta)\[Delta] t);
r0+r1
]
psh0[alpha_List,1/2,-1/2,-1/2,nt_,eta_,xi_]/;Total[Abs[alpha]]==0:=Block[
{m,r0,r1},m=Length[alpha];r0=Exp[-I xi/2]\[Delta]^(-m)eta^m(-1/2)^m;
If[nt==0,Return[r0]];
r1=Exp[-I xi/2-eta]\[Delta]^(-m)eta^m(-1/2)^m (Coth[eta]+1)/(2eta) \[Delta] t+r0 (-\[Delta] t/8+(m/(2 eta)+m (m+1)/(2eta^2)-Coth[eta]/(2eta)-m Coth[eta]/eta)\[Delta] t);
r0+r1
]
psh0[alpha_List,1/2,a_,b_,nt_,eta_,xi_]/;Total[Abs[alpha]]==0&&a!=b:=0
(***************************************************)
psh0[m_,1/2,1/2,1/2,nt_,eta_,xi_]:=Block[
{r0,r1},
r0=Exp[I xi/2]\[Delta]^(-m)eta^m(-1/2)^m;
If[nt==0,Return[r0]];
r1=Exp[I xi/2+eta]\[Delta]^(-m)eta^m(-1/2)^m (Coth[eta]-1)/(2eta) \[Delta] t+r0 (-\[Delta] t/8+(-m/(2 eta)+m (m+1)/(2eta^2)-Coth[eta]/(2eta)-m Coth[eta]/eta)\[Delta] t);
r0+r1
]
psh0[m_,1/2,-1/2,-1/2,nt_,eta_,xi_]:=Block[
{r0,r1},
r0=Exp[-I xi/2]\[Delta]^(-m)eta^m(-1/2)^m;
If[nt==0,Return[r0]];
r1=Exp[-I xi/2-eta]\[Delta]^(-m)eta^m(-1/2)^m (Coth[eta]+1)/(2eta) \[Delta] t+r0 (-\[Delta] t/8+(m/(2 eta)+m (m+1)/(2eta^2)-Coth[eta]/(2eta)-m Coth[eta]/eta)\[Delta] t);
r0+r1
]
psh0[m_,1/2,a_,b_,nt_,eta_,xi_]:=0


psh0[alpha_List,1,a_,b_,nt_,eta_,xi_]/;Total[Abs[alpha]]==0&&a==b:=Block[
{z,m,r0,fac,r1,sgn},z=eta+I xi;m=Length[alpha];
fac=Exp[a z]1/(1+Abs[a])(-1/2)^m;
sgn=1-a-Abs[a];
r0=(-(-1)^a (-1+a^2)-2a sgn Exp[eta sgn])eta^m \[Delta]^(-m);
If[nt==0,Return[fac r0]];
r1=(-1)^a (-(-1+a^2)m (m+1)/(2eta) +(-1+a^2)m Coth[eta] +2(a-Coth[eta]));
r1=r1-sgn  Exp[eta sgn](a m (m+1)/eta-a eta+2a m (sgn-Coth[eta])+1+(Abs[a]-a-1)Coth[eta]);
r1=r1-(Abs[a]-a-1)sgn/Sinh[eta];
r1=r1 eta^(m-1)\[Delta]^(1-m) t;
fac(r0+r1)
]
psh0[alpha_List,1,a_,b_,nt_,eta_,xi_]/;Total[Abs[alpha]]==0&&a!=b:=0
(*******************************)
psh0[m_,1,a_,b_,nt_,eta_,xi_]/;a==b:=Block[
{z,r0,fac,r1,sgn},z=eta+I xi;
fac=Exp[a z]1/(1+Abs[a])(-1/2)^m;
sgn=1-a-Abs[a];
r0=(-(-1)^a (-1+a^2)-2a sgn Exp[eta sgn])eta^m \[Delta]^(-m);
If[nt==0,Return[fac r0]];
r1=(-1)^a (-(-1+a^2)m (m+1)/(2eta) +(-1+a^2)m Coth[eta] +2(a-Coth[eta]));
r1=r1-sgn  Exp[eta sgn](a m (m+1)/eta-a eta+2a m (sgn-Coth[eta])+1+(Abs[a]-a-1)Coth[eta]);
r1=r1-(Abs[a]-a-1)sgn/Sinh[eta];
r1=r1 eta^(m-1)\[Delta]^(1-m) t;
fac(r0+r1)
]
psh0[m_,1,a_,b_,nt_,eta_,xi_]:=0


psh0[alpha_List,iota_,a_,b_,nt_,\[Eta]_,\[Xi]_]/;Total[Abs[alpha]]==0&&a==b:=Block[{g,m,r0,r1,r},g=CoefficientList[Forpsh0[iota,a,b],t]//PadRight[#,2]&;
m=Length[alpha];
r0=(-\[Eta]/(2\[Delta]))^m g[[1]];
If[nt==0,Return[r0]];
r1=(-\[Eta]/(2\[Delta]))^m t g[[2]]+(m(m+1))/4 1/(2\[Delta]) (-\[Eta]/(2\[Delta]))^(m-2) g[[1]]t+m/2 (-\[Eta]/(2\[Delta]))^(m-1) (Coth[\[Eta]]+b)g[[1]]t;
r=r0+r1]
psh0[alpha_List,iota_,a_,b_,nt_,eta_,xi_]/;Total[Abs[alpha]]==0&&a!=b:=0
(**********)
psh0[m_,iota_,a_,b_,nt_,\[Eta]_,\[Xi]_]/;a==b:=Block[{g,r0,r1,r},
g=CoefficientList[Forpsh0[iota,a,b],t]//PadRight[#,2]&;
r0=(-\[Eta]/(2\[Delta]))^m g[[1]];
If[nt==0,Return[r0]];
r1=(-\[Eta]/(2\[Delta]))^m t g[[2]]+(m(m+1))/4 1/(2\[Delta]) (-\[Eta]/(2\[Delta]))^(m-2) g[[1]]t+m/2 (-\[Eta]/(2\[Delta]))^(m-1) (Coth[\[Eta]]+b)g[[1]]t;
r=r0+r1]
psh0[m_,iota_,a_,b_,nt_,eta_,xi_]:=0


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)
