(* ::Package:: *)

NCO={holonomy,P,flux,facind}
epdNCM[(h:NonCommutativeMultiply)[a___,b_Plus,c___]]:=Distribute[h[a,b,c],Plus,h,Plus,epdNCM[h[##]]&]
epdNCM[(h:NonCommutativeMultiply)[a___,(b:Times)[x___,y_/;Cases[{y},yy_/;MemberQ[NCO,yy],Infinity,Heads->True]=!={},z___],c___]]:=Times[x,z] epdNCM[h[a,y,c]]
(*epdNCM[(h:NonCommutativeMultiply)[a___,(b:Times)[x___,y_holonomy,z___],c___]]:=b[x z] epdNCM[h[a,y,c]]
epdNCM[(h:NonCommutativeMultiply)[a___,(b:Times)[x___,y_P,z___],c___]]:=b[x z] epdNCM[h[a,y,c]]
epdNCM[(h:NonCommutativeMultiply)[a___,(b:Times)[x___,y_flux,z___],c___]]:=b[x z] epdNCM[h[a,y,c]]
epdNCM[(h:NonCommutativeMultiply)[a___,(b:Times)[x___,y_facind,z___],c___]]:=Times[x,z] epdNCM[h[a,y,c]]
epdNCM[(h:NonCommutativeMultiply)[a___,(b:Times)[x___,y_NonCommutativeMultiply,z___],c___]]:=Times[x,z] epdNCM[h[a,y,c]]*)
epdNCM[(h:Times)[x__,y__]]:=h[epdNCM[h[x]],epdNCM[h[y]]]
epdNCM[(h:Plus)[x__,y__]]:=h[epdNCM[h[x]],epdNCM[h[y]]]
epdNCM[(h:NonCommutativeMultiply)[x_]]:=x
epdNCM[a___]:=ExpandAll[a]
