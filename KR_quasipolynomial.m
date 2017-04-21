(* ::Package:: *)

SetDirectory[DirectoryName[$InputFileName]];
Get["KR_hvector_EFG.dat"];
adjmat[E,6]=AdjacencyMatrix[Graph[{1<->2,2<->3,3<->4,4<->5,3<->6}]]
adjmat[E,7]=AdjacencyMatrix[Graph[{1<->2,2<->3,3<->4,4<->5,5<->6,3<->7}]]
adjmat[E,8]=AdjacencyMatrix[Graph[{1<->2,2<->3,3<->4,4<->5,5<->6,6<->7,3<->8}]]
cartan[ty_,rk_]:=cartan[ty,rk]=2IdentityMatrix[rk]-adjmat[ty,rk]
cartan[F,4]={{2,-1,0,0},{-1,2,-1,0},{0,-2,2,-1},{0,0,-1,2}};
cartan[G,2]={{2,-1},{-3,2}};
inversecartan[ty_,rk_]:=inversecartan[ty,rk]=Inverse[cartan[ty,rk]]
adjvtx[ty_,rk_,a_]:=Flatten@Position[cartan[ty,rk][[a]],c_/;c<0]
dualCoxeter[E,6]=12;
dualCoxeter[E,7]=18;
dualCoxeter[E,8]=30;
dualCoxeter[F,4]=9;
dualCoxeter[G,2]=4;
ttt[E,rk_,a_]:=1;
ttt[F,4,1]=1;
ttt[F,4,2]=1;
ttt[F,4,3]=2;
ttt[F,4,4]=2;
ttt[G,2,1]=1;
ttt[G,2,2]=3;
eee[ty_,rk_,a_]:=eee[ty,rk,a]=(Total/@(2inversecartan[ty,rk]))[[a]]
ccc[ty_,rk_,a_]:=ttt[ty,rk,a] (eee[ty,rk,a]+1-dualCoxeter[ty,rk])
allVerticesTypeEFG ={{E,6,1},{E,6,2},{E,6,3},{E,6,4},{E,6,5},{E,6,6},{E,7,1},{E,7,2},{E,7,3},{E,7,4},{E,7,5},{E,7,6},{E,7,7},{E,8,1},{E,8,2},{E,8,3},{E,8,4},{E,8,5},{E,8,6},{E,8,7},{E,8,8},{F,4,1},{F,4,2},{F,4,3},{F,4,4},{G,2,1},{G,2,2}};
(* constituents of dimension quasipolynomials of KR modules*)
dimWqp[ty_,rk_,a_][n_,res_Integer]:=Block[{ca,ea,ta,ha},
	ta=ttt[ty,rk,a];
	ea=eee[ty,rk,a];
	ca=ccc[ty,rk,a];ha[j_]:=If[0<=j<=ca,hvector[ty,rk,a][[j+1]],0];
	(* m = ta * n+ res *)
	\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j = 0\), \(ca\)]\(KroneckerDelta[Mod[j, ta], res]\ ha[j]*\ Binomial[Simplify[ea + 
\*FractionBox[\(ta\ *n + res - j\), \(ta\)]], ea]\)\)
]/;0<=res<ttt[ty,rk,a]
dimWqpExpanded[ty_,rk_,a_][n_,res_Integer]:=dimWqpExpanded[ty,rk,a][n,res]=dimWqp[ty,rk,a][n,res]//FunctionExpand//Expand
(* dim W_m^(a) *)
dimW[ty_,rk_,a_][m_Integer]:=Block[{ta,res},
	ta=ttt[ty,rk,a];
	res= Mod[m,ta];
	dimWqp[ty,rk,a][(m-res)/ta,res]
]
(* dim W_1^(a)*)
dimW1[E,6]={27,378,3732,378,27,79};
dimW1[E,7]={134,10451,640871,36080,1673,56,968};
dimW1[E,8]={4124,11315621,26994988264,328909133,3658621,34752,249,185877};
dimW1[F,4]={53,1703,299,26};
dimW1[G,2]={15,7};
dimW1[ty_,rk_,a_]:=dimW1[ty,rk][[a]]
(* Q-system for quasipolynomials *)
QsystemfordimWqp[ty_,rk_,a_][n_,res_Integer]:=Block[{Cm,LHS,RHS,Q,t},
	Cm=cartan[ty,rk];
	t[b_]:=ttt[ty,rk,b];
	Q[b_][t_,nn_,k_]:=dimWqpExpanded[ty,rk,b][nn+(k-Mod[k,t])/t,Mod[k,t]];
	LHS=Q[a][t[a],n,res]^2-Q[a][t[a],n,res+1]Q[a][t[a],n,res-1];
	RHS =Product[If[Cm[[a,b]]<0,Q[b][t[b],n,Floor[(Cm[[b,a]]res-k)/Cm[[a,b]]]],1],{b,1,rk},{k,0,-Cm[[a,b]]-1}];
	{LHS,RHS}
]/;0<=res<ttt[ty,rk,a]
QsystemfordimWqpCheck[ty_,rk_,a_][res_Integer]:=Block[{coefs},
	{coefs[1], coefs[2]}=CoefficientList[QsystemfordimWqp[ty,rk,a][n,res],n];
	coefs[1]-coefs[2]
]/;0<=res<ttt[ty,rk,a]


Print["dimension of fundamental modules (return two numbers which must be the same)"]
Do[
Print[s];
Print[{(dimW1@@s),(dimW@@s)[1]}]
,{s,allVerticesTypeEFG}
]


Print["checking dimW satisfies the Q-system (return zero vector if correct)"]
Do[
Print[{s,res}];
Print[(QsystemfordimWqpCheck@@s)[res]]
,{s,allVerticesTypeEFG},{res,Range[0,(ttt@@s)-1]}
]


(* properties of h-vectors *)
Print["positivity, unimodality, symmetry and log-concavity of h-vectors"]
positiveQ[vec_List]:=And@@Positive[vec]
unimodalQ[vec_List]:=Module[{m=Ordering[vec,-1][[1]]},
	LessEqual@@Take[vec,m]&&GreaterEqual@@Drop[vec,m]
]
symmetricQ[vec_List]:=Equal[vec,Reverse[vec]]
logConcaveQ[vec_List]:=Module[{p=Partition[vec,3,1]},
	If[Length[p]==1,
	p[[1,2]]^2>=p[[1,1]]p[[1,3]],
	#2^2>=#1 #3&@@@And@@p]
]
Do[Print[{s,And[positiveQ[#],unimodalQ[#],symmetricQ[#], logConcaveQ[#]]&@(hvector@@s)}],{s,allVerticesTypeEFG}]
