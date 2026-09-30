(* for symbolic computations: The coefficients of several objects are replaced by formal versions such as b, bT and L[m,vars], respectively. *)
Subscript[b, 0][{},{}]:=1;
Subscript[bT, 0][{},{}]:=1;
L::usage="L[m, vars, pretty] is a formal version of seriesL. Setting the optional argument pretty to False returns a less readable version which is needed internally for handling products of these formal objects.";
L[m_Integer, vars_List:{X,Y},pretty_:True]:=If[pretty,Subscript[L,m]@@vars, L[{m},List@vars]];
prettyL::usage="prettyL[expr] replaces all instances of L[m, vars] in expr to a readable version. See also the optional argument pretty in L[m, vars, pretty].";
prettyL[expr_] :=expr /.L[args_List,vars_List]:>Times@@Apply[L,Transpose[{args,vars}],1];
Unprotect[Times];
L[args1_List,vars1_List] * L[args2_List,vars2_List] := L[Join[args1,args2],Join[vars1,vars2]]
Protect[Times];
bimouldLFormal::usage="bimouldLFormal[m, bivars, maxDegree, pretty] returns a formal version of bimouldL by replacing the q-series seriesL[m] with an unevaluated version. Setting the optional argument pretty to False returns a less readable version which is needed internally for handling products of these formal objects.";
bimouldLFormal[m_Integer, bivars_List, maxDegree_Integer:maxWeight, pretty_:True] := Module[{d = Length[bivars[[1]]], res},
	testInputBivars[bivars];
	If[d === 0,Return[1]];
	res = Sum[L[m,{bivars[[1,j]], Total[bivars[[2]]]}, pretty] * truncatedProduct[
		bimouldB[{Take[bivars[[1]],j-1]-bivars[[1,j]], Take[bivars[[2]],j-1]}, maxDegree], bimouldBtilde[{Take[Reverse[bivars[[1]]],d-j]-bivars[[1,j]], Take[Reverse[bivars[[2]]],d-j]}, maxDegree],
		maxDegree, Variables[bivars]],
	{j,1,d}];
	res
];
bimouldgRegFormalLinComb[bivars_List,maxDegree_Integer:maxWeight]:=Module[{d = Length[bivars[[1]]],dTuples,kTuples,qMaxTmp,res=0},
	If[d===0,Return[1]];
	Do[
		dTuples = Join[#,{d}]&/@increasingTuples[d-1,j-1];
		Do[
			kTuples = boundedIncreasingTuples[dTuple];
			res += Sum[
				coeffBimouldFormal[bivars,dTuple,kTuple] * bimouldg[{bivars[[1,kTuple]], Total/@TakeList[bivars[[2]], Join[{dTuple[[1]]}, Differences[dTuple]]]}, maxDegree, 0], 
			{kTuple,kTuples}],
		{dTuple,dTuples}],
	{j,1,d}];
	Expand[res]
];
coeffBimouldFormal::usage="coeffBimouldFormal[bivars, dTuple, kTuple] returns a formal version of coeffBimould as products of formal objects b and bT that correspond to bimouldB and bimouldBtilde, respectively.";
coeffBimouldFormal[bivars_List,dTuple_List,kTuple_List]:=Module[{j = Length[dTuple],d = Length[bivars[[1]]],dTupleTmp,kTupleTmp},
	testInputBivars[bivars];
	If[Length[dTuple]=!=Length[kTuple],Print["The inputs ",dTuple," and ",kTuple," must have the same length."]; Abort[]];
	If[Last[dTuple]=!=d,Print["The last entry in the 2rd input must be ",d]; Abort[]];
	dTupleTmp = Join[{0},dTuple];
	kTupleTmp = Join[{0},kTuple];
	Product[
	Subscript[b,kTupleTmp[[i+1]] - dTupleTmp[[i]]-1][Take[bivars[[1]], {dTupleTmp[[i]]+1,kTupleTmp[[i+1]]-1}] - bivars[[1,kTupleTmp[[i+1]]]],  Take[bivars[[2]], {dTupleTmp[[i]]+1,kTupleTmp[[i+1]]-1}]]
	* Subscript[bT,dTupleTmp[[i+1]] - kTupleTmp[[i+1]]][Reverse[Take[bivars[[1]],{kTupleTmp[[i+1]]+1, dTupleTmp[[i+1]]}]]-bivars[[1,kTupleTmp[[i+1]]]], Reverse[Take[bivars[[2]], {kTupleTmp[[i+1]]+1,dTupleTmp[[i+1]]}]]], {i,1,j}]
];

bimouldgRegFormal[bivars_List,maxDegree_Integer:maxWeight,pretty_:True] := Module[{d = Length[bivars[[1]]], res=0,dTuples,mTuples},
	testInputBivars[bivars];
	If[d === 0,Return[1]];
	Do[
		dTuples = Join[{0},#,{d}]&/@increasingTuples[d-1,j-1];
		mTuples = Reverse /@ increasingTuples[maxDegree-d,j];
		res += Sum[
			Fold[truncatedProduct[#1,#2,maxDegree,Variables[bivars]]&,
			Table[bimouldLFormal[mTuple[[i]], Take[#,{dTuple[[i]]+1,dTuple[[i+1]]}]&/@bivars, maxDegree+dTuple[[i+1]]-dTuple[[i]],False],{i,1,j}]],
		{dTuple,dTuples},{mTuple,mTuples}],
	{j,1,d}
	];
	If[pretty,prettyL[res],res]
];
bimouldgFormal::usage="bimouldgFormal[{{X1,...,Xd},{Y1,...,Yd}},maxDegree] returns the generating series in depth d of certain q-series as a formal product of seriesL up to degree maxDegree.";
bimouldgFormal[bivars_List,maxDegree_Integer:maxWeight,pretty_:True] := Module[{d = Length[bivars[[1]]], mTuples,res},
	mTuples = Reverse/@increasingTuples[maxDegree,d];
	res=Sum[L[mTuple,Transpose[bivars]],{mTuple,mTuples}];
	If[pretty,prettyL[res],res]
];
bimouldgRegFormal2[bivars_List,maxDegree_Integer:maxWeight,pretty_:True] := Module[{d = Length[bivars[[1]]], res=0,dTuples,mTuples},
	testInputBivars[bivars];
	If[d === 0,Return[1]];
	Do[
		dTuples = Join[{0},#,{d}]&/@increasingTuples[d-1,j-1];
		mTuples = Reverse /@ increasingTuples[maxDegree,j];
		res += Sum[
			Product[bimouldLFormal2[mTuple[[i]], Take[#,{dTuple[[i]]+1,dTuple[[i+1]]}]&/@bivars,False],{i,1,j}],
		{dTuple,dTuples},{mTuple,mTuples}],
	{j,1,d}
	];
	If[pretty,prettyL[res],res]
];
bimouldLFormal2[m_Integer,bivars_List,pretty_:True] := Module[{d = Length[bivars[[1]]], res},
	testInputBivars[bivars];
	If[d === 0,Return[1]];
	res = Sum[L[m,{bivars[[1,j]],Total[bivars[[2]]]},pretty] *
		Subscript[b,j-1][Take[bivars[[1]],j-1]-bivars[[1,j]], Take[bivars[[2]],j-1]] * Subscript[bT,d-j][Take[Reverse[bivars[[1]]],d-j]-bivars[[1,j]], Take[Reverse[bivars[[2]]],d-j]],
	{j,1,d}];
	res
];