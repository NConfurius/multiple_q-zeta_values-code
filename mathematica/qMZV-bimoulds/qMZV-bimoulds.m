(* Initialization by loading pre-computed EDS solution (cf. rationalEDS) and make coefficients available via betaCoeff and betaCoeffReg. *)
Needs["DatabaseLink`"];

Get[FileNameJoin[{"rationalEDS","rationalEDS.m"}]];
Phi = Get[FileNameJoin[{"results","rationalEDS", "RationalEDS-even-14_expanded.m"}]];
PhiReg = Get[FileNameJoin[{"results","rationalEDS", "RationalEDS-even-14_expanded_reg.m"}]];
(* maxWeight is the maximal degree of the EDS solution from above. *)
maxWeight = 15;
betaCoeff::usage="betaCoeff[{k1,...,kd}] returns the resp. coefficient beta(k1,...,kd) from the imported data above.";
betaCoeff[lst_List]:=If[Total[lst]<=maxWeight,
	If[lst === {}, Return[1]];
	Coefficient[Phi,Conv2X[Y@@lst]],
	Print["Coefficient of ",lst," does not exist. Total weight must not exceed ",maxWeight];
	Abort[];
];
betaCoeffReg::usage="betaCoeffReg[{k1,...,kd}] returns the resp. stuffle-regularized coefficient beta_*(k1,...,kd) from the imported data above.";
betaCoeffReg[lst_List] := If[Total[lst]<=maxWeight,
	If[lst === {},Return[1]];
	Coefficient[PhiReg,Y@@lst],
	Print["Coefficient of ",lst," does not exist. Total weight must not exceed ",maxWeight,"."];
	Abort[];
];
beta[k_Integer]:= If[k==1, Return[0],-BernoulliB[k]/(2*k!)];
gammaSeries = Series[Exp[Sum[(-1)^(n)/n*beta[n]*u^n,{n,1,maxWeight}]],{u,0,maxWeight}];
gammaList = Join[{1},Table[Coefficient[gammaSeries,u^k],{k,1,maxWeight}]];
gamma = AssociationThread[Range[0,Length[gammaList]-1],gammaList];
gamma::usage="gamma[k] returns the coefficient gamma_k for k between 0 and maxWeight.";

(* auxiliary functions: *)
poly2List::usage"poly2List[poly, vars, maxDeg] returns an association of the form i->(terms of degree i over vars) for i between 0 and maxDeg. This is an auxilarly function for modTotalDegree and truncatedProduct.";
poly2List[poly_,vars_List,maxDeg_Integer]:=Module[{monomList,degreesList, grouped},
	monomList = MonomialList[poly,vars,"DegreeLexicographic"];
	degreesList = Exponent[#,vars]&/@monomList;
	degreesList = Total/@degreesList;
	grouped=GroupBy[Transpose[{monomList,degreesList}],Last->First,Total];
	grouped = AssociationThread[Range[0,maxDeg],Table[If[KeyExistsQ[grouped,i], grouped[i],0],{i,0,maxDeg}]]
];
modTotalDegree::usage="modTotalDegree[expr, maxDegree] returns expr modulo total degree > maxDegree.\nmodTotalDegree[expr, maxDegree, vars] returns expr modulo total degree > maxDegree w.r.t. the specified list of variables vars.";
modTotalDegree[expr_,maxDegree_Integer,vars_List:_.]:=Module[{varsList, degList},
	varsList = If[vars ===_.,Variables[expr],vars];
	degList = poly2List[expr,varsList,maxDegree];
	Expand[Total[Values[KeySelect[degList,#<=maxDegree&]]]]
];
truncatedProduct::usage="truncatedProduct[expr1, expr2, maxDeg] returns the product of expr1 and expr2 up to total degree maxDeg.\ntruncatedProduct[expr1, expr2, maxDeg, vars] returns the product of expr1 and expr2 up to total degree maxDeg with respect to the specified list of variables vars.";
truncatedProduct[expr1_,expr2_,maxDeg_Integer,vars_List:_.] := Module[{monomList1, monomList2,vars1,vars2,varsList},
	varsList = If[vars ===_.,Join[Variables[expr1],Variables[expr2]],vars];
	If[NumericQ[expr1] || NumericQ[expr2], Return[modTotalDegree[expr1*expr2,maxDeg,varsList]]];
	monomList1 = poly2List[expr1,varsList,maxDeg];
	monomList2 = poly2List[expr2,varsList,maxDeg];
	Expand[Total[Flatten[Table[monomList1[i]*monomList2[j], {i,0,maxDeg}, {j,0,maxDeg-i}]]]]
];
MakeVariables::usage="MakeVariables[n] returns a list of variables {X_1,...,X_n}.\nMakeVariables[n, Var] returns list of variables {Var_1,...,Var_n}.\nMakeVariables[n, Var, shift] returns a list of variables {Var_(1+shift),...,Var_(n+shift)}.";
MakeVariables[n_Integer,Var_:X,shift_Integer:0]:=Table[Subscript[Var,i], {i,1+shift,n+shift}];
MakeBiVariables::usage="MakeBiVariables[n] returns a list of bi-variables {{X_1,...,X_n},{Y_1,...,Y_n}}.\nMakeBiVariables[n, Vars] returns list of bi-variables with X and Y replaces by the two entries of Vars.\nMakeVariables[n, Var, shift] returns a list of bi-variables in the variables Vars with index shifted by shift, cf. MakeVariables.";
MakeBiVariables[n_Integer,Vars_List:{X,Y},shift_Integer:0] := {MakeVariables[n,Vars[[1]],shift],MakeVariables[n,Vars[[2]],shift]};
testInputBivars::usage="testInputBivars[bivars] is a test-function to check whether the input is list with 2 entries consisting of the same number of variables, see MakeBiVariables for an exemplary input. Aborts if input is not of the correct form. Auxilliary function for several bimoulds.";
testInputBivars[bivars_List]:=If[Length[bivars]=!=2 || Length[bivars[[1]]]=!=Length[bivars[[2]]],
	Print["The input ",bivars," must be a list with 2 entries, each consisting of the same number of variables."];
	Abort[];
];
monomialDegreeTuples::usage="monomialDegreeTuples[len, maxDegree] returns a list of all possible exponents of monomials in len many variables of total degree at most maxDegree.";
monomialDegreeTuples[len_Integer,maxDegree_Integer] := Join@@Table[Reverse[FrobeniusSolve[ConstantArray[1,len],k]], {k,0,maxDegree}];
increasingTuples::usage="increasingTuples[d, j] returns all tuples (d1,d2,...,dj) of length j satisfying d1<d2<...<dj<=d.";
increasingTuples[d_Integer,j_Integer]:=If[j===0||d===0,{{}}, Subsets[Range[1,d],{j}]];
boundedIncreasingTuples::usage="boundedIncreasingTuples[tuple] returns a list of all tuples of the same length as tuple where the i-th entry is bounded by the (i-1)-th and i-th entry of tuple.";
boundedIncreasingTuples[tuple_List]:=Module[{res},
	res = TakeList[Range[tuple[[-1]]],Differences[Join[{0},tuple]]];
	Tuples[res]
];
balancedIndexAux::usage="balancedIndexAux[index] returns the bi-index that corresponds to the monomial in generating series with coefficient zeta_q(index). This auxillary function is used to search generating series for resp. coefficient in balancedQMZV.";
balancedIndexAux::indexAdm="The first entry of `1` must be a positive integer.";
balancedIndexAux[index_List]:=Module[{res,zeroCount=0},
	If[index==={}, Return[{{},{}}], res={index[[1]]}];
	If[index[[1]] <1, Message[balancedIndexAux::indexAdm,index]; Abort[]];
		Do[
			If[index[[n]]==0,zeroCount++,
				AppendTo[res,{zeroCount,index[[n]]}];
				zeroCount=0
			],
			{n,2,Length[index]}
		];
	AppendTo[res,zeroCount];
	res = Flatten[res];
	Transpose[{res[[2*#-1]],res[[2*#]]}&/@Range[Length[res]/2]]
];
tau[bivars_List]:=Reverse /@ Reverse @ bivars;
swap[bivars_List] := Module[{d = Length[bivars[[1]]]},
	testInputBivars[bivars];
	If[d === 0, Return[{{},{}}]];
	{Table[Total[Take[bivars[[2]],d-j]],{j,0,d-1}],Join[{bivars[[1,d]]}, (bivars[[1,-#1-1]]-bivars[[1,-#1]]&)/@Range[d-1]]}
];
(* compute certain polynomials and q-series: *)
seriesL::usage="seriesL[m, {X,Y}, maxDegree, qMax] returns the series expansion of exp(X+m*Y)*q^m/(1-exp(X)*q^m) up to maxDegree in {X,Y} and qMax in q. If qMax is omitted, qMax is set to maxDegree by default.";
seriesL[m_Integer, vars_List:{X,Y}, maxDegree_Integer:maxWeight, qMax_Integer:_.] := Module[{res, tmpX, tmpY, t, qMaxTmp},
	If[qMax === _.,qMaxTmp = maxDegree, qMaxTmp = qMax];
	res = Expand[Normal[
		Series[(Exp[t*tmpX+m*t*tmpY]*q^m)/(1-Exp[t*tmpX]*q^m),
		{t,0,maxDegree},{q,0,qMaxTmp}
		]
		]] /. t->1;
	Expand[res /. {tmpX:> vars[[1]], tmpY:>vars[[2]]}]
];
EulerianPol::usage="EulerianPol[n, var] returns the n-th Eulerian polynomial in the variable var.";
EulerianPol[0,var_:t]:=1;
EulerianPol[n_Integer,var_:t]:=Module[{t}, Expand[D[EulerianPol[n-1,t],t]*t*(1-t)+EulerianPol[n-1,t]*(1+(n-1)*t)] /.t:>var];
qEulerianPol::usage="qEulerianPol[n, var] returns a modified version of the EulerianPol that is used to compute the q-series g, cf. seriesG.";
qEulerianPol[n_Integer,var_:t]:=If[n===0, Return[1], Collect[var*EulerianPol[n-1,var]/(n-1)!,var]];
seriesG::usage="seriesG[{k1,...,kd}, {m1,...,md}, qMax] returns the respective q-series up to q^qMax with ki>=1 and mi>=0. The algorithm is based on an implementation from a pari/gp package by Henrik Bachmann. If the argument qMax is zero, a formal version is returned which can be expanded via ExpandSeriesG.";
seriesG[ind1_List,ind2_List,qMax_Integer:20]:=Module[{d = Length[ind1],tmp},
	If[d=== 0, Return[1]];
	If[qMax===0, Return[g[ind1,ind2]]];
	tmp =ConstantArray[0,d+1];
	tmp[[d+1]]=1;
	Do[
		Do[
		tmp[[j]]+=tmp[[j+1]]*m^ind2[[j]] * Series[qEulerianPol[ind1[[j]],q^m]/(1-q^m)^(ind1[[j]]),{q,0,qMax}],
		{j,1,d}],
	{m,1,qMax}];
	Normal[tmp[[1]]+O[q]^(qMax+1)]
];
ExpandSeriesG::usage="ExpandSeriesG[expr, qMax] replaces all instances of g[{k1,...,kd}, {m1,...,md}] in expr with the respective q-series up to q^qMax.";
ExpandSeriesG[expr_,qMax_Integer:10] := Expand[expr/.g[lst1_List,lst2_List] -> seriesG[lst1,lst2,qMax]];

(* moulds and bimoulds: *)
mouldB::usage="mouldB[vars, maxDegree] returns the mould b(vars) up to degree maxDegree, where vars is a list of d variables. Note that maxDegree must not exceed maxWeight-d, cf. betaCoeffReg.";
mouldB[vars_List,maxDegree_Integer:maxWeight]:=Module[{d = Length[vars],tuples,monomialsList,coeffsList},
	If[d=== 0, Return[1]];
	If[d === 1, Return[Total[Join[{0},Table[-BernoulliB[k]/(2*k!)*vars[[1]]^(k-1), {k,2,maxDegree+1}]]]]];
	tuples = monomialDegreeTuples[d,maxDegree];
	monomialsList = Times@@@Power[ConstantArray[vars,Length[tuples]],tuples];
	coeffsList=betaCoeffReg/@(tuples+1);
	Expand[Total[coeffsList * monomialsList]]
];
bimouldB::usage="bimouldB[bivars, maxDegree] returns the bimould b up to degree maxDegree in the bi-variables from bivars.";
bimouldB[bivars_List,maxDegree_Integer:maxWeight]:=Module[{d = Length[bivars[[1]]],res},
	testInputBivars[bivars];
	If[d === 0, Return[1]];
	res = Sum[
		gamma[i]*truncatedProduct[mouldB[Table[Total[Take[bivars[[2]],j-i-n]], {n,0,j-i-1}],maxDegree], mouldB[Take[bivars[[1]],-(d-j)],maxDegree], maxDegree, Variables[bivars]],
		{i,0,d},{j,i,d}
	];
	Expand[res]
];
bimouldBtilde::usage="bimouldBtilde[bivars, maxDegree] returns the bimould tilde(b) up to degree maxDegree in the bi-variables from bivars.";
bimouldBtilde[bivars_List,maxDegree_Integer:maxWeight] := Module[{d=Length[bivars[[1]]],res},
	testInputBivars[bivars];
	res = Sum[(-1)^i/(2^i*i!)*bimouldB[{Take[bivars[[1]],-(d-i)], -Take[bivars[[2]],d-i]},maxDegree],{i,0,d}];
	Expand[res]
];
bimouldL::usage="bimouldL[m, bivars, maxDegree, qMax] returns the bimould L_m up to degree maxDegree in the bi-variables from bivars and up to q^qMax. If qMax is omitted, qMax is set to maxDegree by default.";
bimouldL[m_Integer,bivars_List,maxDegree_Integer:maxWeight,qMax_Integer:_.] := Module[{d = Length[bivars[[1]]],res,qMaxTmp},
	testInputBivars[bivars];
	If[d === 0,Return[1]];
	qMaxTmp =If[qMax === _.,maxDegree,qMax];
	res = Sum[Fold[truncatedProduct[#1,#2,maxDegree,Variables[bivars]]&,
			bimouldB[{Take[bivars[[1]],j-1]-bivars[[1,j]], Take[bivars[[2]],j-1]}, maxDegree], {seriesL[m,{bivars[[1,j]], Total[bivars[[2]]]} ,maxDegree, qMaxTmp],
			bimouldBtilde[{Take[Reverse[bivars[[1]]],d-j]-bivars[[1,j]], Take[Reverse[bivars[[2]]],d-j]},maxDegree]}],
		{j,1,d}];
	Expand[res]
];
bimouldg::usage="bimouldg[bivars, maxDegree, qMax] returns the bimould g up to degree maxDegree in the bi-variables from bivars and up to q^qMax. This bimould is the generating function of certain q-MZVs (see Bachmann 2019 and Bachmann-Kuehn 2020).";
bimouldg[bivars_List,maxDegree_Integer:maxWeight,qMax_Integer:20] := Module[{d=Length[bivars[[1]]],tuples,xVars,yVars,xExp,yExp,gArgs, monomialsList,coeffs},
	testInputBivars[bivars];
	If[d===0,Return[1]];
	{xVars,yVars}=bivars;
	tuples=monomialDegreeTuples[2 d,maxDegree];
	xExp=tuples[[All,1;;d]];
	yExp=tuples[[All,-d;;]];
	monomialsList=Times@@Transpose[ Power[ConstantArray[xVars,Length[tuples]],xExp]] * Times@@Transpose[Power[ConstantArray[yVars,Length[tuples]],yExp]];
	gArgs = seriesG[#[[1]],#[[2]],qMax]&/@ Transpose[{xExp+1,yExp}];
	coeffs=1/Apply[Times,Factorial/@yExp,1];
	Total[gArgs*monomialsList*coeffs]
];
coeffBimould::usage="coeffBimould[bivars, dTuple, kTuple, maxDegree] returns the coefficient B(dTuple,kTuple) in the bi-variables bivars up to maxDegree. These coefficients appear when comparing the bimoulds g and g^*, cf. bimouldgReg.";
coeffBimould[bivars_List, dTuple_List, kTuple_List, maxDegree_Integer:5] := Module[{j = Length[dTuple], d = Length[bivars[[1]]], dTupleTmp, kTupleTmp},
	testInputBivars[bivars];
	If[Length[dTuple]=!=Length[kTuple],Print["The arguments ",dTuple," and ",kTuple," must have the same length."];Abort[]];
	If[Last[dTuple]=!=d,Print["The last entry ",dTuple," must be ",d];Abort[]];
	dTupleTmp = Join[{0},dTuple];
	kTupleTmp = Join[{0},kTuple];
	Fold[truncatedProduct[#1,#2,maxDegree,Variables[bivars]]&,
		Flatten[Table[{bimouldB[{Take[bivars[[1]], {dTupleTmp[[i]]+1, kTupleTmp[[i+1]]-1}] - bivars[[1,kTupleTmp[[i+1]]]], Take[bivars[[2]], {dTupleTmp[[i]]+1, kTupleTmp[[i+1]]-1}]}, maxDegree],
		bimouldBtilde[{Reverse[Take[bivars[[1]], {kTupleTmp[[i+1]]+1, dTupleTmp[[i+1]]}]] - bivars[[1,kTupleTmp[[i+1]]]], Reverse[Take[bivars[[2]], {kTupleTmp[[i+1]]+1, dTupleTmp[[i+1]]}]]}, maxDegree]}
		,{i,1,j}]]
	]
];
bimouldgReg::usage="bimouldgReg[bivars, maxDegree, qMax] returns the bimould g^* in the bi-variables bivars up to degree maxDegree and up to q^qMax. The algorithm uses the alternative description of the bimould g^* as a linear combination in terms of the bimould g and coefficients given by coeffBimould. This results in improved performance compared to bimouldgRegDef which uses the original definition. If the argument qMax is zero (or omitted), the q-series involved are replaced by formal objects which can be expanded via ExpandSeriesG.";
bimouldgReg[bivars_List,maxDegree_Integer:maxWeight,qMax_Integer:0] := Module[{d = Length[bivars[[1]]], bivarsTmp,dTuples,kTuples,res=0,bimouldgTmp,gTmpGeneric},
	If[d===0,Return[1]];
	Do[
		dTuples = Join[#,{d}]&/@increasingTuples[d-1,j-1];
		gTmpGeneric = bimouldg[MakeBiVariables[j],maxDegree,qMax];
		Do[
			kTuples = boundedIncreasingTuples[dTuple];
			Do[
			bivarsTmp={bivars[[1,kTuple]],Total/@TakeList[bivars[[2]], Join[{dTuple[[1]]},Differences[dTuple]]]};
			bimouldgTmp = gTmpGeneric/.Thread[Flatten[MakeBiVariables[j]] -> Flatten[bivarsTmp]];
			res += truncatedProduct[coeffBimould[bivars,dTuple,kTuple,maxDegree], bimouldgTmp,maxDegree,Variables[bivars]],
			{kTuple,kTuples}],
		{dTuple,dTuples}],
	{j,1,d}];
	res
];
bimouldCMES::usage="bimouldCMES[bivars, maxDegree, qMax] returns the bimould of combinatorial bi-multiple Eisenstein series in the bi-variables bivars up to degree maxDegree and up to q^qMax. If the argument qMax is zero (or omitted), the q-series involved are replaced by formal objects which can be expanded via ExpandSeriesG.";
bimouldCMES[bivars_List,maxDegree_Integer:maxWeight,qMax_Integer:0] := Module[{d = Length[bivars[[1]]]}, 
	testInputBivars[bivars];
	If[d === 0,Return[1]];
	Sum[
		truncatedProduct[bimouldgReg[bivars[[All, Range[n]]], maxDegree, qMax], bimouldB[bivars[[All, Range[n+1,d]]], maxDegree], maxDegree, Variables[bivars]],
	{n,0,d}]
];
bimouldBalanced::usage="bimouldBalanced[bivars, maxDegree, qMax] returns the bimould of balanced multiple q-zeta values in the bi-variables bivars up to degree maxDegree and up to q^qMax. If the argument qMax is zero (or omitted), the q-series involved are replaced by formal objects which can be expanded via ExpandSeriesG.";
bimouldBalanced[bivars_List,maxDegree_Integer:maxWeight,qMax_Integer:0] := Module[{d = Length[bivars[[1]]],res},
	testInputBivars[bivars];
	If[d===0,Return[1]];
	res = bimouldCMES[MakeBiVariables[d],maxDegree,qMax];
	res=res/.Thread[Flatten[MakeBiVariables[d]] -> Join[bivars[[1]], Join[{bivars[[2,1]]},bivars[[2,#+1]]-bivars[[2,#]] &/@Range[d-1]]]];
	Expand[res]
];

(* default directories (relative / absolute) for data *)
dataDirAbsCMES=FileNameJoin[{Directory[],"results", "combinatorial_bi-multiple_Eisenstein"}];
dataDirRelCMES=FileNameDrop[dataDirAbsCMES,FileNameDepth[Directory[]]];
dataDirAbsBalanced=FileNameJoin[{Directory[],"results","balanced_qMZV"}];
dataDirRelBalanced=FileNameDrop[dataDirAbsBalanced, FileNameDepth[Directory[]]];

(* auxiliary function to read databases from generating_qMZV.m *)
importFromDataBase[index_List,dataDirRel_String] := Module[{conn, indexStr, res, dataDirAbs = FileNameJoin[{Directory[], dataDirRel}]},
	Needs["DatabaseLink`"];
	conn = OpenSQLConnection[JDBC["SQLite", dataDirAbs]];
	indexStr = ToString[index];
	res=SQLExecute[conn,"SELECT value FROM data WHERE key = ?",{indexStr}];
	CloseSQLConnection[conn];
	If[Length[res]>0,
		ToExpression[res[[1,1]]],
		Print["Index ",index," not found in database located at ",dataDirRel];
		Abort[];
	]
];
CMES::usage="CMES[{k1,...,kd}, {m1,...,md}, qMax] returns the resp. combinatorial bi-multiple Eisenstein series by expanding the q-series g up to q^qMax in the pre-computed generating series from GenerateCMES. If the argument qMax is zero (or omitted), the non-expanded version is returned. \nCMES[{k1,...,kd}, {m1,...,md}, qMax, fileDest] allows to change the (relative) path of the resp. coefficient list with optional argument fileDest.";
CMES::argx="The inputs `1` and `2` must have equal length.";
CMES::keyMissing="Coefficient for indices `1` and `2` is missing in the data.";
CMES[index1_List,index2_List,qMax_Integer:0,fileDest_:dataDirRelCMES] := Module[{d = Length[index1],dbFile,assocTmp,coeffLst,res},
	If[Length[index1]=!=Length[index2], Message[CMES::argx,index1,index2]; Abort[]];
	If[d===0, Return[1]];
	dbFile = FileNameJoin[{fileDest,"CMES_dep"<>ToString[d]<>".db"}];
	If[!FileExistsQ[dbFile],
		Print["No file found at ",dbFile,". Use GenerateCMES["<>ToString[d]<>", maxDeg] with maxDeg at least "<>ToString[Total[index1]-d+Total[index2]]<>" and try again."];
		Abort[];
	];
	coeffLst = Join[index1-1, index2];
	res = importFromDataBase[coeffLst,dbFile]*(Times@@Factorial/@index2);
	ExpandSeriesG[res,qMax]
];
balancedQMZV::usage="balancedQMZV[{s1,...,sd}, qMax] returns the resp. balanced multiple q-zeta value by expanding the q-series g up to q^qMax in the pre-computed generating series from GenerateBalancedQMZV. If the argument qMax is zero (or omitted), the non-expanded version is returned.\nbalancedQMZV[{s1,...,sd}, qMax, fileDest] allows to change the (relative) path of the resp. coefficient list with optional argument fileDest.";
balancedQMZV::keyMissing="Coefficient for index `1` is missing in the data.";
balancedQMZV[index_List,qMax_Integer:0,fileDest_:dataDirRelBalanced] := Module[{d,dbFile,assocTmp,coeffLst,biIndexTmp,res},
	biIndexTmp = balancedIndexAux[index];
	d = Length[biIndexTmp[[1]]];
	If[d===0, Return[1]];
	dbFile = FileNameJoin[{fileDest,"balanced_qMZV_dep"<>ToString[d]<>".db"}];
	If[!FileExistsQ[dbFile],
		Print["No file found at ",dbFile,". Use GenerateBalancedQMZV["<>ToString[d]<>", maxDeg] with maxDeg at least "<>ToString[Total[Flatten[biIndexTmp]]-d]<>" and try again."];
		Abort[];
	];
	coeffLst = Join[biIndexTmp[[1]]-1,biIndexTmp[[2]]];
	res = importFromDataBase[coeffLst,dbFile];
	ExpandSeriesG[res,qMax]
];
balancedQMZV[word_B, qMax_Integer:0, fileDest_:dataDirRelBalanced] := balancedQMZV[List@@word, qMax, fileDest];
balancedQMZV[expr_Plus,qMax_Integer:0,fileDest_:dataDirRelBalanced] := Expand[Total[balancedQMZV[#, qMax, fileDest] & /@ List@@expr]];
balancedQMZV[num_?NumberQ*a_, qMax_Integer:0, fileDest_:dataDirRelBalanced] := Expand[num * balancedQMZV[a, qMax, fileDest]];
shuffleQMZV[index_List, qMax_Integer:0, fileDest_:dataDirRelBalanced]:=Module[{word = V@@index, wordExp},
	wordExp = expHoffman[word];
	balancedQMZV[wordExp, qMax, fileDest]
];
logHoffman::usage = "Isomorphism from balanced quasi-shuffle product to shuffle product. Note that this function is only defined for positive entries.";
logHoffman::invalid="Input `1` contains non-positive or non-integer indices. All indices must be positive integers.";
expHoffman[word_V] := Module[{indices, subwords, compositionsList, resultBlocks, resultConcat}, 
	indices = List @@ word;
	If[Length[indices] == 0, Return[B @@ indices]];
	subwords = SplitBy[indices, # == 0 &];
	compositionsList = Table[
		If[First[ind] > 0, 
			compositions[Length[ind]], 
			{0}
		], 
	{ind, subwords}];
	resultBlocks = Table[
		If[compositionsList[[n]] === {0}, 
			{{1, subwords[[n]]}},
			Table[{1 / Times @@ (Factorial /@ comp),
			Table[
				Total[subwords[[n, Sum[comp[[j]], {j, 1, k - 1}] + 1 ;; Sum[comp[[j]], {j, 1, k}]]]],
		    {k, 1, Length[comp]}]},
			{comp, compositionsList[[n]]}]
		],
	{n, Length[subwords]}];
	resultConcat = Transpose /@ Tuples[resultBlocks];
	Total[Times @@ #[[1]] * B @@ Flatten[#[[2]]] & /@ resultConcat]
];
logHoffman[word_B] := Module[{indices, subwords, compositionsList, resultBlocks, resultConcat}, 
	indices = List @@ word;
	If[Length[indices] == 0, Return[B @@ indices]];
	subwords = SplitBy[indices, # == 0 &];
	compositionsList = Table[
		If[First[ind] > 0, 
			compositions[Length[ind]], 
			{0}
		],
	{ind, subwords}];
	resultBlocks = Table[
		If[compositionsList[[n]] === {0}, 
			{{1, subwords[[n]]}},
			Table[{(-1)^(Length[subwords[[n]]]-Length[comp]) / Times @@ comp,
			Table[
				Total[subwords[[n, Sum[comp[[j]], {j, 1, k - 1}] + 1 ;; Sum[comp[[j]], {j, 1, k}]]]],
		    {k, 1, Length[comp]}]},
			{comp, compositionsList[[n]]}]
		],
	{n, Length[subwords]}];
	resultConcat = Transpose /@ Tuples[resultBlocks];
	Total[Times @@ #[[1]] * V @@ Flatten[#[[2]]] & /@ resultConcat]
];
CMESdepth2Explicit::usage = "CMESdepth2Explicit[k1,k2,m1,m2] returns the combinatorial bi-multiple Eisenstein series CMES[{k1,k2},{m1,m2}] via the explicit formula as a Q-linear combination of the q-series from seriesG.";
CMESdepth2Explicit[k1_Integer, k2_Integer, m1_Integer, m2_Integer] := Module[{res},
	res = g[{k1,k2}, {m1,m2}] + Sum[(-1)^j * g[{k1-j}, {m1+m2}] * beta[k2+j] * Binomial[k2+j-1,j], {j,0,k1-1}] + Sum[(-1)^j * g[{k2-j},{m1+m2}] * beta[k1+j] * Binomial[k1+j-1,j], {j,0,k2-1}];
	If[k1 === 1,
		res += Sum[g[{k2}, {m1+m2-j}] * m1!/(m1-j)! * beta[j+1], {j,0,m1}]
	];
	If[k2 === 1,
		res += g[{k1},{m1}] * beta[m2+1] * m2! - 1/2 * g[{k1}, {m1+m2}] + Sum[(-1)^j * g[{k1}, {m1+m2-j}] * m2!/(m2-j)! * beta[j+1], {j,0,m2}]
	];
	If[m2 === 0,
		res+=g[{k1},{m1}] * beta[k2]
	];
	If[m1 === 0 && m2 === 0,
		res += betaCoeffReg[{k1, k2}]
	];
	If[k1 === 1 && m2 === 0,
		res += beta[m1+1] * beta[k2] * m1!
	];
	If[k1 === 1 && k2 === 1,
		res += Sum[Binomial[m2+j,m2] * betaCoeffReg[{m2+1+j, m1+1-j}] * m1! * m2!, {j,0,m1}]
	];
	If[k1 === 1 && k2 === 1 && m1 === 0 && m2 === 0,
		res += -1/48
	];
	res
];