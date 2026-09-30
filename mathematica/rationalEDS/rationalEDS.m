$RecursionLimit=2^15;
WordWeight::usage="WordWeight[word] returns the weight of word, depending on the head X, Y, U, B or V.";
WordWeight[1]:=0;
WordWeight[word_X]:=Length[word];
WordWeight[word_Y|word_U]:=Plus @@ word;
WordWeight[word_B|word_V]:=Plus @@ word + Count[word,0];
WordWeight[num_?NumberQ word_]:=WordWeight[word];
WordDepth::usage="WordDepth[word] returns the depth of word, depending on the head X, Y, U, B or V.";
WordDepth[word_X]:=Count[word,1];
WordDepth[word_Y|word_U]:=Length[word];
WordDepth[word_B|word_V]:=Length[word]-Count[word,0];
MakeLinear::usage="MakeLinear[func] linearly extends the definition of func.";
MakeLinear[func_]:=(func[expr_Plus]:=Expand[Total[func /@ List @@ expr]];func[num_?NumberQ a_]:=Expand[num func[a]];func[num_?NumberQ]:=num;);
MakeBilinear::usage="MakeBilinear[func] bilinearly extends the definition of func.";
MakeBilinear[func_]:=(func[expr_Plus,b_]:=Expand[Total[(func[#1,b]&) /@ List @@ expr]];func[a_,expr_Plus]:=Expand[Total[(func[a,#1]&) /@ List @@ expr]];func[num_?NumberQ a_,b_]:=Expand[num func[a,b]];func[a_,num_?NumberQ b_]:=Expand[num func[a,b]];func[num1_?NumberQ,num2_?NumberQ]:=num1 num2;);
MakeLinear /@ {Conv2X,Conv2Y,Conv2U,Conv2B,Conv2V,projAdmissibleB};
Conv2X::usage="Conv2X[word] converts words in Y or U to X.";
Conv2Y::usage="Conv2Y[word] converts words in X or U to Y.";
Conv2U::usage="Conv2U[word] converts words in X or Y to U.";
Conv2B::usage="Conv2B[word] converts words in V to B.";
Conv2V::usage="Conv2V[word] converts words in B to V.";
Conv2Y[word_X]:=Module[{res={},zeroCount=0,index},
	If[Last[word]===0,Return[0]];
	For[index=1,index<=Length[word],index++,
		If[word[[index]]===0,zeroCount++,
			res=Append[res,zeroCount+1];zeroCount=0
		];
	];
	Y @@ res
];
Conv2Y[U[num_?IntegerQ]]:=Total[(((-1)^(Length[#1]+1) Y @@ #1)/Length[#1]&) /@ compositions[num]];
Conv2Y[word_U]:= NonCommutativeMultiply @@ Conv2Y /@ U /@ List @@ word;
Conv2Y[terms_List]:= Conv2Y /@ terms;
Conv2X[word_Y]:=X @@ Flatten[Table[{ConstantArray[0,word[[k]]-1],1},{k,1,Length[word]}]];
Conv2X[word_U]:=Conv2X[Conv2Y[word]];
Conv2U[Y[num_?IntegerQ]]:=Total[(U @@ #1/Length[#1]!&) /@ compositions[num]];
Conv2U[word_Y]:=NonCommutativeMultiply @@ Conv2U /@ Y /@ List @@ word;
Conv2U[word_X]:=Module[{res={},zeroCount=0,index},
	If[Last[word]===0,Return[0]];
	For[index=1,index<=Length[word],index++,
		If[word[[index]]===0,
			zeroCount++,
			res=Append[res,zeroCount+1];
			zeroCount=0
		];
	];
	res=Tuples[compositions /@ res];Total[(U @@ Flatten[#1]/Times @@ (Length[#1]!&) /@ #1&) /@ res]
];
Conv2U[terms_List] := Conv2U/@terms;
Conv2B[V[num_?IntegerQ]]:=If[num===0,B[0],Total[(((-1)^(Length[#1]+1) B @@ #1)/Length[#1]&) /@ compositions[num]]];
Conv2V[B[num_?IntegerQ]]:=If[num===0,V[0],Total[(V @@ #1/Length[#1]!&) /@ compositions[num]]];
Conv2B[word_V]:=NonCommutativeMultiply @@ Conv2B /@ V /@ List @@ word;
Conv2V[word_B]:=NonCommutativeMultiply @@ Conv2V /@ B /@ List @@ word;
projAdmissibleB[word_B]:=If[word[[1]]=!=0,word,0];
projAdmissibleB::usage="Identity on words not starting in b0, otherwise returns 0.";
br::usage="br[x,y] is a formal expression for the Lie bracket of x and y. To evaluate the bracket, apply LieExpand.";
lynbra::usage = "lynbra[lynWord] is a formal expression for the Lyndon bracket of lynWord, assuming that lynWord is Lyndon. To expand the bracket, apply lynbraExpand.";
OX::usage="Formal tensor product symbol, e.g. OX[A,B] corresponds to the tensor product of A and B.";
LieExpand::usage="Evaluates all instances of br[x,y] as the commutator bracket with NonCommutativeMultiply as product.";
lynbraExpand::usage = "Evaluates all instances of lynbra[lynWord] via the standard factorization and LieExpand.";
LieExpand[expr_]:=Expand[expr//. br[x_,y_]:>x**y-y**x];
lynbraExpand[expr_] := Module[{res},
   res = expr /. lynbra[lst_] :> LyndonBracket[lst] /. {num_Integer} :> Head[lst]@@num;
	LieExpand[res]];
X[]:=1;Y[]:=1;U[]:=1;B[]:=1;V[]:=1;
Unprotect[NonCommutativeMultiply];
NonCommutativeMultiply::usage="NonCommutativeMultiply is a built-in function that corresponds to concatenation of words in this package. a ** b ** c is a general associative, but non-commutative, form of multiplication.";
c_?NumberQ**x_:=c x
x_**c_?NumberQ:=c x
(c_?NumberQ x_)**y_:=Expand[c x**y]
x_**(c_?NumberQ y_):=Expand[c x**y]
(x_+y_)**z_:=x**z+y**z
x_**(y_+z_):=x**y+x**z
word1_X**word2_X:=If[Plus @@ WordWeight /@ {word1,word2} <= currentWeight, Join @@ {word1,word2},0];
word1_Y**word2_Y:=If[Plus @@ WordWeight /@ {word1,word2} <= currentWeight, Join @@ {word1,word2},0];
word1_U**word2_U:=If[Plus @@ WordWeight /@ {word1,word2} <= currentWeight, Join @@ {word1,word2},0];
word1_B**word2_B:=If[Plus @@ WordWeight /@ {word1,word2} <= currentWeight, Join @@ {word1,word2},0];
word1_V**word2_V:=If[Plus @@ WordWeight /@ {word1,word2} <= currentWeight, Join @@ {word1,word2},0];
OX[lst1__]**OX[lst2__]:=OX @@ MapThread[NonCommutativeMultiply,{{lst1},{lst2}}];
SetAttributes[OX,Flat];
Protect[NonCommutativeMultiply];
OX[c_?NumberQ a_,b_]:=c OX[a,b];
OX[a_,c_?NumberQ b_]:=c OX[a,b];
OX[word1_+word2_,word3_]:=OX[word1,word3]+OX[word2,word3];
OX[word1_,word2_+word3_]:=OX[word1,word2]+OX[word1,word3];
LyndonWordsByLength::usage="LyndonWordsByLength[n,s] generates all Lyndon words over the alphabet {0, 1, ..., s-1} of length at most n.";
LyndonWordsByLength[n_Integer,s_Integer:2]:=Module[{res={},word={-1}},
	While[Length[word]>0,
		word[[-1]]++;
		res=Append[res,word];
		word=word[[Mod[Range[n]-1,Length[word]]+1]];
		While[Length[word]>0&&Last[word]===s-1,
			word=Drop[word,-1]
		];
	];
	res
];
LyndonWordsOfLength[n_Integer,s_Integer:2]:=Select[
		LyndonWordsByLength[n,s],Length[#]==n &
	];
LyndonWordsByWeight::usage="LyndonWordsByWeight[k,minIndex] generates all Lyndon words over the alphabet {minIndex, ..., k} of weight at most k where the weight of each letter equals its index, except for zero having weight 1.";
LyndonWordsByWeight[k_Integer,minIndex_Integer:1]:=Module[
	{res={},word={minIndex-1}},
	While[Length[word]>0,
		word[[-1]]++;
		res=Append[res,word];
		word=word[[Mod[Range[k]-1,Length[word]]+1]];
		While[Total[word] + Count[word,0]>k,
			word=Drop[word,-1]
		];
		If[Total[word] + Count[word,0]===k&&Last[word]=!=0,
			word=Drop[word,-1]
		];
	];
	res
];
LyndonWordsOfWeight[k_Integer,minIndex_Integer:1]:=Select[
	LyndonWordsByWeight[k,minIndex], Total[#] + Count[#,0] == k &
];
LyndonWordTest::usage="LyndonWordTest[w] decides whether w is a Lyndon word. Returns True or False.";
LyndonWordTest[word_List] := Module[{tmp = RotateLeft[word], n},
	For[n=1, n<Length[word], n++,
		If[LexicographicOrder[word,tmp] =!= 1,
			Return[False];
		];		
		tmp = RotateLeft[tmp];
	];
	Return[True];
];
LyndonWordTest[{}] := False;
StandardFactorization::usage="StandardFactorization[lynWord] returns the index of the standard factorization of the Lyndon word lynWord.";
StandardFactorization::error="The input must be a Lyndon word.";
StandardFactorization[lynWord_List]:=Module[{tmp,n},
	If[!LyndonWordTest[lynWord],  Message[StandardFactorization::error]; Return[$Failed]];
	tmp=Drop[lynWord,1];
	For[n=1, n<Length[lynWord], n++,
		If[LyndonWordTest[tmp],
			Return[n];
		];
		tmp = Drop[tmp,1];
	];
];
LyndonBracket::usage="LyndonBracket[word] returns the Lyndon bracket of word as a symbolic expression, apply LieExpand to expand the expression.";
LyndonBracket[word_List] := Module[{indexTmp,res},
	If[Length[word] == 1, Return[word]];
	indexTmp = StandardFactorization[word];
	res = br[LyndonBracket[Take[word,indexTmp]], LyndonBracket[Drop[word,indexTmp]]]
];
LyndonBracket[word_X|word_U|word_Y] := LyndonBracket[List@@word] /. {num_Integer} :> Head[word]@num;
nonCommutativePower[expr_,0]:=1;
nonCommutativePower[expr_,n_Integer]:=Fold[
	NonCommutativeMultiply,expr,ConstantArray[expr,n-1]
];
nonCommutativeExp[expr_]:=Module[{res=1,currentTerm=Expand[expr],i},
	For[i=1,currentTerm=!=0,
		i++;currentTerm=Distribute[currentTerm**expr//. a_Plus word_Y:>Distribute[a word]],
		Distribute[res+=Expand[currentTerm/i!]];
	];
	res
];
nonCommutativeLog[1]=0;
nonCommutativeLog[1+expr_]:=Module[{res=0,currentTerm=Expand[expr],i},
	For[i=1,currentTerm=!=0,++i;currentTerm=currentTerm**(-expr),
	res+=Expand[currentTerm/i]];
	res
];
invertPowerSeries[1]:=1;
invertPowerSeries[1+expr_]:=Module[{currentTerm=Expand[-expr],res},
	For[res=1,currentTerm=!=0,
		currentTerm=currentTerm**(-expr),
		res+=currentTerm
	];
	res
];
compositions[0]:={{}};
compositions[n_Integer]:=compositions[n]=Flatten[Table[(Prepend[#1,first]&) /@ compositions[n-first],{first,1,n}],1];
Shuffle[lst1_List,lst2_List]:=Module[{join=Join[lst1,lst2]},
	Map[join[[#1]]&][Map[Ordering[Ordering[#1]]&][Permutations[Join[(0&) /@ lst1,(1&) /@ lst2]]]]];
Shuffle[word1_X,word2_X]:=Module[{lst1=List @@ word1,lst2=List @@ word2},
	Total[X @@@ Shuffle[lst1,lst2]]];
Shuffle[word_X,1]:=word;
Shuffle[1,word_X]:=word;
Stuffle[lst1_List,lst2_List]:=If[lst1=={}||lst2=={},
	Return[{Join[lst1,lst2]}],
	Assert[AllTrue[lst1,NumericQ]&&AllTrue[lst2,NumericQ]];
	Module[{first1=First[lst1],rest1=Rest[lst1], first2=First[lst2],rest2=Rest[lst2]},
	Return[Join[Prepend[first1] /@ Stuffle[rest1,lst2],Prepend[first2] /@ Stuffle[lst1,rest2],Prepend[first1+first2] /@ Stuffle[rest1,rest2]]]];
];
Stuffle[word1_Y,word2_Y]:=Module[{lst1=List @@ word1,lst2=List @@ word2},
	Total[Y @@@ Stuffle[lst1,lst2]]];
Stuffle[word_Y,1]:=word;
Stuffle[1,word_Y]:=word;
MakeBilinear /@ {Stuffle,Shuffle};
MakeLinear /@ {StuffleRegMZV,ShuffleRegMZV};
ShuffleRegMZV[word_X]:=Module[{j=0,m=0},
	If[word==X[0]||word==X[1],Return[0]];
	While[j<Length[word]&&word[[j+1]]==1,j++];
	While[m<Length[word]&&word[[Length[word]-m]]==0,m++];
	Which[j==0&&m==0,Return[word],
	j>0,Return[ShuffleRegMZV[Expand[word-Shuffle[X[1],Rest[word]]/j]]],
	m>0,Return[ShuffleRegMZV[Expand[word-Shuffle[X[0],Most[word]]/m]]]];
];
ShuffleRegPolynomial[word_X]:=Module[{j=0,m=0,wordSplit,wordAdm},
	If[word==X[1],Return[T]];
	If[word==X[0],Return[U]];
	While[j<Length[word]&&word[[j+1]]==1,j++];
	While[m<Length[word]&&word[[Length[word]-m]]==0,m++];
	wordAdm=word[[Range[j+1,Length[word]-m]]];
	If[j==0&&m==0,Return[word],
		Return[(T^j*U^m*wordAdm)/(j!*m!) + ShuffleRegPolynomial[Expand[word-Fold[Shuffle, Join[ConstantArray[X[1],j], {wordAdm}, ConstantArray[X[0],m]]]/(j!*m!)]]]
	];
];
MakeLinear[ShuffleRegPolynomial];
StuffleRegMZV[word_Y]:=Module[{j=0},
	If[word[[1]]>1,Return[word]];
	While[j<Length[word]&&word[[j+1]]==1,j++];
	StuffleRegMZV[Expand[word-Stuffle[Y[1],Rest[word]]/j]];
];
y1Reg=T; (* regularization of y_1 *)
StuffleRegPolynomial[word_Y]:=Module[{j=0,word1,wordAdm},
	If[word===Y[1],Return[y1Reg]];
	If[word[[1]]>1,Return[word]];
	While[j<Length[word]&&word[[j+1]]==1,j++];
	wordAdm=word[[Range[j+1,Length[word]]]];
	Return[(wordAdm y1Reg^j)/j! + StuffleRegPolynomial[Expand[word-Fold[Stuffle, Join[ConstantArray[Y[1],j],{wordAdm}]]/j!]]];
];
MakeLinear[StuffleRegPolynomial];
CoproductPrimitive::usage="Coproduct where each letter is primitive.";
CoproductPrimitive[word_List,power_:1]:=Module[{len=Length[word],first,rest},
	Which[
		len==0, Return[ConstantArray[{},power+1]],
		len==1, Return[Array[If[#1==#2,word,{}]&,{power+1,power+1}]]
	];
	first=CoproductPrimitive[{First[word]},power];
	rest=CoproductPrimitive[Rest[word],power];
	Flatten[Outer[MapThread[Join,{#1,#2}]&,first,rest,1],1]
];
CoproductPrimitive::usage="Computes shuffle coproduct of words in letters X[0] and X[1].";
CoproductPrimitive[word_X|word_U,power_:1]:=Module[{result,head=Head[word]},
	result=CoproductPrimitive[List @@ word,power];
	result=(head @@@ #1&) /@ result;
	Total[OX @@@ result]
];
CoproductPrimitive[1,power_:1]:=OX @@ ConstantArray[1,power+1];
CoproductStuffle[Y[num_?IntegerQ]]:=Module[{index=num},
	Total[Join[{OX[1,Y[index]]},Table[OX[Y[j],Y[index-j]],{j,1,index-1}], {OX[Y[index],1]}]]
];
CoproductStuffle[word_Y]:=NonCommutativeMultiply @@ CoproductStuffle /@ Y /@ List @@ word;
CoproductStuffle[word_U]:=CoproductStuffle[Conv2Y[word]] /. expr_Y :> Conv2U[expr];
CoproductStuffle[1,power_:1]:=OX @@ ConstantArray[1,power+1];
CoproductQShuffle[word_V,power_:1]:=Module[{result},
	result=CoproductPrimitive[List @@ word,power];
	result=(V @@@ #1&) /@ result;Total[OX @@@ result]
];
CoproductQShuffle[B[num_?IntegerQ]]:=Module[{index=num},
	Total[Join[{OX[1,B[index]]},Table[OX[B[j],B[index-j]],{j,1,index-1}], {OX[B[index],1]}]]
];
CoproductQShuffle[word_B]:=NonCommutativeMultiply @@ CoproductQShuffle /@ B /@ List @@ word;
MakeLinear /@ {CoproductPrimitive,CoproductStuffle,CoproductQShuffle};
SetAttributes[ModWeight,HoldFirst];
currentWeight:= Infinity;
ModWeight[expr_,maxWeight_Integer]:=Module[{res}, 
	currentWeight=maxWeight; 
	res=expr; 
	currentWeight=Infinity;
	res
];
ModWeight::usage="ModWeight[expr, maxWeight] computes expr modulo products of words of weight higher than maxWeight.";
Index2ZeroSegments[vec_List]:=Module[{result={},zeroCount=0},
	If[vec==={},Return[vec]];
	Do[
		If[vec[[n]]==0,zeroCount++,
			AppendTo[result,{zeroCount,vec[[n]]}];
			zeroCount=0
		],
		{n,Length[vec]}
	];
	AppendTo[result,zeroCount];
	Flatten[result]
];
MakeBilinear[GLPIhara];
GLPIhara[word1_X,word2_X]:=Module[
	{result=0, resultTmp, sgn, depth=WordDepth[word2], zeroSegmentedIndex=Index2ZeroSegments[List @@ word2], CoproductList},
	If[WordWeight[word1]+WordWeight[word2]>currentWeight,Return[0]];
	CoproductList=CoproductPrimitive[List @@ word1,2 depth];
	Do[sgn=If[OddQ[Total[Length /@ lst[[Range[2,2 depth,2]]]]],-1,1];
		resultTmp=Append[lst[[1]],Table[{ConstantArray[0,zeroSegmentedIndex[[2 n-1]]], Reverse[lst[[2 n]]], zeroSegmentedIndex[[2 n]],lst[[2 n+1]]},{n,depth}]];
		resultTmp=Flatten[Append[resultTmp,ConstantArray[0, Last[zeroSegmentedIndex]]]];
		result+=sgn X @@ resultTmp,
		{lst,CoproductList}
	];
	result
];
GLPIhara[lst_List]:=Fold[GLPIhara,First[lst],Rest[lst]];
GLPIhara[num_?NumberQ,expr_]:=num GLPIhara[expr];
GLPIhara[expr_,num_?NumberQ]:=num GLPIhara[expr];
GLPIhara[expr_]:=expr;
GLPIharaExp[expr_]:=Module[{res=1,currentTerm=Expand[expr],i},
	For[i=1,currentTerm=!=0,i++;currentTerm=GLPIhara[currentTerm,expr],
		res+=Expand[currentTerm/i!]
	];
	res
];
MakeLinear[Antipode];
Antipode[word_X]:=(-1)^Length[word] X @@ Reverse[word];
StuffleRegularizeY[expr_,degMax_Integer]:=Module[{corrTerm,conv2Y},
	conv2Y=Conv2Y[expr];
	corrTerm=Expand[Sum[((-1)^(n+1) Coefficient[conv2Y,Y[n]] nonCommutativePower[Y[1],n])/n,{n,1,degMax}]];
	Expand[ModWeight[nonCommutativeExp[corrTerm]**conv2Y,degMax]]
];
StuffleRegularizeU[expr_,degMax_Integer]:=Module[{corrTerm,conv2U},
	conv2U=Conv2U[expr];
	corrTerm=Expand[Sum[((-1)^(n+1) Coefficient[expr,X @@ Join[ConstantArray[0,n-1],{1}]] nonCommutativePower[U[1],n])/n,{n,1,degMax}]];
	Expand[ModWeight[nonCommutativeExp[corrTerm]**conv2U,degMax]]
];
StuffleRegularizeLyn[word_X]:=Module[{res,n},
	res=Conv2U[LieExpand[LyndonBracket[word]]/. {num_}:>X[num]];
	If[Last[word]===1&&(Length[word]===1||ContainsOnly[List @@ Most[word],{0}]),
		n=Length[word];
		res+=((-1)^(n-1) U @@ ConstantArray[1,n])/n
	];
	res
];
StuffleRegularizeLinearized[expr_,degMax_Integer]:=Module[{corrTerm,conv2Y},
	conv2Y=Conv2Y[expr];
	corrTerm=Sum[((-1)^(n+1) Coefficient[conv2Y,Y[n]] nonCommutativePower[Y[1],n])/n,{n,1,degMax}];
	conv2Y+corrTerm
];
Diag::usage="Diag[expr,maxWeight] computes OX[expr,expr] up to weight maxWeight.";
Diag[expr_,maxWeight_Integer]:=Module[{listTerms,listWeights,listPairs,len},
	listTerms=List @@ expr;
	listWeights=WordWeight /@ listTerms;
	len=Length[listWeights];
	listPairs=Select[Flatten[Table[{i,j},{i,len},{j,len}],1], Total[listWeights[[#1]]]<=maxWeight&];
	listPairs=(OX @@ listTerms[[#1]]&) /@ listPairs;
	Expand[Total[listPairs]]
];
collectWeights::usage="Returns a List of all terms in expr of weight between 0 and maxWeight.";
collectWeights[expr_]:=Module[{terms=List @@ expr,maxWeight,lstResult,termTmp,pos},
	maxWeight=Max[WordWeight /@ terms];
	lstResult=Table[0,maxWeight+1];
	For[pos=1,pos<=Length[terms],pos++,
		termTmp=terms[[pos]];
		lstResult[[WordWeight[termTmp]+1]]+=termTmp
	];
	lstResult
];
allWordsY::usage = "allWordsY[k] generates a list of all words of weight k in the letters y1, y2, ..., yk.";
allWordsY[k_Integer] := Reverse[Y @@@ compositions[k]];
primitivesShuffle::usage = "primitivesShuffle[k] computes the Lyndon brackets of Lyndon words over x0, x1 in weight k. Apply LieExpand to expand the symbolic Lie brackets.";
primitivesShuffle[k_Integer] := LieExpand /@ (LyndonBracket /@ LyndonWordsOfLength[k, 2] /. {n_Integer} :> X[n]);
primitivesStuffle::usage = "primitivesStuffle[k] computes the Lyndon brackets of Lyndon words over u1, u2, u3, ..., uk in weight k. Apply LieExpand to expand the symbolic Lie brackets.";
primitivesStuffle[k_Integer] := LieExpand /@ (LyndonBracket /@ LyndonWordsOfWeight[k, 1] /. {n_Integer} :> U[n]);
If[k > 1, LieExpand[LyndonBracket /@ Complement[LyndonWordsByWeight[k, 1], LyndonWordsByWeight[k - 1, 1]] /. {n_Integer} :> U[n]], {U[1]}];
betas=Table[If[Mod[k,2]===0,-(BernoulliB[k]/(2 k!)),0],{k,1,20}];
solFromData::usage="solFromData[lyndonCoeffs] returns the exponential of Lyndon brackets with coefficients given by lyndonCoeffs in a symbolic form. To evaluate the expression, apply lynbraExpand afterwards.
E.g. lyndonCoeffs can be one of the pre-computed coefficients lists from the results subfolder; use ReadList to read the respective files.";
solFromData[lyndonCoeffs_List] := Module[{lyndonBrackets, maxWeight = Length[lyndonCoeffs], resLst},
   lyndonBrackets = lynbra /@ X @@@ LyndonWordsOfLength[#, 2] & /@ Range[maxWeight];
   lyndonBrackets = lyndonCoeffs * lyndonBrackets;
   lyndonBrackets = Total /@ lyndonBrackets;
   (* If all coefficients in odd weights vanish, uses a more efficient algorithm. *)
   If[And @@ Table[AllTrue[lst[[i]], # == 0 &], {i, 1, Length[lst], 2}],
		resLst = Table[Join[1/Length[#]! * NonCommutativeMultiply @@ lyndonBrackets[[#]] & /@ (Most[compositions[k/2]*2]), {lyndonBrackets[[k]]}], {k, 2, maxWeight, 2}],
   	resLst = Table[Join[1/Length[#]! * NonCommutativeMultiply @@ lyndonBrackets[[#]] & /@ (Most[compositions[k]]), {lyndonBrackets[[k]]}], {k, maxWeight}];
   ];
   Expand[1+Total[Total /@ resLst]]
];
solFromDataExpanded[lyndonCoeffs_List] := lynbraExpand[solFromData[lyndonCoeffs]];
solFromEvenData[lyndonCoeffs_List] := Module[{lyndonBrackets, maxWeight = Length[lyndonCoeffs], resLst},
   lyndonBrackets = lynbra /@ X @@@ LyndonWordsOfLength[#, 2] & /@ Range[maxWeight];
   lyndonBrackets = lyndonCoeffs * lyndonBrackets;
   lyndonBrackets = Total /@ lyndonBrackets;
   resLst = Table[Join[1/Length[#]! * NonCommutativeMultiply @@ lyndonBrackets[[#]] & /@ (Most[compositions[k/2]*2]), {lyndonBrackets[[k]]}], {k, 2, maxWeight, 2}];
   Expand[1+Total[Total /@ resLst]]
];
solFromEvenDataExpanded[lyndonCoeffs_List] := Module[{lyndonBrackets, maxWeight = Length[lyndonCoeffs], resLst},
   lyndonBrackets = lyndonCoeffs*(primitivesShuffle /@ Range[maxWeight]);
   lyndonBrackets = Total /@ lyndonBrackets;
   resLst = Table[Join[1/Length[#]! * NonCommutativeMultiply @@ lyndonBrackets[[#]] & /@ (Most[compositions[k/2]*2]), {lyndonBrackets[[k]]}], {k, 2, maxWeight, 2}];
   resLst = Total /@ resLst;
   Total[1+LieExpand[resLst]]
];