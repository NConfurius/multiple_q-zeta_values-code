(* When working with formal coefficients instead of numbers, load these definitions after the previous ones. *)
(* if needed, replace
result = LinearSolve[coeffMatrix,vect];
with
result = LinearSolvePari[coeffMatrix,vect];
*)
Unprotect[NonCommutativeMultiply];
c_Symbol**x_:=c*x
x_ **c_Symbol:=c*x
c_Power**x_:=c*x
(c_Symbol*x_)**y_ := Expand[c*(x**y)]
x_**(c_Symbol*y_) := Expand[c*(x**y)]
(c_Power*x_)**y_ := Expand[c*(x**y)]
x_**(c_Power*y_) := Expand[c*(x**y)]
Protect[NonCommutativeMultiply];
Conv2Y[word_X]:=Module[{res = {}, zeroCount = 0,index},
	If[Last[word] === 0, Return[0]];
	For[index=1,index<=Length[word],index++,
		If[word[[index]]===0,
			zeroCount++,
			res=Append[res,zeroCount+1];
			zeroCount=0
		];
	];
	Y@@res
];
Conv2Y[c_Symbol * word_X] := c * Conv2Y[word];
Conv2Y[c_Symbol * word_U] := c * Conv2Y[word];
Conv2Y[word_X * c_Symbol] := c * Conv2Y[word];
Conv2Y[word_U * c_Symbol] := c * Conv2Y[word];
Conv2Y[word_X * c_Times] := c * Conv2Y[word];
Conv2Y[word_U * c_Times] := c * Conv2Y[word];
Conv2Y[c_Power * word_X] := c * Conv2Y[word];
Conv2Y[c_Power * word_U] := c * Conv2Y[word];
Conv2U[c_Symbol * word_X] := c * Conv2U[word];
Conv2U[word_X* c_Symbol ] := c * Conv2U[word];
Conv2U[word_X * c_Times] := c * Conv2U[word];
Conv2U[c_Power * word_X] := c * Conv2U[word];
Conv2U[word_X*c_Power ] := c * Conv2U[word];
Shuffle[c_Symbol * word1_X,word2_X] := c * Shuffle[word1,word2];
Shuffle[c_Times * word1_X,word2_X] := c * Shuffle[word1,word2];
Shuffle[c_Power * word1_X,word2_X] := c * Shuffle[word1,word2];
Shuffle[word1_X,c_Symbol * word2_X] := c * Shuffle[word1,word2];
Shuffle[word1_X,c_Times * word2_X] := c * Shuffle[word1,word2];
Shuffle[word1_X,c_Power * word2_X] := c * Shuffle[word1,word2];
Shuffle[c1_ * word1_X, c2_ * word2_X] := c1*c2*Shuffle[word1,word2];
makeSymbolicVariable[weight_Integer,index_Integer]:= Symbol["L"<>ToString[weight]<>"x"<>ToString[index]];
PrintBr2Lynbra[expr_] := expr //. br[a__] :> lynbra[a] /. X[num_]:>StringJoin["\\x_",ToString[num]];
(* The Mathematica function LinearSolve is very slow when working with symbolic expressions.
To solve system of linear equations in pari/gp instead of mathematica, load the following definitions.
Note: pari/gp must be installed on the system for this. This should work for unix-based systems (Linux, MacOS). *)
tempDataDirAbs = FileNameJoin[{Directory[], "tmpData"}];
tempDataDirRel = FileNameDrop[tempDataDirAbs,FileNameDepth[Directory[]]];
ExportMatrix2Pari[matrix_List,fileName_String] := Module[{rowsString, location = FileNameJoin[{tempDataDirAbs,ToString[fileName]<>".gp"}]},
	rowsString = Map[StringRiffle[ToString[#, InputForm] & /@ #, ", "] &, matrix];
	Export[location,"[" <> StringRiffle[rowsString, "; "] <> "]", "Text"];
];
WritePariExe[filenameMatrix_String, filenameVector_String, memoryAllocation_String:"100M"]:= Module[{file},
	file = OpenWrite[FileNameJoin[{tempDataDirAbs,"pariInput.gp"}], FormatType->OutputForm, PageWidth->Infinity];
	Write[file, StringRiffle[{
		"default(parisize,"<>memoryAllocation<>");",
		"mat=read(\""<>FileNameJoin[{tempDataDirAbs, filenameMatrix}]<>".gp\");",
		"vect=read(\""<>FileNameJoin[{tempDataDirAbs, filenameVector}]<>".gp\");",
		"sol = matinverseimage(mat,vect~)~;",
		"write(\""<>FileNameJoin[{tempDataDirAbs, "pariOutput.gp"}]<>"\",sol);",
		"quit"
		}, "\n"]
	];
	Close[file];
];
LinearSolvePari[matrix_List,vector_List, memoryAllocation_String:"100M"] := Module[{filenameMatrix="pariMatrix", filenameVector="pariVector", resultPari},
	ExportMatrix2Pari[matrix,filenameMatrix];
	ExportMatrix2Pari[{vector},filenameVector];
	If[!FileExistsQ[FileNameJoin[{tempDataDirAbs,"pariInput.gp"}]],
		WritePariExe[filenameMatrix,filenameVector,memoryAllocation]
	];
	RunProcess[{"gp","-q",FileNameJoin[{tempDataDirRel,"pariInput.gp"}]}, "StandardOutput"];
	resultPari = Last[Import[FileNameJoin[{tempDataDirRel,"pariOutput.gp"}], "Lines"]];
	ToExpression[StringReplace[resultPari,{"["->"{","]"->"}"}]]
];