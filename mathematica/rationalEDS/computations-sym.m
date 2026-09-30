(* This file is a copy of 'computations.m' for the most part, but facilitates computations with symbolic variables instead of rational numbers. *)

start = AbsoluteTime[];
words = Reverse[U@@@compositions[k]];
comps = Drop[compositions[k],-1]; (* compositions of k in >1 parts, i.e. excluding (k) *)
termsPhiX = primitivesShuffle[k];
termsPhiX2U = termsPhiX /. X@@Join[ConstantArray[0,k-1],{1}] :> X@@Join[ConstantArray[0,k-1],{1}] + (-1)^(k-1)/k * X@@ConstantArray[1,k];
termsPhiX2U = Conv2U /@ termsPhiX2U;
termsPhiU = primitivesStuffle[k];
coeffMatrix = Table[Coefficient[termsPhiX2U[[n]],words[[m]]], {n,Length[termsPhiX2U]}, {m,Length[words]}];
coeffMatrix = Transpose[Join[coeffMatrix, Table[-Coefficient[termsPhiU[[n]],words[[m]]], {n,Length[termsPhiU]}, {m,Length[words]}]]];
expPrimitivesX = Expand[Total[1/Length[#]! * NonCommutativeMultiply@@primitivesX[[#]]& /@ comps]];
expPrimitivesX2U = Conv2U[expPrimitivesX];
expPrimitivesU = Expand[Total[1/Length[#]! * NonCommutativeMultiply@@primitivesU[[#]]& /@ comps]];
termsCorr = ModWeight[nonCommutativeExp[Total[(-1)^(#-1)/# * Coefficient[PhiX+expPrimitivesX, X@@Join[ConstantArray[0,#-1],{1}]] ** U@@ConstantArray[1,#]& /@ Range[k]]],k];
regularizationTerms = ModWeight[termsCorr ** Conv2U[PhiX],k];
constants = Expand[PhiU + expPrimitivesU-(expPrimitivesX2U + regularizationTerms)];
vect = Coefficient[constants,#]& /@ words;
result = LinearSolvePari[coeffMatrix,vect];
kernel = NullSpace[coeffMatrix];
degsOfFreedom = Length[kernel];
(* Choose a solution by adjusting correctionFactors accordingly, e.g. *)
If[degsOfFreedom =!= 0, 
   Which[
   degsOfFreedom === 1, 
   correctionFactors = If[kernel[[1,1]] =!= 0, 
      {(Symbol["L" <> ToString[k]] - result[[1]])/kernel[[1,1]]},
      {Symbol["L" <> ToString[k]] - result[[1]]}
   ],
   degsOfFreedom > 1, 
   correctionFactors = Table[
      If[kernel[[num,1]] =!= 0, 
      (makeSymbolicVariable[k,num] - result[[1]])/kernel[[num,1]], 
      makeSymbolicVariable[k,num]] - result[[1]], {num, 1, degsOfFreedom}
      ]
   ];
   result += Total[kernel * correctionFactors];
];
coeffsX = result[[Range[Length[termsPhiX]]]]; (* Coefficients of Lyndon words in weight k over x0, x1. *)
coeffsU =  result[[Range[Length[termsPhiX]+1, Length[termsPhiX] + Length[termsPhiU]]]];
resultX = Expand[Total[termsPhiX*coeffsX]];
resultU = Expand[Total[termsPhiU*coeffsU]];
primitivesX = Append[primitivesX,resultX];
primitivesU = Append[primitivesU,resultU];
PhiX += Expand[resultX + expPrimitivesX];
PhiU += Expand[resultU + expPrimitivesU];
end = AbsoluteTime[];
PutAppend[coeffsX, FileNameJoin[{"results", "rationalEDS", "RationalEDS-sym.m"}]];
Print["Finished computation in weight ",k," after ",end-start," seconds."];