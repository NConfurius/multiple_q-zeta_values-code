(* 
Compute rational solutions to the extended double shuffle inductively: 
Before loading this, asign a value to k for the current weight of the computation.
Assumptions: 
* PhiX is solution to the EDS up to weight k-1 and PhiU = StuffleRegularizeU[PhiX,k-1].
* primitivesX and primitivesU are lists of length k-1 such that
   ** the i'th entry is a primitive element of weight i and
   ** the exponential gives back PhiX and PhiU, resp.
*)

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
result = LinearSolve[coeffMatrix, vect];
kernel = NullSpace[coeffMatrix];
degsOfFreedom = Length[kernel];
(* Choose a solution by adjusting correctionFactors accordingly *)
If[degsOfFreedom =!= 0,
   correctionFactors = Table[0, degsOfFreedom];
   For[iter = 1, iter <= degsOfFreedom, iter++,
      correctionFactors[[iter]] = (betas[[k]]-result[[1]]-Total[kernel[[Range[iter-1]]] * correctionFactors[[Range[iter-1]]]]);
      If[kernel[[iter]][[1]]=!=0, correctionFactors[[iter]]/=kernel[[iter]][[1]]];
   ];
   result += Total[kernel * correctionFactors]
];
coeffsX = result[[Range[Length[termsPhiX]]]];
coeffsU =  result[[Range[Length[termsPhiX]+1, Length[termsPhiX] + Length[termsPhiU]]]];
resultX = Expand[Total[termsPhiX*coeffsX]];
resultU = Expand[Total[termsPhiU*coeffsU]];
primitivesX = Append[primitivesX,resultX];
primitivesU = Append[primitivesU,resultU];
PhiX += Expand[resultX + expPrimitivesX];
PhiU += Expand[resultU + expPrimitivesU];
end = AbsoluteTime[];
PutAppend[coeffsX, FileNameJoin[{"results", "rationalEDS", "RationalEDS-Lyndon_basis.m"}]];
Print["Finished computation in weight ",k," after ",end-start," seconds."];