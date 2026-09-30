(* Compute rational solutions to the extended double shuffle inductively: *)
(* To initialize the computation, fix coefficients in weights 1 and 2. *)

coeffX0 = 0;
coeffX1 = 0;
coeffWeight2 = - BernoulliB [2]/(2*2!);
primitivesX = {coeffX0*X[0] + coeffX1*X[1], coeffWeight2 * (X[0,1] - X[1,0])};
primitivesX = Expand[primitivesX];
primitivesU = Expand[{2*coeffX1*U[1], (coeffWeight2 + coeffX0 * coeffX1/2) * U[2]}];
(* primitivesX[[i]] contains the primitive elements w.r.t. to shuffle coproduct of weight i that are currently used. Similar for primitivesU w.r.t. to stuffle coproduct. *)
PhiX = ModWeight[nonCommutativeExp[Total[primitivesX]], Length[primitivesX]];
PhiU = StuffleRegularizeU[PhiX, Length[primitivesX]];
k=3;