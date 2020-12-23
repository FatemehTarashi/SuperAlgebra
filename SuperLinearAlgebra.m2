newPackage(
  "SuperLinearAlgebra",
  Version => "0.1", 
  Date => "29 July 2020",
  Authors => {
      {Name => "Fereshteh Bahadorykhalily", 
       Email => "f.bahadori.khalili@gmail.com", 
       HomePage => "Your page here"},
      {Name => "Fatemeh Tarashi Kashani", 
       Email => "tarashikashanifatemeh@gmail.com", 
       HomePage => "Your page here"}
   },
   Headline => "Berezinian and supertrace of a supermatrix",
   DebuggingMode => true
)

--------------------
--Exports
--------------------

export {
   -- Methods
   "superRing",
   "superMatrix",
   "superTrace",
   "isOdd",
   
   -- "ishomogeneouse (isodd and iseven)",
   -- "Ber",
   -- "InverseSuperMatrix",
   
   --Types and keys 
   "SuperMatrix",
   "supermatrix", "targetM1", "targetM3", "sourceM1", "sourceM2"
 }

--------------------
--SuperRing (Super commutative ring)
--------------------

superRing = method();
superRing (PolynomialRing,PolynomialRing):= (R1,R2) -> (
         n := #gens R1;
         y := symbol y;
 	 R11 := symbol R11; 
	 R22 := symbol R22; 
	 R111 := symbol R111;
         R11 = (coefficientRing R1)[R1_0..R1_(n-1),y_0..y_(n-1)];
	 R111 = R11/apply(0..(n-1), i -> sub(R1_i,R11) * y_i - 1);
         m := #gens R2;
         w := (for i to m-1 list (0))|toList(0..(m-1));
         R22 = (coefficientRing R2)[R2_0..R2_(m-1), MonomialOrder=>{Weights => w,Lex}, SkewCommutative=>true];
         print concatenate {"is a super commutative ring of dimension", toString m, "|",toString n};
         R111**R22
         ) 
     
TEST ///

///
  
--------------------
--SuperMatrix         now work
--------------------  -----------
SuperMatrix = new Type of MutableHashTable;
--a SuperMatrix always has the following keys:
-- supermatrix, targetM1, targetM3, sourceM1, sourceM2

superMatrix = method();
superMatrix (Matrix,Matrix,Matrix,Matrix):= (M1,M2,M3,M4) ->(
         nr1 := numgens target M1;
         nr2 := numgens target M3;
         ns1 := numgens source M1;
         ns2 := numgens source M2;
	 T1 := symbol T1;
	 T2 := symbol T2;
         T1 = M1 | M2;
         T2 = M3 | M4;
	 new SuperMatrix from{
	 supermatrix => T1 || T2,
	 targetM1 => nr1,
	 targetM3 => nr2,
	 sourceM1 => ns1,
	 sourceM2 => ns2
	 }
         )

TEST ///
M1 = matrix {{1,2},{5,6},{9,10}};
M2 = matrix {{3,4},{7,8},{11,12}};
M3 = matrix {{13,14},{17,18}};
M4 = matrix {{15,16},{19,20}};
G = superMatrix(M1,M2,M3,M4);
G.supermatrix;
assert(G.supermatrix == matrix {{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16},{17,18,19,20}})
assert(G.targetM1 == 3)
assert(G.targetM3 == 2)
assert(G.sourceM1 == 2)
assert(G.sourceM2 == 2)
///

--------------------
--Supertrace           now work
--------------------  -----------

superTrace = method ();
superTrace SuperMatrix :=(SM)->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 -1)}, {0..(SM.sourceM1 -1)});
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 -1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 -1)});
    trace Minor11 - trace Minor22
    )

TEST ///
M1 = matrix {{2,3},{4,5}};
M2 = matrix {{2,3,8},{4,5,9}};
M3 = matrix {{2,3},{4,5},{10,11}};
M4 = matrix {{2,3,18},{5,6,19},{16,17,20}};
G = superMatrix(M1,M2,M3,M4);
assert(superTrace G == -21) 
///

--------------------
--Berezinian
--------------------  -----------
-*
Ber = method();
Ber SuperMatrix := (SM) ->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)}); 
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)});
    Minor21 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor12 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2  - 1)});
    if det(Minor11) != 0 then det(Minor11)*det(Minor22-Minor21*inverse(Minor11)*Minor12)^{-1}
    else if det(Minor22) != 0 then det(Minor22)^{-1}*det(Minor11-Minor12*inverse(Minor22)*Minor21)
    else error "At least one of the diagonal blocks should be invertible"
    )
superDeterminant = Ber ---###
*-

------------------------
--inversesupermatrix
----------------------
-*
InverseSuperMatrix = method();
InverseSuperMatrix SuperMatrix := (SM) ->(
    if numRows SM.supermatrix =!= numColumns SM.supermatrix then error "expected a square matrix";
    
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)}); 
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)});
    Minor21 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor12 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2  - 1)});
    if det(Minor11) != 0 and det (Minor22) != 0 then
    
    else error "The SuperMatrix is not invertible"
    )
*-

--------------------
--isOdd               now work only for function 
--------------------  -----------
isOdd = method();
isOdd (RingElement,Ring,List):=(f,R,a) -> (    --- a= oddlist
    e := symbol e;
    e := exponents f;
    l := symbol l;
    l={};
    for i from 0 to (#gens R -1) do (for j from 0 to #a -1 do (if R_(i)==a_(j) then (l= append(l,i))));
    d := symbol d;
    v := symbol v; 
    d=0;
    v=0;
    for i from 0 to (#e-1) do (if (d%2)==0 then v=v+1; d=0; for j from 0 to #l-1 do (if 1==(e_i)_(l_j) then (d = d + 1)));
    d=0; for j from 0 to #l-1 do (if 1==(e_(#e-1))_(l_j) then (d = d + 1)); if (d%2)==0 then v=v+1; 
    ppp := symbol ppp;
    if #e==v-1 then print("joz") else ppp= true;
    ppp
    )

TEST ///
R=QQ[x_0..x_4,y_0..y_1];
f=x_1*x_2*x_3+x_1*y_0+y_1*y_0-4*x_2*y_1*y_0+4;
a={y_0,y_1} ;
assert(isOdd(f,R,a) == true)
///

--------------------


beginDocumentation()

doc ///
Key
  SuperLinearAlgebra
Headline
  Package for super algebra
Description
  Text
    Todo
Caveat
SeeAlso
///

doc ///
Key
  superRing
Headline
  Super ring
Description
  Text
    Todo
  Example
    R = QQ[x_1..x_5]
    F = QQ[y_1..y_5]
    K = QQ[z_1,z_2]
    superRing(F,K)
Caveat
SeeAlso
///


doc ///
Key
  SuperMatrix
Headline
  Super matrix
Description
  Text
    Todo
 -- Example
   -- Todo
Caveat
SeeAlso
///

doc ///
Key
  superMatrix
Headline
  Super matrix
Description
  Text
    Todo
  --Example
   -- Todo
Caveat
SeeAlso
///


-- template for function documentation
--doc ///
--Key
--Headline
--Usage
--Inputs
--Outputs
--Consequences
--  Item
--Description
--  Text
--  Code
--  Pre
--  Example
--  CannedExample
--Subnodes
--Caveat
--SeeAlso
--///

end


------------------------------------------------------------
--Example
restart
--path={"/home/feri/Documents/SuperLinearAlgebra"}|path 
path={"Desktop/SuperAlgebra/SuperLinearAlgebra"}|path

loadPackage("SuperLinearAlgebra",Reload=>true)
debug (SuperLinearAlgebra)

check"SuperLinearAlgebra"
installPackage"SuperLinearAlgebra"

M1 = matrix {{2,3},{4,5}}
M2 = matrix {{2,3,8},{4,5,9}}
M3 = matrix {{2,3},{4,5},{10,11}}
M4 = matrix {{2,3,18},{5,6,19},{16,17,20}}
G = superMatrix(M1,M2,M3,M4)
superTrace G 

viewHelp SuperLinearAlgebra
