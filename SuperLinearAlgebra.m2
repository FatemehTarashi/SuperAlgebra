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
   "Berezinian",
   "isSkewSymmetric",
   "isSuperHomogeneous",
   "inverseSuperMatrix",

   --Types and keys 
   "SuperMatrix",
   "supermatrix", "targetM1", "targetM3", "sourceM1", "sourceM2",
   
   --option
   "OddOrEven"
 }

--------------------------------------------------------------
--SuperRing (Super commutative ring)  ### y(inverse) need work
--------------------------------------------------------------

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
         print concatenate {"is a super commutative ring of dimension", toString n, "|",toString m};
         R111**R22
         )    

TEST ///

/// 
------------------------------------------------------
--SuperMatrix
--This a is new mulitivariate Hash table with 5 keys.
--supermatrix, targetM1, targetM3, sourceM1, sourceM2
------------------------------------------------

SuperMatrix = new Type of MutableHashTable;

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


---------------------------------------------------
--isSkewSymmetric            --For Polynomial Rings
--------------------------------------------------
isSkewSymmetric = method();
isSkewSymmetric Ring := (R1)->(
          i1 := symbol i1;
          i1 = numgens R1;
          L1 := apply(numgens R1, i -> R1_i^2);
          O1 := symbol O1;
          e1 := symbol e1;
          O1 = 0;
          e1 = 0;
          for j from 0 to (i1-1) do(if take(L1,{j,j})=={0} then O1=O1+1);
          if O1 =!= 0 then true else false
           )

TEST ///
r1 = QQ[x_0..x_3]
r2 = QQ[z_0..z_2]
r = superRing(r1,r2)
assert(isSkewSymmetric r == true)
R=QQ[x_0..x_5]
assert(isSkewSymmetric R ==false)
///

--------------------
--Supertrace           
--------------------  
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
Berezinian = method();
Berezinian (SuperMatrix,Ring) := (SM,R1) ->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 - 1)});
    Minor12 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor21 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 - 1)});
    SM1 := sub(Minor11,R1);
    SM2 := sub(Minor22,R1);
    Prod1 := Minor22 - Minor12*inverse(SM1)*Minor21;
    Prod2 := sub(Prod1,R1);
    if numRows Minor11 =!= numColumns Minor11 then error "expected a square matrix";
    if numRows Minor22 =!= numColumns Minor22 then error "expected a square matrix";
    if det(Minor22) =!= 0 then det(inverse(SM2))*det(Minor11-Minor21*inverse(SM2)*Minor12)
    else if (det(Minor11) =!= 0 and det(Minor22 - Minor12*inverse(SM1)*Minor21) =!= 0) then det(Minor11)*det(inverse(Prod2))
    else error "At least one of the diagonal blocks should be invertible"
    )
 
--superDeterminant = Berezinian ---###
TEST///
M1 = matrix{{5,7},{1,2}}
M2 = matrix{{1,2,3},{4,5,6}}
M3 = matrix{{3,4},{5,6},{7,8}}
M4 = matrix{{2,3,11},{4,5,6},{7,8,9}}
M5 = sub(M4,QQ)
G = superMatrix(M1,M2,M3,M4)
assert(Berezinian(G,QQ)== det(inverse(M5))*det(M1-M2*inverse(M5)*M3))
--Example2
S1 = matrix{{1,2},{3,4}}
S2 = matrix{{5,6},{7,8}}
S3 = matrix{{9,10},{11,12}}
S4 = matrix{{0,0},{0,0}}
S5 = sub(S1,QQ)
S6 = S4 - S3*inverse(S5)*S2
F = superMatrix(S1,S2,S3,S4)
assert(Berezinian(F,QQ) == det(S1)*det(inverse(S6)))
///

--------------------
--isSuperHomogeneous  now work only for function 
--------------------  ----------- 
isSuperHomogeneous = method(Options => {OddOrEven => null});
isSuperHomogeneous (RingElement,Ring,List) := ZZ => opts -> (f,R,a) -> (
    e := symbol e;
    e = exponents f;
    l := symbol l;
    l={};
    for i from 0 to (#gens R -1) do (for j from 0 to #a -1 do (if R_(i)==a_(j) then (l= append(l,i))));
    d := symbol d;
    countEvenNumber := symbol countEvenNumber; 
    d=0; 
    countEvenNumber =0; 
    for i from 0 to (#e-1) do (if (d%2)==0 then countEvenNumber = countEvenNumber +1; d=0; for j from 0 to #l-1 do (if 1==(e_i)_(l_j) then (d = d + 1)));
    d=0; for j from 0 to #l-1 do (if 1==(e_(#e-1))_(l_j) then (d = d + 1)); if (d%2)==0 then countEvenNumber = countEvenNumber +1; 
    if opts.OddOrEven ===null then (if (countEvenNumber -1) == #e then true else if (countEvenNumber -1) == 0 then true else false) else (if (countEvenNumber -1) == #e then 0 else if (countEvenNumber -1) == 0 then 1 else -1) 
    )  

TEST ///
R=QQ[x_0..x_4,y_0..y_1];
a={y_0,y_1} ;
g=x_1*x_2*x_3+4;
f=x_1*x_2*x_3+x_1*y_0+y_1*y_0-4*x_2*y_1*y_0+4;
h=y_0+y_0*x_0+y_1;
assert(isSuperHomogeneous(f,R,a) == false)
assert(isSuperHomogeneous(f,R,a,OddOrEven=>true) == -1)
assert(isSuperHomogeneous(g,R,a) == true)
assert(isSuperHomogeneous(g,R,a,OddOrEven=>true) == 0)
assert(isSuperHomogeneous(h,R,a) == true)
assert(isSuperHomogeneous(h,R,a,OddOrEven=>true) == 1)
///


------------------------
--inversesupermatrix
---------------------- 
inverseSuperMatrix = method();
inverseSuperMatrix (SuperMatrix,Ring) := (SM,R1) ->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 - 1)});
    Minor12 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor21 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 - 1)});
    if numRows Minor11 =!= numColumns Minor11 then error "expected a square matrix";
    if numRows Minor22 =!= numColumns Minor22 then error "expected a square matrix";    
    SM11 := sub(Minor11,R1);
    SM22 := sub(Minor22,R1);
    SM12 := sub(Minor12,R1);
    SM21 := sub(Minor21,R1);
    Prod1 := SM22 - SM12*inverse(SM11)*SM21;
    Prod2 := SM11 - SM21*inverse(SM22)*SM12;
    Nminor11 := inverse(Prod2);
    Nminor12 := -inverse(SM22)*SM12*inverse(Prod2);
    Nminor21 := -inverse(SM11)*SM21*inverse(Prod1);
    Nminor22 := inverse(Prod1);
    NSM1 := Nminor11 | Nminor21;
    NSM2 := Nminor12 | Nminor22;
    if (det(SM11) =!= 0 and det (SM22) =!= 0) then NSM1 || NSM2 else error "The SuperMatrix is not invertible"
    )

TEST///
M1 = matrix{{5,7},{1,2}};
M2 = matrix{{1,2,3},{4,5,6}};
M3 = matrix{{3,4},{5,6},{7,8}};
M4 = matrix{{2,3,11},{4,5,6},{7,8,9}};
M44 = sub(M4,QQ);
M11 = sub(M1,QQ);
M22 = sub(M2,QQ);
M33 = sub(M3,QQ);
P2 = M44 - M33*inverse(M11)*M22;
P1 = M11 - M22*inverse(M44)*M33;
N11 = inverse(P1);
N12 = -inverse(M44)*M33*inverse(P1);
N21 = -inverse(M11)*M22*inverse(P2);
N22 = inverse(P2);
NM1 = N11 | N21;
NM2 = N12 | N22;
G = superMatrix(M1,M2,M3,M4);
assert(inverseSuperMatrix(G,QQ) == NM1 || NM2)
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
    Let R_1 and R_2 be Two Polynomial rings on different set of variables
    A superRing is a new polynomial ring with three sets of variables. 
    One set comes from R_1 and the second one is the inverse of it.
    For example, if we have x as a variable in R_1,
    then there is a new variable, say y_0 which is the inverse of $x$.
    The third set of variables comes from R_2.
    We redefine this set to be a set of skew-symmetric variables.
    So superRing of R_1 and R_2 is a quotient ring,
    which has both invertible and skew symmetric variables.
    If the coefficient ring a a field, then we get a super algebra.

  Example
    r1=QQ[x_1..x_5]
    r2=QQ[z_1..z_3]
    superRing(r1,r2)
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
   Let M_1,M_2,M_3,M_4 are four matrices. 
   The number of rows in M_1 and M_2,
   and those of M_3 and M_4 should be equal.
   Also, the number of columns of M_1 and M_3,
   and those of M_2 and M_4 must be equal.
   The idea is to define a (super) Matrix,
   which can be considered as p|q\times r|s matrix.
   This super Matrix can be a morphism between super
   modules A^{p|q} and A^{r|s} over super algebra A. 

   The function merges the matrices M_1 and M_2, and also M_3 and M_4. 
   Finally it merges two new matrices and 
   make a new matrix with the first four matrices as
   the blocks of the new matrix, say matrix {M_1, M_2, M_3,M_4}.
   The key supermatrix shows the result matrix created as above.
   The key targetM1 shows the number of first part rows.
   The key targetM3 shows the number of the rows of the second part
   The key sourceM1 shows the number of columns in the first part
   The key sourceM2 shows the number of columns in the second part.
 Example
    M1 = matrix {{1,2},{5,6},{9,10}}
    M2 = matrix {{3,4},{7,8},{11,12}}
    M3 = matrix {{13,14},{17,18}}
    M4 = matrix {{15,16},{19,20}}
    G = superMatrix(M1,M2,M3,M4)
    G.supermatrix
Caveat
SeeAlso
///


doc ///
Key 
  superTrace
Headline
  super trace
Description
  Text
    Todo
 Example
    M1 = matrix {{2,3},{4,5}};
    M2 = matrix {{2,3,8},{4,5,9}};
    M3 = matrix {{2,3},{4,5},{10,11}};
    M4 = matrix {{2,3,18},{5,6,19},{16,17,20}};
    G = superMatrix(M1,M2,M3,M4);
    superTrace G
Caveat
SeeAlso
///

doc ///
Key 
  Berezinian
Headline
  Berezinian
Description
 Text
  If in a super Matrix, one of the first or the second diagonal block is invertible,
  then we can define Berezinian (as a kind of super Determinant).
  The formula for the Berezinian is different base on which block is invertible.
  But it is shown that the two formulas are equivalent if two blocks are invertible.
  If M= matrix {M_1 , M_2, M_3 , M_4} is a super Matrix, and
  M_4 is invertible, then 
  Ber(M)= det(M_1-M_2M^{-1}_4M_3) det(M_4)^{-1}.
  
  If M_1 is invertible, then
  Ber(M) = det(M_4-M_3M_1^{-1}M_2)^{-1} det(M_1).
 Example
    M1 = matrix{{5,7},{1,2}}
    M2 = matrix{{1,2,3},{4,5,6}}
    M3 = matrix{{3,4},{5,6},{7,8}}
    M4 = matrix{{2,3,11},{4,5,6},{7,8,9}}
    M5 = sub(M4,QQ)
    G = superMatrix(M1,M2,M3,M4)
    Berezinian(G,QQ)
Caveat
SeeAlso
///


doc ///
Key 
  isSuperHomogeneous
Headline
  isSuperHomogeneous
Description
 Text
  Let we have a super algebra (ring), R=R_0 oplus R_1.
  A homogeneous element of R is an element belongs to R_0 or R_1.
  If x in R_0, we say x is even, and if x in R_1 , we say x is odd.

 Example
    R1=QQ[x_0..x_4];
    R2=QQ[e_0,e_1];
    R= superRing(R1,R2)
    a={e_0,e_1}
    f=x_1*x_2*x_3+x_1*e_0+e_1*e_0-4*x_2*e_1*e_0+4
    isSuperHomogeneous(f,R,a)
    g=x_1*x_2*x_3+e_0*e_1+4;
    isSuperHomogeneous(g,R,a)
Caveat
SeeAlso
///


doc ///
Key 
  inverseSuperMatrix
Headline
  InverseSuperMatrix
Description
 Text
  A super Matrix M=matrix{M_1, M_2, M_3, M_4}
  is invertible, if both the diagonal blocks, M_1 and M_4 are invertible.
  In this case, the inverse is given by a blocked matrix,
  T=matrix{T_1, T_2, T_3, T_4}, where
  
  T_1=(M_1 − M_2M^{-1}_4 M_3)^{-1},
  T_2=−M^{-1}_1 M_2(M_4 − M_3M^{-1}_1 M_2)^{-1},
  T_3=−M^{-1}_4 M_3(M_1 − M_2M^{-1}_4 M_3)^{-1}, and
  T_4=(M_4 − M_3M^{-1}_1 M_2)^{-1}.
 Example
    test
    M1 = matrix{{5,7},{1,2}};
    M2 = matrix{{1,2,3},{4,5,6}};
    M3 = matrix{{3,4},{5,6},{7,8}};
    M4 = matrix{{2,3,11},{4,5,6},{7,8,9}};
    G = superMatrix(M1,M2,M3,M4);
    inverseSuperMatrix(G,QQ)
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
path={"/home/ftk/Desktop/SuperAlgebra/SuperLinearAlgebra.m2"}|path

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
