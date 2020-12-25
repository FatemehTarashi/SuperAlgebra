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
   "isSuperHomogeneous",
   "InverseSuperMatrix",
   
   --Types and keys 
   "SuperMatrix",
   "supermatrix", "targetM1", "targetM3", "sourceM1", "sourceM2",
   --option
   "OddOrEven"
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
Berezinian = method();
Berezinian (SuperMatrix,Ring) := (SM,R1) ->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 - 1)});
    Minor12 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor21 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 - 1)});
    SM1 = sub(Minor11,R1);
    SM2 = sub(Minor22,R1);
    Prod1 = Minor22 - Minor12*inverse(SM1)*Minor21;
    Prod2 = sub(Prod1,R1);
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
    SM11 = sub(Minor11,R1);
    SM22 = sub(Minor22,R1);
    SM12 = sub(Minor12,R1);
    SM21 = sub(Minor21,R1);
    Prod1 = SM22 - SM12*inverse(SM11)*SM21;
    Prod2 = SM11 - SM21*inverse(SM22)*SM12;
    Nminor11 = inverse(Prod2);
    Nminor12 = -inverse(SM22)*SM12*inverse(Prod2);
    Nminor21 = -inverse(SM11)*SM21*inverse(Prod1);
    Nminor22 = inverse(Prod1);
    NSM1 = Nminor11 | Nminor21;
    NSM2 = Nminor12 | Nminor22;
    if (det(SM11) =!= 0 and det (SM22) =!= 0) then NSM1 || NSM2
    else error "The SuperMatrix is not invertible"
    )

TEST///
M1 = matrix{{5,7},{1,2}}
M2 = matrix{{1,2,3},{4,5,6}}
M3 = matrix{{3,4},{5,6},{7,8}}
M4 = matrix{{2,3,11},{4,5,6},{7,8,9}}
M44 = sub(M4,QQ)
M11 = sub(M1,QQ)
M22 = sub(M2,QQ)
M33 = sub(M3,QQ)
P2 = M44 - M33*inverse(M11)*M22
P1 = M11 - M22*inverse(M44)*M33
N11 = inverse(P1)
N12 = -inverse(M44)*M33*inverse(P1)
N21 = -inverse(M11)*M22*inverse(P2)
N22 = inverse(P2)
NM1 = N11 | N21
NM2 = N12 | N22
G = superMatrix(M1,M2,M3,M4)
assert(inverseSuperMatrix(G,QQ) == NM1 || NM2)
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
    if opts.OddOrEven ===null then (if (countEvenNumber -1) == #e then true else if (countEvenNumber -1) == 0 then true else false) else (if (countEvenNumber -1) == #e then (print("Homogeneous and even");return 0) else if (countEvenNumber -1) == 0 then (print("Homogeneous and odd");return 1) else false) 
    )  

TEST ///
R=QQ[x_0..x_4,y_0..y_1];
a={y_0,y_1} ;
g=x_1*x_2*x_3+4;
f=x_1*x_2*x_3+x_1*y_0+y_1*y_0-4*x_2*y_1*y_0+4;
h=y_0+y_0*x_0+y_1;
assert(isSuperHomogeneous(f,R,a) == false)
assert(isSuperHomogeneous(f,R,a,OddOrEven=>true) == false)
assert(isSuperHomogeneous(g,R,a) == true)
assert(isSuperHomogeneous(g,R,a,OddOrEven=>true) == 0)
assert(isSuperHomogeneous(h,R,a) == true)
assert(isSuperHomogeneous(h,R,a,OddOrEven=>true) == 1)
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
