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
   "isEven",
   "isOdd",
   "isSuperMatrixHomogeneous",
   "inverseSuperMatrix",
   "isSkewSymmetric",


   --Types and keys 
   "SuperMatrix",
   "supermatrix", "targetM1", "targetM3", "sourceM1", "sourceM2",

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
--isSuperHomogeneous  now work only for function 
--------------------  -----------
isSuperHomogeneous = method();
isSuperHomogeneous (RingElement,Ring,List) := (f,R,a) -> (
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
    if (countEvenNumber -1) == #e then true else if (countEvenNumber -1) == 0 then true else false 
    ) 
TEST ///
R1=QQ[x_0..x_4];
R2=QQ[e_0,e_1];
R= superRing(R1,R2);
a={e_0,e_1};
f=x_1*x_2*x_3+x_1*e_0+e_1*e_0-4*x_2*e_1*e_0+4;
g=x_1*x_2*x_3+e_0*e_1+4;
assert(isSuperHomogeneous(f,R,a) == false)
assert(isSuperHomogeneous(g,R,a) == true)
///
---------------------------------------
--isOdd
--------------------------------------
isOdd = method();
isOdd (RingElement,Ring,List) := (f,R,a) -> (
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
    if (countEvenNumber -1) == 0 then true  else false 
    )  

TEST ///
R1=QQ[x_0..x_4];
R2=QQ[e_0,e_1];
R= superRing(R1,R2);
a={e_0,e_1};
g=x_1*x_2*x_3+e_0*e_1+4;
h=x_1*e_1;
assert(isOdd(g,R,a) == false)
assert(isOdd(h,R,a) == true)
///

--------------------
--isEven
--------------------  
isEven = method();
isEven (RingElement,Ring,List) := (f,R,a) -> (
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
    if (countEvenNumber -1) == #e then true  else false 
    )  

TEST ///
R1=QQ[x_0..x_4];
R2=QQ[e_0,e_1];
R= superRing(R1,R2);
a={e_0,e_1};
g=x_1*x_2*x_3+e_0*e_1+4;
h=x_1*e_1;
assert(isEven(g,R,a) == true)
assert(isEven(h,R,a) == false)
///
------------------------------------
--isSuperMatrixHomogeneous
--------------------------------
isSuperMatrixHomogeneous = method(Options=> {EvenOrOddMatrix=>null});
isSuperMatrixHomogeneous(SuperMatrix,Ring,List) := ZZ => opts -> (SM,R1,a) ->(
    m1 := symbol m1;
    m2 := symbol m2;
    m3 := symbol m3;
    m4 := symbol m4;
    m1 = 0;
    m2 = 0;
    m3 = 0;
    m4 = 0;
    r1 := symbol r1;
    r2 := symbol r2;
    c1 := symbol c1;
    c2 := symbol c2;
    r1=SM.targetM1;
    r2=SM.targetM3;
    c1=SM.sourceM1;
    c2=SM.sourceM2;
    Minor11 := submatrix(SM.supermatrix, {0..(r1 - 1)}, {0..(c1 - 1)});
    Minor22 := submatrix(SM.supermatrix, {r1..(r1 + r2 - 1)}, {c1..(c1 + c2 - 1)});
    Minor21 := submatrix(SM.supermatrix, {r1..(r1 + r2 - 1)}, {0..(c1 - 1)});
    Minor12 := submatrix(SM.supermatrix, {0..(r1 - 1)}, {c1..(c1 + c2 - 1)});
    if isSkewSymmetric(R1)==true then
    (fij := symbol fij;
     count1:= symbol count1;
     count1=0;
     count12:=symbol count12;
     count12=0;
     count2:=symbol count2;
     count2=0;
     count22:=symbol count22;
     count22=0;
     count3:=symbol count3;
     count3=0;
     count33:=symbol count33;
     count33=0;
     count4:=symbol count4;
     count4=0;
     count44:=symbol count44;
     count44=0;
   for i from 0 to (r1-1) do for j from 0 to (c1-1)
	do(fij = Minor11_(i,j);
	    if (isSuperHomogeneous(fij,R1,a)==true) then
	       (if (isEven(fij,R1,a)==false) then 
	           count1 = count1+1
	           else count1 = count1)
	       else count12 = count12+1);
	    if count12 =!= 0 then (return false) else if count1 == 0 then m1= 0 else m1=1;
	for i from 0 to (r1-1) do for j from 0 to (c2-1)
	do(fij = Minor12_(i,j);
	    if isSuperHomogeneous(fij,R1,a)==true then
	    (if (isEven(fij,R1,a)==false)
		then count2 = count2+1
		else count2 = count2)
	   else count22=count22+1);
	   if count22=!=0 then (return false) else if count2 ==0 then m2=0 else m2=1;
       for i from 0 to (r2-1) do for j from 0 to (c1-1)
       do(fij = Minor21_(i,j);
	   if isSuperHomogeneous(fij,R1,a)==true then
	    (if(isEven(fij,R1,a)==false)
		then count3 = count3+1
		else count3 = count3)
	   else count33=count33+1);
	   if count33=!=0 then (return false)  else if count3==0 then m3=0 else m3=1;
       for i from 0 to (r2-1) do for j from 0 to (c2-1)
       do(fij = Minor22_(i,j);
	   if isSuperHomogeneous(fij,R1,a)==true then
	    (if(isEven(fij,R1,a)==false)
		then count4 = count4+1
		else count4 = count4)
	   else cout44=count44+1);
	  if count44=!=0 then (return false) else if count4==0 then m4=0 else m4=1;
      R2 = coefficientRing R1;
      if (isSkewSymmetric(R2)==true) then(
       if (m1==0 and m4==0 and m2==1 and m3==1)then true
       else if (m1==1 and m4==1 and m2==0 and m3==0) then  true else false)
       else if (m1==0 and m4==0 and m2==1 and m3==1) then 
        true else if (m1==1 and m4==1 and m2==0 and m3==0) then
        true else false
	)
    else (print "Ring is not superRing and everything is superHomogeneouse",return true)
)

TEST///
R1 = QQ[x_0..x_3]
R2 = QQ[z_0..z_2]
R = superRing(r1,r2)
T1 = r[n_0..n_3]
T2 = r[e_0..e_3]
T = superRing(t1,t2)
M1 = matrix{{n_0,n_1},{n_2,n_3}}
M2 = matrix{{e_0,e_1},{n_0*e_0,n_1*e_1}}
M3 = matrix{{e_3*n_3,e_1},{e_0,e_2*n_2}}
M4 = matrix{{n_1,n_3},{n_0,n_2+n_3}}
SM = superMatrix(M1,M2,M3,M4)
assert(isSuperMatrixHomogeneous(SM,t,{e_0,e_1,e_2,e_3})==true)
---
E1 = matrix{{e_0,n_1},{n_2,n_3}}
E2 = matrix{{e_0,e_1},{n_0+e_0,n_1*e_1}}
E3 = matrix{{e_3*n_3,e_1},{e_0,e_2*n_2}}
E4 = matrix{{n_1,n_3},{n_0,n_2+n_3}}
G = superMatrix(e1,e2,e3,e4)
assert(isSuperMatrixHomogeneous(G,t,{e_0,e_1,e_2,e_3})==true)
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
-------------------- 
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
    Let $R_1$ and $R_2$ be Two Polynomial rings on different set of variables
    A superRing is a new polynomial ring with three sets of variables. 
    One set comes from $R_1$ and the second one is the inverse of it.
    For example, if we have $x$ as a variable in $R_1$,
    then there is a new variable, say $y_0$ which is the inverse of $x$.
    The third set of variables comes from $R_2$.
    We redefine this set to be a set of skew-symmetric variables.
    So superRing of $R_1$ and $R_2$ is a quotient ring,
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
  Supermatrix
Description
   Let $M_1,M_2,M_3,M_4$ are four matrices. 
   The number of rows in $M_1$ and $M_2$,
   and those of $M_3$ and $M_4$ should be equal.
   Also, the number of columns of $M_1$ and $M_3$,
   and those of $M_2$ and $M_4$ must be equal.
   The idea is to define a (super) Matrix,
   which can be considered as $p|q\times r|s$ matrix.
   This super Matrix can be a morphism between super
   modules $A^{p|q}$ and $A^{r|s}$ over super algebra $A$. 

   The function merges the matrices $M_1$ and $M_2$, and also $M_3$ and $M_4$. 
   Finally it merges two new matrices and 
   make a new matrix with the first four matrices as
   the blocks of the new matrix, say $\begin{bmatrix}M_1 & M_2 \\
   M_3 & M_4   \end{bmatrix}$.
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
  If $M=\begin{bmatrix}M_1 & M_2 \\ M_3 & M_4   \end{bmatrix}$ is a super Matrix, and
  $M_4$ is invertible, then 
  $Ber(M)= \det(M_1-M_2M^{-1}_4M_3)\det(M_4)^{-1}$.
  
  If $M_1$ is invertible, then 
  $ Ber(M) = det(M_4-M_3M_1^{-1}M_2)^{-1}\det(M_1)$.
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
  Let we have a super algebra (ring), $R=R_0\oplus R_1$.
  A homogeneous element of $R$ is an element belongs to $R_0$ or $R_1$.
  If $x\in R_0$, we say $x$ is even, and if $x\in R_1$, we say $x$ is odd.

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
  A super Matrix $M=\begin{bmatrix}M_1 & M_2 \\ M_3 & M_4   \end{bmatrix}$
  is invertible, if both the diagonal blocks, $M_1$ and $M_4$ are invertible.
  In this case, the inverse is given by a blocked matrix,
  $T=\begin{bmatrix}T_1 & T_2 \\ T_3 & T_4   \end{bmatrix}$, where
  
  $T_1=(M_1 − M_2M^{-1}_4 M_3)^{-1}$,
  $T_2=−M^{-1}_1 M_2(M_4 − M_3M^{-1}_1 M_2)^{-1}$,
  $T_3=−M^{-1}_4 M_3(M_1 − M_2M^{-1}_4 M_3)^{-1}$, and
  $T_4=(M_4 − M_3M^{-1}_1 M_2)^{-1}$.
 Example
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
