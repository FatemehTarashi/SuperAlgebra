newPackage(
  "SuperLinearAlgebra",
  Version => "0.1", 
  Date => "29 January 2021",
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
<<<<<<< Updated upstream
    --Types
        "SuperMatrix",
    --Methods
        "Berezinian",
        "inverseSuperMatrix",
        "Parity",
        "superMatrix",
        "superMatrixParity",
        "superRing",
        "superTrace",
    --Symbols
        "supermatrix",
        "targetM1",
        "targetM3", 
	"sourceM1", 
	"sourceM2"
 }

--------------------------------------------------------------
--SuperRing (Super commutative ring) 
--------------------------------------------------------------
=======
   -- Types
    "SuperMatrix", 
    
   -- Methods
    "berezinian", 
    "inverseSuperMatrix", 
    "parity", 
    "superMatrixGenerator", 
    "superMatrixParity", 
    "superRing", 
    "superTrace", 
    
   -- Symbols
    "supermatrix"
}

--------------------
-- SuperRing (Super commutative ring) 
--------------------

>>>>>>> Stashed changes
superRing = method();
superRing (PolynomialRing,PolynomialRing):= (R1,R2) -> (
         n := #gens R1;
         inverseVariable := symbol inverseVariable;
 	 R11 := symbol R11; 
	 R22 := symbol R22; 
	 R111 := symbol R111;
         R11 = (coefficientRing R1)[R1_0..R1_(n-1),inverseVariable_0..inverseVariable_(n-1)];
	 R111 = R11/apply(0..(n-1), i -> sub(R1_i,R11) * inverseVariable_i - 1);
         m := #gens R2;
         w := (for i to m-1 list (0))|toList(0..(m-1));
         R22 = (coefficientRing R2)[R2_0..R2_(m-1), MonomialOrder=>{Weights => w,Lex}, SkewCommutative=>true];
         print concatenate {"is a super commutative ring of dimension", toString n, "|",toString m};
         R111**R22
         )         
 
<<<<<<< Updated upstream
------------------------------------------------------
--SuperMatrix
--This a is new mulitivariate Hash table with 5 keys.
--supermatrix, targetM1, targetM3, sourceM1, sourceM2
------------------------------------------------
SuperMatrix = new Type of MutableHashTable;
=======
--------------------
-- SuperMatrix
-------------------------------------------

SuperMatrix = new Type of MutableHashTable;
superMatrix = method();
superMatrix (Matrix, Matrix, Matrix, Matrix) := (M00,M01,M10,M11)-> (
    new SuperMatrix from {
        supermatrix => matrix{{M00,M01},{M10,M11}}
    }
)
>>>>>>> Stashed changes

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
<<<<<<< Updated upstream
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
=======
M1 = matrix {{1, 2}, {5, 6}, {9, 10}};
M2 = matrix {{3, 4}, {7, 8}, {11, 12}};
M3 = matrix {{13, 14}, {17, 18}};
M4 = matrix {{15, 16}, {19, 20}};
G = superMatrix(M1,M2,M3,M4)
assert(G.supermatrix == matrix {{1, 2, 3, 4}, {5, 6, 7, 8}, {9, 10, 11, 12}, {13, 14, 15, 16}, {17, 18, 19, 20}})
>>>>>>> Stashed changes
///

--------------------
--Parity  
-------------------- 
Parity = method();
Parity (RingElement,Ring,List) := (f,R,a) -> (
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
    if (countEvenNumber -1) == #e then 0 else if (countEvenNumber -1) == 0 then 1 else -1
    ) 

Parity (Number,Ring,List) := (f,R,a) -> (
    0
    ) 

TEST ///
R1 = QQ[x_0..x_3];
R2 = QQ[z_0,z_1];
R = superRing(R1,R2);
a={z_0,z_1} ;
g=x_1*x_2*x_3+4;
f=x_1*x_2*x_3+x_1*z_0+z_1*z_0-4*x_2*z_1*z_0+4;
h=z_0+z_0*x_0+z_1;
assert(Parity(f,R,a) == -1)
assert(Parity(g,R,a) == 0)
assert(Parity(h,R,a) == 1)
assert(Parity(1+2.5*ii,R,a) == 0)
///
<<<<<<< Updated upstream
----------------------------------
--SuperMatrixParity
--------------------------------
superMatrixParity = method();
superMatrixParity(SuperMatrix,Ring,List) := (SM,R1,a) ->(
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
    if isSkewCommutative(R1)==true then
    (fij := symbol fij;
     cout33:= symbol cout33;
     cout44:= symbol cout44;
     count12:= symbol count12;
     count1:= symbol count1;
     count1=0;
     count11:=symbol count12;
     count11=0;
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
	    if fij==0 then count1 = count1 else
	    if (Parity(fij,R1,a)==-1) then (count11 = count11 +1) else
	       if (Parity(fij,R1,a)==1) then 
	           count1 = count1+1
	           else if (Parity(fij,R1,a)==0) then count1 = count1);
	      if count11=!=0 then (return -1)else if count1 == 0 then m1= 0 else m1=1;
	for i from 0 to (r1-1) do for j from 0 to (c2-1)
	do(fij = Minor12_(i,j);
	    if fij==0 then count2 = count2 else
	   if (Parity(fij,R1,a)==-1) then (count22 = count22 + 1) else
	    if (Parity(fij,R1,a)==1)then count2 = count2+1
		else if (Parity(fij,R1,a)==0) then count2 = count2);
	   if count22=!=0 then (return -1) else if count2==0 then m2=0 else m2=1;
       for i from 0 to (r2-1) do for j from 0 to (c1-1)
       do(fij = Minor21_(i,j);
	   if fij==0 then count3 = count3 else
	   if (Parity(fij,R1,a)==-1) then (cout33=count33+1) else
	     if (Parity(fij,R1,a)==1)then count3 = count3+1
		else if (Parity(fij,R1,a)==0) then count3 = count3);
	   if count33=!=0 then (return -1) else if count3==0 then m3=0 else m3=1;
       for i from 0 to (r2-1) do for j from 0 to (c2-1)
       do(fij = Minor22_(i,j);
	   if fij==0 then count4 = count4 else
	   if (Parity(fij,R1,a)==-1) then (cout44=count44+1) else
	   if (Parity(fij,R1,a)==1)then count4 = count4+1
		else if (Parity(fij,R1,a)==0) then count4 = count4);
	  if count44=!=0 then (return -1) else if count4==0 then m4=0 else m4=1;
      R2 := symbol R2;
      R2 = coefficientRing R1;
      if (isSkewCommutative(R2)==true) then(
       if (m1==0 and m4==0 and m2==1 and m3==1)then ( return 0)
       else if (m1==1 and m4==1 and m2==0 and m3==0) then (return 1) else (return -1))
       else(
        if (m1==0 and m4==0 and Minor12==0 and Minor21==0) then  (return 0)
       else if (Minor11==0 and Minor22==0 and m2==0 and m3==0) then (return 1)
       else (return -1))
   )
=======

--------------------
-- superMatrixParity
--------------------

superMatrixParity = method();
superMatrixParity(SuperMatrix, Ring, List) := (SM, R1, a) -> (
    m1 := 0;
    m2 := 0;
    m3 := 0;
    m4 := 0;
    Minor00 := SM.supermatrix^[0]_[0];
    Minor01 := SM.supermatrix^[0]_[1];
    Minor10 := SM.supermatrix^[1]_[0];
    Minor11 := SM.supermatrix^[1]_[1];
    r1 := numgens target Minor00;
    r2 := numgens target Minor10;
    c1 := numgens source Minor00;
    c2 := numgens source Minor01;
    fij := symbol fij;
    if isSkewCommutative(R1) == true then (
        count1 := 0;
        count11 := 0;
        for i from 0 to (r1-1) do
            for j from 0 to (c1-1) do (
                fij = Minor00_(i, j);
                if fij == 0 then count1 = count1 
                else if (parity(fij, R1, a) == -1) then (count11 = count11+1) 
                else if (parity(fij, R1, a) == 1) then count1 = count1+1
                else if (parity(fij, R1, a) == 0) then count1 = count1
            );
        if count11=!=0 then (return-1) 
        else if count1 == 0 then m1= 0 
        else m1=1;    
        count2 := 0;
        count22 := 0;
        for i from 0 to (r1-1) do 
            for j from 0 to (c2-1) do (
                fij = Minor01_(i, j);
                if fij == 0 then count2 = count2 
                else if (parity(fij, R1, a) == -1) then (count22 = count22+1) 
                else if (parity(fij, R1, a) == 1)then count2 = count2+1
                else if (parity(fij, R1, a) == 0) then count2 = count2
            );
        if count22=!=0 then (return-1) 
        else if count2 == 0 then m2=0 
        else m2=1;
        count3 := 0;
        count33 := 0;
        for i from 0 to (r2-1) do 
            for j from 0 to (c1-1) do (
                fij = Minor10_(i, j);
                if fij == 0 then count3 = count3 
                else if (parity(fij, R1, a) == -1) then (cout33 := count33+1)
                else if (parity(fij, R1, a) == 1)then count3 = count3+1
                else if (parity(fij, R1, a) == 0) then count3 = count3
            );
        if count33=!=0 then (return-1) 
        else if count3 == 0 then m3=0 
        else m3=1;
        count4 := 0;
        count44 := 0;
        for i from 0 to (r2-1) do 
            for j from 0 to (c2-1) do (
                fij = Minor11_(i, j);
                if fij == 0 then count4 = count4 
                else if (parity(fij, R1, a) == -1) then (cout44 := count44+1) 
                else if (parity(fij, R1, a) == 1)then count4 = count4+1
                else if (parity(fij, R1, a) == 0) then count4 = count4
            );
        if count44=!=0 then (return-1) 
        else if count4 == 0 then m4=0 
        else m4=1;
        R2 := coefficientRing R1;
        if (isSkewCommutative(R2) == true) then (
            if (m1 == 0 and m4 == 0 and m2 == 1 and m3 == 1) then (return 0)
            else if (m1 == 1 and m4 == 1 and m2 == 0 and m3 == 0) then (return 1) 
            else (return-1)
        )
        else (
            if (m1 == 0 and m4 == 0 and Minor01 == 0 and Minor10 == 0) then  (return 0)
            else if (Minor00 == 0 and Minor11 == 0 and m2 == 0 and m3 == 0) then (return 1)
            else (return-1)
        )
    )  
>>>>>>> Stashed changes
    else (error "Ring should be a superRing")
)

TEST///
R1 = QQ[x_0..x_3];
R2 = QQ[z_0..z_2];
<<<<<<< Updated upstream
R = superRing(R1,R2);
D1 = matrix{{x_0,x_1},{x_2,x_3}};
D2 = matrix{{z_0,z_1},{x_0*z_0,x_1*z_1}};
D3 = matrix{{z_2*x_3,z_1},{z_0,z_2*x_2}};
D4 = matrix{{x_1,x_3},{x_0,x_2+x_3}};
SD = superMatrix(D1,D2,D3,D4);
assert(superMatrixParity(SD,R,{z_0,z_1,z_2}) == -1)

P1 = matrix{{0,0},{0,0}};
P2 = matrix{{x_0,x_1},{x_2,x_3}};
P3 = matrix{{x_1,x_2},{x_0,x_1}};
P4 = matrix{{0,0},{0,0}};
SP = superMatrix(P1,P2,P3,P4);
=======
R = superRing(R1, R2);
D1 = matrix{{x_0, x_1}, {x_2, x_3}};
D2 = matrix{{z_0, z_1}, {x_0*z_0, x_1*z_1}};
D3 = matrix{{z_2*x_3, z_1}, {z_0, z_2*x_2}};
D4 = matrix{{x_1, x_3}, {x_0, x_2+x_3}};
SD = superMatrix(D1, D2, D3, D4);
assert(superMatrixParity(SD, R, {z_0, z_1, z_2}) == -1)

P1 = matrix{{0, 0}, {0, 0}};
P2 = matrix{{x_0, x_1}, {x_2, x_3}};
P3 = matrix{{x_1, x_2}, {x_0, x_1}};
P4 = matrix{{0, 0}, {0, 0}};
SP = superMatrix(P1, P2, P3, P4);
>>>>>>> Stashed changes
SS = SP.supermatrix;
assert(superMatrixParity(SP,R,{z_0,z_1,z_2}) == 1)

T1 = R[n_0..n_3];
T2 = R[e_0..e_3];
<<<<<<< Updated upstream
T = superRing(T1,T2);
M1 = matrix{{n_0,n_1},{n_2,n_3}};
M2 = matrix{{e_0,e_1},{n_0*e_0,n_1*e_1}};
M3 = matrix{{e_3*n_3,e_1},{e_0,e_2*n_2}};
M4 = matrix{{n_1,n_3},{n_0,n_2+n_3}};
SM = superMatrix(M1,M2,M3,M4);
assert(superMatrixParity(SM,T,{e_0,e_1,e_2,e_3}) == 0)
---
E1 = matrix{{e_0,n_1},{n_2,n_3}};
E2 = matrix{{e_0,e_1},{n_0+e_0,n_1*e_1}};
E3 = matrix{{e_3*n_3,e_1},{e_0,e_2*n_2}};
E4 = matrix{{n_1,n_3},{n_0,n_2+n_3}};
G = superMatrix(E1,E2,E3,E4);
assert(superMatrixParity(G,T,{e_0,e_1,e_2,e_3}) == -1)
=======
T = superRing(T1, T2);
M1 = matrix{{n_0, n_1}, {n_2, n_3}};
M2 = matrix{{e_0, e_1}, {n_0*e_0, n_1*e_1}};
M3 = matrix{{e_3*n_3, e_1}, {e_0, e_2*n_2}};
M4 = matrix{{n_1, n_3}, {n_0, n_2+n_3}};
SM = superMatrix(M1, M2, M3, M4);
assert(superMatrixParity(SM, T, {e_0, e_1, e_2, e_3}) == 0)

E1 = matrix{{e_0, n_1}, {n_2, n_3}};
E2 = matrix{{e_0, e_1}, {n_0+e_0, n_1*e_1}};
E3 = matrix{{e_3*n_3, e_1}, {e_0, e_2*n_2}};
E4 = matrix{{n_1, n_3}, {n_0, n_2+n_3}};
G = superMatrix(E1, E2, E3, E4);
assert(superMatrixParity(G, T, {e_0, e_1, e_2, e_3}) == -1)
>>>>>>> Stashed changes
///
--------------------
--Supertrace           
--------------------  
superTrace = method ();
<<<<<<< Updated upstream
superTrace (SuperMatrix,Ring,List) :=(SM,R1,a)->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 -1)}, {0..(SM.sourceM1 -1)});
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 -1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 -1)});
    if (superMatrixParity(SM,R1,a)=!= -1) then
    (par := symbol par;
     par = superMatrixParity(SM,R1,a);
     trace Minor11 -(-1)^par*trace Minor22)
=======
superTrace (SuperMatrix, Ring, List)  := (SM, R1, a) -> (
    Minor00 := SM.supermatrix^[0]_[0];
    Minor11 := SM.supermatrix^[1]_[1];
    if (superMatrixParity(SM, R1, a)=!=-1) then (
        par := superMatrixParity(SM, R1, a);
        trace Minor00-(-1)^par*trace Minor11
    )
>>>>>>> Stashed changes
    else error "SuperMatrix is not superhomogeneous"
    )

TEST ///
R1 = QQ[x_0..x_3];
R2 = QQ[z_0..z_2];
<<<<<<< Updated upstream
R = superRing(R1,R2);
P1 = matrix{{x_0,x_1},{x_2,x_3}};
P2 = matrix{{0,0},{0,0}};
P3 = matrix{{0,0},{0,0}};
P4 = matrix{{x_1,x_2},{x_0,x_1}};
SP = superMatrix(P1,P2,P3,P4);
assert(superTrace(SP,R,{z_0,z_1})==x_0-2*x_1+x_3)
=======
R = superRing(R1, R2);
P1 = matrix{{x_0, x_1}, {x_2, x_3}};
P2 = matrix{{0, 0}, {0, 0}};
P3 = matrix{{0, 0}, {0, 0}};
P4 = matrix{{x_1, x_2}, {x_0, x_1}};
SP = superMatrix(P1, P2, P3, P4);
assert(superTrace(SP, R, {z_0, z_1}) == x_0-2*x_1+x_3)
>>>>>>> Stashed changes

R1 = QQ[x_0..x_3]
R2 = QQ[z_0..z_2]
R = superRing(R1,R2)
T1 = R[n_0..n_3];
T2 = R[e_0..e_3];
<<<<<<< Updated upstream
T  = superRing(T1,T2)
M1 = matrix{{n_0,n_1},{n_2,n_3}}
M2 = matrix{{e_0,e_1},{n_0*e_0,n_1*e_1}}
M3 = matrix{{e_3*n_3,e_1},{e_0,e_2*n_2}}
M4 = matrix{{n_1,n_3},{n_0,n_2+n_3}}
SM = superMatrix(M1,M2,M3,M4)
a = {e_0,e_1,e_2,e_3}
assert(superTrace(SM,T,a)==n_0-n_1-n_2)
=======
T = superRing(T1, T2)
M1 = matrix{{n_0, n_1}, {n_2, n_3}}
M2 = matrix{{e_0, e_1}, {n_0*e_0, n_1*e_1}}
M3 = matrix{{e_3*n_3, e_1}, {e_0, e_2*n_2}}
M4 = matrix{{n_1, n_3}, {n_0, n_2+n_3}}
SM = superMatrix(M1, M2, M3, M4)
a = {e_0, e_1, e_2, e_3}
assert(superTrace(SM, T, a) == n_0-n_1-n_2)
>>>>>>> Stashed changes
///

--------------------
--Berezinian
-------------------- 
<<<<<<< Updated upstream
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
=======

berezinian = method();
berezinian (SuperMatrix, Ring) := (SM, R1) -> (
    Minor00 := SM.supermatrix^[0]_[0];
    Minor01 := SM.supermatrix^[0]_[1];
    Minor10 := SM.supermatrix^[1]_[0];
    Minor11 := SM.supermatrix^[1]_[1];
    SM1 := sub(Minor00, R1);
    SM2 := sub(Minor11, R1);
    Prod1 := Minor11-Minor10*inverse(SM1)*Minor01;
    Prod2 := sub(Prod1, R1);
    if numRows Minor00 =!= numColumns Minor00 then error "expected a square matrix";
    if numRows Minor11 =!= numColumns Minor11 then error "expected a square matrix";
    if det(Minor11) =!= 0 then det(inverse(SM2))*det(Minor00-Minor01*inverse(SM2)*Minor10)
    else if (det(Minor00) =!= 0 and det(Minor11-Minor01*inverse(SM1)*Minor10) =!= 0) then det(Minor00)*det(inverse(Prod2))
>>>>>>> Stashed changes
    else error "At least one of the diagonal blocks should be invertible"
    )
 
TEST///
<<<<<<< Updated upstream
M1 = matrix{{5,7},{1,2}};
M2 = matrix{{1,2,3},{4,5,6}};
M3 = matrix{{3,4},{5,6},{7,8}};
M4 = matrix{{2,3,11},{4,5,6},{7,8,9}};
M5 = sub(M4,QQ);
G = superMatrix(M1,M2,M3,M4);
assert(Berezinian(G,QQ)== det(inverse(M5))*det(M1-M2*inverse(M5)*M3))

S1 = matrix{{1,2},{3,4}};
S2 = matrix{{5,6},{7,8}};
S3 = matrix{{9,10},{11,12}};
S4 = matrix{{0,0},{0,0}};
S5 = sub(S1,QQ);
S6 = S4 - S3*inverse(S5)*S2;
F = superMatrix(S1,S2,S3,S4);
assert(Berezinian(F,QQ) == det(S1)*det(inverse(S6)))
=======
M1 = matrix{{5, 7}, {1, 2}};
M2 = matrix{{1, 2, 3}, {4, 5, 6}};
M3 = matrix{{3, 4}, {5, 6}, {7, 8}};
M4 = matrix{{2, 3, 11}, {4, 5, 6}, {7, 8, 9}};
M5 = sub(M4, QQ);
G = superMatrix(M1, M2, M3, M4);
assert(berezinian(G, QQ) ==  det(inverse(M5))*det(M1-M2*inverse(M5)*M3))

S1 = matrix{{1, 2}, {3, 4}};
S2 = matrix{{5, 6}, {7, 8}};
S3 = matrix{{9, 10}, {11, 12}};
S4 = matrix{{0, 0}, {0, 0}};
S5 = sub(S1, QQ);
S6 = S4-S3*inverse(S5)*S2;
F = superMatrix(S1, S2, S3, S4);
assert(berezinian(F, QQ) == det(S1)*det(inverse(S6)))
>>>>>>> Stashed changes
///

------------------------
--inversesupermatrix
---------------------- 
inverseSuperMatrix = method();
<<<<<<< Updated upstream
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
=======
inverseSuperMatrix (SuperMatrix, Ring) := (SM, R1) -> (
    Minor00 := SM.supermatrix^[0]_[0];
    Minor01 := SM.supermatrix^[0]_[1];
    Minor10 := SM.supermatrix^[1]_[0];
    Minor11 := SM.supermatrix^[1]_[1];
    if numRows Minor00 =!= numColumns Minor00 then error "expected a square matrix";
    if numRows Minor11 =!= numColumns Minor11 then error "expected a square matrix";    
    SM00 := sub(Minor00, R1);
    SM11 := sub(Minor11, R1);
    SM01 := sub(Minor01, R1);
    SM10 := sub(Minor10, R1);
    Prod1 := SM11-SM10*inverse(SM00)*SM01;
    Prod2 := SM00-SM01*inverse(SM11)*SM10;
    Nminor00 := inverse(Prod2);
    Nminor01 :=-inverse(SM11)*SM10*inverse(Prod2);
    Nminor10 :=-inverse(SM00)*SM01*inverse(Prod1);
    Nminor11 := inverse(Prod1);
    if (det(SM00) =!= 0 and det (SM11) =!= 0) then matrix{{Nminor00,Nminor10},{Nminor01,Nminor11}} else error "The SuperMatrix is not invertible"
)
>>>>>>> Stashed changes

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
<<<<<<< Updated upstream
NM1 = N11 | N21;
NM2 = N12 | N22;
G = superMatrix(M1,M2,M3,M4);
assert(inverseSuperMatrix(G,QQ) == NM1 || NM2)
=======
G = superMatrix(M1, M2, M3, M4);
assert(inverseSuperMatrix(G, QQ) == matrix{{N11,N12},{N21,N22}})
>>>>>>> Stashed changes
///

--------------------

beginDocumentation()

doc ///
Key
    SuperLinearAlgebra
Headline 
    Package for super algebra
Description
<<<<<<< Updated upstream
  Text
     This Package is to do the computation in superalgebras, or super vector spaces. \break
     The computations are taken in a superRing, which is a ring with both symmetric and antisymmetric variables. \break
     To see the definitions and theorems, see Varadarajan, V. S. (2004). "Supersymmetry for Mathematicians: An Introduction" (Vol. 11). American Mathematical Soc.\break
=======
    Text
        This Package is to do the computation in superalgebras, or super vector spaces. 
     
        The computations are taken in a superRing, which is a ring with both symmetric and antisymmetric variables. 
     
        To see the definitions and theorems, see Varadarajan, V. S. (2004). "Supersymmetry for Mathematicians:
        An Introduction" (Vol. 11). American Mathematical Soc.
     
>>>>>>> Stashed changes
Caveat
SeeAlso
///


doc ///
Key
    superRing
    (superRing, PolynomialRing, PolynomialRing)
Headline
    Makes a super ring from two polynomial rings.
Usage
    R = superRing(R1, R2)
Inputs
    R1:PolynomialRing
    R2:PolynomialRing
Outputs
    R:QuotientRing
        which has both invertible and skew symmetric variables, superRing
Description
<<<<<<< Updated upstream
  Text
    Let $R_1$ and $R_2$ be Two Polynomial rings on different set of variables
    A superRing is a new polynomial ring with three sets of variables. 
    One set comes from $R_1$ and the second one is the inverse of it.\break
    For example, if we have x as a variable in $R_1$,
    then there is a new variable, say $inverseVariable_0$ which is the inverse of $x$.
    The third set of variables comes from $R_2$.
    We redefine this set to be a set of skew-symmetric variables.
    So superRing of $R_1$ and $R_2$ is a quotient ring,
    which has both invertible and skew symmetric variables.
    If the coefficient ring is a field, then we get a super algebra.
  Example
    R1=QQ[x_1..x_5]
    R2=QQ[z_1..z_3]
    superRing(R1,R2)
=======
    Text
        Let $R_1$ and $R_2$ be Two Polynomial rings on different set of variables
        A superRing is a new polynomial ring with three sets of variables. 
        One set comes from $R_1$ and the second one is the inverse of it.
    
        For example, if we have x as a variable in $R_1$, 
        then there is a new variable, say $inverseVariable_0$ which is the inverse of $x$.
        The third set of variables comes from $R_2$.
        We redefine this set to be a set of skew-symmetric variables.
        So superRing of $R_1$ and $R_2$ is a quotient ring, 
        which has both invertible and skew symmetric variables.
        If the coefficient ring is a field, then we get a super algebra.
    Example
        R1=QQ[x_1..x_5]
        R2=QQ[z_1..z_3]
        superRing(R1, R2)
>>>>>>> Stashed changes
Caveat
SeeAlso
///


doc ///
Key 
<<<<<<< Updated upstream
  SuperMatrix
  superMatrix
  supermatrix
  (superMatrix,Matrix,Matrix,Matrix,Matrix)
  sourceM1
  sourceM2
  targetM1
  targetM3
=======
    SuperMatrix
    supermatrix
    (superMatrix , Matrix, Matrix, Matrix, Matrix)
>>>>>>> Stashed changes
Headline
    Makes a super matrix from its four blocks.
Usage
    G = superMatrix(M1, M2, M3, M4)
Inputs
    M1:Matrix
    M2:Matrix
    M3:Matrix
    M4:Matrix
Outputs
    G:SuperMatrix
Description
<<<<<<< Updated upstream
  Text
   Let $M_1,M_2,M_3,M_4$ are four matrices. 
   The number of rows in $M_1$ and $M_2$,
   and those of $M_3$ and $M_4$ should be equal.
   Also, the number of columns of $M_1$ and $M_3$,
   and those of M_2 and M_4 must be equal./break
   The idea is to define a (super) Matrix,
   which can be considered as $p|q\times r|s$ matrix.
   This super Matrix can be a morphism between super
   modules $A^{p|q}$ and $A^{r|s}$ over super algebra $A$.  \break

   The function merges the matrices M_1 and M_2, and also M_3 and M_4. 
   Finally it merges two new matrices and 
   make a new matrix with the first four matrices as
   the blocks of the new matrix, say $\begin{pmatrix}
     M1&M2\\
     M3&M4\end{pmatrix}$.  \break
   The key supermatrix shows the result matrix created as above. \break
   The key targetM1 shows the number of first part rows. \break
   The key targetM3 shows the number of the rows of the second part.  \break
   The key sourceM1 shows the number of columns in the first part.  \break
   The key sourceM2 shows the number of columns in the second part.  \break
 Example
    M1 = matrix {{1,2},{5,6},{9,10}}
    M2 = matrix {{3,4},{7,8},{11,12}}
    M3 = matrix {{13,14},{17,18}}
    M4 = matrix {{15,16},{19,20}}
    G = superMatrix(M1,M2,M3,M4)
    G.supermatrix
=======
    Text
        Let $M_1, M_2, M_3, M_4$ be four matrices. 
        The number of rows in $M_1$ and $M_2$, 
        and those of $M_3$ and $M_4$ should be equal.
        Also, the number of columns of $M_1$ and $M_3$, 
        and those of M_2 and M_4 must be equal.
   
        The idea is to define a (super) Matrix, 
        which can be considered as $p|q\times r|s$ matrix.
        This super Matrix can be a morphism between super
        modules $A^{p|q}$ and $A^{r|s}$ over super algebra $A$. 

        The function uses four matrices M_1 and M_2, and also M_3 and M_4
	as four blocks of a new matrix, say $\begin{pmatrix}
        M1&M2\\
        M3&M4\end{pmatrix}$.  
     
        The key supermatrix shows the result matrix created as above.
    Example
        M1 = matrix {{1, 2}, {5, 6}, {9, 10}}
        M2 = matrix {{3, 4}, {7, 8}, {11, 12}}
        M3 = matrix {{13, 14}, {17, 18}}
        M4 = matrix {{15, 16}, {19, 20}}
        G = superMatrix(M1, M2, M3, M4)
        G.supermatrix
>>>>>>> Stashed changes
Caveat
SeeAlso
///


doc ///
Key 
    superTrace
    (superTrace, SuperMatrix, Ring, List)
Headline
    Super trace of a homogeneous super matrix.
Usage
    P = superTrace(SM, R, L)
Inputs
    SM:SuperMatrix
    R:Ring
        superRing
    L:List
Outputs
    P:QuotientRing
Description
<<<<<<< Updated upstream
  Text
    Let $A^{p|q}=Ax_1 \oplus \cdots \oplus Ax_p \oplus Ae_1\oplus \cdots \oplus Ae_q$ be a free module over $A$, 
    where $x_i$s are even and $e_j$s are odd generators. A (homogeneous) morphism $T:A^{p|q}\rightarrow A^{r|s}$ has a matrix representation. 
    Denote the matrix by $T$ then we have $T=\begin{pmatrix}
     T1&T2\\
     T3&T4\end{pmatrix}$.  \break
    The super trace of $T$ is defined by $superTrace(T)= Trace(T_1)-(-1)^{p(T)} Trace(T_4)$.
    The inputs of this function are a superMatrix, a ring, which should have skew-symmetric variables, and a list, 
    which is the list of skew-symmetric variables that are used in the superMatrix. 
    In case that the superMatrix is homogeneous, the output is the super trace of the superMatrix.
	
 Example
    R1 = QQ[x_0..x_3];
    R2 = QQ[z_0..z_2];
    R = superRing(R1,R2);
    P1 = matrix{{x_0,x_1},{x_2,x_3}};
    P2 = matrix{{0,0},{0,0}};
    P3 = matrix{{0,0},{0,0}};
    P4 = matrix{{x_1,x_2},{x_0,x_1}};
    SP = superMatrix(P1,P2,P3,P4);
    superTrace(SP,R,{z_0,z_1})
=======
    Text
        Let $A^{p|q}=Ax_1 \oplus \cdots \oplus Ax_p \oplus Ae_1\oplus \cdots \oplus Ae_q$ be a free module over $A$, 
        where $x_i$s are even and $e_j$s are odd generators. A (homogeneous) morphism $T:A^{p|q}\rightarrow A^{r|s}$ has a matrix representation. 
        Denote the matrix by $T$ then we have $T=\begin{pmatrix}
         T1&T2\\
         T3&T4\end{pmatrix}$.  
     
        The super trace of $T$ is defined by $superTrace(T)= Trace(T_1)-(-1)^{p(T)} Trace(T_4)$.
        The inputs of this function are a superMatrix, a ring, which should have skew-symmetric variables, and a list, 
        which is the list of skew-symmetric variables that are used in the superMatrixGenerator. 
        In case that the superMatrix is homogeneous, the output is the super trace of the superMatrix.
        
    Example
        R1 = QQ[x_0..x_3];
        R2 = QQ[z_0..z_2];
        R = superRing(R1, R2);
        P1 = matrix{{x_0, x_1}, {x_2, x_3}};
        P2 = matrix{{0, 0}, {0, 0}};
        P3 = matrix{{0, 0}, {0, 0}};
        P4 = matrix{{x_1, x_2}, {x_0, x_1}};
        SP = superMatrixGenerator(P1, P2, P3, P4);
        superTrace(SP, R, {z_0, z_1})
>>>>>>> Stashed changes
Caveat
SeeAlso
///

doc ///
Key 
    berezinian
    (berezinian, SuperMatrix, Ring)
Headline
    Computes the berezinian of a supermatrix.
Usage
    N = berezinian(G, R)
Inputs
    G:SuperMatrix
    R:Ring
Outputs
    N:Number
Description
<<<<<<< Updated upstream
 Text
  If in a super Matrix, one of the first or the second diagonal block is invertible,
  then we can define Berezinian (as a kind of super Determinant).
  The formula for the Berezinian is different base on which block is invertible.
  But it is shown that the two formulas are equivalent if two blocks are invertible.
  If $M=\begin{pmatrix}
     M1&M2\\
     M3&M4\end{pmatrix}$.  is a super Matrix, and
  $M_4$ is invertible, then 
  $Ber(M)= det(M_1-M_2M^{-1}_4M_3) det(M_4)^{-1}$.\break
  
  If $M_1$ is invertible, then
  $Ber(M) = det(M_4-M_3M_1^{-1}M_2)^{-1} det(M_1)$.
 Example
    M1 = matrix{{5,7},{1,2}}
    M2 = matrix{{1,2,3},{4,5,6}}
    M3 = matrix{{3,4},{5,6},{7,8}}
    M4 = matrix{{2,3,11},{4,5,6},{7,8,9}}
    M5 = sub(M4,QQ)
    G = superMatrix(M1,M2,M3,M4)
    Berezinian(G,QQ)
=======
    Text
        If in a super Matrix, one of the first or the second diagonal blocks is invertible, 
        then we can define the berezinian (as a kind of super Determinant).
        The formula for the berezinian is different base on which block is invertible.
        But it is shown that the two formulas are equivalent if two blocks are invertible.
        If $M=\begin{pmatrix}
        M1&M2\\
        M3&M4\end{pmatrix}$.  is a super Matrix, and
        $M_4$ is invertible, then 
        $Ber(M)= det(M_1-M_2M^{-1}_4M_3) det(M_4)^{-1}$.
  
        If $M_1$ is invertible, then
        $Ber(M) = det(M_4-M_3M_1^{-1}M_2)^{-1} det(M_1)$.
    Example
        M1 = matrix{{5, 7}, {1, 2}}
        M2 = matrix{{1, 2, 3}, {4, 5, 6}}
        M3 = matrix{{3, 4}, {5, 6}, {7, 8}}
        M4 = matrix{{2, 3, 11}, {4, 5, 6}, {7, 8, 9}}
        M5 = sub(M4, QQ)
        G = superMatrixGenerator(M1, M2, M3, M4)
        berezinian(G, QQ)
>>>>>>> Stashed changes
Caveat
SeeAlso
///


doc ///
Key 
    parity
    (parity, RingElement, Ring, List)
Headline
    parity of an element of a super ring.
Usage
    N = parity(f, R, L)
Inputs
    f:RingElement
    R:Ring
        superRing
    L:List
Outputs
    N:Number
        0 for even, 1 for odd and-1 for Nonhomogeneous
Description
<<<<<<< Updated upstream
 Text
  Let we have a super algebra (ring), $R=R_0 \oplus R_1$.
  A homogeneous element of $R$ is an element belongs to $R_0$ or $R_1$.
  This function has three outputs, -1 for non-homogeneous, 0 for homogeneous and even, and 1 for homogeneous and odd elements.
 Example
    R1=QQ[x_0..x_4];
    R2=QQ[e_0,e_1];
    R= superRing(R1,R2)
    L={e_0,e_1}
    f=x_1*x_2*x_3+x_1*e_0+e_1*e_0-4*x_2*e_1*e_0+4
    Parity(f,R,L)
    g=x_1*x_2*x_3+e_0*e_1+4;
    Parity(g,R,L)
Caveat
SeeAlso
  superMatrixParity
=======
    Text
        Let we have a super algebra (ring), $R=R_0 \oplus R_1$.
        A homogeneous element of $R$ is an element belongs to $R_0$ or $R_1$.
        This function has three outputs,-1 for non-homogeneous, 0 for homogeneous and even, and 1 for homogeneous and odd elements.
    Example
        R1=QQ[x_0..x_4];
        R2=QQ[e_0, e_1];
        R= superRing(R1, R2)
        L={e_0, e_1}
        f=x_1*x_2*x_3+x_1*e_0+e_1*e_0-4*x_2*e_1*e_0+4
        parity(f, R, L)
        g=x_1*x_2*x_3+e_0*e_1+4;
        parity(g, R, L)
Caveat
SeeAlso
    superMatrixParity
>>>>>>> Stashed changes
///

doc ///
Key 
    inverseSuperMatrix
    (inverseSuperMatrix, SuperMatrix, Ring) 
Headline
    The inverse of a super matrix.
Usage
    N = inverseSuperMatrix(G, R)
Inputs
    G:SuperMatrix
    R:Ring
Outputs
    M:Matrix
Description
<<<<<<< Updated upstream
 Text
  A super Matrix $M={{M1,M2},{M3,M4}}$ 
  is invertible, if both the diagonal blocks, $M_1$ and $M_4$ are invertible. \break
  In this case, the inverse is given by a blocked matrix,
  $T=\begin{pmatrix}
     T1&T2\\
     T3&T4\end{pmatrix}$, where
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
=======
    Text
        A super Matrix $M={{M1, M2}, {M3, M4}}$ 
        is invertible, if both the diagonal blocks, $M_1$ and $M_4$ are invertible. 
  
        In this case, the inverse is given by a blocked matrix, 
        $T=\begin{pmatrix}
         T1&T2\\
         T3&T4\end{pmatrix}$, where
        $T_1=(M_1 − M_2M^{-1}_4 M_3)^{-1}$, 
        $T_2=−M^{-1}_1 M_2(M_4 − M_3M^{-1}_1 M_2)^{-1}$, 
        $T_3=−M^{-1}_4 M_3(M_1 − M_2M^{-1}_4 M_3)^{-1}$, and
        $T_4=(M_4 − M_3M^{-1}_1 M_2)^{-1}$.
    Example
        M1 = matrix{{5, 7}, {1, 2}};
        M2 = matrix{{1, 2, 3}, {4, 5, 6}};
        M3 = matrix{{3, 4}, {5, 6}, {7, 8}};
        M4 = matrix{{2, 3, 11}, {4, 5, 6}, {7, 8, 9}};
        G = superMatrixGenerator(M1, M2, M3, M4);
        inverseSuperMatrix(G, QQ)
>>>>>>> Stashed changes
Caveat
SeeAlso
///

doc ///
Key 
    superMatrixParity
    (superMatrixParity, SuperMatrix, Ring, List) 
Headline
<<<<<<< Updated upstream
  Parity of a super Matrix.
Usage
  N = superMatrixParity(SM,R,L)
Inputs
  SM:SuperMatrix
  R:Ring
    superRing
  L:List
=======
    parity of a super Matrix.
Usage
    N = superMatrixParity(SM, R, L)
Inputs
    SM:SuperMatrix
    R:Ring
        superRing
    L:List
>>>>>>> Stashed changes
Outputs
    N:Number
        0 for even, 1 for odd and-1 for Nonhomogeneous
Description
<<<<<<< Updated upstream
 Text
  Let $A^{p|q}=Ax_1\oplus \cdots \oplus Ax_p \oplus Ae_1\oplus\cdots\oplus Ae_q$ be a free module over $A$, where $x_i$s are even and $e_j$s are odd generators. A morphism $T:A^{p|q}\rightarrow A^{r|s}$ has a matrix representation. Denote the matrix by $T$ then we have
  $T=\begin{pmatrix}
     T1&T2\\
     T3&T4\end{pmatrix}$. \break
  The matrix (morphism) $T$ is said to be even (odd) if the blocks $T_1$ and $T_4$ are even, and $T_2$ and $T_3$ are odd ($T_1$ and $T_4$ are odd, and $T_2$ and $T_3$ are even).
  Note that if $A$ is an algebra, i.e., it doesn't have odd involution, then to have an even (odd) matrix $T$, we should have $T_3=0$ and $T_2=0$ ($T_1=0$ and $T_4=0$).
 Example
  R1 = QQ[x_0..x_3];
  R2 = QQ[z_0..z_2];
  R = superRing(R1,R2);
  D1 = matrix{{x_0,x_1},{x_2,x_3}};
  D2 = matrix{{z_0,z_1},{x_0*z_0,x_1*z_1}};
  D3 = matrix{{z_2*x_3,z_1},{z_0,z_2*x_2}};
  D4 = matrix{{x_1,x_3},{x_0,x_2+x_3}};
  SM = superMatrix(D1,D2,D3,D4);
  superMatrixParity(SM,R,{z_0,z_1,z_2})
Caveat
SeeAlso
  Parity
///

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
=======
   Text
        Let $A^{p|q}=Ax_1\oplus \cdots \oplus Ax_p \oplus Ae_1\oplus\cdots\oplus Ae_q$ 
        be a free module over $A$, where $x_i$s are even and $e_j$s are odd generators. 
        A morphism $T:A^{p|q}\rightarrow A^{r|s}$ has a matrix representation. 
        Denote the matrix by $T$ then we have
        $T=\begin{pmatrix}
         T1&T2\\
         T3&T4\end{pmatrix}$. 
     
        The matrix (morphism) $T$ is said to be even (odd) if the blocks $T_1$ and $T_4$
        are even, and $T_2$ and $T_3$ are odd ($T_1$ and $T_4$ are odd, and $T_2$ and $T_3$ are even).
        Note that if $A$ is an algebra, i.e., it doesn't have odd involution, then to 
        have an even (odd) matrix $T$, we should have $T_3=0$ and $T_2=0$ ($T_1=0$ and $T_4=0$).
    Example
        R1 = QQ[x_0..x_3];
        R2 = QQ[z_0..z_2];
        R = superRing(R1, R2);
        D1 = matrix{{x_0, x_1}, {x_2, x_3}};
        D2 = matrix{{z_0, z_1}, {x_0*z_0, x_1*z_1}};
        D3 = matrix{{z_2*x_3, z_1}, {z_0, z_2*x_2}};
        D4 = matrix{{x_1, x_3}, {x_0, x_2+x_3}};
        SM = superMatrixGenerator(D1, D2, D3, D4);
        superMatrixParity(SM, R, {z_0, z_1, z_2})
Caveat
SeeAlso
    parity
///

end 
>>>>>>> Stashed changes
