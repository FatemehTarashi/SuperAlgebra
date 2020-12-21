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
   "SuperRing",
   "SuperMatrix",
   "ishomogeneouse (isodd and iseven)",
   "Str",
   "Ber",
   "InverseSuperMatrix"
 }

--------------------
--SuperRing (Super commutative ring)
--------------------

restart
SuperRing = method();
SuperRing (PolynomialRing,PolynomialRing):= (R1,R2) -> (
         n := #gens R1;
         y := symbol y;
         R11 = (coefficientRing R1)[R1_0..R1_(n-1),y_0..y_(n-1)]/apply(0..(n-1), i -> x_i * y_i - 1);   
         m := #gens R2;
         w := (for i to m-1 list (0))|toList(0..(m-1));
         R22 = (coefficientRing R2)[R2_0..R2_(m-1), MonomialOrder=>{Weights => w,Lex}, SkewCommutative=>true];
         print concatenate {"is a super commutative ring of dimension", toString m, "|",toString n};
         R11**R22
         )
     
TEST ///
R = QQ[x_1..x_5]
G = QQ[z_1,z_2]
SuperRing(R,G)
///
  
--------------------
--SuperMatrix
-------------------- 
restart
SuperMatrix = new Type of MutableHashTable;
--a SuperMatrix always has the following keys:
-- supermatrix, targetM1, targetM3, sourceM1, sourceM2

superMatrix = method();
superMatrix (Matrix,Matrix,Matrix,Matrix):= (M1,M2,M3,M4) ->(
         nr1 := numgens target M1;
         nr2 := numgens target M3;
         ns1 := numgens source M1;
         ns2 := numgens source M2;
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
M1 = matrix {{2,3},{4,5},{6,7}}
M2 = matrix {{2,3},{4,5},{6,7}}
M3 = matrix {{2,3},{4,5}}
M4 = matrix {{2,3},{5,6}}
G = superMatrix(M1,M2,M3,M4)
G.supermatrix
///


--------------------
--Supertrace
Str = method ();
Str SuperMatrix :=(SM)->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 -1)}, {0..(SM.sourceM1 -1)});
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 -1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2 -1)});
    trace Minor11 - trace Minor22
    )
--------------------  
TEST ///
M1 = matrix {{2,3},{4,5}}
M2 = matrix {{2,3,8},{4,5,9}}
M3 = matrix {{2,3},{4,5},{10,11}}
M4 = matrix {{2,3,18},{5,6,19},{16,17,20}}
G = superMatrix(M1,M2,M3,M4)
G.supermatrix
Str (G)
///

--------------------------------
--Berezinian
-----------------------------
Ber = method();
Ber SuperMatrix := (SM) ->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)}); 
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)});
    Minor21 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor12 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2  - 1)});
    if det(Minor11) != 0 then
    det(Minor11)*det(Minor22-Minor21*inverse(Minor11)*Minor12)^{-1};
    else if det(Minor22) != 0 then
    det(Minor22)^{-1}*det(Minor11-Minor12*inverse(Minor22)*Minor21);
    else error "At least one of the diagonal blocks should be invertible"
    )

------------------------
--inversesupermatrix
----------------------
-*
InverseSuperMatrix = method();
InverseSuperMatrix SuperMatrix := (SM) ->(
    Minor11 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {0..(SM.sourceM1 - 1)}); 
    Minor22 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)});
    Minor21 := submatrix(SM.supermatrix, {SM.targetM1..(SM.targetM1 + SM.targetM3 - 1)}, {0..(SM.sourceM1 - 1)});
    Minor12 := submatrix(SM.supermatrix, {0..(SM.targetM1 - 1)}, {SM.sourceM1..(SM.sourceM1 + SM.sourceM2  - 1)});
    if det(Minor11) != 0 and det (Minor22) != 0 then
    
    else error "The SuperMatrix is not invertible"
    )
*-
beginDocumentation()

doc ///
Key
  SuperLinearAlgebra
Headline
  Package for super algebra
Description
  Text
    Todo
  Example
    todo
Caveat
SeeAlso
///

doc ///
Key
  SuperRing
Headline
  Super Ring
Description
  Text
    Todo
  Example
    R1 = RR[x_1..x_4]
    R2 = RR[t_1..t_3]
    Superring(R1,R2)
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
path={"/home/ftk/SuperLinearAlgebra"}|path 
--path={"/home/feri/Documents/SuperLinearAlgebra"}|path
loadPackage("SuperLinearAlgebra",Reload=>true)
debug (SuperLinearAlgebra)

check"SuperLinearAlgebra"
installPackage"SuperLinearAlgebra"
