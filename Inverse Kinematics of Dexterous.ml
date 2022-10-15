needs "CNU/matrixanalysis.ml";;
needs "CNU/det_continuous.ml";;
needs "CNU/R_csy_part.ml";;


(* ------------------------------------------------------------------------- *)
(* homogeneous transformation of matrix                                      *)
(* ------------------------------------------------------------------------- *)
    
let homo_trans = new_definition
    `(homo_trans:real^N->real^N^N->real^(N,1)finite_sum^(N,1)finite_sum) x R = 
     (lambda i j. if i = (dimindex(:N) + 1) /\ ~(j = dimindex(:N) + 1) then &0
                 else if i = (dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then &1
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`;;

let point_tybij = new_type_definition "point" ("mk_point","dest_point") 
    (prove(`?x:real^N. T`,REWRITE_TAC[]));;
                           
let homo_point = new_definition
    `(homo_point:(N)point->real^(N,1)finite_sum) x = 
     (lambda i. if i = (dimindex(:N) + 1) then &1
                 else (dest_point x)$i )`;;

let HOMO_TRANS_COMPONENT = prove
    (`!x:real^N R:real^N^N i j.
        1 <= i /\ i <= dimindex(:N) + 1 /\
        1 <= j /\ j <= dimindex(:N) + 1 ==>
        (homo_trans x R)$i$j = 
        (if i = (dimindex(:N) + 1) /\ ~(j = dimindex(:N) + 1) then &0
                 else if i = (dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then &1
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`,
     SIMP_TAC[homo_trans;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1]);;

let HOMO_TRANS_EQ_MAT = prove                           
    (`homo_trans ((vec 0):real^N) (mat 1) = mat 1`,
    SIMP_TAC[homo_trans;CART_EQ;LAMBDA_BETA;VEC_COMPONENT;MAT_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    UNDISCH_TAC `~(~(i = dimindex (:N) + 1) /\ i' = dimindex (:N) + 1)` THEN
    UNDISCH_TAC `~(i = dimindex (:N) + 1 /\ i' = dimindex (:N) + 1)` THEN
    UNDISCH_TAC `~(i = dimindex (:N) + 1 /\ ~(i' = dimindex (:N) + 1))` THEN
    SIMP_TAC[GSYM IMP_CONJ] THEN
    SIMP_TAC[TAUT `((~(P /\ ~Q) /\ ~(P /\ Q)) /\ ~(~P /\ Q)) <=> (~P /\ ~Q)`] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `i <= dimindex (:(N,1)finite_sum)` THEN
    UNDISCH_TAC `i' <= dimindex (:(N,1)finite_sum)` THEN
    SIMP_TAC[ARITH_RULE `m <= n + 1 <=> m <= n \/ m = n + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    ASM_MESON_TAC[MAT_COMPONENT]);;

let HOMO_POINT_MK_POINT = prove
    (`!x:real^N. homo_point (mk_point x) = 
            (lambda i. if i = (dimindex(:N) + 1) then &1
                        else x$i )`,
    MESON_TAC[homo_point;point_tybij;CART_EQ;LAMBDA_BETA]);;
    
let HOMO_TRANS_MUL_POINT = prove    
    (`!x y:real^N R:real^N^N. (homo_trans x R) ** (homo_point (mk_point y)) = homo_point (mk_point (R ** y + x))`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[homo_trans;HOMO_POINT_MK_POINT;
             CART_EQ;LAMBDA_BETA;matrix_vector_mul] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THENL 
    [SIMP_TAC[REAL_ARITH `x + &1 * &1 = &1 <=> x = &0`] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN BETA_TAC THEN
     MESON_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`;REAL_MUL_LZERO]; ALL_TAC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT;GSYM matrix_vector_mul;
             REAL_MUL_RID;REAL_EQ_ADD_RCANCEL] THEN
    UNDISCH_TAC `1 <= i /\ i <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ Q /\ (P \/ R) <=> (~P /\ Q /\ R)`;
             GSYM IMP_CONJ;LE;dot;MATRIX_VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN BETA_TAC THEN
    SIMP_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`]);;
    
let HOMO_TRANS_MUL_TRANS_POINT = prove
    (`!x1 x2 y:real^N R1 R2:real^N^N. 
    (homo_trans x1 R1) ** (homo_trans x2 R2) ** (homo_point (mk_point y)) = 
    homo_point (mk_point (R1 ** R2 ** y + (x1 + R1 ** x2)))`,
    REWRITE_TAC[HOMO_TRANS_MUL_POINT;MATRIX_VECTOR_MUL_ADD_LDISTRIB;VECTOR_ADD_AC]);;

let MATRIX_EQ_HOMO_POINT = prove 
    (`!A:real^(N,1)finite_sum^M B. 
        (A = B) = !y:real^N. A ** (homo_point (mk_point y)) = B ** (homo_point (mk_point y))`, 
    REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN `i:num` o SPEC `(vec 0):real^N`) THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA;
             HOMO_POINT_MK_POINT; VEC_COMPONENT] THEN
    SIMP_TAC[COND_RAND; REAL_MUL_RZERO] THEN
    SIMP_TAC[SUM_DELTA] THEN
    SIMP_TAC[IN_NUMSEG;DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;DIMINDEX_GE_1;REAL_MUL_RID] THEN
    REPEAT STRIP_TAC THEN 
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN `i:num` o SPEC `(basis i):real^N`) THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; HOMO_POINT_MK_POINT; basis] THEN
    DISCH_THEN(MP_TAC o SPEC `i':num`) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    SIMP_TAC[ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
    ARITH_RULE `i <= x ==> ~(i = SUC x)`;DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    ASM_SIMP_TAC[REAL_MUL_RID;REAL_EQ_ADD_RCANCEL] THEN
    ASM_SIMP_TAC[LAMBDA_BETA;COND_RAND; REAL_MUL_RZERO] THEN
    SIMP_TAC[SUM_DELTA;REAL_MUL_RID] THEN
    ASM_CASES_TAC `i' = SUC (dimindex (:N))` THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `i' <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i' = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ (P \/ R) <=> (~P /\ R)`;GSYM IMP_CONJ;LE] THEN
    ASM_SIMP_TAC[IN_NUMSEG;IMP_CONJ]);;
  
let HOMO_TRANS_MUL_TRANS = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
    (homo_trans x1 R1) ** (homo_trans x2 R2) = homo_trans (x1 + R1 ** x2) (R1 ** R2)`, 
    MESON_TAC[MATRIX_EQ_HOMO_POINT;HOMO_TRANS_MUL_POINT;HOMO_TRANS_MUL_TRANS_POINT;MATRIX_VECTOR_MUL_ASSOC]);;
    
let INVERTIBLE_HOMO_TRANS = prove
    (`!x:real^N R:real^N^N. invertible R ==> invertible (homo_trans x R)`,
    REPEAT STRIP_TAC THEN SIMP_TAC[invertible] THEN
    EXISTS_TAC `homo_trans (-- (matrix_inv (R:real^N^N)) ** (x:real^N)) (matrix_inv R)` THEN
    ASM_SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_INV;MATRIX_VECTOR_MUL_ASSOC;
                 MATRIX_MUL_RNEG;MATRIX_VECTOR_MUL_LNEG;MATRIX_VECTOR_MUL_LID;
                 VECTOR_ADD_RINV;VECTOR_ADD_LINV;HOMO_TRANS_EQ_MAT]);;

let MATRIX_INV_HOMO_TRANS = prove    
    (`!x:real^N R:real^N^N. invertible R ==> 
    matrix_inv (homo_trans x R) = homo_trans (-- (matrix_inv R) ** x) (matrix_inv R)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_LEFT THEN
    ASM_SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_INV;MATRIX_VECTOR_MUL_LNEG;VECTOR_ADD_LINV;HOMO_TRANS_EQ_MAT]);;

let HOMO_POINT_MK_POINT_UNIQUE = prove
    (`!x1 x2:real^N. homo_point (mk_point x1) = homo_point (mk_point x2) <=> x1 = x2`,
    REPEAT GEN_TAC THEN SIMP_TAC[HOMO_POINT_MK_POINT;CART_EQ;LAMBDA_BETA] THEN 
    EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;LE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ARITH_TAC);;

let HOMO_TRANS_UNIQUE = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        homo_trans x1 R1 = homo_trans x2 R2 <=> (x1 = x2 /\ R1 = R2)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[MATRIX_EQ_HOMO_POINT;HOMO_TRANS_MUL_POINT;
             HOMO_POINT_MK_POINT_UNIQUE] THEN 
    SIMP_TAC[VECTOR_ARITH `!x1 x2 y1 y2:real^N. (y1 + x1 = y2 + x2) <=> (y1 - y2 = x2 - x1)`; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN EQ_TAC THENL
    [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `(vec 0):real^N`) THEN 
     SIMP_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ARITH `vec 0 = x2 - x1 <=> x1 = x2`] THEN STRIP_TAC THEN UNDISCH_TAC `!y. ((R1:real^N^N) - R2) ** y = x2 - x1` THEN
     ASM_SIMP_TAC[GSYM MATRIX_EQ_0;VECTOR_SUB_REFL;MATRIX_SUB_EQ];
     SIMP_TAC[VECTOR_SUB_REFL;MATRIX_SUB_REFL;MATRIX_VECTOR_MUL_LZERO]]);;

let HOMO_TRANS_SUB = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    (homo_trans x1 R1) - (homo_trans x2 R2) =
    (lambda i j. if i = (dimindex(:N) + 1) /\ ~(j = dimindex(:N) + 1) then &0
                 else if i = (dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then &0
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then (x1 - x2)$i
                           else (R1 - R2)$i$j)`,
    SIMP_TAC[homo_trans;CART_EQ;LAMBDA_BETA;MATRIX_SUB_COMPONENT] THEN
    REPEAT STRIP_TAC THEN 
    COND_CASES_TAC THENL [ASM_SIMP_TAC[REAL_SUB_0]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC[REAL_SUB_0]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC[VECTOR_SUB_COMPONENT]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_SUB_COMPONENT]);;
    
let HOMO_TRANS_LEFT_EQ_DIST = prove
    (`!x:real^N R1 R2:real^N^N. matrix_dist((homo_trans x R1), (homo_trans x R2)) = matrix_dist(R1,R2)`,
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;FNORM_EQ;matrix_mul;TRANSP_COMPONENT;
             LAMBDA_BETA;trace;VECTOR_SUB_REFL;VEC_COMPONENT] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0]);;

let HOMO_TRANS_RIGHT_EQ_DIST = prove
    (`!x1 x2:real^N R:real^N^N. 
        matrix_dist((homo_trans x1 R), (homo_trans x2 R)) = dist(x1,x2)`,
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot;
             MATRIX_SUB_REFL;MAT_0_COMPONENT] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_ADD_LID;REAL_MUL_RZERO;SUM_0]);;
    
let HOMO_TRANS_DIST_TRIANGLE = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= 
        matrix_dist(R1,R2) + dist(x1,x2)`,
    let lem1 = prove
    (`!x y.  (&0 <= x /\ &0 <= y) ==> (&0 <= x * y)`,
    SIMP_TAC[REAL_MUL_POS_LE] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN ITAUT_TAC) in
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_DIST;GSYM REAL_ABS_MATRIX_DIST] THEN
    SIMP_TAC[DIST_POS_LE;MATRIX_DIST_POS_LE;REAL_ARITH `!x y. &0 <= x /\ &0 <= y ==> abs(x) + abs(y) = abs(x + y)`;REAL_LE_SQUARE_ABS] THEN
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_POW_2] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[GSYM REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC (REAL_ARITH `&0 <= C /\ &0 <= D ==> A + B <= A + C + D + B`) THEN
    SIMP_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC lem1 THEN
    SIMP_TAC[SQRT_POS_LE;REAL_POW_2;SUM_SUM_SQUARE_LE] THEN
    SIMP_TAC[SQRT_POS_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2]);;

let HOMO_TRANS_DIST_TRIANGLE_FST = prove    
    (`!x1 x2:real^N R1 R2:real^N^N. 
        dist(x1,x2) <= 
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2))`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_DIST;GSYM REAL_ABS_MATRIX_DIST] THEN
    SIMP_TAC[DIST_POS_LE;MATRIX_DIST_POS_LE;REAL_ARITH `!x y. &0 <= x /\ &0 <= y ==> abs(x) + abs(y) = abs(x + y)`;REAL_LE_SQUARE_ABS] THEN
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_LE_ADDL] THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG;REAL_LE_POW_2]);;
    
let HOMO_TRANS_DIST_TRIANGLE_SND = prove    
    (`!x1 x2:real^N R1 R2:real^N^N. 
        matrix_dist(R1,R2) <= 
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2))`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_DIST;GSYM REAL_ABS_MATRIX_DIST] THEN
    SIMP_TAC[DIST_POS_LE;MATRIX_DIST_POS_LE;REAL_ARITH `!x y. &0 <= x /\ &0 <= y ==> abs(x) + abs(y) = abs(x + y)`;REAL_LE_SQUARE_ABS] THEN
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_LE_ADDR] THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG;REAL_LE_POW_2]);;
        
let HOMO_TRANS_DIST_TRIANGLE_LE_FST = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e ==> dist(x1,x2) <= e`,
    MESON_TAC[REAL_LE_TRANS; HOMO_TRANS_DIST_TRIANGLE_FST]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LE_SND = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e ==> matrix_dist(R1,R2) <= e`,
    MESON_TAC[REAL_LE_TRANS; HOMO_TRANS_DIST_TRIANGLE_SND]);;

let HOMO_TRANS_DIST_TRIANGLE_LT_FST = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e ==> dist(x1,x2) < e`,
    MESON_TAC[REAL_LET_TRANS; HOMO_TRANS_DIST_TRIANGLE_FST]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LT_SND = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e ==> matrix_dist(R1,R2) < e`,
    MESON_TAC[REAL_LET_TRANS; HOMO_TRANS_DIST_TRIANGLE_SND]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LE = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist(R1,R2) + dist(x1,x2) <= e ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e`,
    MESON_TAC[REAL_LE_TRANS; HOMO_TRANS_DIST_TRIANGLE]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LT = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist(R1,R2) + dist(x1,x2) < e ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e`,
    MESON_TAC[REAL_LET_TRANS; HOMO_TRANS_DIST_TRIANGLE]);;

let HOMO_TRANS_DIST_TRIANGLE_HALF_LE = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist(R1,R2) <= e / &2 /\ dist(x1,x2) <= e / &2 ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMO_TRANS_DIST_TRIANGLE_LE THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LE_ADD2;
                  HOMO_TRANS_DIST_TRIANGLE_LE_FST;HOMO_TRANS_DIST_TRIANGLE_LE_SND]);;
    
let HOMO_TRANS_DIST_TRIANGLE_HALF_LT = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist(R1,R2) < e / &2 /\ dist(x1,x2) < e / &2 ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMO_TRANS_DIST_TRIANGLE_LT THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LT_ADD2;
                  HOMO_TRANS_DIST_TRIANGLE_LT_FST;HOMO_TRANS_DIST_TRIANGLE_LT_SND]);;

let INVERTIBLE_HOMO_TRANS_MAT = prove 
    (`!x:real^N. invertible (homo_trans x (mat 1))`,
    GEN_TAC THEN SIMP_TAC[INVERTIBLE_LEFT_INVERSE] THEN 
    EXISTS_TAC `homo_trans (--(x:real^N)) (mat 1)` THEN
    SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_LID;
             MATRIX_MUL_LID;VECTOR_ADD_LINV;HOMO_TRANS_EQ_MAT]);;
             
let INVERTIBLE_HOMO_TRANS_VEC = prove     
    (`!R:real^N^N. invertible R ==> invertible (homo_trans (vec 0) R)`,
    REPEAT STRIP_TAC THEN SIMP_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `homo_trans (vec 0) (matrix_inv (R:real^N^N))` THEN
    ASM_SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_RZERO;
             MATRIX_INV;VECTOR_ADD_LID;HOMO_TRANS_EQ_MAT]);;
             
let HOMO_TRANS_SPLIT = prove
    (`!x:real^N R:real^N^N. 
        homo_trans x R = (homo_trans x (mat 1)) ** (homo_trans (vec 0) R)`,
    SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_RZERO;
             MATRIX_MUL_LID;VECTOR_ADD_RID;HOMO_TRANS_UNIQUE]);;

(*------------------------------------------------------------*)


let MATRIX_POW_SIM = prove
    (`!A:real^N^N P:real^N^N n. invertible P ==>
    (((matrix_inv P) ** A ** P) matrix_pow n) = 
    (matrix_inv P) ** (A matrix_pow n) ** P`,
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    STRIP_TAC THEN SIMP_TAC [matrix_pow] THENL
    [ASM_SIMP_TAC[MATRIX_MUL_LID;MATRIX_INV] ;ALL_TAC] THEN
    ASM_SIMP_TAC[MESON [MATRIX_MUL_ASSOC] `((IP:real^N^N) ** (A:real^N^N) ** P) ** IP **
    (AP:real^N^N) ** (P:real^N^N) = IP ** A ** (P ** IP) **AP **P`] THEN
    ASM_SIMP_TAC[MATRIX_INV] THEN MESON_TAC[MATRIX_MUL_LID;MATRIX_MUL_ASSOC]);;

let MSUMMABLE_MATRIX_EXP = prove
    (`!A:real^N^N. msummable (from 0) (\n. &1 / &(FACT n) %% A matrix_pow n)` ,
    SIMP_TAC[GSYM MSUMS_INFSUM;MATRIX_EXP_CONVERGES;GSYM matrix_exp]);;

let MSUMMABLE_LMUL = prove
    (`!s x:num->real^N^M A:real^M^P. 
    msummable s x ==> msummable s (\n. A ** (x n))`,
    REWRITE_TAC[msummable] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(A:real^M^P) ** (l:real^N^M)` THEN 
    ASM_SIMP_TAC[MSERIES_LMUL] );;
 
let MSUMMABLE_RMUL = prove
    (`!s x:num->real^N^M A:real^P^N. 
    msummable s x ==> msummable s (\n. (x n) ** A)`,
    REWRITE_TAC[msummable] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(l:real^N^M) ** (A:real^P^N)` THEN 
    ASM_SIMP_TAC[MSERIES_RMUL] );;

let MATRIX_EXP_ID_EQ = prove
    (`!A:real^N^N P:real^N^N . invertible P ==>
    (((matrix_inv P )** matrix_exp A ** P) = 
    matrix_exp ((matrix_inv P) ** A ** P))`,
    REPEAT STRIP_TAC THEN SIMP_TAC[matrix_exp] THEN
    ASM_SIMP_TAC[MATRIX_POW_SIM] THEN 
    SIMP_TAC[MESON [MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_MUL_ASSOC] 
    `c %% (x ** y ** z) = x ** (c %% y) ** z`] THEN 
    SIMP_TAC[INFMSUM_RMUL;INFMSUM_LMUL;MSUMMABLE_MATRIX_EXP;
    MSUMMABLE_LMUL;MSUMMABLE_RMUL]);;

let homo_trans_derivative = new_definition
    `(homo_trans_derivative:real^N->real^N^N->real^(N,1)finite_sum^(N,1)finite_sum) x R = 
     (lambda i j. if i = (dimindex(:N) + 1) then &0
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`;;
                           
let homo_vector = new_definition
    `(homo_vector:real^N->real^(N,1)finite_sum) x = 
     (lambda i. if i = (dimindex(:N) + 1) then &0
                 else x$i )`;;

let HOMO_TRANS_DERIVATIVE_MUL_VECTOR = prove    
    (`!x y:real^N R:real^N^N. (homo_trans_derivative x R) ** (homo_vector y) = homo_vector (R ** y)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[homo_trans_derivative;homo_vector;
             CART_EQ;LAMBDA_BETA;matrix_vector_mul] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 
             1 <= SUC x`;DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG;
             REAL_MUL_RZERO] THEN
    GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THENL 
    [SIMP_TAC[REAL_MUL_LZERO;SUM_0;REAL_ADD_RID]; ALL_TAC] THEN
    SIMP_TAC[GSYM matrix_vector_mul;REAL_ADD_RID] THEN
    UNDISCH_TAC `1 <= i /\ i <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ Q /\ (P \/ R) <=> (~P /\ Q /\ R)`;
             GSYM IMP_CONJ;LE;dot;MATRIX_VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN BETA_TAC THEN
    SIMP_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`]);;
    
let HOMO_TRANS_DERIVATIVE_MUL_POINT = prove    
    (`!x y:real^N R:real^N^N. (homo_trans_derivative x R) ** (homo_point (mk_point y)) =
    homo_vector (R ** y + x)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[homo_trans_derivative;homo_vector;HOMO_POINT_MK_POINT;
             CART_EQ;LAMBDA_BETA;matrix_vector_mul] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG;REAL_MUL_RZERO] THEN
    GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THENL 
    [SIMP_TAC[REAL_MUL_LZERO;SUM_0;REAL_ADD_RID]; ALL_TAC] THEN
    SIMP_TAC[GSYM matrix_vector_mul;REAL_ADD_RID;VECTOR_ADD_COMPONENT;
             REAL_MUL_RID;REAL_EQ_ADD_RCANCEL] THEN
    UNDISCH_TAC `1 <= i /\ i <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ Q /\ (P \/ R) <=> (~P /\ Q /\ R)`;
             GSYM IMP_CONJ;LE;dot;MATRIX_VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN BETA_TAC THEN
    SIMP_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`]);;
    
let HOMO_TRANS_DERIVATIVE_MUL_TRANS_POINT = prove
    (`!x1 x2 y:real^N R1 R2:real^N^N. 
    (homo_trans_derivative x1 R1) ** (homo_trans_derivative x2 R2) ** (homo_point (mk_point y)) = 
    homo_vector (R1 ** R2 ** y + R1 ** x2)`,
    REWRITE_TAC[HOMO_TRANS_DERIVATIVE_MUL_POINT;
                HOMO_TRANS_DERIVATIVE_MUL_VECTOR;
                MATRIX_VECTOR_MUL_ADD_LDISTRIB]);;

let HOMO_TRANS_DERIVATIVE_MUL = prove 
    (`!x1 x2 :real^N R1 R2:real^N^N. 
    (homo_trans_derivative x1 R1) ** (homo_trans_derivative x2 R2) = 
    homo_trans_derivative (R1 ** x2) (R1 ** R2)`,
    SIMP_TAC[MATRIX_EQ_HOMO_POINT;HOMO_TRANS_DERIVATIVE_MUL_POINT;
             HOMO_TRANS_DERIVATIVE_MUL_TRANS_POINT;GSYM MATRIX_VECTOR_MUL_ASSOC]);;
    
let HOMO_TRANS_DERIVATIVE_POW = prove
    (`!x:real^N R:real^N^N n:num. 
    (homo_trans_derivative x R) matrix_pow n = 
    if n = 0 then mat 1 else homo_trans_derivative (R matrix_pow (n - 1) ** x) (R matrix_pow n)`,
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
    [SIMP_TAC[matrix_pow]; ALL_TAC] THEN
    ASM_SIMP_TAC[ADD1;ADD_SUB;matrix_pow;ARITH_RULE `~(n + 1 = 0)`] THEN
    COND_CASES_TAC THENL
    [ASM_SIMP_TAC[matrix_pow;MATRIX_MUL_RID;MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
    ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_MUL;
                 (MESON [ARITH_RULE `~(n = 0) ==> n = 1 + (n - 1)`;
                 GSYM MATRIX_POW_ADD] `~(n = 0) ==> R matrix_pow n = 
                 R matrix_pow 1 ** R matrix_pow (n - 1)`);
                 MATRIX_POW_1;MATRIX_VECTOR_MUL_ASSOC]);;
                
let HOMO_TRANS_DERIVATIVE_POW_GE_1 = prove                
    (`!x:real^N R:real^N^N n:num.
    1 <= n ==> (homo_trans_derivative x R) matrix_pow n = 
    homo_trans_derivative (R matrix_pow (n - 1) ** x) (R matrix_pow n)`,                 
    SIMP_TAC[ARITH_RULE `(1 <= n) ==> ~( n = 0)`;
             HOMO_TRANS_DERIVATIVE_POW]);;
                 
let  HOMO_TRANS_DERIVATIVE_LMUL = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
    homo_trans x1 R1 ** homo_trans_derivative x2 R2 = 
    homo_trans_derivative (R1 ** x2) (R1 ** R2)`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix_mul;homo_trans_derivative;
             homo_trans;MATRIX_VECTOR_MUL_COMPONENT;dot;
             DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL 
    [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_EQ_0 THEN ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL 
    [ASM_SIMP_TAC[] THEN SIMP_TAC[COND_RAND;REAL_MUL_RZERO] THEN 
    ONCE_SIMP_TAC[GSYM COND_SWAP] THEN 
    SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`;
             SUM_SING_NUMSEG;REAL_ADD_RID] THEN 
    ASM_SIMP_TAC[matrix_vector_mul;LAMBDA_BETA;
                 ARITH_RULE `i <= N + 1 <=> i <= N \/ i = N + 1`;
                 ARITH_RULE `~(i = N + 1) /\ (i <= N + 1) ==> 
                             i <= N`] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN 
    ASM_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[COND_RAND;REAL_MUL_RZERO] THEN 
    ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN 
    SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`;SUM_SING_NUMSEG;
             REAL_ADD_RID] THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;ARITH_RULE `~(i = N + 1) /\ (i <= N + 1) ==> i <= N`] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC);;
                 
let  HOMO_TRANS_DERIVATIVE_RMUL = prove
    (`!x1 x2:real^N R1 R2:real^N^N.     
      homo_trans_derivative x2 R2 ** homo_trans x1 R1 = 
      homo_trans_derivative (R2 ** x1 + x2) (R2 ** R1) `,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix_mul;homo_trans_derivative;
             homo_trans;MATRIX_VECTOR_MUL_COMPONENT;dot;
             VECTOR_ADD_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_EQ_0 THEN 
    ARITH_TAC;ALL_TAC] THEN 
    COND_CASES_TAC THENL [ASM_SIMP_TAC[] THEN 
    SIMP_TAC[COND_RAND;REAL_MUL_RID] THEN 
    ONCE_SIMP_TAC[GSYM COND_SWAP] THEN 
    SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`] THEN 
    SIMP_TAC[SUM_SING_NUMSEG] THEN
    ASM_SIMP_TAC[matrix_vector_mul;LAMBDA_BETA;ARITH_RULE `i <= N + 1   
                 <=> i <= N \/ i = N + 1`] THEN
    ASM_SIMP_TAC[matrix_vector_mul;LAMBDA_BETA;ARITH_RULE `~(i = N + 1)     
                 /\ (i <= N + 1) ==> i <= N`] THEN
    SIMP_TAC[ARITH_RULE `!a b c:real. a +c = b + c <=> a = b `] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN 
    ASM_SIMP_TAC[] THEN SIMP_TAC[COND_RAND;REAL_MUL_RZERO] THEN ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN 
    SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`] THEN 
    SIMP_TAC[SUM_SING_NUMSEG;REAL_ADD_RID] THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;ARITH_RULE `~(i = N + 1) /\ (i <= N + 1)   
                 ==> i <= N`] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC);;
    
let HOMO_TRANS_DERIVATIVE_ADD = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
      homo_trans_derivative x1 R1 + homo_trans_derivative x2 R2 = 
      homo_trans_derivative (x1 + x2) (R1 + R2)`,
     REPEAT GEN_TAC THEN  
     SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1;       
              homo_trans_derivative;VECTOR_ADD_COMPONENT;
              MATRIX_ADD_COMPONENT] THEN 
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;
    
let HOMO_TRANS_DERIVATIVE_SUB = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
      homo_trans_derivative x1 R1 - homo_trans_derivative x2 R2 = 
      homo_trans_derivative (x1 - x2) (R1 - R2)`,
      REPEAT GEN_TAC THEN  
      SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1;
               homo_trans_derivative;VECTOR_SUB_COMPONENT;
               MATRIX_SUB_COMPONENT] THEN 
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;
    
let HOMO_TRANS_DERIVATIVE_COMPONENT = prove
    (`!x:real^N R:real^N^N i j.
        1 <= i /\ i <= dimindex(:N) + 1 /\
        1 <= j /\ j <= dimindex(:N) + 1 ==>
        (homo_trans_derivative x R)$i$j = 
        (if i = (dimindex(:N) + 1) then &0
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`,
     SIMP_TAC[homo_trans_derivative;LAMBDA_BETA;DIMINDEX_FINITE_SUM;
              DIMINDEX_1]);;
    
let HOMO_TRANS_DERIVATIVE_CMUL = prove 
    (`!c:real x:real^N R:real^N^N. c %% homo_trans_derivative x R = 
    homo_trans_derivative (c % x) (c %% R)`,
    REPEAT GEN_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;homo_trans_derivative;
             MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT;
             DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN 
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL 
    [ASM_ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN ASM_ARITH_TAC);;

new_type_abbrev("screw",`:real^3#real^3`);;

let screw_2_matrix = new_definition
    `(screw_2_matrix:screw->real^(3,1)finite_sum^(3,1)finite_sum) s =
    lambda i j. if i <= 3 /\ j <= 3 then (vec3_2_ssm(FST s))$i$j 
    else if i <= 3 /\ j = 4 then (SND s)$i else &0`;;

let SSM_EQ_0 = prove
    (`vec3_2_ssm (vec 0) = mat 0`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;vec3_2_ssm;VEC_COMPONENT;
             MAT_0_COMPONENT;VECTOR_NEG_COMPONENT;DIMINDEX_3;FORALL_3;
             VECTOR_3;REAL_NEG_0]);;

let SCREW_POW_N_EQ_0 = prove
    (`!s n. 2 <= n /\ FST s = vec 0 ==> 
      (screw_2_matrix s) matrix_pow n = mat 0`,
    GEN_TAC THEN INDUCT_TAC THENL [ARITH_TAC ;ALL_TAC] THEN 
    STRIP_TAC THEN ASM_CASES_TAC `SUC n = 2` THENL [ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;SSM_EQ_0;
    MATRIX_POW_2;matrix_mul;MAT_0_COMPONENT;screw_2_matrix] THEN 
    SIMP_TAC[DIMINDEX_3;DIMINDEX_1;ARITH_RULE `3 + 1 = 4`;FORALL_4;
             SUM_4;COND_ID;DIMINDEX_FINITE_SUM] THEN ARITH_TAC;
    ASM_SIMP_TAC[matrix_pow;
                 ARITH_RULE `2 <= SUC n /\ ~(SUC n = 2) ==> 2 <= n`;
                 MATRIX_MUL_RZERO]]);;

let MATRIX_EXP_SCREW_COND_0 = prove
    (`!s a. FST s = vec 0 ==> matrix_exp(a %% screw_2_matrix s) = 
    mat 1 + a %% screw_2_matrix s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_exp] THEN
    MATCH_MP_TAC INFMSUM_UNIQUE THEN
    SIMP_TAC[MSERIES_FROM;MSUM_CLAUSES_LEFT;LE_0] THEN
    REWRITE_TAC[FACT;REAL_DIV_1;matrix_pow;MATRIX_CMUL_LID] THEN
    MATCH_MP_TAC MATRIX_LIM_ADD THEN
    SIMP_TAC[MATRIX_LIM_CONST;ARITH_RULE `0 + 1 = 1`] THEN
    ONCE_REWRITE_TAC[MATRIX_LIM_NULL] THEN
    MATCH_MP_TAC MATRIX_LIM_EVENTUALLY THEN
    SIMP_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `msum (1..n) (\n. &1 / &(FACT n) %% 
                 (a %% screw_2_matrix s) matrix_pow n) -
                  a %% screw_2_matrix s = msum (1..n)
                  (\n. &1 / &(FACT n) %% (a %% screw_2_matrix s) matrix_pow n) - 
                  (&1 / &(FACT (SUC 0))) %% ((a %% screw_2_matrix s) matrix_pow 1)` SUBST1_TAC THENL
    [SIMP_TAC[FACT] THEN SIMP_TAC[MATRIX_POW_1;MATRIX_CMUL_LID;FACT;REAL_DIV_1;
             ARITH_RULE `SUC 0 = 1`;REAL_MUL_LID;GSYM REAL_OF_NUM_MUL];
    ALL_TAC] THEN
    MP_TAC (ISPECL [`(\n. &1 / &(FACT n) %% (a %% screw_2_matrix s)     
            matrix_pow n)`;`(1..n)`;`1`] (GSYM MSUM_DELETE)) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> SUC (n - 1) = n`;
                 FINITE_NUMSEG;IN_NUMSEG;LE_REFL;
                 ARITH_RULE `SUC 0 = 1`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MSUM_EQ_0 THEN
    SIMP_TAC[IN_NUMSEG;IN_DELETE;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= x /\ ~(x = 1) ==> 2 <= x`;
                 SCREW_POW_N_EQ_0;MATRIX_POW_CMUL;MATRIX_CMUL_RZERO]);;

let MATRIX_EXP_SCREW_COND_0_HOMO = prove
    (`!s:screw a:real. FST s = vec 0 ==> 
    matrix_exp(a %% screw_2_matrix s) = homo_trans (a % (SND s)) (mat 1)`,
    REPEAT STRIP_TAC THEN 
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) 
                    [GSYM HOMO_TRANS_EQ_MAT] THEN
    ASM_SIMP_TAC[homo_trans;CART_EQ;LAMBDA_BETA;MAT_COMPONENT;
                 MATRIX_CMUL_COMPONENT;VEC_COMPONENT;
                 VECTOR_NEG_COMPONENT;VECTOR_MUL_COMPONENT;
                 screw_2_matrix;MATRIX_ADD_COMPONENT;vec3_2_ssm;
                 DIMINDEX_3;DIMINDEX_1;DIMINDEX_FINITE_SUM;
                 ARITH_RULE `3 + 1 = 4`;VECTOR_3;FORALL_4;COND_ID] THEN 
    ARITH_TAC);;
    
let MATRIX_INV_HOMO_TRANS_I = prove    
    (`!x. matrix_inv(homo_trans x (mat 1)) = homo_trans (-- x) (mat 1)`,
    GEN_TAC THEN SIMP_TAC[INVERTIBLE_I;MATRIX_INV_HOMO_TRANS;MATRIX_INV_I;
             MATRIX_VECTOR_MUL_LNEG;MATRIX_VECTOR_MUL_LID]);;

let SCREW_EQ_HOMO_TRANS_DERIVATIVE = prove
    (`!s. screw_2_matrix s = 
      homo_trans_derivative (SND s) (vec3_2_ssm (FST s))`,
    SIMP_TAC[screw_2_matrix;homo_trans_derivative;CART_EQ;LAMBDA_BETA;
             DIMINDEX_3;DIMINDEX_1;DIMINDEX_FINITE_SUM;
             ARITH_RULE `3 + 1 = 4`] THEN ARITH_TAC);;
    
let SCREW_SIMILAR = prove
    (`!s. norm (FST s) = &1 ==> 
      matrix_inv(homo_trans ((FST s) cross (SND s)) (mat 1)) **
      screw_2_matrix s ** (homo_trans ((FST s) cross (SND s)) (mat 1)) 
      = screw_2_matrix (FST s, vec3_vtrans (FST s) ** (SND s))` ,
    GEN_TAC THEN STRIP_TAC THEN SIMP_TAC[MATRIX_INV_HOMO_TRANS_I;SCREW_EQ_HOMO_TRANS_DERIVATIVE;
             HOMO_TRANS_DERIVATIVE_LMUL;HOMO_TRANS_DERIVATIVE_RMUL;
             MATRIX_VECTOR_MUL_LID;MATRIX_MUL_LID;MATRIX_MUL_RID;
             CROSS_SSM;GSYM MATRIX_POW_2;MATRIX_VECTOR_MUL_ASSOC] THEN 
    ASM_SIMP_TAC[SSM_POW_2]THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
             VECTOR_SUB_ADD]);;

let SCREW_SIMILAR_ALT = prove
    (`!s s1. norm (FST s) = &1 /\ s1 = (FST s, vec3_vtrans (FST s) ** (SND s)) ==>
    homo_trans ((FST s) cross (SND s)) (mat 1) ** screw_2_matrix s1 ** 
    matrix_inv(homo_trans ((FST s) cross (SND s)) (mat 1)) = screw_2_matrix s`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_LMUL;HOMO_TRANS_DERIVATIVE_RMUL;
                 MATRIX_INV_HOMO_TRANS_I;SCREW_EQ_HOMO_TRANS_DERIVATIVE;CROSS_SSM;MATRIX_MUL_LID;
                 MATRIX_MUL_RID;
                 MATRIX_VECTOR_MUL_LID] THEN 
    SIMP_TAC[GSYM MATRIX_VECTOR_MUL_LNEG;MATRIX_VECTOR_MUL_ASSOC;
             MATRIX_MUL_RNEG;GSYM MATRIX_POW_2;
             GSYM MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN 
    ASM_SIMP_TAC[SSM_POW_2] THEN 
    SIMP_TAC[MATRIX_NEG_SUB;MATRIX_ADD_LNEG;MATRIX_SUB_ADD;
             MATRIX_VECTOR_MUL_LID]);;

let SCREW_SIMILAR_ALT_EXISTS = prove    
    (`!s. norm (FST s) = &1 ==> 
    ?s1. homo_trans ((FST s) cross (SND s)) (mat 1) ** screw_2_matrix s1 ** 
    matrix_inv(homo_trans ((FST s) cross (SND s)) (mat 1)) = screw_2_matrix s /\ 
    s1 = (FST s, vec3_vtrans (FST s) ** (SND s))`,
    REPEAT STRIP_TAC THEN 
    EXISTS_TAC ` (FST (s:screw), vec3_vtrans (FST s) ** (SND s))`THEN 
    MP_TAC (ISPECL[`s:screw`;`(FST (s:screw), vec3_vtrans (FST s) **    
            (SND s))`] SCREW_SIMILAR_ALT) THEN ASM_SIMP_TAC[]);;
    

let SCREW_SIMILAR_POW_N = prove
    (`!s s1:screw n. 2 <= n /\ norm (FST s) = &1 /\ 
      s1 = (FST s, vec3_vtrans (FST s) ** (SND s)) ==> 
      (screw_2_matrix s1) matrix_pow n = 
      homo_trans_derivative (vec 0) ((vec3_2_ssm (FST s) matrix_pow n))`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[SCREW_EQ_HOMO_TRANS_DERIVATIVE;
                 HOMO_TRANS_DERIVATIVE_POW;
                 ARITH_RULE `2 <= n ==> ~(n = 0)`;
                 ARITH_RULE `2 <= n ==> (n - 1) = (n - 2 + 1)`;
                 MATRIX_POW_ADD;MATRIX_POW_1] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_MUL_ASSOC;
             SSM_LMUL_EQ_0;MATRIX_MUL_RZERO;
             MATRIX_VECTOR_MUL_LZERO]);;

let INFMSUM_ADD_LEFT = prove
    (`!f:num->real^N^N n. (!m. msummable (from m) f) ==>
    infmsum (from n) f = f n + infmsum (from (SUC n)) f`,
    ONCE_REWRITE_TAC[GSYM MSUMMABLE_RESTRICT] THEN
    ONCE_REWRITE_TAC[GSYM INFMSUM_RESTRICT] THEN
    REWRITE_TAC[MATRIX_ARITH `!A B C:real^N^N. A = B + C <=>
                A - C = B`] THEN
    SIMP_TAC[GSYM INFMSUM_SUB] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\i. (if i IN from n then (f:num->real^N^N) i else
                  mat 0) - (if i IN from (SUC n) then f i else mat 0)) 
                  = (\i. (if i IN {n} then f i else mat 0))` 
                  SUBST1_TAC THENL
    [SIMP_TAC[FUN_EQ_THM] THEN SIMP_TAC[IN_ELIM_THM;from;IN_SING] THEN GEN_TAC THEN 
    COND_CASES_TAC THENL
    [FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [ARITH_RULE `n <= x  
    <=> SUC n <= x \/ (x = n)`]) THEN COND_CASES_TAC THENL
    [ASM_SIMP_TAC[ARITH_RULE `SUC n <= x ==> ~(x = n)`;MATRIX_SUB_REFL];
    ASM_SIMP_TAC[ARITH_RULE `(SUC n <= x \/ x = n) /\ ~(SUC n <= x) ==> x = n`;
    MATRIX_SUB_RZERO]]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n <= x) ==> ~(SUC n <= x)`;
                 ARITH_RULE `~((n:num) <= x) ==> 
                 ~(x = n)`;MATRIX_SUB_RZERO];ALL_TAC] THEN
    REWRITE_TAC[INFMSUM_RESTRICT] THEN
    MATCH_MP_TAC INFMSUM_UNIQUE THEN
    SIMP_TAC[msums;MATRIX_LIM_SEQUENTIALLY] THEN 
    REPEAT STRIP_TAC THEN EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[INTER;IN_NUMSEG;IN_SING;LE_0;
                 ARITH_RULE `(n:num) <= m ==> 
                 (x = n /\ x <= m <=> x = n)`;SET_RULE `{x | x = n} = {n}`;MSUM_SING;
                 MATRIX_DIST_REFL]);;

let MSUMMABLE_HOMO_TRANS_DERIVATIVE_VEC_POW = prove
    (`!R:real^N^N n:num. 1 <= n /\ fnorm(R) < &1 ==> 
    msummable (from n) (\n. homo_trans_derivative (vec 0:real^N) (R matrix_pow n))`,
    REWRITE_TAC[msummable] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC[GE] THEN 
    EXISTS_TAC `fnorm (R:real^N^N)` THEN
    EXISTS_TAC `1:num` THEN 
    STRIP_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`vec 0:real^N`;`R:real^N^N`] (GSYM 
                     HOMO_TRANS_DERIVATIVE_POW_GE_1)) THEN 
    ASM_SIMP_TAC[ARITH_RULE `(1 <= n) ==> (1 <= SUC n)`;
                MATRIX_VECTOR_MUL_RZERO] THEN  
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    SIMP_TAC[matrix_pow] THEN
    EXISTS_TAC `fnorm (homo_trans_derivative ((vec 0):real^N)   
                (R:real^N^N)) * fnorm (homo_trans_derivative ((vec 0):real^N) R matrix_pow n')` THEN
    SIMP_TAC[FNORM_SUBMULT] THEN 
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[FNORM_POS_LE] THEN
    MATCH_MP_TAC (REAL_ARITH `(x = y) ==> (x <= y)`) THEN
    SIMP_TAC[fnorm] THEN AP_TERM_TAC THEN
    SIMP_TAC[trace;matrix_mul;DIMINDEX_FINITE_SUM;DIMINDEX_1;
             SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`] THEN
    MATCH_MP_TAC (REAL_ARITH `x = a /\ y = &0 ==> x + y = a`) THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    CONJ_TAC THENL [SIMP_TAC[SUM_SING_NUMSEG;homo_trans_derivative;LAMBDA_BETA;LE_REFL;
              ARITH_RULE `1 <= n + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1;
              REAL_MUL_RZERO;REAL_ADD_RID] THEN 
    MATCH_MP_TAC SUM_EQ_0 THEN 
    SIMP_TAC[LAMBDA_BETA;TRANSP_COMPONENT;
             ARITH_RULE `i <= N ==> i <= N + 1`;
             DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;
             ARITH_RULE `1 <= N + 1`;IN_NUMSEG;VEC_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1;
                 ARITH_RULE `i <= N ==> i <= N + 1`] THEN 
                 MATCH_MP_TAC (REAL_ARITH `x = y /\ a = &0 ==>
                               x + a = y`) THEN 
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    CONJ_TAC THENL[SIMP_TAC[SUM_SING_NUMSEG] THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;TRANSP_COMPONENT;ARITH_RULE `i <= N ==> 
                 i <= N + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;
                 ARITH_RULE `1 <= N + 1`;VEC_COMPONENT;
                 homo_trans_derivative] THEN 
    ARITH_TAC;ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[LAMBDA_BETA;TRANSP_COMPONENT;
                 ARITH_RULE `i <= N ==> i <= N + 1`;DIMINDEX_FINITE_SUM;
                 DIMINDEX_1;LE_REFL;
                 ARITH_RULE `1 <= N + 1`;VEC_COMPONENT;
                 homo_trans_derivative;
                 ARITH_RULE `i <= N ==> ~(i = N + 1)`]);;

let MSUMMABLE_HOMO_TRANS_DERIVATIVE_VEC_POW_ALT = prove
    (`!R:real^N^N n:num. 1 <= n /\ fnorm(R) < &1 ==> 
    msummable (from n) (\n. homo_trans_derivative (vec 0:real^N) R matrix_pow n)`,
    SIMP_TAC[msummable] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC[GE] THEN
    EXISTS_TAC `fnorm (R:real^N^N)` THEN EXISTS_TAC `1:num` THEN 
    STRIP_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC[matrix_pow] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `fnorm (homo_trans_derivative ((vec 0):real^N)  
                (R:real^N^N)) * 
                fnorm (homo_trans_derivative ((vec 0):real^N) R matrix_pow n')` THEN
    SIMP_TAC[FNORM_SUBMULT] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[FNORM_POS_LE] THEN MATCH_MP_TAC (REAL_ARITH `(x = y) ==> (x <= y)`) THEN
    SIMP_TAC[fnorm] THEN AP_TERM_TAC THEN 
    SIMP_TAC[trace;matrix_mul;DIMINDEX_FINITE_SUM;DIMINDEX_1;
             SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`] THEN
    MATCH_MP_TAC (REAL_ARITH `x = a /\ y = &0 ==> x + y = a`) THEN REWRITE_TAC[CONJ_SYM] THEN
    CONJ_TAC THENL [SIMP_TAC[SUM_SING_NUMSEG;homo_trans_derivative;
                    LAMBDA_BETA;LE_REFL;ARITH_RULE `1 <= n + 1`;DIMINDEX_FINITE_SUM;
                    DIMINDEX_1;REAL_MUL_RZERO;REAL_ADD_RID] THEN 
    MATCH_MP_TAC SUM_EQ_0 THEN 
    SIMP_TAC[LAMBDA_BETA;TRANSP_COMPONENT;ARITH_RULE `i <= N ==> 
            i <= N + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;
            ARITH_RULE `1 <= N + 1`;IN_NUMSEG;VEC_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1;
                 ARITH_RULE `i <= N ==> i <= N + 1`] THEN 
    MATCH_MP_TAC (REAL_ARITH `x = y /\ a = &0 ==> x + a = y`) THEN 
    ONCE_REWRITE_TAC[CONJ_SYM] THEN CONJ_TAC THENL[SIMP_TAC[SUM_SING_NUMSEG] THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;TRANSP_COMPONENT;ARITH_RULE `i <= N 
                ==> i <= N + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1;
                LE_REFL;ARITH_RULE `1 <= N + 1`;VEC_COMPONENT;
                homo_trans_derivative] THEN ARITH_TAC;ALL_TAC] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[LAMBDA_BETA;TRANSP_COMPONENT;ARITH_RULE `i <= N ==>
                 i <= N + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;
                 ARITH_RULE `1 <= N + 1`;VEC_COMPONENT;
                 homo_trans_derivative;ARITH_RULE `i <= N ==>
                 ~(i = N + 1)`]);;
                 
let MSUMMABLE_MATRIX_SUB_CONDTION = prove
    (`!R:real^N^N n:num. fnorm(R) < &1 ==> msummable (from n) (\n. R matrix_pow n)`,
    SIMP_TAC[msummable] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC[GE] THEN
    EXISTS_TAC `fnorm (R:real^N^N)` THEN EXISTS_TAC `1:num` THEN
    ASM_SIMP_TAC[matrix_pow;FNORM_SUBMULT]);;
                 
let MATRIX_LIM_COMPONENT = prove
    (`!net f i j l:real^N^M.
     (f ->-> l) net ==> ((\a. lift_lift(f(a)$i$j)) ->-> lift_lift(l$i$j)) net`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[matrixtendsto; matrix_dist; GSYM LIFT2_SUB; FNORM_LIFT2] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[GSYM MATRIX_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    MESON_TAC[COMPONENT_LE_FNORM;REAL_LET_TRANS]);;                 
                 
let MSERIES_COMPONENT = prove
    (`!f s l:real^N^M i j. (f msums l) s /\ 1 <= i /\ i <= dimindex(:M) 
    /\ 1 <= j /\ j <= dimindex(:N) ==> ((\k. lift_lift(f(k)$i$j)) msums lift_lift(l$i$j)) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    ASM_SIMP_TAC[GSYM LIFT2_SUM; GSYM MSUM_COMPONENT;
                 FINITE_INTER; FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[o_DEF; MATRIX_LIM_COMPONENT]);;    

let MATRIXTENDSTO_REAL = prove
    (`(s ---> l) = ((lift_lift o s) ->-> lift_lift l)`,
    REWRITE_TAC[FUN_EQ_THM; matrixtendsto; tendsto_real; o_THM; MATRIX_DIST_LIFT2]);;  
  
let REAL_MSUMS = prove
    (`(f real_sums l) = ((lift_lift o f) msums (lift_lift l))`,
    REWRITE_TAC[FUN_EQ_THM; msums; real_sums; MATRIXTENDSTO_REAL] THEN
    SIMP_TAC[LIFT2_SUM; FINITE_INTER_NUMSEG; o_DEF]);;  
  
let INFMSUM_COMPONENT = prove    
    (`!f:num->real^N^M s i j. 
    msummable s f /\ 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ 
    j <= dimindex(:N) ==> (infmsum s f)$i$j = real_infsum s (\x. f(x)$i$j)`,
    SIMP_TAC[GSYM MSUMS_INFSUM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL[`f:num->real^N^M`;`s:num->bool`;`(infmsum s f):real^N^M`;`i:num`;`j:num`] MSERIES_COMPONENT) THEN ASM_SIMP_TAC[] THEN
    SIMP_TAC[GSYM REAL_MSUMS;GSYM o_DEF] THEN
    STRIP_TAC THEN MATCH_MP_TAC (GSYM REAL_INFSUM_UNIQUE) THEN ASM_SIMP_TAC[]);;

let HOMO_TRANS_DERIVATIVE_ADD_MAT = prove
    (`!x R. homo_trans_derivative x R + (mat 1 :real^(N,1)finite_sum^(N,1)finite_sum) = 
    homo_trans x (R + (mat 1 :real^N^N))`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[GSYM HOMO_TRANS_EQ_MAT;
    MATRIX_ARITH `! x y z:real^(N,1)finite_sum^(N,1)finite_sum. (x + y = z) <=> (x = z - y)`;
    HOMO_TRANS_SUB;VECTOR_SUB_RZERO;MATRIX_ARITH `!A B:real^N^M.(A + B) - B = A`;homo_trans_derivative;
    CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN ARITH_TAC);;

let HOMO_TRANS_SUB_MAT = prove
    (`!x R. homo_trans x R - (mat 1 :real^(N,1)finite_sum^(N,1)finite_sum) =
    homo_trans_derivative x (R - (mat 1 :real^N^N))`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[GSYM HOMO_TRANS_EQ_MAT;HOMO_TRANS_SUB;VECTOR_SUB_RZERO;
             homo_trans_derivative;CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN ARITH_TAC);;

let HOMO_TRANS_DERIVATIVE_INFMSUM_VEC = prove
    (`!R:real^N^N n:num. 1 <= n /\ fnorm(R) < &1 ==> 
       infmsum (from n) (\n. homo_trans_derivative (vec 0) (R matrix_pow n)) =
       homo_trans_derivative (vec 0) (infmsum (from n) (\n. R matrix_pow n))`,
    REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `infmsum (from n)
    (\n. homo_trans_derivative ((vec 0):real^N) ((R:real^N^N) matrix_pow n)) = 
    infmsum (from n) (\n. (homo_trans_derivative (vec 0) R) matrix_pow n)` SUBST1_TAC THENL 
    [MATCH_MP_TAC INFMSUM_EQ THEN
    ASM_SIMP_TAC[MSUMMABLE_HOMO_TRANS_DERIVATIVE_VEC_POW] THEN
    ASM_SIMP_TAC[MSUMMABLE_HOMO_TRANS_DERIVATIVE_VEC_POW_ALT] THEN
    SIMP_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`vec 0:real^N`;`R:real^N^N`;`x:num`] (GSYM 
            HOMO_TRANS_DERIVATIVE_POW_GE_1)) THEN
    ANTS_TAC THENL 
    [ASM_ARITH_TAC;ALL_TAC] THEN SIMP_TAC[MATRIX_VECTOR_MUL_RZERO];ALL_TAC] THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;INFMSUM_COMPONENT;MSUMMABLE_HOMO_TRANS_DERIVATIVE_VEC_POW_ALT;
    DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC[real_infsum] THEN 
    ONCE_SIMP_TAC[GSYM REAL_SERIES_RESTRICT] THEN 
    SIMP_TAC[IN_FROM] THEN 
    SUBGOAL_THEN `(\n'. if n <= n'
                    then ((homo_trans_derivative (vec 0:real^N) R) matrix_pow n')$i$i'
                    else &0) = (\n'. if n <= n'
                    then (homo_trans_derivative (vec 0) (R matrix_pow n'))$i$i'
                    else &0)` SUBST1_TAC THENL 
    [SIMP_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THENL [SIMP_TAC[] THEN 
    MP_TAC (ISPECL [`vec 0:real^N`;`R:real^N^N`;`x:num`] HOMO_TRANS_DERIVATIVE_POW_GE_1) THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO] THEN ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
             SIMP_TAC[];ALL_TAC] THEN SIMP_TAC[];ALL_TAC] THEN
    SIMP_TAC[GSYM IN_FROM;REAL_SERIES_RESTRICT] THEN
    SIMP_TAC[GSYM real_infsum] THEN 
    ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_COMPONENT;VEC_COMPONENT] THEN
    COND_CASES_TAC THENL [SIMP_TAC[REAL_INFSUM_0];ALL_TAC] THEN
    COND_CASES_TAC THENL [SIMP_TAC[REAL_INFSUM_0];ALL_TAC] THEN 
    SIMP_TAC[] THEN MATCH_MP_TAC (GSYM INFMSUM_COMPONENT) THEN 
    ASM_SIMP_TAC[ARITH_RULE `i <= N + 1 /\ ~(i = N + 1) ==> i <= N `] THEN
    SIMP_TAC[msummable] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC[GE] THEN
    EXISTS_TAC `fnorm (R:real^N^N)` THEN EXISTS_TAC `1:num` THEN
    ASM_SIMP_TAC[matrix_pow;FNORM_SUBMULT]);;

let HOMO_TRANS_DERIVATIVE_INFMSUM_VEC_CMUL = prove
    (`!R:real^N^N n:num c. 1 <= n /\ fnorm(R) < &1 ==> 
     infmsum (from n) (\n. homo_trans_derivative (vec 0) (c %% R matrix_pow n)) =
     homo_trans_derivative (vec 0) (infmsum (from n) (\n. c %% R matrix_pow n))`,
    REPEAT STRIP_TAC THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `(vec 0:real^N) = c % (vec 0)`] THEN
    ASM_SIMP_TAC[GSYM HOMO_TRANS_DERIVATIVE_CMUL;MSUMMABLE_HOMO_TRANS_DERIVATIVE_VEC_POW;
                 INFMSUM_CMUL;HOMO_TRANS_DERIVATIVE_INFMSUM_VEC] THEN
    ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_CMUL;MSUMMABLE_MATRIX_SUB_CONDTION;INFMSUM_CMUL]);;

let HOMO_TRANS_DERIVATIVE_INFMSUM_VEC_ALT = prove
    (`!R:num->real^N^N n:num. msummable (from n) (\n. R n) ==> 
    infmsum (from n) (\n. homo_trans_derivative (vec 0) (R n)) =
    homo_trans_derivative (vec 0) (infmsum (from n) (\n. R n))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN 
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[GSYM MSUMS_INFSUM;MSERIES_FROM;MATRIX_LIM_COMPONENTWISE_REAL;
             MSUM_COMPONENT;HOMO_TRANS_DERIVATIVE_COMPONENT;DIMINDEX_FINITE_SUM;
             DIMINDEX_1;VEC_COMPONENT] THEN 
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL 
    [SIMP_TAC[SUM_0;LIM_EQ_LIFT;o_DEF;LIFT_NUM;LIM_CONST];ALL_TAC] THEN 
    SIMP_TAC[] THEN COND_CASES_TAC THENL 
    [SIMP_TAC[SUM_0;LIM_EQ_LIFT;o_DEF;LIFT_NUM;LIM_CONST];ALL_TAC] THEN 
    SIMP_TAC[] THEN FIRST_X_ASSUM (MP_TAC o ISPECL [`i:num`;`j:num`]) THEN 
    ASM_SIMP_TAC[ARITH_RULE `(i <= N + 1) /\ ~(i = N + 1) ==> (i <= N)`]);;
   
let MATRIX_EXP_SCREW_SIMILAR = prove              
    (`!s s1:screw a:real. norm (FST s) = &1 /\ s1 = (FST s, vec3_vtrans (FST s) ** (SND s)) 
    ==> matrix_exp(a %% screw_2_matrix s1) = 
    homo_trans (a % (vec3_vtrans (FST s) ** (SND s))) (matrix_exp (a %% vec3_2_ssm (FST s)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_exp] THEN 
    MP_TAC (SIMP_RULE [MSUMMABLE_EXP] 
    (ISPEC `(\n. &1 / &(FACT n) %% (a %% screw_2_matrix s1) matrix_pow n)` INFMSUM_ADD_LEFT)) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SPEC `0`) THEN 
    FIRST_ASSUM(SUBST1_TAC o SPEC `SUC 0`) THEN
    SIMP_TAC[FACT;matrix_pow] THEN
    SIMP_TAC[GSYM (num_CONV `1`);GSYM (num_CONV`2`);
            MATRIX_MUL_RID;REAL_MUL_RID;GSYM REAL_OF_NUM_MUL;
            REAL_DIV_1;MATRIX_CMUL_LID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) 
    [SCREW_EQ_HOMO_TRANS_DERIVATIVE] THEN
    REWRITE_TAC[GSYM HOMO_TRANS_EQ_MAT;HOMO_TRANS_DERIVATIVE_CMUL] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM INFMSUM_RESTRICT] THEN
    SUBGOAL_THEN `(\n. if n IN from 2
                        then (\n. &1 / &(FACT n) %% (a %% screw_2_matrix s1) 
                        matrix_pow n) n
                        else mat 0) = (\n. if n IN from 2
                        then (\n. &1 / &(FACT n) %% (a pow n) %% 
                        homo_trans_derivative ((vec 0):real^3) ((vec3_2_ssm (FST (s:screw))) 
                        matrix_pow n)) n
                        else mat 0)` SUBST1_TAC THENL
    [SIMP_TAC[FUN_EQ_THM] THEN SIMP_TAC[IN_ELIM_THM;from] THEN 
    GEN_TAC THEN COND_CASES_TAC THENL 
    [ASM_SIMP_TAC[MATRIX_POW_CMUL;SCREW_SIMILAR_POW_N];ARITH_TAC];
    ALL_TAC] THEN REWRITE_TAC[INFMSUM_RESTRICT] THEN
    REWRITE_TAC[HOMO_TRANS_DERIVATIVE_CMUL;MATRIX_CMUL_ASSOC;
                VECTOR_MUL_RZERO] THEN
    SIMP_TAC[GSYM MATRIX_CMUL_ASSOC;GSYM MATRIX_POW_CMUL;
            MSUMMABLE_EXP;HOMO_TRANS_DERIVATIVE_INFMSUM_VEC_ALT] THEN 
    MP_TAC (ISPECL[`(\n. (&1 / &(FACT n) %% (a %% vec3_2_ssm 
            (FST (s:screw))) matrix_pow n)):num ->real^3^3`;`0:num`] INFMSUM_ADD_LEFT) THEN 
    SIMP_TAC[ARITH_RULE `SUC 0 =1`;matrix_pow;FACT;REAL_DIV_1;
            MATRIX_CMUL_1] THEN 
    STRIP_TAC THEN 
    ASM_SIMP_TAC[MSUMMABLE_EXP;MATRIX_ADD_SYM;
                GSYM HOMO_TRANS_DERIVATIVE_ADD_MAT;HOMO_TRANS_EQ_MAT;
                MATRIX_ARITH 
                `((mat 1:real^(3,1)finite_sum^(3,1)finite_sum) + A + B = C + mat 1) <=> A +B = C`] THEN
    MP_TAC (ISPECL[`(\n. (&1 / &(FACT n) %% (a %% vec3_2_ssm 
            (FST (s:screw))) matrix_pow n)):num ->real^3^3`;`1:num`] INFMSUM_ADD_LEFT) THEN 
    SIMP_TAC[ARITH_RULE `SUC 1 = 2`;MATRIX_POW_1;ARITH_RULE `FACT 1 =      
            1`;MATRIX_CMUL_1;REAL_DIV_1] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MSUMMABLE_EXP] THEN 
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_ADD_RID] THEN
    SIMP_TAC[HOMO_TRANS_DERIVATIVE_ADD;VECTOR_ADD_RID]);;

let MATRIX_EXP_SCREW_COND_1 = prove    
    ( `!s:screw a:real. norm (FST s) = &1 ==> 
        matrix_exp(a %% screw_2_matrix s) = 
        homo_trans ((mat 1 - matrix_exp (a %% vec3_2_ssm (FST s))) ** ((FST s) cross (SND s)) + 
        a % (vec3_vtrans (FST s) ** (SND s))) (matrix_exp (a %% vec3_2_ssm (FST s)))`,
    let lem = MESON [MATRIX_MUL_RCANCEL;SWAP_FORALL_THM] 
    `!C A B:real^N^N. invertible C ==> (A ** C = B ** C <=> A = B)` in
    REPEAT STRIP_TAC THEN MP_TAC (ISPEC `s:screw` SCREW_SIMILAR_ALT_EXISTS) THEN 
    ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s1:screw` MP_TAC) THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN 
    SIMP_TAC[] THEN STRIP_TAC THEN 
    MP_TAC (ISPECL [`(FST (s:screw) cross SND s)`; `(mat 1):real^3^3`]  
            INVERTIBLE_HOMO_TRANS) THEN
    SIMP_TAC[INVERTIBLE_I] THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIX_MUL_RMUL] THEN 
    ONCE_REWRITE_TAC[GSYM MATRIX_MUL_LMUL] THEN 
    MP_TAC (GSYM (ISPECL [`a %% screw_2_matrix (s1:screw)`;
    `matrix_inv (homo_trans (FST (s:screw) cross SND s) (mat 1))`] MATRIX_EXP_ID_EQ)) THEN 
    SIMP_TAC[INVERTIBLE_HOMO_TRANS;INVERTIBLE_I;INVERTIBLE_MATRIX_INV;
             MATRIX_INV_INV] THEN 
    STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_EXP_SCREW_SIMILAR] THEN 
    ONCE_ASM_SIMP_TAC[GSYM (ISPEC `(homo_trans (FST (s:screw) cross 
                      SND s) (mat 1))` lem)] THEN
    ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC;MATRIX_INV;
                 MATRIX_MUL_RID;HOMO_TRANS_MUL_TRANS] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
             MATRIX_MUL_LID;MATRIX_MUL_RID] THEN 
    SIMP_TAC[VECTOR_ARITH `((A:real^3) - B + C) + B = A + C`]);;


let DOT_SSM_RMUL = prove
    (`!w a. w dot (vec3_2_ssm w) ** a = &0`,
    REPEAT GEN_TAC THEN SIMP_TAC[GSYM CROSS_SSM;DOT_CROSS_SELF]);;

let DOT_SSM_LMUL = prove
    (`!w a. ((vec3_2_ssm w) ** a) dot w = &0`,
    REPEAT GEN_TAC THEN SIMP_TAC[GSYM CROSS_SSM;DOT_CROSS_SELF]);;

let DOT_SSM_LMUL_SELF = prove
    (`!w a. ((vec3_2_ssm w) ** a) dot a = &0`,
     REPEAT GEN_TAC THEN SIMP_TAC[GSYM CROSS_SSM;DOT_CROSS_SELF]);;

let DOT_SSM_RMUL_SELF = prove
    (`!w a. a dot (vec3_2_ssm w) ** a = &0`,
    REPEAT GEN_TAC THEN SIMP_TAC[GSYM CROSS_SSM;DOT_CROSS_SELF]);;

let SSM_LMUL_EQ_0 = prove
    (`!a:real^3. vec3_2_ssm a ** vec3_vtrans a = mat 0`,
    SIMP_TAC [vec3_2_ssm;vec3_vtrans] THEN MAT3_TAC);;
                
let SSM_RMUL_EQ_0 = prove
    (`!a:real^3. vec3_vtrans a ** vec3_2_ssm a = mat 0`,
    SIMP_TAC [vec3_2_ssm;vec3_vtrans] THEN MAT3_TAC);;

let TRANSP_SSM_RMUL_EQ_0 = prove
    (`!a:real^3. transp(vec3_vtrans a) ** vec3_2_ssm a = mat 0`,
    SIMP_TAC [vec3_2_ssm;vec3_vtrans] THEN MAT3_TAC);;

let TRANSP_EQ_NEG_SSM = prove
    (`!a:real^3. transp (vec3_2_ssm a) = -- (vec3_2_ssm a)` ,
    STRIP_TAC THEN
    SIMP_TAC[transp;vec3_2_ssm;CART_EQ; LAMBDA_BETA;DIMINDEX_3;matrix_neg;
             VECTOR_NEG_COMPONENT;FORALL_3;VECTOR_3;REAL_NEG_NEG;REAL_NEG_0]);;

let TRANSP_EQ_VEC3 = prove
    (`!w:real^3. transp (vec3_vtrans w) = vec3_vtrans w` ,
     STRIP_TAC THEN SIMP_TAC[transp;vec3_vtrans;CART_EQ; LAMBDA_BETA;DIMINDEX_3;
                             FORALL_3;VECTOR_3;REAL_MUL_SYM]);;


let TRANSP_VEC3_RMUL_SELF = prove
    (`!a:real^3. (norm a = &1) ==> transp(vec3_vtrans a) ** vec3_vtrans a = vec3_vtrans a`,
    GEN_TAC THEN 
    SIMP_TAC[vec3_vtrans;CART_EQ;LAMBDA_BETA;matrix_mul;DIMINDEX_3;SUM_3;
             TRANSP_COMPONENT;VECTOR_3;FORALL_3;GSYM REAL_MUL_ASSOC] THEN 
    SIMP_TAC[REAL_ARITH `a * b * c * d = (a * c) * b * d`] THEN 
    SIMP_TAC[GSYM REAL_ADD_LDISTRIB;VEC3_NORM_EQ_1;REAL_MUL_RID] THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC] THEN SIMP_TAC[REAL_ARITH `a * b * c * d = (a * d) * b * c`] THEN 
    SIMP_TAC[GSYM REAL_ADD_LDISTRIB;REAL_MUL_RID] THEN 
    SIMP_TAC[GSYM REAL_ADD_RDISTRIB;REAL_MUL_LID] THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC] THEN SIMP_TAC[REAL_ARITH `a * b * c * d =  (a * c) * b * d`] THEN 
    SIMP_TAC[GSYM REAL_ADD_RDISTRIB;REAL_MUL_LID] THEN SIMP_TAC[REAL_MUL_SYM]);;

let DOT_EQ_MP_VTRANS = prove
    (`! w u v:real^3. w dot u = w dot v ==> vec3_vtrans w ** v = vec3_vtrans w ** u`,
    SIMP_TAC[vec3_vtrans;dot;CART_EQ;LAMBDA_BETA;
             MATRIX_VECTOR_MUL_COMPONENT;DIMINDEX_3;FORALL_3;SUM_3;
             VECTOR_3] THEN
    SIMP_TAC[GSYM REAL_MUL_ASSOC] THEN
    MESON_TAC[REAL_ADD_LDISTRIB;REAL_MUL_AC]);;    

let PADEN_KAHAN_SUB_PRO_1 = prove
    (`!w r u u' v v' p q:real^3 s:screw a:real.
    (--(pi / &2) < a /\ a < pi / &2) /\ s = (w, r cross w) /\
    norm w = &1 /\
    u = p - r /\ v = q - r /\
    u' = u - (vec3_vtrans (FST s) ** u) /\
    v' = v - (vec3_vtrans (FST s) ** v) /\
    matrix_exp(a %% screw_2_matrix s) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a %% screw_2_matrix s) ** (homo_point (mk_point p)) = (homo_point (mk_point q)) /\
    ~(u' = vec 0) ==>
    a = atn ((w dot (u' cross v')) / (u' dot v'))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** vec3_vtrans w =
                  vec3_vtrans w` ASSUME_TAC THENL 
    [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) 
    [MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w = 
    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2] THEN 
    SIMP_TAC[MATRIX_ADD_RDISTRIB;MATRIX_POW_2;SSM_LMUL_EQ_0;GSYM
            MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RZERO;
            MATRIX_ADD_LID];ALL_TAC] THEN 
    SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u:real^3)
                    = v` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a:real) %% screw_2_matrix s) ** 
                   homo_point (mk_point (p:real^3)) = 
                   homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a %% screw_2_matrix s) ** homo_point 
                  (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y = z`;
    VECTOR_ARITH `(a:real^3 = b + a - c) <=> (vec 0 = b - c)`] ;ALL_TAC] THEN
    SUBGOAL_THEN `vec3_vtrans (w:real^3) ** (v:real^3) = vec3_vtrans w ** (u:real^3)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[VECTOR_ARITH
    `!A:real^3^3 b c:real^3. (A ** b= A ** c) <=> ((A:real^3^3)** (b:real^3)- A ** c= vec 0)`;
    GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w:real^3) = &1` THEN SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB;
    RODRIGUES_FORMULA_ALT] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;
    MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB;MATRIX_VECTOR_MUL_SUB_LDISTRIB;MATRIX_VECTOR_MUL_RMUL;
    MATRIX_VECTOR_MUL_ASSOC;
                    SSM_RMUL_EQ_0;MATRIX_VECTOR_MUL_LZERO;VECTOR_MUL_RZERO;VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[VECTOR_ARITH `!x y z. (x+y-x)-y=vec 0`];ALL_TAC] THEN 
    SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u':real^3)
                  = v'` ASSUME_TAC THENL
    [UNDISCH_TAC `(u':real^3) = (u:real^3) - vec3_vtrans (FST (s:screw)) ** u` THEN 
    UNDISCH_TAC `(v':real^3) = (v:real^3) - vec3_vtrans (FST (s:screw)) ** v` THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp ((a:real) %% screw_2_matrix s) ** 
                 homo_point (mk_point (p:real^3)) = 
                 homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r`  THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a %% screw_2_matrix s) ** homo_point 
                (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
             MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = 
                     (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y =
            z`;VECTOR_ARITH `(a:real^3 = b + a - c) 
            <=> (vec 0 = b - c)`] THEN 
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MESON [MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_MUL_LID] `(a:real^3) - (B:real^3^3) ** a = (mat 1 - B) ** a`] THEN
    ONCE_REWRITE_TAC[MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w =
                    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2;RODRIGUES_FORMULA] THEN
    SIMP_TAC[MATRIX_ARITH `mat 1 - (mat 1 + (A:real^3^3) + (B:real^3^3))   
            = --(A + B)`;MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_LNEG;
            MATRIX_ADD_LDISTRIB;MATRIX_ADD_RDISTRIB;MATRIX_MUL_RID] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LMUL;GSYM MATRIX_POW_ADD] THEN
    SIMP_TAC[MESON [MATRIX_POW_ADD;MATRIX_POW_1;
            ARITH_RULE `1 + 2 = 0 + 3`] `!A:real^N^N. A ** A matrix_pow 2 = A matrix_pow (0 + 3)`] THEN
    ASM_SIMP_TAC[SSM_POW_CYCLICITY;ARITH_RULE `2 + 2 = 1 + 3`] THEN
    SIMP_TAC[ARITH;MATRIX_POW_1;MATRIX_CMUL_RNEG;GSYM MATRIX_NEG_ADD;
            MATRIX_ADD_LNEG;MATRIX_ADD_RID;MATRIX_ARITH `-- ((mat 0):real^3^3) = mat 0`;
            MATRIX_VECTOR_MUL_LZERO];ALL_TAC] THEN
    SUBGOAL_THEN `norm(u':real^3) = norm(v':real^3) `ASSUME_TAC THENL
    [SIMP_TAC[NORM_EQ;ARITH_RULE ` ((x:real^3) dot x= y dot y) <=> (x dot x - y dot y= &0)`] THEN 
    POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC] THEN STRIP_TAC THEN 
    SIMP_TAC[TRANSP_TRANS_EXP] THEN  
    SUBGOAL_THEN `(a %% transp (vec3_2_ssm w)) ** (a %% (vec3_2_ssm (w:real^3))) = 
    (a %% (vec3_2_ssm w))** (a %% transp (vec3_2_ssm w))` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL 
    [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
    ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;
    MATRIX_MUL_RNEG];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
    SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `!A:real^3^3. -- A + A = mat 0`;
                   MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID;REAL_SUB_REFL];ALL_TAC] THEN
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** u' = 
                vec 0` ASSUME_TAC THENL 
    [UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN    
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
    SIMP_TAC[VECTOR_SUB_EQ];ALL_TAC] THEN 
    UNDISCH_TAC `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u':real^3) 
                = v'` THEN
    UNDISCH_TAC `norm (w:real^3) = &1` THEN 
    SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN STRIP_TAC THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_LMUL] THEN 
    UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** u' = vec 0` THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_LID;VECTOR_MUL_RZERO;VECTOR_ADD_RID] THEN
    REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `(u':real^3) dot (v':real^3) = 
                  norm u' * norm v' * (cos a)` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[DOT_SYM] THEN 
    MP_TAC (ISPECL[`(cos a) % (u':real^3)+ sin a % (((vec3_2_ssm:real^3->real^3^3) w) ** u')`;
    `v':real^3`;`u':real^3`] 
    (MESON [] `! x y z:real^N. x = y ==> x dot z = y dot z`)) THEN 
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN 
    SIMP_TAC[DOT_LADD;GSYM CROSS_SSM;DOT_CROSS_SELF;DOT_LMUL;GSYM
            NORM_POW_2;REAL_MUL_RZERO;REAL_ADD_RID] THEN 
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN 
    ASM_MESON_TAC[REAL_POW_2;REAL_MUL_AC];ALL_TAC] THEN 
    SUBGOAL_THEN `(u':real^3) cross (v':real^3) = 
            (norm u' * norm v' * (sin a)) % (w:real^3)` ASSUME_TAC THENL
    [MP_TAC (ISPECL[`(cos a) % (u':real^3)+ sin a % (((vec3_2_ssm:real^3->real^3^3) w) ** u')`;
    `v':real^3`;`u':real^3`] (MESON [] `! x y z:real^3. x = y ==> z cross x = z cross y`)) THEN 
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN 
    SIMP_TAC[CROSS_RADD;CROSS_RMUL;CROSS_REFL;VECTOR_MUL_RZERO;
            VECTOR_ADD_LID] THEN STRIP_TAC THEN 
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN 
    UNDISCH_TAC `norm (u':real^3) = norm (v':real^3)` THEN
    DISCH_THEN (MP_TAC o SYM) THEN
    SIMP_TAC[REAL_MUL_ASSOC;GSYM REAL_POW_2;NORM_POW_2;GSYM 
            CROSS_SSM] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC (MESON [] `!x y:real^N. x = b % y ==> c % x = c % b % y`) THEN
    SIMP_TAC[cross;dot;CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;
            SUM_3;VECTOR_3;VECTOR_MUL_COMPONENT] THEN 
    SUBGOAL_THEN `(w:real^3) dot (u':real^3) = &0` ASSUME_TAC THENL
    [UNDISCH_TAC `(u':real^3) = (u:real^3) - vec3_vtrans (FST (s:screw))   
                  ** u` THEN 
    UNDISCH_TAC `(s:screw) = (w:real^3),r cross w` THEN 
    SIMP_TAC[DOT_RSUB;FST] THEN REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `norm (w:real^3) = &1` THEN
    SIMP_TAC[NORM_EQ_1;dot;vec3_vtrans;CART_EQ;LAMBDA_BETA;DIMINDEX_3;
            FORALL_3;SUM_3;VECTOR_3;matrix_vector_mul;GSYM REAL_MUL_ASSOC] THEN 
    REWRITE_TAC[REAL_ARITH `a + b + c = &1 <=> a = &1 - (b + c)`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_SUB_LDISTRIB;
                REAL_SUB_RDISTRIB;GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_ASSOC] THEN ARITH_TAC;ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[dot;SUM_3;DIMINDEX_3] THEN
    REWRITE_TAC[REAL_ARITH `a + b + c = &0 <=> b = --(a + c)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_SUB_LDISTRIB;
                REAL_SUB_RDISTRIB;GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[] THEN SIMP_TAC[REAL_MUL_ASSOC] THEN ARITH_TAC;
    ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[DOT_RMUL] THEN
    UNDISCH_TAC`norm (w:real^3) = &1` THEN
    SIMP_TAC[NORM_EQ_1;REAL_MUL_RID] THEN 
    REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `norm (u':real^3) = norm (v':real^3)` THEN
    UNDISCH_TAC `~((u':real^3) = vec 0)` THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN 
    ASM_SIMP_TAC[REAL_FIELD `! a b c:real. (&0 < a) ==> 
                ((a * b) / (a * c) = (b / c))`;GSYM NORM_POS_LT;GSYM tan;TAN_ATN]);;

(*
let PADEN_KAHAN_SUB_PRO_1 = prove
    (`!w r u u' v v' p q:real^3 s:screw a:real.
    (--(pi / &2) < a /\ a < pi / &2) /\ s = (w, r cross w) /\
    norm w = &1 /\
    u = p - r /\ v = q - r /\
    u' = u - (vec3_vtrans (FST s) ** u) /\
    v' = v - (vec3_vtrans (FST s) ** v) /\
    w dot u = w dot v /\ norm(u') = norm(v') /\ 
    matrix_exp(a %% screw_2_matrix s) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a %% screw_2_matrix s) ** (homo_point (mk_point p)) = (homo_point (mk_point q)) /\ ~(u' = vec 0) ==>
    a = atn ((w dot (u' cross v')) / (u' dot v'))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u':real^3)
                  = v'` ASSUME_TAC THENL
    [UNDISCH_TAC `(u':real^3) = (u:real^3) - vec3_vtrans (FST (s:screw)) ** u` THEN 
    UNDISCH_TAC `(v':real^3) = (v:real^3) - vec3_vtrans (FST (s:screw)) ** v` THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp ((a:real) %% screw_2_matrix s) ** 
                 homo_point (mk_point (p:real^3)) = 
                 homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r`  THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a %% screw_2_matrix s) ** homo_point 
                (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
             MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = 
                     (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y =
            z`;VECTOR_ARITH `(a:real^3 = b + a - c) 
            <=> (vec 0 = b - c)`] THEN 
    REPEAT STRIP_TAC THEN 
    ASM_SIMP_TAC[DOT_EQ_MP_VTRANS;MESON [MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_MUL_LID] `(a:real^3) - (B:real^3^3) ** a = (mat 1 - B) ** a`] THEN
    ONCE_REWRITE_TAC[MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w =
                    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2;RODRIGUES_FORMULA] THEN
    SIMP_TAC[MATRIX_ARITH `mat 1 - (mat 1 + (A:real^3^3) + (B:real^3^3))   
            = --(A + B)`;MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_LNEG;
            MATRIX_ADD_LDISTRIB;MATRIX_ADD_RDISTRIB;MATRIX_MUL_RID] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LMUL;GSYM MATRIX_POW_ADD] THEN
    SIMP_TAC[MESON [MATRIX_POW_ADD;MATRIX_POW_1;
            ARITH_RULE `1 + 2 = 0 + 3`] `!A:real^N^N. A ** A matrix_pow 2 = A matrix_pow (0 + 3)`] THEN
    ASM_SIMP_TAC[SSM_POW_CYCLICITY;ARITH_RULE `2 + 2 = 1 + 3`] THEN
    SIMP_TAC[ARITH;MATRIX_POW_1;MATRIX_CMUL_RNEG;GSYM MATRIX_NEG_ADD;
            MATRIX_ADD_LNEG;MATRIX_ADD_RID;MATRIX_ARITH `-- ((mat 0):real^3^3) = mat 0`;MATRIX_VECTOR_MUL_LZERO];ALL_TAC] THEN
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** u' = 
                vec 0` ASSUME_TAC THENL 
    [UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN 
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** vec3_vtrans w =
                  vec3_vtrans w` ASSUME_TAC THENL 
    [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) 
    [MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w = 
    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2] THEN 
    SIMP_TAC[MATRIX_ADD_RDISTRIB;MATRIX_POW_2;SSM_LMUL_EQ_0;GSYM
            MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RZERO;
            MATRIX_ADD_LID];ALL_TAC] THEN 
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
    SIMP_TAC[VECTOR_SUB_EQ];ALL_TAC] THEN 
    UNDISCH_TAC `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u':real^3) 
                = v'` THEN
    UNDISCH_TAC `norm (w:real^3) = &1` THEN 
    SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN STRIP_TAC THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_LMUL] THEN 
    UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** u' = vec 0` THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_LID;VECTOR_MUL_RZERO;VECTOR_ADD_RID] THEN
    REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `(u':real^3) dot (v':real^3) = 
                  norm u' * norm v' * (cos a)` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[DOT_SYM] THEN 
    MP_TAC (ISPECL[`(cos a) % (u':real^3)+ sin a % (((vec3_2_ssm:real^3->real^3^3) w) ** u')`;
    `v':real^3`;`u':real^3`] (MESON [] `! x y z:real^N. x = y ==> x dot z = y dot z`)) THEN 
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN 
    SIMP_TAC[DOT_LADD;GSYM CROSS_SSM;DOT_CROSS_SELF;DOT_LMUL;GSYM
            NORM_POW_2;REAL_MUL_RZERO;REAL_ADD_RID] THEN 
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN 
    ASM_MESON_TAC[REAL_POW_2;REAL_MUL_AC];ALL_TAC] THEN 
    SUBGOAL_THEN `(u':real^3) cross (v':real^3) = 
            (norm u' * norm v' * (sin a)) % (w:real^3)` ASSUME_TAC THENL
    [MP_TAC (ISPECL[`(cos a) % (u':real^3)+ sin a % (((vec3_2_ssm:real^3->real^3^3) w) ** u')`;	
    `v':real^3`;`u':real^3`](MESON [] `! x y z:real^3. x = y ==> z cross x = z cross y`)) THEN 
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN 
    SIMP_TAC[CROSS_RADD;CROSS_RMUL;CROSS_REFL;VECTOR_MUL_RZERO;
            VECTOR_ADD_LID] THEN STRIP_TAC THEN 
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN 
    UNDISCH_TAC `norm (u':real^3) = norm (v':real^3)` THEN
    DISCH_THEN (MP_TAC o SYM) THEN
    SIMP_TAC[REAL_MUL_ASSOC;GSYM REAL_POW_2;NORM_POW_2;GSYM 
            CROSS_SSM] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC (MESON [] `!x y:real^N. x = b % y ==> c % x = c % b % y`) THEN
    SIMP_TAC[cross;dot;CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;
            SUM_3;VECTOR_3;VECTOR_MUL_COMPONENT] THEN 
    SUBGOAL_THEN `(w:real^3) dot (u':real^3) = &0` ASSUME_TAC THENL
    [UNDISCH_TAC `(u':real^3) = (u:real^3) - vec3_vtrans (FST (s:screw))   
                  ** u` THEN 
    UNDISCH_TAC `(s:screw) = (w:real^3),r cross w` THEN 
    SIMP_TAC[DOT_RSUB;FST] THEN REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `norm (w:real^3) = &1` THEN
    SIMP_TAC[NORM_EQ_1;dot;vec3_vtrans;CART_EQ;LAMBDA_BETA;DIMINDEX_3;
            FORALL_3;SUM_3;VECTOR_3;matrix_vector_mul;GSYM REAL_MUL_ASSOC] THEN 
    REWRITE_TAC[REAL_ARITH `a + b + c = &1 <=> a = &1 - (b + c)`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_SUB_LDISTRIB;
                REAL_SUB_RDISTRIB;GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_ASSOC] THEN ARITH_TAC;ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[dot;SUM_3;DIMINDEX_3] THEN
    REWRITE_TAC[REAL_ARITH `a + b + c = &0 <=> b = --(a + c)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_SUB_LDISTRIB;
                REAL_SUB_RDISTRIB;GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[] THEN SIMP_TAC[REAL_MUL_ASSOC] THEN ARITH_TAC;
    ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[DOT_RMUL] THEN
    UNDISCH_TAC`norm (w:real^3) = &1` THEN
    SIMP_TAC[NORM_EQ_1;REAL_MUL_RID] THEN 
    REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `norm (u':real^3) = norm (v':real^3)` THEN
    UNDISCH_TAC `~((u':real^3) = vec 0)` THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN 
    ASM_SIMP_TAC[REAL_FIELD `! a b c:real. (&0 < a) ==> 
                ((a * b) / (a * c) = (b / c))`;GSYM NORM_POS_LT;GSYM tan;TAN_ATN]);;
*)
                
let gst_initial = new_definition 
    `gst_initial x = homo_trans (x:real^3) (mat 1)`;;

let INVERTIBLE_GST_INITIAL = prove
    (`!x:real^3. invertible (gst_initial x)`, 
    SIMP_TAC[gst_initial;INVERTIBLE_I;INVERTIBLE_HOMO_TRANS]);;

let gst = new_definition
    `gst a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6 x = matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp((a2:real) %% screw_2_matrix s2) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4) ** matrix_exp((a5:real) %% screw_2_matrix s5) ** matrix_exp((a6:real) %% screw_2_matrix s6) ** (gst_initial x)`;;               
                
let gst1 = new_definition                
    `gst1 a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6 = matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp((a2:real) %% screw_2_matrix s2) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4) ** matrix_exp((a5:real) %% screw_2_matrix s5) ** matrix_exp((a6:real) %% screw_2_matrix s6)`;;                
                
let GST1 = prove
    (`!a1 a2 a3 a4 a5 a6:real s1 s2 s3 s4 s5 s6:screw x:real^3.
    (gst a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6 x) ** (matrix_inv (gst_initial x)) = (gst1 a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[gst;gst1;GSYM MATRIX_MUL_ASSOC;INVERTIBLE_GST_INITIAL;
            MATRIX_INV;MATRIX_MUL_RID]);;

let gst2 = new_definition                
    `gst2 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6 = matrix_exp((a2:real) %% screw_2_matrix s2) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4) ** matrix_exp((a5:real) %% screw_2_matrix s5) ** matrix_exp((a6:real) %% screw_2_matrix s6)`;;      


let gst3 = new_definition                
    `gst3 a2 s2 a3 s3 a4 s4  = matrix_exp((a2:real) %% screw_2_matrix s2) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4)`;;
  
let P2_SOLUTION = prove  
    (`!o1 w1 w2 p1 p56 p2:real^3 px py pz d4 c2 c3:real.
    (p2 - p56) dot w2 = &0 /\ 
    (p2 - o1) dot w1 = &0 /\ 
    norm(p2 - o1) = norm(p1 - o1) /\ 
    p1 = (vector[px;py;pz]:real^3) /\ 
    w1 = (vector[&0;&0;&1]:real^3) /\
    w2 = (vector[&1;&0;&0]:real^3) /\ 
    o1 = (vector[&0;&0;pz]:real^3) /\ 
    p56 = (vector[d4;&0;c2+c3+d4]:real^3) ==> 
    (p2$1 = d4 /\ p2$3 = pz /\ p2$2 pow 2 = (px pow 2 + py pow 2 - d4 pow 2) )`, 
    REPEAT GEN_TAC THEN INTRO_TAC "A" THEN 
    SUBGOAL_THEN `(p2:real^3)$1 = d4 /\ p2$3 = pz` ASSUME_TAC THENL
    [POP_ASSUM MP_TAC THEN REPEAT STRIP_TAC THENL
    [UNDISCH_TAC `(p2:real^3 - p56:real^3) dot w2:real^3 = &0` THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;DOT_3;
                VECTOR_3;VECTOR_SUB_COMPONENT;REAL_MUL_RID;
                REAL_MUL_RZERO] THEN 
    ARITH_TAC;ALL_TAC] THEN 
    UNDISCH_TAC `((p2:real^3) - (o1:real^3)) dot (w1:real^3) = &0` THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;DOT_3;VECTOR_3;
                VECTOR_SUB_COMPONENT;REAL_MUL_RID;REAL_MUL_RZERO] THEN 
    ARITH_TAC;ALL_TAC] THEN  ASM_SIMP_TAC[] THEN
    REMOVE_THEN "A" MP_TAC THEN REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `norm((p2:real^3) - (o1:real^3)) =       
                 norm((p1:real^3) - o1)` THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
                NORM_EQ;DOT_3;VECTOR_SUB_COMPONENT;REAL_SUB_REFL;
                REAL_SUB_RZERO;GSYM REAL_POW_2] THEN ARITH_TAC);;

let VEC_0 = prove
    (`(vector [&0; &0; &0]:real^3) = vec 0`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             VEC_COMPONENT]);;
                
let VECTOR_SUB = prove
    (`!x1 x2 y1 y2 z1 z2:real. 
    ((vector[x1; y1; z1]:real^3) - (vector[x2; y2; z2]:real^3)) = (vector[x1 - x2; y1 - y2;z1 - z2]:real^3)`,               
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             VECTOR_SUB_COMPONENT]);;               
                
let VECTOR_MUL = prove
    (`!x1 x2 x3 y1 y2 y3 z1 z2 z3 a b c. 
    (vector [vector [x1; y1; z1]; vector [x2; y2; z2];vector [x3; y3; z3]]:real^3^3) ** (vector [a; b; c]:real^3) = (vector [x1 * a + y1 * b + z1 * c; x2 * a + y2 * b + z2 * c;x3 * a + y3 * b + z3 * c]:real^3)`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             MATRIX_VECTOR_MUL_COMPONENT;DOT_3;SUM_3]);;
                
let VECTOR_ADD_LNEG = prove                
    (`!x1 x2 y1 y2 z1 z2.
    (--(vector [x1; y1; z1]:real^3) + (vector [x2; y2; z2]:real^3)) = 
    (vector [x2 - x1; y2 - y1; z2 - z1]:real^3)`,          
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;
            VECTOR_3;VECTOR_NEG_COMPONENT;VECTOR_ADD_COMPONENT] THEN
    ARITH_TAC);;            
                
let A1_SOLUTION = prove
    (`!p1 p2 w1 r1 o1:real^3 px py pz b1 d4 a1:real s1:screw.
    (p1 = (vector[px;py;pz]:real^3) /\ 
    p2 = (vector[d4;b1;pz]:real^3) /\
    w1 = (vector[&0;&0;&1]:real^3) /\  
    (--(pi / &2) < a1 /\ a1 < pi / &2) /\ s1 = (w1, vec 0) /\
    o1 = (vector[&0;&0;pz]:real^3) /\ norm(p2 - o1) = norm(p1 - o1) /\
    ~ (d4 = &0) /\
    matrix_exp((a1) %% screw_2_matrix s1) ** (homo_point (mk_point p2)) = (homo_point (mk_point p1))) ==>
    a1 = atn ((--((px) * (b1)) + (d4) * (py)) / ((d4) * (px) + (py) *   (b1)))`,
    REPEAT STRIP_TAC THEN 
    MP_TAC (ISPECL[`w1:real^3`;`(vec 0):real^3`;`p2:real^3`;
                    `vector[d4; b1; &0]:real^3`;`p1:real^3`;
                    `vector [px; py; &0]:real^3`;`p2:real^3`;
                    `p1:real^3`;`s1:screw`;`a1:real`]
            PADEN_KAHAN_SUB_PRO_1) THEN
    SUBGOAL_THEN `!x y z:real. vec3_vtrans (vector [&0; &0; &1]) **     
                 vector [x; y; z] = vector [&0; &0; z]` ASSUME_TAC THENL            
    [ASM_SIMP_TAC[vec3_vtrans;CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;
                 VECTOR_3;MATRIX_VECTOR_MUL_COMPONENT;dot;
                 REAL_MUL_LZERO;SUM_3] THEN 
    ARITH_TAC;ALL_TAC] THEN 
    ASM_SIMP_TAC[VECTOR_SUB_RZERO;CROSS_LZERO;vector_norm;SQRT_EQ_1;
                VECTOR_3] THEN
    SUBGOAL_THEN `!x y z:real. ((vector[x; y; z]:real^3) - 
                 (vector[&0; &0; z]:real^3)) = (vector[x; y; &0]:real^3)` ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             VECTOR_SUB_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN 
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL
    [ASM_SIMP_TAC[DOT_3;VECTOR_3;REAL_MUL_LZERO;REAL_MUL_LID;
                REAL_ADD_LID;REAL_ADD_RID] THEN 
    UNDISCH_TAC `norm (p2:real^3 - o1:real^3) = 
                 norm (p1:real^3 - o1)` THEN
    ASM_SIMP_TAC[vector_norm;DOT_3;VECTOR_3;REAL_MUL_LZERO;
                REAL_ADD_RID] THEN STRIP_TAC THEN 
    SUBGOAL_THEN `norm (w1:real^3) = &1` ASSUME_TAC THENL
    [ASM_SIMP_TAC[NORM_EQ_1;DOT_3;VECTOR_3] THEN
     ARITH_TAC;ALL_TAC] THEN            
    CONJ_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;homo_point;DIMINDEX_FINITE_SUM;
             DIMINDEX_3;DIMINDEX_1] THEN 
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `i <= 3` THENL  
    [POP_ASSUM MP_TAC THEN 
    DISCH_THEN (MP_TAC o MATCH_MP (ARITH_RULE `i <= 3 ==> 
                                  ~(i = 3 + 1)`)) THEN
    ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_1;DIMINDEX_3;DIMINDEX_FINITE_SUM;
                MATRIX_VECTOR_MUL_COMPONENT;dot] THEN 
    SIMP_TAC[ARITH_RULE `3 + 1 = 4`;SUM_4;
            (SIMP_RULE [] (GSYM point_tybij));VEC_COMPONENT;ARITH_EQ;
            REAL_MUL_RZERO;REAL_MUL_RID;REAL_ADD_LID] THEN 
    STRIP_TAC THEN 
    MP_TAC (ISPECL [`(vector [&0; &0; &1],vec 0):screw`;`a1:real`]          
            MATRIX_EXP_SCREW_COND_1) THEN 
    ASM_SIMP_TAC[FST] THEN ANTS_TAC THENL
    [ASM_MESON_TAC[];ALL_TAC] THEN 
    SIMP_TAC[] THEN STRIP_TAC THEN 
    SIMP_TAC[CROSS_RZERO;MATRIX_VECTOR_MUL_RZERO;VECTOR_MUL_RZERO;
            VECTOR_ADD_RID] THEN UNDISCH_TAC `i <= 3 + 1` THEN
    ASM_SIMP_TAC[HOMO_TRANS_COMPONENT;DIMINDEX_3;DIMINDEX_1;
                DIMINDEX_FINITE_SUM;ARITH_RULE `3 + 1 = 4`;
                ARITH_RULE `1 <= 4`;LE_REFL;VEC_COMPONENT];ALL_TAC] THEN
    ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_1;DIMINDEX_3;DIMINDEX_FINITE_SUM;
                MATRIX_VECTOR_MUL_COMPONENT;dot] THEN 
    SIMP_TAC[ARITH_RULE `3 + 1 = 4`;SUM_4;
            (SIMP_RULE [] (GSYM point_tybij));VEC_COMPONENT;ARITH_EQ;
            REAL_MUL_RZERO;REAL_MUL_RID;REAL_ADD_LID] THEN 
    MP_TAC (ISPECL [`(vector [&0; &0; &1],vec 0):screw`;`a1:real`]  
            MATRIX_EXP_SCREW_COND_1) THEN 
    ASM_SIMP_TAC[FST] THEN ANTS_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN 
    SIMP_TAC[] THEN STRIP_TAC THEN 
    SIMP_TAC[CROSS_RZERO;MATRIX_VECTOR_MUL_RZERO;VECTOR_MUL_RZERO;
            VECTOR_ADD_RID] THEN 
    UNDISCH_TAC `i <= 3 + 1` THEN 
    UNDISCH_TAC `~(i <= 3)` THEN 
    ASM_SIMP_TAC[HOMO_TRANS_COMPONENT;DIMINDEX_3;DIMINDEX_1;
                DIMINDEX_FINITE_SUM;ARITH_RULE `3 + 1 = 4`;
                ARITH_RULE `1 <= 4`;LE_REFL;VEC_COMPONENT];ALL_TAC] THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
                VEC_COMPONENT];ALL_TAC] THEN
    SUBGOAL_THEN `!x y z:real. vec3_vtrans (vector [&0; &0; &1]) **     
                vector [x; y; z] = vector [&0; &0; z]` ASSUME_TAC THENL            
    [ASM_SIMP_TAC[vec3_vtrans;CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;
                 VECTOR_3;MATRIX_VECTOR_MUL_COMPONENT;dot;
                 REAL_MUL_LZERO;SUM_3] THEN 
    ARITH_TAC;ALL_TAC] THEN 
    ASM_SIMP_TAC[VECTOR_SUB_RZERO;CROSS_LZERO;vector_norm;SQRT_EQ_1;
                VECTOR_3] THEN
    SUBGOAL_THEN `!x y z:real. 
                ((vector[x; y; z]:real^3) - (vector[&0; &0; z]:real^3)) = (vector[x; y; &0]:real^3)` ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             VECTOR_SUB_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN 
    SIMP_TAC[dot;cross;SUM_3;REAL_MUL_RZERO;REAL_MUL_LZERO;
            REAL_SUB_RZERO;VECTOR_3;DIMINDEX_3;REAL_MUL_LID;
            REAL_ADD_LID;REAL_ADD_RID] THEN 
    MESON_TAC[REAL_MUL_SYM;ARITH_RULE `(--(A:real)) + (B:real) = 
                                        B - A`]);;

let INVERTIBLE_MATRIX_EXP = prove    
    (`!x t. invertible (matrix_exp (t %% x))`,
    REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    MESON_TAC[MATRIX_EXP_INV_FUN;LIFT_DROP2]);;
 
let GST_RELATION_THETA56 = prove
    (`!s1 s2 s3 s4 s5 s6:screw x:real^3 a1 a2 a3 a4 a5 a6 d4 d5 c2 c3 M1 M2 M3 N1 N2 N3 G1 G2 G3 H1 H2 H3.
    gst a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6 x = 
    homo_trans (vector[H1; H2; H3])(vector[vector[M1;N1;G1];vector[M2;N2;G2];vector[M3;N3;G3]]:real^3^3) /\ x = vector[d4; &0; c2 + c3 + d5] /\ 
    s1 = ((vector[&0;&0;&1]:real^3),(vector[&0;&0;&0]:real^3)) /\
    s2 = ((vector[&1;&0;&0]:real^3),(vector[&0;&0;&0]:real^3)) /\
    s3 = ((vector[&1;&0;&0]:real^3),(vector[&0;c2;&0]:real^3)) /\
    s4 = ((vector[&1;&0;&0]:real^3),(vector[&0;c2 + c3;&0]:real^3)) /\
    s5 = ((vector[&0;&0;&1]:real^3),(vector[&0;--d4;&0]:real^3)) /\
    s6 = ((vector[&1;&0;&0]:real^3),(vector[&0;c2 + c3 +d5;&0]:real^3)) 
    ==> cos(a5) = M1 * cos(a1) + M2 * sin(a1) /\
        sin(a5) * sin(a6) = G1 * cos(a1) + G2 * sin(a1) /\
        --(sin(a5) * cos(a6)) = N1 * cos(a1) + N2 * sin(a1) /\
        sin(a5) * sin(a2 + a3 + a4) = M3 /\
        sin(a5) * cos(a2 + a3 + a4) = M2 * cos(a1) - M1 * sin(a1)`,
    REPEAT GEN_TAC THEN 
    SUBGOAL_THEN `invertible (matrix_exp ((a1:real) %% screw_2_matrix       
                s1))` ASSUME_TAC THENL
    [SIMP_TAC[INVERTIBLE_MATRIX_EXP];ALL_TAC] THEN 
    SUBGOAL_THEN `matrix_inv(matrix_exp((a1:real) %% screw_2_matrix     
                s1)) ** (gst1 a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6) = (gst2 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6)`  ASSUME_TAC THENL
    [ASM_SIMP_TAC[gst1;gst2;MATRIX_MUL_ASSOC;MATRIX_INV;
                  MATRIX_MUL_LID];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    STRIP_TAC THEN POP_ASSUM MP_TAC THEN 
    REWRITE_TAC[GSYM GST1;gst2;gst_initial] THEN 
    SIMP_TAC[MATRIX_INV_HOMO_TRANS;INVERTIBLE_I;MATRIX_INV_I;
            MATRIX_VECTOR_MUL_LNEG;MATRIX_VECTOR_MUL_LID] THEN 
    SUBGOAL_THEN `norm (FST (s1:screw)) = &1 /\ norm (FST (s2:screw)) 
                = &1 /\ norm (FST (s3:screw)) = &1 /\ norm (FST (s4:screw)) = &1 /\ norm (FST (s5:screw)) = &1 /\ norm (FST (s6:screw)) = &1` MP_TAC THENL
    [ASM_SIMP_TAC[DOT_3;VECTOR_3;NORM_EQ_1;FST] THEN ARITH_TAC;
    ALL_TAC] THEN
    SIMP_TAC[MATRIX_EXP_SCREW_COND_1] THEN
    ONCE_REWRITE_TAC[HOMO_TRANS_MUL_TRANS] THEN 
    SIMP_TAC[MATRIX_MUL_ASSOC] THEN 
    ONCE_REWRITE_TAC[HOMO_TRANS_MUL_TRANS] THEN 
    ONCE_REWRITE_TAC[HOMO_TRANS_MUL_TRANS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `homo_trans
    ((((mat 1 - matrix_exp ((a2:real) %% vec3_2_ssm (FST s2))) ** (FST s2 cross SND s2) +a2 % (vec3_vtrans (FST s2) ** SND s2)) +
    matrix_exp (a2 %% vec3_2_ssm (FST s2)) **((mat 1 - matrix_exp ((a3:real) %% vec3_2_ssm (FST s3))) ** (FST s3 cross SND s3) +
    a3 % (vec3_vtrans (FST s3) ** SND s3))) +(matrix_exp (a2 %% vec3_2_ssm (FST s2)) ** matrix_exp (a3 %% vec3_2_ssm (FST s3))) **
    ((mat 1 - matrix_exp ((a4:real) %% vec3_2_ssm (FST s4))) ** (FST s4 cross SND s4) + a4 % (vec3_vtrans (FST s4) ** SND s4)))
    ((matrix_exp (a2 %% vec3_2_ssm (FST s2)) ** matrix_exp (a3 %% vec3_2_ssm (FST s3))) ** matrix_exp (a4 %% vec3_2_ssm (FST s4))) = 
    homo_trans (matrix_exp (a2 %% vec3_2_ssm (FST s2)) ** 
    (FST s2 cross SND s3) + matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2)) ** (--(FST s2 cross SND s3) + (FST s2 cross SND s4)) - 
    matrix_exp ((a2 + a3 + a4) %% vec3_2_ssm (FST s2)) ** 
    (FST s2 cross SND s4)) (matrix_exp ((a2 + a3 + a4) %% vec3_2_ssm (FST s2)))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[cross;vec3_vtrans;FST;SND;VECTOR_3;REAL_MUL_RZERO;
                 REAL_MUL_LZERO;REAL_SUB_RZERO;REAL_MUL_LID;VEC_0;
                 MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_RID;VECTOR_ADD_LID] THEN 
    SIMP_TAC[GSYM VEC_0;VECTOR_3;VECTOR_ADD_RID;VECTOR_MUL_RZERO;
            VECTOR_MUL;REAL_MUL_RZERO;REAL_MUL_LZERO;REAL_SUB_RZERO;
            REAL_ADD_RID] THEN 
    SIMP_TAC[VEC_0;VECTOR_MUL_RZERO;MATRIX_VECTOR_MUL_RZERO;
    VECTOR_ADD_LID;VECTOR_ADD_RID;VECTOR_SUB_REFL] THEN 
    SUBGOAL_THEN `(a2 %% vec3_2_ssm (vector [&1; &0; &0])) ** (a3 %% vec3_2_ssm (vector [&1; &0; &0])) = 
    (a3 %% vec3_2_ssm (vector [&1; &0; &0])) ** (a2 %% vec3_2_ssm (vector [&1; &0; &0]))` ASSUME_TAC THENL
    [MESON_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL];ALL_TAC] THEN 
    ASM_SIMP_TAC[GSYM MATRIX_EXP_ADD;
                GSYM MATRIX_CMUL_ADD_RDISTRIB] THEN 
    SUBGOAL_THEN `((a2 + a3) %% vec3_2_ssm (vector [&1; &0; &0])) ** (a4 %% vec3_2_ssm (vector [&1; &0; &0])) = 
    (a4 %% vec3_2_ssm (vector [&1; &0; &0])) ** ((a2 + a3) %% vec3_2_ssm (vector [&1; &0; &0]))` ASSUME_TAC THENL
    [MESON_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL];ALL_TAC] THEN 
    ASM_SIMP_TAC[GSYM MATRIX_EXP_ADD;GSYM MATRIX_CMUL_ADD_RDISTRIB;
                GSYM REAL_ADD_ASSOC;MATRIX_SUB_LDISTRIB;VECTOR_ARITH `!x y:real^3. x - y = x + --y`;
                MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_RID;
                MATRIX_VECTOR_MUL_SUB_RDISTRIB;VECTOR_SUB;
                GSYM MATRIX_VECTOR_MUL_RNEG;
                MATRIX_VECTOR_MUL_ADD_LDISTRIB;
                GSYM VECTOR_ADD_ASSOC];ALL_TAC] THEN 
    ASM_SIMP_TAC[FST;SND;cross;RODRIGUES_FORMULA_COMPONENT;VECTOR_3;
                REAL_MUL_LID;REAL_MUL_LZERO;REAL_POW_2;REAL_SUB_RZERO;
                REAL_ADD_RID;REAL_ADD_LID;REAL_SUB_LZERO;REAL_ARITH `A:real - B + B = A`;REAL_ARITH `-- &0 = &0`] THEN 
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_MUL_RZERO;
                VECTOR_ADD_RID;REAL_NEG_NEG;VEC_0] THEN
    SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_SUB_RDISTRIB;
            MATRIX_VECTOR_MUL_LID;vec3_vtrans;VECTOR_3;REAL_MUL_RZERO;
            VECTOR_ADD_LNEG;VECTOR_MUL_RZERO;VEC_0;
            REAL_SUB_RZERO;REAL_MUL_RID;VECTOR_MUL;
            REAL_MUL_LZERO;REAL_ADD_RID;REAL_ADD_LID;
            REAL_ARITH `!x y:real. (x + y) - x = y`] THEN 
    SIMP_TAC[GSYM VEC_0;VECTOR_MUL;REAL_MUL_RZERO;REAL_MUL_LZERO;
            REAL_ADD_RID] THEN 
    SIMP_TAC[VEC_0;VECTOR_MUL_RZERO;VECTOR_ADD_RID] THEN      
    SUBGOAL_THEN `invertible (vector [vector [cos a1; --sin a1; &0]; vector [sin a1; cos a1; &0];vector [&0; &0; &1]]:real^3^3)` ASSUME_TAC THENL
    [SIMP_TAC[invertible] THEN  
    EXISTS_TAC `(vector [vector [cos a1; sin a1; &0]; vector [--sin a1; cos a1; &0];vector [&0; &0; &1]]:real^3^3)` THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;matrix_mul;
                VEC_COMPONENT;MAT_COMPONENT;VECTOR_3;SUM_3;
                GSYM REAL_POW_2;REAL_MUL_RZERO;REAL_MUL_LZERO;
                REAL_POW_ONE;GSYM REAL_NEG_RMUL;REAL_NEG_LMUL;
                REAL_NEG_MUL2;REAL_ADD_RID;REAL_MUL_SYM;SIN_CIRCLE;
                REAL_NEG_NEG;REAL_NEG_0;REAL_ADD_LID;REAL_ARITH `(a * b) + (-- a * b) = &0`;REAL_ADD_SYM;ARITH] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    SIMP_TAC[SIN_CIRCLE];ALL_TAC] THEN 
    ASM_SIMP_TAC[MATRIX_INV_HOMO_TRANS;MATRIX_VECTOR_MUL_RZERO;
                HOMO_TRANS_MUL_TRANS;VECTOR_ADD_LID;
                MATRIX_MUL_RID] THEN 
    SUBGOAL_THEN `matrix_inv(vector [vector [cos a1; --sin a1; &0]; vector [sin a1; cos a1; &0];vector [&0; &0; &1]]:real^3^3) = (vector [vector [cos a1; sin a1; &0]; 
    vector [--sin a1; cos a1; &0];
    vector [&0; &0; &1]]:real^3^3)` ASSUME_TAC THENL
    [ASM_SIMP_TAC [ISPECL[`(vector
    [vector [cos a1; --sin a1; &0]; vector [sin a1; cos a1; &0];
    vector [&0; &0; &1]]:real^3^3)`;`matrix_inv(vector
    [vector [cos a1; --sin a1; &0]; vector [sin a1; cos a1; &0];
    vector [&0; &0; &1]]:real^3^3)`] (GSYM MATRIX_MUL_LCANCEL)] THEN 
    ASM_SIMP_TAC[MATRIX_INV] THEN 
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
            matrix_mul;MAT_COMPONENT;SUM_3;REAL_NEG_NEG;REAL_MUL_LNEG;
            REAL_MUL_RNEG;REAL_MUL_LZERO;
            GSYM REAL_POW_2;REAL_MUL_LID;ARITH_EQ] THEN
    SIMP_TAC[REAL_ADD_ASSOC;
            (ONCE_REWRITE_RULE [REAL_ADD_SYM] SIN_CIRCLE)] THEN
    SIMP_TAC[SIN_CIRCLE] THEN ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[HOMO_TRANS_UNIQUE] THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;VECTOR_3;FORALL_3;SUM_3;
            matrix_vector_mul;vector_add;vector_sub;matrix_add;
            matrix_sub;matrix_mul;vector_neg;matrix_neg;REAL_ADD_LID;
            REAL_ADD_RID;REAL_MUL_RZERO;REAL_MUL_LZERO;REAL_MUL_LID;
            REAL_MUL_RID;REAL_NEG_0;REAL_SUB_LZERO;REAL_MUL_RNEG;
            ARITH_RULE `1 <= 3`;LE_REFL] THEN   
    SIMP_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;real_sub;
            REAL_NEG_NEG;REAL_MUL_LNEG;REAL_MUL_RNEG;
            GSYM REAL_MUL_ASSOC;REAL_NEG_ADD;GSYM REAL_ADD_ASSOC] THEN ARITH_TAC);;

let A56_SOLUTION = prove           
    (`!a1 a2 a3 a4 a5 a6 b2 b3 b4 b5 M1 M2 M3 G1 G2 N1 N2. 
    ~ (sin(a5) = &0) /\ --(pi / &2) < a6 /\ a6 < pi / &2 /\
    --(pi / &2) < (a2 + a3 + a4) /\ (a2 + a3 + a4) < pi / &2 /\
    b2 = M1 * cos(a1) + M2 * sin(a1) /\
    b3 = G1 * cos(a1) + G2 * sin(a1) /\ 
    b4 = N1 * cos(a1) + N2 * sin(a1) /\
    b5 = M2 * cos(a1) - M1 * sin(a1) /\
    cos(a5) = M1 * cos(a1) + M2 * sin(a1) /\
    sin(a5) * sin(a6) = G1 * cos(a1) + G2 * sin(a1) /\
    --(sin(a5) * cos(a6)) = N1 * cos(a1) + N2 * sin(a1) /\
    sin(a5) * sin(a2 + a3 + a4) = M3 /\
    sin(a5) * cos(a2 + a3 + a4) = M2 * cos(a1) - M1 * sin(a1)==>
    (&0 < a5 /\ a5 < pi / &2 ==>
    a5 = atn ((sqrt(&1 - (b2) pow 2)) / b2)) /\ 
    (--(pi / &2) < a5 /\ a5 < &0 ==> 
    a5 = atn (--(sqrt(&1 - (b2) pow 2)) / b2)) /\ 
    a6 = atn (((b3)/(sin(a5)))/(--(b4)/sin(a5))) /\
    a2 + a3 + a4 = atn ((M3/sin(a5))/(b5/(sin(a5))))`,
    REPEAT STRIP_TAC THENL 
    [ASM_SIMP_TAC[] THEN 
    UNDISCH_TAC `cos(a5) = M1 * cos(a1) + M2 * sin(a1)` THEN 
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[ONCE_REWRITE_RULE [REAL_ARITH `a + b = &1 <=> &1 - b = a`] SIN_CIRCLE] THEN SIMP_TAC[POW_2_SQRT_ABS] THEN 
    ASM_SIMP_TAC[REAL_ARITH `&0 < x /\ x < pi / &2 ==>
                &0 < x /\ x < pi`;SIN_POS_PI2;
                REAL_ARITH `!x. &0 < x ==> abs x = x`;
                GSYM tan;REAL_ARITH `&0 < x /\ x < pi / &2 ==>
                --(pi / &2) < x /\ x < pi / &2`;TAN_ATN];
    ASM_SIMP_TAC[] THEN 
    UNDISCH_TAC `cos(a5) = M1 * cos(a1) + M2 * sin(a1)` THEN 
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[ONCE_REWRITE_RULE [REAL_ARITH `a + b = &1 <=> &1 - b = a`] SIN_CIRCLE] THEN SIMP_TAC[POW_2_SQRT_ABS] THEN 
    MP_TAC (ISPEC `--(a5:real)` (SIN_POS_PI2)) THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x. (&0 < --x <=> x < &0) /\ 
                (--x < pi / &2 <=> --(pi / &2) < x)`;SIN_NEG;
                REAL_ARITH `!x. x < &0 ==> abs x = -- x`;REAL_NEG_NEG;
                REAL_ARITH `--(pi / &2) < x /\ x < &0 ==> 
                --(pi / &2) < x /\ x < pi / &2`;GSYM tan;TAN_ATN];
    UNDISCH_TAC `sin a5 * sin a6 = G1 * cos a1 + G2 * sin a1` THEN 
    UNDISCH_TAC `--(sin a5 * cos a6) = N1 * cos a1 + N2 * sin a1` THEN 
    ASM_SIMP_TAC[REAL_NEG_LMUL;REAL_FIELD `!a b c. ~(a = &0) ==> 
                ( a * b = c <=> b = c / a)`;
                REAL_FIELD `!a b c. ~(a = &0) ==>
                ( -- a * b = c <=> b = -- c / a)`] THEN
    DISCH_THEN(MP_TAC o SYM) THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN STRIP_TAC THEN 
    ASM_SIMP_TAC[GSYM tan;TAN_ATN];
    UNDISCH_TAC `sin a5 * sin (a2 + a3 + a4) = M3` THEN 
    UNDISCH_TAC `sin a5 * cos (a2 + a3 + a4) = 
    M2 * cos a1 - M1 * sin a1` THEN 
    ASM_SIMP_TAC[REAL_FIELD `!a b c. ~(a = &0) ==> 
                ( a * b = c <=> b = c / a)`] THEN 
    DISCH_THEN(MP_TAC o SYM) THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN STRIP_TAC THEN 
    ASM_SIMP_TAC[GSYM tan;TAN_ATN]]);;

let GST_RELATION_THETA23 = prove   
    (`!s2 s3 s4 s5 s6:screw a2 a3 a4 a5 a6 c2 c3 d4 d5 m1 m2 m3 n1 n2 n3 g1 g2 g3 t4 t5 t6 t7 t8.     
    s2 = ((vector[&1;&0;&0]:real^3),(vector[&0;&0;&0]:real^3)) /\
    s3 = ((vector[&1;&0;&0]:real^3),(vector[&0;c2;&0]:real^3)) /\
    s4 = ((vector[&1;&0;&0]:real^3),(vector[&0;c2 + c3;&0]:real^3)) /\
    s5 = ((vector[&0;&0;&1]:real^3),(vector[&0;--d4;&0]:real^3)) /\
    s6 = ((vector[&1;&0;&0]:real^3),
    (vector[&0;c2 + c3 +d5;&0]:real^3)) /\
    t7 = t5 - (c2 + c3) * sin(a2 + a3 + a4) /\
    t8 = t6 + (c2 + c3) * cos(a2 + a3 + a4) /\
    gst3 a2 s2 a3 s3 a4 s4 = homo_trans (vector[t4; t5; t6])(vector[vector[m1;n1;g1];
    vector[m2;n2;g2];vector[m3;n3;g3]]:real^3^3) ==>
    -- c3 * sin(a2 + a3) - c2 * sin(a2) = t7 /\
    c3 * cos(a2 + a3) + c2 * cos(a2) = t8`,
    let lemma1 = prove
        (`!A:real^N^N B:real^N^N C:real^N^N D:real^N^N E:real^N^N H:real^N^N G:real^N^N. A ** B ** C ** D ** E ** H ** G =  A ** B ** C ** D ** (E ** H) ** G`,  
        REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN 
        SIMP_TAC[MATRIX_MUL_ASSOC]) in 
    REPEAT GEN_TAC THEN DISCH_TAC THEN 
    SUBGOAL_THEN `invertible (matrix_exp ((a5:real) %% screw_2_matrix s5))  /\ invertible (matrix_exp ((a6:real) %% screw_2_matrix s6))` 
    ASSUME_TAC THENL [SIMP_TAC[INVERTIBLE_MATRIX_EXP];ALL_TAC] THEN
    SUBGOAL_THEN `gst2 a2 s2 a3 s3 a4 s4 a5 s5 a6 s6 ** matrix_inv(matrix_exp((a6:real) %% screw_2_matrix s6)) **  matrix_inv(matrix_exp((a5:real) %% screw_2_matrix s5)) = gst3 a2 s2 a3 s3 a4 s4` ASSUME_TAC THENL
    [SIMP_TAC[gst2;gst3;GSYM MATRIX_MUL_ASSOC] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[MATRIX_INV;MATRIX_MUL_LID;MATRIX_MUL_RID;lemma1];
    ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN  STRIP_TAC THEN STRIP_TAC THEN 
    UNDISCH_TAC `gst3 a2 s2 a3 s3 a4 s4 = 
    homo_trans (vector[t4; t5; t6])(vector[vector[m1;n1;g1];
    vector[m2;n2;g2];vector[m3;n3;g3]]:real^3^3)` THEN
    SIMP_TAC[gst2;GSYM MATRIX_MUL_ASSOC] THEN 
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[MATRIX_INV;MATRIX_MUL_LID;MATRIX_MUL_RID;lemma1] THEN 
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN 
    SUBGOAL_THEN `norm (FST (s2:screw)) = &1 /\ 
    norm (FST (s3:screw)) = &1 /\ norm (FST (s4:screw)) = &1 /\ norm (FST (s5:screw)) = &1 /\ norm (FST (s6:screw)) = &1` MP_TAC THENL
    [ASM_SIMP_TAC[DOT_3;VECTOR_3;NORM_EQ_1;FST] THEN ARITH_TAC;
    ALL_TAC] THEN 
    SIMP_TAC[MATRIX_EXP_SCREW_COND_1] THEN STRIP_TAC THEN   
    SIMP_TAC[MATRIX_MUL_ASSOC] THEN 
    ONCE_REWRITE_TAC[HOMO_TRANS_MUL_TRANS] THEN 
    SUBGOAL_THEN `homo_trans
    (((mat 1 - matrix_exp ((a2:real) %% vec3_2_ssm (FST s2))) ** (FST s2 cross SND s2) + a2 % (vec3_vtrans (FST s2) ** SND s2)) +
    matrix_exp (a2 %% vec3_2_ssm (FST s2)) **
    ((mat 1 - matrix_exp ((a3:real) %% vec3_2_ssm (FST s3))) ** (FST s3 cross SND s3) +
    a3 % (vec3_vtrans (FST s3) ** SND s3)))
    (matrix_exp (a2 %% vec3_2_ssm (FST s2)) **
    matrix_exp (a3 %% vec3_2_ssm (FST s3)))  =
    homo_trans ((matrix_exp (a2 %% vec3_2_ssm (FST s2)) - matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2))) ** (FST s2 cross SND s3))(matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2)))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[cross;vec3_vtrans;FST;SND;VECTOR_3;REAL_MUL_RZERO;
                 REAL_MUL_LZERO;REAL_SUB_RZERO;REAL_MUL_LID] THEN 
    SUBGOAL_THEN `(vector [&0; &0; &0]:real^3) = vec 0` 
    ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             VEC_COMPONENT];ALL_TAC] THEN 
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_RID;VECTOR_ADD_LID;
                VECTOR_MUL_RZERO] THEN  
    SUBGOAL_THEN `!x. vector [vector [&1; &0; &0]; vec 0;vec 0]:real^3^3 ** (vector [&0; x; &0]:real^3) = vec 0` 
    ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;DOT_3;
             VEC_COMPONENT;MATRIX_VECTOR_MUL_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[VECTOR_ADD_RID;VECTOR_MUL_RZERO] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_RID;
            MATRIX_SUB_LDISTRIB] THEN 
    SUBGOAL_THEN `(a2 %% vec3_2_ssm (vector [&1; &0; &0])) ** (a3 %% vec3_2_ssm (vector [&1; &0; &0])) = (a3 %% vec3_2_ssm 
    (vector [&1; &0; &0])) ** (a2 %% vec3_2_ssm (vector [&1; &0; &0]))` ASSUME_TAC THENL
    [MESON_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL];ALL_TAC] THEN 
    ASM_SIMP_TAC[GSYM MATRIX_EXP_ADD;GSYM MATRIX_CMUL_ADD_RDISTRIB];
    ALL_TAC] THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[] THEN STRIP_TAC THEN SIMP_TAC[HOMO_TRANS_MUL_TRANS] THEN 
    SUBGOAL_THEN `homo_trans ((matrix_exp ((a2:real) %% 
    vec3_2_ssm (FST (s2:screw))) - matrix_exp ((a2 + (a3:real)) %% vec3_2_ssm (FST s2))) ** (FST s2 cross SND (s3:screw)) +
    matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2)) **
    ((mat 1 - matrix_exp ((a4:real) %% vec3_2_ssm (FST (s4:screw)))) ** (FST s4 cross SND s4) + a4 % (vec3_vtrans (FST s4) ** SND s4)))
    (matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2)) **
    matrix_exp (a4 %% vec3_2_ssm (FST s4))) = 
    homo_trans ((matrix_exp (a2 %% vec3_2_ssm (FST s2)) -
    matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2))) ** (FST s2 cross SND s3) + (matrix_exp ((a2 + a3) %% vec3_2_ssm (FST s2)) - matrix_exp ((a2 + a3 + a4) %% vec3_2_ssm (FST s2))) ** (FST s2 cross SND s4))
    (matrix_exp ((a2 + a3 + a4) %% vec3_2_ssm (FST s2)))`
    ASSUME_TAC THENL
    [ASM_SIMP_TAC[FST;SND;cross;vec3_vtrans;VECTOR_3;REAL_MUL_RZERO;
                 REAL_MUL_LZERO;REAL_SUB_RZERO;REAL_MUL_LID] THEN 
    SUBGOAL_THEN `!x. vector [vector [&1; &0; &0];vector [&0; &0; &0];vector [&0; &0; &0]]:real^3^3 ** (vector [&0; x; &0]:real^3) = vec 0` ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;DOT_3;
             VEC_COMPONENT;MATRIX_VECTOR_MUL_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_ADD_RID;VECTOR_MUL_RZERO] THEN                 
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_RID;
            MATRIX_SUB_LDISTRIB] THEN 
    SUBGOAL_THEN `((a2 + a3) %% vec3_2_ssm (vector [&1; &0; &0])) ** (a4 %% vec3_2_ssm (vector [&1; &0; &0])) = 
    (a4 %% vec3_2_ssm (vector [&1; &0; &0])) ** ((a2 + a3) %% vec3_2_ssm (vector [&1; &0; &0]))` ASSUME_TAC THENL
    [MESON_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM MATRIX_EXP_ADD;GSYM MATRIX_CMUL_ADD_RDISTRIB] THEN STRIP_TAC THEN SIMP_TAC[GSYM REAL_ADD_ASSOC];ALL_TAC] THEN 
    ASM_SIMP_TAC[FST;SND;GSYM REAL_ADD_ASSOC;cross;vec3_vtrans;
                RODRIGUES_FORMULA_COMPONENT;VECTOR_3;REAL_MUL_LID;
                REAL_MUL_LZERO;REAL_POW_2;REAL_SUB_RZERO;REAL_ADD_RID;
                REAL_ADD_LID;REAL_SUB_LZERO;REAL_ARITH `A:real - B + B = A`;REAL_ARITH `-- &0 = &0`] THEN  
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
            MATRIX_VECTOR_MUL_SUB_LDISTRIB;
            MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    SUBGOAL_THEN `!a b c d. (vector [vector [&1; &0; &0];
    vector [&0; b; -- a];vector [&0; a; b]]:real^3^3) **
    (vector [&0; d; c]:real^3) = (vector [&0; b * d - a * c;a * d +
    b * c]:real^3)` ASSUME_TAC THENL 
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;
             VECTOR_NEG_COMPONENT;MATRIX_VECTOR_MUL_COMPONENT;DOT_3;
             SUM_3] THEN
    ARITH_TAC;ALL_TAC] THEN   
    ASM_SIMP_TAC[HOMO_TRANS_UNIQUE;REAL_MUL_RZERO;REAL_SUB_LZERO] THEN 
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;VECTOR_3;FORALL_3;SUM_3;
            vector_add;vector_sub;matrix_add;matrix_sub;matrix_mul;
            vector_neg;matrix_neg;REAL_ADD_LID;REAL_ADD_RID;
            REAL_MUL_RZERO;REAL_MUL_LZERO;REAL_MUL_LID;REAL_MUL_RID;
            REAL_NEG_0;REAL_SUB_LZERO;REAL_MUL_RNEG;
            ARITH_RULE `1 <= 3`;LE_REFL] THEN 
    SIMP_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;real_sub;REAL_NEG_NEG;     
            REAL_MUL_LNEG;REAL_MUL_RNEG;GSYM REAL_MUL_ASSOC;
            REAL_NEG_ADD;GSYM REAL_ADD_ASSOC] THEN  
            REPEAT STRIP_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    UNDISCH_TAC `--(sin a2 * c2) + sin (a2 + a3) * c2 +
      --(sin (a2 + a3) * c2) + --(sin (a2 + a3) * c3) +
      sin (a2 + a3 + a4) * c2 + sin (a2 + a3 + a4) * c3 = t5` THEN 
    ARITH_TAC;ALL_TAC] THEN POP_ASSUM MP_TAC THEN
    DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `cos a2 * c2 + --(cos (a2 + a3) * c2) +
    cos (a2 + a3) * c2 + cos (a2 + a3) * c3 + --(cos (a2 + a3 + a4) * c2) + --(cos (a2 + a3 + a4) * c3) = t6` THEN ARITH_TAC);;

let REAL_ADD_POW_2 = prove
  (`!x y:real. (x+y) pow 2 = x pow 2 + y pow 2 + &2 * x * y`,
  REAL_ARITH_TAC);;    

 
let A2_SOLUTION = prove 
    (`!a2 a3 c2 c3 t7 t8 b6 b7 A B C.           
    --(pi / &2) < a2 /\ a2 < pi / &2 /\
    --(pi / &2) < (a2 + a3) /\ (a2 + a3) < pi / &2 /\            
    -- (c3 * sin(a2 + a3)) - c2 * sin(a2) = t7 /\
    c3 * cos(a2 + a3) + c2 * cos(a2) = t8 /\
    A = (&2 * c2 * t7) /\ B = (&2 * c2 * t8) /\ 
    C = ((c3) pow 2 - (c2) pow 2 - (t7) pow 2 - (t8) pow 2) /\
    b6 = (c2 * sin(a2) + t7) /\
    b7 = (t8 - c2 * cos(a2)) /\ ~(c3 = &0) /\
    ~(c2 = &0) /\ ~(t7 = &0) /\ ~(t7 pow 2 + t8 pow 2 = &0) /\
    (--(pi / &2) < (atn (t8 / t7) + atn ((t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2)))) /\ ((atn (t8 / t7) + atn ((t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))) < (pi / &2)) ==>
    (&0 < (&2 * t7 * c2 * cos(a2) + &2 * t8 * c2 * sin(a2)) ==>
    (a2 = atn(B / A) + atn(C / (sqrt((A pow 2) + (B pow 2) - (C pow 2)))))) /\  
    ((&2 * t7 * c2 * cos(a2) + &2 * t8 * c2 * sin(a2)) < &0 ==>
    (a2 = atn(B / A) + atn(C / (--(sqrt((A pow 2) + (B pow 2) - (C pow 2))))))) /\ a2 + a3 = atn((--(b6) / c3) / (b7 / c3))`,
    REPEAT STRIP_TAC THENL [ 
    SUBGOAL_THEN `C = &2 * t7 * c2 * sin(a2) - &2 * t8 * c2 * cos(a2)` ASSUME_TAC THENL[
    MP_TAC(ISPEC `(c3 pow 2):real` (REAL_MUL_RID)) THEN
    ASM_SIMP_TAC[REAL_ARITH `!a b c:real. 
                a - b = c <=> a = c + b`] THEN 
    SUBGOAL_THEN `c3 pow 2 = (c3 * cos (a2 + a3)) pow 2 + (c3 * sin (a2 + a3)) pow 2` ASSUME_TAC THENL
    [MESON_TAC[REAL_POW_MUL;REAL_ADD_LDISTRIB;REAL_ADD_SYM;
              GSYM REAL_ADD_LDISTRIB;SIN_CIRCLE;REAL_MUL_RID];
    ALL_TAC] THEN 
    ASM_SIMP_TAC[] THEN  
    UNDISCH_TAC `--(c3 * sin (a2 + a3)) - c2 * sin a2 = t7` THEN 
    UNDISCH_TAC `c3 * cos (a2 + a3) + c2 * cos a2 = t8` THEN 
    SIMP_TAC[REAL_ARITH `!a b c:real. a + b = c <=>
            a = c - b`;REAL_ARITH `!a b c:real. --(a) - b = c <=>
            a = --(c + b)`] THEN 
    REPEAT STRIP_TAC THEN 
    SIMP_TAC[GSYM (REAL_ARITH `!a b c:real. a + b = c <=> 
            a = c - b`)] THEN
    SIMP_TAC[REAL_ARITH `!a b:real. a - b = a + (--b)`;
            REAL_ADD_POW_2] THEN 
    SIMP_TAC[GSYM (REAL_ARITH `!a b:real. a - b = a + (--b)`);
            REAL_POW_2;REAL_NEG_MUL2] THEN 
    SIMP_TAC[GSYM REAL_POW_2;REAL_MUL_RNEG;REAL_ADD_POW_2;
            REAL_ARITH `!a b:real. a + -- b = a - b`]THEN SIMP_TAC[GSYM REAL_ADD_ASSOC] THEN 
    SIMP_TAC[REAL_ARITH `!A B1 B2 C D E :real. 
            A + B1 - C + D + B2 + E = (B2 + B1) - C + D + A + E `;
            REAL_POW_MUL;GSYM REAL_ADD_LDISTRIB;SIN_CIRCLE;
            REAL_MUL_RID] THEN ARITH_TAC;ALL_TAC] THEN 
    SUBGOAL_THEN `sqrt (A pow 2 + B pow 2 - C pow 2) =  &2 * t7 * c2 * cos a2 + &2 * t8 * c2 * sin a2` ASSUME_TAC THENL 
    [POP_ASSUM MP_TAC THEN UNDISCH_TAC `A = &2 * c2 * t7` THEN 
    UNDISCH_TAC `B = &2 * c2 * t8` THEN 
    SIMP_TAC[REAL_ARITH `!a b:real. a - b = a + (--b)`;
            REAL_ADD_POW_2] THEN 
    SIMP_TAC[REAL_POW_2;REAL_NEG_MUL2] THEN             
    SIMP_TAC[REAL_MUL_RNEG;REAL_ARITH `!a b:real. a + -- b = a - b`;
            GSYM REAL_POW_2] THEN REPEAT STRIP_TAC THEN        
    SIMP_TAC[REAL_ARITH `!A A1 B B1 C:real. A + B - (A1 + B1 - C) = 
            (A - A1) + (B - B1) + C`;REAL_POW_MUL;REAL_ARITH `!A B C D:real. 
            A * B * C - A * C * B * D = A * C * B *(&1 - D)`] THEN 
    SUBGOAL_THEN `!x. &1 - sin x pow 2 = cos x pow 2 /\ !x. 
                 &1 - cos x pow 2 = sin x pow 2` ASSUME_TAC THENL 
    [REPEAT STRIP_TAC THENL
    [SIMP_TAC[REAL_ARITH `&1 - a = b <=> a + b = &1`;SIN_CIRCLE];ALL_TAC] THEN 
    MESON_TAC[REAL_ARITH `&1 - a = b <=> a + b = &1`;REAL_ADD_SYM;
             SIN_CIRCLE];ALL_TAC] THEN 
    ASM_SIMP_TAC[GSYM REAL_POW_MUL;REAL_ARITH `&2 * (&2 * a * b * c1) *         
                &2 * a2 * b * c2 = &2 * (&2 * a * b * c2) * &2 * a2 * b * c1`;GSYM REAL_ADD_POW_2;POW_2_SQRT_ABS;REAL_ABS_REFL;
                REAL_LT_IMP_LE];ALL_TAC] THEN 
    UNDISCH_TAC `C = &2 * t7 * c2 * sin a2 - &2 * t8 * c2 * cos a2` THEN 
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `&2 * a1 * b * c1 - &2 * a2 * b * c2 = 
            (&2 * b) * (a1 * c1 - a2 * c2)`;
            REAL_ARITH `&2 * a1 * b * c1 + &2 * a2 * b * c2 = 
            (&2 * b) * (a1 * c1 + a2 * c2)`;REAL_MUL_ASSOC] THEN 
    ASM_SIMP_TAC[REAL_FIELD `!z x y:real. ~(z = &0) ==> 
                (z * x) / (z * y) = x / y`;REAL_ARITH `~(z = &0) ==> ~(&2 * z = &0)`] THEN 
    UNDISCH_TAC `&0 < &2 * t7 * c2 * cos a2 + 
                &2 * t8 * c2 * sin a2` THEN
    SIMP_TAC[REAL_LT_LE;REAL_ARITH `&2 * a1 * b * c1 +
            &2 * a2 * b * c2 = (&2 * b) * ( a1 * c1 + a2 * c2)`] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN 
    SIMP_TAC[REAL_ENTIRE;DE_MORGAN_THM;REAL_ARITH `~(&2 = &0)`] THEN 
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `~(t7 * (t7 * cos a2 + t8 * sin a2) = &0)` 
    ASSUME_TAC THENL 
    [ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) ==> 
                             ~(b * d = &0)`] THEN 
    ARITH_TAC;ALL_TAC] THEN 
    SUBGOAL_THEN `~(&1 - (t8 / t7) * (t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2) = &0)` ASSUME_TAC THENL 
    [ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0)        
                 ==> (a / b) * (c / d) = (a * c) / (b * d)`;
                 REAL_FIELD `~(b = &0) ==>
                 &1 - a / b = (b - a) / b`;REAL_FIELD `~(b = &0) /\
                 ~(a / b = &0) ==> ~(a = &0)`] THEN 
    MATCH_MP_TAC (REAL_FIELD `~(a = &0) /\ ~(a = b) ==> 
    ~((a - b) / a = &0)`) THEN 
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB;REAL_SUB_LDISTRIB;REAL_MUL_ASSOC;
                GSYM REAL_POW_2] THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC;REAL_ARITH `! a b c1 c2:real.
            a pow 2 * c1 + a * b * c2 = a pow 2 * c1 + b * a * c2`;REAL_ARITH `!a b:real. a - b = a + --b`] THEN 
    MATCH_MP_TAC (REAL_FIELD `!a b c d:real. ~(d = &0) /\ ~(a = --c) ==> ~(a * d + b = b + --(c * d))`) THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[COS_POS_PI;REAL_ARITH `!x. &0 < x ==> ~(x = &0)`];
    ALL_TAC] THEN 
    UNDISCH_TAC `~(t7 pow 2 + t8 pow 2 = &0)` THEN 
    ASM_SIMP_TAC[REAL_ARITH ` ~(a + b = &0) ==> ~(a = --b)`];
    ALL_TAC] THEN
    SUBGOAL_THEN `~(t7 * (t7 * cos a2 + t8 * sin a2) - t8 * (t7 * sin a2 - t8 * cos a2) = &0)` ASSUME_TAC THENL [POP_ASSUM MP_TAC THEN 
    ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0)        
                ==> (a / b) * (c / d) = (a * c) / (b * d)`;
                REAL_FIELD `!a b c d:real. ~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0) ==> a / b + c / d = 
                (a * d + b * c) / (b * d)`;REAL_FIELD `~(b = &0) ==> 
                &1 - a / b = (b - a) / b`] THEN 
    ASM_SIMP_TAC[REAL_FIELD `~(a = &0) /\ ~(((a - b) / a) = &0)
                ==> ~((a - b) = &0)`];ALL_TAC] THEN 
    SUBGOAL_THEN `tan(a2) = ((t8 / t7) + ((t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))) / (&1 - ((t8 / t7) * ((t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0)   
                 ==> (a / b) * (c / d) = (a * c) / (b * d)`;
                 REAL_FIELD `!a b c d:real. ~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0) ==> a / b + c / d = (a * d + b * c) / (b * d)`;REAL_FIELD `~(b = &0) ==> &1 - a / b = (b - a) / b`;REAL_FIELD `!x y z:real. ~(y = &0) /\ ~(z = &0) ==> x / z / (y / z) = x / y`] THEN 
    SIMP_TAC[REAL_ADD_LDISTRIB;REAL_SUB_LDISTRIB;REAL_MUL_ASSOC;
            GSYM REAL_POW_2] THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC;GSYM REAL_ADD_ASSOC;
            REAL_ARITH `!a b c1 c2:real. a * b * c1 + a pow 2 * c2 + b pow 2 * c2 - b * a * c1 = (b pow 2  + a pow 2) * c2`;
            REAL_ARITH `!a b c1 c2:real. 
            (b pow 2 * c1 + b * a * c2) - (a * b * c2 - a pow 2 * c1) = (b pow 2  + a pow 2) * c1`] THEN 
    ASM_SIMP_TAC[REAL_FIELD `!x y z:real. ~(z = &0) ==> 
                (z * x) / (z * y) = x / y`;tan];ALL_TAC] THEN 
    MP_TAC (ISPECL[`atn ((t8:real) / (t7:real)) `;
    `atn ((t7 * sin (a2:real) - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))`] TAN_ADD) THEN 
    POP_ASSUM MP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[ATN_TAN] THEN 
    STRIP_TAC THEN ANTS_TAC THENL [CONJ_TAC THENL[
    SIMP_TAC[COS_ZERO_PI;DE_MORGAN_THM;NOT_EXISTS_THM] THEN 
    CONJ_TAC THENL[GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(x = y)`) THEN ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 < (&(n:num) + &1 / &2) * pi` 
    ASSUME_TAC THENL[
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x y:real. &0 < y ==> x < y + x`;
                PI_POS];ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_ARITH `&1 / &2 * x                   
                 = x / &2`;REAL_LT_TRANS];ALL_TAC] THEN 
    GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(y = x)`) THEN 
    ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN 
    SUBGOAL_THEN `--((&(n:num) + &1 / &2) * pi) < --(pi / &2)` ASSUME_TAC THENL[SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`;
                             REAL_NEG_LMUL] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN SIMP_TAC[PI_POS] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_NEG_ADD] THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. -- x < --y ==> y < x`) THEN ASM_SIMP_TAC[GSYM REAL_NEG_ADD;REAL_NEG_NEG;
                REAL_ARITH `!x y:real. &0 < y ==> x < y + x`];
    ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;
                    REAL_ARITH `&1 / &2 * x = x / &2`;
                    REAL_LT_TRANS];ALL_TAC] THEN 
    CONJ_TAC THENL
    [SIMP_TAC[COS_ZERO_PI;DE_MORGAN_THM;NOT_EXISTS_THM] THEN 
    CONJ_TAC THENL [GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(x = y)`) THEN ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 < (&(n:num) + &1 / &2) * pi` 
    ASSUME_TAC THENL
    [POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x y:real. &0 < y ==> x < y + x`;PI_POS];
    ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(y = x)`) THEN 
    ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN 
    SUBGOAL_THEN `--((&(n:num) + &1 / &2) * pi) < --(pi / &2)` ASSUME_TAC THENL[SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`;
                             REAL_NEG_LMUL] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN SIMP_TAC[PI_POS] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN 
    SIMP_TAC[REAL_NEG_ADD] THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. -- x < --y ==> y < x`) THEN ASM_SIMP_TAC[GSYM REAL_NEG_ADD;REAL_NEG_NEG;REAL_ARITH `!x y:real.          
                &0 < y ==> x < y + x`];ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    SIMP_TAC[COS_ZERO_PI;DE_MORGAN_THM;NOT_EXISTS_THM] THEN 
    CONJ_TAC THENL [GEN_TAC THEN MATCH_MP_TAC (REAL_ARITH `!x y:real.
    x < y ==> ~(x = y)`) THEN ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 < (&(n:num) + &1 / &2) * pi` 
    ASSUME_TAC THENL[
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN    STRIP_TAC THEN SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x y:real. &0 < y ==> x < y + x`;PI_POS];
    ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(y = x)`) THEN 
    ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN 
    SUBGOAL_THEN `--((&(n:num) + &1 / &2) * pi) < --(pi / &2)` ASSUME_TAC THENL
    [SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`;REAL_NEG_LMUL] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN SIMP_TAC[PI_POS] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_NEG_ADD] THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. -- x < --y ==> y < x`) THEN ASM_SIMP_TAC[GSYM REAL_NEG_ADD;REAL_NEG_NEG;REAL_ARITH `!x y:real.             
                &0 < y ==> x < y + x`];ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    DISCH_THEN(MP_TAC o AP_TERM `atn`) THEN ASM_SIMP_TAC[TAN_ATN];
    SUBGOAL_THEN `C = &2 * t7 * c2 * sin(a2) - &2 * t8 * c2 * cos(a2)` ASSUME_TAC THENL[
    MP_TAC(ISPEC `(c3 pow 2):real` (REAL_MUL_RID)) THEN 
    ASM_SIMP_TAC[REAL_ARITH `!a b c:real. 
                a - b = c <=> a = c + b`] THEN 
    SUBGOAL_THEN `c3 pow 2 = (c3 * cos (a2 + a3)) pow 2 + (c3 * sin (a2 + a3)) pow 2` ASSUME_TAC THENL
    [MESON_TAC[REAL_POW_MUL;REAL_ADD_LDISTRIB;REAL_ADD_SYM;
              GSYM REAL_ADD_LDISTRIB;SIN_CIRCLE;REAL_MUL_RID];
    ALL_TAC] THEN 
    ASM_SIMP_TAC[] THEN  
    UNDISCH_TAC `--(c3 * sin (a2 + a3)) - c2 * sin a2 = t7` THEN 
    UNDISCH_TAC `c3 * cos (a2 + a3) + c2 * cos a2 = t8` THEN 
    SIMP_TAC[REAL_ARITH `!a b c:real. a + b = c <=> a = c - b`;
            REAL_ARITH `!a b c:real. --(a) - b = c <=> 
            a = --(c + b)`] THEN 
    REPEAT STRIP_TAC THEN SIMP_TAC[GSYM (REAL_ARITH `!a b c:real. 
                                  a + b = c <=> a = c - b`)] THEN
    SIMP_TAC[REAL_ARITH `!a b:real. a - b = a + (--b)`;
            REAL_ADD_POW_2] THEN 
    SIMP_TAC[GSYM (REAL_ARITH `!a b:real. a - b = a + (--b)`);
            REAL_POW_2;REAL_NEG_MUL2] THEN 
    SIMP_TAC[GSYM REAL_POW_2;REAL_MUL_RNEG;REAL_ADD_POW_2;
            REAL_ARITH `!a b:real. a + -- b = a - b`]THEN 
    SIMP_TAC[GSYM REAL_ADD_ASSOC] THEN 
    SIMP_TAC[REAL_ARITH `!A B1 B2 C D E :real. 
            A + B1 - C + D + B2 + E = (B2 + B1) - C + D + A + E `;
            REAL_POW_MUL;GSYM REAL_ADD_LDISTRIB;SIN_CIRCLE;
            REAL_MUL_RID] THEN ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `sqrt (A pow 2 + B pow 2 - C pow 2) = --(&2 * t7 * c2 * cos a2 + &2 * t8 * c2 * sin a2)` ASSUME_TAC THENL 
    [POP_ASSUM MP_TAC THEN UNDISCH_TAC `A = &2 * c2 * t7` THEN 
    UNDISCH_TAC `B = &2 * c2 * t8` THEN 
    SIMP_TAC[REAL_ARITH `!a b:real. a - b = a + (--b)`;
            REAL_ADD_POW_2] THEN 
    SIMP_TAC[REAL_POW_2;REAL_NEG_MUL2] THEN             
    SIMP_TAC[REAL_MUL_RNEG;REAL_ARITH `!a b:real. a + -- b = a - b`;
            GSYM REAL_POW_2] THEN REPEAT STRIP_TAC THEN        
    SIMP_TAC[REAL_ARITH `!A A1 B B1 C:real. A + B - (A1 + B1 - C) = 
            (A - A1) + (B - B1) + C`;REAL_POW_MUL;
            REAL_ARITH `!A B C D:real. A * B * C - A * C * B * D = A * C * B *(&1 - D)`] THEN 
    SUBGOAL_THEN `!x. &1 - sin x pow 2 = cos x pow 2 /\ !x. &1 - cos x pow 2 = sin x pow 2` ASSUME_TAC THENL [REPEAT STRIP_TAC THENL
    [SIMP_TAC[REAL_ARITH `&1 - a = b <=> a + b = &1`;
             SIN_CIRCLE];ALL_TAC] THEN 
    MESON_TAC[REAL_ARITH `&1 - a = b <=> a + b = &1`;REAL_ADD_SYM;
             SIN_CIRCLE];ALL_TAC] THEN 
    ASM_SIMP_TAC[GSYM REAL_POW_MUL;REAL_ARITH `&2 * (&2 * a * b * c1) *         
                &2 * a2 * b * c2 = &2 * (&2 * a * b * c2) * &2 * a2 * b * c1`;GSYM REAL_ADD_POW_2; POW_2_SQRT_ABS] THEN 
    MP_TAC (ISPEC `(&2 * (t7:real) * (c2:real) * cos (a2:real) + &2 * (t8:real) * c2 * sin a2)` REAL_ABS_NEG) THEN 
    DISCH_THEN(MP_TAC o SYM) THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x:real. x < &0 ==> &0 <= --x`;
                REAL_ABS_REFL];ALL_TAC] THEN 
    UNDISCH_TAC `C = &2 * t7 * c2 * sin a2 - &2 * t8 * c2 * cos a2` THEN 
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `&2 * a1 * b * c1 - &2 * a2 * b * c2 = 
            (&2 * b) * (a1 * c1 - a2 * c2)`;REAL_ARITH `&2 * a1 * b * c1 + &2 * a2 * b * c2 = (&2 * b) * (a1 * c1 + a2 * c2)`;
            REAL_MUL_ASSOC] THEN 
    ASM_SIMP_TAC[REAL_FIELD `!z x y:real. ~(z = &0) ==> 
                (z * x) / (z * y) = x / y`;REAL_ARITH `~(z = &0) ==> 
                ~(&2 * z = &0)`;REAL_NEG_NEG] THEN 
    UNDISCH_TAC `&2 * t7 * c2 * cos a2 + &2 * t8 * c2 * sin a2 < &0` THEN SIMP_TAC[REAL_LT_LE;REAL_ARITH `&2 * a1 * b * c1 + &2 * a2 * b * c2 = 
            (&2 * b) * ( a1 * c1 + a2 * c2)`] THEN 
    SIMP_TAC[REAL_ENTIRE;DE_MORGAN_THM;REAL_ARITH `~(&2 = &0)`] THEN 
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `~(t7 * (t7 * cos a2 + t8 * sin a2) = &0)` 
    ASSUME_TAC THENL 
    [ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) ==> 
                             ~(b * d = &0)`] THEN 
    ARITH_TAC;ALL_TAC] THEN 
    SUBGOAL_THEN `~(&1 - (t8 / t7) * (t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2) = &0)` ASSUME_TAC THENL 
    [ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0)        
                 ==> (a / b) * (c / d) = (a * c) / (b * d)`;
                 REAL_FIELD `~(b = &0) ==>
                 &1 - a / b = (b - a) / b`;REAL_FIELD `~(b = &0) /\
                 ~(a / b = &0) ==> ~(a = &0)`] THEN 
    MATCH_MP_TAC (REAL_FIELD `~(a = &0) /\ ~(a = b) ==> 
    ~((a - b) / a = &0)`) THEN 
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB;REAL_SUB_LDISTRIB;REAL_MUL_ASSOC;
                GSYM REAL_POW_2] THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC;REAL_ARITH `! a b c1 c2:real.
            a pow 2 * c1 + a * b * c2 = a pow 2 * c1 + b * a * c2`;REAL_ARITH `!a b:real. a - b = a + --b`] THEN 
    MATCH_MP_TAC (REAL_FIELD `!a b c d:real. ~(d = &0) /\ ~(a = --c) ==> ~(a * d + b = b + --(c * d))`) THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[COS_POS_PI;REAL_ARITH `!x. &0 < x ==> ~(x = &0)`];
    ALL_TAC] THEN 
    UNDISCH_TAC `~(t7 pow 2 + t8 pow 2 = &0)` THEN 
    ASM_SIMP_TAC[REAL_ARITH ` ~(a + b = &0) ==> ~(a = --b)`];
    ALL_TAC] THEN
    SUBGOAL_THEN `~(t7 * (t7 * cos a2 + t8 * sin a2) - t8 * (t7 * sin a2 - t8 * cos a2) = &0)` ASSUME_TAC THENL [POP_ASSUM MP_TAC THEN 
    ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0)        
                ==> (a / b) * (c / d) = (a * c) / (b * d)`;
                REAL_FIELD `!a b c d:real. ~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0) ==> a / b + c / d = 
                (a * d + b * c) / (b * d)`;REAL_FIELD `~(b = &0) ==> 
                &1 - a / b = (b - a) / b`] THEN 
    ASM_SIMP_TAC[REAL_FIELD `~(a = &0) /\ ~(((a - b) / a) = &0)
                ==> ~((a - b) = &0)`];ALL_TAC] THEN 
    SUBGOAL_THEN `tan(a2) = ((t8 / t7) + ((t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))) / (&1 - ((t8 / t7) * ((t7 * sin a2 - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0)   
                 ==> (a / b) * (c / d) = (a * c) / (b * d)`;
                 REAL_FIELD `!a b c d:real. ~(b = &0) /\ ~(d = &0) /\ ~(b * d = &0) ==> a / b + c / d = (a * d + b * c) / (b * d)`;REAL_FIELD `~(b = &0) ==> &1 - a / b = (b - a) / b`;REAL_FIELD `!x y z:real. ~(y = &0) /\ ~(z = &0) ==> x / z / (y / z) = x / y`] THEN 
    SIMP_TAC[REAL_ADD_LDISTRIB;REAL_SUB_LDISTRIB;REAL_MUL_ASSOC;
            GSYM REAL_POW_2] THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC;GSYM REAL_ADD_ASSOC;
            REAL_ARITH `!a b c1 c2:real. a * b * c1 + a pow 2 * c2 + b pow 2 * c2 - b * a * c1 = (b pow 2  + a pow 2) * c2`;
            REAL_ARITH `!a b c1 c2:real. 
            (b pow 2 * c1 + b * a * c2) - (a * b * c2 - a pow 2 * c1) = (b pow 2  + a pow 2) * c1`] THEN 
    ASM_SIMP_TAC[REAL_FIELD `!x y z:real. ~(z = &0) ==> 
                (z * x) / (z * y) = x / y`;tan];ALL_TAC] THEN    
    MP_TAC (ISPECL[`atn ((t8:real) / (t7:real)) `;
    `atn ((t7 * sin (a2:real) - t8 * cos a2) / (t7 * cos a2 + t8 * sin a2))`] TAN_ADD) THEN 
    POP_ASSUM MP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[ATN_TAN] THEN 
    STRIP_TAC THEN ANTS_TAC THENL [CONJ_TAC THENL[
    SIMP_TAC[COS_ZERO_PI;DE_MORGAN_THM;NOT_EXISTS_THM] THEN 
    CONJ_TAC THENL[GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(x = y)`) THEN ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 < (&(n:num) + &1 / &2) * pi` 
    ASSUME_TAC THENL[
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x y:real. &0 < y ==> x < y + x`;
                PI_POS];ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_ARITH `&1 / &2 * x                   
                 = x / &2`;REAL_LT_TRANS];ALL_TAC] THEN 
    GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(y = x)`) THEN 
    ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN 
    SUBGOAL_THEN `--((&(n:num) + &1 / &2) * pi) < --(pi / &2)` ASSUME_TAC THENL[SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`;
                             REAL_NEG_LMUL] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN SIMP_TAC[PI_POS] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_NEG_ADD] THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. -- x < --y ==> y < x`) THEN ASM_SIMP_TAC[GSYM REAL_NEG_ADD;REAL_NEG_NEG;
                REAL_ARITH `!x y:real. &0 < y ==> x < y + x`];
    ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;
                    REAL_ARITH `&1 / &2 * x = x / &2`;
                    REAL_LT_TRANS];ALL_TAC] THEN 
    CONJ_TAC THENL
    [SIMP_TAC[COS_ZERO_PI;DE_MORGAN_THM;NOT_EXISTS_THM] THEN 
    CONJ_TAC THENL [GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(x = y)`) THEN ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 < (&(n:num) + &1 / &2) * pi` 
    ASSUME_TAC THENL
    [POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x y:real. &0 < y ==> x < y + x`;PI_POS];
    ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(y = x)`) THEN 
    ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN 
    SUBGOAL_THEN `--((&(n:num) + &1 / &2) * pi) < --(pi / &2)` ASSUME_TAC THENL[SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`;
                             REAL_NEG_LMUL] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN SIMP_TAC[PI_POS] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN 
    SIMP_TAC[REAL_NEG_ADD] THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. -- x < --y ==> y < x`) THEN ASM_SIMP_TAC[GSYM REAL_NEG_ADD;REAL_NEG_NEG;REAL_ARITH `!x y:real.          
                &0 < y ==> x < y + x`];ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    SIMP_TAC[COS_ZERO_PI;DE_MORGAN_THM;NOT_EXISTS_THM] THEN 
    CONJ_TAC THENL [GEN_TAC THEN MATCH_MP_TAC (REAL_ARITH `!x y:real.
    x < y ==> ~(x = y)`) THEN ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 < (&(n:num) + &1 / &2) * pi` 
    ASSUME_TAC THENL [POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN 
    ASM_SIMP_TAC[REAL_ARITH `!x y:real. &0 < y ==> x < y + x`;PI_POS];
    ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    GEN_TAC THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. x < y ==> ~(y = x)`) THEN 
    ASM_CASES_TAC `&n = &0` THENL
    [ASM_SIMP_TAC[REAL_ADD_LID;REAL_MUL_LZERO;REAL_ADD_RDISTRIB;
                 ATN_BOUNDS;REAL_ARITH `&1 / &2 * x = x / &2`];
    ALL_TAC] THEN 
    SUBGOAL_THEN `--((&(n:num) + &1 / &2) * pi) < --(pi / &2)` ASSUME_TAC THENL
    [SIMP_TAC[REAL_ARITH `pi / &2 = &1 / &2 * pi`;REAL_NEG_LMUL] THEN 
    MATCH_MP_TAC REAL_LT_RMUL THEN SIMP_TAC[PI_POS] THEN 
    POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `~(&(n:num) = &0) <=> &0 < &n`] THEN 
    STRIP_TAC THEN SIMP_TAC[REAL_NEG_ADD] THEN 
    MATCH_MP_TAC (REAL_ARITH `!x y:real. -- x < --y ==> y < x`) THEN ASM_SIMP_TAC[GSYM REAL_NEG_ADD;REAL_NEG_NEG;REAL_ARITH `!x y:real.             
                &0 < y ==> x < y + x`];ALL_TAC] THEN 
    ASM_MESON_TAC[REAL_ADD_RDISTRIB;ATN_BOUNDS;REAL_LT_TRANS;
                 REAL_ARITH `&1 / &2 * x = x / &2`];ALL_TAC] THEN 
    DISCH_THEN(MP_TAC o AP_TERM `atn`) THEN ASM_SIMP_TAC[TAN_ATN]; 
    UNDISCH_TAC `--((c3:real) * sin ((a2:real) + a3)) - (c2:real) * sin (a2:real) = (t7:real)` THEN     
    UNDISCH_TAC `(c3:real) * cos ((a2:real) + (a3:real)) + (c2:real) * cos a2 = (t8:real)` THEN 
    SIMP_TAC[REAL_ARITH `!a b c:real. a + b = c <=> a = c - b`;
            REAL_ARITH `!a b c:real. --a - b = c <=> a = --(b + c)`;
            GSYM REAL_MUL_LNEG] THEN 
    ASM_SIMP_TAC[REAL_ARITH `!a b c:real. a = c - b <=> a + b = c`;
                REAL_FIELD `!a b c. ~(a = &0) ==> (a * b = c <=>
                b = c / a)`;REAL_FIELD `!a b c. ~(a = &0) ==> ( -- a * b = c <=> b = -- c / a)`] THEN 
    DISCH_THEN(MP_TAC o SYM) THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN STRIP_TAC THEN 
    ASM_SIMP_TAC[GSYM tan;TAN_ATN]]);;


let REAL_ABS_REFL_NEG = prove
 (`!x. x < &0 ==> (abs(x) = --x)`,
  REAL_ARITH_TAC);;

let VEC3_LMUL_SELF = prove
    (`!a:real^3. (norm a = &1) ==> vec3_vtrans a ** a = a`,
    GEN_TAC THEN
    SIMP_TAC [NORM_EQ_1;dot;vec3_vtrans;matrix_vector_mul;CART_EQ; LAMBDA_BETA;VECTOR_3;DIMINDEX_3;SUM_3;FORALL_3] THEN
    SIMP_TAC[GSYM REAL_MUL_ASSOC;GSYM REAL_ADD_LDISTRIB;REAL_MUL_RID] THEN 
    SIMP_TAC[REAL_ARITH `x * y * x = y * x * x`;GSYM REAL_ADD_LDISTRIB;REAL_MUL_RID]);;

let POW_2_SQRT_NEG = prove
 (`!x. x < &0 ==> sqrt(x pow 2) = --x`,
  MESON_TAC[REAL_ARITH `x < &0<=> &0 < --x`;REAL_ARITH `x pow 2 = --x pow 2`;SQRT_UNIQUE;REAL_LE_LT]);;

let PADEN_KAHAN_SUB_PRO_2 = prove
    (`!w1 w2 r u u' v v' p q c z:real^3 a a1 a2 x1 x2 x3:real s1 s2:screw.
    (--(pi / &2) < a /\ a < pi / &2) /\
    (--(pi / &2) < a1 /\ a1 < pi / &2) /\
    (--(pi / &2) < a2 /\ a2 < pi / &2) /\
    s1 = (w1, r cross (w1)) /\ s2 = (w2, r cross (w2)) /\
    norm w1 = &1 /\ norm w2 = &1 /\
    u = p - r /\ v = q - r /\ z = c - r /\
    u' = u - (vec3_vtrans (FST s2) ** u) /\
    v' = v - (vec3_vtrans (FST s1) ** v) /\ 
    z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2) /\
    (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * (w1 dot w2) + (x3 pow 2) * (norm(w1 cross w2)) pow 2 /\ 
    ~((norm(w1 cross w2)) pow 2  = &0) /\ ~((w1 dot w2) pow 2 - &1 = &0) /\
    matrix_exp(a1 %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point c)) /\
    matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
    matrix_exp(a1 %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point q)) /\ 
    a = a1 + a2 /\ ~(u' = vec 0) /\ ~(v' = vec 0) ==>
    ((&0 <= x3) ==> (a = --atn ((w1 dot (v' cross
           ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
             ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
             sqrt ((norm u pow 2 -(((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)) -
            vec3_vtrans w1 ** (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) %  w1 +
             ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
             sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) %
             (w1 cross w2))))) / (v' dot ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
            ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 + sqrt ((norm u pow 2 -
              (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
               ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)) -
           vec3_vtrans w1 ** (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
            ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
            sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
               ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) *
              (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2))))) + 
     atn ((w2 dot (u' cross ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
          ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
          sqrt((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
           norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
         (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
          ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
          sqrt ((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
           norm (w1 cross w2) pow 2) % (w1 cross w2))))) /
       (u' dot ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
         ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
         sqrt ((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
          norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
        (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
         ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
         sqrt ((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
          norm (w1 cross w2) pow 2) % (w1 cross w2))))))) /\ 
    ((x3 < &0) ==> (a = --atn((w1 dot(v' cross
                              ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                             sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                             ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) %
                              (w1 cross w2)) - vec3_vtrans w1 **
                              (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                              sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2))))) / (v' dot
                              ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                              sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)) -
                              vec3_vtrans w1 ** (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                              sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2))))) + 
                              atn((w2 dot (u' cross
                               ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                               ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                               sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                              norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
                              (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                            sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                             ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                             ((w1 dot w2) pow 2 - &1)) pow 2 -  (&2 *
                             ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                             ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                             norm (w1 cross w2) pow 2) % (w1 cross w2))))) / (u' dot
                            ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                            ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                           sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                           (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                           (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                           ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                           norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
                           (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                           ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                          sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                          (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                           (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                           ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)))))))`,
    REPEAT STRIP_TAC THENL    
    [SUBGOAL_THEN `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` ASSUME_TAC THENL 
    [UNDISCH_TAC `matrix_exp ((a2:real) %% screw_2_matrix s2) ** 
                   homo_point (mk_point (p:real^3)) = 
                   homo_point (mk_point (c:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `z:real^3 = c - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`]  THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a2 %% screw_2_matrix s2) ** homo_point 
                            (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y = z`;VECTOR_ARITH `(a:real^3 = b + a - c) <=> (vec 0 = b - c)`];ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point (r:real^3))) = 
                              (homo_point (mk_point r))` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a2:real) %% screw_2_matrix s2) ** homo_point 
                             (mk_point (r:real^3)) = homo_point (mk_point r)` THEN 
    UNDISCH_TAC `matrix_exp ((a1:real) %% screw_2_matrix s1) ** homo_point 
                            (mk_point (r:real^3)) = homo_point (mk_point r)` THEN
    SIMP_TAC[];ALL_TAC] THEN  
    SUBGOAL_THEN `invertible (matrix_exp ((a1:real) %% vec3_2_ssm (w1:real^3)))` ASSUME_TAC THENL
    [SIMP_TAC[INVERTIBLE_MATRIX_EXP];ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = 
                               matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3)` ASSUME_TAC THENL
    [SIMP_TAC[GSYM MATRIX_EXP_INV] THEN 
    UNDISCH_TAC `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point (p:real^3))) = 
                             (homo_point (mk_point q))` THEN 
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point (r:real^3))) = 
                              (homo_point (mk_point r))`  THEN 
    UNDISCH_TAC `norm (w1:real^3) = &1` THEN UNDISCH_TAC `norm (w2:real^3) = &1` THEN 
    UNDISCH_TAC `(s1:screw) = ((w1:real^3), (r:real^3) cross (w1))` THEN 
    UNDISCH_TAC `(s2:screw) = ((w2:real^3), (r:real^3) cross (w2))` THEN
    SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB;GSYM VECTOR_ADD_ASSOC] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `(a:real^3) + b + c + d + e + f= b + (a + c + d + e + f)`] THEN 
    SIMP_TAC[VECTOR_ARITH `!x y z:real^3. (x + y = y + z) <=> (x = z)`] THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN 
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC;MATRIX_INV;MATRIX_MUL_LID];ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3) = (z:real^3)` ASSUME_TAC THENL   
    [POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN
    UNDISCH_TAC `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` THEN 
    SIMP_TAC[];ALL_TAC] THEN 
    SUBGOAL_THEN `(w2:real^3) dot (u:real^3) = w2 dot (z:real^3)` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` THEN  
    DISCH_THEN(MP_TAC o SYM) THEN
    SIMP_TAC[ARITH_RULE `!a b c:real^3. (a dot b = a dot c) <=> (a dot b - a dot c = &0)`;GSYM DOT_RSUB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w2:real^3) = &1` THEN SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN 
    SIMP_TAC[DOT_RSUB;MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_RMUL;DOT_SSM_RMUL;REAL_MUL_RZERO;REAL_ADD_LID;
                    GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_EQ_VEC3;VEC3_LMUL_SELF] THEN ARITH_TAC;ALL_TAC] THEN 
   SUBGOAL_THEN `(w1:real^3) dot (v:real^3) = w1 dot (z:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3) = (z:real^3)` THEN 
    DISCH_THEN(MP_TAC o SYM) THEN
    SIMP_TAC[GSYM MATRIX_CMUL_LNEG;ARITH_RULE `!a b c:real^3. (a dot b = a dot c) <=> (a dot b - a dot c = &0)`;GSYM DOT_RSUB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w1:real^3) = &1` THEN 
    MP_TAC(ISPECL [`(w1:real^3)`;`(--a1:real)`] RODRIGUES_FORMULA_ALT) THEN 
    SIMP_TAC[DOT_RSUB;MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_RMUL;DOT_SSM_RMUL;REAL_MUL_RZERO;REAL_ADD_LID;
                    GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_EQ_VEC3;VEC3_LMUL_SELF] THEN ARITH_TAC;ALL_TAC] THEN 
   SUBGOAL_THEN `(norm (u:real^3)) pow 2 = (norm (z:real^3)) pow 2` ASSUME_TAC THENL
   [SIMP_TAC[NORM_POW_2] THEN UNDISCH_TAC `norm (w2:real^3) = &1` THEN
    UNDISCH_TAC `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` THEN  
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN STRIP_TAC THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_LSUB;DOT_LADD] THEN 
    SIMP_TAC[DOT_RMUL;DOT_LMUL;REAL_MUL_ASSOC;GSYM REAL_POW_2;DOT_SSM_RMUL_SELF;DOT_SSM_LMUL_SELF;REAL_MUL_RZERO;
                    GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC;TRANSP_EQ_NEG_SSM;TRANSP_VEC3_RMUL_SELF;TRANSP_EQ_VEC3;
                    SSM_LMUL_EQ_0;SSM_RMUL_EQ_0;MATRIX_MUL_LNEG;MATRIX_VECTOR_MUL_LZERO;MATRIX_NEG_0;
                    REAL_NEG_0;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_LZERO;DOT_LZERO] THEN 
    SIMP_TAC[GSYM MATRIX_POW_2;SSM_POW_2;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
                    MATRIX_VECTOR_MUL_LNEG;VECTOR_NEG_SUB;DOT_LSUB;REAL_SUB_LDISTRIB] THEN 
    SIMP_TAC[REAL_ARITH `((a:real) + b - c) + d - e + (b + f - b) - (c + b - c) = (d + a) - (e + c) + f`;
                    GSYM REAL_ADD_RDISTRIB;SIN_CIRCLE;REAL_MUL_LID;REAL_ARITH ` (x:real) - y + y = x`];ALL_TAC] THEN
   SUBGOAL_THEN `(norm (v:real^3)) pow 2 = (norm (z:real^3)) pow 2` ASSUME_TAC THENL
   [SIMP_TAC[NORM_POW_2] THEN UNDISCH_TAC `norm (w1:real^3) = &1` THEN
    UNDISCH_TAC `matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3) = (z:real^3)` THEN  
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM MATRIX_CMUL_LNEG] THEN 
    MP_TAC(ISPECL [`(w1:real^3)`;`(--a1:real)`] RODRIGUES_FORMULA_ALT) THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_LSUB;DOT_LADD] THEN 
    SIMP_TAC[DOT_RMUL;DOT_LMUL;REAL_MUL_ASSOC;GSYM REAL_POW_2;DOT_SSM_RMUL_SELF;DOT_SSM_LMUL_SELF;REAL_MUL_RZERO;
                    GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC;TRANSP_EQ_NEG_SSM;TRANSP_VEC3_RMUL_SELF;TRANSP_EQ_VEC3;
                    SSM_LMUL_EQ_0;SSM_RMUL_EQ_0;MATRIX_MUL_LNEG;MATRIX_VECTOR_MUL_LZERO;MATRIX_NEG_0;
                    REAL_NEG_0;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_LZERO;DOT_LZERO] THEN 
    SIMP_TAC[GSYM MATRIX_POW_2;SSM_POW_2;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
                    MATRIX_VECTOR_MUL_LNEG;VECTOR_NEG_SUB;DOT_LSUB;REAL_SUB_LDISTRIB] THEN 
    SIMP_TAC[REAL_ARITH `((a:real) + b - c) + d - e + (b + f - b) - (c + b - c) = (d + a) - (e + c) + f`;
                    GSYM REAL_ADD_RDISTRIB;SIN_CIRCLE;REAL_MUL_LID;REAL_ARITH ` (x:real) - y + y = x`];ALL_TAC] THEN
   SUBGOAL_THEN `(w2:real^3) dot (u:real^3) = (x1:real) * (w2 dot w1) + (x2:real)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w2:real^3) dot (u:real^3) = w2 dot (z:real^3)` THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `norm (w2:real^3) = &1` THEN 
    SIMP_TAC[DOT_RADD;DOT_RMUL;DOT_CROSS_SELF;REAL_MUL_RZERO;REAL_ADD_RID;GSYM NORM_POW_2;
                    REAL_POW_ONE;REAL_MUL_RID];ALL_TAC] THEN
   SUBGOAL_THEN `(w1:real^3) dot (v:real^3) = (x1:real) + (x2:real) * (w1 dot w2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w1:real^3) dot (v:real^3) = w1 dot (z:real^3)` THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `norm (w1:real^3) = &1` THEN 
    SIMP_TAC[DOT_RADD;DOT_RMUL;DOT_CROSS_SELF;REAL_MUL_RZERO;REAL_ADD_RID;GSYM NORM_POW_2;
                    REAL_POW_ONE;REAL_MUL_RID];ALL_TAC] THEN
   SUBGOAL_THEN `(x1:real) = (((w1:real^3) dot (w2:real^3)) * (w2 dot (u:real^3)) - w1 dot (v:real^3))/((w1 dot w2) pow 2 - &1)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[REAL_ARITH `(a:real) = b + c <=> c = a - b`;REAL_SUB_RDISTRIB] THEN 
    STRIP_TAC THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC;DOT_SYM;GSYM REAL_POW_2;REAL_ARITH `(a:real) - b = c - d <=> a - c = b - d`] THEN
    UNDISCH_TAC `~(((w1:real^3) dot w2) pow 2 - &1 = &0)` THEN 
    SIMP_TAC[REAL_ARITH `!a b:real. a * b - a = a * (b - &1)`;REAL_FIELD `!a b c. ~(c = &0) ==> ( a = b * c <=> b = a / c)`;REAL_MUL_SYM];ALL_TAC] THEN
   SUBGOAL_THEN `(x2:real) = (((w1:real^3) dot (w2:real^3)) * (w1 dot (v:real^3)) - w2 dot (u:real^3))/((w1 dot w2) pow 2 - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w2:real^3) dot (u:real^3) = (x1:real) * (w2 dot w1) + (x2:real)` THEN
    UNDISCH_TAC `(w1:real^3) dot (v:real^3) = (x1:real) + (x2:real) * (w1 dot w2)` THEN
    SIMP_TAC[REAL_ARITH `(a:real) = b + c <=> b = a - c`;REAL_SUB_RDISTRIB] THEN 
    STRIP_TAC THEN     
    SIMP_TAC[GSYM REAL_MUL_ASSOC;DOT_SYM;GSYM REAL_POW_2;REAL_ARITH `(a:real) - b = c - d <=> a - c = b - d`] THEN
    UNDISCH_TAC `~(((w1:real^3) dot w2) pow 2 - &1 = &0)` THEN 
    SIMP_TAC[REAL_ARITH `!a b:real. a * b - a = a * (b - &1)`;REAL_FIELD `!a b c. ~(c = &0) ==> ( a = b * c <=> b = a / c)`;REAL_MUL_SYM];ALL_TAC] THEN
   SUBGOAL_THEN `(x3:real) = 
   sqrt(((norm (u:real^3)) pow 2 - (x1:real) pow 2 - (x2:real) pow 2 - (&2 * x1 * x2) * ((w1:real^3) dot w2)) /((norm(w1 cross w2)) pow 2))` ASSUME_TAC THENL
   [UNDISCH_TAC `(norm (z:real^3)) pow 2 = (x1:real) pow 2 + (x2:real) pow 2 + (&2 * x1 * x2) * ((w1:real^3) dot w2) + ((x3:real) pow 2) * (norm(w1 cross w2)) pow 2` THEN
    UNDISCH_TAC `(norm (u:real^3)) pow 2 = (norm (z:real^3)) pow 2` THEN
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[REAL_ARITH `!a b c d e:real. a = b + c + d + e <=> e = a - b - c - d`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((norm((w1:real^3) cross w2)) pow 2  = &0)` THEN 
    SIMP_TAC[REAL_FIELD `!a b c. ~(b = &0) ==> ( a * b = c <=> a = c / b)`] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `&0 <= (x3:real)` THEN
    SIMP_TAC[GSYM POW_2_SQRT];ALL_TAC] THEN
    ABBREV_TAC `z1= (z:real^3) - (vec3_vtrans (FST (s1:screw)) ** z)` THEN
    ABBREV_TAC `z2= (z:real^3) - (vec3_vtrans (FST (s2:screw)) ** z)` THEN   
    SUBGOAL_THEN `(a2:real) = atn
     ((w2 dot (u' cross ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
          ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
          sqrt((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
           norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
         (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
          ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
          sqrt ((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
           norm (w1 cross w2) pow 2) % (w1 cross w2))))) /
       (u' dot ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
         ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
         sqrt ((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
          norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
        (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
         ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
         sqrt ((norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * (w1 dot w2)) /
          norm (w1 cross w2) pow 2) % (w1 cross w2))))) ` ASSUME_TAC THENL
    [MP_TAC(ISPECL[`w2:real^3`;`r:real^3`;`u:real^3`;`u':real^3`;`z:real^3`;` z2:real^3`;`p:real^3`;`c:real^3`;`s2:screw`;`a2:real`] 
                    PADEN_KAHAN_SUB_PRO_1) THEN 
    ANTS_TAC THENL
    [ASM_SIMP_TAC[];ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) - (vec3_vtrans (FST (s2:screw)) ** z) = z2` THEN DISCH_THEN(MP_TAC o SYM) THEN 
    UNDISCH_TAC `(s2:screw) = ((w2:real^3), (r:real^3) cross (w2)) ` THEN
    SIMP_TAC[FST] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `(x1:real) = (((w1:real^3) dot (w2:real^3)) * (w2 dot (u:real^3)) - w1 dot (v:real^3))/((w1 dot w2) pow 2 - &1)` THEN
    UNDISCH_TAC `(x2:real) = (((w1:real^3) dot (w2:real^3)) * (w1 dot (v:real^3)) - w2 dot (u:real^3))/((w1 dot w2) pow 2 - &1)` THEN    
    UNDISCH_TAC `(x3:real) = sqrt(((norm (u:real^3)) pow 2 - (x1:real) pow 2 - 
                               (x2:real) pow 2 - (&2 * x1 * x2) * ((w1:real^3) dot w2)) /((norm(w1 cross w2)) pow 2))` THEN
    SIMP_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN `(a1:real) = --atn ((w1 dot (v' cross
           ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
             ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
             sqrt ((norm u pow 2 -(((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)) -
            vec3_vtrans w1 ** (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) %  w1 +
             ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
             sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) %
             (w1 cross w2))))) / (v' dot ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
            ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 + sqrt ((norm u pow 2 -
              (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
               ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)) -
           vec3_vtrans w1 ** (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
            ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 +
            sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
              (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
               ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) *
              (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)))))` ASSUME_TAC THENL
    [MP_TAC(ISPECL[`w1:real^3`;`r:real^3`;`v:real^3`;`v':real^3`;`z:real^3`;` z1:real^3`;`q:real^3`;`c:real^3`;`s1:screw`;`--a1:real`] 
                    PADEN_KAHAN_SUB_PRO_1) THEN 
    SIMP_TAC[REAL_ARITH `--(a:real) = b <=> a = --b`] THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC
    [REAL_ARITH `--(pi / &2) < --a1 /\ --a1 < pi / &2 <=> --(pi / &2) < a1 /\ a1 < pi / &2`];ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) = c - r` THEN DISCH_THEN(MP_TAC o SYM) THEN 
    UNDISCH_TAC `(v:real^3) = q - r` THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `(v':real^3) = v - vec3_vtrans (FST (s1:screw)) ** v` THEN
    DISCH_THEN(MP_TAC o SYM) THEN 
    UNDISCH_TAC `(s1:screw) = ((w1:real^3), (r:real^3) cross (w1)) ` THEN
    SIMP_TAC[FST] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `(x1:real) = (((w1:real^3) dot (w2:real^3)) * (w2 dot (u:real^3)) - w1 dot (v:real^3))/((w1 dot w2) pow 2 - &1)` THEN
    UNDISCH_TAC `(x2:real) = (((w1:real^3) dot (w2:real^3)) * (w1 dot (v:real^3)) - w2 dot (u:real^3))/((w1 dot w2) pow 2 - &1)` THEN    
    UNDISCH_TAC `(x3:real) = sqrt(((norm (u:real^3)) pow 2 - (x1:real) pow 2 - 
                               (x2:real) pow 2 - (&2 * x1 * x2) * ((w1:real^3) dot w2)) /((norm(w1 cross w2)) pow 2))` THEN
    SIMP_TAC[];ALL_TAC] THEN
    UNDISCH_TAC `(a:real) = a1 + a2` THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[];
    SUBGOAL_THEN `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` ASSUME_TAC THENL 
    [UNDISCH_TAC `matrix_exp ((a2:real) %% screw_2_matrix s2) ** 
                   homo_point (mk_point (p:real^3)) = 
                   homo_point (mk_point (c:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `z:real^3 = c - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`]  THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a2 %% screw_2_matrix s2) ** homo_point 
                            (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y = z`;VECTOR_ARITH `(a:real^3 = b + a - c) <=> (vec 0 = b - c)`];ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point (r:real^3))) = 
                              (homo_point (mk_point r))` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a2:real) %% screw_2_matrix s2) ** homo_point 
                             (mk_point (r:real^3)) = homo_point (mk_point r)` THEN 
    UNDISCH_TAC `matrix_exp ((a1:real) %% screw_2_matrix s1) ** homo_point 
                            (mk_point (r:real^3)) = homo_point (mk_point r)` THEN
    SIMP_TAC[];ALL_TAC] THEN  
    SUBGOAL_THEN `invertible (matrix_exp ((a1:real) %% vec3_2_ssm (w1:real^3)))` ASSUME_TAC THENL
    [SIMP_TAC[INVERTIBLE_MATRIX_EXP];ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = 
                               matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3)` ASSUME_TAC THENL
    [SIMP_TAC[GSYM MATRIX_EXP_INV] THEN 
    UNDISCH_TAC `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point (p:real^3))) = 
                             (homo_point (mk_point q))` THEN 
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point (r:real^3))) = 
                              (homo_point (mk_point r))`  THEN 
    UNDISCH_TAC `norm (w1:real^3) = &1` THEN UNDISCH_TAC `norm (w2:real^3) = &1` THEN 
    UNDISCH_TAC `(s1:screw) = ((w1:real^3), (r:real^3) cross (w1))` THEN 
    UNDISCH_TAC `(s2:screw) = ((w2:real^3), (r:real^3) cross (w2))` THEN
    SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB;GSYM VECTOR_ADD_ASSOC] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `(a:real^3) + b + c + d + e + f= b + (a + c + d + e + f)`] THEN 
    SIMP_TAC[VECTOR_ARITH `!x y z:real^3. (x + y = y + z) <=> (x = z)`] THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN 
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC;MATRIX_INV;MATRIX_MUL_LID];ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3) = (z:real^3)` ASSUME_TAC THENL   
    [POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN
    UNDISCH_TAC `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` THEN 
    SIMP_TAC[];ALL_TAC] THEN 
    SUBGOAL_THEN `(w2:real^3) dot (u:real^3) = w2 dot (z:real^3)` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` THEN  
    DISCH_THEN(MP_TAC o SYM) THEN
    SIMP_TAC[ARITH_RULE `!a b c:real^3. (a dot b = a dot c) <=> (a dot b - a dot c = &0)`;GSYM DOT_RSUB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w2:real^3) = &1` THEN SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN 
    SIMP_TAC[DOT_RSUB;MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_RMUL;DOT_SSM_RMUL;REAL_MUL_RZERO;REAL_ADD_LID;
                    GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_EQ_VEC3;VEC3_LMUL_SELF] THEN ARITH_TAC;ALL_TAC] THEN 
   SUBGOAL_THEN `(w1:real^3) dot (v:real^3) = w1 dot (z:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3) = (z:real^3)` THEN 
    DISCH_THEN(MP_TAC o SYM) THEN
    SIMP_TAC[GSYM MATRIX_CMUL_LNEG;ARITH_RULE `!a b c:real^3. (a dot b = a dot c) <=> (a dot b - a dot c = &0)`;GSYM DOT_RSUB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w1:real^3) = &1` THEN 
    MP_TAC(ISPECL [`(w1:real^3)`;`(--a1:real)`] RODRIGUES_FORMULA_ALT) THEN 
    SIMP_TAC[DOT_RSUB;MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_RMUL;DOT_SSM_RMUL;REAL_MUL_RZERO;REAL_ADD_LID;
                    GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_EQ_VEC3;VEC3_LMUL_SELF] THEN ARITH_TAC;ALL_TAC] THEN 
   SUBGOAL_THEN `(norm (u:real^3)) pow 2 = (norm (z:real^3)) pow 2` ASSUME_TAC THENL
   [SIMP_TAC[NORM_POW_2] THEN UNDISCH_TAC `norm (w2:real^3) = &1` THEN
    UNDISCH_TAC `matrix_exp ((a2:real) %% vec3_2_ssm w2) ** (u:real^3) = (z:real^3)` THEN  
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN STRIP_TAC THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_LSUB;DOT_LADD] THEN 
    SIMP_TAC[DOT_RMUL;DOT_LMUL;REAL_MUL_ASSOC;GSYM REAL_POW_2;DOT_SSM_RMUL_SELF;DOT_SSM_LMUL_SELF;REAL_MUL_RZERO;
                    GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC;TRANSP_EQ_NEG_SSM;TRANSP_VEC3_RMUL_SELF;TRANSP_EQ_VEC3;
                    SSM_LMUL_EQ_0;SSM_RMUL_EQ_0;MATRIX_MUL_LNEG;MATRIX_VECTOR_MUL_LZERO;MATRIX_NEG_0;
                    REAL_NEG_0;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_LZERO;DOT_LZERO] THEN 
    SIMP_TAC[GSYM MATRIX_POW_2;SSM_POW_2;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
                    MATRIX_VECTOR_MUL_LNEG;VECTOR_NEG_SUB;DOT_LSUB;REAL_SUB_LDISTRIB] THEN 
    SIMP_TAC[REAL_ARITH `((a:real) + b - c) + d - e + (b + f - b) - (c + b - c) = (d + a) - (e + c) + f`;
                    GSYM REAL_ADD_RDISTRIB;SIN_CIRCLE;REAL_MUL_LID;REAL_ARITH ` (x:real) - y + y = x`];ALL_TAC] THEN
   SUBGOAL_THEN `(norm (v:real^3)) pow 2 = (norm (z:real^3)) pow 2` ASSUME_TAC THENL
   [SIMP_TAC[NORM_POW_2] THEN UNDISCH_TAC `norm (w1:real^3) = &1` THEN
    UNDISCH_TAC `matrix_exp(--((a1:real) %% vec3_2_ssm w1)) ** (v:real^3) = (z:real^3)` THEN  
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM MATRIX_CMUL_LNEG] THEN 
    MP_TAC(ISPECL [`(w1:real^3)`;`(--a1:real)`] RODRIGUES_FORMULA_ALT) THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[DOT_RSUB;DOT_RADD;DOT_LSUB;DOT_LADD] THEN 
    SIMP_TAC[DOT_RMUL;DOT_LMUL;REAL_MUL_ASSOC;GSYM REAL_POW_2;DOT_SSM_RMUL_SELF;DOT_SSM_LMUL_SELF;REAL_MUL_RZERO;
                    GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC;TRANSP_EQ_NEG_SSM;TRANSP_VEC3_RMUL_SELF;TRANSP_EQ_VEC3;
                    SSM_LMUL_EQ_0;SSM_RMUL_EQ_0;MATRIX_MUL_LNEG;MATRIX_VECTOR_MUL_LZERO;MATRIX_NEG_0;
                    REAL_NEG_0;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_LZERO;DOT_LZERO] THEN 
    SIMP_TAC[GSYM MATRIX_POW_2;SSM_POW_2;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;
                    MATRIX_VECTOR_MUL_LNEG;VECTOR_NEG_SUB;DOT_LSUB;REAL_SUB_LDISTRIB] THEN 
    SIMP_TAC[REAL_ARITH `((a:real) + b - c) + d - e + (b + f - b) - (c + b - c) = (d + a) - (e + c) + f`;
                    GSYM REAL_ADD_RDISTRIB;SIN_CIRCLE;REAL_MUL_LID;REAL_ARITH ` (x:real) - y + y = x`];ALL_TAC] THEN
   SUBGOAL_THEN `(w2:real^3) dot (u:real^3) = (x1:real) * (w2 dot w1) + (x2:real)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w2:real^3) dot (u:real^3) = w2 dot (z:real^3)` THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `norm (w2:real^3) = &1` THEN 
    SIMP_TAC[DOT_RADD;DOT_RMUL;DOT_CROSS_SELF;REAL_MUL_RZERO;REAL_ADD_RID;GSYM NORM_POW_2;
                    REAL_POW_ONE;REAL_MUL_RID];ALL_TAC] THEN
   SUBGOAL_THEN `(w1:real^3) dot (v:real^3) = (x1:real) + (x2:real) * (w1 dot w2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w1:real^3) dot (v:real^3) = w1 dot (z:real^3)` THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `norm (w1:real^3) = &1` THEN 
    SIMP_TAC[DOT_RADD;DOT_RMUL;DOT_CROSS_SELF;REAL_MUL_RZERO;REAL_ADD_RID;GSYM NORM_POW_2;
                    REAL_POW_ONE;REAL_MUL_RID];ALL_TAC] THEN
   SUBGOAL_THEN `(x1:real) = (((w1:real^3) dot (w2:real^3)) * (w2 dot (u:real^3)) - w1 dot (v:real^3))/((w1 dot w2) pow 2 - &1)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[REAL_ARITH `(a:real) = b + c <=> c = a - b`;REAL_SUB_RDISTRIB] THEN 
    STRIP_TAC THEN 
    SIMP_TAC[GSYM REAL_MUL_ASSOC;DOT_SYM;GSYM REAL_POW_2;REAL_ARITH `(a:real) - b = c - d <=> a - c = b - d`] THEN
    UNDISCH_TAC `~(((w1:real^3) dot w2) pow 2 - &1 = &0)` THEN 
    SIMP_TAC[REAL_ARITH `!a b:real. a * b - a = a * (b - &1)`;REAL_FIELD `!a b c. ~(c = &0) ==> ( a = b * c <=> b = a / c)`;REAL_MUL_SYM];ALL_TAC] THEN
   SUBGOAL_THEN `(x2:real) = (((w1:real^3) dot (w2:real^3)) * (w1 dot (v:real^3)) - w2 dot (u:real^3))/((w1 dot w2) pow 2 - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w2:real^3) dot (u:real^3) = (x1:real) * (w2 dot w1) + (x2:real)` THEN
    UNDISCH_TAC `(w1:real^3) dot (v:real^3) = (x1:real) + (x2:real) * (w1 dot w2)` THEN
    SIMP_TAC[REAL_ARITH `(a:real) = b + c <=> b = a - c`;REAL_SUB_RDISTRIB] THEN 
    STRIP_TAC THEN     
    SIMP_TAC[GSYM REAL_MUL_ASSOC;DOT_SYM;GSYM REAL_POW_2;REAL_ARITH `(a:real) - b = c - d <=> a - c = b - d`] THEN
    UNDISCH_TAC `~(((w1:real^3) dot w2) pow 2 - &1 = &0)` THEN 
    SIMP_TAC[REAL_ARITH `!a b:real. a * b - a = a * (b - &1)`;REAL_FIELD `!a b c. ~(c = &0) ==> ( a = b * c <=> b = a / c)`;REAL_MUL_SYM];ALL_TAC] THEN
   SUBGOAL_THEN `(x3:real) = 
   --sqrt(((norm (u:real^3)) pow 2 - (x1:real) pow 2 - (x2:real) pow 2 - (&2 * x1 * x2) * ((w1:real^3) dot w2)) /((norm(w1 cross w2)) pow 2))` ASSUME_TAC THENL
   [UNDISCH_TAC `(norm (z:real^3)) pow 2 = (x1:real) pow 2 + (x2:real) pow 2 + (&2 * x1 * x2) * ((w1:real^3) dot w2) + ((x3:real) pow 2) * (norm(w1 cross w2)) pow 2` THEN
    UNDISCH_TAC `(norm (u:real^3)) pow 2 = (norm (z:real^3)) pow 2` THEN
    DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[REAL_ARITH `!a b c d e:real. a = b + c + d + e <=> e = a - b - c - d`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((norm((w1:real^3) cross w2)) pow 2  = &0)` THEN 
    SIMP_TAC[REAL_FIELD `!a b c. ~(b = &0) ==> ( a * b = c <=> a = c / b)`] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x3:real) < &0` THEN
    SIMP_TAC[REAL_ARITH `(a:real) = --b <=> --a = b`;GSYM POW_2_SQRT_NEG];ALL_TAC] THEN
    ABBREV_TAC `z1= (z:real^3) - (vec3_vtrans (FST (s1:screw)) ** z)` THEN
    ABBREV_TAC `z2= (z:real^3) - (vec3_vtrans (FST (s2:screw)) ** z)` THEN   
    SUBGOAL_THEN `(a2:real) = atn((w2 dot (u' cross
                               ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                               ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                               sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                              norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
                              (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                            sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                             ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                             ((w1 dot w2) pow 2 - &1)) pow 2 -  (&2 *
                             ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                             ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                             norm (w1 cross w2) pow 2) % (w1 cross w2))))) / (u' dot
                            ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                            ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                           sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                           (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                           (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                           ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                           norm (w1 cross w2) pow 2) % (w1 cross w2)) - vec3_vtrans w2 **
                           (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                           ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                          sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                          (((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) pow 2 -
                           (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) *
                           ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) /
                           norm (w1 cross w2) pow 2) % (w1 cross w2)))))` ASSUME_TAC THENL
    [MP_TAC(ISPECL[`w2:real^3`;`r:real^3`;`u:real^3`;`u':real^3`;`z:real^3`;` z2:real^3`;`p:real^3`;`c:real^3`;`s2:screw`;`a2:real`] 
                    PADEN_KAHAN_SUB_PRO_1) THEN 
    ANTS_TAC THENL
    [ASM_SIMP_TAC[];ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) - (vec3_vtrans (FST (s2:screw)) ** z) = z2` THEN DISCH_THEN(MP_TAC o SYM) THEN 
    UNDISCH_TAC `(s2:screw) = ((w2:real^3), (r:real^3) cross (w2)) ` THEN
    SIMP_TAC[FST] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `(x1:real) = (((w1:real^3) dot (w2:real^3)) * (w2 dot (u:real^3)) - w1 dot (v:real^3))/((w1 dot w2) pow 2 - &1)` THEN
    UNDISCH_TAC `(x2:real) = (((w1:real^3) dot (w2:real^3)) * (w1 dot (v:real^3)) - w2 dot (u:real^3))/((w1 dot w2) pow 2 - &1)` THEN    
    UNDISCH_TAC `(x3:real) = --sqrt(((norm (u:real^3)) pow 2 - (x1:real) pow 2 - 
                               (x2:real) pow 2 - (&2 * x1 * x2) * ((w1:real^3) dot w2)) /((norm(w1 cross w2)) pow 2))` THEN
    SIMP_TAC[VECTOR_MUL_LNEG;VECTOR_ARITH `(a:real^3) + b + -- c = a + b - c`];ALL_TAC] THEN
    SUBGOAL_THEN `(a1:real) = --atn((w1 dot(v' cross
                              ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                             sqrt((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                             ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) %
                              (w1 cross w2)) - vec3_vtrans w1 **
                              (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                              sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2))))) / (v' dot
                              ((((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                              sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)) -
                              vec3_vtrans w1 ** (((w1 dot w2) * (w2 dot u) - w1 dot v) / ((w1 dot w2) pow 2 - &1) % w1 +
                              ((w1 dot w2) * (w1 dot v) - w2 dot u) / ((w1 dot w2) pow 2 - &1) % w2 -
                              sqrt ((norm u pow 2 - (((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) pow 2 - (&2 * ((w1 dot w2) * (w2 dot u) - w1 dot v) /
                              ((w1 dot w2) pow 2 - &1) * ((w1 dot w2) * (w1 dot v) - w2 dot u) /
                              ((w1 dot w2) pow 2 - &1)) * (w1 dot w2)) / norm (w1 cross w2) pow 2) % (w1 cross w2)))))` ASSUME_TAC THENL
    [MP_TAC(ISPECL[`w1:real^3`;`r:real^3`;`v:real^3`;`v':real^3`;`z:real^3`;` z1:real^3`;`q:real^3`;`c:real^3`;`s1:screw`;`--a1:real`] 
                    PADEN_KAHAN_SUB_PRO_1) THEN 
    SIMP_TAC[REAL_ARITH `--(a:real) = b <=> a = --b`] THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC
    [REAL_ARITH `--(pi / &2) < --a1 /\ --a1 < pi / &2 <=> --(pi / &2) < a1 /\ a1 < pi / &2`];ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) = c - r` THEN DISCH_THEN(MP_TAC o SYM) THEN 
    UNDISCH_TAC `(v:real^3) = q - r` THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `(v':real^3) = v - vec3_vtrans (FST (s1:screw)) ** v` THEN
    DISCH_THEN(MP_TAC o SYM) THEN 
    UNDISCH_TAC `(s1:screw) = ((w1:real^3), (r:real^3) cross (w1)) ` THEN
    SIMP_TAC[FST] THEN STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC ` (z:real^3) = (x1:real) % (w1:real^3) + (x2:real) % (w2:real^3) + (x3:real) % (w1 cross w2)` THEN
    UNDISCH_TAC `(x1:real) = (((w1:real^3) dot (w2:real^3)) * (w2 dot (u:real^3)) - w1 dot (v:real^3))/((w1 dot w2) pow 2 - &1)` THEN
    UNDISCH_TAC `(x2:real) = (((w1:real^3) dot (w2:real^3)) * (w1 dot (v:real^3)) - w2 dot (u:real^3))/((w1 dot w2) pow 2 - &1)` THEN    
    UNDISCH_TAC `(x3:real) = --sqrt(((norm (u:real^3)) pow 2 - (x1:real) pow 2 - 
                               (x2:real) pow 2 - (&2 * x1 * x2) * ((w1:real^3) dot w2)) /((norm(w1 cross w2)) pow 2))` THEN
    SIMP_TAC[VECTOR_MUL_LNEG;VECTOR_ARITH `(a:real^3) + b + -- c = a + b - c`];ALL_TAC] THEN
    UNDISCH_TAC `(a:real) = a1 + a2` THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[]]);;

let PADEN_KAHAN_SUB_PRO_3 = prove
  (`!w r u u' v v' p q:real^3 s:screw d a a0 c d':real.
  ((--(pi / &2) < a0 /\ a0 < pi / &2) /\    
  (--(pi / &2) < a /\ a < pi / &2) /\
  &0 <=(abs c) /\ (abs c) <= pi /\ s = (w, r cross w) /\
   norm w = &1 /\
   u = p - r /\ v = q - r /\ c=a0-a /\ 
   u' = u - (vec3_vtrans (FST s) ** u) /\
   v' = v - (vec3_vtrans (FST s) ** v) /\
   matrix_exp(a0 %% screw_2_matrix s) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
   matrix_exp(a0 %% screw_2_matrix s) ** (homo_point (mk_point p)) = (homo_point (mk_point q)) /\
   ~(u' = vec 0) /\ ~(v' = vec 0)) /\
  (d) pow 2=(norm(v-matrix_exp(a %% vec3_2_ssm w) ** u)) pow 2 /\ 
  (d') pow 2 =(d) pow 2 - (abs(w dot (p - q))) pow 2 ==>
  (&0 <= c ==> a=a0-acs(((norm(u')) pow 2+(norm(v')) pow 2-(d' pow 2))/(&2*(norm(u'))*(norm(v'))))) /\ 
   (c < &0 ==> a=a0+acs(((norm(u')) pow 2+(norm(v')) pow 2-(d' pow 2))/(&2*(norm(u'))*(norm(v')))))`,
   REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** vec3_vtrans w =
                  vec3_vtrans w` ASSUME_TAC THENL 
    [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) 
    [MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w = 
    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2] THEN 
    SIMP_TAC[MATRIX_ADD_RDISTRIB;MATRIX_POW_2;SSM_LMUL_EQ_0;GSYM
            MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RZERO;
            MATRIX_ADD_LID];ALL_TAC] THEN
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** v' = vec 0` ASSUME_TAC THENL 
    [UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN    
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
    SIMP_TAC[VECTOR_SUB_EQ];ALL_TAC] THEN 
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** u' = vec 0` ASSUME_TAC THENL 
    [UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN    
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
    SIMP_TAC[VECTOR_SUB_EQ];ALL_TAC] THEN  
    SUBGOAL_THEN `matrix_exp ((a0:real) %% vec3_2_ssm w) ** (u:real^3)
                    = v` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a0:real) %% screw_2_matrix s) ** 
                   homo_point (mk_point (p:real^3)) = 
                   homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a0 %% screw_2_matrix s) ** homo_point 
                  (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y = z`;VECTOR_ARITH `(a:real^3 = b + a - c) <=> (vec 0 = b - c)`] ;ALL_TAC] THEN
   SUBGOAL_THEN `vec3_vtrans (w:real^3) ** (v:real^3) = vec3_vtrans w ** (u:real^3)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[VECTOR_ARITH `!A:real^3^3 b c:real^3. (A ** b= A ** c) <=> ((A:real^3^3)** (b:real^3)- A ** c= vec 0)`;GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w:real^3) = &1` THEN SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB;RODRIGUES_FORMULA_ALT] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB;MATRIX_VECTOR_MUL_SUB_LDISTRIB;MATRIX_VECTOR_MUL_RMUL;MATRIX_VECTOR_MUL_ASSOC;
                    SSM_RMUL_EQ_0;MATRIX_VECTOR_MUL_LZERO;VECTOR_MUL_RZERO;VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[VECTOR_ARITH `!x y z. (x+y-x)-y=vec 0`];ALL_TAC] THEN 
    SUBGOAL_THEN `matrix_exp ((a0:real) %% vec3_2_ssm w) ** (u':real^3)
                  = v'` ASSUME_TAC THENL
    [UNDISCH_TAC `(u':real^3) = (u:real^3) - vec3_vtrans (FST (s:screw)) ** u` THEN 
    UNDISCH_TAC `(v':real^3) = (v:real^3) - vec3_vtrans (FST (s:screw)) ** v` THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp ((a0:real) %% screw_2_matrix s) ** 
                 homo_point (mk_point (p:real^3)) = 
                 homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r`  THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a0 %% screw_2_matrix s) ** homo_point 
                (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
             MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = 
                     (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y =
            z`;VECTOR_ARITH `(a:real^3 = b + a - c) 
            <=> (vec 0 = b - c)`] THEN 
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MESON [MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_MUL_LID] `(a:real^3) - (B:real^3^3) ** a = (mat 1 - B) ** a`] THEN
    ONCE_REWRITE_TAC[MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w =
                    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2;RODRIGUES_FORMULA] THEN
    SIMP_TAC[MATRIX_ARITH `mat 1 - (mat 1 + (A:real^3^3) + (B:real^3^3))   
            = --(A + B)`;MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_LNEG;
            MATRIX_ADD_LDISTRIB;MATRIX_ADD_RDISTRIB;MATRIX_MUL_RID] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LMUL;GSYM MATRIX_POW_ADD] THEN
    SIMP_TAC[MESON [MATRIX_POW_ADD;MATRIX_POW_1;
            ARITH_RULE `1 + 2 = 0 + 3`] `!A:real^N^N. A ** A matrix_pow 2 = A matrix_pow (0 + 3)`] THEN
    ASM_SIMP_TAC[SSM_POW_CYCLICITY;ARITH_RULE `2 + 2 = 1 + 3`] THEN
    SIMP_TAC[ARITH;MATRIX_POW_1;MATRIX_CMUL_RNEG;GSYM MATRIX_NEG_ADD;
            MATRIX_ADD_LNEG;MATRIX_ADD_RID;MATRIX_ARITH `-- ((mat 0):real^3^3) = mat 0`;MATRIX_VECTOR_MUL_LZERO];ALL_TAC] THEN
    SUBGOAL_THEN `norm(u':real^3) = norm(v':real^3)` ASSUME_TAC THENL
    [SIMP_TAC[NORM_EQ;ARITH_RULE ` ((x:real^3) dot x= y dot y) <=> (x dot x - y dot y= &0)`] THEN 
    POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC] THEN STRIP_TAC THEN 
    SIMP_TAC[TRANSP_TRANS_EXP] THEN  
    SUBGOAL_THEN `(a0 %% transp (vec3_2_ssm w)) ** (a0 %% (vec3_2_ssm (w:real^3))) = (a0 %% (vec3_2_ssm w))** (a0 %% transp (vec3_2_ssm w))` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
    ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
   SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
   SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `!A:real^3^3. -- A + A = mat 0`;
                   MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID;REAL_SUB_REFL];ALL_TAC] THEN 
    SUBGOAL_THEN ` (norm((v':real^3)-matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3))) pow 2= (d':real) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(d':real) pow 2 =(norm(((v':real^3) + (vec3_vtrans (FST (s:screw)) ** v))-
                                matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** ((u':real^3)+(vec3_vtrans (FST (s:screw)) ** u)))) pow 2 - 
                                (abs((w:real^3) dot ((p:real^3) - (q:real^3)))) pow 2` ASSUME_TAC THENL
                               [UNDISCH_TAC `(u':real^3) = u - (vec3_vtrans (FST (s:screw)) ** u)` THEN 
                                UNDISCH_TAC `(v':real^3) = v - (vec3_vtrans (FST (s:screw)) ** v)` THEN 
                                SIMP_TAC[VECTOR_ARITH `(x:real^3) - y + y = x`] THEN
                                UNDISCH_TAC `(d':real) pow 2 =(d:real) pow 2 - (abs((w:real^3) dot ((p:real^3) - (q:real^3)))) pow 2` THEN
                                UNDISCH_TAC ` (d:real) pow 2=(norm((v:real^3)-matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** (u:real^3))) pow 2` THEN
                                SIMP_TAC[];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    UNDISCH_TAC `u:real^3 = p - r` THEN UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`;VECTOR_ARITH `((x:real^3) + y) - (x + z) = y - z`] THEN
    REPEAT STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `(a:real) = b - c <=> c= b - a`] THEN 
    SUBGOAL_THEN `abs ((w:real^3) dot ((u:real^3) - (v:real^3))) pow 2 = (w dot u) * (w dot u)- &2 * (v dot w) * (w dot u) + (w dot v) * (w dot v)`ASSUME_TAC THENL
                              [SIMP_TAC[REAL_POW2_ABS;REAL_POW_2;DOT_RSUB;REAL_SUB_RDISTRIB;REAL_SUB_LDISTRIB;REAL_MUL_SYM;DOT_SYM;
                               REAL_ARITH `(a:real) - b - (c - d) = a - b - c + d`;REAL_ARITH ` (x:real) - &2 * y = x - y - y`];ALL_TAC] THEN
    SUBGOAL_THEN `norm ((v':real^3) - matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3)) pow 2 = 
                               v' dot v' + u' dot u' - &2 * (v' dot (matrix_exp (a %% vec3_2_ssm w) ** u'))` ASSUME_TAC THENL
                              [SIMP_TAC[NORM_POW_2;DOT_LSUB;DOT_RSUB;DOT_LADD;DOT_RADD] THEN
    SUBGOAL_THEN `(matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3)) dot
                               (matrix_exp (a %% vec3_2_ssm w) ** u') = u' dot u'` ASSUME_TAC THENL
                               [SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_TRANS_EXP] THEN
    SUBGOAL_THEN ` (a %% (vec3_2_ssm w))** (a %% transp (vec3_2_ssm w)) = (a %% transp (vec3_2_ssm w)) ** (a %% (vec3_2_ssm (w:real^3)))` ASSUME_TAC THENL
                               [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
                               ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
                               ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN
                               POP_ASSUM MP_TAC THEN 
                               SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
                               SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `--(a:real^3^3) + a = mat 0`;
                                               REAL_MUL_RZERO;MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN
     POP_ASSUM MP_TAC THEN SIMP_TAC[REAL_ARITH `(a:real) - b - (c - d) = a +d - (b + c)`;DOT_SYM;REAL_ARITH `x + x = &2 * x`];ALL_TAC] THEN
     SUBGOAL_THEN `(matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** ((u':real^3) + vec3_vtrans (FST (s:screw)) ** u)) dot
                               (matrix_exp (a %% vec3_2_ssm w) ** (u' + vec3_vtrans (FST s) ** u)) = (u' + vec3_vtrans (FST s) ** u) dot (u' + vec3_vtrans (FST s) ** u)` ASSUME_TAC THENL
                                [SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_TRANS_EXP] THEN
    SUBGOAL_THEN ` (a %% (vec3_2_ssm w))** (a %% transp (vec3_2_ssm w)) = (a %% transp (vec3_2_ssm w)) ** (a %% (vec3_2_ssm (w:real^3)))` ASSUME_TAC THENL
                               [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
                               ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
                               ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN
                               POP_ASSUM MP_TAC THEN 
                               SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
                               SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `--(a:real^3^3) + a = mat 0`;
                                               REAL_MUL_RZERO;MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN               
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN  
     SIMP_TAC[NORM_POW_2;DOT_LSUB;DOT_RSUB] THEN  REPEAT STRIP_TAC THEN 
     SIMP_TAC[REAL_ARITH `(a:real) - b - (c - d) = a +d - (b + c)`;REAL_ARITH `((a:real) + b - c) - d = a + b - c - d`;DOT_SYM;REAL_ARITH `x + x = &2 * x`] THEN 
     UNDISCH_TAC `(s:screw) = (w:real^3),r cross w` THEN 
     SIMP_TAC[REAL_ARITH `(a:real) - (b+ c - d) = a - b - c + d`;DOT_LADD;DOT_RADD;GSYM REAL_ADD_ASSOC;
                     MATRIX_VECTOR_MUL_ADD_LDISTRIB;DOT_SYM;FST] THEN STRIP_TAC THEN                  
     SIMP_TAC[REAL_ARITH `(a:real) + b + b + c= a +(b + b) + c`;REAL_ARITH `x + x = &2 * x`;REAL_ADD_LDISTRIB;
                     REAL_ARITH `(a:real) + b +c + (a0 + b0 + c0) - (a1 + b1 + c1 + d1) - a - a0 + a1 = b + c + b0 + c0 - b1 - c1 - d1`] THEN 
     SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** vec3_vtrans w = vec3_vtrans w` ASSUME_TAC THENL          
                               [ASM_SIMP_TAC[RODRIGUES_FORMULA_ALT;MATRIX_ADD_RDISTRIB;MATRIX_MUL_LMUL;MATRIX_MUL_LID;
                                                         SSM_LMUL_EQ_0;MATRIX_CMUL_RZERO;MATRIX_ADD_LID] THEN 
                               SIMP_TAC[MATRIX_CMUL_SUB_RDISTRIB;MATRIX_CMUL_LID;MATRIX_ARITH `(A:real^3^3) + B - A = B`];ALL_TAC] THEN 
     POP_ASSUM MP_TAC THEN SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
     UNDISCH_TAC `norm (w:real^3) = &1` THEN 
     SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;GSYM TRANSP_TRANSP;MATRIX_VECTOR_MUL_ASSOC;
                     GSYM MATRIX_TRANSP_MUL;TRANSP_VEC3_RMUL_SELF;TRANSP_EQ_VEC3] THEN REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `vec3_vtrans (w:real^3) ** matrix_exp ((a:real) %% vec3_2_ssm w) = vec3_vtrans w` ASSUME_TAC THENL     
                               [ASM_SIMP_TAC[RODRIGUES_FORMULA_ALT;MATRIX_ADD_LDISTRIB;MATRIX_MUL_RMUL;MATRIX_MUL_RID;
                                                         SSM_RMUL_EQ_0;MATRIX_CMUL_RZERO;MATRIX_ADD_LID] THEN 
                               SIMP_TAC[MATRIX_CMUL_SUB_RDISTRIB;MATRIX_CMUL_LID;MATRIX_ARITH `(A:real^3^3) + B - A = B`];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** v' = vec 0` THEN UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** u' = vec 0` THEN
    SIMP_TAC[DOT_LZERO;REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_RZERO;REAL_SUB_LZERO] THEN REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `! x y z:real^3. (y dot z) * (x dot z) = (vec3_vtrans z ** x) dot y` ASSUME_TAC THENL 
                              [REPEAT STRIP_TAC THEN SIMP_TAC[dot;vec3_vtrans;CART_EQ;LAMBDA_BETA;matrix_vector_mul;DIMINDEX_3;SUM_3;VECTOR_3;
                                                                                       FORALL_3;REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;GSYM REAL_MUL_ASSOC] THEN
                               ARITH_TAC;ALL_TAC] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u':real^3)
                  = matrix_exp (--(c:real) %% vec3_2_ssm w) ** (v':real^3)` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a0:real) %% vec3_2_ssm w) ** (u':real^3) = v'` THEN
    UNDISCH_TAC `(c:real) = a0 - a` THEN
    SIMP_TAC[REAL_ARITH `(c:real) = a - b <=> a = c + b`] THEN STRIP_TAC THEN
    SIMP_TAC[MATRIX_CMUL_ADD_RDISTRIB] THEN
    SUBGOAL_THEN `((c:real) %% vec3_2_ssm w) ** ((a:real) %% vec3_2_ssm (w:real^3)) = (a%% vec3_2_ssm w) ** (c%% vec3_2_ssm w)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL;MATRIX_CMUL_ASSOC;REAL_MUL_SYM];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[MATRIX_EXP_ADD] THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN
    SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN STRIP_TAC THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC] THEN 
    SUBGOAL_THEN `((c:real) %% vec3_2_ssm w) ** (--(c:real) %% vec3_2_ssm (w:real^3)) = (--c%% vec3_2_ssm w) ** (c%% vec3_2_ssm w)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL;MATRIX_CMUL_ASSOC;REAL_MUL_SYM];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
    SIMP_TAC[GSYM MATRIX_CMUL_ADD_RDISTRIB;REAL_ARITH `--x + x = &0`;MATRIX_CMUL_LZERO;MATRIX_EXP_0;MATRIX_MUL_LID];ALL_TAC] THEN
    SUBGOAL_THEN `(d':real) pow 2 = &2 % (v':real^3) dot v' - (&2 * cos(c:real)) % v' dot v'` ASSUME_TAC THENL
    [UNDISCH_TAC `(norm((v':real^3)-matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3))) pow 2= (d':real) pow 2` THEN 
     POP_ASSUM MP_TAC THEN 
     SIMP_TAC[] THEN STRIP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
     SIMP_TAC[NORM_POW_2;DOT_LSUB;DOT_RSUB;REAL_ARITH `(a:real) - b - (c - d) = a - b - c + d`] THEN 
     STRIP_TAC THEN SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN 
     SIMP_TAC[GSYM DOT_MATRIX_TRANSP_RMUL;TRANSP_TRANSP;TRANSP_TRANS_EXP;TRANSP_EQ_NEG_SSM;
                     MATRIX_CMUL_RNEG;MATRIX_CMUL_LNEG;MATRIX_NEG_NEG;MATRIX_VECTOR_MUL_ASSOC] THEN 
    SUBGOAL_THEN `((c:real) %% vec3_2_ssm w) ** (--(c:real) %% vec3_2_ssm (w:real^3)) = (--c%% vec3_2_ssm w) ** (c%% vec3_2_ssm w)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL;MATRIX_CMUL_ASSOC;REAL_MUL_SYM];ALL_TAC] THEN 
     SIMP_TAC[GSYM MATRIX_CMUL_LNEG] THEN 
    POP_ASSUM MP_TAC THEN  DISCH_THEN (MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
    SIMP_TAC[GSYM MATRIX_CMUL_ADD_RDISTRIB;REAL_ARITH `x + --x = &0`;MATRIX_CMUL_LZERO;MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID] THEN
    SIMP_TAC[VECTOR_ARITH `x dot x - x dot (A** x) - x dot (B** x) + x dot x = &2 % x dot x - x dot (A** x) - x dot (B** x)`;
                    VECTOR_ARITH `&2 % x dot x - x dot (A** x) - x dot (B** x) = &2 % x dot x - (x dot (A** x) + x dot (B** x))`;
                    GSYM DOT_RADD;GSYM MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN   
    UNDISCH_TAC `norm (w:real^3) = &1` THEN 
    SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN STRIP_TAC THEN 
    SIMP_TAC[SIN_NEG;COS_NEG;GSYM MATRIX_ADD_ASSOC] THEN 
    SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_ARITH `(A:real^3^3) + --(B:real^3^3) + (C:real^3^3) + A + B + C= (&2:real) %% A + &2 %%C`] THEN
    UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** v' = vec 0` THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_CMUL_ASSOC;MATRIX_VECTOR_LMUL;VECTOR_MUL_RZERO;
                     VECTOR_ADD_RID;MATRIX_VECTOR_MUL_LID;DOT_RMUL;DOT_LMUL;REAL_MUL_ASSOC];ALL_TAC] THEN
    SUBGOAL_THEN `(norm(u':real^3)) pow 2+(norm(v':real^3)) pow 2 - &2*(norm(u':real^3))*(norm(v':real^3))*cos(c:real)=(d':real) pow 2` ASSUME_TAC THENL 
    [UNDISCH_TAC `norm(u':real^3) = norm(v':real^3)` THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `(a:real) + a - b = &2 * a - b`;REAL_ARITH `(a:real) * b * b * c = (a * c) * ((b) pow 2)`;NORM_POW_2;GSYM DOT_LMUL] THEN 
    UNDISCH_TAC `(d':real) pow 2 = &2 % (v':real^3) dot v' - (&2 * cos(c:real)) % v' dot v'`  THEN 
    SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `(a:real) + b - c = d <=> c = a + b - d`;REAL_MUL_ASSOC] THEN  
    SUBGOAL_THEN ` &0 < (&2 * (norm (u':real^3))) * (norm (v':real^3))` ASSUME_TAC THENL 
    [SIMP_TAC[GSYM REAL_MUL_ASSOC;GSYM (REAL_ARITH` &0 < x <=> &0 < &2 * x`)] THEN
    UNDISCH_TAC `~((v':real^3) = vec 0)` THEN UNDISCH_TAC `~((u':real^3) = vec 0)` THEN 
    SIMP_TAC[GSYM NORM_POS_LT] THEN MP_TAC (ISPECL[`norm(u':real^3)`;`&0`;`norm(v':real^3)`] REAL_LT_LMUL) THEN 
    SIMP_TAC[REAL_MUL_RZERO];ALL_TAC] THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_FIELD `!a b c.  &0 <a ==> ( a * b = c <=> b = c / a)`] THEN STRIP_TAC THEN 
    ONCE_REWRITE_TAC[GSYM COS_ABS] THEN 
    DISCH_THEN (MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    UNDISCH_TAC `(abs c) <= pi` THEN UNDISCH_TAC ` &0 <=(abs c)` THEN 
    SIMP_TAC[ACS_COS] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC ` &0 <= c` THEN 
    SIMP_TAC[GSYM REAL_ABS_REFL] THEN STRIP_TAC THEN 
    ONCE_REWRITE_TAC[REAL_ARITH `(a:real) = a0 - c <=> c = a0 - a`] THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** vec3_vtrans w =
                  vec3_vtrans w` ASSUME_TAC THENL 
    [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) 
    [MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w = 
    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2] THEN 
    SIMP_TAC[MATRIX_ADD_RDISTRIB;MATRIX_POW_2;SSM_LMUL_EQ_0;GSYM
            MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RZERO;
            MATRIX_ADD_LID];ALL_TAC] THEN
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** v' = vec 0` ASSUME_TAC THENL 
    [UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN    
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
    SIMP_TAC[VECTOR_SUB_EQ];ALL_TAC] THEN 
    SUBGOAL_THEN `(vec3_vtrans:real^3->real^3^3) w ** u' = vec 0` ASSUME_TAC THENL 
    [UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN    
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
    SIMP_TAC[VECTOR_SUB_EQ];ALL_TAC] THEN   
    SUBGOAL_THEN `matrix_exp ((a0:real) %% vec3_2_ssm w) ** (u:real^3)
                    = v` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a0:real) %% screw_2_matrix s) ** 
                   homo_point (mk_point (p:real^3)) = 
                   homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a0 %% screw_2_matrix s) ** homo_point 
                  (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y = z`;VECTOR_ARITH `(a:real^3 = b + a - c) <=> (vec 0 = b - c)`] ;ALL_TAC] THEN
   SUBGOAL_THEN `vec3_vtrans (w:real^3) ** (v:real^3) = vec3_vtrans w ** (u:real^3)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[VECTOR_ARITH `!A:real^3^3 b c:real^3. (A ** b= A ** c) <=> ((A:real^3^3)** (b:real^3)- A ** c= vec 0)`;GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN 
    STRIP_TAC THEN UNDISCH_TAC `norm (w:real^3) = &1` THEN SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB;RODRIGUES_FORMULA_ALT] THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_LID;VECTOR_SUB_RDISTRIB;VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB;MATRIX_VECTOR_MUL_SUB_LDISTRIB;MATRIX_VECTOR_MUL_RMUL;MATRIX_VECTOR_MUL_ASSOC;
                    SSM_RMUL_EQ_0;MATRIX_VECTOR_MUL_LZERO;VECTOR_MUL_RZERO;VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[VECTOR_ARITH `!x y z. (x+y-x)-y=vec 0`];ALL_TAC] THEN 
    SUBGOAL_THEN `matrix_exp ((a0:real) %% vec3_2_ssm w) ** (u':real^3)
                  = v'` ASSUME_TAC THENL
    [UNDISCH_TAC `(u':real^3) = (u:real^3) - vec3_vtrans (FST (s:screw)) ** u` THEN 
    UNDISCH_TAC `(v':real^3) = (v:real^3) - vec3_vtrans (FST (s:screw)) ** v` THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp ((a0:real) %% screw_2_matrix s) ** 
                 homo_point (mk_point (p:real^3)) = 
                 homo_point (mk_point (q:real^3))` THEN
    UNDISCH_TAC `u:real^3 = p - r` THEN
    UNDISCH_TAC `v:real^3 = q - r`  THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `matrix_exp (a0 %% screw_2_matrix s) ** homo_point 
                (mk_point r) = homo_point (mk_point r)` THEN
    ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;FST] THEN 
    SIMP_TAC[HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE;
             MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN 
    ONCE_REWRITE_TAC[VECTOR_ARITH `((a:real^3) + b) + c = 
                     (a + c)  + b`] THEN 
    SIMP_TAC[VECTOR_ARITH `(x:real^3) + y = x + z <=> y =
            z`;VECTOR_ARITH `(a:real^3 = b + a - c) 
            <=> (vec 0 = b - c)`] THEN 
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MESON [MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_MUL_LID] `(a:real^3) - (B:real^3^3) ** a = (mat 1 - B) ** a`] THEN
    ONCE_REWRITE_TAC[MATRIX_ARITH `(vec3_vtrans:real^3->real^3^3) w =
                    (vec3_vtrans w - mat 1) + mat 1`] THEN 
    ASM_SIMP_TAC[GSYM SSM_POW_2;RODRIGUES_FORMULA] THEN
    SIMP_TAC[MATRIX_ARITH `mat 1 - (mat 1 + (A:real^3^3) + (B:real^3^3))   
            = --(A + B)`;MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_LNEG;
            MATRIX_ADD_LDISTRIB;MATRIX_ADD_RDISTRIB;MATRIX_MUL_RID] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LMUL;GSYM MATRIX_POW_ADD] THEN
    SIMP_TAC[MESON [MATRIX_POW_ADD;MATRIX_POW_1;
            ARITH_RULE `1 + 2 = 0 + 3`] `!A:real^N^N. A ** A matrix_pow 2 = A matrix_pow (0 + 3)`] THEN
    ASM_SIMP_TAC[SSM_POW_CYCLICITY;ARITH_RULE `2 + 2 = 1 + 3`] THEN
    SIMP_TAC[ARITH;MATRIX_POW_1;MATRIX_CMUL_RNEG;GSYM MATRIX_NEG_ADD;
            MATRIX_ADD_LNEG;MATRIX_ADD_RID;MATRIX_ARITH `-- ((mat 0):real^3^3) = mat 0`;MATRIX_VECTOR_MUL_LZERO];ALL_TAC] THEN
    SUBGOAL_THEN `norm(u':real^3) = norm(v':real^3)` ASSUME_TAC THENL
    [SIMP_TAC[NORM_EQ;ARITH_RULE ` ((x:real^3) dot x= y dot y) <=> (x dot x - y dot y= &0)`] THEN 
    POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;MATRIX_VECTOR_MUL_ASSOC] THEN STRIP_TAC THEN 
    SIMP_TAC[TRANSP_TRANS_EXP] THEN  
    SUBGOAL_THEN `(a0 %% transp (vec3_2_ssm w)) ** (a0 %% (vec3_2_ssm (w:real^3))) = (a0 %% (vec3_2_ssm w))** (a0 %% transp (vec3_2_ssm w))` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
    ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
   SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
   SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `!A:real^3^3. -- A + A = mat 0`;
                   MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID;REAL_SUB_REFL];ALL_TAC] THEN 
    SUBGOAL_THEN ` (norm((v':real^3)-matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3))) pow 2= (d':real) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(d':real) pow 2 =(norm(((v':real^3) + (vec3_vtrans (FST (s:screw)) ** v))-
                                matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** ((u':real^3)+(vec3_vtrans (FST (s:screw)) ** u)))) pow 2 - 
                                (abs((w:real^3) dot ((p:real^3) - (q:real^3)))) pow 2` ASSUME_TAC THENL
                               [UNDISCH_TAC `(u':real^3) = u - (vec3_vtrans (FST (s:screw)) ** u)` THEN 
                                UNDISCH_TAC `(v':real^3) = v - (vec3_vtrans (FST (s:screw)) ** v)` THEN 
                                SIMP_TAC[VECTOR_ARITH `(x:real^3) - y + y = x`] THEN
                                UNDISCH_TAC `(d':real) pow 2 =(d:real) pow 2 - (abs((w:real^3) dot ((p:real^3) - (q:real^3)))) pow 2` THEN
                                UNDISCH_TAC ` (d:real) pow 2=(norm((v:real^3)-matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** (u:real^3))) pow 2` THEN
                                SIMP_TAC[];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    UNDISCH_TAC `u:real^3 = p - r` THEN UNDISCH_TAC `v:real^3 = q - r` THEN
    SIMP_TAC[VECTOR_ARITH `(c:real^3) = a - b <=> a = b + c`;VECTOR_ARITH `((x:real^3) + y) - (x + z) = y - z`] THEN
    REPEAT STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `(a:real) = b - c <=> c= b - a`] THEN 
    SUBGOAL_THEN `abs ((w:real^3) dot ((u:real^3) - (v:real^3))) pow 2 = (w dot u) * (w dot u)- &2 * (v dot w) * (w dot u) + (w dot v) * (w dot v)`ASSUME_TAC THENL
                              [SIMP_TAC[REAL_POW2_ABS;REAL_POW_2;DOT_RSUB;REAL_SUB_RDISTRIB;REAL_SUB_LDISTRIB;REAL_MUL_SYM;DOT_SYM;
                               REAL_ARITH `(a:real) - b - (c - d) = a - b - c + d`;REAL_ARITH ` (x:real) - &2 * y = x - y - y`];ALL_TAC] THEN
    SUBGOAL_THEN `norm ((v':real^3) - matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3)) pow 2 = 
                               v' dot v' + u' dot u' - &2 * (v' dot (matrix_exp (a %% vec3_2_ssm w) ** u'))` ASSUME_TAC THENL
                              [SIMP_TAC[NORM_POW_2;DOT_LSUB;DOT_RSUB;DOT_LADD;DOT_RADD] THEN
    SUBGOAL_THEN `(matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3)) dot
                               (matrix_exp (a %% vec3_2_ssm w) ** u') = u' dot u'` ASSUME_TAC THENL
                               [SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_TRANS_EXP] THEN
    SUBGOAL_THEN ` (a %% (vec3_2_ssm w))** (a %% transp (vec3_2_ssm w)) = (a %% transp (vec3_2_ssm w)) ** (a %% (vec3_2_ssm (w:real^3)))` ASSUME_TAC THENL
                               [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
                               ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
                               ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN
                               POP_ASSUM MP_TAC THEN 
                               SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
                               SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `--(a:real^3^3) + a = mat 0`;
                                               REAL_MUL_RZERO;MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN
     POP_ASSUM MP_TAC THEN SIMP_TAC[REAL_ARITH `(a:real) - b - (c - d) = a +d - (b + c)`;DOT_SYM;REAL_ARITH `x + x = &2 * x`];ALL_TAC] THEN
     SUBGOAL_THEN `(matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** ((u':real^3) + vec3_vtrans (FST (s:screw)) ** u)) dot
                               (matrix_exp (a %% vec3_2_ssm w) ** (u' + vec3_vtrans (FST s) ** u)) = (u' + vec3_vtrans (FST s) ** u) dot (u' + vec3_vtrans (FST s) ** u)` ASSUME_TAC THENL
                                [SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;TRANSP_TRANS_EXP] THEN
    SUBGOAL_THEN ` (a %% (vec3_2_ssm w))** (a %% transp (vec3_2_ssm w)) = (a %% transp (vec3_2_ssm w)) ** (a %% (vec3_2_ssm (w:real^3)))` ASSUME_TAC THENL
                               [SIMP_TAC[MATRIX_MUL_RMUL] THEN ASM_CASES_TAC `a = &0` THENL [ASM_SIMP_TAC[MATRIX_CMUL_LZERO];ALL_TAC] THEN
                               ASM_SIMP_TAC[MATRIX_CMUL_LCANCEL ] THEN 
                               ASM_SIMP_TAC[MATRIX_MUL_LMUL ;MATRIX_CMUL_LCANCEL;TRANSP_EQ_NEG_SSM;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN
                               POP_ASSUM MP_TAC THEN 
                               SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
                               SIMP_TAC[TRANSP_EQ_NEG_SSM;MATRIX_CMUL_RNEG;MATRIX_ARITH `--(a:real^3^3) + a = mat 0`;
                                               REAL_MUL_RZERO;MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN               
     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN  
     SIMP_TAC[NORM_POW_2;DOT_LSUB;DOT_RSUB] THEN  REPEAT STRIP_TAC THEN 
     SIMP_TAC[REAL_ARITH `(a:real) - b - (c - d) = a +d - (b + c)`;REAL_ARITH `((a:real) + b - c) - d = a + b - c - d`;DOT_SYM;REAL_ARITH `x + x = &2 * x`] THEN 
     UNDISCH_TAC `(s:screw) = (w:real^3),r cross w` THEN 
     SIMP_TAC[REAL_ARITH `(a:real) - (b+ c - d) = a - b - c + d`;DOT_LADD;DOT_RADD;GSYM REAL_ADD_ASSOC;
                     MATRIX_VECTOR_MUL_ADD_LDISTRIB;DOT_SYM;FST] THEN STRIP_TAC THEN                  
     SIMP_TAC[REAL_ARITH `(a:real) + b + b + c= a +(b + b) + c`;REAL_ARITH `x + x = &2 * x`;REAL_ADD_LDISTRIB;
                     REAL_ARITH `(a:real) + b +c + (a0 + b0 + c0) - (a1 + b1 + c1 + d1) - a - a0 + a1 = b + c + b0 + c0 - b1 - c1 - d1`] THEN 
     SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm (w:real^3)) ** vec3_vtrans w = vec3_vtrans w` ASSUME_TAC THENL          
                               [ASM_SIMP_TAC[RODRIGUES_FORMULA_ALT;MATRIX_ADD_RDISTRIB;MATRIX_MUL_LMUL;MATRIX_MUL_LID;
                                                         SSM_LMUL_EQ_0;MATRIX_CMUL_RZERO;MATRIX_ADD_LID] THEN 
                               SIMP_TAC[MATRIX_CMUL_SUB_RDISTRIB;MATRIX_CMUL_LID;MATRIX_ARITH `(A:real^3^3) + B - A = B`];ALL_TAC] THEN 
     POP_ASSUM MP_TAC THEN SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
     UNDISCH_TAC `norm (w:real^3) = &1` THEN 
     SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;GSYM TRANSP_TRANSP;MATRIX_VECTOR_MUL_ASSOC;
                     GSYM MATRIX_TRANSP_MUL;TRANSP_VEC3_RMUL_SELF;TRANSP_EQ_VEC3] THEN REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `vec3_vtrans (w:real^3) ** matrix_exp ((a:real) %% vec3_2_ssm w) = vec3_vtrans w` ASSUME_TAC THENL     
                               [ASM_SIMP_TAC[RODRIGUES_FORMULA_ALT;MATRIX_ADD_LDISTRIB;MATRIX_MUL_RMUL;MATRIX_MUL_RID;
                                                         SSM_RMUL_EQ_0;MATRIX_CMUL_RZERO;MATRIX_ADD_LID] THEN 
                               SIMP_TAC[MATRIX_CMUL_SUB_RDISTRIB;MATRIX_CMUL_LID;MATRIX_ARITH `(A:real^3^3) + B - A = B`];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** v' = vec 0` THEN UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** u' = vec 0` THEN
    SIMP_TAC[DOT_LZERO;REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_RZERO;REAL_SUB_LZERO] THEN REPEAT STRIP_TAC THEN 
    SUBGOAL_THEN `! x y z:real^3. (y dot z) * (x dot z) = (vec3_vtrans z ** x) dot y` ASSUME_TAC THENL 
                              [REPEAT STRIP_TAC THEN SIMP_TAC[dot;vec3_vtrans;CART_EQ;LAMBDA_BETA;matrix_vector_mul;DIMINDEX_3;SUM_3;VECTOR_3;
                                                                                       FORALL_3;REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;GSYM REAL_MUL_ASSOC] THEN
                               ARITH_TAC;ALL_TAC] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp ((a:real) %% vec3_2_ssm w) ** (u':real^3)
                  = matrix_exp (--(c:real) %% vec3_2_ssm w) ** (v':real^3)` ASSUME_TAC THENL
    [UNDISCH_TAC `matrix_exp ((a0:real) %% vec3_2_ssm w) ** (u':real^3) = v'` THEN
    UNDISCH_TAC `(c:real) = a0 - a` THEN
    SIMP_TAC[REAL_ARITH `(c:real) = a - b <=> a = c + b`] THEN STRIP_TAC THEN
    SIMP_TAC[MATRIX_CMUL_ADD_RDISTRIB] THEN
    SUBGOAL_THEN `((c:real) %% vec3_2_ssm w) ** ((a:real) %% vec3_2_ssm (w:real^3)) = (a%% vec3_2_ssm w) ** (c%% vec3_2_ssm w)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL;MATRIX_CMUL_ASSOC;REAL_MUL_SYM];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[MATRIX_EXP_ADD] THEN STRIP_TAC THEN 
    DISCH_THEN(MP_TAC o SYM) THEN
    SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN STRIP_TAC THEN 
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC] THEN 
    SUBGOAL_THEN `((c:real) %% vec3_2_ssm w) ** (--(c:real) %% vec3_2_ssm (w:real^3)) = (--c%% vec3_2_ssm w) ** (c%% vec3_2_ssm w)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL;MATRIX_CMUL_ASSOC;REAL_MUL_SYM];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
    SIMP_TAC[GSYM MATRIX_CMUL_ADD_RDISTRIB;REAL_ARITH `--x + x = &0`;MATRIX_CMUL_LZERO;MATRIX_EXP_0;MATRIX_MUL_LID];ALL_TAC] THEN
    SUBGOAL_THEN `(d':real) pow 2 = &2 % (v':real^3) dot v' - (&2 * cos(c:real)) % v' dot v'` ASSUME_TAC THENL
    [UNDISCH_TAC `(norm((v':real^3)-matrix_exp((a:real) %% vec3_2_ssm (w:real^3)) ** (u':real^3))) pow 2= (d':real) pow 2` THEN 
     POP_ASSUM MP_TAC THEN 
     SIMP_TAC[] THEN STRIP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN 
     SIMP_TAC[NORM_POW_2;DOT_LSUB;DOT_RSUB;REAL_ARITH `(a:real) - b - (c - d) = a - b - c + d`] THEN 
     STRIP_TAC THEN SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN 
     SIMP_TAC[GSYM DOT_MATRIX_TRANSP_RMUL;TRANSP_TRANSP;TRANSP_TRANS_EXP;TRANSP_EQ_NEG_SSM;
                     MATRIX_CMUL_RNEG;MATRIX_CMUL_LNEG;MATRIX_NEG_NEG;MATRIX_VECTOR_MUL_ASSOC] THEN 
    SUBGOAL_THEN `((c:real) %% vec3_2_ssm w) ** (--(c:real) %% vec3_2_ssm (w:real^3)) = (--c%% vec3_2_ssm w) ** (c%% vec3_2_ssm w)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_MUL_RMUL;MATRIX_MUL_LMUL;MATRIX_CMUL_ASSOC;REAL_MUL_SYM];ALL_TAC] THEN 
     SIMP_TAC[GSYM MATRIX_CMUL_LNEG] THEN 
    POP_ASSUM MP_TAC THEN  DISCH_THEN (MP_TAC o SYM) THEN 
    SIMP_TAC[GSYM MATRIX_EXP_ADD] THEN STRIP_TAC THEN
    SIMP_TAC[GSYM MATRIX_CMUL_ADD_RDISTRIB;REAL_ARITH `x + --x = &0`;MATRIX_CMUL_LZERO;MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID] THEN
    SIMP_TAC[VECTOR_ARITH `x dot x - x dot (A** x) - x dot (B** x) + x dot x = &2 % x dot x - x dot (A** x) - x dot (B** x)`;
                    VECTOR_ARITH `&2 % x dot x - x dot (A** x) - x dot (B** x) = &2 % x dot x - (x dot (A** x) + x dot (B** x))`;
                    GSYM DOT_RADD;GSYM MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN   
    UNDISCH_TAC `norm (w:real^3) = &1` THEN 
    SIMP_TAC[RODRIGUES_FORMULA_ALT] THEN STRIP_TAC THEN 
    SIMP_TAC[SIN_NEG;COS_NEG;GSYM MATRIX_ADD_ASSOC] THEN 
    SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_ARITH `(A:real^3^3) + --(B:real^3^3) + (C:real^3^3) + A + B + C= (&2:real) %% A + &2 %%C`] THEN
    UNDISCH_TAC `((vec3_vtrans w):real^3^3) ** v' = vec 0` THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_CMUL_ASSOC;MATRIX_VECTOR_LMUL;VECTOR_MUL_RZERO;
                     VECTOR_ADD_RID;MATRIX_VECTOR_MUL_LID;DOT_RMUL;DOT_LMUL;REAL_MUL_ASSOC];ALL_TAC] THEN
    SUBGOAL_THEN `(norm(u':real^3)) pow 2+(norm(v':real^3)) pow 2 - &2*(norm(u':real^3))*(norm(v':real^3))*cos(c:real)=(d':real) pow 2` ASSUME_TAC THENL 
    [UNDISCH_TAC `norm(u':real^3) = norm(v':real^3)` THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    SIMP_TAC[REAL_ARITH `(a:real) + a - b = &2 * a - b`;REAL_ARITH `(a:real) * b * b * c = (a * c) * ((b) pow 2)`;NORM_POW_2;GSYM DOT_LMUL] THEN 
    UNDISCH_TAC `(d':real) pow 2 = &2 % (v':real^3) dot v' - (&2 * cos(c:real)) % v' dot v'`  THEN 
    SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_ARITH `(a:real) + b - c = d <=> c = a + b - d`;REAL_MUL_ASSOC] THEN  
    SUBGOAL_THEN ` &0 < (&2 * (norm (u':real^3))) * (norm (v':real^3))` ASSUME_TAC THENL 
    [SIMP_TAC[GSYM REAL_MUL_ASSOC;GSYM (REAL_ARITH` &0 < x <=> &0 < &2 * x`)] THEN
    UNDISCH_TAC `~((v':real^3) = vec 0)` THEN UNDISCH_TAC `~((u':real^3) = vec 0)` THEN 
    SIMP_TAC[GSYM NORM_POS_LT] THEN MP_TAC (ISPECL[`norm(u':real^3)`;`&0`;`norm(v':real^3)`] REAL_LT_LMUL) THEN 
    SIMP_TAC[REAL_MUL_RZERO];ALL_TAC] THEN POP_ASSUM MP_TAC THEN 
    SIMP_TAC[REAL_FIELD `!a b c.  &0 <a ==> ( a * b = c <=> b = c / a)`] THEN STRIP_TAC THEN 
    ONCE_REWRITE_TAC[GSYM COS_ABS] THEN 
    DISCH_THEN (MP_TAC o SYM) THEN SIMP_TAC[] THEN STRIP_TAC THEN 
    UNDISCH_TAC `(abs c) <= pi` THEN UNDISCH_TAC ` &0 <=(abs c)` THEN 
    SIMP_TAC[ACS_COS] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC ` c < &0` THEN 
    SIMP_TAC[REAL_ABS_REFL_NEG] THEN STRIP_TAC THEN 
    ASM_SIMP_TAC[REAL_ARITH `(a:real) = a0 + -- c <=> c = a0 - a`]]);;

let gst_a = new_definition
    `gst_a a1 s1 a2 s2 a3 s3 a4 s4 x = 
     matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp((a2:real) %% screw_2_matrix s2) ** 
     matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4) ** (gst_initial x)`;;               

let GST_A = prove              
     (`!s1 s2 s3 s4 s5:screw gd:real^(3,1)finite_sum^(3,1)finite_sum a1 a2 a3 a4 a5 a6:real.
       gst_a a1 s1 a2 s2 a3 s3 a4 s4 x = gd ==>
       gd = matrix_exp(a1 %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** 
       matrix_exp(a3 %% screw_2_matrix s3) ** matrix_exp(a4 %% screw_2_matrix s4) ** (gst_initial x)`,
       REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[gst_a]);;

let g_1 = new_definition
    `g_1 a2 s2 a3 s3 a4 s4 = matrix_exp((a2:real) %% screw_2_matrix s2) ** 
     matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4)`;;  

let G1 = prove
    (`!a1 a2 a3 a4:real s1 s2 s3 s4:screw x:real^3 gd:real^(3,1)finite_sum^(3,1)finite_sum.
    gst_a a1 s1 a2 s2 a3 s3 a4 s4 x = gd ==>
    matrix_exp(-- (a1) %% screw_2_matrix s1) ** gd ** (matrix_inv (gst_initial x)) = (g_1 a2 s2 a3 s3 a4 s4)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `matrix_exp(-- (a1) %% screw_2_matrix s1) ** gst_a a1 s1 a2 s2 a3 s3 a4 s4 x ** (matrix_inv (gst_initial x)) =
                              (g_1 a2 s2 a3 s3 a4 s4)` ASSUME_TAC THENL
    [SIMP_TAC[gst_a;g_1;GSYM MATRIX_MUL_ASSOC;INVERTIBLE_GST_INITIAL;
                     MATRIX_INV;MATRIX_MUL_RID] THEN
    SUBGOAL_THEN `-- (a1:real) %% screw_2_matrix (s1:screw)** (a1 %% screw_2_matrix s1)
                  = (a1 %% screw_2_matrix s1) ** -- (a1:real) %% screw_2_matrix (s1:screw)` ASSUME_TAC THENL
    [SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN 
    ASM_SIMP_TAC[MATRIX_MUL_ASSOC;GSYM MATRIX_EXP_ADD;MATRIX_CMUL_LNEG;MATRIX_ARITH `--A + A = mat 0`;
                             MATRIX_EXP_0;MATRIX_MUL_LID];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[]);;

let G2 = prove
    (`!a2 a3 a4:real s2 s3 s4:screw.
    matrix_exp(a2 %% screw_2_matrix s2) = (g_1 a2 s2 a3 s3 a4 s4) ** matrix_exp(-- (a4) %% screw_2_matrix s4) ** matrix_exp(-- (a3) %% screw_2_matrix s3)`,                
    REPEAT GEN_TAC THEN  
    SUBGOAL_THEN `(g_1 a2 s2 a3 s3 a4 s4) ** matrix_exp(-- (a4:real) %% screw_2_matrix s4) =
                               matrix_exp((a2:real) %% screw_2_matrix s2) ** matrix_exp((a3:real) %% screw_2_matrix s3)` ASSUME_TAC THENL
    [SIMP_TAC[g_1;GSYM MATRIX_MUL_ASSOC] THEN
    SUBGOAL_THEN `invertible (matrix_exp ((a4:real) %% screw_2_matrix s4))` ASSUME_TAC THENL
    [SIMP_TAC[INVERTIBLE_MATRIX_EXP];ALL_TAC] THEN 
    ASM_SIMP_TAC[MATRIX_CMUL_LNEG;GSYM MATRIX_EXP_INV;MATRIX_INV;MATRIX_MUL_RID];ALL_TAC] THEN 
    ASM_SIMP_TAC[MATRIX_MUL_ASSOC] THEN 
    SUBGOAL_THEN `invertible (matrix_exp ((a3:real) %% screw_2_matrix s3))` ASSUME_TAC THENL
    [SIMP_TAC[INVERTIBLE_MATRIX_EXP];ALL_TAC] THEN 
    ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC;MATRIX_CMUL_LNEG;GSYM MATRIX_EXP_INV;MATRIX_INV;MATRIX_MUL_RID]);;

let SOLUTION_OF_A1 = prove
    (`!a1 a2 a3 a4 h1 h2 h3 h4 px py.
    px = cos(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4)) /\
    py = sin(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4))  /\
    a1 = atn((cos(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4)))/(sin(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4)))) ==>
    a1 = atn(px/py)`,
    REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `px = cos(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4))` THEN
    UNDISCH_TAC `py = sin(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4))` THEN 
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN 
    UNDISCH_TAC `a1 = atn((cos(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4)))/(sin(a1) * (h1 + h2 * cos(a2) +h3 * cos(a2+a3)+h4 * cos(a2+a3+a4))))` THEN 
    SIMP_TAC[]);;

let SOLUTION_OF_A2 = prove
    (`!a2 a3 a4:real s2 s3 s4:screw p':real^3 g2:real^(3,1)finite_sum^(3,1)finite_sum.
      g2 = (g_1 a2 s2 a3 s3 a4 s4) ** matrix_exp(-- (a4) %% screw_2_matrix s4) ** matrix_exp(-- (a3) %% screw_2_matrix s3) ==>
     matrix_exp(a2 %% screw_2_matrix s2) ** homo_point (mk_point p') = g2** homo_point (mk_point p')`,      
     REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[G2] THEN ASM_SIMP_TAC[]);;

let SOLUTION_OF_A3 = prove
    (`!p q:real^3 s2 s3 s4:screw a2 a3 a4.
    (matrix_exp((a2) %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point p)) /\ 
     matrix_exp(a2 %% screw_2_matrix s2) ** (matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q)) -
    (homo_point (mk_point p))) = matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q)) - (homo_point (mk_point p)) /\ 
    matrix_exp((a4) %% screw_2_matrix s4) ** (homo_point (mk_point q)) = (homo_point (mk_point q))) ==>
    norm(matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q)) - (homo_point (mk_point p))) = 
    norm(g_1 a2 s2 a3 s3 a4 s4 ** (homo_point (mk_point q)) - (homo_point (mk_point p)))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ` matrix_exp((a2:real) %% screw_2_matrix s2) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** 
                                matrix_exp((a4:real) %% screw_2_matrix s4) ** (homo_point (mk_point (q:real^3))) = 
                                matrix_exp(a2 %% screw_2_matrix s2) ** matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q))` ASSUME_TAC THENL 
    [AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[];ALL_TAC] THEN 
    POP_ASSUM MP_TAC THEN SIMP_TAC[g_1;GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    STRIP_TAC THEN 
    SUBGOAL_THEN ` (matrix_exp((a2:real) %% screw_2_matrix (s2:screw)) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** 
                                (homo_point (mk_point (q:real^3)))) - (homo_point (mk_point (p:real^3))) = 
                                matrix_exp(a2 %% screw_2_matrix s2) ** (matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q)) -
                                (homo_point (mk_point p)))` ASSUME_TAC THENL 
    [UNDISCH_TAC `matrix_exp((a2:real) %% screw_2_matrix (s2:screw)) ** (homo_point (mk_point (p:real^3))) = (homo_point (mk_point p))` THEN 
     SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB];ALL_TAC] THEN
    SUBGOAL_THEN ` (matrix_exp((a2:real) %% screw_2_matrix (s2:screw)) ** matrix_exp((a3:real) %% screw_2_matrix s3) ** 
                                (homo_point (mk_point (q:real^3)))) - (homo_point (mk_point (p:real^3))) = 
                                matrix_exp((a3:real) %% screw_2_matrix s3) ** 
                                (homo_point (mk_point (q:real^3))) - (homo_point (mk_point p))` ASSUME_TAC THENL 
    [ASM_SIMP_TAC[];ALL_TAC] THEN ASM_SIMP_TAC[]);;

let ga = new_definition
    `ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x = 
     matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp((a2:real) %% screw_2_matrix s2) ** 
     matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4) ** 
     matrix_exp((a5:real) %% screw_2_matrix s5) **(gst_initial x)`;;  

let SOLUTION_OF_A5 = prove
     (`!h2 a1 a2 a3 a4 a5:real s1 s2 s3 s4 s5:screw g_d:real^(3,1)finite_sum^(3,1)finite_sum pw q:real^3.
     ((matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2)) ** 
     ((homo_point (mk_point pw)) - (homo_point (mk_point q))) = (homo_point (mk_point pw)) - (homo_point (mk_point q)) /\
     matrix_exp((a3) %% screw_2_matrix s3) ** matrix_exp((a4) %% screw_2_matrix s4) ** 
     (homo_point (mk_point pw)) = (homo_point (mk_point pw)) /\
     matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
     (homo_point (mk_point q)) = (homo_point (mk_point q)) /\ 
      g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x)==>
     norm((homo_point (mk_point pw)) - (homo_point (mk_point q))) = norm(g_d ** (matrix_inv (gst_initial x)) ** matrix_exp(--a5 %% screw_2_matrix s5) **
     (homo_point (mk_point pw)) - (homo_point (mk_point q)))`,
     REPEAT STRIP_TAC THEN 
     SUBGOAL_THEN `matrix_exp((a1:real) %% screw_2_matrix s1) ** matrix_exp((a2:real) %% screw_2_matrix s2) ** 
                                matrix_exp((a3:real) %% screw_2_matrix s3) ** matrix_exp((a4:real) %% screw_2_matrix s4) =
                                g_d ** (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[ga] THEN SIMP_TAC[GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN 
     AP_TERM_TAC THEN AP_TERM_TAC THEN 
     SUBGOAL_THEN `gst_initial x ** matrix_inv (gst_initial x) ** matrix_exp (--a5 %% screw_2_matrix s5) = 
                                matrix_exp (--a5 %% screw_2_matrix s5)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_MUL_ASSOC;INVERTIBLE_GST_INITIAL;MATRIX_INV;MATRIX_MUL_LID];ALL_TAC] THEN 
     ASM_SIMP_TAC[] THEN 
     SUBGOAL_THEN `(--a5 %% screw_2_matrix s5)** (a5 %% screw_2_matrix s5)
                                = (a5 %% screw_2_matrix s5) ** (--a5%% screw_2_matrix s5)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN 
     ASM_SIMP_TAC[GSYM MATRIX_EXP_ADD;MATRIX_CMUL_LNEG;MATRIX_ARITH `A + --A = mat 0`;
                              MATRIX_EXP_0;MATRIX_MUL_RID];ALL_TAC] THEN 
     SUBGOAL_THEN `matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
                               (homo_point (mk_point pw)) = g_d ** (matrix_inv (gst_initial x)) ** 
                               matrix_exp(-- (a5) %% screw_2_matrix s5) ** (homo_point (mk_point pw))` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN 
     SIMP_TAC[GSYM MATRIX_MUL_ASSOC] THEN SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN 
     STRIP_TAC THEN 
     UNDISCH_TAC `matrix_exp((a3) %% screw_2_matrix s3) ** matrix_exp((a4) %% screw_2_matrix s4) ** 
                             (homo_point (mk_point pw)) = (homo_point (mk_point pw))` THEN SIMP_TAC[];ALL_TAC] THEN 
     SUBGOAL_THEN `matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
                               (homo_point (mk_point pw)) - (homo_point (mk_point q))= 
                               (matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2)) ** 
                               ((homo_point (mk_point pw)) - (homo_point (mk_point q)))` ASSUME_TAC THENL
     [UNDISCH_TAC `matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
                              (homo_point (mk_point q)) = (homo_point (mk_point q))` THEN 
     SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB;GSYM MATRIX_VECTOR_MUL_ASSOC];ALL_TAC] THEN 
     UNDISCH_TAC `matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
                             (homo_point (mk_point pw)) = g_d ** (matrix_inv (gst_initial x)) ** 
                              matrix_exp(-- (a5) %% screw_2_matrix s5) ** (homo_point (mk_point pw))` THEN 
     DISCH_THEN(MP_TAC o SYM) THEN SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN 
     UNDISCH_TAC `matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
                             (homo_point (mk_point pw)) - (homo_point (mk_point q))= 
                             (matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2)) ** 
                             ((homo_point (mk_point pw)) - (homo_point (mk_point q)))` THEN 
     UNDISCH_TAC `(matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2)) ** 
                             ((homo_point (mk_point pw)) - (homo_point (mk_point q))) = 
                             (homo_point (mk_point pw)) - (homo_point (mk_point q))` THEN SIMP_TAC[]);;

let SOLUTION_OF_A1_A2 = prove
    (`!s1 s2 s3 s4 s5:screw a1 a2 a3 a4 a5:real pw x:real^3 g_d:real^(3,1)finite_sum^(3,1)finite_sum ga_2:real^(3,1)finite_sum.
     (g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x /\
     matrix_exp((a3) %% screw_2_matrix s3) ** matrix_exp((a4) %% screw_2_matrix s4) ** 
     (homo_point (mk_point pw)) = (homo_point (mk_point pw)) /\
     ga_2 = g_d ** (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5) ** 
                (homo_point (mk_point pw))) ==>
     matrix_exp((a1) %% screw_2_matrix s1) ** matrix_exp((a2) %% screw_2_matrix s2) ** 
                               (homo_point (mk_point pw)) = ga_2`,
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ga] THEN SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN 
     AP_TERM_TAC THEN  AP_TERM_TAC THEN
     SUBGOAL_THEN `gst_initial x ** matrix_inv (gst_initial x) ** matrix_exp (--a5 %% screw_2_matrix s5) ** (homo_point (mk_point pw)) = 
                                matrix_exp (--a5 %% screw_2_matrix s5) ** (homo_point (mk_point pw))` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;INVERTIBLE_GST_INITIAL;MATRIX_INV;MATRIX_MUL_LID];ALL_TAC] THEN 
     POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN 
     SUBGOAL_THEN `(--a5 %% screw_2_matrix s5)** (a5 %% screw_2_matrix s5)
                                = (a5 %% screw_2_matrix s5) ** (--a5%% screw_2_matrix s5)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN 
     SUBGOAL_THEN `matrix_exp (a5 %% screw_2_matrix s5) ** matrix_exp (--a5 %% screw_2_matrix s5) ** 
                               (homo_point (mk_point pw)) = (homo_point (mk_point pw))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_EXP_ADD;MATRIX_CMUL_LNEG;MATRIX_ARITH `A + --A = mat 0`;
                              MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN 
     POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[]);;

let SOLUTION_OF_A3_A4 = prove
    (`!s1 s2 s3 s4 s5:screw a1 a2 a3 a4 a5:real p q x:real^3 g_d:real^(3,1)finite_sum^(3,1)finite_sum.
     (g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x /\
     q = matrix_exp(-- (a2) %% screw_2_matrix s2) ** matrix_exp(-- (a1) %% screw_2_matrix s1) ** g_d **
            (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5) ** 
                (homo_point (mk_point p))) ==>
     matrix_exp((a3) %% screw_2_matrix s3) ** matrix_exp((a4) %% screw_2_matrix s4) ** 
                               (homo_point (mk_point p)) = q`,
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ga;GSYM MATRIX_VECTOR_MUL_ASSOC] THEN 
     SUBGOAL_THEN `gst_initial x ** matrix_inv (gst_initial x) ** matrix_exp (--a5 %% screw_2_matrix s5) ** (homo_point (mk_point p)) = 
                                matrix_exp (--a5 %% screw_2_matrix s5) ** (homo_point (mk_point p))` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;INVERTIBLE_GST_INITIAL;MATRIX_INV;MATRIX_MUL_LID];ALL_TAC] THEN 
     POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN 
     SUBGOAL_THEN `(--a5 %% screw_2_matrix s5)** (a5 %% screw_2_matrix s5)
                                = (a5 %% screw_2_matrix s5) ** (--a5%% screw_2_matrix s5)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN 
     SUBGOAL_THEN `matrix_exp (a5 %% screw_2_matrix s5) ** matrix_exp (--a5 %% screw_2_matrix s5) ** 
                               (homo_point (mk_point p)) = (homo_point (mk_point p))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_EXP_ADD;MATRIX_CMUL_LNEG;MATRIX_ARITH `A + --A = mat 0`;
                              MATRIX_EXP_0;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN 
     POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN 
     SUBGOAL_THEN ` matrix_exp (--a2 %% screw_2_matrix s2) ** matrix_exp (--a1 %% screw_2_matrix s1) **
                                 matrix_exp (a1 %% screw_2_matrix s1) ** matrix_exp (a2 %% screw_2_matrix s2) = mat 1` ASSUME_TAC THENL
     [SUBGOAL_THEN ` matrix_exp (--a1 %% screw_2_matrix s1) **matrix_exp (a1 %% screw_2_matrix s1) ** 
                                  matrix_exp (a2 %% screw_2_matrix s2) = matrix_exp (a2 %% screw_2_matrix s2)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_MUL_ASSOC] THEN 
      SUBGOAL_THEN `(--a1 %% screw_2_matrix s1)** (a1 %% screw_2_matrix s1)
                                = (a1 %% screw_2_matrix s1) ** (--a1%% screw_2_matrix s1)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN 
      ASM_SIMP_TAC[MATRIX_MUL_ASSOC;GSYM MATRIX_EXP_ADD;MATRIX_CMUL_LNEG;MATRIX_ARITH `--A + A = mat 0`;
                              MATRIX_EXP_0;MATRIX_MUL_LID];ALL_TAC] THEN ASM_SIMP_TAC[] THEN 
      SUBGOAL_THEN `(--a2 %% screw_2_matrix s2)** (a2 %% screw_2_matrix s2)
                                = (a2 %% screw_2_matrix s2) ** (--a2%% screw_2_matrix s2)` ASSUME_TAC THENL
     [SIMP_TAC[MATRIX_CMUL_LNEG;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG];ALL_TAC] THEN 
      ASM_SIMP_TAC[MATRIX_MUL_ASSOC;GSYM MATRIX_EXP_ADD;MATRIX_CMUL_LNEG;MATRIX_ARITH `--A + A = mat 0`;
                              MATRIX_EXP_0];ALL_TAC] THEN 
      ASM_MESON_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_VECTOR_MUL_LID]);;


(* solutions of index finger *)

let SOLUTION_OF_A2_ALT = prove
    (`!a2 a3 a4:real s2 s3 s4:screw p':real^3 
      w r u u' v v' q g2:real^(3,1)finite_sum^(3,1)finite_sum.
      g2 = (g_1 a2 s2 a3 s3 a4 s4) ** matrix_exp(-- (a4) %% screw_2_matrix s4) ** matrix_exp(-- (a3) %% screw_2_matrix s3) /\
      homo_point (mk_point q) = g2** homo_point (mk_point p') /\
      (--(pi / &2) < a2 /\ a2 < pi / &2) /\
      s2 = w,r cross w /\
      norm w = &1 /\
      u = p' - r /\
      v = q - r /\
      u' = u - vec3_vtrans (FST s2) ** u /\
      v' = v - vec3_vtrans (FST s2) ** v /\
      matrix_exp (a2 %% screw_2_matrix s2) ** homo_point (mk_point r) =
      homo_point (mk_point r) /\
      ~(u' = vec 0)
      ==>
      a2 = atn ((w dot (u' cross v')) / (u' dot v'))`, 
      INTRO_TAC "! *; g2 q cond " THEN
      MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_1 THEN
      MAP_EVERY EXISTS_TAC [`r:real^3`;`u:real^3`;`v:real^3`;`p':real^3`;`q:real^3`;`s2:screw`] THEN
      REMOVE_THEN "q" SUBST1_TAC THEN
      ASM_MESON_TAC[SOLUTION_OF_A2]);;
      
let RODRIGUES_FORMULA_MUL_SSM_2 = prove
    (`!a w. norm w = &1 ==>
    (mat 1 - matrix_exp (a %% vec3_2_ssm w)) ** vec3_2_ssm w ** vec3_2_ssm w
     = matrix_exp (a %% vec3_2_ssm w) - mat 1`,
     REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC[RODRIGUES_FORMULA;MATRIX_SUB_RDISTRIB;MATRIX_ADD_RDISTRIB] THEN
     SIMP_TAC[MATRIX_MUL_LID;GSYM MATRIX_POW_2;MATRIX_MUL_LMUL;GSYM MATRIX_POW_ADD] THEN
     SIMP_TAC[GSYM matrix_pow;ARITH_RULE `SUC 2 = 3`] THEN
     ASM_SIMP_TAC[matrix_pow;ARITH_RULE `2 + 2 = 1 + 3`;SSM_POW_CYCLICITY;SSM_POW_3;ARITH_RULE `(1 + 1) = 2`] THEN
     MATRIX_ARITH_TAC);;
     
let HOMO_POINT_SUB_EQ_VECTOR = prove
    (`!p q. homo_point(mk_point p) - homo_point(mk_point q) = homo_vector(p - q)`,
    SIMP_TAC[HOMO_POINT_MK_POINT;CART_EQ;LAMBDA_BETA;homo_vector;VECTOR_SUB_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN SIMP_TAC[] THEN REAL_ARITH_TAC);;
    
let NORM_HOMO_VECTOR = prove
    (`!v. norm(homo_vector v) = norm v`,
    SIMP_TAC[NORM_EQ;dot;homo_vector;LAMBDA_BETA] THEN
    GEN_TAC THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    SIMP_TAC[FINITE_NUMSEG;SUBSET;IN_NUMSEG;DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x <= N ==> x <= N + 1`;ARITH_RULE `x <= N ==> ~(x = N + 1)`] THEN
    SIMP_TAC[ARITH_RULE `1 <= x /\ x <= N + 1 <=> (1 <= x /\ x <= N) \/ x = N + 1`] THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;
      
let SOLUTION_OF_A3_ALT = prove
    (`!p q:real^3 s2 s3 s4:screw a2 a3 a4 w r u u' v v' d a0 c d'.
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point(mk_point p)) = (homo_point(mk_point p)) /\ 
     matrix_exp(a2 %% screw_2_matrix s2) ** (matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point(mk_point q)) -
    (homo_point(mk_point p))) = matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q)) - (homo_point (mk_point p)) /\ 
    matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point q)) = (homo_point (mk_point q)) /\ 
    d = norm(g_1 a2 s2 a3 s3 a4 s4 ** (homo_point (mk_point q)) - (homo_point (mk_point p))) /\
    ((--(pi / &2) < a0 /\ a0 < pi / &2) /\
     (--(pi / &2) < a3 /\ a3 < pi / &2) /\
     &0 <= abs c /\ abs c <= pi /\
     s3 = w,r cross w /\
     norm w = &1 /\
     u = q - r /\
     v = p - r /\
     c = a0 - a3 /\
     u' = u - vec3_vtrans (FST s3) ** u /\
     v' = v - vec3_vtrans (FST s3) ** v /\
     ~(u' = vec 0) /\
     ~(v' = vec 0)) /\
     matrix_exp (a0 %% screw_2_matrix s3) ** homo_point (mk_point q) =
       homo_point (mk_point p) /\
     d' pow 2 = d pow 2 - abs (w dot (q - p)) pow 2
     ==> (&0 <= c
              ==> a3 =
                  a0 -
                  acs
                  ((norm u' pow 2 + norm v' pow 2 - d' pow 2) /
                   (&2 * norm u' * norm v'))) /\
             (c < &0
              ==> a3 =
                  a0 +
                  acs
                  ((norm u' pow 2 + norm v' pow 2 - d' pow 2) /
                   (&2 * norm u' * norm v')))`,
    INTRO_TAC "! *; eq1 eq2 eq3 d cond " THEN
    SUBGOAL_THEN `norm(FST (s3:screw)) = &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[];ALL_TAC] THEN 
    SUBGOAL_THEN `(vec3_vtrans w ** (r cross w)) = vec 0` ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[CROSS_SKEW] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_RNEG;CROSS_SSM;SSM_RMUL_EQ_0;MATRIX_VECTOR_MUL_ASSOC;MATRIX_VECTOR_MUL_LZERO;VECTOR_NEG_0]
     ;ALL_TAC] THEN
    SUBGOAL_THEN `matrix_exp (a0 %% screw_2_matrix s3) ** homo_point (mk_point r) = homo_point (mk_point r)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE] THEN
     SIMP_TAC[VECTOR_MUL_RZERO;VECTOR_ADD_RID] THEN
     ONCE_REWRITE_TAC[CROSS_SSM] THEN
     ONCE_REWRITE_TAC[CROSS_SKEW] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_RNEG;CROSS_SSM;MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_MUL_ASSOC] THEN
     ASM_SIMP_TAC[RODRIGUES_FORMULA_MUL_SSM_2] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID] THEN
     VECTOR_ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `d pow 2 = norm (v - matrix_exp (a3 %% vec3_2_ssm w) ** u) pow 2` ASSUME_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN
     REMOVE_THEN "d" SUBST1_TAC THEN
     MP_TAC (ISPECL [`p:real^3`;`q:real^3`;`s2:screw`;`s3:screw`;`s4:screw`;`a2:real`;`a3:real`;`a4:real`] SOLUTION_OF_A3) THEN 
     ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     ASM_SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN     
     REMOVE_THEN "cond" MP_TAC THEN
     STRIP_TAC THEN
     ASM_SIMP_TAC[MATRIX_EXP_SCREW_COND_1;HOMO_TRANS_MUL_POINT;HOMO_POINT_MK_POINT_UNIQUE] THEN
     ASM_SIMP_TAC[VECTOR_MUL_RZERO;VECTOR_ADD_RID] THEN
     ONCE_REWRITE_TAC[CROSS_SSM] THEN
     ONCE_REWRITE_TAC[CROSS_SKEW] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_RNEG;CROSS_SSM;MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_MUL_ASSOC] THEN
     ASM_SIMP_TAC[RODRIGUES_FORMULA_MUL_SSM_2] THEN
     SIMP_TAC[HOMO_POINT_SUB_EQ_VECTOR;NORM_HOMO_VECTOR] THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NORM_SUB] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;VECTOR_ARITH `p:real^N - (q + --(r1 - r2)) = p - r2 - (q - r1)`;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN
    MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_3 THEN
    MAP_EVERY EXISTS_TAC [`w:real^3`;`r:real^3`;`u:real^3`;`v:real^3`;`q:real^3`;`p:real^3`;`s3:screw`;`d:real`] THEN
    ASM_SIMP_TAC[]);;
    
let SOLUTION_OF_A4_ALT = prove
    (`!p q:real^3 s2 s3 s4:screw a2 a3 a4 w r u u' v v' d a0 c d'.
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point(mk_point p)) = (homo_point(mk_point p)) /\ 
     matrix_exp(a2 %% screw_2_matrix s2) ** (matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point(mk_point q)) -
    (homo_point(mk_point p))) = matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point q)) - (homo_point (mk_point p)) /\ 
    matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point q)) = (homo_point (mk_point q)) /\ 
    d = norm(g_1 a2 s2 a3 s3 a4 s4 ** (homo_point (mk_point q)) - (homo_point (mk_point p))) /\
    ((--(pi / &2) < a0 /\ a0 < pi / &2) /\
     (--(pi / &2) < a3 /\ a3 < pi / &2) /\
     &0 <= abs c /\ abs c <= pi /\
     s3 = w,r cross w /\
     norm w = &1 /\
     u = q - r /\
     v = p - r /\
     c = a0 - a3 /\
     u' = u - vec3_vtrans (FST s3) ** u /\
     v' = v - vec3_vtrans (FST s3) ** v /\
     ~(u' = vec 0) /\
     ~(v' = vec 0)) /\
     matrix_exp (a0 %% screw_2_matrix s3) ** homo_point (mk_point q) =
       homo_point (mk_point p) /\
     d' pow 2 = d pow 2 - abs (w dot (q - p)) pow 2 /\
     a3 = a4
     ==> (&0 <= c
              ==> a4 =
                  a0 -
                  acs
                  ((norm u' pow 2 + norm v' pow 2 - d' pow 2) /
                   (&2 * norm u' * norm v'))) /\
             (c < &0
              ==> a4 =
                  a0 +
                  acs
                  ((norm u' pow 2 + norm v' pow 2 - d' pow 2) /
                   (&2 * norm u' * norm v')))`,
    MESON_TAC[SOLUTION_OF_A3_ALT]);;
    
(* solutions of thumb *)

let PADEN_KAHAN_SUB_PRO_2_ALT = prove
    (`!w1 w2 r u u' v v' p q c:real^3 k1 k2 k3:real z:real^3 a1 a2 x1 x2 x3:real s1 s2:screw z1 z2:real^3 a:real.
    (--(pi / &2) < a /\ a < pi / &2) /\
    (--(pi / &2) < a1 /\ a1 < pi / &2) /\
    (--(pi / &2) < a2 /\ a2 < pi / &2) /\
    s1 = (w1, r cross (w1)) /\ s2 = (w2, r cross (w2)) /\
    norm w1 = &1 /\ norm w2 = &1 /\
    u = p - r /\ v = q - r /\ z = c - r /\
    u' = u - (vec3_vtrans (FST s2) ** u) /\
    v' = v - (vec3_vtrans (FST s1) ** v) /\ 
    k1 = w1 dot w2 /\ k2 = w2 dot u /\ k3 = w1 dot v /\
    x1 = (k1 * k2 - k3) / (k1 pow 2 - &1) /\
    x2 = (k1 * k3 - k2) / (k1 pow 2 - &1) /\
    abs(x3) = sqrt(norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm (w1 cross w2)) /\
    ~((norm(w1 cross w2)) pow 2  = &0) /\ ~((w1 dot w2) pow 2 - &1 = &0) /\
    z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2) /\
    (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * k1 + (x3 pow 2) * (norm(w1 cross w2)) pow 2 /\ 
    matrix_exp(a1 %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point c)) /\
    matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
    matrix_exp(a1 %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point q)) /\ 
    a = a1 + a2 /\ ~(u' = vec 0) /\ ~(v' = vec 0) /\
    z1 = z - vec3_vtrans w1 ** z /\
    z2 = z - vec3_vtrans w2 ** z
    ==>
    a = atn((w2 dot (u' cross z2)) / (u' dot z2)) 
        - atn((w1 dot (v' cross z1)) / (v' dot z1))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (ISPECL [`w1:real^3`;`w2:real^3`;`r:real^3`;`u:real^3`;`u':real^3`; `v:real^3`; `v':real^3`; `p:real^3`; `q:real^3`; `c:real^3`; `z:real^3`; `a:real`; `a1:real`; `a2:real`; `x1:real`; `x2:real`; `x3:real`; `s1:screw`; `s2:screw`] PADEN_KAHAN_SUB_PRO_2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    UNDISCH_THEN `k1 = (w1:real^3) dot w2` (LABEL_TAC "k1" o SYM) THEN
    UNDISCH_THEN `k2 = (w2:real^3) dot u` (LABEL_TAC "k2" o SYM) THEN
    UNDISCH_THEN `k3 = (w1:real^3) dot v` (LABEL_TAC "k3" o SYM) THEN
    UNDISCH_THEN `x1 = (k1 * k2 - k3) / (k1 pow 2 - &1)` (LABEL_TAC "x1" o SYM) THEN
    UNDISCH_THEN `x2 = (k1 * k3 - k2) / (k1 pow 2 - &1)` (LABEL_TAC "x2" o SYM) THEN
    UNDISCH_THEN `abs(x3) = sqrt(norm (u:real^3) pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm ((w1:real^3) cross w2))` (LABEL_TAC "x3" o SYM) THEN
    USE_THEN "k1" SUBST1_TAC THEN
    USE_THEN "k2" SUBST1_TAC THEN
    USE_THEN "k3" SUBST1_TAC THEN
    USE_THEN "x1" SUBST1_TAC THEN
    USE_THEN "x2" SUBST1_TAC THEN
    ASM_CASES_TAC `&0 <= x3` THENL
    [USE_THEN "x3" MP_TAC THEN
     POP_ASSUM MP_TAC THEN
     SIMP_TAC[REAL_ARITH `&0 <= x ==> ~(x < &0)`;SQRT_DIV;POW_2_SQRT;NORM_POS_LE] THEN
     SIMP_TAC[GSYM REAL_ABS_REFL] THEN
     STRIP_TAC THEN STRIP_TAC THEN
     UNDISCH_THEN `z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2)` (SUBST1_TAC o SYM) THEN
     UNDISCH_THEN `z1 = z - vec3_vtrans w1 ** z` (SUBST1_TAC o SYM) THEN
     UNDISCH_THEN `z2 = z - vec3_vtrans w2 ** z` (SUBST1_TAC o SYM) THEN
     REAL_ARITH_TAC;ALL_TAC] THEN
    USE_THEN "x3" MP_TAC THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> x < &0`;SQRT_DIV;POW_2_SQRT;NORM_POS_LE] THEN
    SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> abs(x) = --x`;VECTOR_ARITH `x - (--k)% y:real^N = x + k % y`] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_THEN `z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2)` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `z1 = z - vec3_vtrans w1 ** z` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `z2 = z - vec3_vtrans w2 ** z` (SUBST1_TAC o SYM) THEN
    REAL_ARITH_TAC);;
    
let SOLUTION_OF_A1_A2_ALT = prove
    (`!s1 s2 s3 s4 s5:screw a1 a2 a3 a4 a5:real pw x:real^3 g_d:real^(3,1)finite_sum^(3,1)finite_sum ga_2:real^(3,1)finite_sum
     w1 w2 r u u' v v' q c:real^3 k1 k2 k3:real z a x1 x2 x3:real z1 z2:real^3.
     (g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x /\
     matrix_exp(a3 %% screw_2_matrix s3) ** matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point(mk_point pw)) = (homo_point(mk_point pw)) /\
     ga_2 = g_d ** (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5) ** (homo_point (mk_point pw))) /\
     (homo_point (mk_point q)) = ga_2 /\ 
     (--(pi / &2) < a /\ a < pi / &2) /\
     (--(pi / &2) < a1 /\ a1 < pi / &2) /\
     (--(pi / &2) < a2 /\ a2 < pi / &2) /\
     s1 = (w1, r cross (w1)) /\ s2 = (w2, r cross (w2)) /\
     norm w1 = &1 /\ norm w2 = &1 /\
     u = pw - r /\ v = q - r /\ z = c - r /\
     u' = u - (vec3_vtrans (FST s2) ** u) /\
     v' = v - (vec3_vtrans (FST s1) ** v) /\ 
     k1 = w1 dot w2 /\ k2 = w2 dot u /\ k3 = w1 dot v /\
     x1 = (k1 * k2 - k3) / (k1 pow 2 - &1) /\
     x2 = (k1 * k3 - k2) / (k1 pow 2 - &1) /\
     abs(x3) = sqrt(norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm (w1 cross w2)) /\
     ~((norm(w1 cross w2)) pow 2  = &0) /\ ~((w1 dot w2) pow 2 - &1 = &0) /\
     z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2) /\
     (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * k1 + (x3 pow 2) * (norm(w1 cross w2)) pow 2 /\ 
     matrix_exp(a1 %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point pw)) = (homo_point (mk_point c)) /\
     matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
     a = a1 + a2 /\ ~(u' = vec 0) /\ ~(v' = vec 0) /\
     z1 = z - vec3_vtrans w1 ** z /\
     z2 = z - vec3_vtrans w2 ** z ==>           
     a = atn( (w2 dot (u' cross z2)) / (u' dot z2)) 
             - atn((w1 dot (v' cross z1)) / (v' dot z1))`,
     INTRO_TAC "! *; eq1 eq2 eq3 q cond" THEN
     SUBGOAL_THEN `matrix_exp(a1 %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point pw)) = ga_2` ASSUME_TAC THENL
     [MATCH_MP_TAC SOLUTION_OF_A1_A2 THEN
      ASM_MESON_TAC[];ALL_TAC] THEN
     MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_2_ALT THEN
     MAP_EVERY EXISTS_TAC [`r:real^3`;`u:real^3`;`v:real^3`;`pw:real^3`;`q:real^3`;`c:real^3`;`k1:real`;`k2:real`;`k3:real`;`z:real^3`;`a1:real`; `a2:real`; `x1:real`; `x2:real`;`x3:real`; `s1:screw`; `s2:screw`] THEN
     REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;
      
let SOLUTION_OF_A3_A4_ALT = prove
    (`!s1 s2 s3 s4 s5:screw a1 a2 a3 a4 a5:real p q x:real^3 g_d:real^(3,1)finite_sum^(3,1)finite_sum 
    w3 w4 r u u' v v' q c:real^3 k1 k2 k3:real z:real^3 a x1 x2 x3:real z3 z4:real^3.
     (g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x /\
     (homo_point (mk_point q)) = matrix_exp(-- (a2) %% screw_2_matrix s2) ** matrix_exp(-- (a1) %% screw_2_matrix s1) ** g_d **
            (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5) ** 
                (homo_point (mk_point p))) /\
     (--(pi / &2) < a /\ a < pi / &2) /\
     (--(pi / &2) < a3 /\ a3 < pi / &2) /\
     (--(pi / &2) < a4 /\ a4 < pi / &2) /\
     s3 = (w3, r cross (w3)) /\ s4 = (w4, r cross (w4)) /\
     norm w3 = &1 /\ norm w4 = &1 /\
     u = p - r /\ v = q - r /\ z = c - r /\
     u' = u - (vec3_vtrans (FST s4) ** u) /\
     v' = v - (vec3_vtrans (FST s3) ** v) /\ 
     k1 = w3 dot w4 /\ k2 = w4 dot u /\ k3 = w3 dot v /\
     x1 = (k1 * k2 - k3) / (k1 pow 2 - &1) /\
     x2 = (k1 * k3 - k2) / (k1 pow 2 - &1) /\
     abs(x3) = sqrt(norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm (w3 cross w4)) /\
     ~((norm(w3 cross w4)) pow 2  = &0) /\ ~((w3 dot w4) pow 2 - &1 = &0) /\
     z = x1 % w3 + x2 % w4 + x3 % (w3 cross w4) /\
     (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * k1 + (x3 pow 2) * (norm(w3 cross w4)) pow 2 /\ 
     matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp((--a3) %% screw_2_matrix s3) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point p)) = (homo_point (mk_point c)) /\
     matrix_exp((--a3) %% screw_2_matrix s3) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
     a = a3 + a4 /\ ~(u' = vec 0) /\ ~(v' = vec 0) /\
     z3 = z - vec3_vtrans w3 ** z /\
     z4 = z - vec3_vtrans w4 ** z ==>           
     a = atn( (w4 dot (u' cross z4)) / (u' dot z4)) 
             - atn((w3 dot (v' cross z3)) / (v' dot z3))`,
     INTRO_TAC "! *; eq1 cond" THEN
     SUBGOAL_THEN `matrix_exp(a3 %% screw_2_matrix s3) ** matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point p)) = (homo_point (mk_point q))` ASSUME_TAC THENL
     [MATCH_MP_TAC SOLUTION_OF_A3_A4 THEN
      ASM_MESON_TAC[];ALL_TAC] THEN
     MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_2_ALT THEN
     MAP_EVERY EXISTS_TAC [`r:real^3`;`u:real^3`;`v:real^3`;`p:real^3`;`q:real^3`;`c:real^3`;`k1:real`;`k2:real`;`k3:real`;`z:real^3`;`a3:real`; `a4:real`; `x1:real`; `x2:real`; `x3:real`; `s3:screw`; `s4:screw`] THEN
     REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let SSM_MUL_SELF_0 = prove
    (`!w. vec3_2_ssm w ** w = vec 0`,
    SIMP_TAC[GSYM CROSS_SSM;CROSS_REFL]);;
     
let SSM_POW_SELF_0 = prove
    (`!w n. ~(n = 0) ==> vec3_2_ssm w matrix_pow n ** w = vec 0`,
    GEN_TAC THEN INDUCT_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[matrix_pow] THEN ASM_CASES_TAC `n = 0` THENL
    [ASM_SIMP_TAC[matrix_pow;MATRIX_MUL_RID;SSM_MUL_SELF_0];ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC;MATRIX_VECTOR_MUL_RZERO]);;
    
let DOT_CROSS_NORM_1 = prove
    (`!w1 w2. norm w1 = &1 /\ norm w2 = &1 ==>
        (w1 cross w2) dot (w1 cross w2) = &1 - (w1 dot w2) pow 2`,
    SIMP_TAC[NORM_EQ_1;VECTOR_ARITH `(k1 % x - y) dot (k1 % x - y:real^3) = k1 * k1 * (x dot x) + y dot y - &2 * k1 * (x dot y)`] THEN
    SIMP_TAC[DOT_CROSS;REAL_ARITH `k * k + &1 - &2 * k * k = &1 - k pow 2`;REAL_MUL_RID] THEN
    SIMP_TAC[REAL_POW_2;DOT_SYM]);;
     
let PADEN_KAHAN_SUB_PRO_2_ALT_SPLIT = prove
    (`!w1 w2 r u u' v v' p q c:real^3 k1 k2 k3:real z:real^3 a1 a2 x1 x2 x3:real s1 s2:screw z1 z2:real^3.
    (--(pi / &2) < (a1 + a2) /\ (a1 + a2) < pi / &2) /\
    (--(pi / &2) < a1 /\ a1 < pi / &2) /\
    (--(pi / &2) < a2 /\ a2 < pi / &2) /\
    s1 = (w1, r cross (w1)) /\ s2 = (w2, r cross (w2)) /\
    norm w1 = &1 /\ norm w2 = &1 /\
    u = p - r /\ v = q - r /\ z = c - r /\
    u' = u - (vec3_vtrans (FST s2) ** u) /\
    v' = v - (vec3_vtrans (FST s1) ** v) /\ 
    k1 = w1 dot w2 /\ k2 = w2 dot u /\ k3 = w1 dot v /\
    x1 = (k1 * k2 - k3) / (k1 pow 2 - &1) /\
    x2 = (k1 * k3 - k2) / (k1 pow 2 - &1) /\
    abs(x3) = sqrt(norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm (w1 cross w2)) /\
    ~((norm(w1 cross w2)) pow 2  = &0) /\ ~((w1 dot w2) pow 2 - &1 = &0) /\
    z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2) /\
    (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * k1 + (x3 pow 2) * (norm(w1 cross w2)) pow 2 /\ 
    matrix_exp(a1 %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
    matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point c)) /\
    matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
    matrix_exp(a1 %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point p)) = (homo_point (mk_point q)) /\ 
    ~(u' = vec 0) /\ ~(v' = vec 0) /\
    z1 = z - vec3_vtrans w1 ** z /\
    z2 = z - vec3_vtrans w2 ** z
    ==>
    a1 = -- atn((w1 dot (v' cross z1)) / (v' dot z1)) /\
    a2 = atn((w2 dot (u' cross z2)) / (u' dot z2))`,
    MP_TAC PADEN_KAHAN_SUB_PRO_2_ALT THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    ONCE_REWRITE_TAC[GSYM IMP_CONJ] THEN
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
    STRIP_TAC THEN
    DISCH_THEN (MP_TAC o ISPEC `a1 + a2:real`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    INTRO_TAC "cond" THEN
    UNDISCH_THEN `norm (w1:real^3) = &1` (LABEL_TAC "w1_eq") THEN
    UNDISCH_THEN `norm (w2:real^3) = &1` (LABEL_TAC "w2_eq") THEN
    UNDISCH_THEN `k1 = w1 dot (w2:real^3)` (LABEL_TAC "k1") THEN
    UNDISCH_THEN `x2 = (k1 * k3 - k2) / (k1 pow 2 - &1)` (LABEL_TAC "x2") THEN
    UNDISCH_THEN `z = c - r:real^3` (LABEL_TAC "z" o SYM) THEN
    SUBGOAL_THEN `(k1 pow 2 - &1) = --((norm (w1 cross w2)) pow 2)` (LABEL_TAC "norm_eq") THENL
    [USE_THEN "k1" SUBST1_TAC THEN
     SIMP_TAC[REAL_ARITH `(x - y) = --z:real <=> y - x = z`;NORM_POW_2] THEN
     ASM_SIMP_TAC[DOT_CROSS_NORM_1];ALL_TAC] THEN
    SUBGOAL_THEN `((w2:real^3) dot z) = (w2 dot u)` ASSUME_TAC THENL
    [UNDISCH_THEN `z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2)` SUBST1_TAC THEN
     REMOVE_THEN "w2_eq" MP_TAC THEN
     SIMP_TAC[DOT_RADD;DOT_RMUL;NORM_EQ_1;REAL_MUL_RID;DOT_CROSS_SELF;REAL_MUL_RZERO;REAL_ADD_RID] THEN
     INTRO_TAC "w2_eq" THEN
     UNDISCH_THEN `k2 = (w2:real^3) dot u` (LABEL_TAC "k2") THEN
     UNDISCH_THEN `k3 = (w1:real^3) dot v` (LABEL_TAC "k3") THEN
     USE_THEN "k2" (SUBST1_TAC o SYM) THEN
     ONCE_REWRITE_TAC[DOT_SYM] THEN
     USE_THEN "k1" (SUBST1_TAC o SYM) THEN
     UNDISCH_THEN `x1 = (k1 * k2 - k3) / (k1 pow 2 - &1)` (SUBST1_TAC) THEN
     USE_THEN "x2" (SUBST1_TAC) THEN
     SIMP_TAC[real_div;REAL_ARITH `((k1 * k2 - k3) * inv (k1 pow 2 - &1)) * k1 + (k1 * k3 - k2) * inv (k1 pow 2 - &1) = k2 * (k1 pow 2 - &1) * inv (k1 pow 2 - &1)`] THEN
     UNDISCH_THEN `~(norm (w1 cross w2) pow 2 = &0)` MP_TAC THEN
     USE_THEN "norm_eq" (MP_TAC o SYM) THEN
     SIMP_TAC[REAL_ARITH `--x = y <=> x = --y`;REAL_ARITH `--x = &0 <=> x = &0`;REAL_MUL_RINV;REAL_MUL_RID];ALL_TAC] THEN
    REMOVE_THEN "cond" MP_TAC THEN 
    SUBGOAL_THEN `a2 = atn ((w2 dot (u' cross z2)) / (u' dot z2))` MP_TAC THENL
     [MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_1 THEN
      MAP_EVERY EXISTS_TAC [`r:real^3`; `u:real^3`; `z:real^3`; `p:real^3`; `c:real^3`; `s2:screw`] THEN
      ASM_SIMP_TAC[];ALL_TAC] THEN 
    REAL_ARITH_TAC);;
    
let SOLUTION_OF_A1_A2_ALT_SPLIT = prove
    (`!s1 s2 s3 s4 s5:screw a1 a2 a3 a4 a5:real pw x:real^3 g_d:real^(3,1)finite_sum^(3,1)finite_sum ga_2:real^(3,1)finite_sum
     w1 w2 r u u' v v' q c:real^3 k1 k2 k3:real z a x1 x2 x3:real z1 z2:real^3.
     (g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x /\
     matrix_exp(a3 %% screw_2_matrix s3) ** matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point(mk_point pw)) = (homo_point(mk_point pw)) /\
     ga_2 = g_d ** (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5) ** (homo_point (mk_point pw))) /\
     (homo_point (mk_point q)) = ga_2 /\ 
     (--(pi / &2) < a /\ a < pi / &2) /\
     (--(pi / &2) < a1 /\ a1 < pi / &2) /\
     (--(pi / &2) < a2 /\ a2 < pi / &2) /\
     s1 = (w1, r cross (w1)) /\ s2 = (w2, r cross (w2)) /\
     norm w1 = &1 /\ norm w2 = &1 /\
     u = pw - r /\ v = q - r /\ z = c - r /\
     u' = u - (vec3_vtrans (FST s2) ** u) /\
     v' = v - (vec3_vtrans (FST s1) ** v) /\ 
     k1 = w1 dot w2 /\ k2 = w2 dot u /\ k3 = w1 dot v /\
     x1 = (k1 * k2 - k3) / (k1 pow 2 - &1) /\
     x2 = (k1 * k3 - k2) / (k1 pow 2 - &1) /\
     abs(x3) = sqrt(norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm (w1 cross w2)) /\
     ~((norm(w1 cross w2)) pow 2  = &0) /\ ~((w1 dot w2) pow 2 - &1 = &0) /\
     z = x1 % w1 + x2 % w2 + x3 % (w1 cross w2) /\
     (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * k1 + (x3 pow 2) * (norm(w1 cross w2)) pow 2 /\ 
     matrix_exp(a1 %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point pw)) = (homo_point (mk_point c)) /\
     matrix_exp((--a1) %% screw_2_matrix s1) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
     a = a1 + a2 /\ ~(u' = vec 0) /\ ~(v' = vec 0) /\
     z1 = z - vec3_vtrans w1 ** z /\
     z2 = z - vec3_vtrans w2 ** z ==>           
     a1 = -- atn((w1 dot (v' cross z1)) / (v' dot z1)) /\
     a2 = atn((w2 dot (u' cross z2)) / (u' dot z2))`,
     INTRO_TAC "! *; eq1 eq2 eq3 q cond" THEN
     SUBGOAL_THEN `matrix_exp(a1 %% screw_2_matrix s1) ** matrix_exp(a2 %% screw_2_matrix s2) ** (homo_point (mk_point pw)) = ga_2` ASSUME_TAC THENL
     [MATCH_MP_TAC SOLUTION_OF_A1_A2 THEN
      ASM_MESON_TAC[];ALL_TAC] THEN
     MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_2_ALT_SPLIT THEN
     MAP_EVERY EXISTS_TAC [`r:real^3`;`u:real^3`;`v:real^3`;`pw:real^3`;`q:real^3`;`c:real^3`;`k1:real`;`k2:real`;`k3:real`;`z:real^3`; `x1:real`; `x2:real`;`x3:real`; `s1:screw`; `s2:screw`] THEN
     REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let SOLUTION_OF_A3_A4_ALT_SPLIT = prove
    (`!s1 s2 s3 s4 s5:screw a1 a2 a3 a4 a5:real p q x:real^3 g_d:real^(3,1)finite_sum^(3,1)finite_sum 
    w3 w4 r u u' v v' q c:real^3 k1 k2 k3:real z:real^3 a x1 x2 x3:real z3 z4:real^3.
     (g_d = ga a1 s1 a2 s2 a3 s3 a4 s4 a5 s5 x /\
     (homo_point (mk_point q)) = matrix_exp(-- (a2) %% screw_2_matrix s2) ** matrix_exp(-- (a1) %% screw_2_matrix s1) ** g_d **
            (matrix_inv (gst_initial x)) ** matrix_exp(-- (a5) %% screw_2_matrix s5) ** 
                (homo_point (mk_point p))) /\
     (--(pi / &2) < a /\ a < pi / &2) /\
     (--(pi / &2) < a3 /\ a3 < pi / &2) /\
     (--(pi / &2) < a4 /\ a4 < pi / &2) /\
     s3 = (w3, r cross (w3)) /\ s4 = (w4, r cross (w4)) /\
     norm w3 = &1 /\ norm w4 = &1 /\
     u = p - r /\ v = q - r /\ z = c - r /\
     u' = u - (vec3_vtrans (FST s4) ** u) /\
     v' = v - (vec3_vtrans (FST s3) ** v) /\ 
     k1 = w3 dot w4 /\ k2 = w4 dot u /\ k3 = w3 dot v /\
     x1 = (k1 * k2 - k3) / (k1 pow 2 - &1) /\
     x2 = (k1 * k3 - k2) / (k1 pow 2 - &1) /\
     abs(x3) = sqrt(norm u pow 2 - x1 pow 2 - x2 pow 2 - (&2 * x1 * x2) * k1) / (norm (w3 cross w4)) /\
     ~((norm(w3 cross w4)) pow 2  = &0) /\ ~((w3 dot w4) pow 2 - &1 = &0) /\
     z = x1 % w3 + x2 % w4 + x3 % (w3 cross w4) /\
     (norm z) pow 2 = x1 pow 2 + x2 pow 2 + (&2 * x1 * x2) * k1 + (x3 pow 2) * (norm(w3 cross w4)) pow 2 /\ 
     matrix_exp(a3 %% screw_2_matrix s3) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp((--a3) %% screw_2_matrix s3) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point r)) = (homo_point (mk_point r)) /\
     matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point p)) = (homo_point (mk_point c)) /\
     matrix_exp((--a3) %% screw_2_matrix s3) ** (homo_point (mk_point q)) = (homo_point (mk_point c)) /\
     a = a3 + a4 /\ ~(u' = vec 0) /\ ~(v' = vec 0) /\
     z3 = z - vec3_vtrans w3 ** z /\
     z4 = z - vec3_vtrans w4 ** z ==>           
     a3 = -- atn((w3 dot (v' cross z3)) / (v' dot z3)) /\
     a4 = atn((w4 dot (u' cross z4)) / (u' dot z4))`,
     INTRO_TAC "! *; eq1 cond" THEN
     SUBGOAL_THEN `matrix_exp(a3 %% screw_2_matrix s3) ** matrix_exp(a4 %% screw_2_matrix s4) ** (homo_point (mk_point p)) = (homo_point (mk_point q))` ASSUME_TAC THENL
     [MATCH_MP_TAC SOLUTION_OF_A3_A4 THEN
      ASM_MESON_TAC[];ALL_TAC] THEN
     MATCH_MP_TAC PADEN_KAHAN_SUB_PRO_2_ALT_SPLIT THEN
     MAP_EVERY EXISTS_TAC [`r:real^3`;`u:real^3`;`v:real^3`;`p:real^3`;`q:real^3`;`c:real^3`;`k1:real`;`k2:real`;`k3:real`;`z:real^3`; `x1:real`; `x2:real`; `x3:real`; `s3:screw`; `s4:screw`] THEN
     REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;
    
    

