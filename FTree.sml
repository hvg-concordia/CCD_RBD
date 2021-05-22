
(* ========================================================================= *)
(* File Name: FTree.sml		                                             *)
(*---------------------------------------------------------------------------*)
(* Description: Fault Tree Diagrams in Higher-order Logic                    *)
(*                                                                           *)
(*              HOL4-Kananaskis 13 		 			     *)
(*									     *)
(*		Author :  Waqar Ahmed             		     	     *)
(* ========================================================================= *)

 
app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
          "real_probabilityTheory",
	  "numTheory", "dep_rewrite", "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory","real_sigmaTheory",
	  "indexedListsTheory", "listLib", "bossLib", "metisLib", "realLib", "numLib",
          "combinTheory", "arithmeticTheory","boolTheory", "listSyntax", "lebesgueTheory",
	  "real_sigmaTheory", "cardinalTheory", "ETreeTheory", "RBDTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory
     indexedListsTheory listLib satTheory numTheory bossLib metisLib realLib numLib
     combinTheory arithmeticTheory boolTheory listSyntax lebesgueTheory real_sigmaTheory
     cardinalTheory ETreeTheory RBDTheory;
                    
val _ = new_theory "FTree";

(*------new tactics for set simplification----*)
(*--------------------*)
infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;
fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);

(*---------------------------*)
fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN METIS_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);


val set_rewrs
= [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
SUBSET_UNION];

val UNIONL_def = Define `(UNIONL [] = {})
/\ (UNIONL (s::ss) = (s:'a ->bool) UNION UNIONL ss)`;

val IN_UNIONL = store_thm
("IN_UNIONL",
``!l (v:'a ). (v IN UNIONL l) = (?s. MEM s l /\ v IN s)``,
Induct >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
++ RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
++ PROVE_TAC []);

val IN_o = store_thm
  ("IN_o", ``!x f s. x IN (s o f) <=> f x IN s``,
    RW_TAC std_ss [SPECIFICATION, o_THM]);
   
val elt_rewrs
= [SUBSET_DEF, IN_COMPL, IN_DIFF, IN_UNIV, NOT_IN_EMPTY, IN_UNION,
IN_INTER, IN_IMAGE, IN_FUNSET, IN_DFUNSET, GSPECIFICATION,
DISJOINT_DEF, IN_BIGUNION, IN_BIGINTER, IN_COUNT, IN_o,
IN_UNIONL, IN_DELETE, IN_PREIMAGE, IN_SING, IN_INSERT];

(*--------------------*)
(*------------------------------*)
(*      Fault Tree Gates datatypes           *)
(*------------------------------*)
val _ = type_abbrev( "event" , ``:'a ->bool``);

(*val _ = Hol_datatype` gate = AND of gate list | OR of gate list | atomic of 'a  event `; *)

val _ = Hol_datatype` gate = AND of gate list | OR of gate list  | NOT of gate | atomic of 'a  event `;


(*----------------------------------------------*)
(*      Fault Tree  Semantic Function        *)
(*----------------------------------------------*)
val FTree_def = Define `
    (FTree p (atomic a)  = a) /\
    (FTree p (NOT a) =  p_space p DIFF FTree p a)/\
    (FTree p (AND []) = p_space p) /\
    (FTree p (AND (x::xs)) =
                FTree p (x:'a gate) INTER FTree p (AND (xs))) /\
     (FTree p (OR []) = {} ) /\
     (FTree p (OR (x::xs)) =
                 FTree p (x:'a gate) UNION FTree p (OR (xs)))`;


(* val FTree_def = Define `
    (FTree p ( atomic a)  = a) /\
    (FTree p (AND []) = p_space p) /\
    (FTree p (AND (x::xs)) =
                FTree p (x:'a gate) INTER FTree p (AND (xs))) /\
     (FTree p (OR []) = {} ) /\
     (FTree p (OR (x::xs)) =
                 FTree p (x:'a gate) UNION FTree p (OR (xs)))`;
*)
(*---rbd list from atomic events---*)

val gate_list_def = Define `
    (gate_list [] = []) /\
    (gate_list (h::t) =  atomic h::gate_list t)`;

(**)
(* -------------------- *)
(*      Definitions     *)
(* -------------------- *)

(*-------AND_gate_eq_PATH---*)
        
val AND_gate_eq_PATH = store_thm("AND_gate_eq_PATH",
  ``!p L. FTree p (AND (gate_list L)) = 
       	  PATH p L``,
GEN_TAC
++ Induct
>> (RW_TAC std_ss[gate_list_def,FTree_def,PATH_DEF])
++ RW_TAC std_ss[gate_list_def,FTree_def,PATH_DEF]);

(*-------------------------------------*)
(*		AND Gate	       *)
(*-------------------------------------*)

val AND_gate_thm = store_thm("AND_gate_thm",
  ``!p L. prob_space p /\ 
       	  ~NULL L /\ 
	  (!x'. MEM x' L ==> x' IN events p) /\
 	  MUTUAL_INDEP p L ==>
	   (prob p (FTree p (AND (gate_list L))) =
	    PROD_LIST (PROB_LIST p L))``,
RW_TAC std_ss[] THEN
(`(FTree p (AND (gate_list L))) = PATH p L ` by Induct_on `L`) THEN1
RW_TAC std_ss[gate_list_def,FTree_def,PATH_DEF] THENL[
RW_TAC std_ss[PATH_DEF] THEN
FULL_SIMP_TAC std_ss[NULL] THEN
RW_TAC std_ss[] THEN
Cases_on `L` THEN1
RW_TAC std_ss[gate_list_def,FTree_def,PATH_DEF] THEN
FULL_SIMP_TAC std_ss[NULL] THEN
(`(!x'. MEM x' ((h'::t):'a  event list) ==> x' IN events p) /\
          MUTUAL_INDEP p (h'::t)` by RW_TAC std_ss[]) 
THENL[
FULL_SIMP_TAC list_ss[],
MATCH_MP_TAC MUTUAL_INDEP_CONS THEN
EXISTS_TAC(``h:'a ->bool``) THEN
RW_TAC std_ss[],
FULL_SIMP_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[gate_list_def,FTree_def,PATH_DEF]],
FULL_SIMP_TAC std_ss[MUTUAL_INDEP_DEF] THEN
POP_ASSUM (K ALL_TAC) THEN
POP_ASSUM (MP_TAC o Q.SPEC `(L:'a  event list)`) THEN
RW_TAC std_ss[] THEN
POP_ASSUM (MP_TAC o Q.SPEC `LENGTH((L:'a  event list))`) THEN
RW_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[PERM_REFL] THEN
FULL_SIMP_TAC std_ss[GSYM LENGTH_NOT_NULL] THEN
(`1 <= LENGTH (L:'a  event list)` by ONCE_REWRITE_TAC[ONE]) THENL[
MATCH_MP_TAC LESS_OR THEN
RW_TAC std_ss[],
FULL_SIMP_TAC std_ss[TAKE_LENGTH_ID]]]);
 

(*------------------------------------*)
(*      OR Fault Tree Gate	      *)
(*------------------------------------*)

(*------------------------------------*)
(*      Lemmma's             *)
(*------------------------------------*)

val OR_gate_lem1 = store_thm("OR_gate_lem1",
  ``!p L. prob_space p /\
       	   (!x'. MEM x' L ==> x'  IN  events p) ==> 
	   (one_minus_list (PROB_LIST p L) =
	    PROB_LIST p ( compl_list p L))``,
GEN_TAC THEN
Induct THEN1
RW_TAC list_ss[compl_list_def,PROB_LIST_DEF,one_minus_list_def] THEN
RW_TAC list_ss[compl_list_def,PROB_LIST_DEF,one_minus_list_def] THEN
MATCH_MP_TAC EQ_SYM THEN
MATCH_MP_TAC PROB_COMPL THEN
RW_TAC std_ss[]);

(*-------OR_gate_lem2---------*)
val OR_gate_lem2 = store_thm("OR_gate_lem2",
  ``!L1 (L2:('a ->bool)list) Q. (LENGTH (L1 ++ ((Q::L2))) = LENGTH ((Q::L1) ++ (L2)))``,
RW_TAC list_ss[LENGTH_APPEND]);
(*-------OR_gate_lem3---------*)
val OR_gate_lem3 = store_thm("OR_gate_lem3",
  ``!A B C D. A INTER B INTER C INTER D = (B INTER C) INTER D INTER A ``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]
);
(*--------------OR_gate_lem4---------*)
val OR_gate_lem4 = store_thm("OR_gate_lem4",
  ``!p A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C)) ``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]
);
(*--------------OR_gate_lem5---------*)
val  OR_gate_lem5 = store_thm("OR_gate_lem5",
  ``!m (L:('a ->bool)list) x. MEM x (TAKE m L) ==> MEM x L ``,
Induct
THEN1(Induct
 THEN1 (RW_TAC std_ss[TAKE_def,MEM])
 THEN RW_TAC std_ss[TAKE_def,MEM])
 THEN Induct
  THEN1( RW_TAC std_ss[TAKE_def,MEM])
 THEN RW_TAC std_ss[TAKE_def,MEM]
THEN NTAC 2 (POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `L`)
THEN RW_TAC std_ss[] );
(*-------------OR_gate_lem6----------------*)
val OR_gate_lem6 = store_thm("OR_gate_lem6",``!A C. A INTER (p_space p DIFF C) = (A INTER p_space p DIFF (A INTER C))``,
SRW_TAC[][IN_INTER,EXTENSION,GSPECIFICATION]
THEN METIS_TAC[]);
(*-------------OR_gate_lem7----------------*)
val OR_gate_lem7 =  store_thm("OR_gate_lem7",``!(L1:('a ->bool) list) p.
 prob_space p /\
 (!x. MEM x (L1) ==> x IN events p ) ==>
((L1:('a ->bool) list) =  compl_list p (compl_list p L1)) ``,
Induct
>> (RW_TAC list_ss[compl_list_def,MAP])
++ RW_TAC std_ss[compl_list_def,MAP]
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC DIFF_DIFF_SUBSET
   ++ (`h =  h INTER p_space p` by MATCH_MP_TAC EQ_SYM)
      >> (ONCE_REWRITE_TAC[INTER_COMM]
         ++ MATCH_MP_TAC INTER_PSPACE
         ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[INTER_SUBSET])
++ NTAC 2 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[compl_list_def]);

(*--------------------------*)
val prob_indep_PATH2 = store_thm("prob_indep_PATH2",
``!(L1:('a ->bool) list) (L2:('a ->bool) list) n p.
	   prob_space p  /\ MUTUAL_INDEP p (L1 ++ (L2)) /\
	   (!x. MEM x (L1 ++ (L2)) ==> x IN events p ) /\
	    1 <=  (LENGTH (L1 ++ (L2))) ==>
	     (prob p (PATH p (TAKE n (compl_list p L1)) INTER 
	     	      PATH p ((L2) )) =
              PROD_LIST (PROB_LIST p (TAKE (n)(compl_list p L1) )) *
	       PROD_LIST (PROB_LIST p (( L2) )))``,
Induct
THEN1(RW_TAC real_ss[compl_list_def,MAP,TAKE_def,PATH_DEF,PROB_LIST_DEF,PROD_LIST_DEF]
 THEN FULL_SIMP_TAC std_ss[MUTUAL_INDEP_DEF]
 THEN NTAC 2 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `((L2):('a ->bool)list) `)
 THEN RW_TAC real_ss[]
 THEN NTAC 2 (POP_ASSUM MP_TAC)
 THEN POP_ASSUM (MP_TAC o Q.SPEC `LENGTH ((L2):('a ->bool)list)`)
 THEN RW_TAC real_ss[]
 THEN FULL_SIMP_TAC list_ss[PERM_REFL,PATH_DEF]
 THEN (`(p_space p INTER (PATH p ((L2:('a ->bool)list)))) = (PATH p (L2))` by MATCH_MP_TAC INTER_PSPACE)
 THEN1( RW_TAC std_ss[]
  THEN MATCH_MP_TAC in_events_PATH
  THEN FULL_SIMP_TAC std_ss[])
 THEN ONCE_ASM_REWRITE_TAC[]
 THEN RW_TAC std_ss[]
 THEN RW_TAC std_ss[PROB_LIST_DEF,PROD_LIST_DEF])
THEN Induct_on `n`
   THEN1(RW_TAC real_ss[compl_list_def,MAP,TAKE_def,PATH_DEF,PROB_LIST_DEF,PROD_LIST_DEF]
   THEN FULL_SIMP_TAC std_ss[APPEND,LENGTH,LE_SUC]
    THEN1 (NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `L2:('a ->bool)list`)
     THEN RW_TAC std_ss[]
     THEN NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `0:num`)
     THEN RW_TAC std_ss[]
     THEN NTAC 4 (POP_ASSUM MP_TAC)
     THEN POP_ASSUM (MP_TAC o Q.SPEC `p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`)
     THEN RW_TAC std_ss[]
     THEN FULL_SIMP_TAC std_ss[]
     THEN (`MUTUAL_INDEP p (L1 ++ L2) /\
      (!x. MEM x (L1 ++ L2) ==> x IN events p)` by STRIP_TAC)
      THEN1( MATCH_MP_TAC MUTUAL_INDEP_CONS
       THEN EXISTS_TAC (``h:'a  event``)
       THEN RW_TAC std_ss[])
      THEN1 (RW_TAC std_ss[]
      THEN FULL_SIMP_TAC list_ss[])
     THEN FULL_SIMP_TAC std_ss[]
     THEN FULL_SIMP_TAC list_ss[]
     THEN FULL_SIMP_TAC list_ss[PATH_DEF]
     THEN RW_TAC real_ss[PROB_LIST_DEF,PROD_LIST_DEF])
  THEN FULL_SIMP_TAC list_ss[OR_gate_lem2]
  THEN FULL_SIMP_TAC list_ss[APPEND,LENGTH_NIL]
  THEN RW_TAC real_ss[PATH_DEF,PROB_LIST_DEF,PROD_LIST_DEF,INTER_IDEMPOT,PROB_UNIV])
THEN RW_TAC std_ss[compl_list_def,MAP,TAKE_def,HD,TL,PATH_DEF]
THEN RW_TAC std_ss[INTER_ASSOC]
THEN (`!a b c. a INTER b INTER c =  b INTER c INTER a` by SET_TAC[])
THEN POP_ORW
THEN RW_TAC std_ss[GSYM compl_list_def]
THEN RW_TAC std_ss[OR_gate_lem4]
THEN DEP_REWRITE_TAC[prob_compl_subset]
THEN RW_TAC std_ss[]
THEN1 (MATCH_MP_TAC EVENTS_INTER
      THEN RW_TAC std_ss[]
      THEN1 (MATCH_MP_TAC EVENTS_INTER
      	    THEN RW_TAC std_ss[]
	    THEN1 (MATCH_MP_TAC in_events_PATH
      	    	  THEN RW_TAC std_ss[]
		  THEN (`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC OR_gate_lem5)
		  THEN1 (EXISTS_TAC(``n:num``)
       		  	THEN RW_TAC std_ss[])
		  THEN FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
      		  THEN MATCH_MP_TAC EVENTS_COMPL
      		  THEN RW_TAC std_ss[]
      		  THEN FULL_SIMP_TAC list_ss[])
	    THEN MATCH_MP_TAC in_events_PATH
     	    THEN RW_TAC std_ss[]
     	    THEN FULL_SIMP_TAC list_ss[])
      THEN RW_TAC std_ss[EVENTS_SPACE])
THEN1 (MATCH_MP_TAC EVENTS_INTER
      THEN RW_TAC std_ss[]
      THEN1 (MATCH_MP_TAC EVENTS_INTER
      	    THEN RW_TAC std_ss[]
	    THEN1 (MATCH_MP_TAC in_events_PATH
      	    	  THEN RW_TAC std_ss[]
		  THEN (`MEM x (compl_list p (L1:'a  event list))` by MATCH_MP_TAC OR_gate_lem5)
		  THEN1 (EXISTS_TAC(``n:num``)
       		  	THEN RW_TAC std_ss[])
		  THEN FULL_SIMP_TAC std_ss[compl_list_def,MEM_MAP]
      		  THEN MATCH_MP_TAC EVENTS_COMPL
      		  THEN RW_TAC std_ss[]
      		  THEN FULL_SIMP_TAC list_ss[])
	    THEN MATCH_MP_TAC in_events_PATH
     	    THEN RW_TAC std_ss[]
     	    THEN FULL_SIMP_TAC list_ss[])
      THEN FULL_SIMP_TAC list_ss[])
THEN1 ((`PATH p L2 INTER p_space p =  PATH p L2` by ONCE_REWRITE_TAC [INTER_COMM])
      THEN1 (MATCH_MP_TAC INTER_PSPACE
      	    THEN RW_TAC std_ss[]
 	    THEN MATCH_MP_TAC in_events_PATH
 	    THEN RW_TAC std_ss[]
 	    THEN FULL_SIMP_TAC list_ss[])
      THEN RW_TAC std_ss[GSYM INTER_ASSOC]
      THEN RW_TAC std_ss[INTER_ASSOC,INTER_SUBSET])
THEN (`PATH p L2 INTER p_space p =  PATH p L2` by ONCE_REWRITE_TAC [INTER_COMM])
  THEN1(MATCH_MP_TAC INTER_PSPACE
   THEN RW_TAC std_ss[]
   THEN MATCH_MP_TAC in_events_PATH
   THEN RW_TAC std_ss[]
   THEN FULL_SIMP_TAC list_ss[])
THEN RW_TAC std_ss[GSYM INTER_ASSOC]
THEN RW_TAC std_ss[INTER_ASSOC]
THEN POP_ASSUM (K ALL_TAC)
THEN (` LENGTH (h::L1 ++ L2) =  LENGTH (h::(L1 ++ L2))` by RW_TAC list_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN POP_ASSUM (K ALL_TAC)
THEN FULL_SIMP_TAC std_ss[LENGTH]
THEN FULL_SIMP_TAC std_ss[LE_SUC]
THEN1 (DEP_ONCE_ASM_REWRITE_TAC[]
      THEN RW_TAC std_ss[]
      THEN1 (MATCH_MP_TAC MUTUAL_INDEP_CONS
      	    THEN EXISTS_TAC (``h:'a  event``)
      	    THEN FULL_SIMP_TAC list_ss[])
      THEN1 (RW_TAC std_ss[]
      	    THEN FULL_SIMP_TAC list_ss[])
      THEN FIRST_X_ASSUM (Q.SPECL_THEN [`(h::L2):('a ->bool)list`,`n:num`,`p:(  'a    -> bool) # ((  'a    -> bool) -> bool) # ((  'a    -> bool) -> real)`] MP_TAC)
      THEN RW_TAC std_ss[]
      THEN (` MUTUAL_INDEP p (L1 ++ h::L2) ∧
      (∀x. MEM x (L1 ++ h::L2) ⇒ x ∈ events p) ∧
      1 ≤ LENGTH (L1 ++ h::L2)` by RW_TAC std_ss[])
      THEN1 (MATCH_MP_TAC MUTUAL_INDEP_CONS_append
      	    THEN RW_TAC std_ss[])
      THEN1 (FULL_SIMP_TAC list_ss[])
      THEN1 ((`LENGTH (L1 ++ h::L2) =  LENGTH (h::L1 ++ L2)` by RW_TAC list_ss[])
      	    THEN POP_ORW
	    THEN RW_TAC list_ss[])
      THEN FULL_SIMP_TAC std_ss[]
      THEN FULL_SIMP_TAC std_ss[PATH_DEF]
      THEN RW_TAC std_ss[GSYM INTER_ASSOC]
      THEN (`!a b c. a INTER (b INTER c) =  a INTER (c INTER b)` by SET_TAC[])
      THEN POP_ORW
      THEN RW_TAC std_ss[]
      THEN RW_TAC list_ss[PROB_LIST_DEF,PROD_LIST_DEF]
      THEN DEP_REWRITE_TAC[PROB_COMPL]
      THEN RW_TAC std_ss[]
      THEN1 (FULL_SIMP_TAC list_ss[])
      THEN REAL_ARITH_TAC)
THEN FULL_SIMP_TAC list_ss[]
THEN FULL_SIMP_TAC std_ss[LENGTH_NIL]
THEN RW_TAC list_ss[compl_list_def,PATH_DEF,PROB_LIST_DEF,PROD_LIST_DEF]
THEN RW_TAC real_ss[INTER_IDEMPOT]
THEN RW_TAC std_ss[PROB_UNIV]
THEN DEP_REWRITE_TAC[PROB_COMPL]
THEN RW_TAC std_ss[]
THEN DEP_ONCE_REWRITE_TAC[INTER_PSPACE]
THEN RW_TAC std_ss[]);

(*------------------------------------*)
(*------OR RBD Configuration----*)
(*------------------------------------*)

(*------OR_Lemma1----*)
val OR_lem1 = store_thm("OR_lem1",``!p s t. p_space p DIFF (s UNION t) = (p_space p DIFF s) INTER (p_space p DIFF t)``,
SRW_TAC [][EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------- OR_lem2---------------*)
val OR_lem2 = store_thm("OR_lem2",``!p  (L:('a  -> bool) list).  prob_space p /\ (!x. MEM x L ==> x IN  events p)  ==>
         ( FTree p (AND (gate_list (compl_list p L))) = p_space p DIFF (FTree p ( OR (gate_list L)) ))``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def,DIFF_EMPTY])
++ RW_TAC std_ss[]
++ RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM compl_list_def]
++ (`(!x. MEM x L ==> x IN  events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[OR_lem1]);
(*------------OR_lem3-------------*)
val OR_lem3 = store_thm("OR_lem3",``!L p. (!x. MEM x L ==> x IN events p) /\
prob_space p ==>
  (FTree p (OR (gate_list L)) IN events p)``,
RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def,EVENTS_EMPTY])
++ RW_TAC std_ss[gate_list_def,MAP, FTree_def]
++ (`(!x. MEM x L ==> x IN  events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ MATCH_MP_TAC EVENTS_UNION
++ FULL_SIMP_TAC list_ss[]);
(*----------------OR_lem4----------------------*)
val OR_lem4 = store_thm("OR_lem4",``!p L. (!x. MEM x L ==> x IN events p) /\
prob_space p /\
  ((FTree p (OR (gate_list L))) IN events p) ==> ((FTree p (OR (gate_list L))) SUBSET p_space p )``,
GEN_TAC
++ Induct
>> (RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def]
   ++ FULL_SIMP_TAC std_ss[SUBSET_DEF, NOT_IN_EMPTY])
++ RW_TAC std_ss[compl_list_def,MAP,gate_list_def,FTree_def]
++ RW_TAC std_ss[UNION_SUBSET]
>> ((`h = h INTER p_space p` by MATCH_MP_TAC EQ_SYM)
   >> (ONCE_REWRITE_TAC[INTER_COMM]
      ++ MATCH_MP_TAC INTER_PSPACE
      ++ FULL_SIMP_TAC list_ss[])
   ++ POP_ORW
   ++ RW_TAC std_ss[INTER_SUBSET])
++ FULL_SIMP_TAC std_ss[]
++ (`(!x. MEM x L ==> x IN events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[OR_lem3]);
(*----------------OR_lem5----------------------*)
val OR_lem5 = store_thm("OR_lem5",``!p L. FTree p (AND (gate_list L)) = PATH p L``,
 RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC list_ss[gate_list_def,FTree_def,PATH_DEF])
++ RW_TAC list_ss[gate_list_def,FTree_def,PATH_DEF]);

(*-----------------OR_lem6---------------------*)

val OR_lem6 = store_thm("OR_lem6",``!p x L.  prob_space p /\ (!x'. MEM x' L ==> x' IN events p)                                ==>
(prob p (FTree p (OR (gate_list L))) = 1 - prob p (FTree p (AND (gate_list (compl_list p ( L))))))``,
RW_TAC std_ss[]
++ (`FTree p (OR (gate_list L)) SUBSET p_space p` by MATCH_MP_TAC  OR_lem4)
>> (RW_TAC std_ss[]
   ++ MATCH_MP_TAC OR_lem3
   ++ RW_TAC std_ss[])
++  (`(1 - prob p (FTree p (AND (gate_list (compl_list p L)))))  = (prob p (p_space p DIFF (FTree p (AND (gate_list (compl_list p L))))))` by MATCH_MP_TAC EQ_SYM)
>> (MATCH_MP_TAC PROB_COMPL
   ++  RW_TAC std_ss[]
   ++  RW_TAC std_ss[OR_lem5]
   ++  MATCH_MP_TAC in_events_PATH
   ++ RW_TAC list_ss[compl_list_def,MEM_MAP]
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[]
++ RW_TAC std_ss[OR_lem2]
++ RW_TAC std_ss[DIFF_DIFF_SUBSET]);
(*--------------OR_lem7----------------------*)
val OR_lem7 = store_thm("OR_lem7",``!p (L). prob_space p /\ (!x'. MEM x' L ==> x'  IN  events p )   ==> (one_minus_list (PROB_LIST p L) = PROB_LIST p ( compl_list p L))``,
RW_TAC std_ss[]
++ Induct_on `L`
>> (RW_TAC std_ss[one_minus_list_def,compl_list_def,MAP,PROB_LIST_DEF])
++ RW_TAC std_ss[one_minus_list_def,compl_list_def,MAP,PROB_LIST_DEF]
>> (MATCH_MP_TAC EQ_SYM
   ++ MATCH_MP_TAC PROB_COMPL
   ++ FULL_SIMP_TAC list_ss[])
++ (`(!x'. MEM x' L ==> x' IN events p)` by FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM compl_list_def]);
(*------------------------------------*)
val OR_lem8 = store_thm("OR_lem8",
  `` !L. one_minus_list L =  MAP (\a. 1 - a) L ``,
Induct
++ RW_TAC list_ss[one_minus_list_def]);
(*------------------------------------*)
(*-----------OR_gate_thm------*)
(*------------------------------------*)
val OR_gate_thm = store_thm("OR_gate_thm", ``!p L . ~NULL L /\ (!x'. MEM x' L ==> x' IN events p) /\ prob_space p  /\ MUTUAL_INDEP p L  ==> (prob p (FTree p (OR (gate_list L))) =
       1 -  PROD_LIST (one_minus_list (PROB_LIST p L)))``,
RW_TAC real_ss[OR_lem6,real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
++ (`prob p (FTree p (AND (gate_list (compl_list p L)))) = PROD_LIST (PROB_LIST p (compl_list p L))` by MATCH_MP_TAC AND_gate_thm)
>> (RW_TAC std_ss[]
   >> (RW_TAC std_ss[GSYM LENGTH_NOT_NULL]
       ++ RW_TAC std_ss[compl_list_def,LENGTH_MAP]
       ++ RW_TAC std_ss[LENGTH_NOT_NULL])
   >> (FULL_SIMP_TAC list_ss[compl_list_def,MEM_MAP]
      ++ MATCH_MP_TAC EVENTS_COMPL
      ++ FULL_SIMP_TAC list_ss[])
   ++ MATCH_MP_TAC MUTUAL_INDEP_compl
   ++ FULL_SIMP_TAC list_ss[]
   ++ Cases_on `L`
   >> (FULL_SIMP_TAC list_ss[])
   ++ FULL_SIMP_TAC list_ss[])
++ POP_ORW
++ RW_TAC std_ss[OR_lem7]);
(*----------------------------*)
(*  NAND Fault Tree Gate      *)
(*----------------------------*)
(*-------AND_gate_append----*)
val AND_gate_append = store_thm("AND_gate_append",
 ``!p h L1. prob_space p /\ (!x. MEM x (h++L1) ==> x IN events p) ==> 
      	    (FTree p (AND (gate_list h)) INTER
	      FTree p (AND (gate_list L1)) =
	     FTree p (AND (gate_list (h ++ L1))))``,
REPEAT GEN_TAC
++ Induct_on `h`
>> (RW_TAC list_ss[gate_list_def,FTree_def]
   ++ MATCH_MP_TAC INTER_PSPACE
   ++ RW_TAC std_ss[AND_gate_eq_PATH]
   ++ MATCH_MP_TAC in_events_PATH
   ++ RW_TAC std_ss[])
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC list_ss[gate_list_def,FTree_def]
++ (`(!x. MEM x ((h ++ L1):'a  event list) ==> x IN events p)` by RW_TAC std_ss[MEM_APPEND] )
>> (FULL_SIMP_TAC list_ss[])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]
++ RW_TAC std_ss[GSYM INTER_ASSOC]);

(*----------------------------*)
val NAND_eq_PATH_alt_form = store_thm("NAND_eq_PATH_alt_form",
  ``!p L1 L2. (prob_space p ∧ ∀x. MEM x (compl_list p L1 ++ L2) ⇒ x ∈ events p) ==> 
       	      		((PATH p (compl_list p L1) ∩ PATH p L2) = 
			(FTree p (AND (gate_list (compl_list p L1 ++ L2)))))``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[GSYM AND_gate_append]
++ RW_TAC std_ss[]
++ DEP_REWRITE_TAC[AND_gate_eq_PATH]);


(*---------------------------*)
val NAND_FT_gate = store_thm("NAND_FT_gate",
  ``!p L1 L2. 
       prob_space p /\
       (1 ≤ LENGTH (L1 ++ L2)) /\
       (!x'. MEM x' (L1++L2) ==> x' IN  events p) /\
       MUTUAL_INDEP p (L1++L2) ==>
        (prob p (FTree p (AND (gate_list (compl_list p L1 ++ L2)))) =
	 PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p L2))  ``,
RW_TAC std_ss[]
++ MP_TAC(Q.ISPECL [`(L1:('a->bool)list)`,`(L2:('a->bool)list)`,`(LENGTH (compl_list p L1)):num`,`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`] prob_indep_PATH2)
++ RW_TAC std_ss[TAKE_LENGTH_ID]
++ DEP_REWRITE_TAC[GSYM NAND_eq_PATH_alt_form]
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC list_ss[]
++ FULL_SIMP_TAC list_ss[compl_list_def]
++ FULL_SIMP_TAC list_ss[MEM_MAP]
++ MATCH_MP_TAC EVENTS_COMPL
++ RW_TAC std_ss[]);

(*-------------------*)
(* ------------------------------------------------------------------------- *)
(*                 NOR_FT gate Theorem     *)
(* ------------------------------------------------------------------------- *)
val NOR_FT_gate_def = Define `NOR_FT_gate p L = (p_space p DIFF FTree p (OR (gate_list L)))`;

(*-------------------*)
val NOR_gate_thm = store_thm("NOR_gate_thm", ``!p L . ~NULL L /\ (!x'. MEM x' L ==> x' IN events p) /\ prob_space p  /\ MUTUAL_INDEP p L  ==> (prob p (NOR_FT_gate p L) =
       PROD_LIST (one_minus_list (PROB_LIST p L)))``,
RW_TAC std_ss[NOR_FT_gate_def]
++ DEP_REWRITE_TAC[PROB_COMPL]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[OR_lem3]
   ++ RW_TAC std_ss[])
++ DEP_REWRITE_TAC [OR_gate_thm]
++ RW_TAC real_ss[]);

(*----------------------------------------------------*)
(*---------------------xor_gate_temp1-----------------------------------*)
val xor_gate_temp1 = store_thm("xor_gate_temp1",
  ``!A B. ((COMPL A INTER B) UNION (COMPL B INTER A)) = (A DIFF B) UNION (B DIFF A)  ``,
SRW_TAC[][COMPL_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------------------- xor_gate_temp2---------------------------------*)
val xor_gate_temp2 = store_thm("xor_gate_temp2",
``!A B . A DIFF B = A DIFF (A INTER B)``,
SRW_TAC[][COMPL_DEF,EXTENSION,GSPECIFICATION]
++ METIS_TAC[]);
(*----------------------PROB_COMPL_SUBSET----------------------------------*)
val PROB_COMPL_SUBSET = store_thm("PROB_COMPL_SUBSET",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ t SUBSET s ==> (prob p (s DIFF t) = prob p s - prob p t)  ``,
METIS_TAC [MEASURE_COMPL_SUBSET,prob_space_def,events_def,prob_def,p_space_def]);
(*--------------------PROB_XOR_GATE------------------------------------*)
val PROB_XOR_GATE = store_thm("PROB_XOR_GATE",
  ``!A B p .  prob_space p /\ A IN events p /\ B IN events p ==>
(prob p  ((COMPL A INTER B) UNION (COMPL B INTER A)) = prob p A + prob p B - 2 *prob p (A INTER B))``,
RW_TAC std_ss[xor_gate_temp1]
++ MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `A DIFF B:'a->bool`,`(B DIFF A):'a->bool`,
                 `(A DIFF B UNION (B DIFF A)):'a->bool`]
       PROB_ADDITIVE )
++ FULL_SIMP_TAC std_ss[EVENTS_DIFF]
++ KNOW_TAC(``DISJOINT (A DIFF B) (B DIFF (A:'a->bool))``)
>> (RW_TAC std_ss[DISJOINT_DIFF]
   ++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[])
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ ONCE_REWRITE_TAC[xor_gate_temp2]
++  MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `A:'a->bool`,`(A INTER B):'a->bool`]
       PROB_COMPL_SUBSET)
++ FULL_SIMP_TAC std_ss[INTER_SUBSET,EVENTS_INTER]
++ MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `B:'a->bool`,`(B INTER A):'a->bool`]
       PROB_COMPL_SUBSET)
++ FULL_SIMP_TAC std_ss[INTER_SUBSET,EVENTS_INTER]
++ RW_TAC std_ss[INTER_COMM]
++ REAL_ARITH_TAC);
(*-----prob_compl_A_INTER_B-----------------*)
val prob_compl_A_INTER_B = store_thm("prob_compl_A_INTER_B",
  ``!a b p. prob_space p ∧ a ∈ events p ∧ b ∈ events p ⇒
     (prob p (compl_pspace p a ∩ b) = prob p b - prob p (a ∩ b))``,
RW_TAC std_ss[]
++ REWRITE_TAC[REAL_EQ_SUB_LADD]
++ MATCH_MP_TAC EQ_SYM
++ ONCE_REWRITE_TAC[REAL_ADD_SYM]
++ RW_TAC std_ss[prob_B]);
(*-----compl_event_nevent_empty-----------------*)
val compl_event_nevent_empty = store_thm("compl_event_nevent_empty",
  ``!p A. compl_pspace p A INTER A = EMPTY``,
RW_TAC std_ss[compl_pspace_def]
++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[]);

(*--------------------PROB_XOR_GATE1------------------------------------*)
val PROB_XOR_GATE1 = store_thm("PROB_XOR_GATE1",
  ``!A B p .  prob_space p /\ A IN events p /\ B IN events p ==>
(prob p  (((p_space p DIFF A) INTER B) UNION ((p_space p DIFF B) INTER A)) = 
prob p A + prob p B - 2 *prob p (A INTER B)) ``,
RW_TAC std_ss[]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_COMPL]
   ++ RW_TAC std_ss[])
>> (DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_COMPL]
   ++ RW_TAC std_ss[])
++ REWRITE_TAC[GSYM  compl_pspace_def]
++ RW_TAC std_ss[prob_compl_A_INTER_B]
++ (`compl_pspace p A ∩ B ∩ (compl_pspace p B ∩ A) = EMPTY` by ALL_TAC)
>> (FULL_SIMP_TAC std_ss[prove (``!a b c d. (a INTER b INTER (c INTER d)) = ((a INTER d) INTER (c INTER b ))``, RW_TAC std_ss[]++(SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[]))]
++ RW_TAC std_ss[compl_event_nevent_empty]
++ RW_TAC std_ss[INTER_IDEMPOT])
++ POP_ORW 
++ RW_TAC real_ss[PROB_EMPTY]
++ RW_TAC real_ss[real_sub,REAL_ADD_ASSOC]
++  SUBST_OCCS_TAC [([1], SPECL [``B:('a->bool)``, ``A:('a->bool)``] 
                               INTER_COMM)]
++ REAL_ARITH_TAC);
(*--------------------*)
val XOR_FT_gate_def = Define 
    `XOR_FT_gate p A B = 
     FTree p (OR [AND [NOT A; B] ; AND [A;NOT B]])`;
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(*    XOR Fault Tree Gate                                                     *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*--------------------XOR_FT_gate Theorem------------------------------------*)
val XOR_FT_gate_thm = store_thm("XOR_FT_gate_thm",
  ``!a b p.  prob_space p /\ a IN events p /\ 
       	      b IN events p /\ indep p a b ==>
	    (prob p  (XOR_FT_gate p (atomic a) (atomic b)) = 
	    prob p a * (1 - prob p b) + prob p b * 
	    	 (1 - prob p a))``,
RW_TAC std_ss[XOR_FT_gate_def, FTree_def]
++ RW_TAC std_ss[UNION_EMPTY]
++ SUBST_OCCS_TAC [([1], SPECL [``b:('a->bool)``, ``p_space p:('a->bool)``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[INTER_ASSOC]
++ FULL_SIMP_TAC std_ss[prove (``!a b c. a INTER b INTER c = b INTER (c INTER a)``, RW_TAC std_ss[]++(SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[]))]
++ SUBST_OCCS_TAC [([1], SPECL [``b:('a->bool)``, ``p_space p:('a->bool)``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[PROB_XOR_GATE1]
++ FULL_SIMP_TAC std_ss[indep_def]
++ REAL_ARITH_TAC);



(******************************************************************************)
(*                                                                            *)
(*  Inhibit Gate                                                              *)
(*                                                                            *)
(******************************************************************************)
val inhibit_FT_gate_def = Define 
    `inhibit_FT_gate p A B C =
     FTree p (AND [OR [A;B]; NOT C])`;

(*----------MUTUAL_INDEP_append_sym------*)
val MUTUAL_INDEP_append_sym = store_thm("MUTUAL_INDEP_append_sym",``!L1 L p.  MUTUAL_INDEP p (L1++L) ==> MUTUAL_INDEP p (L++L1)``,
RW_TAC std_ss[MUTUAL_INDEP_DEF]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
++ RW_TAC std_ss[]
++ NTAC 3 (POP_ASSUM MP_TAC)
++ POP_ASSUM (MP_TAC o Q.SPEC `n`)
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[]
++ (`PERM ((L1 ++ L):'a  event list) (L1') /\
      n <= LENGTH ((L1 ++ L):'a  event list)` by STRIP_TAC)
>> (MATCH_MP_TAC PERM_TRANS
   ++ EXISTS_TAC(``( L ++ L1):'a  event list``)
   ++ RW_TAC std_ss[PERM_APPEND])
>> (FULL_SIMP_TAC list_ss[])
++ FULL_SIMP_TAC std_ss[]);
(*-----------------------------*)
val indep_compl_event_nevents = store_thm("indep_compl_event_nevents",
  ``!p A B C. prob_space p /\  A IN events p /\ 
       	      B IN events p /\ C IN events p /\ 
	      MUTUAL_INDEP p [A;B;C] ==>
       (prob p (compl_pspace p C INTER A INTER B) = 
       prob p A * prob p B − prob p A * prob p B * prob p C) ``,
RW_TAC std_ss[]
++ REWRITE_TAC [GSYM INTER_ASSOC]
++ DEP_REWRITE_TAC[prob_compl_A_INTER_B]
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[EVENTS_INTER])
++ SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``A INTER B:'a event``] 
                               INTER_COMM)]
++ `((A INTER B) = FTree p (AND (gate_list [A;B]))) /\
   		 	       	      	 ((A INTER B INTER C) =  FTree p (AND (gate_list [A;B;C])))` by RW_TAC list_ss[gate_list_def,FTree_def] 
>> (SUBST_OCCS_TAC [([1], SPECL [``B:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
    ++ RW_TAC std_ss[INTER_PSPACE])
>> (SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
    ++ RW_TAC std_ss[INTER_PSPACE]
    ++ REWRITE_TAC[INTER_ASSOC])
++ POP_ORW ++ POP_ORW
++ DEP_REWRITE_TAC[AND_gate_thm]
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (MATCH_MP_TAC MUTUAL_INDEP_CONS
   ++ EXISTS_TAC(``C:'a event``)
   ++ RW_TAC std_ss[prove (``[C;A;B] = [C] ++ [A;B]``, RW_TAC list_ss[])]
   ++ MATCH_MP_TAC MUTUAL_INDEP_append_sym
   ++ RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[PROB_LIST_DEF,PROD_LIST_DEF]
++ RW_TAC real_ss[]
++ REAL_ARITH_TAC);
(*-----------------------------*)
val inhibit_FT_gate_thm = store_thm("inhibit_FT_gate_thm",
  ``!p A B C.  prob_space p /\ A IN events p /\ 
       	      B IN events p /\ C IN events p /\ 
	      MUTUAL_INDEP p [A;B;C] ==>
	    (prob p (inhibit_FT_gate p (atomic A) (atomic B) (atomic C)) = 
	    (1 - (1 - prob p A) * (1 - prob p B)) * (1 - prob p C))``,
RW_TAC std_ss[inhibit_FT_gate_def, FTree_def]
++ RW_TAC std_ss[UNION_EMPTY,UNION_ASSOC]
++ SUBST_OCCS_TAC [([1], SPECL [``(p_space p DIFF C)``, ``p_space p``] 
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ RW_TAC std_ss[]
>> (RW_TAC std_ss[EVENTS_COMPL])
++ ONCE_REWRITE_TAC[INTER_COMM]
++ REWRITE_TAC[UNION_OVER_INTER]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (DEP_REWRITE_TAC[EVENTS_INTER]
   ++ RW_TAC std_ss[EVENTS_COMPL])
>> (DEP_REWRITE_TAC[EVENTS_INTER]
   ++ RW_TAC std_ss[EVENTS_COMPL])
++ REWRITE_TAC[GSYM compl_pspace_def]
++ DEP_REWRITE_TAC[prob_compl_A_INTER_B]
++ RW_TAC std_ss[]
++ FULL_SIMP_TAC std_ss[prove(``!A B C. A INTER B INTER (A INTER C) = A INTER B INTER C``, RW_TAC std_ss[] ++ SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
   ++ METIS_TAC[])]
++ SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``B:'a event``] 
                               INTER_COMM)]
++ (`MUTUAL_INDEP p [C;A] /\ 
   MUTUAL_INDEP p [B;C]` by RW_TAC std_ss[])
>> (MATCH_MP_TAC MUTUAL_INDEP_CONS
   ++ EXISTS_TAC(``B:'a->bool``)
   ++ FULL_SIMP_TAC std_ss[prove(``!A B C. [B;C;A] = [B;C]++[A]``, RW_TAC list_ss[])]
   ++ MATCH_MP_TAC MUTUAL_INDEP_append_sym
   ++ FULL_SIMP_TAC list_ss[])
>> (MATCH_MP_TAC MUTUAL_INDEP_CONS
   ++ EXISTS_TAC(``A:'a->bool``)
   ++ RW_TAC std_ss[])
++ DEP_REWRITE_TAC[indep_compl_event_nevents]
++ RW_TAC std_ss[]
++ (`((C INTER A) = FTree p (AND (gate_list [C;A]))) /\ ((B INTER C) = FTree p (AND (gate_list [B;C])))` by RW_TAC std_ss[])
>> (RW_TAC std_ss[FTree_def,gate_list_def]
   ++ SUBST_OCCS_TAC [([1], SPECL [``A:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
   ++ RW_TAC std_ss[INTER_PSPACE])
>> (RW_TAC std_ss[FTree_def,gate_list_def]
   ++ SUBST_OCCS_TAC [([1], SPECL [``C:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
   ++ RW_TAC std_ss[INTER_PSPACE])
++ POP_ORW ++ POP_ORW
++ DEP_REWRITE_TAC[AND_gate_thm]
++ RW_TAC list_ss[]
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
>> (RW_TAC list_ss[])
++ RW_TAC list_ss[PROD_LIST_DEF,PROB_LIST_DEF]
++ REAL_ARITH_TAC);

(******************************************************************************)
(*                                                                            *)
(*          Comparator Fault Tree Gate                                        *)
(*                                                                            *)
(******************************************************************************)

val comp_FT_gate_def = Define 
    `comp_FT_gate p A B = FTree p (OR [AND [A; B]; NOT (OR [A;B])])`;


val comp_FT_gate_thm = store_thm("comp_FT_gate_thm",
  ``!p A B. prob_space p /\ A IN events p /\ 
       	      B IN events p /\ 
	      indep p A B ==> 
	      (prob p (comp_FT_gate p (atomic A) (atomic B)) = 
	      (1 − (prob p A + prob p B − 2* (prob p A * prob p B))))``,
RW_TAC std_ss[comp_FT_gate_def,FTree_def,UNION_EMPTY]
++ REWRITE_TAC[OR_lem1]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ RW_TAC std_ss[]
>> (MATCH_MP_TAC EVENTS_INTER
   ++ ONCE_REWRITE_TAC[INTER_COMM]
   ++ RW_TAC std_ss[INTER_PSPACE])
>> (MATCH_MP_TAC EVENTS_INTER
   ++ RW_TAC std_ss[EVENTS_COMPL])
++ REWRITE_TAC[GSYM OR_lem1]
++ DEP_REWRITE_TAC[PROB_COMPL]
++ DEP_REWRITE_TAC[Prob_Incl_excl]
++ REWRITE_TAC[OR_lem1]
++ (`(A ∩ (B ∩ p_space p) ∩ ((p_space p DIFF A) ∩ (p_space p DIFF B))) = EMPTY` by 
   SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION])
>> (METIS_TAC[])
++ POP_ORW
++ DEP_ASM_REWRITE_TAC[EVENTS_UNION]
++ RW_TAC real_ss[PROB_EMPTY]
++ SUBST_OCCS_TAC [([1], SPECL [``B:'a event``, ``p_space p :'a event``] 
                               INTER_COMM)]
++ DEP_ASM_REWRITE_TAC[INTER_PSPACE]
++ FULL_SIMP_TAC std_ss[indep_def]
++ REAL_ARITH_TAC);

(*-----------------------------------------------------*)
(* ----------------------------------------------------*)
(* 	K-out-N RBD	                               *)
(* ----------------------------------------------------*)


val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);


val binomial_def= 
Define `(binomial n 0 = (1:num)) /\
        (binomial 0 (SUC k) = (0:num)) /\
        (binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k)`;

(*--------------------sum_set------------------------------------*)

val sum_set_def =  Define `sum_set s f =  REAL_SUM_IMAGE f s`;
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Definition:         K_out_N_struct_def                                    *)
(* ------------------------------------------------------------------------- *)
val K_out_N_struct_def =  Define `
K_out_N_struct p X k n = 
(BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) 
	  ({x|(k:num) <= x /\ x < SUC n})))`;

(* ------------------------------------------------------------------------- *)
(* SUM_0_SUM_1			                                             *)
(* ------------------------------------------------------------------------- *)

val SUM_0_SUM_1 = store_thm("SUM_0_SUM_1",
  ``!n f. (sum (0,SUC n) f = f (0) + sum (1,n) f )``,
Induct_on `n` THEN 
RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
(* ------------------------------------------------------------------------- *)
(* SUM_0_SUM_2			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_0_SUM_2 = store_thm("SUM_0_SUM_2",
  ``!n f. sum (0,SUC (SUC n)) f = f(0) + f(1)+ sum (2,n) f``,
Induct_on `n`
++ RW_TAC real_ss [sum]
++ RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);

(* ------------------------------------------------------------------------- *)
(* SUM_1_SUM_2			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_1_SUM_2 = store_thm("SUM_1_SUM_2",
  ``!n f. sum (1,SUC n) f = f (1) + sum (2,n) f``,
Induct_on `n` 
++ RW_TAC real_ss [sum]
++ RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]);
(* ------------------------------------------------------------------------- *)
(* SUM_SHIFT			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_SHIFT = store_thm("SUM_SHIFT",
  ``!n f. sum (0, n) f = sum (1, n) (\i. f (i-1))``,
Induct_on `n` THEN RW_TAC real_ss [sum]);
(* ------------------------------------------------------------------------- *)
(* SUM_SHIFT_P			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_SHIFT_P = store_thm("SUM_SHIFT_P",
  ``!n p f. sum (p, n) (\i. f ((i+1))) = sum (p+1, n) f``,
RW_TAC std_ss []
++ Induct_on `n`
++ RW_TAC real_ss [sum]
++ RW_TAC real_ss [sum]);
(* ------------------------------------------------------------------------- *)
(* SUM_C_EQ			                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_C_EQ = store_thm("SUM_C_EQ",
  ``!n m (c:real). sum (n,SUC m) (\i. c)= &(m + 1)*c``,
RW_TAC std_ss []
++ Induct_on`m`
++ RW_TAC real_ss [sum]
++ ONCE_REWRITE_TAC [sum]
++ RW_TAC std_ss []
++ ONCE_REWRITE_TAC [GSYM add_ints]
++ RW_TAC real_ss [SUC_ONE_ADD]
++ ONCE_REWRITE_TAC [GSYM add_ints]
++ REAL_ARITH_TAC);
(* ------------------------------------------------------------------------- *)
(* SUM_SWITCH_SUM		                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_SWITCH_SUM = store_thm("SUM_SWITCH_SUM",
  ``!f n1 n2 m1 m2. 
       sum (n1,m1) (\i. sum (n2,m2)(\j. f i j)) = 
       sum (n2,m2) (\j. sum (n1,m1)(\i. f i j))``,
RW_TAC std_ss []
++ Induct_on `m1`
++ RW_TAC real_ss [sum,SUM_0]
++ RW_TAC real_ss [sum,REAL_ADD_ASSOC,ADD1]
++ POP_ORW
++ RW_TAC real_ss [SUM_ADD]);

(* ------------------------------------------------------------------------- *)
(* 	SUM_POS_LT	                                             *)
(* ------------------------------------------------------------------------- *)
val SUM_POS_LT = store_thm("SUM_POS_LT",
  ``!f. (!n. 0 < f n) ==> (!m n. 0 < sum (m,SUC n) f)``,
RW_TAC std_ss []
++ Induct_on `n`
>> (RW_TAC real_ss [sum])
++ ONCE_REWRITE_TAC [sum]
++ METIS_TAC [REAL_LT_ADD]);

(* ---------------------------------------------------*)
(* 	BINOMIAL_DEF1	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF1 = store_thm("BINOMIAL_DEF1",
  ``!n. binomial n  0 = 1``,
Cases_on `n` THEN REWRITE_TAC [binomial_def]); 
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF2	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF2 = store_thm("BINOMIAL_DEF2",
  ``!n k. n < k ==> (binomial n k = 0)``,
Induct_on `n`
>> (Cases_on `k`
>> (RW_TAC real_ss [])
   ++ REWRITE_TAC [binomial_def])
++ Cases_on `k`
>> (RW_TAC real_ss [])
++ RW_TAC arith_ss [binomial_def]);
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF3	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF3 = store_thm("BINOMIAL_DEF3",
  ``!n. (binomial n n = 1)``,
Induct_on `n` THEN 
REWRITE_TAC [binomial_def] THEN 
RW_TAC arith_ss [BINOMIAL_DEF2]);
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF4	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF4 = store_thm("BINOMIAL_DEF4",
  ``!n k. (binomial (SUC n) (SUC k) = 
       	   binomial n (SUC k) + binomial n k)``,
REWRITE_TAC [binomial_def]); 
(* -------------------------------------------------- *)
(* 	BINOMIAL_DEF5	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_DEF5 = store_thm("BINOMIAL_DEF5",
  ``!n k. k <= n ==> (binomial n k <> 0)``,
Induct_on `n`
>> (Cases_on `k`
   >> (RW_TAC real_ss []
      ++ RW_TAC real_ss [binomial_def])
   ++ RW_TAC real_ss [])
++ Cases_on `k`
>> (RW_TAC real_ss []
   ++ RW_TAC arith_ss [binomial_def])
++ RW_TAC arith_ss [binomial_def]);
(* -------------------------------------------------- *)
(* 	BINOMIAL_FACT	                              *)
(* -------------------------------------------------- *)
val BINOMIAL_FACT = store_thm("BINOMIAL_FACT",
  ``!a b. binomial (a+b) b * (FACT a * FACT b) = FACT (a+b)``,
Induct_on `b`
>> (REWRITE_TAC[BINOMIAL_DEF1,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ Induct_on `a`
>> (REWRITE_TAC[BINOMIAL_DEF3,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ `SUC a + SUC b = SUC (SUC a + b)` by RW_TAC arith_ss [ADD_CLAUSES]
++ (ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB])
++ POP_ORW
++ `binomial (SUC a + b) (SUC b) * (FACT (SUC a) * FACT (SUC b)) =
    (binomial (a + SUC b) (SUC b) * (FACT a * FACT (SUC b))) * SUC a` 
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC[]
++ POP_ORW
++ `binomial (SUC a + b) b * (FACT (SUC a) * FACT (SUC b)) =
                       (binomial (SUC a + b) b * (FACT (SUC a) * FACT b)) * SUC b`
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC [ADD_CLAUSES, FACT]
++ REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]
++ `SUC a + SUC b = SUC (SUC (a + b))` by RW_TAC arith_ss [ADD_CLAUSES]
++ ASM_REWRITE_TAC[]
++ RW_TAC arith_ss []);
(* --------------------------------------------------- *)
(* 	BINOMIAL_DEF6	                               *)
(* --------------------------------------------------- *)
val BINOMIAL_DEF6 = store_thm("BINOMIAL_DEF6",
  ``!n. (binomial (SUC n) 1 = SUC n)``,
RW_TAC std_ss []
++ ONCE_REWRITE_TAC[ONE]
++ (MP_TAC o Q.SPECL [`n`,`SUC 0`]) BINOMIAL_FACT
++ ONCE_REWRITE_TAC[FACT]
++ ONCE_REWRITE_TAC[GSYM ONE]
++ ONCE_REWRITE_TAC[ADD_COMM]
++ ONCE_REWRITE_TAC[GSYM SUC_ONE_ADD]
++ ONCE_REWRITE_TAC[FACT]
++ STRIP_TAC
++ FULL_SIMP_TAC real_ss [EQ_MULT_LCANCEL]
++ METIS_TAC [FACT_LESS, NOT_ZERO_LT_ZERO]);
(* --------------------------------------------------- *)
(* 	BINOMIAL_DEF7	                               *)
(* --------------------------------------------------- *)
val BINOMIAL_DEF7 = store_thm("BINOMIAL_DEF7",
  ``!n k. 0 <= binomial n k``,
Induct_on `n`
++ RW_TAC arith_ss [binomial_def]
++ RW_TAC arith_ss [binomial_def]);
(* --------------------------------------------------- *)
(* 	BINOMIAL_FACT	                               *)
(* --------------------------------------------------- *)
val BINOMIAL_FACT = store_thm("BINOMIAL_FACT",
  ``!a b. binomial (a+b) b * (FACT a * FACT b) = FACT (a+b)``,
Induct_on `b`
 >> (REWRITE_TAC[BINOMIAL_DEF1,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ Induct_on `a`
>> (REWRITE_TAC[BINOMIAL_DEF3,FACT,ADD_CLAUSES,MULT_CLAUSES])
++ `SUC a + SUC b = SUC (SUC a + b)` by RW_TAC arith_ss [ADD_CLAUSES]
++ ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]
++ POP_ORW
++  `binomial (SUC a + b) (SUC b) * (FACT (SUC a) * FACT (SUC b)) =
                   (binomial (a + SUC b) (SUC b) * (FACT a * FACT (SUC b))) * SUC a` 
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC[]
++ POP_ORW
++ `binomial (SUC a + b) b * (FACT (SUC a) * FACT (SUC b)) =
                       (binomial (SUC a + b) b * (FACT (SUC a) * FACT b)) * SUC b`
by REWRITE_TAC[FACT,ADD_CLAUSES]
>> (PROVE_TAC[MULT_ASSOC,MULT_SYM])
++ ASM_REWRITE_TAC [ADD_CLAUSES, FACT]
++ REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]
++ `SUC a + SUC b = SUC (SUC (a + b))` by RW_TAC arith_ss [ADD_CLAUSES]
++ ASM_REWRITE_TAC[]
++ RW_TAC arith_ss []);
(* -----------------BINOMIAL_DEF2--------------------------- *)
val BINOMIAL_DEF2 = store_thm("BINOMIAL_DEF2",
  ``!n k. n < k ==> (binomial n k = 0)``,
Induct_on `n`
>> (Cases_on `k`
   >> (RW_TAC real_ss [])
   ++ REWRITE_TAC [binomial_def])
++ Cases_on `k`
>> (RW_TAC real_ss [])
++ RW_TAC arith_ss [binomial_def]);
(* -----------------BINOMIAL_DEF3--------------------------- *)
val BINOMIAL_DEF3 = store_thm("BINOMIAL_DEF3",
  ``!n. (binomial n n = 1)``,
Induct_on `n` THEN REWRITE_TAC [binomial_def] THEN RW_TAC arith_ss [BINOMIAL_DEF2]);
(* -----------------BINOMIAL_DEF4--------------------------- *)
val BINOMIAL_DEF4 = store_thm("BINOMIAL_DEF4",
  ``!n k. (binomial (SUC n) (SUC k) = binomial n (SUC k) + binomial n k)``,
REWRITE_TAC [binomial_def]); 
(* -----------------BINOMIAL_DEF6--------------------------- *)
val BINOMIAL_DEF6 = store_thm("BINOMIAL_DEF6",
  ``!n. (binomial (SUC n) 1 = SUC n)``,
RW_TAC std_ss []
++ ONCE_REWRITE_TAC[ONE]
++ (MP_TAC o Q.SPECL [`n`,`SUC 0`]) BINOMIAL_FACT
++ ONCE_REWRITE_TAC[FACT]
++ ONCE_REWRITE_TAC[GSYM ONE]
++ ONCE_REWRITE_TAC[ADD_COMM]
++ ONCE_REWRITE_TAC[GSYM SUC_ONE_ADD]
++ ONCE_REWRITE_TAC[FACT]
++ STRIP_TAC
++ FULL_SIMP_TAC real_ss [EQ_MULT_LCANCEL]
++ METIS_TAC [FACT_LESS, NOT_ZERO_LT_ZERO]);
(* --------------------------------------------------------- *)
(* 	EXP_PASCAL_REAL	                                     *)
(* --------------------------------------------------------- *)
val EXP_PASCAL_REAL = store_thm("EXP_PASCAL_REAL",
  ``!(a:real) (b:real) n. 
((a + b) pow n = REAL_SUM_IMAGE (\x. &(binomial n x) * a pow (n - x) * b pow x) (count (SUC n)))``,
Induct_on `n`
>> (RW_TAC real_ss [pow, BINOMIAL_DEF3]
   ++ `count 1 = 0 INSERT {}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
   ++ POP_ORW
   ++ RW_TAC real_ss [REAL_SUM_IMAGE_SING,BINOMIAL_DEF1])
++ ONCE_REWRITE_TAC [pow]
++ POP_ORW
++ RW_TAC real_ss []
++ ONCE_REWRITE_TAC [REAL_ADD_RDISTRIB]
++ `FINITE (count (SUC n))` by METIS_TAC [COUNT_SUC, FINITE_INSERT,FINITE_COUNT]
++ RW_TAC real_ss [GSYM REAL_SUM_IMAGE_CMUL]
++ RW_TAC real_ss [REAL_SUM_IMAGE_COUNT]
++ Know ` sum (0,SUC n) (\x. a* (&binomial n x * a pow (n  - x) * b pow x)) =
a pow (n+1)+ sum (1, SUC n) (\x. a*(&binomial n x * a pow (n - x) * b pow x)) `
>> (RW_TAC real_ss [SUM_0_SUM_1, BINOMIAL_DEF1,sum, BINOMIAL_DEF2,GSYM pow,ADD1]
   ++ RW_TAC real_ss [])
++ DISCH_TAC
++ POP_ORW
++ Know ` sum (0,SUC n) (\x. b* (&binomial n x * a pow (n - x) * b pow x)) =
sum (0, n) (\x. b*(&binomial n x * a pow (n - x) * b pow x)) + b pow (n+1) `
>> (RW_TAC real_ss [sum, BINOMIAL_DEF3,GSYM pow,ADD1]
   ++ RW_TAC real_ss [])
++ DISCH_TAC
++ POP_ORW
++ RW_TAC real_ss [GSYM ADD1,pow]
++ RW_TAC real_ss [SUM_SHIFT]
++ RW_TAC real_ss [REAL_ADD_ASSOC]
++ Know ` sum (1,SUC n) (\x. a * (&binomial n x * a pow (n - x) * b pow x))=
sum (1, n) (\x. &binomial n x * a pow (n - x + 1) * b pow x)`
>> (RW_TAC real_ss [sum, BINOMIAL_DEF2]
   ++ MATCH_MP_TAC SUM_EQ
   ++ RW_TAC real_ss []
   ++ RW_TAC real_ss [REAL_MUL_ASSOC]
   ++ Know ` a * &binomial n r * a pow (n - r)= &binomial n r * a pow (n + 1 - r)`
   >> (ONCE_REWRITE_TAC [REAL_MUL_COMM]
      ++ RW_TAC real_ss [REAL_MUL_ASSOC]
      ++ Know ` a pow (n - r) * a= a pow (n + 1 - r) `
      >> (ONCE_REWRITE_TAC [REAL_MUL_COMM]
      	 ++ RW_TAC real_ss [GSYM pow]
	 ++ RW_TAC real_ss [ADD1])
      ++ RW_TAC real_ss [])
   ++ RW_TAC real_ss [])
++ RW_TAC real_ss []
++ POP_ORW
++ ONCE_REWRITE_TAC [REAL_ADD_COMM]
++ Know ` sum (1,n) (\i. b * (&binomial n (i - 1) * a pow (n - (i - 1)) * b pow (i - 1)))=
sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i) `
>> (MATCH_MP_TAC SUM_EQ
   ++ RW_TAC real_ss [REAL_MUL_ASSOC]
   ++ ONCE_REWRITE_TAC [REAL_MUL_COMM]
   ++ RW_TAC real_ss [REAL_MUL_ASSOC]
   ++ Suff ` b pow (r - 1) * b= b pow r `
   >> (RW_TAC real_ss [])
   ++ `r=SUC (r - 1)` by RW_TAC real_ss []	
   ++ ONCE_ASM_REWRITE_TAC []
   ++ RW_TAC real_ss [pow, ADD, REAL_MUL_COMM]
   ++ RW_TAC real_ss [])
++ RW_TAC real_ss[]
++ POP_ORW
++ Know ` sum (1,n) (\x. &binomial n x * a pow (n - x + 1) * b pow x) +
    sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i)=
sum (1,n) (\i. &binomial (SUC n) (SUC (i-1)) * a pow (n - i + 1) * b pow i)`
>> (RW_TAC real_ss [GSYM SUM_ADD]
   ++ MATCH_MP_TAC SUM_EQ
   ++ RW_TAC real_ss [BINOMIAL_DEF4]
   ++ ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC]
   ++ RW_TAC real_ss [GSYM REAL_ADD_RDISTRIB,ADD1]
   ++ RW_TAC real_ss [])
++ RW_TAC real_ss [GSYM pow]
++ RW_TAC real_ss[]
++ `b pow (SUC n) +
    (a pow (SUC n) +
     sum (1,n) (\x. &binomial n x * a pow (n - x + 1) * b pow x)) +
    sum (1,n) (\i. &binomial n (i - 1) * a pow (n - i + 1) * b pow i)= 
b pow (SUC n)+ a pow (SUC n) +
     sum (1,n) (\i. &binomial (SUC n) (SUC (i - 1)) * a pow (n - i + 1) * b pow i)` by ALL_TAC
>> (RW_TAC real_ss []
   ++ ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]
   ++ RW_TAC real_ss [REAL_EQ_LADD]
   ++ ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]
   ++ RW_TAC real_ss [REAL_EQ_LADD])
++ FULL_SIMP_TAC std_ss[REAL_ADD_ASSOC]
++ POP_ORW
++ `sum (1,SUC (SUC n))
      (\i. (\i. &binomial (SUC n) i * a pow (SUC n - i) *  b pow i) (i-1))=
sum (0,SUC (SUC n))
      (\i. &binomial (SUC n) i * a pow (SUC n - i) *  b pow i)` by RW_TAC real_ss [GSYM SUM_SHIFT]
++ FULL_SIMP_TAC real_ss []
++ POP_ORW
++ ONCE_REWRITE_TAC [sum]
++ ONCE_REWRITE_TAC [SUM_0_SUM_1]
++ RW_TAC real_ss [pow,BINOMIAL_DEF1, BINOMIAL_DEF3]
++ ONCE_REWRITE_TAC [GSYM pow]
++ ONCE_REWRITE_TAC [ADD1]
++ ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC]
++ `a pow (n + 1) +
    (sum (1,n) (\i. &binomial (n + 1) i * a pow (n + 1 - i) * b pow i) +
     b pow (n + 1))= b pow (n + 1) +
    (a pow (n + 1) +
    sum (1,n) (\i. &binomial (n + 1) i * a pow (n + 1 - i) * b pow i))` by REAL_ARITH_TAC
++ POP_ORW
++ RW_TAC real_ss [REAL_EQ_LADD]
++ MATCH_MP_TAC SUM_EQ
++ RW_TAC real_ss [ADD1]);
(* ---------------------------------------------------------- *)
(* 	EXP_PASCAL_REAL1	                              *)
(* ---------------------------------------------------------- *)
val EXP_PASCAL_REAL1 = store_thm("EXP_PASCAL_REAL1",
  ``!(a:real) (b:real) n. 
((a + b) pow n = 
 sum_set (count (SUC n))  (\x. &(binomial n x) * a pow (n - x) * b pow x))``,
RW_TAC std_ss[sum_set_def,EXP_PASCAL_REAL]);

(*------------------------------------------------------------*)

(*-----------------num_neq------------------------------------*)
 val num_neq = store_thm("num_neq",
  ``!a b:num.  (a <> b) <=> a < b \/ b < a``,
RW_TAC std_ss []
++ RW_TAC std_ss [NOT_NUM_EQ]
++ EQ_TAC
>> (RW_TAC arith_ss[])
++ RW_TAC arith_ss[]);
(*------------------disj_thm---------------------------------*)
val disj_thm = store_thm("disj_thm",
  ``!X (m:num) (n:num).(m <> n)==>  DISJOINT ((PREIMAGE X {Normal &m} INTER p_space p) ) ((PREIMAGE X {Normal &n} INTER p_space p) )``,
RW_TAC std_ss [DISJOINT_ALT]
++ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]
++ RW_TAC std_ss [DISJOINT_ALT]
++ FULL_SIMP_TAC real_ss [IN_INTER,IN_PREIMAGE,IN_SING]);


(*--------------k_out_n_lemma1--------------------------*)
val k_out_n_lemma1 = store_thm("k_out_n_lemma1",
  ``!p s n k.
       prob_space p /\ 
       ((\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN ((count n) -> events p)) ==> 
        ((IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p) (count n)) SUBSET events p)``,
FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]
++ RW_TAC std_ss[]
++ RW_TAC std_ss[SUBSET_DEF]
++ FULL_SIMP_TAC real_ss [IN_IMAGE,IN_FUNSET,IN_COUNT]);
(*------------------k_out_n_lemma2---------------------*)
val k_out_n_lemma2 = store_thm("k_out_n_lemma2",
  ``!k n:num. 
       {x |  k<= x /\ x < n} = {x |  k<= x } INTER {x |x < n}``,
SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
(*----------------------k_out_ntemp1-------------------*)
val k_out_ntemp1 = store_thm("k_out_ntemp1",
  ``!k n:num. 
       n INSERT {x |  k <= x /\ x < n} =  
       n INSERT {x | x < n /\  k <= x }``,
SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]
++ METIS_TAC[]);
(*--------------------------k_out_n_temp2--------------*)
val k_out_n_temp2 = store_thm("k_out_n_temp2",
  ``!k n:num. 
       {x | x < n /\ k <= x} = {x |x < n} INTER {x | k <= x}``,
SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
(*-------------------------------------------------------*)
(*val k_out_n_temp1 = store_thm("k_out_n_temp1",
  ``!k n:num.  {x |  k <= x /\ x < (SUC n)}  = n INSERT  {x | k <= x /\ x < n}``,
RW_TAC std_ss[k_out_ntemp1]
++ RW_TAC std_ss[k_out_n_temp2]
++ RW_TAC std_ss[GSYM count_def]
++ ` n INSERT count n INTER {x | k <= x} =  
     (n INSERT count n) INTER {x | k <= x}` by ALL_TAC
>> (RW_TAC std_ss[GSYM COUNT_SUC]
   ++ RW_TAC std_ss[]);
e (KNOW_TAC (``{x | k <= x /\ x < n} = {x |  x < n /\ k <= x}``));
e (SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
e (METIS_TAC[]);
e (RW_TAC std_ss[k_out_ntemp1]);
e (RW_TAC std_ss[k_out_n_lemma2]);
e (SRW_TAC[][EXTENSION,GSPECIFICATION,IN_INSERT]);
val k_out_n_temp1 = top_thm();
drop();
*)
(*---------------------k_out_n_lemma3---------------------*)
val k_out_n_lemma3 = store_thm("k_out_n_lemma3",
  ``!k n:num. FINITE {x | k <= x /\ x < n}``,
GEN_TAC
++ RW_TAC std_ss[k_out_n_lemma2]
++ FULL_SIMP_TAC std_ss[k_out_n_lemma2]
++ MATCH_MP_TAC FINITE_INTER
++ DISJ2_TAC
++ ONCE_REWRITE_TAC[GSYM count_def]
++ RW_TAC std_ss[FINITE_COUNT]);
(*------------------k_out_n_lemma4------------------------*)
val k_out_n_lemma4 = store_thm("k_out_n_lemma4",
  ``!k (n:num). (k < n) ==>  (({x | k <= x /\ x < n} UNION count k) = count n)``,
SRW_TAC[][EXTENSION,IN_COUNT,GSPECIFICATION,IN_UNION]
++ EQ_TAC
>> (RW_TAC arith_ss[])
   ++ RW_TAC arith_ss[]);

val _ = export_theory();
