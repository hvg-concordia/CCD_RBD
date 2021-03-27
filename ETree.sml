
(* ========================================================================= *)
(* File Name: ETree.sml	          	                                     *)
(*---------------------------------------------------------------------------*)
(*          Description: Formalization of Event Trees using		     *)	
(* 	    		 Higher-order Logic Theorem Proving                  *)
(*                                                                           *)
(*          HOL4-Kananaskis 13 		 			     	     *)
(*									     *)
(*	    Author : Mohamed Abdelghany             		     	     *)
(*                                              			     *)
(* 	    Department of Electrical and Computer Engineering (ECE)          *)
(*	    Concordia University                                             *)
(*          Montreal, Quebec, Canada, 2021                                   *)
(*                                                                           *)
(* ========================================================================= *)

app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "real_probabilityTheory",
	  "numTheory", "dep_rewrite", "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory","real_sigmaTheory",
	  "indexedListsTheory", "listLib", "bossLib", "metisLib", "realLib", "numLib", "combinTheory",
          "arithmeticTheory","boolTheory", "listSyntax", "lebesgueTheory",
	  "real_sigmaTheory", "cardinalTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax lebesgueTheory real_sigmaTheory cardinalTheory;


val _ = new_theory "ETree";

(*---------------------------------------------------------------------------------------------------*)

val disjoint = new_definition ("disjoint",
 ``!A. disjoint A = !a b. a IN A /\ b IN A /\ (a <> b) ==> (a INTER b = {})``);

val disjointI = store_thm ("disjointI",
 ``(!a b . a IN A ==> b IN A ==> (a <> b) ==> (a INTER b = {})) ==> disjoint A``, METIS_TAC [disjoint]);

val disjointD = store_thm ("disjointD",
 ``disjoint A ==> a IN A ==> b IN A ==> (a <> b) ==> (a INTER b = {})``, METIS_TAC [disjoint]);

val disjoint_empty = store_thm ("disjoint_empty",
 ``disjoint {}``, rw [disjoint]);
 
val op by = BasicProvers.byA;
type_abbrev ("SET", ``:('a -> bool)``);
(*---------------------------------------------------------------------------------------------------*)

		    (*--------------------------------------------------*)  
		    (*          Event Tree Analysis in Set Theory       *)
		    (*--------------------------------------------------*)
			      
(*----------------------------*)  
(*        Definitions         *)
(*----------------------------*)

val EVENT_OUTCOME_SPACE_DEF = Define
`EVENT_OUTCOME_SPACE W = {x | x IN W /\ disjoint W /\ FINITE W}`;

val INTER_CARTESIAN_DEF = Define
`INTER_CARTESIAN W1 W2 = {(x INTER y) | x IN EVENT_OUTCOME_SPACE W1 /\ y IN EVENT_OUTCOME_SPACE W2}`;

val ETREE_CARTN_PROD_DEF = Define
` ETREE_CARTN_PROD W1 W2 = {x | x IN INTER_CARTESIAN W1 W2 /\ disjoint (INTER_CARTESIAN W1 W2)}`;

val EVENT_OUTCOME_SPACE_OK_DEF = Define
`EVENT_OUTCOME_SPACE_OK W <=> disjoint W /\ FINITE W`;

val N_ETREE_CARTN_PROD_DEF = Define
`N_ETREE_CARTN_PROD S WN = pred_set$ITSET (\W1 W2. ETREE_CARTN_PROD W1 W2) S WN`;

val U = UTF8.chr;
val CARTESIAN_PRODUCT =  U 0x02297;
val OMEGA =  U 0x003A9;
val INTER =  U 0x02229;
val TRUE  =  U 0x022A8;
val N     =  U 0x0039D;
val L     =  U 0x1D473;
val C     =  U 0x00043;

val _ = Unicode.unicode_version {u = OMEGA, tmnm = "EVENT_OUTCOME_SPACE"};
val _ = Unicode.unicode_version {tmnm = "INTER_CARTESIAN", u = INTER^CARTESIAN_PRODUCT};
val _ = Unicode.unicode_version {u = CARTESIAN_PRODUCT, tmnm = "ETREE_CARTN_PROD"};
val _ = Unicode.unicode_version {tmnm = "EVENT_OUTCOME_SPACE_OK", u = OMEGA^TRUE};
val _ = Unicode.unicode_version {tmnm = "N_ETREE_CARTN_PROD", u = CARTESIAN_PRODUCT^N};				 
(*---------------------------------------------------------------------------------------------------*)

val POP_ORW = pop_assum (fn th => once_rewrite_tac[th]);
val absorption = #1 (EQ_IMP_RULE (SPEC_ALL ABSORPTION));
val delete_non_element = #1 (EQ_IMP_RULE (SPEC_ALL DELETE_NON_ELEMENT));
(*---------------------------------------------------------------------------------------------------*)

(*----------------------------*)  
(*        Lemmas              *)
(*----------------------------*)

val CATRESIAN_PRODUCT_COMM = store_thm("CATRESIAN_PRODUCT_COMM",
  ``! W1 W2. $⊗ W1 W2 = $⊗ W2 W1``,
once_rewrite_tac [ETREE_CARTN_PROD_DEF]
\\ rw [EXTENSION]
\\ EQ_TAC
>- (once_rewrite_tac[INTER_CARTESIAN_DEF]
   \\ rw [EXTENSION]
      >- (Q.EXISTS_TAC `y`
      	 \\ Q.EXISTS_TAC `x'`
	 \\ metis_tac [])
   \\imp_res_tac disjointD
   \\ irule disjointI
   \\ rw[]
   \\ first_x_assum (mp_tac o Q.SPECL[`x'' ∩ y'`])
   \\ rw []
   \\ sg `(∃x y. (x'' ∩ y' = x ∩ y) ∧ x ∈ EVENT_OUTCOME_SPACE W1 ∧ y ∈ EVENT_OUTCOME_SPACE W2)`
      >-(metis_tac[INTER_COMM])
   \\ metis_tac [INTER_COMM])
\\ once_rewrite_tac[INTER_CARTESIAN_DEF]
\\ rw [EXTENSION]
   >-( Q.EXISTS_TAC `y`
       \\ Q.EXISTS_TAC `x'`
       \\ metis_tac [])
\\imp_res_tac disjointD
\\ irule disjointI
\\ rw[]
\\ first_x_assum (mp_tac o Q.SPECL[`x'' ∩ y'`])
\\ rw []
\\ metis_tac [INTER_COMM]);
(*---------------------------------------------------------------------------------------------------*)

val INTER_CARTESIAN_COMM = store_thm("INTER_CARTESIAN_COMM",
  ``! W1 W2. INTER_CARTESIAN W1 W2 =  INTER_CARTESIAN W2 W1``, 

rw []
\\ once_rewrite_tac[INTER_CARTESIAN_DEF]
\\ rw [EXTENSION]
\\ EQ_TAC
   >- (  rw []
      	 \\ Q.EXISTS_TAC `y`
      	 \\ Q.EXISTS_TAC `x'`
	 \\ metis_tac [])
\\ rw []
\\ Q.EXISTS_TAC `y`
\\ Q.EXISTS_TAC `x'`
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val CHOICE_EXISTS =
    TAC_PROOF
    (([], (“?CHOICE. !s:'a set. ~(s = EMPTY) ==> (CHOICE s) IN s”)),
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY] THEN
     EXISTS_TAC (“\s. @x:'a. x IN s”) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV SELECT_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REWRITE_TAC []);
(*---------------------------------------------------------------------------------------------------*)

val IN_ETREE_CARTN_PROD = store_thm("IN_ETREE_CARTN_PROD",
  ``!x W1 W2.
  x IN ETREE_CARTN_PROD W1 W2 <=> (x IN (INTER_CARTESIAN W1 W2)) /\ disjoint (INTER_CARTESIAN W1 W2)``,
rw[EXTENSION,ETREE_CARTN_PROD_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_INTER_CARTESIAN = store_thm("IN_INTER_CARTESIAN",
  ``! x W1 W2. x IN INTER_CARTESIAN W1 W2 <=>
(?x' y'. (x = x' INTER y') /\ x' IN EVENT_OUTCOME_SPACE W1 /\ y' IN EVENT_OUTCOME_SPACE W2)``,
rw [EXTENSION, INTER_CARTESIAN_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_INTER_CARTESIAN_CARTESIAN1 = store_thm("IN_INTER_CARTESIAN_CARTESIAN1",
``! x X Y Z. x ∈ INTER_CARTESIAN (ETREE_CARTN_PROD X Y) Z <=>
(?x' y'. (x = x' INTER y') /\ x' IN EVENT_OUTCOME_SPACE (ETREE_CARTN_PROD X Y)
     	      	       	   /\ y' IN EVENT_OUTCOME_SPACE Z)``,
rw [EXTENSION, INTER_CARTESIAN_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_INTER_CARTESIAN_CARTESIAN2 = store_thm("IN_INTER_CARTESIAN_CARTESIAN2",
``! x X Y Z. x ∈ INTER_CARTESIAN X (ETREE_CARTN_PROD Y Z) <=>
(?x' y'. (x = x' INTER y') /\ x' IN EVENT_OUTCOME_SPACE X
     	      	       	   /\ y' IN EVENT_OUTCOME_SPACE (ETREE_CARTN_PROD Y Z))``,
rw [EXTENSION, INTER_CARTESIAN_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_INTER_CARTESIAN_INTER1 = store_thm("IN_INTER_CARTESIAN_INTER1",
``! x X Y Z. x ∈ INTER_CARTESIAN (INTER_CARTESIAN X Y) Z <=>
(?x' y'. (x = x' INTER y') /\ x' IN EVENT_OUTCOME_SPACE (INTER_CARTESIAN  X Y)
     	      	       	   /\ y' IN EVENT_OUTCOME_SPACE Z)``,
rw [EXTENSION, INTER_CARTESIAN_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_INTER_CARTESIAN_INTER2 = store_thm("IN_INTER_CARTESIAN_INTER2",
``! x X Y Z. x ∈ INTER_CARTESIAN X (INTER_CARTESIAN Y Z) <=>
(?x' y'. (x = x' INTER y') /\ x' IN EVENT_OUTCOME_SPACE X
     	      	       	   /\ y' IN EVENT_OUTCOME_SPACE (INTER_CARTESIAN  Y Z))``,
rw [EXTENSION, INTER_CARTESIAN_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_EVENT_OUTCOME_SPACE= store_thm("IN_EVENT_OUTCOME_SPACE",
``!x W. x IN EVENT_OUTCOME_SPACE W <=> x IN W /\  disjoint W ∧ FINITE W ``,
rw [EXTENSION, EVENT_OUTCOME_SPACE_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_EVENT_OUTCOME_SPACE_INSERT= store_thm("IN_EVENT_OUTCOME_SPACE_INSERT",
``!x W h. x IN EVENT_OUTCOME_SPACE (h INSERT W) <=> x IN (h INSERT W) /\ 
       	       		      	     	  disjoint (h INSERT W) ∧ FINITE (h INSERT W) ``,
rw [EXTENSION, EVENT_OUTCOME_SPACE_DEF]);
(*---------------------------------------------------------------------------------------------------*)
val IN_EVENT_OUTCOME_SPACE_CARTESIAN= store_thm("IN_EVENT_OUTCOME_SPACE_CARTESIAN",
``!a X Y. a IN EVENT_OUTCOME_SPACE (ETREE_CARTN_PROD X Y) <=> a IN (ETREE_CARTN_PROD X Y)
					        /\ disjoint (ETREE_CARTN_PROD X Y)
					        /\ FINITE (ETREE_CARTN_PROD X Y)``,
rw [EXTENSION, EVENT_OUTCOME_SPACE_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val IN_EVENT_OUTCOME_SPACE_INTER_CARTESIAN= store_thm("IN_EVENT_OUTCOME_SPACE_INTER_CARTESIAN",
``!a X Y. a IN EVENT_OUTCOME_SPACE (INTER_CARTESIAN X Y) <=> a IN (INTER_CARTESIAN X Y)
					           /\ disjoint (INTER_CARTESIAN X Y)
					           /\ FINITE (INTER_CARTESIAN X Y)``,
rw [EXTENSION, EVENT_OUTCOME_SPACE_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_CARTESIAN = store_thm("DISJOINT_CARTESIAN",
``! X Y. disjoint (ETREE_CARTN_PROD X Y)``,
rw []
\\ irule disjointI
\\ rw[]
\\ fs[IN_ETREE_CARTN_PROD,IN_INTER_CARTESIAN, IN_EVENT_OUTCOME_SPACE]
\\ fs[disjoint]
\\ rw []
\\ ntac 2 (pop_assum mp_tac)
\\ first_x_assum (mp_tac o Q.SPECL[`y'`,`y''`])
\\ first_x_assum (mp_tac o Q.SPECL[`x'`,`x''`])
\\ rw[]
\\ once_rewrite_tac [prove (``!a b c d. a INTER b INTER (c INTER d)
   = a INTER c INTER (b INTER d)``,rw[EXTENSION,INTER_DEF] \\ metis_tac[])]
\\ Cases_on `x' <> x''`
   >-(metis_tac[INTER_EMPTY])
\\ fs[]
\\ Cases_on `y' <> y''`
   >- (metis_tac[INTER_EMPTY])
\\ fs[]);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_INTER_CARTESIAN = store_thm("DISJOINT_INTER_CARTESIAN",
``! X Y. disjoint (INTER_CARTESIAN  X Y)``,
rw []
\\ irule disjointI
\\ rw[]
\\ fs[IN_INTER_CARTESIAN, IN_EVENT_OUTCOME_SPACE, disjoint]
\\ rw []
\\ pop_assum mp_tac
\\ first_x_assum (mp_tac o Q.SPECL[`y'`,`y''`])
\\ first_x_assum (mp_tac o Q.SPECL[`x'`,`x''`])
\\ rw[]
\\ once_rewrite_tac [prove (``!a b c d. a INTER b INTER (c INTER d)
   = a INTER c INTER (b INTER d)``,rw[EXTENSION,INTER_DEF] \\ metis_tac[])]
\\ Cases_on `x' <> x''`
   >-(metis_tac[INTER_EMPTY])
\\ fs[]
\\ Cases_on `y' <> y''`
   >- (metis_tac[INTER_EMPTY])
\\ fs[]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_CARTN_PROD_EMPTY1 = store_thm("ETREE_CARTN_PROD_EMPTY1",
  `` ! W1. ETREE_CARTN_PROD W1 {} = {} ``,
rw [ETREE_CARTN_PROD_DEF]
\\ rw [EXTENSION]
\\ CCONTR_TAC 
\\ fs [DISJOINT_INTER_CARTESIAN, INTER_CARTESIAN_DEF, IN_EVENT_OUTCOME_SPACE]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_CARTN_PROD_EMPTY2 = store_thm("ETREE_CARTN_PROD_EMPTY2",
  `` ! W1. ETREE_CARTN_PROD {} W1 = {} ``,
rw [ETREE_CARTN_PROD_DEF]
\\ rw [EXTENSION]
\\ CCONTR_TAC 
\\ fs [DISJOINT_INTER_CARTESIAN, INTER_CARTESIAN_DEF, IN_EVENT_OUTCOME_SPACE]);
(*---------------------------------------------------------------------------------------------------*)

val INTER_CARTESIAN_IMAGE_CROSS = store_thm("INTER_CARTESIAN_IMAGE_CROSS",
``!X Y. INTER_CARTESIAN X Y =  IMAGE (\ (n, m). n INTER m) ((EVENT_OUTCOME_SPACE X) CROSS (EVENT_OUTCOME_SPACE Y))``,
rw []
\\ once_rewrite_tac [INTER_CARTESIAN_DEF, IMAGE_DEF, IN_CROSS]
\\ once_rewrite_tac [EXTENSION]
\\ GEN_TAC
\\ EQ_TAC
   >-( rw [EXTENSION]
       \\ Q.EXISTS_TAC `(x', y)`
       \\ rw [])
\\ rw [EXTENSION]
\\ Q.EXISTS_TAC `FST x'`
\\ Q.EXISTS_TAC `SND x'`
\\ rw []
\\ sg `x' = (FST x',SND x')`
   >- (rw[GSYM PAIR])
\\ once_asm_rewrite_tac[]
\\ rw[INTER_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val FINITE_ETREE_CARTN_PROD = store_thm("FINITE_ETREE_CARTN_PROD",
``!W1 W2.  (disjoint W1) /\ (FINITE W1) /\
           (disjoint W2) /\ (FINITE W2) ==> (FINITE (ETREE_CARTN_PROD  W1 W2))``,
rw [ETREE_CARTN_PROD_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]
\\ rw [INTER_CARTESIAN_IMAGE_CROSS] 
\\ sg `FINITE (EVENT_OUTCOME_SPACE W1)`
   >-( rw [EVENT_OUTCOME_SPACE_DEF])
\\ sg ` FINITE (EVENT_OUTCOME_SPACE W2)`
   >-( rw [EVENT_OUTCOME_SPACE_DEF])
\\ match_mp_tac IMAGE_FINITE
\\ match_mp_tac FINITE_CROSS
\\ fs []);
(*---------------------------------------------------------------------------------------------------*)

val FINITE_INTER_CARTESIAN = store_thm("FINITE_INTER_CARTESIAN",
``!W1 W2.  (disjoint W1) /\ (FINITE W1) /\
           (disjoint W2) /\ (FINITE W2) ==> (FINITE (INTER_CARTESIAN  W1 W2))``,
rw [INTER_CARTESIAN_IMAGE_CROSS] 
\\ sg `FINITE (EVENT_OUTCOME_SPACE W1)`
   >-( rw [EVENT_OUTCOME_SPACE_DEF])
\\ sg ` FINITE (EVENT_OUTCOME_SPACE W2)`
   >-( rw [EVENT_OUTCOME_SPACE_DEF])
\\ match_mp_tac IMAGE_FINITE
\\ match_mp_tac FINITE_CROSS
\\ fs []);
(*---------------------------------------------------------------------------------------------------*)

(*--------------------*)
(*     Theorems       *)
(*--------------------*)

val ETREE_CARTN_PROD_ASOCC = store_thm("ETREE_CARTN_PROD_ASSOC",
``!X Y Z. $⊗ X ($⊗ Y Z) = $⊗ ($⊗ X Y) Z``,
rw []
\\ once_rewrite_tac [Once ETREE_CARTN_PROD_DEF]
\\ rw [EXTENSION]
\\ once_rewrite_tac [IN_INTER_CARTESIAN_CARTESIAN2]
\\ once_rewrite_tac [Once ETREE_CARTN_PROD_DEF]
\\ once_rewrite_tac [DISJOINT_INTER_CARTESIAN]
\\ once_rewrite_tac [Once ETREE_CARTN_PROD_DEF]
\\ once_rewrite_tac [IN_INTER_CARTESIAN_CARTESIAN1]
\\ once_rewrite_tac [Once ETREE_CARTN_PROD_DEF]
\\ once_rewrite_tac [DISJOINT_INTER_CARTESIAN]
\\ rw [EXTENSION]
\\ once_rewrite_tac [IN_EVENT_OUTCOME_SPACE_INTER_CARTESIAN]
\\ once_rewrite_tac [DISJOINT_INTER_CARTESIAN]
\\ EQ_TAC
   >-( rw []
       \\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
       \\ rw []
       \\ qpat_x_assum `y' ∈ INTER_CARTESIAN Y Z` mp_tac
       \\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
       \\ rw []
       \\ Q.EXISTS_TAC `x' ∩ x''`
       \\ Q.EXISTS_TAC `y''`
       \\ rw []
       	  >-(metis_tac [INTER_ASSOC])
	  >-( Q.EXISTS_TAC `x'`
       	      \\ Q.EXISTS_TAC `x''`
	      \\ rw [])
       \\  fs [EVENT_OUTCOME_SPACE_DEF]
       \\ metis_tac [FINITE_INTER_CARTESIAN])
\\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
\\ rw []
\\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
\\ rw []
\\ Q.EXISTS_TAC `x''`
\\ Q.EXISTS_TAC `y'' ∩ y'`
\\ rw []
   >-(metis_tac [INTER_ASSOC])
   >-( Q.EXISTS_TAC `y''`
       \\ Q.EXISTS_TAC `y'`
       \\ rw [])
\\ fs [EVENT_OUTCOME_SPACE_DEF]
\\ metis_tac [FINITE_INTER_CARTESIAN]);
(*---------------------------------------------------------------------------------------------------*)

val INTER_CARTESIAN_ASOCC = store_thm("INTER_CARTESIAN_ASOCC",
``!X Y Z. ∩⊗ X (∩⊗ Y Z) = ∩⊗ (∩⊗ X Y) Z``,
rw [EXTENSION]
\\ once_rewrite_tac [IN_INTER_CARTESIAN_INTER2]
\\ once_rewrite_tac [IN_INTER_CARTESIAN_INTER1]
\\ once_rewrite_tac [IN_EVENT_OUTCOME_SPACE_INTER_CARTESIAN]
\\ EQ_TAC
   >-( rw []
       \\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
       \\ qpat_x_assum `y' ∈ INTER_CARTESIAN Y Z` mp_tac
       \\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
       \\ rw []
       \\ Q.EXISTS_TAC `x' ∩ x''`
       \\ Q.EXISTS_TAC `y''`
       \\ rw []
       	  >-(metis_tac [INTER_ASSOC])
	  >-( Q.EXISTS_TAC `x'`
       	      \\ Q.EXISTS_TAC `x''`
	      \\ rw [])
          >-(metis_tac [DISJOINT_INTER_CARTESIAN])
       \\ fs [EVENT_OUTCOME_SPACE_DEF] \\ metis_tac [FINITE_INTER_CARTESIAN])
\\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
\\ rw []
\\ once_rewrite_tac [Once IN_INTER_CARTESIAN]
\\ rw []
\\ Q.EXISTS_TAC `x''`
\\ Q.EXISTS_TAC `y'' ∩ y'`
\\ rw []
   >-(metis_tac [INTER_ASSOC])
   >-( Q.EXISTS_TAC `y''`
       \\ Q.EXISTS_TAC `y'`
       \\ rw [])
   >-(metis_tac [DISJOINT_INTER_CARTESIAN])
\\  fs [EVENT_OUTCOME_SPACE_DEF] 
\\ metis_tac [FINITE_INTER_CARTESIAN]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_CARTN_PROD_ASOCC_COMM = store_thm("ETREE_CARTN_PROD_ASSOC_COMM",
``!X Y Z. ETREE_CARTN_PROD X (ETREE_CARTN_PROD Y Z) = ETREE_CARTN_PROD Y (ETREE_CARTN_PROD X Z)``,
rw []
\\ sg `!X Y Z. ETREE_CARTN_PROD X (ETREE_CARTN_PROD Y Z) =
               ETREE_CARTN_PROD (ETREE_CARTN_PROD X Y) Z`
   >-(rw [ETREE_CARTN_PROD_ASOCC])
\\ sg `! W1 W2. ETREE_CARTN_PROD W1 W2 =  ETREE_CARTN_PROD W2 W1`
   >-(rw [CATRESIAN_PRODUCT_COMM])
\\ ntac 2 (pop_assum mp_tac)
\\ metis_tac [boolTheory.LCOMM_THM]);
(*---------------------------------------------------------------------------------------------------*)

val INTER_CARTESIAN_ASSOC_COMM = store_thm("INTER_CARTESIAN_ASSOC_COMM",
``!X Y Z. ∩⊗ X (∩⊗ Y Z) = ∩⊗ Y (∩⊗ X Z)``,
rw []
\\ sg `!X Y Z. INTER_CARTESIAN X (INTER_CARTESIAN Y Z) =
               INTER_CARTESIAN (INTER_CARTESIAN  X Y) Z`
   >-(rw [INTER_CARTESIAN_ASOCC])
\\ sg `! W1 W2. INTER_CARTESIAN W1 W2 =  INTER_CARTESIAN W2 W1`
   >-(rw [INTER_CARTESIAN_COMM])
\\ ntac 2 (pop_assum mp_tac)
\\ metis_tac [boolTheory.LCOMM_THM]);
(*---------------------------------------------------------------------------------------------------*)

val COMMUTING_N_ETREE_CARTN_PROD_RECURSES = store_thm("COMMUTING_N_ETREE_CARTN_PROD_RECURSES",
``!W1 WN S. (FINITE S) ==> (N_ETREE_CARTN_PROD (W1 INSERT S) WN =
                        ETREE_CARTN_PROD W1 (N_ETREE_CARTN_PROD (S DELETE W1) WN))``,
rw []
\\ once_rewrite_tac [N_ETREE_CARTN_PROD_DEF]
\\ DEP_REWRITE_TAC [COMMUTING_ITSET_RECURSES]
\\ rw [ETREE_CARTN_PROD_ASOCC_COMM]);
(*---------------------------------------------------------------------------------------------------*)

val COMMUTING_N_ETREE_CARTN_PROD_INSERT = store_thm("COMMUTING_N_ETREE_CARTN_PROD_INSERT",
``!W1 WN S. (FINITE S) ==> ⊗Ν (W1 INSERT S) WN = ⊗Ν (S DELETE W1) ($⊗ W1 WN)``,
rw []
\\ once_rewrite_tac [N_ETREE_CARTN_PROD_DEF]
\\ DEP_REWRITE_TAC [COMMUTING_ITSET_INSERT]
\\ rw [ETREE_CARTN_PROD_ASOCC_COMM]);
(*---------------------------------------------------------------------------------------------------*)

val EVENT_OUTCOME_SPACE_OK_ETREE_CARTN_PROD = store_thm(
  "EVENT_OUTCOME_SPACE_OK_ETREE_CARTN_PROD",
   `` !W1 W2. Ω⊨ W1 ∧ Ω⊨ W2 ⇒ Ω⊨ ($⊗ W1 W2)``,
rw [EVENT_OUTCOME_SPACE_OK_DEF]
>-( rw [ETREE_CARTN_PROD_DEF]
    \\ rw [DISJOINT_INTER_CARTESIAN])
\\ rw [ETREE_CARTN_PROD_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]
\\ rw [INTER_CARTESIAN_IMAGE_CROSS] 
\\ sg `FINITE (EVENT_OUTCOME_SPACE W1)`
   >-( rw [EVENT_OUTCOME_SPACE_DEF])
\\ sg ` FINITE (EVENT_OUTCOME_SPACE W2)`
   >-( rw [EVENT_OUTCOME_SPACE_DEF])
\\ match_mp_tac IMAGE_FINITE
\\ match_mp_tac FINITE_CROSS
\\ fs []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

		    (*--------------------------------------------------*)  
		    (*          Event Tree Analysis in List Theory      *)
		    (*--------------------------------------------------*)
			         					
(*----------------------------------*)  
(*     New EVENT TREE Data Type     *)
(*----------------------------------*)

type_abbrev ("EVENT", ``:('a -> bool)``);

val _ = Datatype.Hol_datatype `EVENT_TREE = ATOMIC of ('a EVENT)
                                          | NODE of EVENT_TREE list
                                          | BRANCH of ('a EVENT) => EVENT_TREE `;

val ETREE_DEF = Define
`(ETREE (ATOMIC X) = X) /\
 (ETREE (NODE []) = {}) /\
 (ETREE (NODE (h::t)) = ETREE h UNION ETREE (NODE t)) /\
 (ETREE (BRANCH X Y)  =  X INTER ETREE Y)`;

val ET_PATH_DEF = Define
`(ET_PATH p [] = p_space p) /\
 (ET_PATH p (h::t)  = FOLDL (λa b. ETREE (BRANCH  a (ATOMIC b))) h t)`;

val EVENT_TREE_LIST_DEF = Define `EVENT_TREE_LIST L = MAP (\A. ATOMIC A) L`;
(*---------------------------------------------------------------------------------------------------*)

(*---------------------------------------*)  
(*     EVENT TREE Modeling Functions     *)
(*---------------------------------------*)

val ALL_BRANCHES_DEF = Define
`ALL_BRANCHES X L  = MAP (\a. ETREE (BRANCH  X (ATOMIC a))) L `;

val ETREE_TWO_STAIR_DEF = Define
`ETREE_TWO_STAIR L1 L2 = FLAT (MAP (\a. ALL_BRANCHES a L2) L1)`;

val ETREE_N_STAIR_DEF = Define
`ETREE_N_STAIR LN L = FOLDR (\ a b. ETREE_TWO_STAIR a b) LN L `;

val _ = Unicode.unicode_version {tmnm = "ETREE_TWO_STAIR", u = CARTESIAN_PRODUCT^L};

val _ = Unicode.unicode_version {tmnm = "ETREE_N_STAIR", u = CARTESIAN_PRODUCT^N^L};
(*---------------------------------------------------------------------------------------------------*)

(*---------------------------*)
(*    CONVERT DATA TYPES     *)
(*---------------------------*)

val LIST2_SET_LIST_DEF = Define
`LIST2_SET_LIST L = (MAP (\a. set a ) L)`;

val LIST2_SET_SET_DEF = Define
`LIST2_SET_SET L = set (MAP (\a. set a ) L)`;

val EVENT_OUTCOME_SPACE_CONDS_DEF = Define
`(EVENT_OUTCOME_SPACE_CONDS [] = T) /\
 (EVENT_OUTCOME_SPACE_CONDS (h::t) <=> (ALL_DISTINCT h) /\ (disjoint (set h)) /\ (EVENT_OUTCOME_SPACE_CONDS t) )`;
			    
val _ = Unicode.unicode_version {tmnm = "EVENT_OUTCOME_SPACE_CONDS", u = OMEGA^N^C};
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_INSERT_IMPL = store_thm("DISJOINT_INSERT_IMPL",
  ``!x L1. disjoint (x INSERT (set L1)) ==> disjoint (set L1)``,
rw[disjoint]);
(*---------------------------------------------------------------------------------------------------*)

val ALL_DISTINCT_DELETE1 = store_thm("ALL_DISTINCT_DELETE1",
  ``! h L. (ALL_DISTINCT (h::L)) ==> ((set L) DELETE (h) =  set L)``,
rw [EXTENSION]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val ALL_DISTINCT_DELETE2 = store_thm("ALL_DISTINCT_DELETE2",
  ``!h x L. (ALL_DISTINCT (LIST2_SET_LIST (h::L)))  ==>
    ((LIST2_SET_SET L) DELETE (set h) =  LIST2_SET_SET L)``,

rw [LIST2_SET_SET_DEF]
\\ DEP_REWRITE_TAC [ALL_DISTINCT_DELETE1]
\\ fs [LIST2_SET_LIST_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val SUBSET_BIGUNION = store_thm("SUBSET_BIGUNION",
  ``!f g. f SUBSET g ==> BIGUNION f SUBSET BIGUNION g``,
rw [BIGUNION]
\\ rw [SUBSET_DEF]
\\ Q.EXISTS_TAC `s`
\\ fs [SUBSET_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val INTER_BIGUNION = store_thm("INTER_BIGUNION",
``!s t. t ∩ BIGUNION s = BIGUNION {t ∩ x | x IN s}``,
rw [EXTENSION]
\\ SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION, IN_INTER]
\\ metis_tac [IN_INTER]);
(*---------------------------------------------------------------------------------------------------*)

val BIGUNION_CARTESIAN_SINGLETON = store_thm("BIGUNION_CARTESIAN_SINGLETON",
  ``!h W2. FINITE W2 /\ disjoint {h} /\ disjoint W2 ==> BIGUNION ($⊗ {h} W2) = h ∩ BIGUNION W2``,
rw [ETREE_CARTN_PROD_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]
\\ rw [INTER_CARTESIAN_DEF]
\\ rewrite_tac [IN_EVENT_OUTCOME_SPACE]
\\ rw [INTER_BIGUNION]
\\ fs []       
\\ rewrite_tac[SET_EQ_SUBSET]
\\ strip_tac
   >-( irule SUBSET_BIGUNION
       \\ rw [SUBSET_DEF]
       \\ Q.EXISTS_TAC `y`
       \\ rw []
       \\ fs []
       \\ sg `x' = h `
       	   >-( rw [EXTENSION]
	       \\ EQ_TAC
     	       	  >-( metis_tac [])
	       \\ metis_tac [])
       \\ fs [])
\\ irule SUBSET_BIGUNION
\\ rw [SUBSET_DEF]
\\ Q.EXISTS_TAC `h`
\\ Q.EXISTS_TAC `x'`
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_CARTN_PROD_INSERT = store_thm("ETREE_CARTN_PROD_INSERT",
  ``!h W1 W2. ~(h IN W1) /\ (disjoint (h INSERT W1)) /\ FINITE W1 /\ (disjoint (W2)) ==>
              BIGUNION ($⊗ (h INSERT W1) W2) = BIGUNION ($⊗ {h} W2) ∪ BIGUNION ($⊗ W1 W2)``,
rw []
\\ once_rewrite_tac[GSYM BIGUNION_UNION]
\\ rewrite_tac[SET_EQ_SUBSET]
\\ strip_tac
   >-( irule SUBSET_BIGUNION
     \\ rw [ETREE_CARTN_PROD_DEF]
     \\ rw [DISJOINT_INTER_CARTESIAN]
     \\ rw [INTER_CARTESIAN_DEF]
     \\ rewrite_tac [IN_EVENT_OUTCOME_SPACE]
     \\ asm_rewrite_tac[]
     \\ rw [SUBSET_DEF]
        >-( fs [disjoint]
	    \\ metis_tac [])
     \\ disj2_tac
     \\ Q.EXISTS_TAC `x'`
     \\ Q.EXISTS_TAC `y`
     \\ fs[] 
     \\ fs [disjoint])
\\ irule SUBSET_BIGUNION
\\ rw [ETREE_CARTN_PROD_DEF]
   >-( rw [DISJOINT_INTER_CARTESIAN]
       \\ rw [INTER_CARTESIAN_DEF]
       \\ rewrite_tac [IN_EVENT_OUTCOME_SPACE]
       \\ fs [disjoint]
       \\ rw [SUBSET_DEF]
       \\ metis_tac [])
\\ rw [DISJOINT_INTER_CARTESIAN, INTER_CARTESIAN_DEF]
\\ rewrite_tac [IN_EVENT_OUTCOME_SPACE]
\\ rw [SUBSET_DEF] 
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val NODE_EQ_BIGUNION = store_thm("NODE_EQ_BIGUNION",
  ``!LN. ETREE (NODE (EVENT_TREE_LIST LN)) = BIGUNION (set LN)``,
Induct
>-(rw [EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val BRANCH_EQ_INTER_NODE = store_thm("BRANCH_EQ_INTER_NODE",
  ``!L2 h. ETREE (BRANCH h (NODE L2)) = h INTER ETREE (NODE L2)``,
Induct
>-(rw [ETREE_DEF, EVENT_TREE_LIST_DEF])
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF]
\\ rw [pred_setTheory.UNION_OVER_INTER, pred_setTheory.INTER_ASSOC]);
(*---------------------------------------------------------------------------------------------------*)

val BRANCH_EQ_INTER_BIGUNION = store_thm("BRANCH_EQ_INTER_BIGUNION",
  ``!L2 h. ETREE (BRANCH  h (NODE (EVENT_TREE_LIST L2))) = h INTER BIGUNION (set L2)``,
rw [BRANCH_EQ_INTER_NODE, NODE_EQ_BIGUNION]);
(*---------------------------------------------------------------------------------------------------*)

val EVENT_TREE_SPLIT = store_thm("EVENT_TREE_SPLIT",
``!X Y. EVENT_TREE_LIST (X ++ Y) = EVENT_TREE_LIST X ++ EVENT_TREE_LIST Y``,

Induct
>-(rw [EVENT_TREE_LIST_DEF])
\\ rw [APPEND, EVENT_TREE_LIST_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val ETREE_NODE_SPLIT = store_thm("ETREE_NODE_SPLIT",
  ``!X Y. ETREE (NODE ( X ++ Y )) = ETREE (NODE X) UNION ETREE (NODE Y)``,
  
Induct
>-(rw [ETREE_DEF])
\\ rw [APPEND, ETREE_DEF, UNION_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val NODE_MAP_SPLIT = store_thm("NODE_MAP_SPLIT",
``!L2 X. ETREE (NODE (EVENT_TREE_LIST (MAP (λa. X ∩ a) L2))) = X INTER ETREE (NODE (EVENT_TREE_LIST L2))``, 

Induct
>-( rw [ETREE_TWO_STAIR_DEF, EVENT_OUTCOME_SPACE_CONDS_DEF, ETREE_DEF, ALL_BRANCHES_DEF, EVENT_TREE_LIST_DEF])
\\ rw [ETREE_TWO_STAIR_DEF, EVENT_OUTCOME_SPACE_CONDS_DEF, ETREE_DEF, ALL_BRANCHES_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ metis_tac [UNION_OVER_INTER]);
(*-------------------------------------------------------------------------------------------------*)

val BIGUNION_ALL_BRANCHES_EQ_BIGUNION_CARTN_PROD = store_thm("BIGUNION_ALL_BRANCHES_EQ_BIGUNION_CARTN_PROD",
``!L2 h.  disjoint {h} /\ disjoint (set L2) ==> set (ALL_BRANCHES h L2) =  $⊗ {h} (set L2)``,

Induct
>-( rw [ALL_BRANCHES_DEF, ETREE_CARTN_PROD_DEF]
    \\ rw [DISJOINT_INTER_CARTESIAN]
    \\ rw [INTER_CARTESIAN_DEF]
    \\ rewrite_tac [IN_EVENT_OUTCOME_SPACE]
    \\ asm_rewrite_tac[]
    \\ fs [])
\\ rw [ALL_BRANCHES_DEF, ETREE_CARTN_PROD_DEF, ETREE_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]
\\ sg `MAP (λa. h' ∩ a) L2 = MAP (λa. ETREE (BRANCH h' (ATOMIC a))) L2`
   >-( rw [ALL_BRANCHES_DEF, ETREE_DEF])
\\ POP_ORW
\\ rw [GSYM ALL_BRANCHES_DEF]
\\ sg `disjoint (set L2) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ sg `set (ALL_BRANCHES h' L2) = $⊗ {h'} (set L2) ` 
   >-(metis_tac [])
\\ fs []
\\ ntac 2 POP_ORW
\\ DEP_REWRITE_TAC [ETREE_CARTN_PROD_INSERT]
\\ rw [ETREE_CARTN_PROD_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]
\\ rw [INTER_CARTESIAN_DEF]
\\ rewrite_tac [IN_EVENT_OUTCOME_SPACE]
\\ fs []
\\ sg `disjoint (set L2) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)  
(*   Equivelance Between Set and List Event Tree Formalizations (Theorem 1)  *)
(*---------------------------------------------------------------------------*)

val TWO_STAIR_EQ_ETREE_CARTN_PROD = store_thm("TWO_STAIR_EQ_ETREE_CARTN_PROD",
``!L1 L2 X. ΩΝC [(X::L1); L2]  ==>
          ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 (X::L1) L2))) = BIGUNION ($⊗ (set (X::L1)) (set L2))``,

Induct
>-( rw [ETREE_TWO_STAIR_DEF, EVENT_OUTCOME_SPACE_CONDS_DEF, ETREE_DEF, ALL_BRANCHES_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM EVENT_TREE_LIST_DEF]
    \\ DEP_REWRITE_TAC [NODE_MAP_SPLIT]
    \\ DEP_REWRITE_TAC [NODE_EQ_BIGUNION]
    \\ DEP_REWRITE_TAC [BIGUNION_CARTESIAN_SINGLETON]
    \\ fs [])
\\ rw []
\\ first_x_assum (mp_tac o Q.SPECL [`L2`])
\\ rw []
\\ first_x_assum (mp_tac o Q.SPECL [`X`])
\\ rw []
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ sg `disjoint (X INSERT set L1) `
    >-( fs [disjoint]
    	\\ metis_tac [])
\\ sg `disjoint (set L2) `
    >-( fs [disjoint]
    	\\ metis_tac [])
\\ sg `ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 (X::L1) L2))) =
       BIGUNION ($⊗ (X INSERT set L1) (set L2)) `
   >-(metis_tac [])
\\ fs [ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ fs [EVENT_TREE_SPLIT, ETREE_NODE_SPLIT]
\\ fs [GSYM ETREE_TWO_STAIR_DEF]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES X L2))) ∪
       ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES h L2))) ∪
       ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2))) =
       ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES h L2))) ∪
       (ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES X L2))) ∪
        ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2))))`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ fs []
\\ ntac 2 (POP_ORW)
\\ DEP_REWRITE_TAC [NODE_EQ_BIGUNION]
\\ sg `X INSERT h INSERT set L1 = h INSERT X INSERT set L1 ` 
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ Q.ABBREV_TAC `Y = X INSERT set L1`
\\ sg ` BIGUNION ($⊗ (h INSERT Y) (set L2)) =   BIGUNION ($⊗ {h} (set L2)) ∪ BIGUNION ($⊗ Y (set L2))` 
   >-( DEP_REWRITE_TAC [ETREE_CARTN_PROD_INSERT]
       \\ Q.UNABBREV_TAC `Y`
       \\ fs [disjoint]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [BIGUNION_ALL_BRANCHES_EQ_BIGUNION_CARTN_PROD]
\\ Q.UNABBREV_TAC `Y`
\\ fs [disjoint]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val TWO_ALL_BRANCHES_SPLITS = store_thm("TWO_ALL_BRANCHES_SPLITS",
  ``!L X Y. ALL_BRANCHES X (ALL_BRANCHES Y L) = ALL_BRANCHES (X INTER Y) L``,

Induct
>-(rw [ALL_BRANCHES_DEF])
\\ rw [ALL_BRANCHES_DEF, ETREE_DEF]
   >-(rw [INTER_ASSOC])
\\ fs [ALL_BRANCHES_DEF, ETREE_DEF]); 
(*---------------------------------------------------------------------------------------------------*)

val INTER_ETREE_BRANCH_NODE = store_thm("INTER_ETREE_BRANCH_NODE",
  ``!LN X. X  ∩ ETREE (BRANCH X (NODE LN)) = ETREE (BRANCH X (NODE LN))``,

Induct
>-( rw [EVENT_TREE_LIST_DEF]
    \\ rw [ETREE_DEF])
\\ rw [ETREE_DEF, UNION_OVER_INTER]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val ETREE_NODE_ALL_BRANCHES_EQ_BRANCH_NODE = store_thm("ETREE_NODE_ALL_BRANCHES_EQ_BRANCH_NODE",
  ``!LN X Y. ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES X (ALL_BRANCHES Y LN)))) =
             X ∩ ETREE (BRANCH Y (NODE (EVENT_TREE_LIST LN)))``,

Induct
>-( rw [EVENT_TREE_LIST_DEF, ALL_BRANCHES_DEF, ETREE_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ALL_BRANCHES_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ fs [ALL_BRANCHES_DEF, ETREE_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val NODE_ALL_BRANCHES_EQ_BRANCH_NODE = store_thm("NODE_ALL_BRANCHES_EQ_BRANCH_NODE",
  ``!X Y LN L.
      X ∩ ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES Y L))) =
      ETREE (BRANCH (X ∩ Y) (NODE (EVENT_TREE_LIST L)))``,

rw [BRANCH_EQ_INTER_NODE]
\\ rw [ALL_BRANCHES_DEF, ETREE_DEF]
\\ DEP_REWRITE_TAC [NODE_MAP_SPLIT]
\\ rw [INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val ETREE_NODE_ALL_BRANCHES = store_thm("ETREE_NODE_ALL_BRANCHES",
  ``!L X. ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES X L))) =  X ∩ ETREE (NODE (EVENT_TREE_LIST L))``,
  
Induct
>-( rw [ALL_BRANCHES_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [ALL_BRANCHES_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ fs [ALL_BRANCHES_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ metis_tac [UNION_OVER_INTER, INTER_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val BRANCH_NODE_EQ_NODE_ALL_BRANCHES = store_thm("BRANCH_NODE_EQ_NODE_ALL_BRANCHES",
 ``!L X LN. ETREE (BRANCH X (NODE (EVENT_TREE_LIST L))) = ETREE (NODE (EVENT_TREE_LIST (ALL_BRANCHES X L)))``,
 
Induct
>-( rw [EVENT_TREE_LIST_DEF, ALL_BRANCHES_DEF, ETREE_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ALL_BRANCHES_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ fs [ALL_BRANCHES_DEF, ETREE_DEF]
\\ metis_tac [UNION_OVER_INTER, INTER_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val DISJOINT_N_CARTESIAN = store_thm("DISJOINT_N_CARTESIAN",
  ``!L LN. ALL_DISTINCT (LIST2_SET_LIST L) ∧ ΩΝC (LN::L) ⇒  disjoint (⊗Ν (LIST2_SET_SET L) (set LN))``,

Induct
   >-( rw [LIST2_SET_SET_DEF]
       \\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ rw [N_ETREE_CARTN_PROD_DEF]
       \\ once_rewrite_tac [pred_setTheory.ITSET_def]
       \\ rw [])
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`LN`])
\\ rw [LIST2_SET_SET_DEF]
\\ rw [GSYM LIST2_SET_SET_DEF]
\\ sg `FINITE (LIST2_SET_SET L) `
   >-( rw [LIST2_SET_SET_DEF])
\\ rw [COMMUTING_N_ETREE_CARTN_PROD_RECURSES]
\\ sg `LIST2_SET_SET L DELETE set h = LIST2_SET_SET L`
   >-(rw [ALL_DISTINCT_DELETE2])
\\ fs []
\\ sg ` EVENT_OUTCOME_SPACE_CONDS (h::L) ==> EVENT_OUTCOME_SPACE_CONDS L`
   >-( once_rewrite_tac[EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ rw [])
\\ sg `ALL_DISTINCT (LIST2_SET_LIST (h::L)) ==> ALL_DISTINCT (LIST2_SET_LIST L)`
   >-( once_rewrite_tac[LIST2_SET_LIST_DEF]
       \\ once_rewrite_tac [MAP]
       \\ once_rewrite_tac [ALL_DISTINCT]
       \\ rw [])
\\ ntac 2 (pop_assum mp_tac)
\\ rw []
\\ fs []
\\ once_rewrite_tac [ETREE_CARTN_PROD_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]);
(*---------------------------------------------------------------------------------------------------*)

val FINITE_N_CARTESIAN = store_thm("FINITE_N_CARTESIAN",
  ``!L LN. ALL_DISTINCT (LIST2_SET_LIST L) ∧ ΩΝC (LN::L) ⇒ FINITE (⊗Ν (LIST2_SET_SET L) (set LN))``,
  
rw []
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ Induct_on `L`
   >-( rw [LIST2_SET_SET_DEF]
       \\ rw [N_ETREE_CARTN_PROD_DEF]
       \\ once_rewrite_tac [pred_setTheory.ITSET_def]
       \\ rw [])
\\ rw [LIST2_SET_SET_DEF]
\\ rw [GSYM LIST2_SET_SET_DEF]
\\ sg `FINITE (LIST2_SET_SET L) `
   >-( rw [LIST2_SET_SET_DEF])
\\ rw [COMMUTING_N_ETREE_CARTN_PROD_RECURSES]
\\ sg `LIST2_SET_SET L DELETE set h = LIST2_SET_SET L`
   >-(rw [ALL_DISTINCT_DELETE2])
\\ fs []
\\ POP_ORW
\\ sg ` EVENT_OUTCOME_SPACE_CONDS (h::L) ==> EVENT_OUTCOME_SPACE_CONDS L`
   >-( once_rewrite_tac[EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ rw [])
\\ sg `ALL_DISTINCT (LIST2_SET_LIST (h::L)) ==> ALL_DISTINCT (LIST2_SET_LIST L)`
   >-( once_rewrite_tac[LIST2_SET_LIST_DEF]
       \\ once_rewrite_tac [MAP]
       \\ once_rewrite_tac [ALL_DISTINCT]
       \\ rw [])
\\ ntac 2 (pop_assum mp_tac)
\\ rw []
\\ fs []
\\ once_rewrite_tac [ETREE_CARTN_PROD_DEF]
\\ rw [DISJOINT_INTER_CARTESIAN]
\\ rw [INTER_CARTESIAN_IMAGE_CROSS]
\\ sg `FINITE (EVENT_OUTCOME_SPACE (set h))`
   >-( rw [EVENT_OUTCOME_SPACE_DEF]
       \\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF])
\\ match_mp_tac IMAGE_FINITE
\\ match_mp_tac FINITE_CROSS
\\ fs []
\\ fs [LIST2_SET_LIST_DEF]
\\ fs [GSYM LIST2_SET_LIST_DEF]
\\ rw [EVENT_OUTCOME_SPACE_DEF]
\\ sg `disjoint (N_ETREE_CARTN_PROD (LIST2_SET_SET L) (set LN))` 
   >-( DEP_REWRITE_TAC [DISJOINT_N_CARTESIAN]
       \\ rw [EVENT_OUTCOME_SPACE_CONDS_DEF])
\\ fs []);
(*---------------------------------------------------------------------------------------------------*)

val TWO_N_STAIR_EQ_CARTESIAN_N_PRODUCT = store_thm("TWO_N_STAIR_EQ_CARTESIAN_N_PRODUCT",
  ``!h LN L.
         ALL_DISTINCT h ∧ disjoint (set h) ∧ ALL_DISTINCT (LIST2_SET_LIST L) ∧ ΩΝC (LN::L) ∧
         (ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) = BIGUNION (⊗Ν (LIST2_SET_SET L) (set LN))) ⇒
         ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))) =
	 BIGUNION ($⊗ (set h) (⊗Ν (LIST2_SET_SET L) (set LN)))``,

Induct
>-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ disj1_tac
    \\ rw [ETREE_CARTN_PROD_DEF, DISJOINT_INTER_CARTESIAN, INTER_CARTESIAN_DEF, IN_EVENT_OUTCOME_SPACE])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ sg `disjoint (set h)`
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ DEP_REWRITE_TAC [NODE_EQ_BIGUNION]
\\ sg `BIGUNION ($⊗ (h' INSERT set h) (⊗Ν (LIST2_SET_SET L) (set LN))) =
       BIGUNION ($⊗ {h'} (⊗Ν (LIST2_SET_SET L) (set LN))) UNION
       BIGUNION ($⊗ (set h) (⊗Ν (LIST2_SET_SET L) (set LN))) `
   >-( DEP_REWRITE_TAC [ETREE_CARTN_PROD_INSERT]
       \\ fs []
       \\ metis_tac [DISJOINT_N_CARTESIAN])
\\ POP_ORW
\\ sg `BIGUNION (set (ALL_BRANCHES h' (⊗Ν𝑳 LN L))) = BIGUNION ($⊗ {h'} (⊗Ν (LIST2_SET_SET L) (set LN)))`
   >-( rw [ALL_BRANCHES_DEF, ETREE_DEF]
       \\ rw [GSYM NODE_EQ_BIGUNION]
       \\ DEP_REWRITE_TAC [NODE_MAP_SPLIT]
       \\ rw [NODE_EQ_BIGUNION]
       \\ DEP_REWRITE_TAC [BIGUNION_CARTESIAN_SINGLETON]
       \\ rw [FINITE_N_CARTESIAN, DISJOINT_N_CARTESIAN]
       \\ fs [disjoint]
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)  
(*   Equivelance Between Set and List Event Tree Formalizations (Theorem 2)  *)
(*---------------------------------------------------------------------------*)

val N_STAIR_EQ_N_CARTESIAN = store_thm("N_STAIR_EQ_N_CARTESIAN",
``!L LN. ALL_DISTINCT (LIST2_SET_LIST L) ∧ ΩΝC (LN::L) ⇒
         ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) = BIGUNION (⊗Ν (set (LIST2_SET_LIST L)) (set LN))``,

rw [LIST2_SET_LIST_DEF]
\\ rw [GSYM LIST2_SET_SET_DEF]
\\ fs [GSYM LIST2_SET_LIST_DEF]
\\ Induct_on `L`
>-( rw [ETREE_N_STAIR_DEF]
    \\ rw [N_ETREE_CARTN_PROD_DEF, LIST2_SET_SET_DEF]
    \\ once_rewrite_tac [pred_setTheory.ITSET_def]
    \\ rw [NODE_EQ_BIGUNION])
\\ rw []
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ rw [ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ rw [LIST2_SET_SET_DEF]
\\ rw [GSYM LIST2_SET_SET_DEF]
\\ sg `FINITE (LIST2_SET_SET L) `
   >-( rw [LIST2_SET_SET_DEF])
\\ rw [COMMUTING_N_ETREE_CARTN_PROD_RECURSES]
\\ sg `LIST2_SET_SET L DELETE set h = LIST2_SET_SET L`
   >-(rw [ALL_DISTINCT_DELETE2])
\\ fs []
\\ rw []
\\ sg `ALL_DISTINCT (LIST2_SET_LIST (h::L)) ==> ALL_DISTINCT (LIST2_SET_LIST L)`
   >-( once_rewrite_tac[LIST2_SET_LIST_DEF]
       \\ once_rewrite_tac [MAP]
       \\ once_rewrite_tac [ALL_DISTINCT]
       \\ rw [])
\\ pop_assum mp_tac
\\ rw []
\\ fs []
\\ DEP_REWRITE_TAC[TWO_N_STAIR_EQ_CARTESIAN_N_PRODUCT]
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

			(*----------------------------------------------------*)  
			(*  ET Reduction Process and ET Partitioning Process  *)
			(*----------------------------------------------------*)

(*----------------------------*)  
(*       Definitions          *)
(*----------------------------*)

val DELETE_N_DEF = Define
`DELETE_N L N = FOLDL (\b a. delN a b) L N `;

val INTER_PATH_DEF = Define
`(INTER_PATH [] = 𝕌(:α)) /\
 (INTER_PATH (h::t) = h ∩ INTER_PATH t)`;

val INDEX_LT_LEN_DEF = Define
`(INDEX_LT_LEN [] L = T) /\
 (INDEX_LT_LEN (h::t) L <=> (h < LENGTH L - LENGTH t) /\ INDEX_LT_LEN t L)`;
			     
val COMPLETE_CYLINDER_DEF  = Define
`COMPLETE_CYLINDER L N CE = LUPDATE (INTER_PATH CE) (LAST N) (DELETE_N L (TAKE ((LENGTH N)-1) N))`;

val NESTED_COMPLETE_CYLINDER_DEF  = Define
`(NESTED_COMPLETE_CYLINDER L [] []) = L /\
 (NESTED_COMPLETE_CYLINDER L (X::Ns) (XS::CEs) = NESTED_COMPLETE_CYLINDER (COMPLETE_CYLINDER L X XS) Ns CEs)`;

val PARTITIONING_DEF = Define
`PARTITIONING N L = MAP (\a. EL a L) N`;

val X_BOX =  U 0x02612;
val BOX_PART =  U 0x0229E;

val _ = Unicode.unicode_version {tmnm = "COMPLETE_CYLINDER", u = X_BOX};
val _ = Unicode.unicode_version {tmnm = "NESTED_COMPLETE_CYLINDER", u = X_BOX^N};
val _ = Unicode.unicode_version {tmnm = "PARTITIONING", u = BOX_PART};				 
(*-------------------------------------------------------------------------------------------------*)

(*--------------------------*)  
(*        Theorems          *)
(*--------------------------*)

val LENGTH_TWO_delN = store_thm("LENGTH_TWO_delN",
``!L x y. y < x ==> (LENGTH(delN y (delN x L)) = LENGTH(delN (x - 1) (delN y L))) ``,
Induct
>-(rw [delN_def])
\\ rw [delN_def]
\\ first_x_assum (mp_tac o Q.SPECL [`x - 1`])
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val TWO_delN_COMM = store_thm("TWO_delN_COMM",
``!L x y. y < x ==> (delN y (delN x L) = delN (x - 1) (delN y L)) ``,
Induct
>-(rw [delN_def])
\\ rw [delN_def]);
(*-------------------------------------------------------------------------------------------------*)

val SORTED_SNOC = store_thm("SORTED_SNOC",
``!N x. SORTED (λa b. a > b) (SNOC (x:num) N) ==> (SORTED (λa b. a > b) N)``,
Induct
>-(fs [SORTED_DEF, SNOC])
\\ rw [SORTED_DEF, SNOC]
\\ Cases_on`N`
   >-(rw [SORTED_DEF, SNOC])
\\ first_x_assum (mp_tac o Q.SPECL [`x`])
\\ rw [SORTED_DEF]
   >-(fs [SORTED_DEF, SNOC])
\\ fs [SORTED_DEF, SNOC]);
(*-------------------------------------------------------------------------------------------------*)

val DELETE_N_SNOC = store_thm("DELETE_N_SNOC",
``!N L x. (DELETE_N L (SNOC x N) = delN x (DELETE_N L N))``,
RW_TAC std_ss[delN_def,DELETE_N_DEF,FOLDL]
\\ DEP_ONCE_REWRITE_TAC [FOLDL_SNOC]);
(*-------------------------------------------------------------------------------------------------*)

val DELETE_N_LENGTH = store_thm("DELETE_N_LENGTH",
``!N L. (INDEX_LT_LEN (REVERSE N) L) ==> (LENGTH (DELETE_N L N) = LENGTH L - LENGTH N)``,
SNOC_INDUCT_TAC
>-(rw [delN_def,DELETE_N_DEF,FOLDL, REVERSE])
\\ rw [delN_def,DELETE_N_DEF,FOLDL, REVERSE]
\\ rw [FOLDL_SNOC]
\\ DEP_REWRITE_TAC [delN_shortens]
\\ rw []
   >-( fs [REVERSE_SNOC]
       \\ fs [INDEX_LT_LEN_DEF]
       \\ rw [GSYM DELETE_N_DEF])
\\ fs [REVERSE_SNOC]
\\ fs [INDEX_LT_LEN_DEF]
\\ rw [GSYM DELETE_N_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val INDEX_LT_LEN_TAKE  = store_thm("INDEX_LT_LEN_TAKE",
``! N L. INDEX_LT_LEN (REVERSE N) L ==>
             (INDEX_LT_LEN (REVERSE (TAKE (LENGTH N − 1) N)) L)``,
SNOC_INDUCT_TAC
>-(rw [INDEX_LT_LEN_DEF])
\\ fs [REVERSE_SNOC]
\\ fs [INDEX_LT_LEN_DEF]
\\ rw []
\\ sg `INDEX_LT_LEN (REVERSE (TAKE (LENGTH N − 1) N)) L `
   >-(metis_tac [])
\\ rw [TAKE_SNOC]);
(*-------------------------------------------------------------------------------------------------*)

val LENGTH_AFTER_COMPLETE_CYLINDER = store_thm("LENGTH_AFTER_COMPLETE_CYLINDER",
``!N L CE. INDEX_LT_LEN (REVERSE N) L /\ (LENGTH N >= 1) ==>
           (LENGTH (COMPLETE_CYLINDER L N CE) = LENGTH L + 1 - LENGTH N)``,

rw [COMPLETE_CYLINDER_DEF]
\\ DEP_REWRITE_TAC [DELETE_N_LENGTH]
\\ rw [INDEX_LT_LEN_TAKE]
\\ rw [SUB_SUB]);
(*-------------------------------------------------------------------------------------------------*)

val DELETE_ETREE_N_STAIR_LENGTH = store_thm("DELETE_ETREE_N_STAIR_LENGTH",
``!N LN L. (INDEX_LT_LEN (REVERSE N) (ETREE_N_STAIR LN L)) ==>
(LENGTH (DELETE_N (ETREE_N_STAIR LN L) N) =
LENGTH (ETREE_N_STAIR LN L) - LENGTH N)``,
metis_tac [DELETE_N_LENGTH]);
(*-------------------------------------------------------------------------------------------------*)

val LENGTH_ETREE_AFTER_CYLINDER = store_thm("LENGTH_ETREE_AFTER_CYLINDER",
``! N L LN CE. INDEX_LT_LEN (REVERSE N) (ETREE_N_STAIR LN L) /\
             (LENGTH N >= 1) ==>
           (LENGTH (COMPLETE_CYLINDER (ETREE_N_STAIR LN L) N CE)
	   = LENGTH (ETREE_N_STAIR LN L) + 1 - LENGTH N)``,
metis_tac [LENGTH_AFTER_COMPLETE_CYLINDER]);
(*-------------------------------------------------------------------------------------------------*)

val EL_DELETE_N_BEFORE = store_thm("EL_DELETE_N_BEFORE",
 ``!N L i. (!x. MEM x N ==> (i < x)) /\  (INDEX_LT_LEN (REVERSE N) L) /\
           (SORTED (\a b. a > b) N) ==> (EL i (DELETE_N L N) = EL i L)``,
SNOC_INDUCT_TAC
>-(rw [delN_def,DELETE_N_DEF,FOLDL, REVERSE])
\\ rw [delN_def,DELETE_N_DEF,FOLDL, REVERSE]
\\ rw [FOLDL_SNOC]
\\ fs [REVERSE_SNOC]
\\ fs [INDEX_LT_LEN_DEF]
\\ rw [GSYM DELETE_N_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`L`, `i`])
\\ rw []
\\ sg `SORTED (λa b. a > b) N `
   >-(metis_tac [SORTED_SNOC])
\\ fs []
\\ DEP_REWRITE_TAC [EL_delN_BEFORE]
\\ rw []
\\ metis_tac [DELETE_N_LENGTH]);
(*-------------------------------------------------------------------------------------------------*)

val EL_COMPLETE_CYLINDER_BEFORE = store_thm("EL_COMPLETE_CYLINDER_BEFORE",
 ``!N L i CE. (!x. MEM x N ==> (i < x)) /\  (INDEX_LT_LEN (REVERSE N) L) /\
 (LENGTH N >= 1) /\ (SORTED (\a b. a > b) N) /\ (i <> LAST N) ==>
  (EL i (COMPLETE_CYLINDER L N CE) = EL i L)``,
SNOC_INDUCT_TAC
>-(rw [COMPLETE_CYLINDER_DEF, delN_def,DELETE_N_DEF,FOLDL, REVERSE])
\\ rw [COMPLETE_CYLINDER_DEF, delN_def,DELETE_N_DEF,FOLDL, REVERSE]
\\ rw [TAKE_SNOC]
\\ rw [GSYM DELETE_N_DEF]
\\ rw [EL_LUPDATE]
\\ DEP_REWRITE_TAC [EL_DELETE_N_BEFORE]
\\ fs [REVERSE_SNOC]
\\ fs [INDEX_LT_LEN_DEF]
\\ metis_tac [SORTED_SNOC]);
(*-------------------------------------------------------------------------------------------------*)

val LENGTH_AFTER_PARTITIONING = store_thm("LENGTH_AFTER_PARTITIONING",
  ``!N L. LENGTH (PARTITIONING N L) = LENGTH N``,
Induct
>-(rw [PARTITIONING_DEF])
\\ rw [PARTITIONING_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val MEM_PARTITIONING_BEFORE = store_thm("MEM_PARTITIONING_BEFORE",
 ``!N L. (!y. MEM y N ==> (y < LENGTH L)) ==> (!x. MEM x (PARTITIONING N L) ==> MEM x L)``,
Induct
>-(rw [PARTITIONING_DEF])   
\\ rw [PARTITIONING_DEF]
   >-( DEP_REWRITE_TAC [EL_MEM]
       \\ metis_tac [])
\\ fs [GSYM PARTITIONING_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val PARTITIONING_APPEND_DISTRIB = store_thm("PARTITIONING_APPEND_DISTRIB",
 ``!N M L.  PARTITIONING (N ++ M) L = PARTITIONING N L ++ PARTITIONING M L``,
Induct
>-(rw [PARTITIONING_DEF]) 
\\ rw [PARTITIONING_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val PARTITIONING_COMM = store_thm("PARTITIONING_COMM",
 ``!N L.  PARTITIONING (REVERSE N) L = REVERSE (PARTITIONING N L)``,
SNOC_INDUCT_TAC
>-(rw [PARTITIONING_DEF])
\\ fs [REVERSE_SNOC]
\\ once_rewrite_tac [PARTITIONING_DEF]
\\ fs []
\\ POP_ORW
\\ Induct_on `N`
   >-(rw [PARTITIONING_DEF])
\\ rw [PARTITIONING_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val NESSTED_CYLINDER_ETREE_COMM = store_thm("NESSTED_CYLINDER_ETREE_COMM",
 ``!N L LN Ns CEs.
             PARTITIONING (REVERSE N)
            (NESTED_COMPLETE_CYLINDER (ETREE_N_STAIR LN L) Ns CEs)  =
	    REVERSE (PARTITIONING N
            (NESTED_COMPLETE_CYLINDER (ETREE_N_STAIR LN L) Ns CEs))``,
metis_tac [PARTITIONING_COMM]);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

			   (*---------------------------------------------*)  
			   (*       Event Tree Probabilistic Analysis     *)
			   (*---------------------------------------------*)

(*----------------------------*)  
(*        Definitions         *)
(*----------------------------*)

val PATH_DEF = Define
`(PATH p [] = p_space p) /\
 (PATH p (h::t) = h ∩ PATH p t)`;
 
val PROD_LIST_DEF =  Define
 `(PROD_LIST ([]) =  1:real) /\
  (PROD_LIST (h :: t)  =  h * (PROD_LIST t ))`;

val SUM_LIST_DEF =  Define
 `(SUM_LIST ([]) =  0:real) /\
  (SUM_LIST (h::t)  =  h + (SUM_LIST t ))`;

val PROB_LIST_DEF  = Define
` (PROB_LIST p [] = []) /\
  (PROB_LIST p (h::t) =  prob p (h)::PROB_LIST p t )`;

val PROB_SUM_LIST_DEF = Define
`(PROB_SUM_LIST p [] = []) /\
 (PROB_SUM_LIST p (h::t) = (SUM_LIST (PROB_LIST p h))::PROB_SUM_LIST p t)`;

val  MUTUAL_INDEP_DEF  = Define
`MUTUAL_INDEP p (L) =
 !L1 n. (PERM L L1 /\ (1 <=  n /\ n <=  LENGTH L) ==>
 (prob p (PATH p (TAKE n L1)) = PROD_LIST (PROB_LIST p (TAKE n L1 ))))`;

val COMPL_PSPACE_DEF = Define `COMPL_PSPACE p s = p_space p DIFF s`;

val TWO   =  U 0x1D7DA;
val DIM =  U 0x1D5D7;
val P 	  =  U 0x1D477;
val R	  =  U 0x1D479;
val O 	  =  U 0x1D476;
val B 	  =  U 0x1D469;
val A 	  =  U 0x1D468;
val D 	  =  U 0x1D46B;
val G 	  =  U 0x1D46E;
val I 	  =  U 0x1D470;
val T 	  =  U 0x1D47B;
val H 	  =  U 0x1D46F;
val S 	  =  U 0x1D47A;
val SUM   =  U 0x02211;
val PROD  =  U 0x0220F;

val _ = Unicode.unicode_version {tmnm = "SUM_LIST", u = SUM};	
val _ = Unicode.unicode_version {tmnm = "PROD_LIST", u = PROD};			 
val _ = Unicode.unicode_version {tmnm = "PROB_SUM_LIST", u = SUM^TWO^DIM^P^R^O^B};				 
(*---------------------------------------------------------------------------------------------------*)

(*------------------------*)  
(*         Theorems       *)
(*------------------------*)

val ET_PATH_EQ_PATH = store_thm("ET_PATH_EQ_PATH",
``!L p. prob_space p /\ (∀x'. MEM x' L ⇒ x' ∈ events p) ==> ET_PATH p L = PATH p L ``,

rw []
\\ Induct_on `L`
   >-( rw [PATH_DEF, ET_PATH_DEF])
\\ rw [PATH_DEF, ET_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [INTER_COMM]
\\ DEP_REWRITE_TAC [FOLDL_EQ_FOLDR]
\\ rw []
   >-( rw [ASSOC_DEF]
       \\ metis_tac [INTER_ASSOC])
   >-( rw [COMM_DEF]
       \\ metis_tac [INTER_COMM])
\\ POP_ASSUM mp_tac
\\ POP_ORW
\\ rw []
\\ Induct_on `L`
   >-( rw [PATH_DEF, ET_PATH_DEF]
       \\ metis_tac [INTER_COMM , INTER_PSPACE])
\\ rw [PATH_DEF, ET_PATH_DEF]
\\ sg ` (∀x'. x' = h ∨ MEM x' L ⇒ x' ∈ events p)`
   >-( metis_tac [])
\\ sg `FOLDR (λa b. a ∩ b) h L = h ∩ PATH p L `
   >-( metis_tac [])
\\ fs []
\\ rw []
\\ rw [INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)
                   
val PROB_PATH = store_thm("PROB_PATH",
  ``!p L. prob_space p /\ ~NULL L /\ (!x'. MEM x' L ==> x'  IN  events p ) /\
          MUTUAL_INDEP p L ==> (prob p (PATH p L) =  PROD_LIST (PROB_LIST p L))``,

RW_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[MUTUAL_INDEP_DEF] THEN
POP_ASSUM (MP_TAC o Q.SPEC `(L:'a EVENT list)`) THEN
RW_TAC std_ss[] THEN
POP_ASSUM (MP_TAC o Q.SPEC `LENGTH((L:'a EVENT list))`) THEN
RW_TAC std_ss[] THEN
FULL_SIMP_TAC std_ss[PERM_REFL] THEN
FULL_SIMP_TAC std_ss[GSYM LENGTH_NOT_NULL] THEN
(`1 <= LENGTH (L:'a EVENT list)` by (ONCE_REWRITE_TAC[ONE])) THENL[
MATCH_MP_TAC LESS_OR THEN
RW_TAC std_ss[],
FULL_SIMP_TAC std_ss[TAKE_LENGTH_ID]]);
(*---------------------------------------------------------------------------------------------------*)

val NODE_IN_EVENTS = store_thm("NODE_IN_EVENTS",
``! L p. prob_space p /\ (∀y. MEM y L ⇒ y ∈ events p)  ==> (ETREE (NODE (EVENT_TREE_LIST L)) IN events p)``,

rw []
\\ Induct_on `L`
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
    \\ rw [EVENTS_EMPTY])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ metis_tac [EVENTS_UNION]);
(*--------------------------------------------------------------------------------------------------*)

val NODE_DISJOINT = store_thm("NODE_DISJOINT",
``! L h p. prob_space p /\ (∀y. MEM y L ⇒ y ∈ events p) /\ ALL_DISTINCT (h::L) /\
           disjoint (h INSERT set L)  ==> (DISJOINT h (ETREE (NODE (EVENT_TREE_LIST L))))``,

rw [DISJOINT_DEF]
\\ Induct_on `L`
   >-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [UNION_OVER_INTER]
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ sg `h INSERT h' INSERT set L = h' INSERT h INSERT set L `
   >-( rw [INSERT_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ fs []
\\ sg `disjoint (h' INSERT h INSERT set L) `
   >-( metis_tac [])
\\ sg `disjoint (h' INSERT h INSERT set L) ==> (disjoint (h INSERT set L))`
   >-( rw [disjoint]
       >-( sg`disjoint (set L)`
  	   >-( fs [disjoint])
           \\ fs [disjoint])
       >-( sg`disjoint (set L)`
  	   >-( fs [disjoint])
           \\ fs [disjoint])
       \\ sg`disjoint (set L)`
  	  >-( fs [disjoint])
       \\ fs [disjoint])
 \\ fs []);
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------*)  
(*    Probability of NODE    *)
(*---------------------------*)

val PROB_NODE = store_thm("PROB_NODE",
``! L p. prob_space p /\ (∀y. MEM y L ⇒ y ∈ events p) /\ ΩΝC [L]  ==>
    (prob p (ETREE (NODE (EVENT_TREE_LIST L))) = ∑ (PROB_LIST p L))``,

Induct
>-(rw [EVENT_TREE_LIST_DEF, ETREE_DEF, PROB_LIST_DEF, SUM_LIST_DEF, PROB_EMPTY])
\\ rw [EVENT_OUTCOME_SPACE_CONDS_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PROB_LIST_DEF, SUM_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ sg `disjoint (set L) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ sg `ETREE (NODE (EVENT_TREE_LIST L))  IN events p`
   >-( rw [NODE_IN_EVENTS])
\\ sg `DISJOINT h (ETREE (NODE (EVENT_TREE_LIST L)))`
   >-( DEP_REWRITE_TAC [NODE_DISJOINT]
       \\ rw []
       \\ metis_tac [])
\\  sg `additive p `
   >-(rw [PROB_SPACE_ADDITIVE])
\\ sg `prob p (h ∪ ETREE (NODE (EVENT_TREE_LIST L))) = prob p h + prob p (ETREE (NODE (EVENT_TREE_LIST L))) `
   >-( metis_tac [ADDITIVE_PROB])
\\ sg `prob p (h ∪ ETREE (NODE (EVENT_TREE_LIST L))) = prob p h + prob p (ETREE (NODE (EVENT_TREE_LIST L))) `
   >-( metis_tac [ADDITIVE_PROB])
\\ POP_ORW
\\ metis_tac [EVENT_OUTCOME_SPACE_CONDS_DEF]);
(*--------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_CONS = store_thm("MUTUAL_INDEP_CONS",
  ``!L h p. MUTUAL_INDEP p (h::L) ==> MUTUAL_INDEP  p L``,
  
RW_TAC std_ss[MUTUAL_INDEP_DEF]THEN
NTAC 3(POP_ASSUM MP_TAC) THEN
POP_ASSUM (MP_TAC o Q.SPEC `(L1 ++[h]):'a EVENT list`) THEN
RW_TAC std_ss[] THEN
NTAC 3(POP_ASSUM MP_TAC) THEN
POP_ASSUM (MP_TAC o Q.SPEC `( n:num)`) THEN
RW_TAC std_ss[] THEN
(`(TAKE n ((L1 ++ [h]):'a EVENT list)) = (TAKE n (L1))` by (MATCH_MP_TAC TAKE_APPEND1)) THENL[
(`LENGTH (L1:('a  -> bool)list) = LENGTH ((L):('a  -> bool)list) ` by (MATCH_MP_TAC PERM_LENGTH) ) THENL[
         ONCE_REWRITE_TAC[PERM_SYM] THEN
         RW_TAC std_ss[],
         ONCE_ASM_REWRITE_TAC[] THEN
         RW_TAC std_ss[]
                ],
FULL_SIMP_TAC std_ss[] THEN
POP_ASSUM (K ALL_TAC) THEN
(` PERM (((h:('a  -> bool))::L):('a  -> bool)list) ((L1 ++ [h]):('a  -> bool)list) /\ n <= LENGTH ((h::L):('a  -> bool)list) ` by (RW_TAC std_ss[])) THENL[
   (` ((h::L):'a EVENT list) =  [h ]++ (L:('a  -> bool)list) ` by (RW_TAC list_ss[])) THEN  ONCE_ASM_REWRITE_TAC[] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MATCH_MP_TAC APPEND_PERM_SYM THEN
   MATCH_MP_TAC PERM_CONG THEN
   RW_TAC std_ss[PERM_REFL],
   MATCH_MP_TAC LESS_EQ_TRANS THEN
   EXISTS_TAC(``LENGTH (L:('a  -> bool)list)``) THEN
   RW_TAC list_ss[LENGTH],
FULL_SIMP_TAC std_ss[]
]]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_APPEND_SYM = store_thm("MUTUAL_INDEP_APPEND_SYM",
    ``!L1 L p.  MUTUAL_INDEP p (L1++L) ==> MUTUAL_INDEP p (L++L1)``,
    
RW_TAC std_ss[MUTUAL_INDEP_DEF]
\\  NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
\\ RW_TAC std_ss[]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `n`)
\\ RW_TAC std_ss[]
\\ FULL_SIMP_TAC std_ss[]
\\ sg`PERM ((L1 ++ L)) (L1') /\ n <= LENGTH (L1 ++ L)`
   >-( STRIP_TAC
       >-( MATCH_MP_TAC PERM_TRANS
       	   \\ Q.EXISTS_TAC `L ++ L1`
   	   \\ RW_TAC std_ss[PERM_APPEND])
       \\ FULL_SIMP_TAC list_ss[])
\\ FULL_SIMP_TAC std_ss[]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_SWAP  = store_thm("MUTUAL_INDEP_SWAP",
``!p L1 h. MUTUAL_INDEP p (h::L1) ==>  MUTUAL_INDEP  p (L1 ++ [h])``,

RW_TAC std_ss[MUTUAL_INDEP_DEF]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `(L1'):'a EVENT list`)
THEN RW_TAC std_ss[]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN (`PERM (h::L1)  ((L1'):('a  -> bool)list)` by (MATCH_MP_TAC PERM_TRANS))
   THEN1( EXISTS_TAC (``(L1 ++ [h]):'a EVENT list``)
   THEN RW_TAC std_ss[]
   THEN (`((h::L1) :('a  -> bool)list) = [h] ++ L1` by (RW_TAC list_ss[]))
   THEN ONCE_ASM_REWRITE_TAC[]
   THEN POP_ASSUM (K ALL_TAC)
   THEN RW_TAC std_ss[PERM_APPEND])
THEN FULL_SIMP_TAC std_ss[]
THEN FULL_SIMP_TAC list_ss[LENGTH]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_APPEND  = store_thm("MUTUAL_INDEP_APPEND",
``!L1 L2 Q h p. MUTUAL_INDEP p (h::L1 ++ Q::L2) ==>  MUTUAL_INDEP  p (L1 ++ Q::h::L2)``,

RW_TAC std_ss[MUTUAL_INDEP_DEF]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `(L1'):'a EVENT list`)
THEN RW_TAC std_ss[]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN (`PERM (h::L1 ++ Q::L2) ((L1'):('a  -> bool)list)` by (MATCH_MP_TAC PERM_TRANS))
   THEN1( EXISTS_TAC (``(L1 ++ Q::h::L2):'a EVENT list``)
   THEN RW_TAC std_ss[]
   THEN RW_TAC std_ss[PERM_EQUIVALENCE_ALT_DEF]
   THEN MATCH_MP_TAC EQ_SYM
   THEN RW_TAC std_ss[PERM_FUN_APPEND_CONS,APPEND,PERM_FUN_SWAP_AT_FRONT]
   THEN RW_TAC std_ss[])
THEN FULL_SIMP_TAC std_ss[]
THEN (` n <= LENGTH (h::L1 ++ Q::L2)` by (FULL_SIMP_TAC list_ss[LENGTH_APPEND]))
     THEN FULL_SIMP_TAC std_ss[]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_APPEND_APPEND_CONS  = store_thm("MUTUAL_INDEP_APPEND_APPEND_CONS",``!L1 L2 h p.
    MUTUAL_INDEP p (h::L1 ++ L2) ==>  MUTUAL_INDEP p (L1 ++ h::L2)``,
    
RW_TAC std_ss[MUTUAL_INDEP_DEF]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `(L1'):'a EVENT list`)
THEN RW_TAC std_ss[]
THEN NTAC 3(POP_ASSUM MP_TAC)
THEN POP_ASSUM (MP_TAC o Q.SPEC `n:num`)
THEN RW_TAC std_ss[]
THEN (`PERM (h::L1 ++ L2) ((L1'):('a  -> bool)list)` by (MATCH_MP_TAC PERM_TRANS))
   THEN1( EXISTS_TAC (``(L1 ++ h::L2):'a EVENT list``)
   THEN RW_TAC std_ss[]
   THEN RW_TAC std_ss[PERM_EQUIVALENCE_ALT_DEF]
   THEN MATCH_MP_TAC EQ_SYM
   THEN RW_TAC std_ss[PERM_FUN_APPEND_CONS])
THEN FULL_SIMP_TAC std_ss[]
THEN (` n <= LENGTH (h::((L1):('a  -> bool)list) ++ L2)` by (FULL_SIMP_TAC list_ss[LENGTH_APPEND]))
     THEN FULL_SIMP_TAC std_ss[]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_APPEND_SYM = store_thm("MUTUAL_INDEP_APPEND_SYM",
``!L1 L p.  MUTUAL_INDEP p (L1++L) ==> MUTUAL_INDEP p (L++L1)``,

RW_TAC std_ss[MUTUAL_INDEP_DEF]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
\\ RW_TAC std_ss[]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `n`)
\\ RW_TAC std_ss[]
\\FULL_SIMP_TAC std_ss[]
\\ (`PERM ((L1 ++ L):'a EVENT list) (L1') /\
      n <= LENGTH ((L1 ++ L):'a EVENT list)` by (STRIP_TAC))
>- (MATCH_MP_TAC PERM_TRANS
   \\ EXISTS_TAC(``( L ++ L1):'a EVENT list``)
   \\ RW_TAC std_ss[PERM_APPEND])
>- (FULL_SIMP_TAC list_ss[])
\\ FULL_SIMP_TAC std_ss[]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_APPEND1 = store_thm("MUTUAL_INDEP_APPEND1",
``!L1 L2 L p.  MUTUAL_INDEP p (L1++L2++L) ==> MUTUAL_INDEP  p (L2++L1++L)``,

RW_TAC std_ss[MUTUAL_INDEP_DEF]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `L1'`)
\\ RW_TAC std_ss[]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `n`)
\\ RW_TAC std_ss[]
\\ FULL_SIMP_TAC std_ss[]
\\ (`PERM ((L1 ++ L2 ++ L):'a EVENT list) (L1') /\
      n <= LENGTH ((L1 ++ L2 ++ L):'a EVENT list)` by STRIP_TAC)
>-(MATCH_MP_TAC PERM_TRANS
   \\ Q.EXISTS_TAC`(L2 ++ L1 ++ L):'a EVENT list`
   \\ RW_TAC std_ss[PERM_APPEND_IFF,PERM_APPEND])
>- (FULL_SIMP_TAC list_ss[])
\\ FULL_SIMP_TAC std_ss[]);
(*---------------------------------------------------------------------------------------------------*)

val MUTUAL_INDEP_FRONT_APPEND  = store_thm("MUTUAL_INDEP_FRONT_APPEND",
``!L1 L p.  MUTUAL_INDEP p (L1 ++ L) ==> MUTUAL_INDEP p L``,

RW_TAC std_ss[MUTUAL_INDEP_DEF]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\POP_ASSUM (MP_TAC o Q.SPEC `L1' ++ L1`)
\\ RW_TAC std_ss[]
\\ NTAC 3 (POP_ASSUM MP_TAC)
\\ POP_ASSUM (MP_TAC o Q.SPEC `n`)
\\ RW_TAC std_ss[]
\\ FULL_SIMP_TAC std_ss[]
\\ (`PERM ((L1 ++ L):'a EVENT list) (L1' ++ L1) /\ n <= LENGTH (L1 ++ L)` by (STRIP_TAC))
>- (MATCH_MP_TAC APPEND_PERM_SYM
   \\ RW_TAC list_ss[PERM_APPEND_IFF])
>- (MATCH_MP_TAC LESS_EQ_TRANS
   \\ EXISTS_TAC (``LENGTH (L:'a EVENT list)``)
   \\ RW_TAC list_ss[])
\\ FULL_SIMP_TAC std_ss[]
\\ (`(TAKE n (L1' ++ L1)) = TAKE n (L1':('a ->bool) list) `by (ALL_TAC))
>- ( MATCH_MP_TAC TAKE_APPEND1
   \\ (`LENGTH L = LENGTH (L1': 'a EVENT list)  ` by (MATCH_MP_TAC PERM_LENGTH))
   >> (RW_TAC std_ss[])
   \\ FULL_SIMP_TAC std_ss[])
\\ FULL_SIMP_TAC std_ss[]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_BRANCH_IN_EVENTS = store_thm("ETREE_BRANCH_IN_EVENTS",
  ``!X L p. (∀x'. (x' = X) ∨ MEM x' L ⇒ x' ∈ events p) /\ prob_space p
            ==> (ETREE (BRANCH X (NODE (EVENT_TREE_LIST L))) ∈ events p)``,
      
rw []
\\ Induct_on `L`
   >-( rw []
       \\ rw [EVENT_TREE_LIST_DEF]
       \\ rw [ETREE_DEF]
       \\ rw [EVENTS_EMPTY])
\\ rw []       
\\ sg ` (∀x'. (x' = X)  ∨ (x' = h) ∨ MEM x' L ⇒ x' ∈ events p) ==>
       	 (∀x'. (x' = X) ∨ MEM x' L ⇒ x' ∈ events p)`
   >-( rw []
       \\metis_tac [])
\\ sg `(∀x'. (x' = X) ∨ MEM x' L ⇒ x' ∈ events p) `
   >-( metis_tac [])       
\\ qpat_x_assum `(∀x'. (x' = X) ∨ MEM x' L ⇒ x' ∈ events p) ⇒
         ETREE (BRANCH X (NODE (EVENT_TREE_LIST L))) ∈ events p ` mp_tac
\\ ASM_REWRITE_TAC []
\\ rw []
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF]
\\ rw [UNION_OVER_INTER]
\\ fs [ETREE_DEF]
\\ metis_tac [EVENTS_INTER, EVENTS_UNION]);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_ETREE_BRANCH = store_thm("DISJOINT_ETREE_BRANCH",
  ``!h L X. disjoint (h  INSERT set L) /\ ¬MEM h L 
    ==> (DISJOINT (X ∩ h) (X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L)))))``,
    
rw [DISJOINT_DEF]
\\ rw [INTER_ASSOC]
\\ Induct_on `L`
   >-( rw []
       \\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw []       
\\ fs []
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
   >-( sg `h INTER h' = {} `
       >-(fs [disjoint])
       \\ sg `X ∩ h ∩ X ∩ X ∩ h' = X ∩ (h ∩ h') `
       	  >-( rw [EXTENSION]
              \\ EQ_TAC
              	 >-(metis_tac [])
              \\ metis_tac [])
       \\ fs [])
\\ sg `disjoint (h INSERT h' INSERT set L) ==> (disjoint (h INSERT set L))`
   >-( fs  [disjoint]
       \\ metis_tac [])
\\ fs []
\\ sg `X ∩ h ∩ X ∩ X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L))) =
       X ∩ h ∩ X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L))) `
   >-( rw [EXTENSION]
       \\ EQ_TAC
          >-(metis_tac [])
       \\ metis_tac [])
\\ fs [ETREE_DEF, INTER_ASSOC]);
(*---------------------------------------------------------------------------------------------------*)

val BIGUNION_IN_EVENTS = store_thm("BIGUNION_IN_EVENTS",
  ``!L p. (!y. MEM y L ==> y IN events p) /\ (prob_space p)  ==> (BIGUNION (set L) IN events p) ``,
  
Induct
>-( rw []
    \\ rw [EVENTS_EMPTY])
\\ rw []
\\ metis_tac [EVENTS_UNION]);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_BIGUNION = store_thm("DISJOINT_BIGUNION",
  ``!h L.  ¬MEM h L /\ ALL_DISTINCT L /\
           disjoint (h INSERT set L)  ==> (DISJOINT h (BIGUNION (set L)))``,
	   
rw []
\\ fs [disjoint]
\\ rw [DISJOINT_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`h`,`s'`])
\\ rw []
\\ sg `h <> s' `
   >-( Induct_on `L`
       >-(rw [])
       \\ metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_TWO_STAIR_IN_EVENTS = store_thm("ETREE_TWO_STAIR_IN_EVENTS",
  ``!L1 L2 p. prob_space p /\ (∀x. MEM x L1 ⇒ x ∈ events p) /\ (∀y. MEM y L2 ⇒ y ∈ events p)
    ==>  (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2))) IN events p) ``,
    
Induct
   >-( rw [ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, EVENTS_EMPTY])
\\ rw [ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ first_x_assum (mp_tac o Q.SPECL [`L2`,`p`])
\\ rw [ETREE_NODE_ALL_BRANCHES]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ metis_tac [NODE_IN_EVENTS, EVENTS_INTER, EVENTS_UNION]);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_ETREE_TWO_STAIR = store_thm("DISJOINT_ETREE_TWO_STAIR",
  ``!L1 h L2. (disjoint (h INSERT set L1)) /\ (disjoint (set L2)) /\ (¬MEM h L1) ==>
 (DISJOINT (h ∩ BIGUNION (set L2)) (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2)))))``,

Induct
   >-( rw [DISJOINT_DEF, ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [DISJOINT_DEF, ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`h'`,`L2`])
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ sg `disjoint (h  INSERT set L1)`
   >-( fs [disjoint]
       \\ metis_tac [])       
\\ fs []
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ rw [NODE_EQ_BIGUNION]
   >-( sg `h' ∩ BIGUNION (set L2) ∩ h ∩ BIGUNION (set L2)  = (h ∩ h') ∩ BIGUNION (set L2)`
       >-( rw [EXTENSION]
       	   \\ metis_tac [])
       \\ POP_ORW
       \\ fs [disjoint]
       \\ metis_tac [])
\\ sg ` disjoint (h' INSERT set L1)`
  >-( fs [disjoint]
       \\ metis_tac [])
\\ sg `DISJOINT (h' ∩ BIGUNION (set L2)) (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2)))) `
   >-(metis_tac [])
\\ metis_tac [DISJOINT_DEF, NODE_EQ_BIGUNION]);
(*---------------------------------------------------------------------------------------------------*)

(*---------------------------*)  
(*   Probability of BRANCH   *)
(*---------------------------*)

val PROB_BRANCH = store_thm("PROB_BRANCH",
  ``!L2 p X.
            (prob_space p) /\ ΩΝC [L2] /\
	    (!x'. MEM x' (X::L2) ==> x' IN events p)  /\ (MUTUAL_INDEP p (X::L2)) ==>
    (prob p (ETREE (BRANCH  X (NODE (EVENT_TREE_LIST L2)))) = prob p X * ∑ (PROB_LIST p L2))``,
    
Induct
   >-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, SUM_LIST_DEF, PROB_LIST_DEF, PROB_EMPTY])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, SUM_LIST_DEF, PROB_LIST_DEF, PROB_EMPTY]
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [REAL_ADD_LDISTRIB, UNION_OVER_INTER]
\\ first_x_assum (mp_tac o Q.SPECL [`p`,`X`])
\\ rw []
\\ sg `disjoint (set L2) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ sg `(∀x'. x' = X ∨ MEM x' L2 ⇒ x' ∈ events p) `
   >-(metis_tac [])
\\ sg` MUTUAL_INDEP p (X::L2)`
   >-( once_rewrite_tac[(prove(``!a b c. a::c = [a]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ sg `prob p (ETREE (BRANCH X (NODE (EVENT_TREE_LIST L2)))) = prob p X * SUM_LIST (PROB_LIST p L2) ` 
   >-( metis_tac [])
\\ sg `X ∩ h IN events p `
   >-(metis_tac [EVENTS_INTER])
\\ sg `(ETREE (BRANCH X (NODE (EVENT_TREE_LIST L2)))) IN events p`
    >-( metis_tac [ETREE_BRANCH_IN_EVENTS])
\\ sg `X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L2))) IN events p `
   >-(metis_tac [EVENTS_INTER])
\\ sg `DISJOINT (X ∩ h) (X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L2))))`
   >-(metis_tac [DISJOINT_ETREE_BRANCH])
\\ sg ` prob p (X ∩ h ∪ X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L2)))) =
        prob p (X ∩ h) + prob p (X ∩ ETREE (BRANCH X (NODE (EVENT_TREE_LIST L2)))) `
   >-( sg `additive p `
       >-(rw [PROB_SPACE_ADDITIVE])
       \\ metis_tac [ADDITIVE_PROB])
\\ fs [ETREE_DEF]
\\ sg `X ∩ (X ∩ ETREE (NODE (EVENT_TREE_LIST L2))) =  X ∩ ETREE (NODE (EVENT_TREE_LIST L2))` 
   >-( rw [EXTENSION]
       \\ metis_tac []) 
\\ fs []
\\ sg `MUTUAL_INDEP p [X; h]`
   >-( irule MUTUAL_INDEP_FRONT_APPEND 
       \\ Q.EXISTS_TAC `L2`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
 \\ sg `X ∩ h = PATH p [X; h] `
    >-( rw [PATH_DEF]
       	\\ rw [INTER_ASSOC]
	\\ sg `X ∩ h IN events p `
	   >-(metis_tac[EVENTS_INTER])
        \\ sg `X ∩ h ∩ p_space p = p_space p ∩ X ∩ h `
	   >-( rw [EXTENSION]
	       \\ EQ_TAC
	          >-(metis_tac [])
	       \\ metis_tac [])
        \\ fs []
	\\ metis_tac [INTER_PSPACE])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
   >-(metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

(*------------------------------*)  
(*   Probability of TWO STAIR   *)
(*------------------------------*)

val PROB_ETREE_TWO_STAIR = store_thm("PROB_ETREE_TWO_STAIR",
  ``!L1 L2 p. (prob_space p) /\ ΩΝC [L1; L2] /\ (!y. MEM y (FLAT [L1;L2]) ==> y IN events p)  /\
	      (MUTUAL_INDEP p (FLAT [L1; L2])) ==>
	      prob p (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2)))) =  ∏ (∑𝟚𝗗𝑷𝑹𝑶𝑩 p [L1; L2])``,

Induct
   >-(rw [ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PROB_SUM_LIST_DEF,
          SUM_LIST_DEF, PROD_LIST_DEF, PROB_LIST_DEF, PROB_EMPTY])
\\ rw [ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PROB_SUM_LIST_DEF,
       EVENT_OUTCOME_SPACE_CONDS_DEF, SUM_LIST_DEF, PROD_LIST_DEF, PROB_LIST_DEF, PROB_EMPTY]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ sg `ETREE (NODE (EVENT_TREE_LIST L2)) = BIGUNION (set L2)  `
   >-(metis_tac [NODE_EQ_BIGUNION])
\\ POP_ORW
\\ sg `BIGUNION (set L2) IN events p `
   >-( DEP_REWRITE_TAC [BIGUNION_IN_EVENTS]
       \\ metis_tac [])
\\ sg `h ∩ BIGUNION (set L2) IN events p `
    >-(metis_tac [EVENTS_INTER])
\\ sg `ETREE (NODE (EVENT_TREE_LIST (ETREE_TWO_STAIR L1 L2))) IN events p `
   >-( metis_tac [ETREE_TWO_STAIR_IN_EVENTS])
\\ sg ` DISJOINT (h ∩ BIGUNION (set L2))
       	       	 (ETREE (NODE (EVENT_TREE_LIST (ETREE_TWO_STAIR L1 L2)))) `
   >-(metis_tac [DISJOINT_ETREE_TWO_STAIR])
\\ sg `additive p `
   >-(rw [PROB_SPACE_ADDITIVE])
\\ sg ` prob p (h ∩ BIGUNION (set L2) ∪ ETREE (NODE (EVENT_TREE_LIST (ETREE_TWO_STAIR L1 L2))))
        = prob p (h ∩ BIGUNION (set L2)) +
	  prob p (ETREE (NODE (EVENT_TREE_LIST (ETREE_TWO_STAIR L1 L2))))`
   >-(metis_tac [ADDITIVE_PROB])
\\ fs []
\\ sg `h ∩ BIGUNION (set L2) = ETREE (BRANCH h (NODE (EVENT_TREE_LIST L2)))`
   >-( metis_tac [GSYM BRANCH_EQ_INTER_BIGUNION])
\\ fs []
\\ DEP_REWRITE_TAC [PROB_BRANCH]
\\ rw [EVENT_OUTCOME_SPACE_CONDS_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ fs [])
\\ first_x_assum (mp_tac o Q.SPECL [`L2`,`p`])
\\ rw []
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ sg`disjoint (set L1)`
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ sg `MUTUAL_INDEP p (L1 ⧺ L2)`
   >-(  irule MUTUAL_INDEP_FRONT_APPEND 
   	\\ Q.EXISTS_TAC `[h]`
    	\\ rw[])
\\ fs []
\\ sg `(∀y. MEM y L1 ∨ MEM y L2 ⇒ y ∈ events p)`
   >-(metis_tac [])
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 L1 L2)))) = ∏ (PROB_SUM_LIST p [L1; L2]) `
   >-(metis_tac [])
\\ POP_ORW
\\ rw [PROB_SUM_LIST_DEF, PROB_LIST_DEF, SUM_LIST_DEF, PROD_LIST_DEF]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

val PATH_IN_EVENTS = store_thm("PATH_IN_EVENTS",
  ``!L p. (!x. MEM x L ==> x IN events p) /\ prob_space p ==> (PATH p L IN events p)``,
RW_TAC std_ss []
\\ Induct_on `L`
   >-( RW_TAC std_ss [MEM, PATH_DEF, EVENTS_SPACE])
\\ RW_TAC std_ss [MEM, PATH_DEF]
\\ MATCH_MP_TAC EVENTS_INTER
\\ RW_TAC std_ss []);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_BRANCH_MULTIPLE_EVENTS = store_thm("ETREE_BRANCH_MULTIPLE_EVENTS",
  ``!LN p X. prob_space p /\ (∀x'. MEM x' (FLAT [X;LN]) ⇒ x' ∈ events p) /\
    	       ΩΝC [LN] /\ (MUTUAL_INDEP p (FLAT [X;LN])) ==>
      	      (prob p (ETREE (BRANCH (PATH p X) (NODE (EVENT_TREE_LIST LN)))) =
      	       ∏ (PROB_LIST p X) *  ∑ (PROB_LIST p LN))``,

Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, PROB_EMPTY, SUM_LIST_DEF, PROB_LIST_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, PROB_EMPTY, SUM_LIST_DEF, PROB_LIST_DEF]
\\ rw [GSYM  EVENT_TREE_LIST_DEF]
\\ rw [UNION_OVER_INTER, REAL_ADD_LDISTRIB]
\\ sg `PATH p X ∩ h  ∈ events p`
   >-( Induct_on `X`
       >-( rw []
       	   \\ rw [PATH_DEF]
	   \\ metis_tac [EVENTS_SPACE, EVENTS_INTER])
       \\ rw []
       \\ rw [PATH_DEF]
       \\ fs []
       \\ sg `(∀x'. MEM x' X ∨ (x' = h) ∨ MEM x' LN ⇒ x' ∈ events p) `
       	  >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (X ⧺ h::LN) `
       	  >-( irule MUTUAL_INDEP_FRONT_APPEND
	      \\ Q.EXISTS_TAC `[h']`
	      \\ rw [])
       \\ qpat_x_assum `(∀x'. MEM x' X ∨ (x' = h) ∨ MEM x' LN ⇒ x' ∈ events p) ⇒
          	       MUTUAL_INDEP p (X ⧺ h::LN) ⇒
         	       PATH p X ∩ h ∈ events p` mp_tac
       \\ ASM_REWRITE_TAC []
       \\ rw []
       \\ sg `h' ∩ PATH p X ∩ h  = h' ∩ (PATH p X ∩ h)`
       	  >-( metis_tac [INTER_ASSOC])
       \\ fs []
       \\ metis_tac [EVENTS_INTER])
\\ sg `PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST LN)) ∈ events p `     
   >-( metis_tac [ETREE_BRANCH_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
\\ sg `DISJOINT (PATH p X ∩ h)
      		(PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST LN)))`
   >-( rw [DISJOINT_DEF]
       \\ ntac 3 (POP_ORW) 
       \\ ntac 3 (pop_assum (mp_tac))
       \\ POP_ORW
       \\ rw []
       \\ Induct_on `LN`
       	  >-(rw [EVENT_TREE_LIST_DEF, ETREE_DEF])
       \\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ rw [INTER_ASSOC]
       \\ rw [UNION_OVER_INTER]
       	  >-( sg `PATH p X ∩ h ∩ PATH p X  ∩ h' =  (h ∩ h') ∩
	          PATH p X`
	          >-( rw [EXTENSION]
		      \\ EQ_TAC
		      	 >-(metis_tac [])
		      \\ metis_tac [])
	      \\ POP_ORW
	      \\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
	      \\ sg `h ∩ h' =  {} `
		 >-( fs [disjoint]
		     \\ metis_tac [])
	      \\ fs [])
      \\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
      \\ sg`disjoint (h INSERT set LN) `
      	 >-( fs [disjoint]
	     \\ metis_tac [])
      \\ fs []
      \\ sg `(∀x'. MEM x' X ∨ x' = h ∨ MEM x' LN ⇒ x' ∈ events p) `
         >-( metis_tac [])
      \\ metis_tac [INTER_ASSOC])
\\ sg `additive p `
   >-(rw [PROB_SPACE_ADDITIVE])
\\ sg `prob p (PATH p X ∩ h ∪ PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST LN))) =
      prob p (PATH p X ∩ h) + prob p (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST LN)))`
   >-(metis_tac [ADDITIVE_PROB])
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`p`,`X`])
\\ rw []
\\ sg `disjoint (set LN)`
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ sg ` MUTUAL_INDEP p (X ⧺ LN)`
   >-( irule MUTUAL_INDEP_FRONT_APPEND
    \\ Q.EXISTS_TAC `[h]`
    \\ once_rewrite_tac[APPEND_ASSOC]
    \\ irule MUTUAL_INDEP_APPEND1
    \\ once_rewrite_tac[GSYM APPEND_ASSOC]
    \\ rewrite_tac[GSYM CONS_APPEND]
    \\ rw [])
\\ fs []
\\ sg ` (∀x'. MEM x' X ∨ MEM x' LN ⇒ x' ∈ events p) `
   >-(metis_tac [])
\\ fs [ETREE_DEF]
\\ sg `prob p (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST LN))) =
        ∏ (PROB_LIST p X) * SUM_LIST (PROB_LIST p LN) `
   >-(metis_tac [])
\\ POP_ORW
\\ sg `PATH p X ∩ h = PATH p (h::X)`
   >-( rw [PATH_DEF]
       \\ rw [INTER_COMM])
\\ fs []      
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(  once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       	\\ irule MUTUAL_INDEP_APPEND_SYM
	\\ irule MUTUAL_INDEP_FRONT_APPEND
       	\\ Q.EXISTS_TAC `LN`
	\\ irule MUTUAL_INDEP_APPEND_SYM
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
   	\\ rewrite_tac[GSYM CONS_APPEND]
    	\\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

val BRANCH_N_STAIR_EQ_INTER_NODE = store_thm("BRANCH_N_STAIR_EQ_INTER_NODE",
  ``!L h LN. ETREE (BRANCH h (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) =
             h ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))``,

Induct
   >-( rw [ETREE_N_STAIR_DEF, BRANCH_EQ_INTER_NODE])
\\ rw [ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF])    
\\ metis_tac [ETREE_TWO_STAIR_DEF, ETREE_DEF, UNION_OVER_INTER]);
(*---------------------------------------------------------------------------------------------------*)

val BRANCH_PATH_TWO_STAIR_N_STAIR = store_thm("BRANCH_PATH_TWO_STAIR_N_STAIR",
  ``!h LN L X p. ETREE (BRANCH (PATH p X) (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))) =
                 PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))``, 

Induct
>-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, UNION_OVER_INTER, INTER_ASSOC]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_NODE_N_STAIR_IN_EVENTS = store_thm("ETREE_NODE_N_STAIR_IN_EVENTS",
  ``!L LN p. (∀x'. MEM x' LN ∨ MEM x' (FLAT L) ⇒ x' ∈ events p) /\ prob_space p  ==>
      	     ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∈ events p``,
	   
Induct
   >-( rw [ETREE_N_STAIR_DEF, NODE_EQ_BIGUNION]
       \\ metis_tac [BIGUNION_IN_EVENTS])
\\ rw [ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENTS_EMPTY, EVENT_TREE_LIST_DEF])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`LN`,`p`])
\\ rw []
\\ sg `ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))) ∈ events p`
   >-(metis_tac [])
\\ sg ` ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∈ events p `
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ metis_tac [EVENTS_UNION, EVENTS_INTER]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_BRANCH_N_STAIR_IN_EVENTS = store_thm("ETREE_BRANCH_N_STAIR_IN_EVENTS",
  ``!L LN p h. (∀x'. MEM x' LN ∨ (x' = h)  ∨ MEM x' (FLAT L) ⇒ x' ∈ events p) /\ prob_space p  ==>
      	       ETREE (BRANCH h (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) ∈ events p``,

Induct
   >-( rw [ETREE_N_STAIR_DEF]
       \\ metis_tac [ETREE_BRANCH_IN_EVENTS])
\\ rw [ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, EVENTS_EMPTY])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ rw [BRANCH_N_STAIR_EQ_INTER_NODE]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ sg `(∀x'. MEM x' LN ∨ x' = h' ∨ MEM x' h ∨ MEM x' (FLAT L) ⇒ x' ∈ events p)`
   >-(metis_tac [])
\\ sg `ETREE (BRANCH h' (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))) ∈ events p `
   >-(metis_tac [])   
\\ fs [ETREE_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`LN`,`p`, `h''`])
\\ rw []
\\ sg `(∀x'. MEM x' LN ∨ x' = h'' ∨ MEM x' (FLAT L) ⇒ x' ∈ events p)` 
   >-(metis_tac [])
\\ sg `h'' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∈ events p `
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ metis_tac [INTER_ASSOC, EVENTS_INTER, EVENTS_UNION]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_NODE_TWO_STAIR_N_STAIR_IN_EVENTS = store_thm("ETREE_NODE_TWO_STAIR_N_STAIR_IN_EVENTS",
  ``!h LN L p. (∀x'. MEM x' LN ∨ MEM x' h ∨ MEM x' (FLAT L) ⇒ x' ∈ events p) /\ prob_space p ==>
               ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))) ∈ events p``, 

Induct
   >-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, EVENTS_EMPTY])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`LN`,`L`, `p`])
\\ rw []
\\ sg `(∀x'. MEM x' LN ∨ MEM x' h ∨ MEM x' (FLAT L) ⇒ x' ∈ events p) ` 
   >-(metis_tac [])
\\ sg `ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))) ∈ events p `
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ metis_tac [EVENTS_UNION, EVENTS_INTER, ETREE_BRANCH_N_STAIR_IN_EVENTS, ETREE_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_ETREE_N_STAIR = store_thm("DISJOINT_ETREE_N_STAIR",
  ``!h h' LN L. disjoint (h' INSERT set h) ∧ disjoint (set LN) ∧ ~MEM h' h ∧ ΩΝC L ⇒
                DISJOINT (h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))))
                         (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))))``,

Induct
   >-( rw [DISJOINT_DEF, EVENT_TREE_LIST_DEF, ETREE_TWO_STAIR_DEF, ETREE_DEF])
\\ rw [DISJOINT_DEF, EVENT_TREE_LIST_DEF, ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ first_x_assum (mp_tac o Q.SPECL [`h''`,`LN`,`L`])
\\ rw []
\\ sg `disjoint (h''  INSERT set h)`
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs [DISJOINT_DEF]
   >-( sg  `h'' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∩ h' ∩
       	           ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) =
	    (h'' ∩ h') ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) `
        >-( rw [EXTENSION]
            \\ EQ_TAC
       	       >-(metis_tac [])
            \\ metis_tac [])
       \\ fs []
       \\ fs [disjoint]
       \\ metis_tac [])
\\ sg  `h'' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∩ h' ∩
       	       ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) =
	(h'' ∩ h') ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) `
  >-( rw [EXTENSION]
      \\ EQ_TAC
       	 >-(metis_tac [])
      \\ metis_tac [])
\\ fs []
\\ fs [disjoint]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val DISJOINT_PATH_N_STAIR  = store_thm("DISJOINT_PATH_N_STAIR",
``!h h' LN L p X.
            disjoint (h' INSERT set h) ∧ disjoint (set LN) ∧ ~MEM h' h ∧ ΩΝC L ⇒
            DISJOINT
	      (PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))))
              (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))))``,

Induct
   >-( rw [DISJOINT_DEF, ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [DISJOINT_DEF, ETREE_TWO_STAIR_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
   >-( rw [INTER_ASSOC]
       \\ sg ` h' ∩ h'' = {}`
       	  >-( fs [disjoint]
       	      \\ metis_tac [])   
       \\ sg `PATH p X ∩ h'' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∩
              PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) =
	      (h' ∩ h'') ∩ PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))`
          >-( rw [EXTENSION]
       	      \\ EQ_TAC
       	      	 >-(metis_tac [])
              \\ metis_tac [])
       \\ fs [])
\\ first_x_assum (mp_tac o Q.SPECL [`h''`,`LN`,`L`, `p`, `X`])
\\ rw []
\\ sg `disjoint (h''  INSERT set h)`
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs [DISJOINT_DEF]
\\ metis_tac [INTER_IDEMPOT, INTER_ASSOC]);
(*---------------------------------------------------------------------------------------------------*)

val ETREE_BRANCH_MULTIPLE_EVENTS_N_STAIR = store_thm("ETREE_BRANCH_MULTIPLE_EVENTS_N_STAIR",
   ``!L X LN p h.
            prob_space p ∧ (∀x'. MEM x' (FLAT (X::LN::L)) ⇒ x' ∈ events p) ∧
            ΩΝC (LN::L) ∧ MUTUAL_INDEP p (FLAT (X::LN::L)) ⇒
            prob p (ETREE (BRANCH (PATH p X) (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))))) =
            ∏ (PROB_LIST p X) * ∑ (PROB_LIST p LN) * ∏ (∑𝟚𝗗𝑷𝑹𝑶𝑩 p L)``,

Induct
   >-( rw [ETREE_N_STAIR_DEF, PROB_SUM_LIST_DEF, PROD_LIST_DEF]
       \\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ DEP_REWRITE_TAC [ETREE_BRANCH_MULTIPLE_EVENTS]
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF])	      
\\ rw [PROB_SUM_LIST_DEF, PROD_LIST_DEF, REAL_MUL_ASSOC, ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, PROB_LIST_DEF,
          SUM_LIST_DEF,  PROB_EMPTY])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF]
\\ DEP_REWRITE_TAC [BRANCH_N_STAIR_EQ_INTER_NODE]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ rw [PROB_LIST_DEF, SUM_LIST_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ fs [ETREE_DEF]
\\ sg `prob p (PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∪
               PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))) =
       prob p (PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) +
       prob p (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))))`	       	      
   >-( sg`PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∈ events p`
       >-(metis_tac [PATH_IN_EVENTS, EVENTS_INTER, ETREE_NODE_N_STAIR_IN_EVENTS])
       \\ sg `PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))  ∈ events p`
          >-(metis_tac [PATH_IN_EVENTS, EVENTS_INTER, ETREE_NODE_TWO_STAIR_N_STAIR_IN_EVENTS])
       \\ sg `DISJOINT (PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))))
                      (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))))`
	 >-( DEP_REWRITE_TAC [DISJOINT_PATH_N_STAIR]
	     \\ fs[disjoint]
	     \\ metis_tac [])
       \\ sg `additive p `
          >-(rw [PROB_SPACE_ADDITIVE])
       \\ metis_tac [ADDITIVE_PROB])
\\ POP_ORW
\\ sg `prob p (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))) =
        ∏ (PROB_LIST p X) * SUM_LIST (PROB_LIST p LN) *
        SUM_LIST (PROB_LIST p h) * ∏ (PROB_SUM_LIST p L)`
   >-( sg `MUTUAL_INDEP p (X ⧺ LN ⧺ h ⧺ FLAT L)`
       	  >-( Q.ABBREV_TAC `x = X ⧺ LN `
       	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       	      \\ Q.ABBREV_TAC `y =  h ⧺ FLAT L`
       	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `[h']`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ Q.UNABBREV_TAC `x`
       	      \\ Q.UNABBREV_TAC `y`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ sg `X ⧺ LN ⧺ [h'] ⧺ h ⧺ FLAT L =
       	             X ⧺ LN ⧺ h'::h ⧺ FLAT L`
	         >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++b``,rw[]))]	      
	      	     \\ rw [])
	       \\ metis_tac [])
       \\ sg `disjoint (set h)`
          >-( fs [disjoint]
       	      \\ metis_tac [])
       \\ sg `(∀x'.
             ((MEM x' X ∨ MEM x' LN) ∨ MEM x' h) ∨ MEM x' (FLAT L) ⇒
             x' ∈ events p) `
          >-(metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) =
               ∏ (PROB_LIST p X) * prob p h' * SUM_LIST (PROB_LIST p LN) * ∏ (PROB_SUM_LIST p L)`
   >-( sg `PATH p X ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) =
           PATH p (h'::X) ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))`
       >-( rw [PATH_DEF]
       	   \\ rw [EXTENSION]
	   \\ metis_tac [])
       \\ POP_ORW
       \\ first_x_assum (mp_tac o Q.SPECL [`h'::X`, `LN`, `p`])
       \\ rw []
       \\ sg `(∀x'. (((x' = h') ∨ MEM x' X) ∨ MEM x' LN) ∨ MEM x' (FLAT L) ⇒  x' ∈ events p)`
       	  >-(metis_tac [])
       \\ sg` MUTUAL_INDEP p (h'::(X ⧺ LN ⧺ FLAT L))`
       	  >-(  once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ Q.ABBREV_TAC `x = X ⧺ LN ⧺ [h'] `
	       \\ irule MUTUAL_INDEP_FRONT_APPEND
     	       \\ Q.EXISTS_TAC `h`
	       \\ once_rewrite_tac[APPEND_ASSOC]
               \\ irule MUTUAL_INDEP_APPEND1
	       \\ Q.UNABBREV_TAC `x`
	       \\ sg `X ⧺ LN ⧺ [h'] ⧺ h ⧺ FLAT L =
	               X ⧺ LN ⧺ h'::h ⧺ FLAT L`
	          >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++b``,rw[]))]
	              \\ rw [])
	        \\ metis_tac [])
       \\ fs []
       \\ sg `prob p (PATH p (h'::X) ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) =
              ∏ (PROB_LIST p (h'::X)) * SUM_LIST (PROB_LIST p LN) * ∏ (PROB_SUM_LIST p L) `
	  >-(metis_tac [])
       \\ POP_ORW
       \\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
       \\ disj2_tac
       \\ disj2_tac
       \\ REAL_ARITH_TAC)     
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*-----------------------------------------*)  
(*   Probability of Event Tree N Stair     *)
(*-----------------------------------------*)

val PROB_ETREE_N_STAIR = store_thm("PROB_ETREE_N_STAIR",
  ``!L p LN. prob_space p ∧ ΩΝC (LN::L) ∧ (∀x'. MEM x' (FLAT (LN::L)) ⇒ x' ∈ events p) ∧
             MUTUAL_INDEP p (FLAT (LN::L)) ⇒
             prob p (ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) = ∏ (∑𝟚𝗗𝑷𝑹𝑶𝑩  p (LN::L))``,

Induct
   >-( rw [ETREE_N_STAIR_DEF, PROB_SUM_LIST_DEF, PROD_LIST_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ DEP_REWRITE_TAC [PROB_NODE]
       \\ metis_tac [])
\\ rw [ETREE_N_STAIR_DEF, PROB_SUM_LIST_DEF, PROD_LIST_DEF, EVENT_TREE_LIST_DEF, PROB_SUM_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ fs [EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`p`,`LN`])
\\ rw []
\\ sg `∀x'. MEM x' LN ∨ MEM x' (FLAT L) ⇒ x' ∈ events p`
   >-(metis_tac [])
\\ sg `MUTUAL_INDEP p (LN ⧺ FLAT L)`
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ fs [])
\\ fs []
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) =
        ∏ (PROB_SUM_LIST p (LN::L)) `
   >-(metis_tac [])
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, PROB_EMPTY, SUM_LIST_DEF, PROB_LIST_DEF])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, PROB_EMPTY, SUM_LIST_DEF, PROB_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ rw [GSYM ETREE_TWO_STAIR_DEF]
\\ DEP_REWRITE_TAC [EVENT_TREE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_SPLIT]
\\ DEP_REWRITE_TAC [ETREE_NODE_ALL_BRANCHES]
\\ sg `additive p `
   >-(rw [PROB_SPACE_ADDITIVE])
\\ sg `prob p (h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∪ ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))) =
       prob p (h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) +
       prob p (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))))`
   >-( sg `h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))) ∈ events p `
       >-(metis_tac [EVENTS_INTER, ETREE_NODE_N_STAIR_IN_EVENTS])
       \\ sg `ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))) ∈ events p`
	  >-(metis_tac [ETREE_NODE_TWO_STAIR_N_STAIR_IN_EVENTS])
       \\ sg `DISJOINT (h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L))))
                       (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L)))))`
	  >-( sg `disjoint (h' INSERT set h)`
	      >-( fs[disjoint]
		  \\ metis_tac [])    
              \\ metis_tac [DISJOINT_ETREE_N_STAIR])
           \\ metis_tac [ADDITIVE_PROB])
\\ POP_ORW
\\ sg `disjoint (set h) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs []
\\ sg ` MUTUAL_INDEP p (LN ⧺ h ⧺ FLAT L)`
   >-( once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ Q.ABBREV_TAC `x = h ⧺ FLAT L`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `[h']`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ sg `LN ⧺ [h'] ⧺ h ⧺ FLAT L = LN ⧺ h'::h ⧺ FLAT L`
	  >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++b``,rw[]))]
	      \\ rw [])
       \\ metis_tac [])
\\ fs []
\\ sg `(∀x'. MEM x' LN ∨ MEM x' h ∨ MEM x' (FLAT L) ⇒ x' ∈ events p)`
   >-(metis_tac [])
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST (⊗𝑳 h (⊗Ν𝑳 LN L))))) =
        SUM_LIST (PROB_LIST p LN) *
        (SUM_LIST (PROB_LIST p h) * ∏ (PROB_SUM_LIST p L)) `
   >-(metis_tac [])
\\ POP_ORW
\\ sg `prob p (h' ∩ ETREE (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))) =
       prob p (ETREE (BRANCH (PATH p [h']) (NODE (EVENT_TREE_LIST (⊗Ν𝑳 LN L)))))`
   >-(metis_tac [PATH_DEF, ETREE_DEF, INTER_PSPACE, INTER_COMM])
\\ POP_ORW
\\ DEP_REWRITE_TAC [ETREE_BRANCH_MULTIPLE_EVENTS_N_STAIR]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [EVENT_OUTCOME_SPACE_CONDS_DEF])
 >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ ho_match_mp_tac MUTUAL_INDEP_APPEND1
     \\ Q.ABBREV_TAC `x = LN ⧺ [h']`
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `h`
     \\ once_rewrite_tac[APPEND_ASSOC]
     \\ irule MUTUAL_INDEP_APPEND1
     \\ Q.UNABBREV_TAC `x`
     \\ sg `LN ⧺ [h'] ⧺ h ⧺ FLAT L = LN ⧺ h'::h ⧺ FLAT L`
	>-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++b``,rw[]))]
	    \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++b``,rw[]))]
	    \\ rw [])
     \\ metis_tac [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val NODE_OF_PATHS_IN_EVENTS = store_thm("NODE_OF_PATHS_IN_EVENTS",
  `` !p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) ==>
     (ETREE (NODE (EVENT_TREE_LIST ((MAP (\a. PATH p a)) L))) IN events p) ``,
RW_TAC std_ss[]
\\ Induct_on `L`
   >-( RW_TAC list_ss[ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ RW_TAC std_ss[EVENTS_EMPTY])
\\ RW_TAC list_ss[ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ sg `(∀x. MEM x (FLAT L) ⇒ x ∈ events p) `
   >-( metis_tac [])
\\ FULL_SIMP_TAC std_ss[]
\\ MATCH_MP_TAC EVENTS_UNION
\\ RW_TAC std_ss[]
\\ rw [PATH_IN_EVENTS]);
(*--------------------------------------------------------------------------------------------------*)

val PATH_APPEND = store_thm("PATH_APPEND",
 ``!p L1 L2. prob_space p /\ (!x. MEM x (L1++L2) ==> x IN events p) ==>
   ((PATH p L1) INTER (PATH p L2) =  PATH p (L1 ++ L2))``,
REPEAT GEN_TAC
\\ Induct_on `L1`
   >-( RW_TAC list_ss[PATH_DEF]
       \\  MATCH_MP_TAC INTER_PSPACE
       \\  RW_TAC std_ss[PATH_IN_EVENTS])
\\RW_TAC std_ss[PATH_DEF]
\\ fs [MEM_APPEND]
\\ sg `(∀x. MEM x (L1 ⧺ L2) ⇒ x ∈ events p) `
   >-( metis_tac [MEM_APPEND])
\\ rw [GSYM INTER_ASSOC]
\\ FULL_SIMP_TAC std_ss[]
\\ RW_TAC list_ss[PATH_DEF]);
(*--------------------------------------------------------------------------------------------------*)

val INTER_ASSOC_COMBINATION = store_thm("INTER_ASSOC_COMBINATION",
  ``!a b c d. a INTER b INTER c INTER d = a INTER (b INTER c) INTER d ``,
SRW_TAC [][IN_INTER,GSPECIFICATION,EXTENSION]
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)

val MEM_NULL_LIST = store_thm("MEM_NULL_LIST",
  ``!L1 L2 L. (!x. MEM x (L1::L2::L) ==> ~NULL x) ==> (!x. MEM x ((L1++L2)::L)  ==>  ~NULL x)``,
RW_TAC list_ss[]
>-( POP_ASSUM (MP_TAC o Q.SPEC `L2 `)
    \\ RW_TAC list_ss[])
\\ Induct_on `L1`
    >-(RW_TAC list_ss[])
\\ RW_TAC list_ss[]);
(*--------------------------------------------------------------------------------------------------*)

val PROB_PATH_APPEND = store_thm("PROB_PATH_APPEND",
  ``!p L2 L1. prob_space p /\ (!x. MEM x (L2++L1) ==> x IN events p ) /\ (~NULL L2) /\ (~NULL L1) /\  MUTUAL_INDEP p (L2++L1) ==>
    (prob p (PATH p (L2 ++ L1)) = prob p (PATH p L2) * prob p (PATH p L1))``,
GEN_TAC
\\ Induct
   >-(RW_TAC list_ss[PATH_DEF])
\\ RW_TAC std_ss[]
\\ sg`prob p (PATH p (h::L2 ++ L1)) = PROD_LIST (PROB_LIST p (h::L2 ++ L1)) `
   >-( MATCH_MP_TAC PROB_PATH
       \\ RW_TAC list_ss[])
\\ POP_ORW
\\ RW_TAC list_ss[PROB_LIST_DEF,PROD_LIST_DEF]
\\ sg `PROD_LIST (PROB_LIST p (L2 ++ L1)) = prob p (PATH p (L2 ++ L1))`
   >-( MATCH_MP_TAC EQ_SYM
       \\ MATCH_MP_TAC PROB_PATH
       \\  RW_TAC std_ss[]
       	   >-( FULL_SIMP_TAC list_ss[])
      	   >-( Cases_on `L2`
      	       >-(fs [MEM_APPEND])
      	       \\ fs [MEM_APPEND])
       \\ irule MUTUAL_INDEP_CONS
       \\ Q.EXISTS_TAC `h`
       \\ FULL_SIMP_TAC list_ss[])
\\ POP_ORW
\\ sg `prob p (PATH p (L2 ++ L1)) = prob p (PATH p L2) * prob p (PATH p L1)`
   >-( NTAC 5 (POP_ASSUM MP_TAC)
       \\ POP_ASSUM (MP_TAC o Q.SPEC `L1 `)
       \\  RW_TAC std_ss[]
       \\ FULL_SIMP_TAC std_ss[]
       \\ Cases_on `L2`
       	  >-( RW_TAC list_ss[PATH_DEF, PROB_UNIV]
     	      \\  RW_TAC real_ss[])
       \\ FULL_SIMP_TAC std_ss[NULL]
       \\ rw []
       \\ sg `(!x. MEM x ((h'::t ++ L1)) ==> x IN events p) /\ MUTUAL_INDEP p (h'::t ++ L1)`
          >-( RW_TAC std_ss[]
   	      >-( FULL_SIMP_TAC list_ss[])
   	      \\ MATCH_MP_TAC MUTUAL_INDEP_CONS
      	      \\ Q.EXISTS_TAC `h`
      	      \\ FULL_SIMP_TAC list_ss[])
       \\  rw [PATH_DEF]
       \\ fs [PATH_DEF]
       \\ sg `(∀x. (x = h' ∨ MEM x t) ∨ MEM x L1 ⇒ x ∈ events p) `
       	  >-( metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ sg`prob p (PATH p (h::L2))= prob p h * prob p (PATH p L2)`
   >-( NTAC 5 (POP_ASSUM MP_TAC)
       \\ POP_ASSUM (MP_TAC o Q.SPEC `[h] `)
       \\ RW_TAC std_ss[]
       \\ FULL_SIMP_TAC std_ss[]
       \\ Cases_on `L2`
       	  >- ( RW_TAC list_ss[PATH_DEF, PROB_UNIV]
	      \\ sg `h ∩ p_space p = p_space p ∩ h`
	         >-( rw [INTER_COMM])
              \\ POP_ORW
     	      \\ rw [INTER_PSPACE, MEM_APPEND])
       \\  FULL_SIMP_TAC std_ss[NULL]
       \\ sg `(!x. MEM x ((h'::t ++ [h])) ==> x IN events p) /\ MUTUAL_INDEP p (h'::t ++ [h])`
          >-( RW_TAC std_ss[]
  	      >-(FULL_SIMP_TAC list_ss[])
              \\ irule MUTUAL_INDEP_APPEND_SYM
     	      \\ RW_TAC std_ss[]
      	      \\ MATCH_MP_TAC MUTUAL_INDEP_FRONT_APPEND 
      	      \\ Q.EXISTS_TAC `L1`
	      \\ irule MUTUAL_INDEP_APPEND_SYM
     	      \\ rw []
	      \\ sg `h::h'::(t ⧺ L1) = h::h'::t ⧺ L1 `
	      	 >-( metis_tac [APPEND])
              \\ fs [])
        \\  FULL_SIMP_TAC std_ss[]
	\\ sg `PATH p (h'::t ⧺ [h]) = PATH p (h::h'::t) `
	   >-( rw [PATH_DEF]
	       \\ DEP_REWRITE_TAC [GSYM PATH_APPEND]
	       \\ rw []
	       	  >-( fs [MEM_APPEND])
		  >-( fs [MEM_APPEND])
	       \\ rw [PATH_DEF]
	       \\ sg `h ∩ p_space p = p_space p ∩ h`
	         >-( rw [INTER_COMM])
              \\ POP_ORW
	      \\ sg `p_space p ∩ h = h `
	      	 >-( rw [INTER_PSPACE])
	      \\ POP_ORW
	      \\ rw [INTER_ASSOC]
	      \\ rw [EXTENSION]
	      \\ metis_tac [])
        \\ fs []
	\\ rw [PATH_DEF]
	\\ sg `h ∩ p_space p = p_space p ∩ h`
	   >-( rw [INTER_COMM])
        \\ POP_ORW
	\\ sg `p_space p ∩ h = h `
	   >-( rw [INTER_PSPACE])
	\\ POP_ORW
	\\ REAL_ARITH_TAC)
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val PROB_COMPL_A_INTER_B = store_thm("PROB_COMPL_A_INTER_B",
``!p a b. prob_space p /\  (a IN events p /\  b IN events p)  ==>
   (prob p b = prob p (a INTER b) + prob p (COMPL_PSPACE p a INTER b ))``,
RW_TAC std_ss[]
\\ sg `(a INTER b)  UNION ((COMPL_PSPACE p a) INTER (b )) = b`
   >-( ONCE_REWRITE_TAC[INTER_COMM] 
       \\ RW_TAC std_ss[GSYM UNION_OVER_INTER]
       \\ RW_TAC std_ss[COMPL_PSPACE_DEF,DIFF_SAME_UNION]
       \\ sg `a SUBSET p_space p`
       	  >-( sg `a = p_space p INTER a`
	      >-( MATCH_MP_TAC EQ_SYM
              	  \\ MATCH_MP_TAC INTER_PSPACE
              	  \\ RW_TAC std_ss[])
              \\ ONCE_ASM_REWRITE_TAC[] 
              \\  RW_TAC std_ss[INTER_SUBSET])
         \\ RW_TAC std_ss[UNION_DIFF] 
         \\ ONCE_REWRITE_TAC[INTER_COMM] 
         \\ MATCH_MP_TAC INTER_PSPACE 
         \\ RW_TAC std_ss[])
\\ sg ` prob p (a INTER b) + prob p (COMPL_PSPACE p a INTER b) =
        prob p ( a INTER b UNION (COMPL_PSPACE p a INTER b))`
   >-( MATCH_MP_TAC EQ_SYM 
       \\ MATCH_MP_TAC PROB_ADDITIVE 
       \\ RW_TAC std_ss[]
          >-( MATCH_MP_TAC EVENTS_INTER
              \\ RW_TAC std_ss[])
          >-( MATCH_MP_TAC EVENTS_INTER
              \\ RW_TAC std_ss[COMPL_PSPACE_DEF] 
              \\ MATCH_MP_TAC EVENTS_COMPL
              \\ RW_TAC std_ss[])
          \\ RW_TAC std_ss[DISJOINT_DEF] 
          \\ RW_TAC std_ss[INTER_COMM] 
          \\ RW_TAC std_ss[INTER_ASSOC]
          \\ sg `(a INTER b INTER b INTER COMPL_PSPACE p a) =
	         (a INTER COMPL_PSPACE p a) INTER b`
             >-( SRW_TAC[][INTER_DEF,EXTENSION,GSPECIFICATION]
                 \\ EQ_TAC 
                    >-( RW_TAC std_ss[])
                 \\ RW_TAC std_ss[])
          \\ ONCE_ASM_REWRITE_TAC[] 
          \\ RW_TAC std_ss[COMPL_PSPACE_DEF] 
          \\ sg `a INTER (p_space p DIFF a) = EMPTY`
	     >-( ONCE_REWRITE_TAC[INTER_COMM]
                 \\ RW_TAC std_ss[DIFF_INTER] 
                 \\ sg `p_space p INTER  a  =  a`
		    >-( MATCH_MP_TAC INTER_PSPACE 
                        \\ RW_TAC std_ss[])
                 \\ ONCE_ASM_REWRITE_TAC[] 
                 \\ RW_TAC std_ss[DIFF_EQ_EMPTY])
          \\ ONCE_ASM_REWRITE_TAC[] 
          \\ RW_TAC std_ss[INTER_EMPTY])
\\ FULL_SIMP_TAC std_ss[]);
(*--------------------------------------------------------------------------------------------------*)

val PROB_A_UNION_B = store_thm("PROB_A_UNION_B",
``!p A B. prob_space p /\ A IN events p /\ B IN events p ==>
  ( prob p (A UNION B) = prob p (A) + prob p (B) - prob p (A INTER B))``,
REPEAT GEN_TAC
\\ RW_TAC std_ss[] 
\\ sg` prob p (A UNION (COMPL_PSPACE p A  INTER B)) = prob p (A ) + prob p (COMPL_PSPACE p A INTER B)`
   >-( MATCH_MP_TAC PROB_ADDITIVE
       \\ rw []
          >-(  MATCH_MP_TAC EVENTS_INTER
      	       \\ RW_TAC std_ss[COMPL_PSPACE_DEF]
     	       \\ MATCH_MP_TAC EVENTS_COMPL 
      	       \\ RW_TAC std_ss[])
       \\ RW_TAC std_ss[DISJOINT_DEF]
       \\ RW_TAC std_ss[INTER_ASSOC]
       \\ RW_TAC std_ss[COMPL_PSPACE_DEF] 
       \\ sg `A INTER (p_space p DIFF A) = EMPTY`
       	  >-( ONCE_REWRITE_TAC[INTER_COMM]
	      \\  RW_TAC std_ss[DIFF_INTER] 
      	      \\ sg `p_space p INTER A  =  A`
	      	 >-( MATCH_MP_TAC INTER_PSPACE 
          	     \\ RW_TAC std_ss[])
              \\ ONCE_ASM_REWRITE_TAC[] 
              \\ RW_TAC std_ss[DIFF_EQ_EMPTY])
       \\ ONCE_ASM_REWRITE_TAC[] 
       \\ RW_TAC std_ss[INTER_EMPTY])
\\ sg`A UNION (COMPL_PSPACE p A INTER B) = A UNION B`
   >-( RW_TAC std_ss[INTER_OVER_UNION]
       \\  RW_TAC std_ss[COMPL_PSPACE_DEF] 
       \\ sg`(A UNION (p_space p DIFF A)) = p_space p`
          >-( sg`A SUBSET p_space p` 
              >-( sg `A = p_space p INTER A`
	      	  >-( MATCH_MP_TAC EQ_SYM 
                      \\ MATCH_MP_TAC INTER_PSPACE
                      \\ RW_TAC std_ss[]) 
                  \\ ONCE_ASM_REWRITE_TAC[] 
           	  \\ RW_TAC std_ss[INTER_SUBSET])
              \\ RW_TAC std_ss[UNION_DIFF]) 
       \\ ONCE_ASM_REWRITE_TAC[] 
       \\ MATCH_MP_TAC INTER_PSPACE
       \\ RW_TAC std_ss[] 
       \\ MATCH_MP_TAC EVENTS_UNION
       \\ RW_TAC std_ss[]) 
\\ FULL_SIMP_TAC std_ss[]
\\ sg `prob p B = prob p (A ∩ B) + prob p (COMPL_PSPACE p A ∩ B) `
   >-( rw[ PROB_COMPL_A_INTER_B])
\\ RW_TAC std_ss[] 
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val MEM_NULL_LIST = store_thm("MEM_NULL_LIST",
  ``!L1 h L. (∀x. x = L1 ∨ x = h ∨ MEM x L ⇒ ~NULL x) ==>
  	      (∀x. x = h ⧺ L1 ∨ MEM x L ⇒ ~NULL x)``,
RW_TAC list_ss[]
>-( rw [NULL_APPEND])
\\ RW_TAC list_ss[]);
(*--------------------------------------------------------------------------------------------------*)

val PATH_INTER_NODE_PATHS = store_thm("PATH_INTER_NODE_PATHS",
  ``!p L L1. prob_space p /\(!x. MEM x (L1::L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L1::L))) ==> x IN events p)
            /\ MUTUAL_INDEP p (FLAT (L1::L)) ==>
    (prob p ((PATH p L1) INTER (ETREE (NODE (EVENT_TREE_LIST ((MAP (\a. PATH p a)) L)))))
     =  prob p (PATH p L1) * prob p (ETREE (NODE (EVENT_TREE_LIST ((MAP (\a. PATH p a)) L)))))``,
GEN_TAC
\\ Induct
   >-( RW_TAC list_ss[EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF, INTER_EMPTY,PROB_EMPTY]
       \\ RW_TAC real_ss[])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF]
\\ RW_TAC std_ss[GSYM EVENT_TREE_LIST_DEF]
\\ RW_TAC std_ss[UNION_OVER_INTER]
\\ sg `PATH p L1 ∩ PATH p h = PATH p (h++L1)`
   >-( ONCE_REWRITE_TAC[INTER_COMM]
       \\ MATCH_MP_TAC PATH_APPEND
       \\ RW_TAC std_ss[]
       \\ FULL_SIMP_TAC list_ss[])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ RW_TAC std_ss[]
   >-( sg `PATH p (h ⧺ L1) = PATH p h ∩ PATH p L1 `
       >-( DEP_REWRITE_TAC [PATH_APPEND]
       	   \\ rw []
	   \\ metis_tac [])
       \\ fs []
       \\ FULL_SIMP_TAC std_ss[PATH_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [PATH_IN_EVENTS, EVENTS_INTER, NODE_OF_PATHS_IN_EVENTS])
   >-( metis_tac [PATH_IN_EVENTS])
   >-( metis_tac [ NODE_OF_PATHS_IN_EVENTS])
\\ RW_TAC std_ss[INTER_ASSOC]
\\ sg `PATH p (h ⧺ L1) = PATH p h ∩ PATH p L1 `
   >-( DEP_REWRITE_TAC [PATH_APPEND]
       \\ rw []
       \\ metis_tac [])
\\ FULL_SIMP_TAC std_ss[INTER_ASSOC]
\\ sg `PATH p h ∩ PATH p L1 ∩ PATH p L1 ∩
           ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))) =
       PATH p h ∩ PATH p L1 ∩ 
           ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L)))`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p h ∩ PATH p L1 = PATH p (h ⧺ L1) `
   >-( DEP_REWRITE_TAC [PATH_APPEND]
       \\ rw []
       \\ metis_tac [])
\\ POP_ORW 
\\ sg ` prob p (PATH p (h ⧺ L1) ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L)))) =
	prob p (PATH p (h ⧺ L1))  * prob p (ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))))` 
   >-( NTAC 4 (POP_ASSUM MP_TAC)
       \\ first_x_assum (mp_tac o Q.SPECL [`h ++ L1`]) 
       \\ rw []
       \\ sg `PATH p (h ⧺ L1) = PATH p h ∩ PATH p L1 `
       	  >-( DEP_REWRITE_TAC [PATH_APPEND]
       	      \\ rw []
       	      \\ metis_tac [])
       \\ FULL_SIMP_TAC list_ss[]
       \\ POP_ORW
       \\ sg `  (∀x. x = h ⧺ L1 ∨ MEM x L ⇒ ~NULL x) ∧
                (∀x. (MEM x h ∨ MEM x L1) ∨ MEM x (FLAT L) ⇒ x ∈ events p) ∧
                MUTUAL_INDEP p (h ⧺ L1 ⧺ FLAT L) `
          >-( STRIP_TAC
	      >-( metis_tac [MEM_NULL_LIST])
	      \\ STRIP_TAC
	      	 >-( metis_tac [])
              \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p L1 ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L)))) =
   prob p (PATH p L1) * prob p (ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))))`
   >-( NTAC 4 (POP_ASSUM MP_TAC)
       \\ first_x_assum (mp_tac o Q.SPECL [`L1`]) 
       \\ rw []
       \\ sg `(∀x. x = L1 ∨ MEM x L ⇒ ~NULL x) ∧
              (∀x. MEM x L1 ∨ MEM x (FLAT L) ⇒ x ∈ events p) ∧
              MUTUAL_INDEP p (L1 ⧺ FLAT L) `
          >-( STRIP_TAC
	      >-( metis_tac [])
	      \\ STRIP_TAC
	      	 >-( metis_tac [])
              \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `h`
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw [])
      \\ metis_tac [])
\\ sg `prob p (PATH p h ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L)))) =
   prob p (PATH p h) * prob p (ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))))`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
         >-( metis_tac [])
	 >-( metis_tac [])
	 >-( metis_tac [])
	 >-( metis_tac [])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_APPEND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val PROB_NODE_OF_PATHS = store_thm("PROB_NODE_OF_PATHS",
  ``!p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\
     disjoint (set (MAP (λa. PATH p a) L)) /\ ALL_DISTINCT (MAP (λa. PATH p a) L) /\
    (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( MUTUAL_INDEP p (FLAT L)) ==>
    (prob p (ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L)))) =
    SUM_LIST (MAP (λa. PROD_LIST (PROB_LIST p a)) L))``,
    
GEN_TAC
\\ Induct
  >-(RW_TAC list_ss[ETREE_DEF, EVENT_TREE_LIST_DEF, PROD_LIST_DEF,PROB_EMPTY, SUM_LIST_DEF])
\\ RW_TAC list_ss[ETREE_DEF, EVENT_TREE_LIST_DEF, PROD_LIST_DEF,PROB_EMPTY, SUM_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ FULL_SIMP_TAC std_ss[]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS])
   >-( metis_tac [NODE_OF_PATHS_IN_EVENTS])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ sg `MUTUAL_INDEP p (FLAT L) `
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ rw [])
\\ sg `disjoint (set (MAP (λa. PATH p a) L)) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ FULL_SIMP_TAC std_ss[]
\\ sg `PATH p h ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))) = {} `
   >-(  ntac 4 POP_ORW
   	\\ NTAC 4 (POP_ASSUM MP_TAC)
   	\\ ntac 2 POP_ORW
	\\ rw []
	\\ Induct_on `L`
      	   >-( RW_TAC list_ss[ETREE_DEF, EVENT_TREE_LIST_DEF, PROD_LIST_DEF,PROB_EMPTY, SUM_LIST_DEF]
       	       \\ rw [])
      \\ RW_TAC list_ss[ETREE_DEF, EVENT_TREE_LIST_DEF, PROD_LIST_DEF,PROB_EMPTY, SUM_LIST_DEF]
      \\ rw [GSYM EVENT_TREE_LIST_DEF]
      \\ rw [UNION_OVER_INTER]
         >-( fs [disjoint]
	     \\ metis_tac [])
      \\ FULL_SIMP_TAC std_ss[]
      \\ sg `disjoint (PATH p h INSERT set (MAP (λa. PATH p a) L)) `
         >-( fs [disjoint]
	     \\ metis_tac [])      
      \\ metis_tac [])
\\ FULL_SIMP_TAC std_ss[]
\\ rw [PROB_EMPTY]);
(*--------------------------------------------------------------------------------------------------*)

val MAP_ET_PATH_EQ_MAP_PATHS = store_thm("MAP_ET_PATH_EQ_MAP_PATHS",
``! L p. prob_space p /\  (!x'. MEM x' (FLAT (L)) ==> (x' IN events p))
         ==> MAP (λa. ET_PATH p a) L = MAP (λa. PATH p a) L``,
Induct
>-( rw [ET_PATH_DEF, PATH_DEF])
\\ rw [ET_PATH_DEF, PATH_DEF]
\\ DEP_REWRITE_TAC [ET_PATH_EQ_PATH]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_ET_PATH = store_thm("PROB_ET_PATH",
  ``!p L. prob_space p /\ ~NULL L /\ (!x'. MEM x' L ==> x'  IN  events p ) /\
 MUTUAL_INDEP p L ==> (prob p (ET_PATH p L) =  PROD_LIST (PROB_LIST p L))``,
rw []
\\ DEP_REWRITE_TAC [ET_PATH_EQ_PATH]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_NODE_OF_ET_PATHS = store_thm("PROB_NODE_OF_ET_PATHS",
  ``!p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\
     disjoint (set (MAP (λa. PATH p a) L)) /\ ALL_DISTINCT (MAP (λa. PATH p a) L) /\
    (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( MUTUAL_INDEP p (FLAT L)) ==>
    (prob p (ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a) L)))) =
    SUM_LIST (MAP (λa. PROD_LIST (PROB_LIST p a)) L))``,

rw []
\\ DEP_REWRITE_TAC [MAP_ET_PATH_EQ_MAP_PATHS]
\\ DEP_REWRITE_TAC [PROB_NODE_OF_PATHS]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

		    (*----------------------------------------------------*)  
		    (*    Failure and Success Probability Distributions   *)
		    (*----------------------------------------------------*)

(*-----------------*)  
(*   Definitions   *)
(*-----------------*)

val FAIL_DEF = Define
`FAIL p X t =  PREIMAGE X {y | y <= Normal t} ∩ p_space p `;

val SUCCESS_DEF = Define `
SUCCESS p X t =  PREIMAGE X {y | Normal t < y} ∩ p_space p `;

val CDF_DEF = Define
`CDF p X t = distribution p X {y | y <= Normal t} `;

val RELIABILITY_DEF = Define
`RELIABILITY p X t =  distribution p X {y |  Normal t < y}`;

val EXP_ET_FAIL_DISTRIB_DEF = Define
`EXP_ET_FAIL_DISTRIB p X FR = !t. 0 <= t ==> (CDF p X t = 1 - exp (-FR * t))`;

val EXP_ET_SUCCESS_DISTRIB_DEF = Define
`EXP_ET_SUCCESS_DISTRIB p X FR = !t. 0 <= t ==> (RELIABILITY p X t = exp (-FR * t))`;

val EXP_ET_FAIL_DISTRIB_LIST_DEF = Define
` (EXP_ET_FAIL_DISTRIB_LIST p [] [] = T) /\
  (EXP_ET_FAIL_DISTRIB_LIST p (h::t) (x::xs) <=> (EXP_ET_FAIL_DISTRIB p h x) /\ EXP_ET_FAIL_DISTRIB_LIST p t xs) `;


val EXP_ET_SUCCESS_DISTRIB_LIST_DEF = Define
`(EXP_ET_SUCCESS_DISTRIB_LIST p [] [] = T) /\
 (EXP_ET_SUCCESS_DISTRIB_LIST p (h::t) (x::xs) <=> (EXP_ET_SUCCESS_DISTRIB p h x) /\ EXP_ET_SUCCESS_DISTRIB_LIST p t xs) `;
						     
val SUCCESS_FAIL_LIST_DEF = Define
`(SUCCESS_FAIL_LIST p [] t = []) /\
 (SUCCESS_FAIL_LIST p (h::L) t = [SUCCESS p h t; FAIL p h t]::SUCCESS_FAIL_LIST p L t)`;

val UP    =  U 0x02191;
val DOWN  =  U 0x02193;

val _ = Unicode.unicode_version {tmnm = "SUCCESS",  u = UP};
val _ = Unicode.unicode_version {tmnm = "FAIL", u = DOWN};
val _ = Unicode.unicode_version {tmnm = "SUCCESS_FAIL_LIST", u = UP^DOWN};
(*--------------------------------------------------------------------------------------------------*)

val SUCCESS_EQ_FAIL  = store_thm("SUCCESS_EQ_FAIL",
  ``!X t p. p_space p DIFF ↓ p X t = ↑ p X t ``,
  RW_TAC std_ss[FAIL_DEF, SUCCESS_DEF]  
  \\ SRW_TAC[][IN_DIFF,PREIMAGE_def,EXTENSION,GSPECIFICATION]
  \\ RW_TAC std_ss[GSYM extreal_lt_def]
  \\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val COMPL_SUCCESS_PREIMAGE_EQ_FAIL_PREIMAGE  = store_thm("COMPL_SUCCESS_PREIMAGE_EQ_FAIL_PREIMAGE",
``!p t s. prob_space p ==> ((p_space p DIFF PREIMAGE s {y | Normal t < y} ∩ p_space p)
                            = (PREIMAGE s {y | y <= Normal t} ∩ p_space p))  ``,
SRW_TAC[][PREIMAGE_def,DIFF_DEF,EXTENSION,GSPECIFICATION,REAL_NOT_LT]
\\ sg`!x y. ~(x < y) = ~(~(y <=  x)) `
   >-( RW_TAC std_ss [] 
       \\ PROVE_TAC[extreal_lt_def])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)  
(*     Probability of Event Tree Node  Equal 1    *)
(*------------------------------------------------*)

val PROB_ETREE_NODE_EQ_ONE = store_thm("PROB_ETREE_NODE_EQ_ONE",
``!p L t.   prob_space p ∧ ΩΝC (↑↓ p [L] t) ∧
            (∀x'. MEM x' (FLAT (↑↓ p [L] t)) ⇒ x' ∈ events p) ⇒
            prob p (ETREE (NODE (EVENT_TREE_LIST (FLAT (↑↓ p [L] t))))) = 1``,

rw [FLAT, SUCCESS_FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [SUM_LIST_DEF, PROD_LIST_DEF, PROB_LIST_DEF, PROB_EMPTY]
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `prob p (PREIMAGE L {y | y ≤ Normal t} ∩ p_space p) = distribution p L {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)  
(*     Probability of Event Tree Branch Success   *)
(*------------------------------------------------*)

val PROB_BRANCH_SUCCESS= store_thm("PROB_BRANCH_SUCCESS",
``!p L X t FR_X.
            prob_space p ∧ 0 ≤ t ∧ ΩΝC (↑↓ p [L] t) ∧
            (∀x'. MEM x' (FLAT (↑↓ p [X; L] t)) ⇒ x' ∈ events p) ∧
            MUTUAL_INDEP p (FLAT (↑↓ p [X; L] t)) ∧
            EXP_ET_FAIL_DISTRIB p X FR_X ⇒
            prob p
              (ETREE
                 (BRANCH (↑ p X t)
                    (NODE (EVENT_TREE_LIST (FLAT (↑↓ p [L] t)))))) = exp (-FR_X * t)``,

rw [FLAT, SUCCESS_FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_BRANCH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a c. a::c = [a]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[FAIL p X t]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1 
       \\ rw[])
\\ rw [PROB_EMPTY]
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ fs []
\\ sg `prob p (PREIMAGE L {y | y ≤ Normal t} ∩ p_space p) = distribution p L {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [SUM_LIST_DEF, PROB_LIST_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ sg `prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ fs [EXP_ET_FAIL_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)  
(*     Probability of Event Tree Branch Failure   *)
(*------------------------------------------------*)

val PROB_BRANCH_FAIL= store_thm("PROB_BRANCH_FAIL",
``!p L X t FR_X.
       prob_space p ∧ 0 ≤ t ∧ ΩΝC (↑↓ p [L] t) ∧
            (∀x'. MEM x' (FLAT (↑↓ p [X; L] t)) ⇒ x' ∈ events p) ∧
            MUTUAL_INDEP p (FLAT (↑↓ p [X; L] t)) ∧
            EXP_ET_FAIL_DISTRIB p X FR_X ⇒
            prob p
              (ETREE
                 (BRANCH (↓ p X t)
                    (NODE (EVENT_TREE_LIST (FLAT (↑↓ p [L] t)))))) = 1 − exp (-FR_X * t)``,

rw [FLAT, SUCCESS_FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_BRANCH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_CONS
       \\ Q.EXISTS_TAC `SUCCESS p X t`
       \\ rw[])
\\ rw [PROB_EMPTY]
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ fs []
\\ sg `prob p (PREIMAGE L {y | y ≤ Normal t} ∩ p_space p) = distribution p L {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [SUM_LIST_DEF, PROB_LIST_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ sg `prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ fs [EXP_ET_FAIL_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)  
(*   Probability of Event Tree N Stair  Equal 1   *)
(*------------------------------------------------*)

val PROB_ETREE_N_STAIR_EQ_ONE = store_thm("PROB_ETREE_N_STAIR_EQ_ONE",
``!p L LN t.
           prob_space p ∧ ΩΝC (↑↓ p (LN::L) t) ∧
            (∀x'. MEM x' (FLAT (↑↓ p (LN::L) t)) ⇒ x' ∈ events p) ∧
            MUTUAL_INDEP p (FLAT (↑↓ p (LN::L) t)) ⇒
            prob p
              (ETREE
                 (NODE
                    (EVENT_TREE_LIST (⊗Ν𝑳 (FLAT (↑↓ p [LN] t)) (↑↓ p L t))))) = 1``,
 
rw [FLAT, SUCCESS_FAIL_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_ETREE_N_STAIR]
\\ rw []
   >-(metis_tac [SUCCESS_FAIL_LIST_DEF])
   >-(fs [SUCCESS_FAIL_LIST_DEF, FLAT])
   >-(fs [SUCCESS_FAIL_LIST_DEF, FLAT])
\\ rw [PROB_SUM_LIST_DEF]
\\ rw [PROD_LIST_DEF]
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ rw [SUM_LIST_DEF, PROB_LIST_DEF]
\\ sg `prob p (PREIMAGE LN {y | y ≤ Normal t} ∩ p_space p) = distribution p LN {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ rw [PROB_EMPTY]
\\ Induct_on `L`
   >-(rw [SUCCESS_FAIL_LIST_DEF, PROB_SUM_LIST_DEF, PROD_LIST_DEF])
\\ rw [SUCCESS_FAIL_LIST_DEF, PROB_SUM_LIST_DEF, PROD_LIST_DEF]
\\ rw [PROB_EMPTY]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [REAL_SUB_ADD]
\\ rw [SUM_LIST_DEF, PROB_LIST_DEF]
\\ sg `(∀x'. x' = SUCCESS p LN t ∨ x' = FAIL p LN t ∨
             MEM x' (FLAT (SUCCESS_FAIL_LIST p L t)) ⇒
             x' ∈ events p) `
   >-(metis_tac [])
\\ sg `EVENT_OUTCOME_SPACE_CONDS
          ([SUCCESS p LN t; FAIL p LN t]::SUCCESS_FAIL_LIST p L t) `
   >-(metis_tac [EVENT_OUTCOME_SPACE_CONDS_DEF])
\\ fs []
\\ sg ` MUTUAL_INDEP p (SUCCESS p LN t::FAIL p LN t::
               FLAT (SUCCESS_FAIL_LIST p L t))`
   >-( once_rewrite_tac[(prove(``!a b c. a::b::c = [a;b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND 
       \\ Q.EXISTS_TAC `[SUCCESS p h t]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1 
       \\ rw[]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c::e = [a;b;c]++e``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `[FAIL p h t]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1 
       \\ rw[])
\\ sg `∏ (PROB_SUM_LIST p (↑↓ p L t)) = 1 `
   >-( metis_tac [])
\\ fs []
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

	(*------------------------------------------------------------------------*)
     	(* Power System Generic Functions of  SAIFI, SAIDI and CAIDI for N Buses  *)
     	(*------------------------------------------------------------------------*)

val LOAD_INTERRUPTIONS_DEF = Define
`(LOAD_INTERRUPTIONS LN L Ns CEs [] [] p = 0) /\ 
 (LOAD_INTERRUPTIONS LN L Ns CEs (E::Es) (CN::CNs) p =
  (\a b. prob p (ETREE (NODE (EVENT_TREE_LIST (PARTITIONING a
	 (NESTED_COMPLETE_CYLINDER (ETREE_N_STAIR LN L) Ns CEs))))) * b) E (&CN)
 + (LOAD_INTERRUPTIONS LN L Ns CEs Es CNs p))`;

val LIGHTNING  =  U 0x021AF;
val _ = Unicode.unicode_version {tmnm = "LOAD_INTERRUPTIONS", u = SUM^L^O^A^D^LIGHTNING};
(*--------------------------------------------------------------------------------------------------*)

val GRID_INTERRUPTIONS_DEF = Define
`(GRID_INTERRUPTIONS [] [] [] [] [] [] p = 0) /\
 (GRID_INTERRUPTIONS (LN::LN_ALL) (L::L_ALL) (Ns::Ns_ALL) (CEs::CEs_ALL) (Es::Es_ALL) (CNs::CNs_ALL) p =
  ∑𝑳𝑶𝑨𝑫↯ LN L Ns CEs Es CNs p +
  GRID_INTERRUPTIONS LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL CNs_ALL p)`;

val _ = Unicode.unicode_version {tmnm = "GRID_INTERRUPTIONS", u = SUM^G^R^I^D^LIGHTNING};
(*--------------------------------------------------------------------------------------------------*)

val SUM_CUSTOMERS_DEF = Define
`(SUM_CUSTOMER [] = 0) /\
 (SUM_CUSTOMER (h::L) = LAST (h:num list) + SUM_CUSTOMER L)`;
(*--------------------------------------------------------------------------------------------------*)

val SAIFI_DEF = Define
`SAIFI LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL CNs_ALL p =
(∑𝑮𝑹𝑰𝑫↯ LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL CNs_ALL p)/ (&SUM_CUSTOMER CNs_ALL)`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val LOAD_TIME_INTERRUPTIONS_DEF = Define
`(LOAD_TIME_INTERRUPTIONS LN L Ns CEs [] [] [] p = 0) /\ 
 (LOAD_TIME_INTERRUPTIONS LN L Ns CEs (E::Es)  (MTTR::MTTRs) (CN::CNs) p =
  (\a b c. prob p (ETREE (NODE (EVENT_TREE_LIST (PARTITIONING a
	 (NESTED_COMPLETE_CYLINDER (ETREE_N_STAIR LN L) Ns CEs))))) * b * c) E (&CN) MTTR
 + (LOAD_TIME_INTERRUPTIONS LN L Ns CEs Es MTTRs CNs p))`;

val _ = Unicode.unicode_version {tmnm = "LOAD_TIME_INTERRUPTIONS", u = SUM^T^L^O^A^D^LIGHTNING};
(*--------------------------------------------------------------------------------------------------*)

val GRID_TIME_INTERRUPTIONS_DEF = Define
`(GRID_TIME_INTERRUPTIONS [] [] [] [] [] [] [] p = 0) /\
 (GRID_TIME_INTERRUPTIONS (LN::LN_ALL) (L::L_ALL) (Ns::Ns_ALL) (CEs::CEs_ALL) (Es::Es_ALL)
                          (MTTRs::MTTRs_ALL) (CNs::CNs_ALL) p =
  ∑𝑻𝑳𝑶𝑨𝑫↯ LN L Ns CEs Es MTTRs CNs p +
  GRID_TIME_INTERRUPTIONS LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL MTTRs_ALL CNs_ALL p)`;


val _ = Unicode.unicode_version {tmnm = "GRID_TIME_INTERRUPTIONS", u = SUM^T^G^R^I^D^LIGHTNING};
(*--------------------------------------------------------------------------------------------------*)

val SAIDI_DEF = Define
`SAIDI LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL MTTRs_ALL CNs_ALL p =
(∑𝑻𝑮𝑹𝑰𝑫↯ LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL MTTRs_ALL CNs_ALL p)/ (&SUM_CUSTOMER CNs_ALL)`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

val CAIDI_DEF = Define
`CAIDI  LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL MTTRs_ALL CNs_ALL p =
 (SAIDI LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL MTTRs_ALL CNs_ALL p)/(SAIFI LN_ALL L_ALL Ns_ALL CEs_ALL Es_ALL CNs_ALL p)`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*where*)
(* LN   : Last subsystem modes*)
(* L    : list of subsystems modes in order*)
(* Ns   : list of complete cylinder path numbers in order*)
(* CEs  : list of complete cylinder conditional events in order*)
(* Ms   : list of events partitioning paths in order*)
(* CNs  : list of customer numbers affected by Ms in order*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

				(*----------------------------*)  
				(*   ML Automatic Functions   *)
				(*----------------------------*)

val ERR = Feedback.mk_HOL_ERR "binary_ieeeLib"
(*--------------------------------------------------------------------------------------------------*)

fun HOL_TO_REAL t =
  if      t ~~ ``($*):real -> real -> real`` then Real.*
  else if t ~~ ``($+):real -> real -> real`` then Real.+
  else if t ~~ ``($/):real -> real -> real`` then Real./
  else if t ~~ ``($-):real -> real -> real`` then Real.-
  else failwith "Unrecognized HOL operator";
(*--------------------------------------------------------------------------------------------------*)

fun REAL_TO_POS_ARBRAT tm =
      case Lib.total realSyntax.dest_injected tm of
         SOME a => Arbrat.fromNat (numLib.dest_numeral a)
       | NONE => raise ERR "REAL_TO_POS_ARBRAT" "";
(*--------------------------------------------------------------------------------------------------*)

fun REAL_TO_SIGNED_ARBRAT tm =
      case Lib.total realSyntax.dest_negated tm of
         SOME a => Arbrat.negate (REAL_TO_POS_ARBRAT a)
       | NONE => REAL_TO_POS_ARBRAT tm;
(*--------------------------------------------------------------------------------------------------*)
     
fun REAL_TO_ARBRAT tm =
      case Lib.total realSyntax.dest_div tm of
         SOME (a, b) =>
            Arbrat./ (REAL_TO_SIGNED_ARBRAT a, REAL_TO_SIGNED_ARBRAT b)
       | NONE => REAL_TO_SIGNED_ARBRAT tm;
(*--------------------------------------------------------------------------------------------------*)
       
fun ARBRAT_TO_MATH_REAL x =
  Real./ (Real.fromInt (Arbint.toInt (Arbrat.numerator x)),
          Real.fromInt (Arbnum.toInt (Arbrat.denominator x)));
(*--------------------------------------------------------------------------------------------------*)

val REAL_TO_MATH_REAL = ARBRAT_TO_MATH_REAL o REAL_TO_ARBRAT;

fun HOL_TO_REAL_EVALUATION t =
 let
     val failstring = "Symbolic expression could not be translated in a number"
 in
     case strip_comb t of 
       (f,[a1, a2]) => HOL_TO_REAL f (HOL_TO_REAL_EVALUATION a1, HOL_TO_REAL_EVALUATION a2)
       | (f,[a]) =>
           if f ~~ ``($&):num -> real`` then Arbnum.toReal (dest_numeral a)
           else failwith failstring
       | _ => failwith failstring
 end;
(*--------------------------------------------------------------------------------------------------*)

fun HOL4_EVALUATION t =
 let
    val failstring = "Symbolic expression could not be translated in a number"
 in
    case strip_comb t of (f,[a1,a2]) =>  

       HOL_TO_REAL f (HOL4_EVALUATION a1,HOL4_EVALUATION a2)
       | (f,[a]) =>
                if f ~~ ``($&):num -> real`` then Arbnum.toReal (dest_numeral a)
	   	else if f ~~  ``exp:real -> real`` then Math.exp (REAL_TO_MATH_REAL (a))
		else failwith failstring
       |_ => failwith failstring
 end;
(*--------------------------------------------------------------------------------------------------*)

				(*----------------------------*)  
				(*    ML Printing Functions   *)
				(*----------------------------*)
				
fun CONVERT_LIST (L:term) = fst(dest_list L);
(*--------------------------------------------------------------------------------------------------*)

fun PRINT_PATH n L =
let
     val value = List.nth ((CONVERT_LIST L), n);
in
     print("Path #" ^ " " ^ (int_to_string (n)) ^ " : " ^ " " ^ (term_to_string (value)) ^  "\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun PRINT_ALL_PATH_NUMBERS L =
let
    val N = ref (List.length (CONVERT_LIST L) - 1)
in
    while !N <> 0 do
        (PRINT_PATH (!N) L;N := !N -1);
  PRINT_PATH (!N) L
end;
(*--------------------------------------------------------------------------------------------------*)

fun PROBABILITY T X =
let 
    val value = HOL4_EVALUATION  X;
in
    print("Actual Probability of " ^ " " ^ (term_to_string (T)) ^ " " ^ "Equal" ^ " ");
    print(Real.toString (value) ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun SAIFI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("SAIFI for 5 Years" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Interruptions / System Customer"^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun SAIDI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("SAIDI for 5 Years" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Hours / System Customer"^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun CAIDI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("CAIDI for 5 Years" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Hours / Customer Interruption"^ "\n\n")
end;

val _ = export_theory();
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
	(*------------------------------------------------------------------------------*)
		       (*--------------------------------------------------*)
			         (*--------------------------------*)
					  (*---------------*)