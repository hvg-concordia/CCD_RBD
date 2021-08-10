(* ========================================================================= *)
(* File Name: CCD_FT.sml	          	                             *)
(*---------------------------------------------------------------------------*)
(*          Description: Cause Consequence Diagram Reliability Analysis      *)
(*	    		 based on Fault Trees and Event Trees  using         *)
(*                       Theorem Proving	  			     *)
(*                                                                           *)
(*          HOL4-Kananaskis 13 		 			     	     *)
(*									     *)
(*	    Author : Mohamed Wagdy Abdelghany             		     *)
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
	  "real_sigmaTheory", "cardinalTheory", "FTreeTheory", "ETreeTheory", "RBDTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax lebesgueTheory real_sigmaTheory cardinalTheory
     FTreeTheory ETreeTheory RBDTheory;

val _ = new_theory "CCD_FT";

(*---------------------------------------------------------------------------------------------------*)

			(*--------------------------------------------*)  
			(*     Cause-Consequence Diagram Definition   *)
			(*--------------------------------------------*)

val DECISION_BOX_DEF = Define
`DECISION_BOX p X Y =  if X = (1:num) then FST Y
	      	        else if X = 0 then SND Y
		        else p_space p`;

val CONSEQ_PATH_DEF = Define
`(CONSEQ_PATH p [] = p_space p) /\
 (CONSEQ_PATH p (h::t)  = FOLDL (λa b. ETREE (BRANCH a (ATOMIC b))) h t)  `;

val CONSEQ_BOX_DEF = Define
`CONSEQ_BOX p L = ETREE (NODE (EVENT_TREE_LIST ((MAP (\a. CONSEQ_PATH p a)) L)))  `;

val NAND_DEF = Define `NAND p L = FTree p (NOT (AND (gate_list L)))`;

val NOR_DEF  = Define `NOR p L  = FTree p (NOT (OR (gate_list L)))`;

val COMPL_PSPACE_DEF = Define `COMPL_PSPACE p s = p_space p DIFF s`;

val BIG_UNION_DEF =  Define
 ` (BIG_UNION p [] = {}) /\
   (BIG_UNION p (h::t)  = (h  UNION BIG_UNION  p t ))`;

val FAIL_LIST_DEF = Define
`(FAIL_LIST p [] t = []) /\
 (FAIL_LIST p (h::L) t = FAIL p h t::FAIL_LIST p L t)`;

val N_DECISION_BOXES_DEF = Define
`(N_DECISION_BOXES p [] [] = []) /\
 (N_DECISION_BOXES p (X::N) (Y::M) =  (DECISION_BOX p X Y)::N_DECISION_BOXES p N M) `;

val SUBSYSTEMS_OR_DEF = Define
`(SUBSYSTEMS_OR p [] = []) /\
 (SUBSYSTEMS_OR p (h::L) = FTree p (OR h)::SUBSYSTEMS_OR p L)`;

val COMPL_SUBSYSTEMS_OR_DEF = Define
`(COMPL_SUBSYSTEMS_OR p [] = []) /\
 (COMPL_SUBSYSTEMS_OR p (h::L) = (NOR p h)::COMPL_SUBSYSTEMS_OR p L)`;

val SUBSYSTEMS_AND_DEF = Define
`(SUBSYSTEMS_AND p [] = []) /\
 (SUBSYSTEMS_AND p (h::L) = FTree p (AND h)::SUBSYSTEMS_AND p L)`;

val COMPL_SUBSYSTEMS_AND_DEF = Define
`(COMPL_SUBSYSTEMS_AND p [] = []) /\
 (COMPL_SUBSYSTEMS_AND p (h::L) = (NAND p h)::COMPL_SUBSYSTEMS_AND p L)`;

(*------------------*)  
(*    Unicode       *)
(*------------------*)

val S 	  =  U 0x1D47A;
val O	  =  U 0x1D476;
val R	  =  U 0x1D479;
val dash  =  U 0x0005F;
val A 	  =  U 0x1D468;
val N 	  =  U 0x1D475;
val D 	  =  U 0x1D46B;
val YES1  =  U 0x1D688;
val YES2  =  U 0x1D674;
val YES3  =  U 0x1D682;
val NO1   =  U 0x1D67D;
val NO2   =  U 0x1D67E;
val _ = Unicode.unicode_version {tmnm = "SUBSYSTEMS_OR", u = S^S^O^R^YES1^YES2^YES3};
val _ = Unicode.unicode_version {tmnm = "COMPL_SUBSYSTEMS_OR", u = S^S^O^R^NO1^NO2};
val _ = Unicode.unicode_version {tmnm = "SUBSYSTEMS_AND", u = S^S^A^N^D^YES1^YES2^YES3};
val _ = Unicode.unicode_version {tmnm = "COMPL_SUBSYSTEMS_AND", u = S^S^A^N^D^NO1^NO2};
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

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

val CONSEQ_PATH_EQ_ET_PATH = store_thm("CONSEQ_PATH_EQ_ET_PATH",
``!L p. prob_space p /\ (∀x'. MEM x' L ⇒ x' ∈ events p) ==>
        CONSEQ_PATH p L = PATH p L ``,

rw []
\\ Induct_on `L`
   >-( rw [PATH_DEF, CONSEQ_PATH_DEF])
\\ rw [PATH_DEF, CONSEQ_PATH_DEF]
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
   >-( rw [PATH_DEF, CONSEQ_PATH_DEF]
       \\ metis_tac [INTER_COMM , INTER_PSPACE])
\\ rw [PATH_DEF, CONSEQ_PATH_DEF]
\\ sg ` (∀x'. x' = h ∨ MEM x' L ⇒ x' ∈ events p)`
   >-( metis_tac [])
\\ sg `FOLDR (λa b. a ∩ b) h L = h ∩ PATH p L `
   >-( metis_tac [])
\\ fs []
\\ rw []
\\ rw [INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
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
  ``!p L2 L1. prob_space p /\ (!x. MEM x (L2++L1) ==> x IN events p ) /\ (~NULL L2) /\ (~NULL L1) /\
    MUTUAL_INDEP p (L2++L1) ==>
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
	     	 \\ rw [DIFF_DEF]
		 \\ rw [EXTENSION]
		 \\ metis_tac [])
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
	     	 \\ rw [DIFF_DEF]
		 \\ rw [EXTENSION]
		 \\ metis_tac [])
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

val CONSEQ_PATH_INTER_BOX_OF_CONSEQ_PATHS_EQ_ET_PATH_INTER_NODE_OF_PATHS =
store_thm("CONSEQ_PATH_INTER_BOX_OF_CONSEQ_PATHS_EQ_ET_PATH_INTER_NODE_OF_PATHS",
  ``!p L L1. prob_space p /\ (!x. MEM x (L1::L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L1::L))) ==> x IN events p)
            /\ MUTUAL_INDEP p (FLAT (L1::L)) ==>
    ((CONSEQ_PATH p L1) INTER (CONSEQ_BOX p L) =
    (PATH p L1) INTER (ETREE (NODE (EVENT_TREE_LIST ((MAP (\a. PATH p a)) L)))))``,
rw []
\\ Induct_on `L`
   >-( RW_TAC list_ss[CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF,
                      CONSEQ_BOX_DEF, INTER_EMPTY,PROB_EMPTY])
\\ RW_TAC list_ss[CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF,
                  CONSEQ_BOX_DEF, INTER_EMPTY,PROB_EMPTY]
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
\\ rw [UNION_OVER_INTER]
\\ rw []
\\ sg ` (∀x. x = L1 ∨ MEM x L ⇒ ~NULL x)`
   >-( metis_tac [])
\\ sg `(∀x. MEM x L1 ∨ MEM x (FLAT L) ⇒ x ∈ events p) `
    >-( metis_tac [])
\\ sg `MUTUAL_INDEP p (L1 ⧺ FLAT L) `
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ rw []
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ sg `CONSEQ_PATH p L1 ∩ CONSEQ_BOX p L =
        PATH p L1 ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))) `
   >-( metis_tac [])
\\ fs [CONSEQ_BOX_DEF]
\\ fs [EVENT_TREE_LIST_DEF]
\\ sg `CONSEQ_PATH p L1 = PATH p L1 `
  >-( DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
      \\ rw [])
\\ fs []);
(*--------------------------------------------------------------------------------------------------*)

val BOX_OF_CONSEQ_PATHS_EQ_ET_NODE_OF_PATHS =store_thm("BOX_OF_CONSEQ_PATHS_EQ_ET_NODE_OF_PATHS",
  ``!p L L1. prob_space p /\ (!x. MEM x (L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L))) ==> x IN events p)
            /\ MUTUAL_INDEP p (FLAT (L)) ==>
    (CONSEQ_BOX p L =  (ETREE (NODE (EVENT_TREE_LIST ((MAP (\a. PATH p a)) L)))))``,
rw []
\\ Induct_on `L`
   >-( RW_TAC list_ss[CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF,
                      CONSEQ_BOX_DEF, INTER_EMPTY,PROB_EMPTY])
\\ RW_TAC list_ss[CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF,
                  CONSEQ_BOX_DEF, INTER_EMPTY,PROB_EMPTY]
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
\\ rw [UNION_OVER_INTER]
\\ rw []
\\ sg ` (∀x.  MEM x L ⇒ ~NULL x)`
   >-( metis_tac [])
\\ sg `(∀x.  MEM x (FLAT L) ⇒ x ∈ events p) `
    >-( metis_tac [])
\\ sg `MUTUAL_INDEP p (FLAT L) `
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ rw [])
\\ sg `CONSEQ_BOX p L = ETREE (NODE (EVENT_TREE_LIST (MAP (λa. PATH p a) L))) `
   >-( metis_tac [])
\\ fs [CONSEQ_BOX_DEF]
\\ fs [EVENT_TREE_LIST_DEF]);
(*--------------------------------------------------------------------------------------------------*)

val MAP_CONSEQ_PATHS_EQ_MAP_ET_PATHS = store_thm("MAP_CONSEQ_PATHS_EQ_MAP_ET_PATHS",
  ``!p L L1. prob_space p /\ (!x. MEM x (L) ==> ~NULL x) /\ (!x. MEM x (FLAT ((L))) ==> x IN events p)
            /\ MUTUAL_INDEP p (FLAT (L)) ==>
    ((MAP (\a. CONSEQ_PATH p a)) L =  (MAP (\a. PATH p a)) L)``,
rw []
\\ Induct_on `L`
   >-( RW_TAC list_ss[CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF,
                      CONSEQ_BOX_DEF, INTER_EMPTY,PROB_EMPTY])
\\ RW_TAC list_ss[CONSEQ_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, PATH_DEF,
                  CONSEQ_BOX_DEF, INTER_EMPTY,PROB_EMPTY]
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
\\ rw [UNION_OVER_INTER]
\\ rw []
\\ sg ` (∀x. MEM x L ⇒ ~NULL x)`
   >-( metis_tac [])
\\ sg `(∀x. MEM x (FLAT L) ⇒ x ∈ events p) `
    >-( metis_tac [])
\\ sg `MUTUAL_INDEP p (FLAT L) `
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ rw [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val ET_PATH_INTER_NODE_OF_PATHS = store_thm("ET_PATH_INTER_NODE_OF_PATHS",
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

val PROB_ET_NODE_OF_PATHS = store_thm("PROB_ET_NODE_OF_PATHS",
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

val CONSEQ_PATH_INTER_BOX_OF_CONSEQ_PATHS = store_thm("CONSEQ_PATH_INTER_BOX_OF_CONSEQ_PATHS",
  ``!p L L1. prob_space p /\ (!x. MEM x (L1::L) ==> ~NULL x) /\
     (!x. MEM x (FLAT ((L1::L))) ==> x IN events p) /\ MUTUAL_INDEP p (FLAT (L1::L)) ==>
    (prob p ((CONSEQ_PATH p L1) INTER (CONSEQ_BOX p L))
     =  prob p (CONSEQ_PATH p L1) * prob p (CONSEQ_BOX p L))``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_INTER_BOX_OF_CONSEQ_PATHS_EQ_ET_PATH_INTER_NODE_OF_PATHS]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
\\ DEP_REWRITE_TAC [ET_PATH_INTER_NODE_OF_PATHS]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
\\ DEP_REWRITE_TAC [BOX_OF_CONSEQ_PATHS_EQ_ET_NODE_OF_PATHS]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val MAP_PROD_PROB_EQ_PROB_MAP_CONSEQ_PATHS = store_thm("MAP_PROD_PROB_EQ_PROB_MAP_CONSEQ_PATHS",
``!L p. prob_space p /\ (∀x'. MEM x' (FLAT L) ⇒ x' ∈ events p) /\ (!z. MEM z (L)  ==>  ~NULL z) /\
     ( MUTUAL_INDEP p (FLAT L)) ==>
     (MAP (λa. PROD_LIST (PROB_LIST p a)) L = PROB_LIST p (MAP (λa. CONSEQ_PATH p a) L))``,
rw []
\\ Induct_on`L`
   >-( rw [CONSEQ_PATH_DEF, PROB_LIST_DEF])
\\ rw [PROB_LIST_DEF]
   >-( DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
       \\ rw []
       \\ DEP_REWRITE_TAC [PROB_PATH]
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ fs []
\\ sg `MUTUAL_INDEP p (FLAT L) `
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ rw [])
\\ metis_tac []);       
(*--------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_BOX_OF_MAP_CONSEQ_PATHS = store_thm("PROB_CONSEQ_BOX_OF_MAP_CONSEQ_PATHS",
  ``!p L.  (!z. MEM z (L)  ==>  ~NULL z) /\ prob_space p /\
     disjoint (set (MAP (λa. CONSEQ_PATH p a) L)) /\ ALL_DISTINCT (MAP (λa. CONSEQ_PATH p a) L) /\
    (!x'. MEM x' (FLAT (L)) ==> (x' IN events p)) /\ ( MUTUAL_INDEP p (FLAT L)) ==>
    (prob p (CONSEQ_BOX p L) =
    SUM_LIST (PROB_LIST p (MAP (λa. CONSEQ_PATH p a) L)))``,
rw []
\\ DEP_REWRITE_TAC [BOX_OF_CONSEQ_PATHS_EQ_ET_NODE_OF_PATHS]
\\ rw []
\\ qpat_x_assum`disjoint (set (MAP (λa. CONSEQ_PATH p a) L))` mp_tac
\\ qpat_x_assum` ALL_DISTINCT (MAP (λa. CONSEQ_PATH p a) L)` mp_tac
\\ DEP_REWRITE_TAC[MAP_CONSEQ_PATHS_EQ_MAP_ET_PATHS]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_ET_NODE_OF_PATHS]
\\ rw []
\\ DEP_REWRITE_TAC [MAP_PROD_PROB_EQ_PROB_MAP_CONSEQ_PATHS]
\\ rw []
\\ metis_tac [MAP_CONSEQ_PATHS_EQ_MAP_ET_PATHS]);
(*--------------------------------------------------------------------------------------------------*)

val FT_AND_IN_EVENTS = store_thm("FT_AND_IN_EVENTS",
``!p L.  (∀x'. MEM x' L ==> x' ∈ events p) /\ prob_space p ==>
         (FTree p (AND (gate_list L)) ∈ events p)``,

GEN_TAC
\\ Induct
   >-( rw [gate_list_def, FTree_def]
       \\ rw [EVENTS_SPACE])
\\ rw [gate_list_def, FTree_def]
\\ sg `FTree p (AND (gate_list L)) ∈ events p`
   >-(metis_tac [])
\\ rw [EVENTS_INTER]);
(*--------------------------------------------------------------------------------------------------*)

val DIFF_INTER = store_thm("DIFF_INTER",
``!p s t. p_space p DIFF (s INTER t) = (p_space p DIFF s) UNION (p_space p DIFF t)``,
SRW_TAC [][EXTENSION,GSPECIFICATION]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val FT_NAND_IN_EVENTS = store_thm("FT_NAND_IN_EVENTS",
``!p L.  (∀x'. MEM x' L ==> x' ∈ events p) /\ prob_space p ==>
          (FTree p (NOT (AND (gate_list L))) ∈ events p)``,
GEN_TAC
\\ Induct
   >-( rw [gate_list_def, FTree_def]
       \\ rw [EVENTS_EMPTY])
\\ rw [gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ metis_tac [FT_AND_IN_EVENTS, EVENTS_COMPL, EVENTS_UNION]);
(*--------------------------------------------------------------------------------------------------*)

val FT_OR_IN_EVENTS  = store_thm("FT_OR_IN_EVENTS",
``!L p. (!x. MEM x L ==> x IN events p) /\ prob_space p ==>
  (FTree p (OR (gate_list L)) IN events p)``,
RW_TAC std_ss[]
\\ Induct_on `L`
   >-( RW_TAC list_ss[compl_list_def,gate_list_def,FTree_def,EVENTS_EMPTY])
\\ RW_TAC std_ss[gate_list_def,MAP, FTree_def]
\\ sg `(!x. MEM x L ==> x IN  events p)`
  >-(FULL_SIMP_TAC list_ss[])
\\ FULL_SIMP_TAC std_ss[]
\\ MATCH_MP_TAC EVENTS_UNION
\\ FULL_SIMP_TAC list_ss[]);
(*--------------------------------------------------------------------------------------------------*)

val FT_NOR_IN_EVENTS = store_thm("FT_NOR_IN_EVENTS",
``!p L.  (∀x'. MEM x' L ==> x' ∈ events p) /\ prob_space p ==>
          (FTree p (NOT (OR (gate_list L))) ∈ events p)``,
GEN_TAC
\\ Induct
   >-( rw [gate_list_def, FTree_def]
       \\ rw [EVENTS_SPACE])
\\ rw [gate_list_def, FTree_def]
\\ rw [OR_lem1]
\\ metis_tac [FT_OR_IN_EVENTS, EVENTS_COMPL, EVENTS_INTER]);
(*--------------------------------------------------------------------------------------------------*)

val OR_gate_eq_BIG_UNION = store_thm("OR_gate_eq_BIG_UNION",
  ``!p L. FTree p (OR (gate_list L)) =  BIG_UNION p L``,
GEN_TAC
\\ Induct
   >-(RW_TAC std_ss[gate_list_def,FTree_def,BIG_UNION_DEF])
\\ RW_TAC std_ss[gate_list_def,FTree_def,BIG_UNION_DEF]);
(*--------------------------------------------------------------------------------------------------*)

val BIG_UNION_IN_EVENTS = store_thm("BIG_UNION_IN_EVENTS",
``!L1 p. (prob_space p) /\ (!y. MEM y L1  ==> y IN events p)
         ==> (BIG_UNION p L1 ∈ events p) ``,
rw []
\\Induct_on `L1`
>-( rw [BIG_UNION_DEF]
    \\ rw [EVENTS_EMPTY])
\\ rw []
\\ rw [BIG_UNION_DEF]
\\ sg `BIG_UNION p L1 ∈ events p`
   >-(metis_tac [])
\\ rw [EVENTS_UNION]);
(*--------------------------------------------------------------------------------------------------*)

val PROB_P_SPACE_DIFF = store_thm("PROB_P_SPACE_DIFF",
``!X p. prob_space p /\ X ∈ events p ==>
        (prob p (p_space p DIFF (p_space p DIFF X)) = prob p X)``,
rw []
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
   >-( rw [EVENTS_COMPL])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val P_SPACE_DIFF = store_thm("P_SPACE_DIFF",
``!X p. prob_space p /\  X ∈ events p ==>
        p_space p DIFF (p_space p DIFF X) = X INTER p_space p ``,
rw [DIFF_DEF]
\\ rw [EXTENSION, GSPECIFICATION]
\\ EQ_TAC
   >-( rw [])
\\ rw []);  
(*--------------------------------------------------------------------------------------------------*)

val NODE_ET_EQ_OR_FT = store_thm("NODE_ET_EQ_OR_FT",
  ``!L p. FTree p (OR (gate_list L)) = ETREE (NODE (EVENT_TREE_LIST L))``,
Induct
>-(rw [ETREE_DEF, EVENT_TREE_LIST_DEF, FTree_def, gate_list_def])
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF, FTree_def, gate_list_def]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`p`])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)
				
val BRANCH_ET_EQ_AND_OR_FT = store_thm("BRANCH_ET_EQ_AND__OR_FT",
``!L X p. (prob_space p) /\ (!x'. MEM x' (X::L) ==> x' IN events p) ==>
          (FTree p (AND [atomic X; OR (gate_list L)]) = ETREE (BRANCH  X (NODE (EVENT_TREE_LIST L))))``,
Induct
>-(rw [ETREE_DEF, EVENT_TREE_LIST_DEF, FTree_def, gate_list_def])
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF, FTree_def, gate_list_def]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [INTER_ASSOC]
\\ first_x_assum (mp_tac o Q.SPECL [`X`, `p`])
\\ rw [FTree_def]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ sg ` ETREE (BRANCH X (NODE (EVENT_TREE_LIST L))) =
        X ∩ (FTree p (OR (gate_list L)) ∩ p_space p)` 
   >-(metis_tac [])
\\ fs []
\\ rw []
\\ rw [INTER_ASSOC]
\\ sg `FTree p (OR (gate_list L)) IN events p `
   >-( POP_ORW
       \\ Induct_on `L`
          >-( rw [FTree_def, gate_list_def]
              \\ rw [EVENTS_EMPTY])
       \\ rw [FTree_def, gate_list_def]
       \\ sg `FTree p (OR (gate_list L)) ∈ events p`
       	  >-(metis_tac [])
       \\ fs []
       \\ rw []
       \\ metis_tac [EVENTS_UNION])
\\ rw [INTER_COMM]
\\ DEP_REWRITE_TAC [INTER_PSPACE]
\\ fs []
\\ rw []
   >-(metis_tac [EVENTS_INTER, EVENTS_UNION])
\\ metis_tac [NODE_ET_EQ_OR_FT]);
(*--------------------------------------------------------------------------------------------------*)

val PROB_NAND = store_thm("PROB_NAND",
``!p L . ~NULL L  /\ (!x'. MEM x' L ==> x' IN events p) /\
         prob_space p  /\ MUTUAL_INDEP p L
         ==> (prob p (NAND p L) = 1 - PROD_LIST (PROB_LIST p L))``,
rw [NAND_DEF, FTree_def]
\\ DEP_REWRITE_TAC[PROB_COMPL]
\\ rw []
   >-(rw [FT_AND_IN_EVENTS])
\\ DEP_REWRITE_TAC [AND_gate_thm]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val DIFF_AND_EQ_OR_COMPL = store_thm("DIFF_AND_EQ_OR_COMPL",
``!p L. prob_space p /\ (!y. MEM y L ==> y IN events p) ==>   
        p_space p DIFF PATH p L = BIG_UNION p (compl_list p L)``,
GEN_TAC
\\ Induct
   >-( rw [BIG_UNION_DEF, PATH_DEF, compl_list_def])
\\ rw [BIG_UNION_DEF, PATH_DEF, compl_list_def]
\\ rw [GSYM  compl_list_def]
\\ fs []
\\ rw [DIFF_INTER]);
(*--------------------------------------------------------------------------------------------------*)

val COMPL_LIST_SPLIT = store_thm("COMPL_LIST_SPLIT",
``!p L1 L2.  compl_list p (L1 ++ L2) = compl_list p L1 ⧺ compl_list p L2 ``,
GEN_TAC
\\ Induct
   >-( rw [compl_list_def])
\\ rw [compl_list_def]);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    AND INTER NOR     *)
(*----------------------*)

val AND_INTER_NOR = store_thm("AND_INTER_NOR",
``!p L1 L2. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p)  /\
	    (MUTUAL_INDEP p (compl_list p L1 ++ L2)) /\ ~NULL L2
           ==> (prob p (PATH p L2 ∩ (NOR p L1)) =
	        prob p (PATH p L2) * PROD_LIST (PROB_LIST p (compl_list p L1)))``,

GEN_TAC
\\ GEN_TAC
\\ once_rewrite_tac [NOR_DEF]
\\ once_rewrite_tac [FTree_def]
\\ once_rewrite_tac [OR_gate_eq_BIG_UNION]
\\ Induct_on`L1`
>-( rw [BIG_UNION_DEF, SUM_LIST_DEF, PROB_LIST_DEF]
    \\ sg ` PATH p L2 ∩ p_space p = PATH p L2 `
       >-( metis_tac [PATH_IN_EVENTS, EVENTS_INTER, INTER_COMM, INTER_PSPACE])
    \\ fs []
    \\ rw [compl_list_def]
    \\ rw [PROB_LIST_DEF, PROD_LIST_DEF])
\\ rw [BIG_UNION_DEF]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ rw [SUM_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p L2 ∩ (p_space p DIFF h) = PATH p ((p_space p DIFF h)::L2) `
   >-( rw  [PATH_DEF]
       \\ metis_tac [INTER_COMM])
\\ fs []
\\ first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L2)`])
\\ rw []
\\ sg `MUTUAL_INDEP p (compl_list p L1 ⧺ p_space p DIFF h::L2) `
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]	
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ sg `(∀y. MEM y L1 ∨ y = p_space p DIFF h ∨ MEM y L2 ⇒ y ∈ events p) `
   >-( metis_tac [EVENTS_COMPL])
\\ sg `prob p
          (PATH p (p_space p DIFF h::L2) ∩
           (p_space p DIFF BIG_UNION p L1)) =
        prob p (PATH p (p_space p DIFF h::L2)) *
        PROD_LIST (PROB_LIST p (compl_list p L1))`
   >-( metis_tac [])
\\ fs []
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
    >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (h::L1)`
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [compl_list_def]
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*---------------------*)  
(*    NAND INTER NOR   *)
(*---------------------*)

val NAND_INTER_NOR = store_thm("NAND_INTER_NOR",
``!p L1 L2. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p)  /\
           (MUTUAL_INDEP p (compl_list p (L1 ⧺ L2)))  ==> 
      prob p (NAND p L1 ∩ NOR p L2) =
      prob p (NAND p L1) * PROD_LIST (PROB_LIST p (compl_list p L2))``,
GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ sg `p_space p DIFF FTree p (AND (gate_list L1)) = NAND p L1 `
   >-(  rw [FTree_def, NAND_DEF])
\\ POP_ORW
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [NOR_DEF, FTree_def]
\\ rw [OR_gate_eq_BIG_UNION]
\\ sg `(p_space p DIFF BIG_UNION p L2) ∩ (p_space p DIFF h) =
       (p_space p DIFF h) ∩ (p_space p DIFF BIG_UNION p L2)`
   >-( rw [INTER_COMM])
\\ fs []
\\ POP_ORW
\\ rw [GSYM OR_lem1]
\\ rw [GSYM BIG_UNION_DEF]
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NOR_DEF]
\\ sg `NOR p (h::L2)  IN events p `
   >-( rw [NOR_DEF, gate_list_def, FTree_def]
       \\ rw [OR_lem1]
       \\ metis_tac [EVENTS_INTER, EVENTS_COMPL, OR_lem3, EVENTS_INTER, EVENTS_UNION])
\\ rw [INTER_COMM]
\\ sg `NAND p L1 ∩ NOR p L2 IN events p `
   >-( metis_tac [NAND_DEF, NOR_DEF, FT_NAND_IN_EVENTS, FT_NOR_IN_EVENTS, EVENTS_INTER])
\\ rw [FTree_def]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS])
\\ sg `prob p (NAND p L1 ∩ NOR p L2) = prob p (NAND p L1) * PROD_LIST (PROB_LIST p (compl_list p L2))`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
       	  >-( metis_tac [])
  	  >-( metis_tac [])
       \\ fs [COMPL_LIST_SPLIT]	  
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h ]`
       \\ rw [])
\\ POP_ORW
\\ sg `prob p ((p_space p DIFF h) ∩ NAND p L1) = prob p (p_space p DIFF h) * prob p (NAND p L1)`
   >-( sg `(p_space p DIFF h) ∩ NAND p L1 = NAND p L1 ∩ NOR p [h]`
          >-( rw [NOR_DEF, INTER_COMM, FTree_def, gate_list_def])
       \\ fs []
       \\ first_x_assum (mp_tac o Q.SPECL [`[h]`])
       \\ rw []
       \\ sg `(∀y. MEM y L1 ∨ y = h ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (compl_list p (L1 ⧺ [h]))`
          >-( fs [COMPL_LIST_SPLIT]	  
       	      \\ fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
       	      \\ irule MUTUAL_INDEP_append_sym
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `compl_list p L2`
	      \\ irule MUTUAL_INDEP_append_sym
	      \\ rw [])
       \\ sg `prob p (NAND p L1 ∩ NOR p [h]) =
              prob p (NAND p L1) * PROD_LIST (PROB_LIST p (compl_list p [h]))`
          >-( metis_tac [])
       \\ fs []
       \\ rw  [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ sg `NOR p (h::L2) ∩ (NAND p L1 ∩ NOR p L2) = NOR p (h::L2) ∩ NAND p L1`
   >-( rw  [NOR_DEF, FTree_def, gate_list_def]
       \\ rw  [OR_lem1]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ fs []
\\ rw [INTER_COMM]
\\ sg `prob p (NAND p L1 ∩ NOR p (h::L2)) = prob p (NAND p L1) *
      	      	                            PROD_LIST (PROB_LIST p (compl_list p (h::L2))) `
   >-( first_x_assum (mp_tac o Q.SPECL [`(h::L2)`])
       \\ rw []
       \\ sg `(∀y. MEM y L1 ∨ y = h ∨ MEM y L2 ⇒ y ∈ events p)  `
       	  >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (compl_list p (L1 ⧺ h::L2))`
       	  >-( fs [COMPL_LIST_SPLIT]	  
       	      \\ fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
       	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       	      \\ once_rewrite_tac [APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [NOR_DEF, FTree_def, gate_list_def]
\\ rw [GSYM compl_list_def]
\\ rw [OR_lem1]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NOR_DEF]
\\ rw [FTree_def]
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF]
       \\ metis_tac [EVENTS_COMPL, EVENTS_INTER, INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [COMPL_LIST_SPLIT]	  
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])  
   >-( fs [COMPL_LIST_SPLIT]	  
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]	     
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym 
       \\ rw [])
\\ rw [PROB_LIST_DEF, compl_list_def, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ REAL_ARITH_TAC); 
(*--------------------------------------------------------------------------------------------------*)

val PROB_NOR = store_thm("PROB_NOR",
``!p L . (!x'. MEM x' L ==> x' IN events p) /\ prob_space p  /\ MUTUAL_INDEP p (compl_list p L)
         ==> (prob p (NOR p L) = PROD_LIST (PROB_LIST p (compl_list p L)))``,

GEN_TAC
\\ Induct
   >-(  rw [NOR_DEF, FTree_def, gate_list_def, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
   	\\  rw [PROB_UNIV])
\\ rw [NOR_DEF, FTree_def, gate_list_def, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [OR_lem1]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NOR_DEF]
\\ rw [FTree_def]
\\ rw [GSYM compl_list_def]
\\ sg ` (p_space p DIFF h) = PATH p [p_space p DIFF h]`
   >-( rw [PATH_DEF]
       \\ rw [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [EVENTS_COMPL])
\\ fs [GSYM compl_list_def]
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------*)  
(*    AND INTER NAND     *)
(*-----------------------*)

val AND_INTER_NAND = store_thm("AND_INTER_NAND",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p)  /\
           (MUTUAL_INDEP p (L1 ++ compl_list p L2)) /\ ~NULL L1
          ==> (prob p (PATH p L1 ∩ NAND p L2) =
	       prob p (PATH p L1) * prob p (NAND p L2))``,
GEN_TAC
\\ GEN_TAC
\\ once_rewrite_tac [NAND_DEF]
\\ once_rewrite_tac [FTree_def]
\\ once_rewrite_tac [AND_gate_eq_PATH]
\\ Induct_on`L2`
   >-( RW_TAC list_ss[PATH_DEF, INTER_EMPTY,PROB_EMPTY]
       \\ rw [DIFF_EQ_EMPTY]
       \\ rw [PROB_EMPTY])
\\ RW_TAC std_ss[PATH_DEF]
\\ rw [DIFF_INTER]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p L1 ∩ (p_space p DIFF h) IN events p `
   >-( rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg ` PATH p L1 ∩ (p_space p DIFF PATH p L2)IN events p `
   >-( rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL, PATH_IN_EVENTS])
\\ rw []
\\ sg `PATH p L1 ∩ (p_space p DIFF h) = PATH p ((p_space p DIFF h)::L1) `
   >-( rw  [PATH_DEF]
       \\ metis_tac [INTER_COMM])
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( rw [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 = L1 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])       
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (h::L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ RW_TAC std_ss[PATH_DEF]
\\ sg `(p_space p DIFF h) ∩ PATH p L1 ∩
           (PATH p L1 ∩ (p_space p DIFF PATH p L2)) =
       PATH p ((p_space p DIFF h)::L1) ∩ (p_space p DIFF PATH p L2)`	   
    >-( rw [PATH_DEF]
        \\ rw [EXTENSION]
        \\ metis_tac [])   
\\ fs [INTER_ASSOC]
\\ POP_ORW
\\ sg `prob p (PATH p (p_space p DIFF h::L1) ∩
               (p_space p DIFF PATH p L2)) =  
       prob p (PATH p (p_space p DIFF h::L1)) *  
       prob p (p_space p DIFF PATH p L2)`
   >-( first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L1)`])
       \\ rw []
       \\ sg `(∀y. (y = p_space p DIFF h ∨ MEM y L1) ∨ MEM y L2 ⇒ y ∈ events p) `
       	  >-( RW_TAC list_ss  [EVENTS_COMPL]
	      \\ rw [EVENTS_COMPL])
       \\ sg `MUTUAL_INDEP p (p_space p DIFF h::(L1 ⧺ compl_list p L2)) `
          >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 = L1 ⧺ p_space p DIFF h::compl_list p L2 `
              	 >-( rw [APPEND])
               \\ rw [])       
       \\ metis_tac [])
\\ rw []
\\ sg `(p_space p DIFF h) ∩ (p_space p DIFF PATH p L2) =
        PATH p [(p_space p DIFF h)] ∩ (p_space p DIFF PATH p L2)`
   >-( rw  [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])   
\\ rw []
\\ sg `prob p (PATH p [p_space p DIFF h] ∩
               (p_space p DIFF PATH p L2)) =  
       prob p (p_space p DIFF h) *  
       prob p (p_space p DIFF PATH p L2)`
   >-( first_x_assum (mp_tac o Q.SPECL [`[p_space p DIFF h]`])
       \\ rw []
       \\ sg `(∀y. y = p_space p DIFF h ∨ MEM y L2 ⇒ y ∈ events p) `
       	  >-( RW_TAC list_ss  [EVENTS_COMPL]
	      \\ rw [EVENTS_COMPL])
       \\ sg `MUTUAL_INDEP p (p_space p DIFF h:: compl_list p L2) `
          >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `L1`
	      \\ rw [])      
       \\ sg `(p_space p DIFF h) = PATH p [(p_space p DIFF h)]`
       	  >-( rw  [PATH_DEF]
       	      \\ rw [EXTENSION]
       	      \\ metis_tac [])   
       \\ metis_tac [])
\\ rw []       
\\ sg `prob p (PATH p L1 ∩ (p_space p DIFF PATH p L2)) =
       prob p (PATH p L1) * prob p (p_space p DIFF PATH p L2)`
   >-( ntac 6 POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
          >-( rw [])
	  >-( rw [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
       	      L1 ⧺ p_space p DIFF h::compl_list p L2`
          >-( rw [APPEND])
       \\ rw [])
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC ` compl_list p (h::L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 = L1 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])       
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    AND INTER AND     *)
(*----------------------*)

val AND_INTER_AND = store_thm("AND_INTER_AND",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p)  /\
           (MUTUAL_INDEP p (L1 ++ L2)) /\ ~NULL L1 /\ ~NULL L2
          ==> (prob p (PATH p L1 ∩  (PATH p L2)) =
	       prob p (PATH p L1) * prob p (PATH p L2))``,

rw []
\\ DEP_REWRITE_TAC [PATH_APPEND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_APPEND] 
\\ rw []
   >-( metis_tac [])
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    AND INTER OR      *)
(*----------------------*)

val AND_INTER_OR = store_thm("AND_INTER_OR",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2)) /\ ~NULL L1
            ==> (prob p (PATH p L1 ∩ BIG_UNION p L2) =
       	         prob p (PATH p L1) * prob p (BIG_UNION p L2))``,

GEN_TAC
\\ Induct
>-( rw [BIG_UNION_DEF]
    \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p L1 ∩ h IN events p `
   >-( metis_tac [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 IN events p `
   >-( metis_tac [BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ sg `h ∩ BIG_UNION p L2 =  PATH p [h] ∩ BIG_UNION p L2`
   >-( metis_tac [PATH_DEF, INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `prob p (PATH p [h] ∩ BIG_UNION p L2) =
       prob p (PATH p [h]) * prob p (BIG_UNION p L2)  `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1`
	\\ rw [])    
\\ POP_ORW
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-(metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `prob p (PATH p L1 ∩ BIG_UNION p L2) =
       prob p (PATH p L1) * prob p (BIG_UNION p L2)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ sg `L1 ⧺ [h] ⧺ L2 = L1 ⧺ h::L2 `
	   >-( rw [APPEND])
	\\ rw [])   
\\ POP_ORW
\\ sg  `PATH p L1 ∩ h ∩ (PATH p L1 ∩ BIG_UNION p L2) =
        (h INTER PATH p L1)  ∩  BIG_UNION p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [GSYM PATH_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`(h::L1)`])
\\ rw []
\\ sg `(∀y. (y = h ∨ MEM y L1) ∨ MEM y L2 ⇒ y ∈ events p)  `
   >-(metis_tac [])
\\ sg `MUTUAL_INDEP p (h::(L1 ⧺ L2)) `
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ sg `L1 ⧺ [h] ⧺ L2 = L1 ⧺ h::L2 `
	   >-( rw [APPEND])
	\\ rw [])  
\\ sg `prob p (PATH p (h::L1) ∩ BIG_UNION p L2) =
        prob p (PATH p (h::L1)) * prob p (BIG_UNION p L2) `
   >-(metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `(h::L2)`
	\\ irule MUTUAL_INDEP_append_sym
        \\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2`
	\\ irule MUTUAL_INDEP_append_sym
	\\ sg `L1 ⧺ [h] ⧺ L2 = L1 ⧺ h::L2 `
	   >-( rw [APPEND])
	\\ rw [])  
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ rw [INTER_COMM]
\\ rw [GSYM PATH_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2`
	\\ irule MUTUAL_INDEP_append_sym
	\\ sg `L1 ⧺ [h] ⧺ L2 = L1 ⧺ h::L2 `
	   >-( rw [APPEND])
	\\ rw [])  
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------*)  
(*    AND INTER OR INTER OR     *)
(*------------------------------*)

val AND_INTER_OR_INTER_OR = store_thm("AND_INTER_OR_INTER_OR",
``!p L3 L1 L2. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2 ++ L3)) /\ ~NULL L1
            ==> (prob p (PATH p L1 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3 ) =
       	         prob p (PATH p L1) * prob p (BIG_UNION p L2) * prob p (BIG_UNION p L3))``,

GEN_TAC
\\ Induct
>-( rw [BIG_UNION_DEF]
    \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p L1 ∩  BIG_UNION p L2 ∩ h IN events p `
   >-( metis_tac [PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3 IN events p `
   >-( metis_tac [BIG_UNION_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ sg `h ∩ BIG_UNION p L3 =  PATH p [h] ∩ BIG_UNION p L3`
   >-( metis_tac [PATH_DEF, INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `prob p (PATH p [h] ∩ BIG_UNION p L3) =
       prob p (PATH p [h]) * prob p (BIG_UNION p L3)  `
   >-( DEP_REWRITE_TAC [AND_INTER_OR]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ++ L2`
	\\ rw [])    
\\ POP_ORW
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-(metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `PATH p L1 ∩ BIG_UNION p L2 ∩ h = (h ∩ PATH p L1) ∩ BIG_UNION p L2 `
   >-( metis_tac [INTER_COMM, INTER_ASSOC])
\\ POP_ORW
\\ rw [GSYM PATH_DEF]
\\ DEP_REWRITE_TAC [AND_INTER_OR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 = L1 ⧺ L2 ⧺ h::L3 `
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 = L1 ⧺ L2 ⧺ h::L3 `
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])  
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `prob p (PATH p L1 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3) =
       prob p (PATH p L1) * prob p (BIG_UNION p L2) * prob p (BIG_UNION p L3)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
        \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 = L1 ⧺ L2 ⧺ h::L3 `
          >-( rw [APPEND])
        \\ rw [])
\\ POP_ORW
\\ sg `prob p (PATH p (h::L1) ∩ BIG_UNION p L2 ∩ BIG_UNION p L3) =
       prob p (PATH p (h::L1)) * prob p (BIG_UNION p L2) * prob p (BIG_UNION p L3)`
   >-( first_x_assum (mp_tac o Q.SPECL [`(h::L1)`, `L2`])
       \\ rw []
       \\ sg `(∀y. ((y = h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3 ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (h::(L1 ⧺ L2 ⧺ L3)) `
          >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
              \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 = L1 ⧺ L2 ⧺ h::L3 `
              	 >-( rw [APPEND])
               \\ rw [])
       \\ metis_tac [])
\\ sg `PATH p (h::L1) ∩ BIG_UNION p L2 ∩
           (PATH p L1 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3) =
       PATH p (h::L1) ∩ BIG_UNION p L2 ∩ BIG_UNION p L3` 
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ ntac 2 POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND
        \\ Q.EXISTS_TAC `L2 ⧺ h::L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
        \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 = L1 ⧺ L2 ⧺ h::L3 `
           >-( rw [APPEND])
         \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    OR INTER OR       *)
(*----------------------*)

val OR_INTER_OR = store_thm("OR_INTER_OR",
``!p L1 L2. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2)) 
            ==> (prob p (BIG_UNION p L1 ∩ BIG_UNION p L2) =
       	         prob p (BIG_UNION p L1) * prob p (BIG_UNION p L2))``,
GEN_TAC
\\ Induct
>-( rw [BIG_UNION_DEF]
    \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ sg `BIG_UNION p L2 ∩ h IN events p `
   >-( metis_tac [BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ sg `BIG_UNION p L2 ∩ BIG_UNION p L1 IN events p `
   >-( metis_tac [BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ sg `h ∩ BIG_UNION p L1 = BIG_UNION p L1 ∩ BIG_UNION p [h] `
   >-( rw [BIG_UNION_DEF, INTER_COMM])
\\ POP_ORW
\\ sg `prob p (BIG_UNION p L1 ∩ BIG_UNION p [h]) =
       prob p (BIG_UNION p L1) * prob p (BIG_UNION p [h]) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
   	\\ irule MUTUAL_INDEP_append_sym
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2`
      	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])    
\\ POP_ORW
\\ rw [BIG_UNION_DEF]
\\ sg `prob p (BIG_UNION p L1 ∩ BIG_UNION p L2) =
       prob p (BIG_UNION p L1) * prob p (BIG_UNION p L2)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ rw [])   
\\ POP_ORW
\\ sg `BIG_UNION p L2 ∩ h ∩  (BIG_UNION p L2 ∩ BIG_UNION p L1) =
       BIG_UNION p L1  ∩  (h ∩ BIG_UNION p L2)`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `BIG_UNION p L2 ∩ h = PATH p [h] INTER BIG_UNION p L2 `
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_ASSOC, INTER_COMM, INTER_PSPACE, BIG_UNION_IN_EVENTS])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ sg `L1 ⧺ [h] ⧺ L2 = L1 ⧺ h::L2 `
	   >-( rw [APPEND])
	\\ rw []) 
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-(metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ rw [INTER_COMM]
\\ sg `prob p (BIG_UNION p L1 ∩ BIG_UNION p L2) =
       prob p (BIG_UNION p L1) * prob p (BIG_UNION p L2) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ rw [])
\\ POP_ORW
\\ sg `BIG_UNION p L1 ∩ (h ∩ BIG_UNION p L2) =
       PATH p [h]  ∩ BIG_UNION p L1 ∩ BIG_UNION p L2`
  >-( rw [PATH_DEF]
      \\ metis_tac [INTER_COMM, INTER_ASSOC, BIG_UNION_IN_EVENTS, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_OR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac []) 
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND
        \\ Q.EXISTS_TAC `L1 ++ L2`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*    AND INTER NAND INTER NAND   *)
(*--------------------------------*)

val AND_INTER_NAND_INTER_NAND = store_thm("AND_INTER_NAND_INTER_NAND",
``∀p L2 L3 L1.
         prob_space p ∧ (∀y. MEM y (L1 ⧺ L3 ++ L2) ⇒ y ∈ events p) ∧
         MUTUAL_INDEP p (L1 ⧺ compl_list p (L3 ++ L2)) ∧ ~NULL L1 ⇒
         prob p (PATH p L1 ∩ NAND p L3 ∩ NAND p L2) =
         prob p (PATH p L1) * prob p (NAND p L3) * prob p (NAND p L2)``,

GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ once_rewrite_tac [NAND_DEF]
\\ once_rewrite_tac [FTree_def]
\\ once_rewrite_tac [AND_gate_eq_PATH]
\\ Induct_on`L2`
   >-( RW_TAC list_ss[PATH_DEF, INTER_EMPTY,PROB_EMPTY]
       \\ rw [DIFF_EQ_EMPTY]
       \\ rw [PROB_EMPTY])
\\ RW_TAC std_ss[PATH_DEF]
\\ rw [DIFF_INTER]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p L1 ∩ (p_space p DIFF PATH p L3) ∩ (p_space p DIFF h) IN events p `
   >-( sg `PATH p L1 ∩ (p_space p DIFF PATH p L3) IN events p `
       >-(rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
       \\ rw [EVENTS_INTER, EVENTS_COMPL])
\\ sg ` PATH p L1 ∩ (p_space p DIFF PATH p L3) ∩ (p_space p DIFF PATH p L2) IN events p `
   >-( sg `PATH p L1 ∩ (p_space p DIFF PATH p L3) IN events p `
       >-(rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
       \\ rw [PATH_IN_EVENTS,EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL, PATH_IN_EVENTS])
\\ rw []
\\ sg `PATH p L1 ∩ (p_space p DIFF PATH p L3) ∩ (p_space p DIFF h)
       = PATH p ((p_space p DIFF h)::L1) ∩ (NAND p L3) `
   >-( rw  [PATH_DEF, NAND_DEF, FTree_def, AND_gate_eq_PATH]
       \\ metis_tac [INTER_COMM, INTER_ASSOC])
\\ rw []
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1  ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              L1  ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              L1 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])       
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ h::L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `p_space p DIFF PATH p L2 = NAND p L2 `
   >-( rw [NAND_DEF, AND_gate_eq_PATH, FTree_def])
\\ POP_ORW
\\ sg `p_space p DIFF PATH p L3 = NAND p L3 `
   >-( rw [NAND_DEF, AND_gate_eq_PATH, FTree_def])
\\ POP_ORW
\\ sg `(p_space p DIFF h) ∩ NAND p L2 = PATH p [p_space p DIFF h] ∩ NAND p L2  `
   >-( rw  [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])   
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1 ⧺ compl_list p L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1 ⧺ compl_list p L3`
       \\ rw [])       
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `prob p (PATH p L1 ∩ NAND p L3 ∩ NAND p L2) =
       prob p (PATH p L1) * prob p (NAND p L3) * prob p (NAND p L2)`
   >-( fs [GSYM AND_gate_eq_PATH]
       \\ fs [GSYM FTree_def]
       \\ fs [GSYM NAND_DEF]
       \\ ntac 3 POP_ORW
       \\ fs [AND_gate_eq_PATH]
       \\ first_x_assum (match_mp_tac)
       \\ rw []
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
       	      L1 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L2`
          >-( rw [APPEND])
       \\ rw [])
\\ ntac 4 POP_ORW
\\ sg `PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩
           (PATH p L1 ∩ NAND p L3 ∩ NAND p L2) =
       PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ NAND p L2`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [NAND_DEF] 
\\ rw [FTree_def]
\\ rw [AND_gate_eq_PATH]
\\ first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L1)`])
\\ rw []
\\ sg `(∀y. ((y = p_space p DIFF h ∨ MEM y L1) ∨ MEM y L3) ∨ MEM y L2 ⇒  y ∈ events p)`
   >-( RW_TAC list_ss  [EVENTS_COMPL]
        \\ rw [EVENTS_COMPL])
\\ sg `MUTUAL_INDEP p (p_space p DIFF h::(L1 ⧺ compl_list p (L3 ⧺ L2)))`
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1  ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              L1  ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p
          (PATH p (p_space p DIFF h::L1) ∩
           (p_space p DIFF PATH p L3) ∩ (p_space p DIFF PATH p L2)) =
        prob p (PATH p (p_space p DIFF h::L1)) *
        prob p (p_space p DIFF PATH p L3) *
        prob p (p_space p DIFF PATH p L2)`
   >-( metis_tac [])   
\\ ntac 4 POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ h::L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1       
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1  ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              L1  ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])       
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    NAND INTER NAND   *)
(*----------------------*)

val NAND_INTER_NAND = store_thm("NAND_INTER_NAND",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p)  /\
           (MUTUAL_INDEP p (compl_list p (L1 ++ L2))) 
          ==> (prob p (NAND p L1 ∩ NAND p L2) =
	       prob p (NAND p L1) * prob p (NAND p L2))``,
GEN_TAC
\\ Induct
   >-( RW_TAC list_ss[NAND_DEF, FTree_def, gate_list_def, INTER_EMPTY,PROB_EMPTY]
       \\ rw [DIFF_EQ_EMPTY]
       \\ rw [PROB_EMPTY])
\\ RW_TAC std_ss[NAND_DEF, FTree_def, gate_list_def]
\\ rw [DIFF_INTER]
\\ rw [UNION_OVER_INTER]
\\ rw [AND_gate_eq_PATH]
\\ sg `(p_space p DIFF PATH p L1) ∩ (p_space p DIFF h) IN events p `
   >-( rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg ` (p_space p DIFF PATH p L1) ∩ (p_space p DIFF PATH p L2)IN events p `
   >-( rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL, PATH_IN_EVENTS])
\\ rw [INTER_COMM]
\\ sg `(p_space p DIFF h) ∩ (p_space p DIFF PATH p L1) ∩
           ((p_space p DIFF PATH p L1) ∩
            (p_space p DIFF PATH p L2)) =

       (p_space p DIFF h) ∩ (p_space p DIFF PATH p L1) ∩
            (p_space p DIFF PATH p L2)`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ rw []
\\ POP_ORW
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h]`
   >-( metis_tac  [PATH_DEF, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ sg `(p_space p DIFF h) ∩ (p_space p DIFF PATH p L1) =
       PATH p [p_space p DIFF h] ∩ (p_space p DIFF PATH p L1)`
   >-(metis_tac [])
\\ fs []
\\ POP_ORW
\\ sg `p_space p DIFF PATH p L1 = NAND p L1 `
   >-( rw [NAND_DEF, AND_gate_eq_PATH, FTree_def])
\\ POP_ORW
\\ sg `p_space p DIFF PATH p L2 = NAND p L2 `
   >-( rw [NAND_DEF, AND_gate_eq_PATH, FTree_def])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\  once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])       
\\ rw [PATH_DEF]
\\ sg `(p_space p DIFF h) ∩ p_space p = (p_space p DIFF h)`
   >-( metis_tac  [EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ fs []
\\ sg `prob p ((p_space p DIFF h) ∩ (NAND p L2)) =
       prob p (p_space p DIFF h) * prob p (NAND p L2)`
   >-( sg `(p_space p DIFF h) =  NAND p [h]`
       >-( rw [NAND_DEF, FTree_def, gate_list_def, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (mp_tac o Q.SPECL [`[h]`])
       \\ rw []
       \\ sg `(∀y. y = h ∨ MEM y L2 ⇒ y ∈ events p) `
          >-(metis_tac [])
       \\ sg ` MUTUAL_INDEP p (compl_list p (h::L2)) `
          >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]  
       	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `compl_list p L1 `
       	      \\ once_rewrite_tac [APPEND_ASSOC]
       	      \\ rw [])
       \\ sg `prob p (NAND p [h] ∩ NAND p L2) =
        prob p (NAND p [h]) * prob p (NAND p L2)`
          >-(metis_tac []))
\\ POP_ORW
\\ sg `prob p (NAND p L1 ∩ NAND p L2) = prob p (NAND p L1) * prob p (NAND p L2)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
       	  >-( metis_tac [])   
   	  >-( metis_tac [])   
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 `
	  >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ sg `prob p ((p_space p DIFF h) ∩ NAND p L1 ∩ NAND p L2) =
       prob p (PATH p [p_space p DIFF h] ∩  (NAND p L1) ∩ (NAND p L2))`
   >-( rw [PATH_DEF])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\  once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1       
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 `
          >-( rw [APPEND])
       \\ rw [])       
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw [])      
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)


(*--------------------------------*)  
(*    AND INTER OR INTER NAND     *)
(*--------------------------------*)

val AND_INTER_OR_INTER_NAND = store_thm("AND_INTER_OR_INTER_NAND",
``!p L3 L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2 ++ compl_list p L3)) /\ ~NULL L1
            ==> (prob p (PATH p L1 ∩ BIG_UNION p L2 ∩ NAND p L3) =
       	         prob p (PATH p L1) * prob p (BIG_UNION p L2) * prob p (NAND p L3))``,

GEN_TAC
\\ GEN_TAC
\\ Induct
>-( rw [BIG_UNION_DEF]
    \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ sg `NAND p L3 ∩ PATH p L1 ∩ h IN events p `
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ sg `NAND p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 IN events p `
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER])       
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg `h ∩ NAND p L3 ∩ PATH p L1 =  PATH p (h::L1) ∩ NAND p L3`
   >-( metis_tac [PATH_DEF, INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1       
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2`
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ [h] ⧺ L2 ⧺ compl_list p L3 =
              L1 ⧺ h::L2 ⧺ compl_list p L3`
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1 ⧺ [h] ⧺ L2 ⧺ compl_list p L3 =
              L1 ⧺ h::L2 ⧺ compl_list p L3`
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h::L2 ⧺ compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])     
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg ` prob p (PATH p L1 ∩ BIG_UNION p L2 ∩ NAND p L3) =
         prob p (BIG_UNION p L2) * prob p (PATH p L1) * prob p (NAND p L3) `
   >-( sg `BIG_UNION p L2 ∩ PATH p L1 ∩ NAND p L3 =
           PATH p L1 ∩ BIG_UNION p L2 ∩ NAND p L3`
       >-( rw [EXTENSION]
       	   \\ metis_tac [])
       \\ POP_ORW
       \\ sg `prob p (BIG_UNION p L2) * prob p (PATH p L1) *
              prob p (NAND p L3) = prob p (PATH p L1) * prob p (BIG_UNION p L2) *
              prob p (NAND p L3) `
	  >-( REAL_ARITH_TAC)
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
       	  >-( metis_tac [])   
   	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ once_rewrite_tac [GSYM APPEND_ASSOC]	  
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `L1 ⧺ [h] ⧺ L2 ++ compl_list p L3 =
              L1 ⧺ h::L2 ++ compl_list p L3 `
	  >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ sg `h ∩ BIG_UNION p L2 =  PATH p [h] ∩ BIG_UNION p L2`
   >-( metis_tac [PATH_DEF, INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR]
\\ rw []
   >-( metis_tac [])   
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC ` h::L2 ⧺ compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ sg `L1 ⧺ [h] ⧺ L2 ++ compl_list p L3 =
              L1 ⧺ h::L2 ++ compl_list p L3 `
	  >-( rw [APPEND])
       \\ rw [])       
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p L1 ∩ NAND p L3 ∩ BIG_UNION p L2 ∩ NAND p L3 ∩
           PATH p (h::L1) =
       PATH p (h::L1) ∩  BIG_UNION p L2 ∩ NAND p L3`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(h::L1)`])
\\ rw []
\\ sg `(∀y. ((y = h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3 ⇒ y ∈ events p)`
   >-(metis_tac [])
\\ sg `MUTUAL_INDEP p (h::(L1 ⧺ L2 ⧺ compl_list p L3)) `
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `L1 ⧺ [h] ⧺ L2 ++ compl_list p L3 =
              L1 ⧺ h::L2 ++ compl_list p L3 `
	  >-( rw [APPEND])
       \\ rw [])   
\\ sg `prob p (PATH p (h::L1) ∩ BIG_UNION p L2 ∩ NAND p L3) =
        prob p (PATH p (h::L1)) * prob p (BIG_UNION p L2) *
        prob p (NAND p L3)`
   >-(metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ++ compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1 ⧺ [h] ⧺ L2 ++ compl_list p L3 =
              L1 ⧺ h::L2 ++ compl_list p L3 `
	  >-( rw [APPEND])
       \\ rw []) 
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    OR INTER NAND     *)
(*----------------------*)

val OR_INTER_NAND = store_thm("OR_INTER_NAND",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ compl_list p L2)) 
            ==> (prob p (BIG_UNION p L1 ∩ NAND p L2) =
       	         prob p (BIG_UNION p L1) * prob p (NAND p L2))``,
GEN_TAC
\\ Induct
>-( rw [NAND_DEF, FTree_def, gate_list_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, FTree_def, gate_list_def]
\\ rw [DIFF_INTER]
\\ rw [UNION_OVER_INTER]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `BIG_UNION p L1 ∩ (p_space p DIFF h) IN events p `
   >-( metis_tac [BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `BIG_UNION p L1 ∩ NAND p L2 IN events p `
   >-( metis_tac [BIG_UNION_IN_EVENTS, NAND_DEF, FT_NAND_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `prob p (BIG_UNION p L1 ∩ (p_space p DIFF h)) =
       prob p (BIG_UNION p L1) * prob p (p_space p DIFF h)`
   >-( sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
       >-( rw [PATH_DEF]
       	   \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
      \\ POP_ORW
      \\ sg `BIG_UNION p L1 ∩ PATH p [p_space p DIFF h] =
             PATH p [p_space p DIFF h]  ∩ BIG_UNION p L1 `
         >-( rw [INTER_COMM])
      \\ POP_ORW
      \\ DEP_REWRITE_TAC [AND_INTER_OR]
      \\ rw []
      	 >-( metis_tac [EVENTS_COMPL])
  	 >-( metis_tac [])
	 >-( fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	     \\ irule MUTUAL_INDEP_append_sym 
       	     \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	     \\ Q.EXISTS_TAC `compl_list p L2`
       	     \\ irule MUTUAL_INDEP_append_sym
       	     \\ rw []     
       	     \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
                    L1 ⧺ p_space p DIFF h::compl_list p L2 `
                >-( rw [APPEND])
              \\ rw [])  
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ sg `prob p (BIG_UNION p L1 ∩ NAND p L2) =
       prob p (BIG_UNION p L1) * prob p  (NAND p L2)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
       	  >-( metis_tac [])   
   	  >-( metis_tac [])   
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              L1 ⧺ p_space p DIFF h::compl_list p L2 `
	  >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ sg `prob p ((p_space p DIFF h) ∩ NAND p L2) =
       prob p (p_space p DIFF h) * prob p (NAND p L2)`
   >-( sg `(p_space p DIFF h) = BIG_UNION p [p_space p DIFF h] `
       >-( rw [BIG_UNION_DEF]
       	   \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
       \\ POP_ORW
       \\ first_x_assum (mp_tac o Q.SPECL [`[p_space p DIFF h]`])
       \\ rw []
       \\ sg `(∀y. y = p_space p DIFF h ∨ MEM y L2 ⇒ y ∈ events p)  `
          >-( metis_tac [EVENTS_COMPL])
       \\ sg `MUTUAL_INDEP p (p_space p DIFF h::compl_list p L2) `
          >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `L1`
	      \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ sg `BIG_UNION p L1 ∩ (p_space p DIFF h) ∩ (BIG_UNION p L1 ∩ NAND p L2) =
       PATH p [p_space p DIFF h] ∩ BIG_UNION p L1 ∩ NAND p L2`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])   
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac [APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
              L1 ⧺ p_space p DIFF h::compl_list p L2`
	  >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw []) 
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------*)  
(*    AND INTER OR INTER NOR      *)
(*--------------------------------*)

val AND_INTER_OR_INTER_NOR = store_thm("AND_INTER_OR_INTER_NOR",
``!p L3 L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2 ++ compl_list p L3)) /\ ~NULL L1
            ==> (prob p (PATH p L1  ∩ BIG_UNION p L2 ∩ NOR p L3) =
       	         prob p (PATH p L1) * prob p (BIG_UNION p L2) * prob p (NOR p L3))``,

GEN_TAC
\\ GEN_TAC
\\ Induct
>-( rw [BIG_UNION_DEF]
    \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ sg `NOR p L3 ∩ PATH p L1 ∩ h IN events p `
   >-( metis_tac [NOR_DEF, FT_NOR_IN_EVENTS, PATH_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ sg `NOR p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 IN events p `
   >-( metis_tac [NOR_DEF, FT_NOR_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_UNION])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [NOR_DEF, FT_NOR_IN_EVENTS, PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [NOR_DEF, FT_NOR_IN_EVENTS, PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ sg `PATH p L1 ∩ h = PATH p (h::L1) `
   >-( rw [PATH_DEF, INTER_COMM])
\\ POP_ORW
\\ sg `NOR p L3 ∩ PATH p (h::L1) = PATH p (h::L1) ∩ NOR p L3 `
   >-( rw [INTER_COMM])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_APPEND1 
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1 
       \\ sg `L1 ⧺ [h] ⧺ L2 ⧺ compl_list p L3 = L1 ⧺ h::L2 ⧺ compl_list p L3`
	  >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3 `
	\\ irule MUTUAL_INDEP_append_sym
	\\ sg `L1 ⧺ [h] ⧺ L2  ⧺ compl_list p L3 = L1 ⧺ h::L2  ⧺ compl_list p L3`
	   >-( rw [APPEND])
	\\ rw [])
  >-( irule MUTUAL_INDEP_FRONT_APPEND  
      \\ Q.EXISTS_TAC `h::L2 ⧺ compl_list p L3`
      \\ irule MUTUAL_INDEP_append_sym
      \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `prob p (NOR p L3 ∩ (PATH p L1 ∩ BIG_UNION p L2)) =
       prob p (PATH p L1) * prob p (BIG_UNION p L2) * prob p (NOR p L3)`
   >-( sg `NOR p L3 ∩ (PATH p L1 ∩ BIG_UNION p L2) =
           PATH p L1 ∩ BIG_UNION p L2 ∩ NOR p L3`
       >-( rw [EXTENSION]
       	   \\ metis_tac [])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]  
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ sg `L1 ⧺ [h] ⧺ L2 ⧺ compl_list p L3 = L1 ⧺ h::L2 ⧺ compl_list p L3 `
	   >-( rw [APPEND])
	\\ rw [])          
\\ POP_ORW
\\ sg `prob p (h ∩ BIG_UNION p L2) = prob p h * prob p (BIG_UNION p L2) `
   >-( sg `h = PATH p [h] `
       >-( rw [PATH_DEF]
       	   \\ metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [AND_INTER_OR]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw [])
\\ POP_ORW
\\ sg `PATH p (h::L1) ∩ NOR p L3 ∩
           (NOR p L3 ∩ (PATH p L1 ∩ BIG_UNION p L2)) =
       PATH p (h::L1) ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(h::L1)`])
\\ rw []
\\ sg `(∀y. ((y = h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3 ⇒ y ∈ events p)`
   >-(metis_tac [])
\\ sg `MUTUAL_INDEP p (h::(L1 ⧺ L2 ⧺ compl_list p L3))`
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ sg `L1 ⧺ [h] ⧺ L2 ++ compl_list p L3 = L1 ⧺ h::L2 ++ compl_list p L3 `
	  >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p (PATH p (h::L1) ∩ BIG_UNION p L2 ∩ NOR p L3) =
        prob p (PATH p (h::L1)) * prob p (BIG_UNION p L2) *
        prob p (NOR p L3)`
   >-(metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `(h::L2) ⧺ compl_list p L3`
	\\ irule MUTUAL_INDEP_append_sym
        \\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ sg `L1 ⧺ [h] ⧺ L2 ⧺ compl_list p L3 = L1 ⧺ h::L2 ⧺ compl_list p L3 `
	   >-( rw [APPEND])
	\\ rw [])  
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ h::L2 `
	\\ rw [])  
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*    OR INTER NOR      *)
(*----------------------*)

val OR_INTER_NOR = store_thm("OR_INTER_NOR",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ compl_list p L2)) 
            ==> (prob p (BIG_UNION p L1 ∩ NOR p L2) =
       	         prob p (BIG_UNION p L1) * prob p (NOR p L2))``,
GEN_TAC
\\ Induct
>-( rw [NOR_DEF, FTree_def, gate_list_def]
    \\ rw [PROB_UNIV]
    \\ metis_tac [INTER_COMM, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ rw [NOR_DEF, FTree_def, gate_list_def]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NOR_DEF]
\\ rw [FTree_def]
\\ sg `prob p ((p_space p DIFF h) ∩ NOR p L2) =
       prob p (p_space p DIFF h) * prob p (NOR p L2)`
   >-( sg `(p_space p DIFF h) = BIG_UNION p [(p_space p DIFF h)] `
       >-( rw [BIG_UNION_DEF])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
       	  >-( metis_tac [EVENTS_COMPL])   
   	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw [])
\\ POP_ORW
\\ sg `BIG_UNION p L1 ∩ (p_space p DIFF h) ∩ NOR p L2 =
       PATH p [p_space p DIFF h]  ∩ BIG_UNION p L1 ∩ NOR p L2`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
	\\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
	       L1 ⧺ p_space p DIFF h::compl_list p L2`
	   >-( rw [APPEND])
	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1`
	\\ sg `L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
	       L1 ⧺ p_space p DIFF h::compl_list p L2`
	   >-( rw [APPEND])
	\\ rw [])  
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*   NOR INTER NOR      *)
(*----------------------*)

val NOR_INTER_NOR = store_thm("NOR_INTER_NOR",
``!p L2 L1. prob_space p /\ (!y. MEM y (L1 ++ L2) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2))) 
            ==> (prob p (NOR p L1 ∩ NOR p L2) =
       	         prob p (NOR p L1) * prob p (NOR p L2))``,
GEN_TAC
\\ Induct
>-( rw [NOR_DEF, FTree_def, gate_list_def]
    \\ rw [PROB_UNIV]
    \\ sg `(p_space p DIFF FTree p (OR (gate_list L1))) = NOR p L1 `
       >-( metis_tac [FTree_def, NOR_DEF])
    \\ POP_ORW
    \\ metis_tac [INTER_COMM, NOR_DEF, FT_NOR_IN_EVENTS, INTER_PSPACE])
\\ rw [NOR_DEF, FTree_def, gate_list_def]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NOR_DEF]
\\ rw [FTree_def]
\\ sg `NOR p L1 ∩ (p_space p DIFF h) = NOR p (h::L1) `
   >-( rw [NOR_DEF, OR_lem1, gate_list_def, FTree_def]
       \\ metis_tac [INTER_COMM])
\\ POP_ORW
\\ sg `(p_space p DIFF h) = NOR p [h] `
   >-( rw [NOR_DEF, gate_list_def, FTree_def])
\\ POP_ORW
\\ sg `prob p (NOR p [h] ∩ NOR p L2) = prob p (NOR p [h]) * prob p (NOR p L2) `
   >-( first_x_assum (mp_tac o Q.SPECL [`[h]`])
       \\ rw []
       \\ sg `(∀y. y = h ∨ MEM y L2 ⇒ y ∈ events p) `
       	  >-( metis_tac [])
       \\ sg ` MUTUAL_INDEP p (compl_list p (h::L2))`
       	  >-( fs [COMPL_LIST_SPLIT]
	      \\ fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `compl_list p L1`
	      \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(h::L1)`])
\\ rw []
\\ sg ` (∀y. (y = h ∨ MEM y L1) ∨ MEM y L2 ⇒ y ∈ events p) `
   >-( metis_tac [])
\\ sg `MUTUAL_INDEP p (compl_list p (h::(L1 ⧺ L2))) `
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
       	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2`
	  >-(rw [APPEND])
       \\ rw [])
\\ sg `prob p (NOR p (h::L1) ∩ NOR p L2) =
        prob p (NOR p (h::L1)) * prob p (NOR p L2) `
   >-( metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
       	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2`
	  >-(rw [APPEND])
       \\ rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1 ⧺ [p_space p DIFF h]`
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
       	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2`
	  >-(rw [APPEND])
       \\ rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC ` p_space p DIFF h::compl_list p L2 `
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 =
       	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2`
	  >-(rw [APPEND])
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------*)  
(*    AND INTER NOR  INTER NOR   *)
(*-------------------------------*)

val AND_INTER_NOR_INTER_NOR = store_thm("AND_INTER_NOR_INTER_NOR",
``!p L1  L3 L2. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p)  /\
	    (MUTUAL_INDEP p (compl_list p (L1++L3) ++ L2)) /\ ~NULL L2
           ==> (prob p (PATH p L2 ∩ (NOR p L1) ∩ (NOR p L3)) =
	        prob p (PATH p L2) * PROD_LIST (PROB_LIST p (compl_list p L1))
		                        * PROD_LIST (PROB_LIST p (compl_list p L3)))``,

GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ once_rewrite_tac [NOR_DEF]
\\ once_rewrite_tac [FTree_def]
\\ once_rewrite_tac [OR_gate_eq_BIG_UNION]
\\ Induct_on`L1`
>-( rw [BIG_UNION_DEF, SUM_LIST_DEF, PROB_LIST_DEF]
    \\ sg ` PATH p L2 ∩ p_space p = PATH p L2 `
       >-( metis_tac [PATH_IN_EVENTS, EVENTS_INTER, INTER_COMM, INTER_PSPACE])
    \\ fs []
    \\ rw [compl_list_def]
    \\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
    \\ rw [GSYM compl_list_def]
    \\ once_rewrite_tac [GSYM OR_gate_eq_BIG_UNION]
    \\ sg `p_space p DIFF FTree p (OR (gate_list L3)) = NOR p L3 `
       >-( rw [NOR_DEF, FTree_def])
    \\ POP_ORW
    \\ DEP_REWRITE_TAC [AND_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
    \\ metis_tac [])
\\ rw [BIG_UNION_DEF]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ sg `PATH p L2 ∩ (p_space p DIFF h) = PATH p ((p_space p DIFF h)::L2) `
   >-( rw  [PATH_DEF]
       \\ metis_tac [INTER_COMM])
\\ fs []
\\ first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L2)`])
\\ rw []
\\ sg `(∀y.
             (MEM y L1 ∨ y = p_space p DIFF h ∨ MEM y L2) ∨ MEM y L3 ⇒
             y ∈ events p) `
   >-( metis_tac [EVENTS_COMPL])
\\ sg `MUTUAL_INDEP p (compl_list p (L1 ⧺ L3) ⧺ p_space p DIFF h::L2) `
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]	
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ sg `prob p
          (PATH p (p_space p DIFF h::L2) ∩
           (p_space p DIFF BIG_UNION p L1) ∩ (p_space p DIFF BIG_UNION p L3)) =
        prob p (PATH p (p_space p DIFF h::L2)) *
        PROD_LIST (PROB_LIST p (compl_list p L1)) *
        PROD_LIST (PROB_LIST p (compl_list p L3))`
   >-( metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1++L3)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [COMPL_LIST_SPLIT])
    >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (h::(L1 ⧺ L3))`
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ rw [compl_list_def]
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------*)  
(*    AND INTER NAND INTER OR INTER OR     *)
(*-----------------------------------------*)

val AND_INTER_NAND_INTER_OR_INTER_OR = store_thm("AND_INTER_NAND_INTER_OR_INTER_OR",
``!p L3 L1 L4 L2. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2 ++ L3 ++ compl_list p L4)) /\ ~NULL L1
            ==> (prob p (PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3 ) =
       	         prob p (PATH p L1) * prob p (NAND p L4 ) * prob p (BIG_UNION p L2) *
		 prob p (BIG_UNION p L3))``,

GEN_TAC
\\ Induct
>-( rw [BIG_UNION_DEF]
    \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p L1 ∩ NAND p L4 ∩  BIG_UNION p L2 ∩ h IN events p `
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, BIG_UNION_IN_EVENTS,
                  EVENTS_INTER, EVENTS_UNION])
\\ sg `PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3 IN events p `
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS, BIG_UNION_IN_EVENTS, PATH_IN_EVENTS,
                  EVENTS_INTER, EVENTS_UNION])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ sg `h ∩ BIG_UNION p L3 =  PATH p [h] ∩ BIG_UNION p L3`
   >-( metis_tac [PATH_DEF, INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `prob p (PATH p [h] ∩ BIG_UNION p L3) =
       prob p (PATH p [h]) * prob p (BIG_UNION p L3)  `
   >-( DEP_REWRITE_TAC [AND_INTER_OR]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ++ L2`
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])    
\\ POP_ORW
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-(metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ h = (h ∩ PATH p L1) ∩ BIG_UNION p L2 ∩ NAND p L4`
   >-( metis_tac [INTER_COMM, INTER_ASSOC])
\\ POP_ORW
\\ rw [GSYM PATH_DEF]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NAND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3  ⧺ compl_list p L4 = L1 ⧺ L2 ⧺ h::L3  ⧺ compl_list p L4`
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3  ⧺ compl_list p L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 ⧺ compl_list p L4 = L1 ⧺ L2 ⧺ h::L3  ⧺ compl_list p L4`
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ h::L3 ⧺ compl_list p L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])  
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `prob p (PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3) =
       prob p (PATH p L1) * prob p (NAND p L4) * prob p (BIG_UNION p L2) * prob p (BIG_UNION p L3)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
        \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 ⧺ compl_list p L4 = L1 ⧺ L2 ⧺ h::L3 ⧺ compl_list p L4 `
          >-( rw [APPEND])
        \\ rw [])
\\ POP_ORW
\\ sg `prob p (PATH p (h::L1) ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3) =
       prob p (PATH p (h::L1)) * prob p (NAND p L4) * prob p (BIG_UNION p L2) *
       prob p (BIG_UNION p L3)`
   >-( first_x_assum (mp_tac o Q.SPECL [`(h::L1)`, `L4`, `L2`])
       \\ rw []
       \\ sg `(∀y.
             (((y = h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3) ∨ MEM y L4 ⇒
             y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (h::(L1 ⧺ L2 ⧺ L3 ⧺ compl_list p L4))`
          >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
              \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 ++ compl_list p L4 = L1 ⧺ L2 ⧺ h::L3 ++ compl_list p L4`
              	 >-( rw [APPEND])
               \\ rw [])
       \\ metis_tac [])
\\ sg `PATH p (h::L1) ∩ BIG_UNION p L2 ∩ NAND p L4 ∩
           (PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3) =
       PATH p (h::L1) ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ BIG_UNION p L3` 
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ ntac 2 POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND
        \\ Q.EXISTS_TAC `L2 ⧺ h::L3 ⧺ compl_list p L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L3 ⧺ compl_list p L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
        \\ sg `L1 ⧺ L2 ⧺ [h] ⧺ L3 ⧺ compl_list p L4 = L1 ⧺ L2 ⧺ h::L3 ⧺ compl_list p L4`
           >-( rw [APPEND])
         \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*    AND INTER NAND INTER OR INTER NOR      *)
(*-------------------------------------------*)

val AND_INTER_NAND_INTER_OR_INTER_NOR = store_thm("AND_INTER_NAND_INTER_OR_INTER_NOR",
``!p L3 L2 L4 L1. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L1 ++ L2 ++ compl_list p L3 ++ compl_list p L4)) /\ ~NULL L1
            ==> (prob p (PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3) =
       	         prob p (PATH p L1) * prob p (NAND p L4) *
		 prob p (BIG_UNION p L2) * prob p (NOR p L3))``,

GEN_TAC
\\ GEN_TAC
\\ GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ PATH p L1 ∩ (p_space p DIFF h) IN events p `
   >-( metis_tac [PATH_IN_EVENTS, FT_NOR_IN_EVENTS, NOR_DEF, BIG_UNION_IN_EVENTS,
                  EVENTS_INTER, EVENTS_COMPL])
\\ sg ` NOR p L3 ∩ BIG_UNION p L2 ∩ PATH p L1 ∩
        (p_space p DIFF FTree p (AND (gate_list L4))) IN events p`
   >-( metis_tac [FT_AND_IN_EVENTS, PATH_IN_EVENTS, FT_NOR_IN_EVENTS, NOR_DEF,
       		  BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [FT_AND_IN_EVENTS, PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
   >-( metis_tac [FT_AND_IN_EVENTS, PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ ntac 2 POP_ORW
\\ sg `PATH p L1 ∩ (p_space p DIFF h) = PATH p ((p_space p DIFF h)::L1) `
   >-( rw [PATH_DEF, INTER_COMM])
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ POP_ORW
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ PATH p (p_space p DIFF h::L1) =
       PATH p (p_space p DIFF h::L1) ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L1 ⧺ L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L4 =
              L1 ⧺ L2 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L4`
	  >-( rw [APPEND])
       \\ rw [])
\\ sg `p_space p DIFF h = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ compl_list p L3`
	\\ fs [compl_list_def])
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ (PATH p L1 ∩ NAND p L4) =
       PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC])
\\ POP_ORW
\\ sg `prob p (PATH p L1 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3) =
       prob p (PATH p L1) * prob p (NAND p L4) *
       prob p (BIG_UNION p L2) * prob p (NOR p L3)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
        \\ sg `L1 ⧺ L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L4 =
               L1 ⧺ L2 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L4`
	   >-( rw [APPEND])
        \\ rw []
	\\ fs [compl_list_def])
\\ POP_ORW
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ PATH p L1 ∩ (PATH p [p_space p DIFF h] ∩
       (NOR p L3 ∩ BIG_UNION p L2 ∩ PATH p L1 ∩ NAND p L4)) =
       PATH p L1 ∩ BIG_UNION p L2 ∩ NOR p L3 ∩ PATH p [p_space p DIFF h] ∩
       NAND p L4 ∩ PATH p L1 ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( metis_tac [INTER_COMM,  INTER_ASSOC])
\\ POP_ORW
\\ sg `PATH p L1 ∩ BIG_UNION p L2 ∩ NOR p L3 ∩
           PATH p [p_space p DIFF h] ∩ NAND p L4 ∩ PATH p L1 ∩
           BIG_UNION p L2 ∩ NOR p L3 =
       PATH p (p_space p DIFF h::L1) ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION] 
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L1)`])
\\ rw []
\\ sg `(∀y.
             (((y = p_space p DIFF h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3) ∨
             MEM y L4 ⇒
             y ∈ events p) `
   >-(metis_tac [EVENTS_COMPL])
\\ sg `MUTUAL_INDEP p
          (p_space p DIFF h::(L1 ⧺ L2 ⧺ compl_list p L3 ⧺ compl_list p L4)) `
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L1 ⧺ L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L4 =
              L1 ⧺ L2 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L4`
	  >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p
          (PATH p (p_space p DIFF h::L1) ∩ NAND p L4 ∩ BIG_UNION p L2 ∩
           NOR p L3) =
        prob p (PATH p (p_space p DIFF h::L1)) * prob p (NAND p L4) *
        prob p (BIG_UNION p L2) * prob p (NOR p L3) `
   >-(metis_tac [])
\\ POP_ORW
\\ sg `PATH p [p_space p DIFF h] = p_space p DIFF h `
   >-( rw [PATH_DEF, INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( metis_tac [])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3 ⧺ compl_list p L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
  >-( irule MUTUAL_INDEP_FRONT_APPEND  
      \\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3 ⧺ compl_list p (h::L4)`
      \\ irule MUTUAL_INDEP_append_sym
      \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*    NAND INTER NAND INTER OR INTER NOR     *)
(*-------------------------------------------*)

val NAND_INTER_NAND_INTER_OR_INTER_NOR = store_thm("NAND_INTER_NAND_INTER_OR_INTER_NOR",
``!p L1 L2 L3 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L3 ++ L4) ++ L1 ++ L2 ++ L3 ++ L4)) 
            ==> (prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ NOR p L4) =
       	         prob p (NAND p L1) * prob p (NAND p L2) *
		 prob p (BIG_UNION p L3) * prob p (NOR p L4))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `NOR p L4 ∩ BIG_UNION p L3 ∩ NAND p L2 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `NOR p L4 ∩ BIG_UNION p L3 ∩ NAND p L2 ∩ NAND p L1 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `(p_space p DIFF h) = PATH p [(p_space p DIFF h)]`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `(h::L1) ++ L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                         compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ NOR p L4) =
       prob p (NAND p L1) * prob p (NAND p L2) * prob p (BIG_UNION p L3) * prob p (NOR p L4)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ rw []
       \\ sg `p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                compl_list p L4 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L3 ⧺ L4) =
	      p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4)	`
          >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW
\\ sg `NAND p L1 ∩ PATH p [p_space p DIFF h] =  PATH p [p_space p DIFF h] ∩ NAND p L1 `
   >-( metis_tac [INTER_COMM])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC ` compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                         compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ NOR p L4 ∩
       PATH p [p_space p DIFF h] ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ NOR p L4 =
       NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ NOR p (h::L4)`
   >-( rw [NOR_DEF, FTree_def, gate_list_def]
       \\ rw [PATH_DEF, OR_lem1]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`L2`, `L3`, `(h::L4)`])
\\ rw []
\\ sg `(∀y.
             ((MEM y L1 ∨ MEM y L2) ∨ MEM y L3) ∨ y = h ∨ MEM y L4 ⇒
             y ∈ events p) `
   >-( metis_tac [])
\\ sg `MUTUAL_INDEP p
          (compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ h::L4) ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4) `
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	\\ Q.ABBREV_TAC `Y = [p_space p DIFF h] ⧺ (X ⧺ compl_list p L4)`
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
	\\ Q.UNABBREV_TAC `Y`
        \\ sg `p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                compl_list p L4 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L3 ⧺ L4) =
	      p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4)	`
          >-( rw [APPEND])
	\\ rw [])	
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ NOR p (h::L4)) =
        prob p (NAND p L1) * prob p (NAND p L2) * prob p (BIG_UNION p L3) *
        prob p (NOR p (h::L4)) `
   >-( metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h] ++ compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3`
	\\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3`
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
           p_space p DIFF h::(compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4) =
	   compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
           p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
          >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)  
(*    AND INTER NAND INTER NOR INTER NOR      *)
(*--------------------------------------------*)

val AND_INTER_NAND_INTER_NOR_INTER_NOR = store_thm("AND_INTER_NAND_INTER_NOR_INTER_NOR",
``!p L1 L2 L3 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\
           (MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)) /\ ~NULL L1
       ==> (prob p (PATH p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4) =
       	    prob p (PATH p L1) * prob p (NAND p L2) * prob p (NOR p L3) * prob p (NOR p L4))``,

GEN_TAC
\\ GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `NOR p L4 ∩ NOR p L3 ∩ PATH p L1 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, PATH_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg ` NOR p L4 ∩ NOR p L3 ∩ PATH p L1 ∩ NAND p L2 IN events p `
   >-( metis_tac [NAND_DEF, PATH_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `PATH p L1 ∩ (p_space p DIFF h) = PATH p ((p_space p DIFF h)::L1)`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_NOR_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( metis_tac [])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
        \\ irule MUTUAL_INDEP_FRONT_APPEND
	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND
	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
        \\ irule MUTUAL_INDEP_FRONT_APPEND
       	\\ Q.EXISTS_TAC `compl_list p L1`
        \\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
        \\ rw [])
     >-( irule MUTUAL_INDEP_FRONT_APPEND
	 \\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4`
	 \\ irule MUTUAL_INDEP_append_sym
	 \\ irule MUTUAL_INDEP_FRONT_APPEND
	 \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ h::L2 ⧺ L3 ⧺ L4)`
	 \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg `prob p (PATH p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4) =
       prob p (PATH p L1) * prob p (NAND p L2) * prob p (NOR p L3) * prob p (NOR p L4)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ [h] ++ L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
       \\ rw [])
\\ sg `PATH p L1 ∩ NAND p L2 ∩ NOR p L4 ∩ NOR p L3 = PATH p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ ntac 2 POP_ORW
\\ sg `(p_space p DIFF h) ∩ NAND p L2 = PATH p [p_space p DIFF h] ∩ NAND p L2`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                         compl_list p L3 ⧺ compl_list p L4`
	\\ rw [])
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1`
	\\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
        \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4 ∩ PATH p L1 ∩
       (p_space p DIFF h) ∩ NOR p L4 ∩ NOR p L3 =
       PATH p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p (h::L4)`
   >-( rw [NOR_DEF, FTree_def, gate_list_def]
       \\ rw [PATH_DEF, OR_lem1]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`L3`, `(h::L4)`])
\\ rw []
\\ sg `(∀y.
             ((MEM y L1 ∨ MEM y L2) ∨ MEM y L3) ∨ y = h ∨ MEM y L4 ⇒
             y ∈ events p) `
   >-( metis_tac [])
\\ sg `MUTUAL_INDEP p
          (compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ h::L4) ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4) `
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 5 POP_ORW
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])	
	\\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ ntac 7 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 9 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
           compl_list p L3 ⧺ compl_list p L4 ++ L1 `
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
        \\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ [h] ++ L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
        \\ rw [])	
\\ sg `prob p (PATH p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p (h::L4)) =
        prob p (PATH p L1) * prob p (NAND p L2) * prob p (NOR p L3) *
        prob p (NOR p (h::L4))`
   >-( metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 `
	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ++ [p_space p DIFF h]`
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               [p_space p DIFF h] ⧺ compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4 =
               compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
          >-( rw [APPEND])
	\\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3`
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               p_space p DIFF h::(compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4) = 
               compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
          >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                         compl_list p L3 ⧺ compl_list p L4`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------------*)  
(*   NAND INTER NAND INTER NOR INTER NOR      *)
(*--------------------------------------------*)

val NAND_INTER_NAND_INTER_NOR_INTER_NOR = store_thm("NAND_INTER_NAND_INTER_NOR_INTER_NOR",
``!p L1 L2 L3 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\
           (MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)) /\ ~NULL L1
       ==> (prob p (NAND p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4) =
       	    prob p (NAND p L1) * prob p (NAND p L2) * prob p (NOR p L3) * prob p (NOR p L4))``,

GEN_TAC
\\ GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `NOR p L4 ∩ NOR p L3 ∩ NAND p L1 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, PATH_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg ` NOR p L4 ∩ NOR p L3 ∩ NAND p L1 ∩ NAND p L2 IN events p `
   >-( metis_tac [NAND_DEF, PATH_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF]) 
\\ sg `p_space p DIFF h = PATH p [p_space p DIFF h]`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ sg `NOR p L4 ∩ NOR p L3 ∩ NAND p L1 ∩ PATH p [p_space p DIFF h] =
       PATH p [p_space p DIFF h] ∩ NAND p L1 ∩ NOR p L4 ∩ NOR p L3`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NOR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ rw [P_SPACE_DIFF]
       \\ sg `h ∩ p_space p = h `
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW	  
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `[h] ⧺ L2 = h::L2 `
          >-( rw [APPEND])
       \\ POP_ORW
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ compl_list p L4 ⧺ compl_list p L3 ⧺ [p_space p DIFF h]`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ Q.UNABBREV_TAC `X`    
       \\ Q.ABBREV_TAC `X = L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`
       \\ rw []
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg ` [p_space p DIFF h]⧺ compl_list p  L2 = p_space p DIFF h::compl_list p  L2 `
          >-( rw [APPEND])
       \\ POP_ORW
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.UNABBREV_TAC `X`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND
	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND
       	\\ Q.EXISTS_TAC `compl_list p L1`
        \\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
        \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `NOR p L4 ∩ NOR p L3 ∩ NAND p L1 ∩ NAND p L2 =
       NAND p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4 `
   >-( rw [EXTENSION]
       \\ metis_tac[])
\\ POP_ORW
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4) =
       prob p (NAND p L1) * prob p (NAND p L2) * prob p (NOR p L3) * prob p (NOR p L4)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ [h] ++ L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
       \\ rw [])    
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1`
	\\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
        \\ rw [])   
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p [p_space p DIFF h] ∩ NAND p L1 ∩ NOR p L4 ∩ NOR p L3 ∩
       (NAND p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p L4) =
        NAND p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p (h::L4)`
   >-( rw [PATH_DEF, NOR_DEF, FTree_def, gate_list_def]
       \\ rw [PATH_DEF, OR_lem1]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`L3`, `(h::L4)`])
\\ rw []
\\ sg `(∀y.
             ((MEM y L1 ∨ MEM y L2) ∨ MEM y L3) ∨ y = h ∨ MEM y L4 ⇒
             y ∈ events p) `
   >-( metis_tac [])
\\ sg `MUTUAL_INDEP p
          (compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ h::L4) ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4) `
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 5 POP_ORW
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])	
	\\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ ntac 7 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 9 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
           compl_list p L3 ⧺ compl_list p L4 ++ L1 `
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
        \\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ [h] ++ L2 ⧺ L3 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
        \\ rw [])	
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ NOR p L3 ∩ NOR p (h::L4)) =
        prob p (NAND p L1) * prob p (NAND p L2) * prob p (NOR p L3) *
        prob p (NOR p (h::L4))`
   >-( metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h ]`
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               [p_space p DIFF h] ⧺ compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4 =
               compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
          >-( rw [APPEND])
	\\ rw [])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2`
	\\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3`
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               p_space p DIFF h::(compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4) = 
               compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
               p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ L3 ⧺ h::L4`
          >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------*)  
(*    AND INTER NAND INTER NAND INTER OR INTER OR     *)
(*----------------------------------------------------*)

val AND_INTER_NAND_INTER_NAND_INTER_OR_INTER_OR = store_thm("AND_INTER_NAND_INTER_NAND_INTER_OR_INTER_OR",
``!p L2 L1 L3 L4 L5. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4 ++ L5) ==> y IN events p) /\ ~NULL L1 /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L3 ++ L4 ++ L5) ++ L1 ++ L2 ++ L3 ++ L4 ++ L5)) 
            ==> (prob p (PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5) =
       	         prob p (PATH p L1) * prob p (NAND p L2) * prob p (NAND p L3) * prob p (BIG_UNION p L4) *
		 prob p (BIG_UNION p L5))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]    
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `BIG_UNION p L5 ∩ BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg ` BIG_UNION p L5 ∩ BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩ NAND p L2 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `(p_space p DIFF h) = PATH p [(p_space p DIFF h)]`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5 `
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4 ⧺ L5` 
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                         compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5` 
	\\ rw [])
   >-( rw [EVENTS_COMPL])
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺
	                 L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5` 
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1` 
	\\ rw []
	\\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5 =
	       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5`
	   >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `BIG_UNION p L5 ∩ BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩ PATH p [p_space p DIFF h] =
       PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `BIG_UNION p L5 ∩ BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩  NAND p L2 =
       PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ BIG_UNION p L4 ∩
           BIG_UNION p L5 ∩ (PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5)=
       PATH p (p_space p DIFF h::L1) ∩  NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5`
    >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `prob p (PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5) =
       	prob p (PATH p (p_space p DIFF h::L1))  * prob p (NAND p L3) * prob p (BIG_UNION p L4) *
	prob p (BIG_UNION p L5)  `
   >-( DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_OR]
       \\ rw []
       >-( metis_tac [EVENTS_COMPL])
       >-( metis_tac [])
       >-( metis_tac [])
       >-( metis_tac [])
       >-( metis_tac [])
       \\ fs [compl_list_def]
       	   \\ fs [GSYM compl_list_def]
	   \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L2`
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1`
       	   \\ rw []
	   \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2`
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L4 ⧺ compl_list p L5`
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	   \\ Q.ABBREV_TAC `Y = compl_list p L3 ⧺ (compl_list p L4 ⧺ compl_list p L5)`
	   \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ Q.UNABBREV_TAC `X`
	   \\ Q.UNABBREV_TAC `Y`
	   \\ rw []
	   \\ Q.ABBREV_TAC `Y = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                                compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 `
           \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `h::L2 ⧺ L3`
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ Q.UNABBREV_TAC `Y`
	   \\ rw []
	   \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                  compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5 =
		  compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                  compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5`
	      >-( rw [APPEND])
	   \\ rw [])
\\ POP_ORW
\\ sg `prob p (PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4 ∩ BIG_UNION p L5) =
       prob p (PATH p L1) * prob p (NAND p L2) * prob p (NAND p L3) * prob p (BIG_UNION p L4) *
       prob p (BIG_UNION p L5) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 8 (once_rewrite_tac[GSYM APPEND_ASSOC])      
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`       
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                           compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1`			   
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ Q.UNABBREV_TAC `X`
       \\ rw []
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ [h] ⧺ L2 ⧺ L3 ⧺ L4 ⧺ L5 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5`
          >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW  
\\ sg `prob p (PATH p (p_space p DIFF h::L1) ∩ NAND p L2 ∩ NAND p L3 ∩  BIG_UNION p L4 ∩ BIG_UNION p L5) =
       prob p (PATH p (p_space p DIFF h::L1)) * prob p (NAND p L2)  * prob p (NAND p L3) *
       prob p (BIG_UNION p L4) * prob p (BIG_UNION p L5)`
   >-( first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L1)`, `L3`, `L4`, `L5`])
       \\ rw []
       \\ sg `(∀y. ((((y = p_space p DIFF h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3) ∨
                   MEM y L4) ∨ MEM y L5 ⇒ y ∈ events p)  `
          >-( metis_tac [EVENTS_COMPL])
       \\ sg `MUTUAL_INDEP p (compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L3 ⧺ L4 ⧺ L5)) ⧺
                              p_space p DIFF h::L1 ⧺ L2 ⧺ L3 ⧺ L4 ⧺ L5) `
	  >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ rw [P_SPACE_DIFF]
	      \\ sg `h ∩ p_space p = h `
	         >-( metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
	      \\ POP_ORW
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                                   compl_list p L4 ⧺ compl_list p L5 ⧺ p_space p DIFF h::L1 `
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ Q.UNABBREV_TAC `X`
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ Q.ABBREV_TAC `X =  L1 ⧺ ([h] ⧺ ([] ⧺ (L2 ⧺ (L3 ⧺ (L4 ⧺ L5)))))`
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])	
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ Q.UNABBREV_TAC `X`
	      \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                     compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺
                     (L1 ⧺ ([h] ⧺ ([] ⧺ (L2 ⧺ (L3 ⧺ (L4 ⧺ L5)))))) =
		     compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                     compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺
          	      L3 ⧺ L4 ⧺ L5`
		 >-( rw [APPEND])
	      \\ rw [])
       \\  metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( metis_tac [])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` h::L2 ⧺ L3 ⧺ L4 ⧺ L5`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ Q.ABBREV_TAC `X = L1 ⧺ (h::L2 ⧺ L3 ⧺ L4 ⧺ L5)`
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` compl_list p L1`
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
	\\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5 =
	       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4 ⧺ compl_list p L5 ⧺ L1 ⧺ h::L2 ⧺  L3 ⧺ L4 ⧺ L5`
          >-( rw [APPEND])
        \\ rw [])
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4 ⧺ L5`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ h::L2 ⧺ L3 ⧺ L4 ⧺ L5)`
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*    NAND INTER NAND INTER OR INTER OR      *)
(*-------------------------------------------*)

val NAND_INTER_NAND_INTER_OR_INTER_OR = store_thm("NAND_INTER_NAND_INTER_OR_INTER_OR",
``!p L1 L2 L3 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L3 ++ L4) ++ L1 ++ L2 ++ L3 ++ L4)) 
            ==> (prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ BIG_UNION p L4) =
       	         prob p (NAND p L1) * prob p (NAND p L2) *
		 prob p (BIG_UNION p L3) * prob p (BIG_UNION p L4))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `BIG_UNION p L4 ∩ BIG_UNION p L3 ∩ NAND p L2 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `BIG_UNION p L4 ∩ BIG_UNION p L3 ∩ NAND p L2 ∩ NAND p L1 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `(p_space p DIFF h) = PATH p [(p_space p DIFF h)]`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ sg `BIG_UNION p L4 ∩ BIG_UNION p L3 ∩ NAND p L2 ∩ PATH p [p_space p DIFF h] =
       PATH p [p_space p DIFF h] ∩ NAND p L2 ∩ BIG_UNION p L4 ∩ BIG_UNION p L3`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_OR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\  irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2`
       \\ rw []
       \\ Q.ABBREV_TAC `X = compl_list p L3 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw []
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.UNABBREV_TAC `X`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                         compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `BIG_UNION p L4 ∩ BIG_UNION p L3 ∩ NAND p L2 ∩ NAND p L1 =
       NAND p L1 ∩ NAND p L2  ∩ BIG_UNION p L3 ∩ BIG_UNION p L4`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW       
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ BIG_UNION p L4) =
       prob p (NAND p L1) * prob p (NAND p L2) * prob p (BIG_UNION p L3) * prob p (BIG_UNION p L4)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ rw []
       \\ sg `p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                compl_list p L4 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L3 ⧺ L4) =
	      p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4)	`
          >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW
\\ sg `NAND p L1 ∩ PATH p [p_space p DIFF h] =  PATH p [p_space p DIFF h] ∩ NAND p L1 `
   >-( metis_tac [INTER_COMM])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC ` compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                         compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p [p_space p DIFF h] ∩ NAND p L2 ∩ BIG_UNION p L4 ∩ BIG_UNION p L3 ∩
       (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ BIG_UNION p L4) =
       PATH p [p_space p DIFF h] ∩ NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 ∩ BIG_UNION p L4`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NAND_INTER_OR_INTER_OR]
\\ rw []
   >-(rw [EVENTS_COMPL])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ rw [P_SPACE_DIFF]
       \\ sg `h ∩ p_space p = h `
       	  >-( metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
       \\ POP_ORW
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ Q.ABBREV_TAC `X = L1 ⧺ (L2 ⧺ (L3 ⧺ L4))`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])	  
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ Q.UNABBREV_TAC `X`
       \\ rw []
       \\ sg `p_space p DIFF h:: (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
              compl_list p L4 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L3 ⧺ L4) =
	      p_space p DIFF h:: (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
              compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4)`
 	      >-( rw [APPEND])
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                          compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*     NAND INTER OR INTER NOR               *)
(*-------------------------------------------*)

val NAND_INTER_OR_INTER_NOR = store_thm("NAND_INTER_OR_INTER_NOR",
``!p L4 L2 L3. prob_space p /\ (!y. MEM y (L2 ++ L3 ++ L4) ==> y IN events p) /\
	    (MUTUAL_INDEP p (L2 ++ compl_list p L3 ++ compl_list p L4 ++ L4))
            ==> (prob p (NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3) =
       	         prob p (NAND p L4) * prob p (BIG_UNION p L2) * prob p (NOR p L3))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ (p_space p DIFF h) IN events p `
   >-( metis_tac [PATH_IN_EVENTS, FT_NOR_IN_EVENTS, NOR_DEF, BIG_UNION_IN_EVENTS,
                  EVENTS_INTER, EVENTS_COMPL])
\\ sg ` NOR p L3 ∩ BIG_UNION p L2 ∩
        (p_space p DIFF FTree p (AND (gate_list L4))) IN events p`
   >-( metis_tac [FT_AND_IN_EVENTS, PATH_IN_EVENTS, FT_NOR_IN_EVENTS, NOR_DEF,
       		  BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [FT_AND_IN_EVENTS, PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
   >-( metis_tac [FT_AND_IN_EVENTS, PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ ntac 2 POP_ORW
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF, INTER_COMM, EVENTS_COMPL, EVENTS_INTER, INTER_PSPACE])
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ PATH p [p_space p DIFF h] =
       PATH p [p_space p DIFF h]  ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L4 ++ (h::L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ sg `L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L4 ++ (h::L4)=
              L2 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L4 ++ (h::L4)`
	  >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2 ⧺ compl_list p L3`
	\\ fs [compl_list_def])
\\ sg `NOR p L3 ∩ BIG_UNION p L2 ∩ NAND p L4 =
       NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC])
\\ POP_ORW
\\ sg `prob p (NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L3) =
       prob p (NAND p L4) * prob p (BIG_UNION p L2) * prob p (NOR p L3)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
       	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h]`
	\\ ntac 3 (once_rewrite_tac [APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
        \\ sg `L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L4 ⧺ [h] ⧺ L4=
               L2 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L4 ⧺ h::L4`
	   >-( rw [APPEND])
        \\ rw []
	\\ fs [compl_list_def])
\\ POP_ORW
\\ sg `PATH p [p_space p DIFF h] ∩ BIG_UNION p L2 ∩ NOR p L3 ∩ NOR p L3 ∩
       BIG_UNION p L2 ∩ NAND p L4  =  NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p (h::L3)`
   >-( rw [NOR_DEF, FTree_def, gate_list_def, OR_lem1, PATH_DEF, P_SPACE_DIFF]
       \\ sg `(p_space p DIFF h) ∩ p_space p = (p_space p DIFF h)`
          >-( metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`L2`, `h::L3`])
\\ rw []
\\ sg `(∀y. (MEM y L2 ∨ y = h ∨ MEM y L3) ∨ MEM y L4 ⇒ y ∈ events p)`
   >-(metis_tac [EVENTS_COMPL])
\\ sg `MUTUAL_INDEP p (L2 ⧺ compl_list p (h::L3) ⧺ compl_list p L4 ⧺ L4)`
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ rw []
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `[h]`
	\\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
        \\ sg `L2 ⧺ compl_list p L3 ⧺ [p_space p DIFF h] ⧺ compl_list p L4 ++ [h] ⧺ L4=
              L2 ⧺ compl_list p L3 ⧺ p_space p DIFF h::compl_list p L4 ++ h::L4`
	   >-( rw [APPEND])
        \\ rw [])
\\ sg ` prob p (NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p (h::L3)) =
        prob p (NAND p L4) * prob p (BIG_UNION p L2) * prob p (NOR p (h::L3))`
   >-(metis_tac [])
\\ POP_ORW
\\ sg `PATH p [p_space p DIFF h] = p_space p DIFF h `
   >-( rw [PATH_DEF, INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L4 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2 ⧺ [p_space p DIFF h]`
	\\ rw []
        \\ sg `L2 ⧺ [p_space p DIFF h] ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺ L4 =
	       L2 ⧺ p_space p DIFF h::compl_list p L3 ⧺ compl_list p L4 ⧺ L4`
	   >-( rw [APPEND])
        \\ rw [])
   >-( rw [EVENTS_COMPL])
   >-( rw [EVENTS_COMPL])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
      \\ Q.EXISTS_TAC `compl_list p L4 ⧺ L4`
      \\ irule MUTUAL_INDEP_append_sym
      \\ irule MUTUAL_INDEP_FRONT_APPEND  
      \\ Q.EXISTS_TAC `L2`
      \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------*)  
(*     NAND INTER OR INTER OR              *)
(*-----------------------------------------*)

val NAND_INTER_OR_INTER_OR = store_thm("NAND_INTER_OR_INTER_OR",
``!p L3 L1 L2. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p L3 ++ L1 ++ L2 ++ L3)) 
            ==> (prob p (NAND p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 ) =
       	         prob p (NAND p L3 ) * prob p (BIG_UNION p L1) *
		 prob p (BIG_UNION p L2))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ sg `p_space p DIFF h = PATH p [p_space p DIFF h]`
   >-( rw [PATH_DEF, EVENTS_COMPL, INTER_COMM, EVENTS_INTER, INTER_PSPACE])
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF, INTER_COMM, EVENTS_COMPL, EVENTS_INTER, INTER_PSPACE])
\\ POP_ORW
\\ sg `(BIG_UNION p L2 ∩ BIG_UNION p L1 ∩ PATH p [p_space p DIFF h]) IN events p `
   >-( rw [PATH_IN_EVENTS, BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `(BIG_UNION p L2 ∩ BIG_UNION p L1 ∩ NAND p L3)  IN events p`
   >-( rw [FT_AND_IN_EVENTS, PATH_IN_EVENTS, FT_NAND_IN_EVENTS, NAND_DEF,
       		  BIG_UNION_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ ntac 2 POP_ORW
\\ sg `BIG_UNION p L2 ∩ BIG_UNION p L1 ∩ PATH p [p_space p DIFF h] =
       PATH p [p_space p DIFF h]  ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_OR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `h::L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p L3`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw [])
\\ sg `prob p (BIG_UNION p L2 ∩ BIG_UNION p L1 ∩ NAND p L3) =
       prob p (BIG_UNION p L2) * prob p (BIG_UNION p L1) * prob p (NAND p L3) `
   >-( rw [INTER_COMM]
       \\ rw [INTER_ASSOC]
       \\  first_x_assum (mp_tac o Q.SPECL [`L1`, `L2`])
       \\ rw []
       \\ sg `(∀y. (MEM y L1 ∨ MEM y L2) ∨ MEM y L3 ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg ` MUTUAL_INDEP p (compl_list p L3 ⧺ L1 ⧺ L2 ⧺ L3)`
          >-( irule MUTUAL_INDEP_append_sym
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
              \\ Q.EXISTS_TAC `[h]`
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_append_sym
	      \\  fs [compl_list_def]
              \\ fs [GSYM compl_list_def]
	      \\  irule MUTUAL_INDEP_FRONT_APPEND  
              \\ Q.EXISTS_TAC `[p_space p DIFF h]`
	      \\ rw []
	      \\ sg `p_space p DIFF h::(compl_list p L3 ⧺ L1 ⧺ L2 ⧺ [h] ⧺ L3)  =
	             p_space p DIFF h::(compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3)`
		 >-( rw [APPEND])
              \\ rw [])
         \\ sg `prob p (NAND p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2) =
            prob p (NAND p L3) * prob p (BIG_UNION p L1) *
            prob p (BIG_UNION p L2) `
	    >-( metis_tac [])
	 \\ POP_ORW
	 \\ REAL_ARITH_TAC)   
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def])
\\ sg `PATH p [p_space p DIFF h] ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 ∩
       BIG_UNION p L2 ∩ BIG_UNION p L1 ∩ NAND p L3 =
       PATH p [p_space p DIFF h] ∩ NAND p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ rw [INTER_ASSOC]
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_OR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------*)  
(*     NAND INTER NOR INTER NOR            *)
(*-----------------------------------------*)

val NAND_INTER_NOR_INTER_NOR = store_thm("NAND_INTER_NOR_INTER_NOR",
``!p L3 L1 L2. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L3) ++ L1 ++ L2 ++ L3)) 
            ==> (prob p (NAND p L3 ∩ NOR p L1 ∩ NOR p L2 ) =
       	         prob p (NAND p L3 ) * prob p (NOR p L1) *
		 prob p (NOR p L2))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ sg `p_space p DIFF h = PATH p [p_space p DIFF h]`
   >-( rw [PATH_DEF, EVENTS_COMPL, INTER_COMM, EVENTS_INTER, INTER_PSPACE])
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF, INTER_COMM, EVENTS_COMPL, EVENTS_INTER, INTER_PSPACE])
\\ POP_ORW
\\ sg `(NOR p L2 ∩ NOR p L1 ∩ PATH p [p_space p DIFF h]) IN events p `
   >-( rw [PATH_IN_EVENTS, FT_NOR_IN_EVENTS, NOR_DEF, EVENTS_INTER, EVENTS_COMPL])
\\ sg `(NOR p L2 ∩ NOR p L1 ∩ NAND p L3)  IN events p`
   >-( rw [FT_NOR_IN_EVENTS, NOR_DEF, PATH_IN_EVENTS, FT_NAND_IN_EVENTS, NAND_DEF,
       	   EVENTS_INTER, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( rw [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ ntac 2 POP_ORW
\\ sg `NOR p L2 ∩ NOR p L1 ∩ PATH p [p_space p DIFF h] =
       PATH p [p_space p DIFF h]  ∩ NOR p L1 ∩ NOR p L2 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ [p_space p DIFF h] ⧺ compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3 =
	       compl_list p L1 ⧺ compl_list p L2 ⧺ p_space p DIFF h::compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3`
	   >-( rw [APPEND])	   
	\\ rw [])
\\ sg `prob p (NOR p L2 ∩ NOR p L1 ∩ NAND p L3) =
       prob p (NOR p L2) * prob p (NOR p L1) * prob p (NAND p L3) `
   >-( rw [INTER_COMM]
       \\ rw [INTER_ASSOC]
       \\  first_x_assum (mp_tac o Q.SPECL [`L1`, `L2`])
       \\ rw []
       \\ sg `(∀y. (MEM y L1 ∨ MEM y L2) ∨ MEM y L3 ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ⧺ L3) ⧺ L1 ⧺ L2 ⧺ L3)`
          >-( fs [compl_list_def]
              \\ fs [GSYM compl_list_def]
	      \\ irule MUTUAL_INDEP_append_sym
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
              \\ Q.EXISTS_TAC `[h]`
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_append_sym
	      \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
              \\ Q.EXISTS_TAC `[p_space p DIFF h]`
	      \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ [p_space p DIFF h] ⧺
                     compl_list p L3 ⧺ L1 ⧺ L2 ⧺ [h] ⧺ L3 = compl_list p L1 ⧺ compl_list p L2 ⧺
                     p_space p DIFF h::compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3`
		 >-( rw [APPEND])
              \\ rw [])
         \\ sg `prob p (NAND p L3 ∩ NOR p L1 ∩ NOR p L2) =
                prob p (NAND p L3) * prob p (NOR p L1) * prob p (NOR p L2) `
	    >-( metis_tac [])
	 \\ POP_ORW
	 \\ REAL_ARITH_TAC)   
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2`
       \\ rw [])
\\ sg `PATH p [p_space p DIFF h] ∩ NOR p L1 ∩ NOR p L2 ∩
       NOR p L2 ∩ NOR p L1 ∩ NAND p L3 =
       PATH p [p_space p DIFF h] ∩ NAND p L3 ∩ NOR p L1 ∩ NOR p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ rw [INTER_ASSOC]
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NOR_INTER_NOR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ rw [P_SPACE_DIFF]
       \\ sg `h ∩ p_space p = h `
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `X = [p_space p DIFF h] ⧺ compl_list p L3`
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.ABBREV_TAC `Y = L1 ⧺ (L2 ⧺ ([h] ⧺ L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ Q.ABBREV_TAC `Z = compl_list p L1 ⧺ compl_list p L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `X`
       \\ Q.UNABBREV_TAC `Y`
       \\ Q.UNABBREV_TAC `Z`
       \\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ [p_space p DIFF h] ⧺
           compl_list p L3 ⧺ L1 ⧺ L2 ⧺ [h] ⧺ L3 = compl_list p L1 ⧺ compl_list p L2 ⧺
           p_space p DIFF h::compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3 `
	   >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2`
       \\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ [p_space p DIFF h] ⧺
           compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3 = compl_list p L1 ⧺ compl_list p L2 ⧺
           p_space p DIFF h::compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3 `
	   >-( rw [APPEND])
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `p_space p DIFF h::compl_list p L3 ⧺ L1 ⧺ L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ⧺ h::L3) ⧺ L1 ⧺ L2 ⧺ h::L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*    NAND INTER NAND INTER  NOR             *)
(*-------------------------------------------*)

val NAND_INTER_NAND_INTER_NOR = store_thm("NAND_INTER_NAND_INTER_NOR",
``!p L1 L2 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L4) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L4) ++ L1 ++ L2 ++ L4)) 
            ==> (prob p (NAND p L1 ∩ NAND p L2 ∩ NOR p L4) =
       	         prob p (NAND p L1) * prob p (NAND p L2) * prob p (NOR p L4))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `NOR p L4  ∩ NAND p L2 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `NOR p L4  ∩ NAND p L2 ∩ NAND p L1 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `NOR p L4 ∩ NAND p L2 ∩ (p_space p DIFF h) =  NAND p L2  ∩ NOR p (h::L4)`
   >-( rw [NOR_DEF, OR_lem1, gate_list_def, FTree_def]
       \\ rw [GSYM FTree_def]
       \\ rw [GSYM NOR_DEF]
       \\ rw [FTree_def]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h::L1 ⧺ L2 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`      
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF, INTER_COMM, EVENTS_COMPL, EVENTS_INTER, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ NOR p L4) =
       prob p (NAND p L1) * prob p (NAND p L2) * prob p (NOR p L4)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]       
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ rw []
       \\ sg `p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺
                compl_list p L4 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L4) =
	      p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺
                compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L4)	`
          >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW
\\ sg `NAND p L2 ∩ NOR p (h::L4) ∩ NAND p L1 ∩ NAND p L2 ∩ NOR p L4 =
        NAND p L1 ∩ NAND p L2 ∩ NOR p (h::L4)`
   >-( rw [NOR_DEF, FTree_def, gate_list_def, OR_lem1]      
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`L2`, `(h::L4)`])
\\ rw []
\\ sg ` (∀y. (MEM y L1 ∨ MEM y L2) ∨ y = h ∨ MEM y L4 ⇒ y ∈ events p)`
   >-( metis_tac [])
\\ sg ` MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ⧺ h::L4) ⧺ L1 ⧺ L2 ⧺ h::L4) `
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ Q.ABBREV_TAC `X = [p_space p DIFF h] ⧺ (compl_list p L1 ⧺ compl_list p L2) ⧺ compl_list p L4`
	\\ rw []
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
        \\ sg `[p_space p DIFF h] ⧺ (compl_list p L1 ⧺ compl_list p L2) ⧺
               compl_list p L4 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L4 = p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L4)`	
           >-( rw [APPEND])
	\\ rw [])	
\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ NOR p (h::L4)) =
        prob p (NAND p L1) * prob p (NAND p L2) * prob p (NOR p (h::L4)) `
   >-( metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `(compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L4 ⧺ h::L1 ⧺ L2 ⧺ L4)`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L1 ⧺ L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h] ++ compl_list p L1 ⧺ compl_list p L2`
	\\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ h::L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2`
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺
           p_space p DIFF h::(compl_list p L4 ⧺ L1 ⧺ L2 ⧺ h::L4) =
	   compl_list p L1 ⧺ compl_list p L2  ⧺
           p_space p DIFF h::compl_list p L4 ⧺ L1 ⧺ L2 ⧺ h::L4`
          >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def]
\\ rw [GSYM compl_list_def]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*     AND INTER NAND INTER  NOR             *)
(*-------------------------------------------*)

val AND_INTER_NAND_INTER_NOR = store_thm("AND_INTER_NAND_INTER_NOR",
``!p L2 L1 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L4) ==> y IN events p) /\  ~NULL L1 /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L4) ++ L1 ++ L2 ++ L4)) 
            ==> (prob p (PATH p L1 ∩ NAND p L2 ∩ NOR p L4) =
       	         prob p (PATH p L1) * prob p (NAND p L2) * prob p (NOR p L4))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `NOR p L4  ∩ PATH p L1 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `NOR p L4  ∩ PATH p L1 ∩ NAND p L1 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [NAND_DEF, FT_NAND_IN_EVENTS])
\\ sg `NOR p L4 ∩ PATH p L1 ∩ (p_space p DIFF h) =  PATH p (p_space p DIFF h::L1) ∩ NOR p L4`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h::L2 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2`      
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw []
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4 =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4`
          >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p (PATH p L1 ∩ NAND p L2 ∩ NOR p L4) =
        prob p (PATH p L1) * prob p (NAND p L2) * prob p (NOR p L4) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
       	   >-( rw [EVENTS_COMPL])
       	   >-( rw [EVENTS_COMPL])
	   >-( rw [EVENTS_COMPL])
  	       \\ fs [compl_list_def]
           	\\ fs [GSYM compl_list_def]
		\\ once_rewrite_tac[GSYM APPEND_ASSOC]
        	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       		\\ Q.EXISTS_TAC `[h]`
		\\  once_rewrite_tac[APPEND_ASSOC]
       		\\ irule MUTUAL_INDEP_APPEND1
		\\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
		\\ irule MUTUAL_INDEP_FRONT_APPEND  
       		\\ Q.EXISTS_TAC `[p_space p DIFF h]`
		\\  once_rewrite_tac[APPEND_ASSOC]
       		\\ irule MUTUAL_INDEP_APPEND1
		\\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺
           	       (compl_list p L2 ⧺ (compl_list p L4 ⧺ (L1 ⧺ ([h] ⧺ (L2 ⧺ L4))))) =
		       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
           	       compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4`
                   >-( rw [APPEND])
	        \\ rw []) 	   
\\ sg`NOR p L4 ∩ PATH p L1 ∩ NAND p L2 = PATH p L1 ∩ NAND p L2 ∩ NOR p L4 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ ntac 2 POP_ORW
\\ sg `PATH p (p_space p DIFF h::L1) ∩ NOR p L4 ∩  (PATH p L1 ∩ NAND p L2 ∩ NOR p L4) =
       PATH p (p_space p DIFF h::L1) ∩ NAND p L2 ∩ NOR p L4 `
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`p_space p DIFF h::L1`, `L4`])
\\ rw []
\\ sg `(∀y. ((y = p_space p DIFF h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L4 ⇒
             y ∈ events p)`
   >-( metis_tac [EVENTS_COMPL])
\\ sg `  MUTUAL_INDEP p (compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L4)) ⧺
         p_space p DIFF h::L1 ⧺ L2 ⧺ L4) `
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ rw [P_SPACE_DIFF]
	\\ sg `h ∩ p_space p = h `
	   >-(metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE])
	\\ POP_ORW
	\\ rw []
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L4 ⧺
               p_space p DIFF h::L1 ⧺ [h] ⧺ L2 ⧺ L4 =
	       compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L4 ⧺
               p_space p DIFF h::L1 ⧺ h::L2 ⧺ L4`
	   >-( rw [APPEND])
	\\ POP_ORW
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
               compl_list p L4 ⧺ L1 ⧺ [h] ⧺ L2 ⧺ L4 =
	       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
               compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4`	
           >-( rw [APPEND])
	\\ rw [])	
\\ sg `prob p (PATH p (p_space p DIFF h::L1) ∩ NAND p L2 ∩ NOR p L4) =
        prob p (PATH p (p_space p DIFF h::L1)) * prob p (NAND p L2) *
        prob p (NOR p L4)`
   >-( metis_tac [])
\\ POP_ORW
\\ sg `(p_space p DIFF h) ∩ NAND p L2 = PATH p [p_space p DIFF h] ∩ NAND p L2`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( rw [EVENTS_COMPL])
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1`
	\\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
               compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4=
	       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
               compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L4`	
           >-( rw [APPEND])
	\\ rw [])	
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( rw [EVENTS_COMPL])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L4))`
	\\ rw [])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` h::L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ h::L2 ⧺ L4)`
	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L4))`
	\\ rw []
        \\ sg `compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L4)) ⧺
               [p_space p DIFF h] ⧺ L1 ⧺ L2 ⧺ L4 =
	       compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L4)) ⧺
               p_space p DIFF h::L1 ⧺ L2 ⧺ L4`	
           >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1 ⧺ h::L2 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*    AND INTER NAND INTER NAND INTER OR     *)
(*-------------------------------------------*)

val AND_INTER_NAND_INTER_NAND_INTER_OR = store_thm("AND_INTER_NAND_INTER_NAND_INTER_OR",
``!p L2 L1 L3 L4. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3 ++ L4) ==> y IN events p) /\ ~NULL L1 /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L3 ++ L4) ++ L1 ++ L2 ++ L3 ++ L4)) 
            ==> (prob p (PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4) =
       	         prob p (PATH p L1) * prob p (NAND p L2) * prob p (NAND p L3) * prob p (BIG_UNION p L4))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]    
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS, PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg ` BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩ NAND p L2 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,PATH_IN_EVENTS, 
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `(p_space p DIFF h) = PATH p [(p_space p DIFF h)]`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 `
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4` 
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                         compl_list p L3 ⧺ compl_list p L4` 
	\\ rw [])
   >-( rw [EVENTS_COMPL])
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4 ⧺
	                 L1 ⧺ h::L2 ⧺ L3 ⧺ L4` 
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1` 
	\\ rw []
	\\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4  ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4  =
	       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4  ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
	   >-( rw [APPEND])
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩ PATH p [p_space p DIFF h] =
       PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ BIG_UNION p L4`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `BIG_UNION p L4 ∩ NAND p L3 ∩ PATH p L1 ∩  NAND p L2 =
       PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ BIG_UNION p L4 ∩
           (PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4) =
       PATH p (p_space p DIFF h::L1) ∩  NAND p L2 ∩ NAND p L3 ∩  BIG_UNION p L4`
    >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
\\ POP_ORW
\\ sg `PATH p (p_space p DIFF h::L1) ∩ NAND p L3 ∩ BIG_UNION p L4 =
       PATH p (p_space p DIFF h::L1) ∩ BIG_UNION p L4 ∩ NAND p L3 `     
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NAND]
\\ rw []
       >-( metis_tac [EVENTS_COMPL])
       >-( metis_tac [])
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [compl_list_def]
       	   \\ fs [GSYM compl_list_def]
	   \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L2`
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1`
       	   \\ rw []
	   \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2`
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L4`
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	   \\ Q.ABBREV_TAC `Y = compl_list p L3 ⧺ (compl_list p L4)`
	   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ Q.UNABBREV_TAC `X`
	   \\ Q.UNABBREV_TAC `Y`
	   \\ rw []
	   \\ Q.ABBREV_TAC `Y = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                                compl_list p L3 ⧺ compl_list p L4 ++ L1`
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `h::L2 ⧺ L3`
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ Q.UNABBREV_TAC `Y`
	   \\ rw []
	   \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                  compl_list p L3 ⧺ compl_list p L4  ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4 =
		  compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
                  compl_list p L3 ⧺ compl_list p L4  ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
	      >-( rw [APPEND])
	   \\ rw [])
\\ POP_ORW
\\ sg `prob p (PATH p L1 ∩ NAND p L2 ∩ NAND p L3 ∩ BIG_UNION p L4) =
       prob p (PATH p L1) * prob p (NAND p L2) * prob p (NAND p L3) * prob p (BIG_UNION p L4)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 7 (once_rewrite_tac[GSYM APPEND_ASSOC]) 
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`       
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                           compl_list p L3 ⧺ compl_list p L4  ⧺ L1`			   
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ Q.UNABBREV_TAC `X`
       \\ rw []
       \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4  ⧺ L1 ⧺ [h] ⧺ L2 ⧺ L3 ⧺ L4  =
	      compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
              compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4`
          >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW  
\\ sg `prob p (PATH p (p_space p DIFF h::L1) ∩ NAND p L2 ∩ NAND p L3 ∩  BIG_UNION p L4) =
       prob p (PATH p (p_space p DIFF h::L1)) * prob p (NAND p L2)  * prob p (NAND p L3) *
       prob p (BIG_UNION p L4)`
   >-( first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h::L1)`, `L3`, `L4`])
       \\ rw []
       \\ sg `(∀y. (((y = p_space p DIFF h ∨ MEM y L1) ∨ MEM y L2) ∨ MEM y L3) ∨ MEM y L4 ⇒ y ∈ events p)`
          >-( metis_tac [EVENTS_COMPL])
       \\ sg ` MUTUAL_INDEP p (compl_list p (p_space p DIFF h::(L1 ⧺ L2 ⧺ L3 ⧺ L4)) ⧺
                p_space p DIFF h::L1 ⧺ L2 ⧺ L3 ⧺ L4)`
	  >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ rw [P_SPACE_DIFF]
	      \\ sg `h ∩ p_space p = h `
	         >-( metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
	      \\ POP_ORW
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                                   compl_list p L4  ⧺ p_space p DIFF h::L1 `
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ Q.UNABBREV_TAC `X`
	      \\ sg `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
              	     compl_list p L4 ⧺ p_space p DIFF h::L1 ⧺ [h] ⧺ L2 ⧺ L3 ⧺ L4 =
	             compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
           	     compl_list p L4 ⧺ p_space p DIFF h::L1 ⧺   h::L2 ⧺ L3 ⧺ L4`
		 >-( rw [APPEND])
              \\ POP_ORW
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ Q.ABBREV_TAC `X =  L1 ⧺ ([h] ⧺ (L2 ⧺ (L3 ⧺ L4)))`
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ Q.UNABBREV_TAC `X`
	      \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
                    compl_list p L3 ⧺ compl_list p L4 ⧺
           	    (L1 ⧺ ([h] ⧺ (L2 ⧺ (L3 ⧺ L4)))) =
	   	    (compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
           	    compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4)`
		 >-( rw [APPEND])
	      \\ rw [])
       \\  metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-( metis_tac [])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ Q.ABBREV_TAC `X = L1 ⧺ (h::L2 ⧺ L3 ⧺ L4)`
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L2 ⧺ compl_list p L3 ⧺ compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC ` compl_list p L1`
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
	\\ rw []
        \\ sg `compl_list p L1 ⧺ [p_space p DIFF h] ⧺ compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4  ⧺ L1 ⧺ h::L2 ⧺ L3 ⧺ L4  =
	       compl_list p L1 ⧺ p_space p DIFF h::compl_list p L2 ⧺
               compl_list p L3 ⧺ compl_list p L4 ⧺ L1 ⧺ h::L2 ⧺  L3 ⧺ L4 `
          >-( rw [APPEND])
        \\ rw [])
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h::L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ h::L2 ⧺ L3 ⧺ L4)`
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------------------*)  
(*       NAND INTER NAND INTER OR            *)
(*-------------------------------------------*)

val NAND_INTER_NAND_INTER_OR = store_thm("NAND_INTER_NAND_INTER_OR",
``!p L1 L2 L3. prob_space p /\ (!y. MEM y (L1 ++ L2 ++ L3) ==> y IN events p) /\
	    (MUTUAL_INDEP p (compl_list p (L1 ++ L2 ++ L3) ++ L1 ++ L2 ++ L3)) 
            ==> (prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3) =
       	         prob p (NAND p L1) * prob p (NAND p L2) * prob p (BIG_UNION p L3))``,

GEN_TAC
\\ Induct
>-( rw [NAND_DEF, gate_list_def, FTree_def]
    \\ rw [PROB_EMPTY])
\\ rw [NAND_DEF, gate_list_def, FTree_def]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ rw [GSYM FTree_def]
\\ rw [GSYM NAND_DEF]
\\ rw [FTree_def]
\\ sg `BIG_UNION p L3 ∩ NAND p L2 ∩ (p_space p DIFF h) IN events p`
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL])
\\ sg `BIG_UNION p L3 ∩ NAND p L2 ∩ NAND p L1 IN events p `
   >-( metis_tac [NAND_DEF, BIG_UNION_IN_EVENTS, FT_NAND_IN_EVENTS,
                  NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER])	  
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [FT_NAND_IN_EVENTS, NAND_DEF])
\\ sg `(p_space p DIFF h) = PATH p [(p_space p DIFF h)]`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE, EVENTS_COMPL])
\\ POP_ORW
\\ sg `BIG_UNION p L3 ∩ NAND p L2 ∩ PATH p [p_space p DIFF h] =
       PATH p [p_space p DIFF h] ∩ BIG_UNION p L3 ∩ NAND p L2 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3 ⧺ h::L1 ⧺ L2`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])

\\ sg `prob p (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3) =
       prob p (NAND p L1) * prob p (NAND p L2) * prob p (BIG_UNION p L3)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h]`
       \\ rw []
       \\ sg `p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺
                compl_list p L3 ⧺ [h] ⧺ L1 ⧺ L2 ⧺ L3) =
	      p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2  ⧺
                compl_list p L3 ⧺ h::L1 ⧺ L2 ⧺ L3)	`
          >-( rw [APPEND])
	\\ rw [])
\\ sg `BIG_UNION p L3 ∩ NAND p L2 ∩ NAND p L1 = NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ ntac 2 POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC ` compl_list p L2 ⧺ compl_list p L3 ⧺ h::L1 ⧺ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ sg `PATH p [p_space p DIFF h] ∩ BIG_UNION p L3 ∩ NAND p L2 ∩
       (NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3) =
       PATH p [p_space p DIFF h] ∩  NAND p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NAND_INTER_OR]
\\ rw []
   >-( metis_tac [EVENTS_COMPL])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ rw [P_SPACE_DIFF]
 	\\ sg `h ∩ p_space p = h `
 	   >-( metis_tac [INTER_COMM, INTER_ASSOC, INTER_PSPACE])
        \\ POP_ORW
	\\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ Q.ABBREV_TAC `X = compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3`
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.UNABBREV_TAC `X`
        \\ sg `p_space p DIFF h::
               (compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺ [h] ⧺
                L1 ⧺ L2 ⧺ L3) =
		p_space p DIFF h::(compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺ h::L1 ⧺ L2 ⧺ L3)`
          >-( rw [APPEND])
	\\ rw [])	
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( rw [EVENTS_COMPL])
   >-(  fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 ⧺ compl_list p L3 ⧺
                         h::L1 ⧺ L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

			(*--------------------------------------------*)  
			(*     Cause-Consequence Diagram Theorems     *)
			(*--------------------------------------------*)

(*---------------------------*)  
(*  DECISION BOX WITH FT OR  *)
(*---------------------------*)

val DECISION_BOX_WITH_FT_OR = store_thm("DECISION_BOX_WITH_FT_OR",
``!p X L. prob_space p /\  ~NULL L /\ (∀x'. MEM x' L ⇒ x' ∈ events p) /\
     	  MUTUAL_INDEP p L ==> 
  (prob p (DECISION_BOX p X  (FTree p (NOT (OR (gate_list L))), FTree p (OR (gate_list L)))) =
          if X = 0 then 1 - PROD_LIST ((PROB_LIST p (compl_list p L)))
  	  else if X = 1 then PROD_LIST (PROB_LIST p (compl_list p L))
  	  else 1)``,
rw []
>-( rw [DECISION_BOX_DEF]
    \\ DEP_REWRITE_TAC [OR_gate_thm]
    \\ rw [OR_lem7])
>-( rw [DECISION_BOX_DEF]
    \\ rw [FTree_def]
    \\ rw [GSYM NOR_FT_gate_def]
    \\ DEP_REWRITE_TAC [NOR_gate_thm]
    \\ rw [OR_lem7])
>-( rw [DECISION_BOX_DEF]
    \\ rw [PROB_UNIV])
\\ rw [DECISION_BOX_DEF]
\\ rw [PROB_EMPTY]);
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------*)  
(* DECISION BOX WITH FT NOR  *)
(*---------------------------*)

val DECISION_BOX_WITH_FT_NOR = store_thm("DECISION_BOX_WITH_FT_NOR",
``!p X L. prob_space p /\  ~NULL L /\ (∀x'. MEM x' L ⇒ x' ∈ events p) /\
     	  MUTUAL_INDEP p L ==> 
  (prob p (DECISION_BOX p X (FTree p (OR (gate_list L)), FTree p (NOT (OR (gate_list L))))) =
   if X = 1 then 1 - PROD_LIST (PROB_LIST p (compl_list p L))
   else if X = 0 then PROD_LIST (PROB_LIST p (compl_list p L))
   else 1)``,
rw []
>-( rw [DECISION_BOX_DEF]
    \\ DEP_REWRITE_TAC [OR_gate_thm]
    \\ rw [OR_lem7])
>-( rw [DECISION_BOX_DEF]
    \\ rw [FTree_def]
    \\ rw [GSYM NOR_FT_gate_def]
    \\ DEP_REWRITE_TAC [NOR_gate_thm]
    \\ rw [OR_lem7])
>-( rw [DECISION_BOX_DEF]
    \\ rw [PROB_UNIV])    
\\ rw [DECISION_BOX_DEF]
\\ rw [PROB_EMPTY]);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------*)  
(*  DECISION BOX WITH FT AND  *)
(*----------------------------*)

val DECISION_BOX_WITH_FT_AND = store_thm("DECISION_BOX_WITH_FT_AND",
``!p X L. prob_space p /\  ~NULL L /\ (∀x'. MEM x' L ⇒ x' ∈ events p) /\
     	  MUTUAL_INDEP p L ==> 
  (prob p (DECISION_BOX p X (FTree p (NOT (AND (gate_list L))), FTree p (AND (gate_list L)))) =
   if X = 0 then PROD_LIST (PROB_LIST p L)
   else if X = 1 then 1 - PROD_LIST (PROB_LIST p L)
   else 1)``,
rw []
>-( rw [DECISION_BOX_DEF]
    \\ DEP_REWRITE_TAC [AND_gate_thm]
    \\ rw [])
>-( rw [DECISION_BOX_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw [])
>-( rw [DECISION_BOX_DEF]
    \\ rw [PROB_UNIV])     
\\ rw [DECISION_BOX_DEF]
\\ rw [PROB_EMPTY]);
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------*)  
(*  DECISION BOX WITH FT NAND  *)
(*-----------------------------*)

val DECISION_BOX_WITH_FT_NAND = store_thm("DECISION_BOX_WITH_FT_NAND",
``!p X L. prob_space p /\  ~NULL L /\ (∀x'. MEM x' L ⇒ x' ∈ events p) /\
     	  MUTUAL_INDEP p L ==> 
  (prob p (DECISION_BOX p X (FTree p (AND (gate_list L)), FTree p (NOT (AND (gate_list L))))) =
   if X = 0 then 1 - PROD_LIST (PROB_LIST p L) 
   else if X = 1 then PROD_LIST (PROB_LIST p L)
   else 1)``,
rw []
>-( rw [DECISION_BOX_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw [])
>-( rw [DECISION_BOX_DEF]
    \\ DEP_REWRITE_TAC [AND_gate_thm]
    \\ rw [])
>-( rw [DECISION_BOX_DEF]
    \\ rw [PROB_UNIV])    
\\ rw [DECISION_BOX_DEF]
\\ rw [PROB_EMPTY]);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs AND then OR  *)
(*---------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_10 =
    store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_10",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   (1 - PROD_LIST (PROB_LIST p L1)) * (1 − PROD_LIST (PROB_LIST p (compl_list p L2))))``,

rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ rw [OR_gate_eq_BIG_UNION]
    \\ rw [INTER_COMM]
    \\ DEP_REWRITE_TAC [OR_INTER_NAND]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_append_sym
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L2 ⧺ L1`
       	   \\ once_rewrite_tac[APPEND_ASSOC]
       	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw []
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` compl_list p L1 ++ compl_list p L2 `
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ rw [])   
    \\ DEP_REWRITE_TAC [GSYM OR_gate_eq_BIG_UNION]
    \\ rw []
    \\ DEP_REWRITE_TAC [OR_gate_thm]
    \\ rw []
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	    \\ Q.EXISTS_TAC ` compl_list p (L1 ⧺ L2) ⧺ L1`
	    \\ rw [])
     \\ rw [OR_lem7]
     \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_01 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_01",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p L1) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,

rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ rw [AND_gate_eq_PATH]
    \\ DEP_REWRITE_TAC [AND_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2 `
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1 `
    	   \\ once_rewrite_tac[APPEND_ASSOC]
    	   \\ rw [])
    \\ disj2_tac
    \\ DEP_REWRITE_TAC [PROB_PATH]
    \\ rw []
    \\ irule MUTUAL_INDEP_FRONT_APPEND  
    \\ Q.EXISTS_TAC `L2 `
    \\ irule MUTUAL_INDEP_append_sym
    \\ irule MUTUAL_INDEP_FRONT_APPEND  
    \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
    \\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_00 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_00",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p L1) * (1 − PROD_LIST (PROB_LIST p (compl_list p L2))))``,
   rw []
    \\  rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
    \\ DEP_REWRITE_TAC [AND_INTER_OR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ++ L2) `
    	   \\ once_rewrite_tac[APPEND_ASSOC]
    	   \\ rw [])
     \\ DEP_REWRITE_TAC [PROB_PATH]
     \\ rw []
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` L2 `
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ++ L2) `
	   \\ rw [])
     \\ disj2_tac
     \\ rw [GSYM OR_gate_eq_BIG_UNION]
     \\ DEP_REWRITE_TAC [OR_gate_thm]
     \\ rw []
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	    \\ Q.EXISTS_TAC ` compl_list p (L1 ⧺ L2) ⧺ L1`
	    \\ rw [])
     \\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_11 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_11",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   (1 - PROD_LIST (PROB_LIST p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,

    rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ DEP_REWRITE_TAC [NAND_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L1 ⧺ L2`
       	   \\ irule MUTUAL_INDEP_append_sym 
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NAND]	   
    \\ rw []
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` compl_list p L1 ++ compl_list p L2 `
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ rw [])
     \\ disj2_tac
     \\ DEP_REWRITE_TAC [PROB_NOR]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC ` compl_list p L1 `
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC `L1 ⧺ L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_02 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_02",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 2 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p L1))``,

     rw [DECISION_BOX_DEF]
     \\ rw [CONSEQ_PATH_DEF]
     \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
     \\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
     \\ sg `PATH p L1 ∩ p_space p = PATH p L1`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, PATH_IN_EVENTS])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [PROB_PATH]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 `
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC ` L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_12 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_OR_12",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 2 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   (1 - PROD_LIST (PROB_LIST p L1)))``,

    rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ sg `NAND p L1 ∩ p_space p = NAND p L1`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, FT_NAND_IN_EVENTS, NAND_DEF])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [PROB_NAND]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 `
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC ` L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs OR then AND  *)
(*---------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_00 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_00",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [ DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
  	    DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))]) =
   (1 − PROD_LIST (PROB_LIST p (compl_list p L2))) * PROD_LIST (PROB_LIST p L1))``,

REPEAT GEN_TAC
\\ sg `CONSEQ_PATH p
       [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
        DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))] =
       CONSEQ_PATH p
       [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
        DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]`
    >-( rw [INTER_COMM, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
    \\ POP_ORW
    \\ rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
    \\ DEP_REWRITE_TAC [AND_INTER_OR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ++ L2) `
    	   \\ once_rewrite_tac[APPEND_ASSOC]
    	   \\ rw [])
     \\ DEP_REWRITE_TAC [PROB_PATH]
     \\ rw []
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` L2 `
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ++ L2) `
	   \\ rw [])
     \\ rw [GSYM OR_gate_eq_BIG_UNION]
     \\ DEP_REWRITE_TAC [OR_gate_thm]
     \\ rw []
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	    \\ Q.EXISTS_TAC ` compl_list p (L1 ⧺ L2) ⧺ L1`
	    \\ rw [])
     \\ rw [OR_lem7]
     \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_10 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_10",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [ DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
  	    DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))]) =
   PROD_LIST (PROB_LIST p (compl_list p L2)) *  PROD_LIST (PROB_LIST p L1))``,

REPEAT GEN_TAC
\\ sg `CONSEQ_PATH p
       [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
        DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))] =
       CONSEQ_PATH p
       [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
        DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]`
    >-( rw [INTER_COMM, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
    \\ POP_ORW
    \\  rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ rw [AND_gate_eq_PATH]
    \\ DEP_REWRITE_TAC [AND_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2 `
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1 `
    	   \\ once_rewrite_tac[APPEND_ASSOC]
    	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_PATH]
    \\ rw []
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2 `
    	   \\ irule MUTUAL_INDEP_append_sym
   	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
    	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
   	   \\ rw [])
    \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_01 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_01",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [ DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
  	    DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))]) =
   (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *  (1 - PROD_LIST (PROB_LIST p L1)))``,

REPEAT GEN_TAC
\\ sg `CONSEQ_PATH p
       [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
        DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))] =
       CONSEQ_PATH p
       [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
        DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]`
    >-( rw [INTER_COMM, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
    \\ POP_ORW
    \\  rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ rw [OR_gate_eq_BIG_UNION]
    \\ rw [INTER_COMM]
    \\ DEP_REWRITE_TAC [OR_INTER_NAND]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_append_sym
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L2 ⧺ L1`
       	   \\ once_rewrite_tac[APPEND_ASSOC]
       	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw []
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` compl_list p L1 ++ compl_list p L2 `
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ rw [])
    \\ disj2_tac
    \\ DEP_REWRITE_TAC [GSYM OR_gate_eq_BIG_UNION]
    \\ rw []
    \\ DEP_REWRITE_TAC [OR_gate_thm]
    \\ rw []
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	    \\ Q.EXISTS_TAC ` compl_list p (L1 ⧺ L2) ⧺ L1`
	    \\ rw [])
     \\ rw [OR_lem7]
     \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_11 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_11",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [ DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
  	    DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))]) =
   PROD_LIST (PROB_LIST p (compl_list p L2)) *  (1 - PROD_LIST (PROB_LIST p L1)))``,

REPEAT GEN_TAC
\\ sg `CONSEQ_PATH p
       [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
        DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))] =
       CONSEQ_PATH p
       [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
        DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]`
    >-( rw [INTER_COMM, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
    \\ POP_ORW
    \\  rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ DEP_REWRITE_TAC [NAND_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L1 ⧺ L2`
       	   \\ irule MUTUAL_INDEP_append_sym 
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NAND]	   
    \\ rw []
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` compl_list p L1 ++ compl_list p L2 `
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ rw [])
     \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_12 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_12",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [ DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
  	    DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))]) =
   PROD_LIST (PROB_LIST p (compl_list p L2)))``,

     rw [DECISION_BOX_DEF]
     \\ rw [CONSEQ_PATH_DEF]
     \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
     \\ rw [GSYM NOR_DEF]
     \\ sg `NOR p L2 ∩ p_space p = NOR p L2`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, FT_NOR_IN_EVENTS, NOR_DEF])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [PROB_NOR]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `compl_list p L1  `
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC ` L1 ++ L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);  
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_02 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_AND_02",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ++ L2) ++ L1 ++ L2)  ⇒
  (prob p (CONSEQ_PATH p
          [ DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)));
  	    DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)))]) =
   (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,
   
     rw [DECISION_BOX_DEF]
     \\ rw [CONSEQ_PATH_DEF]
     \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
     \\ sg `FTree p (OR (gate_list L2)) ∩ p_space p = FTree p (OR (gate_list L2))`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, OR_lem3])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [OR_gate_thm]
     \\ rw []
     	>-( irule MUTUAL_INDEP_FRONT_APPEND
     	    \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) ⧺ L1`
     	    \\ rw [])
      \\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs AND then AND *)
(*---------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_00 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_00",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
  	  [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)))]) =
  PROD_LIST (PROB_LIST p L1) *  PROD_LIST (PROB_LIST p L2))``,

   rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ DEP_REWRITE_TAC [AND_gate_append]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
    \\ rw [AND_gate_eq_PATH]
    \\ DEP_REWRITE_TAC [PROB_PATH]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-(  irule MUTUAL_INDEP_FRONT_APPEND  
    	    \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
    	    \\ rw [])
    \\ REPEAT POP_ORW
    \\ Induct_on `L1`
       >-( rw [PROB_LIST_DEF , PROD_LIST_DEF])
    \\ rw [PROB_LIST_DEF , PROD_LIST_DEF]
    \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_10 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_10",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
  	  [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)))]) =
  (1 - PROD_LIST (PROB_LIST p L1)) * PROD_LIST (PROB_LIST p L2))``,

rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ rw [AND_gate_eq_PATH]
    \\ ONCE_REWRITE_TAC [INTER_COMM]
    \\ DEP_REWRITE_TAC [AND_INTER_NAND]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L2 ⧺ L1`
	   \\ irule MUTUAL_INDEP_append_sym
       	   \\ once_rewrite_tac[APPEND_ASSOC]
       	   \\ irule MUTUAL_INDEP_append_sym 
	   \\ rw []
	   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_PATH]
    \\ rw []
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) ⧺ L1`
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw []
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym 
    	   \\ rw [])
    \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_01 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_01",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
  	  [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)))]) =
  PROD_LIST (PROB_LIST p L1) *  (1 - PROD_LIST (PROB_LIST p L2)))``,

rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [AND_gate_eq_PATH]
    \\ rw [GSYM NAND_DEF]
    \\ DEP_REWRITE_TAC [AND_INTER_NAND]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_append_sym
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym
       	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1`
	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_PATH]
    \\ rw []
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym
 	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2  `
	   \\ rw [])
    \\ disj2_tac
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw []
    \\ irule MUTUAL_INDEP_FRONT_APPEND  
    \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) ⧺ L1`
    \\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_11 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_11",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
  	  [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)))]) =
  (1 - PROD_LIST (PROB_LIST p L1)) *  (1 - PROD_LIST (PROB_LIST p L2)))``,

    rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ DEP_REWRITE_TAC [NAND_INTER_NAND]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L1 ⧺ L2`
	   \\ irule MUTUAL_INDEP_append_sym 
    	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NAND]
    \\ rw []
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym 
    	   \\ rw [])
    \\ irule MUTUAL_INDEP_FRONT_APPEND  
    \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) ⧺ L1`
    \\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_12 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_12",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
  	  [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p L1))``,

     rw [DECISION_BOX_DEF]
     \\ rw [CONSEQ_PATH_DEF]
     \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
     \\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
     \\ sg `PATH p L1 ∩ p_space p = PATH p L1`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, PATH_IN_EVENTS])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [PROB_PATH]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 `
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC ` L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_12 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS_AND_THEN_AND_12",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
  	  [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	   DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)))]) =
   (1 - PROD_LIST (PROB_LIST p L1)))``,
   
    rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NAND_DEF]
    \\ sg `NAND p L1 ∩ p_space p = NAND p L1`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, FT_NAND_IN_EVENTS, NAND_DEF])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [PROB_NAND]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2 `
     \\ irule MUTUAL_INDEP_FRONT_APPEND  
     \\ Q.EXISTS_TAC ` L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs OR then OR   *)
(*---------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_00 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS__OR_THEN_OR_00",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   (1 − PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,
    rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF] 
    \\ rw [OR_gate_eq_BIG_UNION]
    \\ DEP_REWRITE_TAC [OR_INTER_OR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) `
    	   \\ rw [])
     \\ rw [GSYM OR_gate_eq_BIG_UNION]
     \\ DEP_REWRITE_TAC [OR_gate_thm]
     \\ rw []
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2`
	   \\ irule MUTUAL_INDEP_append_sym 
    	   \\ rw [])
        >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	    \\ Q.EXISTS_TAC ` compl_list p (L1 ⧺ L2) ⧺ L1`
	    \\ rw [])
     \\ rw [OR_lem7]
     \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_01 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS__OR_THEN_OR_01",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   (1 − PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,

rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ rw [OR_gate_eq_BIG_UNION]
    \\ DEP_REWRITE_TAC [OR_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2 `
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_APPEND1 
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1 `
    	   \\ once_rewrite_tac[APPEND_ASSOC]
    	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NOR]
    \\ rw []
     	>-( fs [COMPL_LIST_SPLIT]
     	    \\ irule MUTUAL_INDEP_FRONT_APPEND  
     	    \\ Q.EXISTS_TAC ` compl_list p L1 `
     	    \\ irule MUTUAL_INDEP_FRONT_APPEND  
     	    \\ Q.EXISTS_TAC `L1 ⧺ L2 `
     	    \\ irule MUTUAL_INDEP_append_sym
     	    \\ rw [])
    \\ disj2_tac
    \\ rw  [GSYM OR_gate_eq_BIG_UNION]
    \\ rw []
    \\ DEP_REWRITE_TAC [OR_gate_thm]
    \\ rw []
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L2 `
	   \\ irule MUTUAL_INDEP_append_sym
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L1 ⧺ compl_list p L2`
    	   \\ once_rewrite_tac[APPEND_ASSOC]
    	   \\ rw [])
    \\ rw [OR_lem7]
    \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_10 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS__OR_THEN_OR_10",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,

rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ rw [OR_gate_eq_BIG_UNION]
    \\ rw [INTER_COMM]
    \\ DEP_REWRITE_TAC [OR_INTER_NOR]
    \\ rw []
       >-( metis_tac [])
       >-( metis_tac [])
       >-( fs [COMPL_LIST_SPLIT]
       	   \\ irule MUTUAL_INDEP_append_sym
       	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `L1 `
	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
	   \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p L2 `
    	   \\ once_rewrite_tac[APPEND_ASSOC]
	   \\ irule MUTUAL_INDEP_APPEND1
    	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NOR]
    \\ rw []
     	>-( fs [COMPL_LIST_SPLIT]
     	    \\ irule MUTUAL_INDEP_FRONT_APPEND  
     	    \\ Q.EXISTS_TAC `compl_list p L2 ⧺ L1 ⧺ L2`
	    \\ irule MUTUAL_INDEP_append_sym
     	    \\ rw [])
    \\ rw  [GSYM OR_gate_eq_BIG_UNION]
    \\ rw []
    \\ DEP_REWRITE_TAC [OR_gate_thm]
    \\ rw []
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) ⧺ L1 `
    	   \\ rw [])
    \\ rw [OR_lem7]
    \\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_11 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS__OR_THEN_OR_11",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,

    rw [DECISION_BOX_DEF]
    \\ rw [CONSEQ_PATH_DEF]
    \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
    \\ rw [GSYM NOR_DEF]
    \\ DEP_REWRITE_TAC [NOR_INTER_NOR]
    \\ rw []
       >-( metis_tac [])    
       >-( metis_tac [])
       >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	   \\ Q.EXISTS_TAC ` L1 ++ L2`
	   \\ irule MUTUAL_INDEP_append_sym
    	   \\ rw [])
    \\ DEP_REWRITE_TAC [PROB_NOR]
    \\ rw []
     	>-( fs [COMPL_LIST_SPLIT]
     	    \\ irule MUTUAL_INDEP_FRONT_APPEND  
     	    \\ Q.EXISTS_TAC `compl_list p L2 ⧺ L1 ⧺ L2`
	    \\ irule MUTUAL_INDEP_append_sym
     	    \\ rw [])
    \\ fs [COMPL_LIST_SPLIT]
    \\ irule MUTUAL_INDEP_FRONT_APPEND  
    \\ Q.EXISTS_TAC ` compl_list p L1 `
    \\ irule MUTUAL_INDEP_FRONT_APPEND  
    \\ Q.EXISTS_TAC `L1 ⧺ L2 `
    \\ irule MUTUAL_INDEP_append_sym
    \\ rw []);  
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_12 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS__OR_THEN_OR_12",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   PROD_LIST (PROB_LIST p (compl_list p L1)))``,

     rw [DECISION_BOX_DEF]
     \\ rw [CONSEQ_PATH_DEF]
     \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
     \\ rw [GSYM NOR_DEF]
     \\ sg `NOR p L1 ∩ p_space p = NOR p L1`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, FT_NOR_IN_EVENTS, NOR_DEF])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [PROB_NOR]
     \\ rw []
     \\ fs [COMPL_LIST_SPLIT]
     \\ irule MUTUAL_INDEP_FRONT_APPEND
     \\ Q.EXISTS_TAC `compl_list p L2  ⧺ L1 ⧺ L2 `
     \\ irule MUTUAL_INDEP_append_sym
     \\ rw []);  
(*--------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_DECISION_BOXES_WITH_FTS_OR_THEN_OR_02 =
store_thm("CONSECUTIVE_DECISION_BOXES_WITH_FTS__OR_THEN_OR_02",
 ``!L2 L1 X Y p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (∀y. MEM y (L1 ⧺ L2) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2) ⧺ L1 ⧺ L2)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list L2))), FTree p (OR (gate_list L2)))]) =
   (1 - PROD_LIST (PROB_LIST p (compl_list p L1))))``,

     rw [DECISION_BOX_DEF]
     \\ rw [CONSEQ_PATH_DEF]
     \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
     \\ sg `FTree p (OR (gate_list L1)) ∩ p_space p = FTree p (OR (gate_list L1))`
       >-( metis_tac [INTER_COMM, INTER_PSPACE, OR_lem3])
     \\ POP_ORW
     \\ DEP_REWRITE_TAC [OR_gate_thm]
     \\ rw []
     	>-( irule MUTUAL_INDEP_FRONT_APPEND
     	    \\ Q.EXISTS_TAC ` L2 `
     	    \\ irule MUTUAL_INDEP_append_sym
     	    \\ irule MUTUAL_INDEP_FRONT_APPEND
     	    \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
     	    \\ rw [])
      \\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

		(*----------------------------------------------------------------*)  
		(*    Three Consecutive Decision Boxes With FTs 2 ORs & 1 AND     *)
		(*            000 001 010 011 100 101 110 111 	         	  *)
		(*----------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_000 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_000",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`
     	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
       \\ rw [])
\\ rw [OR_lem7]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_010 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_010",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [GSYM NOR_DEF]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_APPEND1
    	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L3)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1`
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3) ⧺ L1 ++ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ rw [GSYM COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_100 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_100",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [GSYM NOR_DEF]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym 
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L2 ++ L3)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3) ⧺ L1 ++ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [GSYM COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_110 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_110",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [GSYM NOR_DEF]
\\ DEP_REWRITE_TAC [AND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1 ++ L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw [APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L3)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_101 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_101",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ rw [GSYM NAND_DEF]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ NAND p L3 = NAND p L3 ∩ BIG_UNION p L2  ∩ NOR p L1  `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\  once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L2)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3) ⧺ L1 ++ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [GSYM COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_011 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_011",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) *  PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ rw [GSYM NAND_DEF]
\\ sg `BIG_UNION p L1 ∩ NOR p L2 ∩ NAND p L3 = NAND p L3 ∩ BIG_UNION p L1  ∩ NOR p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ++ compl_list p (L1)`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\  once_rewrite_tac[GSYM APPEND_ASSOC]
	\\  once_rewrite_tac[GSYM APPEND_ASSOC]
	\\  irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\  once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3) ⧺ L1 ++ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ rw [GSYM COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_001 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_001",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) *  (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
          (1 - PROD_LIST (PROB_LIST p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ rw [GSYM NAND_DEF]
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ NAND p L3 = NAND p L3 ∩ BIG_UNION p L1  ∩ BIG_UNION p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-(  irule MUTUAL_INDEP_FRONT_APPEND  
         \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`
	 \\ fs [compl_list_def])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]      
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_111 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_111",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p (compl_list p L1)) *  PROD_LIST (PROB_LIST p (compl_list p L2)) *
          (1 - PROD_LIST (PROB_LIST p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ rw [GSYM NAND_DEF]
\\ sg `NOR p L1 ∩ NOR p L2 ∩ NAND p L3 = NAND p L3 ∩ NOR p L1  ∩ NOR p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L2 ⧺ L3) ⧺ L1 ⧺ L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
     	\\ fs [compl_list_def])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L3) ⧺ L1 ⧺ L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1)`
	\\ fs [compl_list_def]) 
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1 ⧺ L2`
	\\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_002 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_002",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ p_space p = BIG_UNION p L1 ∩ BIG_UNION p L2`
   >-( rw [INTER_COMM, EVENTS_COMPL, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_OR]
\\ rw []
   >-( metis_tac []) 
   >-( metis_tac []) 
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ++ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_012 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_012",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg `BIG_UNION p L1 ∩ NOR p L2 ∩ p_space p = BIG_UNION p L1 ∩ NOR p L2`
   >-( rw [INTER_COMM, EVENTS_COMPL, NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_NOR]
\\ rw []
   >-( metis_tac []) 
   >-( metis_tac []) 
   >-(  irule MUTUAL_INDEP_append_sym
   	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ++ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
   	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L3)`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1)`
     	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p L3 ⧺ L1 ⧺ L2 ⧺ L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p L1`
\\ fs [COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_102 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_102",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg ` NOR p L1 ∩ BIG_UNION p L2 ∩ p_space p =  BIG_UNION p L2 ∩  NOR p L1`
   >-( rw [INTER_COMM, EVENTS_COMPL, NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_NOR]
\\ rw []
   >-( metis_tac []) 
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ rw []
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3)`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
   	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
   	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p ( L1 ++ L2 ++ L3)`
	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3) ⧺ L1 ⧺ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_112 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_112",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg ` NOR p L1 ∩ NOR p L2 ∩ p_space p =  NOR p L1 ∩  NOR p L2`
   >-( rw [INTER_COMM, EVENTS_COMPL, NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NOR_INTER_NOR]
\\ rw []
   >-( metis_tac []) 
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L3 ++ L1 ⧺ L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3) ⧺ L1 ⧺ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p L3 ⧺ L1 ⧺ L2 ⧺ L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p L1`
\\ fs [COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_022 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_022",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p (compl_list p L1))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ p_space p ∩ p_space p = BIG_UNION p L1`
   >-( rw [INTER_COMM, EVENTS_COMPL, NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_OR_OR_AND_122 = store_thm("THREE_DECISION_BOXES_OR_OR_AND_122",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p (compl_list p L1)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg ` NOR p L1 ∩ p_space p ∩ p_space p =  NOR p L1`
   >-( rw [INTER_COMM, EVENTS_COMPL, NOR_DEF, FT_NOR_IN_EVENTS, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L2 ++ L3) ⧺ L1 ⧺ L2 ⧺ L3`
\\ irule MUTUAL_INDEP_append_sym
\\ fs [COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

		(*----------------------------------------------------------------*)  
		(*    Three Consecutive Decision Boxes With FTs 2 ANDs & 1 OR     *)
		(*            000 001 010 011 100 101 110 111 	         	  *)
		(*----------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_000 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_000",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1) *  PROD_LIST (PROB_LIST p L2) *
	  (1 - PROD_LIST (PROB_LIST p (compl_list p L3))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ DEP_REWRITE_TAC [PATH_APPEND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
\\ sg `BIG_UNION p L3 ∩ PATH p (L1 ⧺ L2) = PATH p (L1 ⧺ L2) ∩ BIG_UNION p L3`
   >-( rw [INTER_COMM])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ⧺ L1 ⧺ L2`
     	\\ rw [])
\\ rw [OR_lem7]
\\ disj2_tac
\\ sg `PATH p (L1 ⧺ L2) = PATH p L1 ∩ PATH p L2 `
   >-( DEP_REWRITE_TAC [PATH_APPEND]
       \\ rw []
       	  >-( metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_AND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_001 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_001",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1) *  PROD_LIST (PROB_LIST p L2) *
	  PROD_LIST (PROB_LIST p (compl_list p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ DEP_REWRITE_TAC [PATH_APPEND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
\\ rw [GSYM NOR_DEF]
\\ sg `NOR p L3 ∩ PATH p (L1 ⧺ L2) = PATH p (L1 ⧺ L2) ∩ NOR p L3`
   >-( rw [INTER_COMM])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2) `
     	\\ fs [COMPL_LIST_SPLIT])
\\ disj2_tac
\\ sg `PATH p (L1 ⧺ L2) = PATH p L1 ∩ PATH p L2 `
   >-( DEP_REWRITE_TAC [PATH_APPEND]
       \\ rw []
       	  >-( metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_AND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`
     	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_010 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_010",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1) *  (1 - PROD_LIST (PROB_LIST p L2)) *
	  (1 - PROD_LIST (PROB_LIST p (compl_list p L3))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ sg `PATH p L1 ∩ NAND p L2 ∩ BIG_UNION p L3 =  PATH p L1 ∩ BIG_UNION p L3 ∩  NAND p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NAND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ⧺ L1 ⧺ L2`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L3`
        \\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
        \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_100 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_100",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)) *  PROD_LIST (PROB_LIST p L2) *
	  (1 - PROD_LIST (PROB_LIST p (compl_list p L3))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ sg `NAND p L1 ∩ PATH p L2 ∩ BIG_UNION p L3 =  PATH p L2 ∩ BIG_UNION p L3 ∩  NAND p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NAND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ rw []
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L2 ++ compl_list p L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ⧺ L1 ⧺ L2`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L3`
        \\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_111 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_111",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)) *  (1 - PROD_LIST (PROB_LIST p L2)) *
	  PROD_LIST (PROB_LIST p (compl_list p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ DEP_REWRITE_TAC [NAND_INTER_NAND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3`
        \\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`       
        \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_101 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_101",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)) *  PROD_LIST (PROB_LIST p L2) *
	  PROD_LIST (PROB_LIST p (compl_list p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ sg `NAND p L1 ∩ PATH p L2 ∩ NOR p L3 = PATH p L2 ∩ NAND p L1 ∩ NOR p L3 `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3`
        \\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`       
        \\ fs [COMPL_LIST_SPLIT])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_011 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_011",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1) *  (1 - PROD_LIST (PROB_LIST p L2)) *
	  PROD_LIST (PROB_LIST p (compl_list p L3)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NOR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L1 ⧺ L2 ⧺ L3`
        \\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2)`       
        \\ fs [COMPL_LIST_SPLIT])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_110 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_110",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)) *  (1 - PROD_LIST (PROB_LIST p L2)) *
	  (1 - PROD_LIST (PROB_LIST p (compl_list p L3))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ DEP_REWRITE_TAC [NAND_INTER_NAND_INTER_OR]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ⧺ L1 ⧺ L2`
     	\\ rw [])
\\ rw [OR_lem7]
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_002 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_002",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1) *  PROD_LIST (PROB_LIST p L2))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `PATH p L1 ∩ PATH p L2 ∩ p_space p = PATH p L1 ∩ PATH p L2`
   >-( rw [INTER_COMM, EVENTS_COMPL, EVENTS_INTER, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_AND]
\\ rw []
    >-( metis_tac [])
    >-( metis_tac [])
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L3`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ++ L3) `
     	\\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_012 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_012",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1) *  (1 - PROD_LIST (PROB_LIST p L2)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ sg `PATH p L1 ∩ NAND p L2 ∩ p_space p = PATH p L1 ∩ NAND p L2`
   >-( rw [INTER_COMM, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, EVENTS_INTER, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
    >-( metis_tac [])
    >-( metis_tac [])
    >-( irule MUTUAL_INDEP_append_sym
    	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L2 ⧺ L3`
        \\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p L3`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p L1`
        \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L3`
        \\ irule MUTUAL_INDEP_append_sym
        \\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ⧺ L1`       
        \\ fs [COMPL_LIST_SPLIT])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L2 ⧺ L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_102 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_102",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)) *  PROD_LIST (PROB_LIST p L2))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ sg `NAND p L1 ∩ PATH p L2 ∩ p_space p = PATH p L2 ∩ NAND p L1`
   >-( rw [INTER_COMM, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, EVENTS_INTER, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ⧺ L3) ++ L1`
       \\ rw []
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_112 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_112",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)) *  (1 - PROD_LIST (PROB_LIST p L2)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ sg `NAND p L1 ∩ NAND p L2 ∩ p_space p = NAND p L1 ∩ NAND p L2`
   >-( rw [INTER_COMM, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, EVENTS_INTER, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_NAND]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3) ⧺ L1 ⧺ L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L2 ⧺ L3`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
       \\ rw [])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3) ++ L1`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_022 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_022",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          PROD_LIST (PROB_LIST p L1))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ sg `PATH p L1 ∩ p_space p  ∩ p_space p = PATH p L1`
   >-( rw [INTER_COMM, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, EVENTS_INTER, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L2 ⧺ L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

val THREE_DECISION_BOXES_AND_AND_OR_122 = store_thm("THREE_DECISION_BOXES_AND_AND_OR_122",
 ``!L1 L2 L3 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3) ⧺ L1 ⧺ L2 ++ L3)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L1))), FTree p (AND (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L2))), FTree p (AND (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L3))), FTree p (OR (gate_list L3)))]) =	  
          (1 - PROD_LIST (PROB_LIST p L1)))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ sg `NAND p L1 ∩ p_space p  ∩ p_space p = NAND p L1`
   >-( rw [INTER_COMM, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, EVENTS_INTER, PATH_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `L2 ⧺ L3`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3)`       
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

		(*----------------------------------------------------------------*)  
		(*    FOUR Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs     *)
		(*         0000 0001 0010 0011 0100 0101 0110 0111 		  *)
		(*  	   1000 1001 1010 1011 1100 1101 1110 1111                *)
		(*----------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0000)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0000 = store_thm("FOUR_DECISION_BOXES_0000",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4)  /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ sg `FTree p (AND (gate_list L3)) ∩ FTree p (AND (gate_list L4)) = FTree p (AND (gate_list (L3 ++L4)))`
   >-( DEP_REWRITE_TAC [AND_gate_append]
       \\ rw []
       	  >-( metis_tac [])    
       \\ metis_tac [])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ rw [INTER_COMM]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `(1 − PROD_LIST (PROB_LIST p (compl_list p L1))) *
        (1 − PROD_LIST (PROB_LIST p (compl_list p L2))) *
        PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =
        PROD_LIST (PROB_LIST p (L3 ++ L4)) * (1 − PROD_LIST (PROB_LIST p (compl_list p L1))) *
        (1 − PROD_LIST (PROB_LIST p (compl_list p L2))) `
   >-( sg `PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =  PROD_LIST (PROB_LIST p (L3 ++ L4)) `
       >-( REPEAT POP_ORW
       	   \\ Induct_on `L3`
       	       >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
	       	   \\ REAL_ARITH_TAC)
           \\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
       	   \\ rw [GSYM REAL_MUL_ASSOC])
       \\ rw [GSYM REAL_MUL_ASSOC]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
\\ rw []);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0100)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0100 = store_thm("FOUR_DECISION_BOXES_0100",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4)  /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ sg `FTree p (AND (gate_list L3)) ∩ FTree p (AND (gate_list L4)) = FTree p (AND (gate_list (L3 ++L4)))`
   >-( DEP_REWRITE_TAC [AND_gate_append]
       \\ rw []
       	  >-( metis_tac [])    
       \\ metis_tac [])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ rw [INTER_COMM]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg ` (1 − PROD_LIST (PROB_LIST p (compl_list p L1))) *
        PROD_LIST (PROB_LIST p (compl_list p L2)) *
        PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =
        PROD_LIST (PROB_LIST p (L3 ++ L4)) * (1 − PROD_LIST (PROB_LIST p (compl_list p L1))) *
        PROD_LIST (PROB_LIST p (compl_list p L2)) `
   >-( sg `PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =  PROD_LIST (PROB_LIST p (L3 ++ L4)) `
       >-( REPEAT POP_ORW
       	   \\ Induct_on `L3`
       	       >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
	       	   \\ REAL_ARITH_TAC)
           \\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
       	   \\ rw [GSYM REAL_MUL_ASSOC])
       \\ rw [GSYM REAL_MUL_ASSOC]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_APPEND1
    	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1`
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
	\\ rw [])
\\ disj2_tac 
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1)`
\\ rw [GSYM COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1000)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1000 = store_thm("FOUR_DECISION_BOXES_1000",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4)  /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	 	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ sg `FTree p (AND (gate_list L3)) ∩ FTree p (AND (gate_list L4)) = FTree p (AND (gate_list (L3 ++L4)))`
   >-( DEP_REWRITE_TAC [AND_gate_append]
       \\ rw []
       	  >-( metis_tac [])    
       \\ metis_tac [])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ rw [INTER_COMM]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg ` PROD_LIST (PROB_LIST p (compl_list p L1)) *
        (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
        PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =
        PROD_LIST (PROB_LIST p (L3 ++ L4)) * PROD_LIST (PROB_LIST p (compl_list p L1)) *
        (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) `
   >-( sg `PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =  PROD_LIST (PROB_LIST p (L3 ++ L4)) `
       >-( REPEAT POP_ORW
       	   \\ Induct_on `L3`
       	       >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
	       	   \\ REAL_ARITH_TAC)
           \\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
       	   \\ rw [GSYM REAL_MUL_ASSOC])
       \\ rw [GSYM REAL_MUL_ASSOC]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym 
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [GSYM COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1100)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1100 = store_thm("FOUR_DECISION_BOXES_1100",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4)  /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	 	    
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ sg `FTree p (AND (gate_list L3)) ∩ FTree p (AND (gate_list L4)) = FTree p (AND (gate_list (L3 ++L4)))`
   >-( DEP_REWRITE_TAC [AND_gate_append]
       \\ rw []
       	  >-( metis_tac [])    
       \\ metis_tac [])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ rw [INTER_COMM]
\\ rw [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [GSYM NOR_DEF]
\\ sg ` PROD_LIST (PROB_LIST p (compl_list p L1)) *
        (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
        PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =
        PROD_LIST (PROB_LIST p (L3 ++ L4)) * PROD_LIST (PROB_LIST p (compl_list p L1)) *
        (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) `
   >-( sg `PROD_LIST (PROB_LIST p L3) * PROD_LIST (PROB_LIST p L4) =  PROD_LIST (PROB_LIST p (L3 ++ L4)) `
       >-( REPEAT POP_ORW
       	   \\ Induct_on `L3`
       	       >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
	       	   \\ REAL_ARITH_TAC)
           \\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
       	   \\ rw [GSYM REAL_MUL_ASSOC])
       \\ rw [GSYM REAL_MUL_ASSOC]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1 ++ L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw [APPEND_ASSOC]
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4)`
	\\ once_rewrite_tac [APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
     	\\ rw [GSYM COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
    	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
	\\ rw [])
\\ REPEAT POP_ORW
\\ Induct_on `L3`
   >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
       \\ REAL_ARITH_TAC)
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ sg `prob p h * PROD_LIST (PROB_LIST p (L3 ⧺ L4)) *
       PROD_LIST (PROB_LIST p (compl_list p L1)) *
       PROD_LIST (PROB_LIST p (compl_list p L2)) =
       prob p h * (PROD_LIST (PROB_LIST p (L3 ⧺ L4)) *
       PROD_LIST (PROB_LIST p (compl_list p L1)) *
       PROD_LIST (PROB_LIST p (compl_list p L2)))`
   >-( rw [REAL_MUL_ASSOC])
\\ POP_ORW
\\ fs []
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0010)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0010 = store_thm("FOUR_DECISION_BOXES_0010",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =		  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])	
    	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
    	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1 ++ compl_list p L2`
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2 ⧺ L3 `
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0001)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0001 = store_thm("FOUR_DECISION_BOXES_0001",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ PATH p L3 ∩ NAND p L4 =
       PATH p L3 ∩ NAND p L4 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1 ++ compl_list p L2 ++ compl_list p L3`
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0101)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0101 = store_thm("FOUR_DECISION_BOXES_0101",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L3`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1`
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1001)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1001 = store_thm("FOUR_DECISION_BOXES_1001",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3)  /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	 	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ PATH p L3 ∩ NAND p L4 =
       PATH p L3 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_APPEND1
    	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L2 ++ compl_list p L3`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1010)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1010 = store_thm("FOUR_DECISION_BOXES_1010",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ NAND p L3 ∩ PATH p L4 =
       PATH p L4  ∩  NAND p L3 ∩ BIG_UNION p L2 ∩ NOR p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L2 `
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []       
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0110)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0110 = store_thm("FOUR_DECISION_BOXES_0110",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ NOR p L2 ∩ NAND p L3 ∩ PATH p L4 =
       PATH p L4 ∩ NAND p L3 ∩ BIG_UNION p L1 ∩ NOR p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ++ L3`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_APPEND1	
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1 `
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []     
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0111)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0111 = store_thm("FOUR_DECISION_BOXES_0111",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =		  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [NAND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw [])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ⧺ L3 `
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1011)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1011 = store_thm("FOUR_DECISION_BOXES_1011",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ NAND p L3 ∩ NAND p L4 = NAND p L3 ∩ NAND p L4 ∩ BIG_UNION p L2 ∩ NOR p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac [])
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ Q.ABBREV_TAC `X = compl_list p L3 ⧺ compl_list p L4`
	\\ irule MUTUAL_INDEP_APPEND1
	\\ Q.ABBREV_TAC `Y = (L1 ⧺ (L2 ⧺ (L3 ⧺ L4)))`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ Q.UNABBREV_TAC `X`
	\\ Q.UNABBREV_TAC `Y`
	\\ rw [])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ⧺ L3 `
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1101)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1101 = store_thm("FOUR_DECISION_BOXES_1101",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac [])
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ Q.ABBREV_TAC `X = compl_list p L3 ⧺ compl_list p L4`
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_APPEND1
	\\ Q.ABBREV_TAC `Y = (L1 ⧺ (L2 ⧺ (L3 ⧺ L4)))`
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ Q.UNABBREV_TAC `X`
	\\ Q.UNABBREV_TAC `Y`
	\\ rw [])		
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1110)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1110 = store_thm("FOUR_DECISION_BOXES_1110",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)) * PROD_LIST (PROB_LIST p L4))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ NOR p L2 ∩ NAND p L3 ∩ PATH p L4 = PATH p L4 ∩  NAND p L3 ∩ NOR p L1 ∩ NOR p L2  `
   >-( metis_tac [INTER_COMM, INTER_ASSOC])
\\ POP_ORW  
\\ DEP_REWRITE_TAC [AND_INTER_NAND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac [])
    >-( Q.ABBREV_TAC `X = compl_list p (L4 ⧺ L3 ⧺ L1 ⧺ L2)`
    	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ Q.UNABBREV_TAC `X`
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ Q.ABBREV_TAC `X = compl_list p L3 ⧺ compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ Q.ABBREV_TAC `Y = (L1 ⧺ (L2 ⧺ (L3 ⧺ L4)))`
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ Q.UNABBREV_TAC `X`
	\\ Q.UNABBREV_TAC `Y`
	\\ rw [])		
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ⧺ L1 ⧺ L2 ⧺ L3`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1111)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1111 = store_thm("FOUR_DECISION_BOXES_1111",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [NAND_INTER_NAND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw [])	
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ⧺ L3 `
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ++ L3`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0011)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0011 = store_thm("FOUR_DECISION_BOXES_0011",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3)  /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)) * (1 - PROD_LIST (PROB_LIST p L4)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [NAND_INTER_NAND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
    	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_APPEND1 
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ rw [COMPL_LIST_SPLIT]
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ Q.ABBREV_TAC `X = L1 ⧺ (L2 ⧺ (L3 ⧺ L4))`
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ Q.UNABBREV_TAC `X `
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ⧺ L1 ⧺ L2 ⧺ L3`
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw [])
\\ REAL_ARITH_TAC);

(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0002)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0002 = store_thm("FOUR_DECISION_BOXES_0002",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ PATH p L3 ∩ p_space p =
       BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ PATH p L3`
   >-( rw [INTER_COMM]
       \\ metis_tac [INTER_ASSOC, EVENTS_COMPL, PATH_IN_EVENTS, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ sg `BIG_UNION p L1 ∩ BIG_UNION p L2 ∩ PATH p L3 = PATH p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
	\\ rw [])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0012)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0012 = store_thm("FOUR_DECISION_BOXES_0012",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =		  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg `p_space p ∩ NAND p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 = NAND p L3 ∩ BIG_UNION p L1 ∩ BIG_UNION p L2`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, PATH_IN_EVENTS, NAND_DEF, FT_NAND_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
    	\\ irule MUTUAL_INDEP_append_sym
    	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1 ++ compl_list p L2`
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0102)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0102 = store_thm("FOUR_DECISION_BOXES_0102",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ NOR p L2 ∩ PATH p L3 ∩ p_space p = BIG_UNION p L1 ∩ NOR p L2 ∩ PATH p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, PATH_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2`
	\\ rw []
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L3 ++ compl_list p L4`
	\\ rw []
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1`
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0112)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0112 = store_thm("FOUR_DECISION_BOXES_0112",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ NOR p L2 ∩ NAND p L3 ∩ p_space p = BIG_UNION p L1 ∩ NOR p L2 ∩ NAND p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ ONCE_REWRITE_TAC [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_append_sym
    	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2`
	\\ rw []
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1 `
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []     
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1002)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1002 = store_thm("FOUR_DECISION_BOXES_1002",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3)  /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	 	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           PROD_LIST (PROB_LIST p L3))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ PATH p L3 ∩ p_space p = NOR p L1 ∩ BIG_UNION p L2 ∩ PATH p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, PATH_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ sg `NOR p L1  ∩ BIG_UNION p L2 ∩ PATH p L3 = PATH p L3 ∩ BIG_UNION p L2 ∩ NOR p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L1`
	\\ rw []
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L2 ++ compl_list p L3 ++ compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1012)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1012 = store_thm("FOUR_DECISION_BOXES_1012",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))) *
           (1 - PROD_LIST (PROB_LIST p L3)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ NAND p L3 ∩ p_space p = NOR p L1 ∩ BIG_UNION p L2 ∩ NAND p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ sg `NOR p L1  ∩ BIG_UNION p L2 ∩ NAND p L3 = NAND p L3 ∩ BIG_UNION p L2 ∩ NOR p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `compl_list p L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
    	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `L1`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ⧺ L3 `
       \\ rw [])
\\ rw [OR_lem7]      
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1102)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1102 = store_thm("FOUR_DECISION_BOXES_1102",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 0 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           PROD_LIST (PROB_LIST p L3))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ NOR p L2 ∩ PATH p L3 ∩ p_space p = NOR p L1 ∩ NOR p L2 ∩ PATH p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, PATH_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ sg `NOR p L1 ∩ NOR p L2 ∩ PATH p L3 = PATH p L3 ∩ NOR p L1 ∩ NOR p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p L3 ⧺ compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
        \\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L1 ++ L2`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [COMPL_LIST_SPLIT])		
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC ` L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ⧺ L2`
        \\ rw [])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1112)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1112 = store_thm("FOUR_DECISION_BOXES_1112",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 1 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)) *
           (1 - PROD_LIST (PROB_LIST p L3)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ NOR p L2 ∩ NAND p L3 ∩ p_space p = NOR p L1 ∩ NOR p L2 ∩ NAND p L3`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ sg `NOR p L1 ∩ NOR p L2 ∩ NAND p L3 = NAND p L3 ∩ NOR p L1 ∩ NOR p L2`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NAND_INTER_NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( once_rewrite_tac[GSYM APPEND_ASSOC]
    	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `L4`
    	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [COMPL_LIST_SPLIT])	
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2`
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1 ++ L2 ⧺ L3 `
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L1)`
       \\ fs [COMPL_LIST_SPLIT])
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0022)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0022 = store_thm("FOUR_DECISION_BOXES_0022",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =		  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg `p_space p ∩ BIG_UNION p L1 ∩ BIG_UNION p L2 = BIG_UNION p L1 ∩ BIG_UNION p L2`
   >-( metis_tac [INTER_ASSOC, EVENTS_COMPL, EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_OR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ++ L4`
    	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0122)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0112 = store_thm("FOUR_DECISION_BOXES_0112",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ NOR p L2 ∩ p_space p ∩ p_space p = BIG_UNION p L1 ∩ NOR p L2`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_append_sym
    	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L3`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p L1`
	\\ rw []
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ++ L3 ++ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1)`
\\ fs [COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1022)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1022 = store_thm("FOUR_DECISION_BOXES_1022",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * (1 - PROD_LIST (PROB_LIST p (compl_list p L2))))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ BIG_UNION p L2 ∩ p_space p ∩ p_space p = NOR p L1 ∩ BIG_UNION p L2`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ sg `NOR p L1 ∩ BIG_UNION p L2 = BIG_UNION p L2  ∩ NOR p L1`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-(  irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `L3 ++ L4`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
    	\\ irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `L1`
	\\ rw []
    	\\ irule MUTUAL_INDEP_append_sym
	\\ irule MUTUAL_INDEP_FRONT_APPEND
     	\\ Q.EXISTS_TAC `compl_list p (L2 ⧺ L3 ⧺ L4)`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ fs [COMPL_LIST_SPLIT])	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4) ++ L1`
     	\\ rw [])
\\ rw [OR_lem7]
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])    
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1122)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1122 = store_thm("FOUR_DECISION_BOXES_1122",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)) * PROD_LIST (PROB_LIST p (compl_list p L2)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ NOR p L2 ∩ p_space p ∩ p_space p = NOR p L1 ∩ NOR p L2`
   >-( metis_tac [INTER_COMM, INTER_ASSOC, EVENTS_COMPL, NAND_DEF, FT_NAND_IN_EVENTS, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [NOR_INTER_NOR]
\\ rw []
    >-( metis_tac []) 
    >-( metis_tac []) 
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ⧺ L2 ⧺ L3 ⧺ L4`
    	\\ irule MUTUAL_INDEP_append_sym
	\\ fs [COMPL_LIST_SPLIT])	
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
       \\ irule MUTUAL_INDEP_append_sym
       \\ fs [COMPL_LIST_SPLIT])
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
\\ irule MUTUAL_INDEP_append_sym
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L1)`
\\ fs [COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (0222)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_0222 = store_thm("FOUR_DECISION_BOXES_0222",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 0 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           (1 - PROD_LIST (PROB_LIST p (compl_list p L1))))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `BIG_UNION p L1 ∩ p_space p  ∩ p_space p ∩ p_space p = BIG_UNION p L1`
   >-( metis_tac [INTER_COMM,  EVENTS_COMPL, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW	
\\ rw [GSYM OR_gate_eq_BIG_UNION]
\\ DEP_REWRITE_TAC [OR_gate_thm]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `L2 ⧺ L3 ⧺ L4`
	\\ irule MUTUAL_INDEP_append_sym
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
     	\\ Q.EXISTS_TAC `compl_list p (L1 ⧺ L2 ⧺ L3 ⧺ L4)`
     	\\ rw [])
\\ rw [OR_lem7]);
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------------------------*)  
(*  Consecutive Decision Boxes With FTs 2 ORs & 2 ANDs (1222)     *)
(*----------------------------------------------------------------*)

val FOUR_DECISION_BOXES_1222 = store_thm("FOUR_DECISION_BOXES_1222",
 ``!L2 L1 L3 L4 X1 X2 X3 X4 p.
     	 prob_space p /\ (~NULL L1) /\ (~NULL L2) /\ (~NULL L3) /\ (~NULL L4) /\
	 (∀y. MEM y (L1 ⧺ L2 ++ L3 ++ L4) ⇒ y ∈ events p) /\
	 MUTUAL_INDEP p (compl_list p (L1 ⧺ L2 ++ L3 ++ L4) ⧺ L1 ⧺ L2 ++ L3 ++ L4)  ⇒
  (prob p (CONSEQ_PATH p
            [DECISION_BOX p 1 (FTree p (NOT (OR (gate_list  L1))), FTree p (OR (gate_list L1)));
  	     DECISION_BOX p 2 (FTree p (NOT (OR (gate_list  L2))), FTree p (OR (gate_list L2)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L3))), FTree p (AND (gate_list L3)));
	     DECISION_BOX p 2 (FTree p (NOT (AND (gate_list L4))), FTree p (AND (gate_list L4)))]) =	  
           PROD_LIST (PROB_LIST p (compl_list p L1)))``,
rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_PATH_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM NAND_DEF]
\\ rw [GSYM NOR_DEF]
\\ rw  [OR_gate_eq_BIG_UNION, AND_gate_eq_PATH]
\\ sg `NOR p L1 ∩ p_space p ∩ p_space p ∩ p_space p = NOR p L1`
   >-( metis_tac [INTER_COMM, EVENTS_COMPL, NOR_DEF, FT_NOR_IN_EVENTS,
                  EVENTS_INTER, BIG_UNION_IN_EVENTS, INTER_PSPACE])
\\ POP_ORW	
\\ DEP_REWRITE_TAC [PROB_NOR]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (L2 ++ L3 ⧺ L4) ⧺ L1 ++ L2 ⧺ L3 ⧺ L4`
\\ irule MUTUAL_INDEP_append_sym
\\ fs [COMPL_LIST_SPLIT]);
(*--------------------------------------------------------------------------------------------------*)

				(*------------------------------------------*)  
				(*    N LEVEL CAUSE CONSEQUENCE ANALYSIS    *)
				(*------------------------------------------*)

val PROB_CONSEQ_PATH = store_thm("PROB_CONSEQ_PATH",
  ``!p L. prob_space p /\ ~NULL L /\ (!x'. MEM x' L ==> x'  IN  events p ) /\
          MUTUAL_INDEP p L ==>
	  (prob p (CONSEQ_PATH p L) =  PROD_LIST (PROB_LIST p L))``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ metis_tac []);
(*--------------------------------------------------------------------------------------------------*)

val PROB_N_LEVEL_DEC_BOXES = store_thm("PROB_N_LEVEL_DEC_BOXES",

 ``!p X Y N M.
         MUTUAL_INDEP p (N_DECISION_BOXES p (X::N) (Y::M)) /\ prob_space p /\
	 ~NULL (N_DECISION_BOXES p N M) /\ 
	 (!x'. MEM x' (N_DECISION_BOXES p (X::N) (Y::M)) ==> x'  IN  events p) ==>
	 prob p (CONSEQ_PATH p (N_DECISION_BOXES p (X::N) (Y::M))) =
	 prob p (CONSEQ_PATH p [DECISION_BOX p X Y]) *
	 prob p (CONSEQ_PATH p (N_DECISION_BOXES p N M))``,

rw []
\\ DEP_REWRITE_TAC [PROB_CONSEQ_PATH]
\\ rw [N_DECISION_BOXES_DEF]
   >-( fs [N_DECISION_BOXES_DEF]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `N_DECISION_BOXES p N M`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
   >-( fs [N_DECISION_BOXES_DEF]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[DECISION_BOX p X Y]`
       \\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

		(*------------------------------------------------------------*)
     		(* Power System Generic CCD Reliability and Energy Indices    *)
     		(*------------------------------------------------------------*)

			(*--------------------------------------*)
			(* Power System CCD Reliability Indices *)
			(*--------------------------------------*)

val PROB_CCD_X_DEF = Define
`PROB_CCD_X p (Path1::PathN) = prob p (CONSEQ_BOX p  (Path1::PathN))`;
(*--------------------------------------------------------------------------------------------------*)

val LOAD_INTERRUPTIONS_DEF = Define
`(LOAD_INTERRUPTIONS p [] [] = 0) /\ 
 (LOAD_INTERRUPTIONS p (PathN::PathNALL) (CN::CNs) =
 (PROB_CCD_X p PathN) * (&CN) + (LOAD_INTERRUPTIONS p PathNALL CNs))`;

val LIGHTNING  =  U 0x021AF;
val _ = Unicode.unicode_version {tmnm = "LOAD_INTERRUPTIONS", u = SUM^L^O^A^D^LIGHTNING};
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------*)
(* System Avergae Interruption Frequencey Index *)
(*----------------------------------------------*)

val SAIFI_DEF = Define
`SAIFI p PathNALL CNs = (∑𝑳𝑶𝑨𝑫↯  p PathNALL CNs) / (&SUM CNs)`;
(*--------------------------------------------------------------------------------------------------*)

val LOAD_TIME_INTERRUPTIONS_DEF = Define
`(LOAD_TIME_INTERRUPTIONS p [] [] [] = 0) /\ 
 (LOAD_TIME_INTERRUPTIONS p (PathN::PathNALL) (CN::CNs) (MTTR::MTTRs) =
 (PROB_CCD_X p PathN) * MTTR * (&CN) + (LOAD_TIME_INTERRUPTIONS p PathNALL CNs MTTRs))`;

val _ = Unicode.unicode_version {tmnm = "LOAD_TIME_INTERRUPTIONS", u = SUM^T^L^O^A^D^LIGHTNING};
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------------------------*)
(* System Avergae Interruption Duration Index   *)
(*----------------------------------------------*)

val SAIDI_DEF = Define
`SAIDI p PathNALL CNs MTTRs = (∑𝑻𝑳𝑶𝑨𝑫↯ p PathNALL CNs MTTRs) / &(SUM CNs)`;
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------*)
(* Customer Avergae Interruption Duration Index   *)
(*------------------------------------------------*)

val CAIDI_DEF = Define
`CAIDI p PathNALL CNs MTTRs  = (SAIDI p PathNALL CNs MTTRs)/(SAIFI  p PathNALL CNs)`;
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------*)
(* Average Service Availability Index   *)
(*--------------------------------------*)

val ASAI_DEF = Define
`ASAI p PathNALL CNs MTTRs =
((&(SUM CNs) * 8760) - ∑𝑻𝑳𝑶𝑨𝑫↯  p PathNALL CNs MTTRs)/(&(SUM CNs) * 8760)`;
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------*)
(* Average Service Unavailability Index *)
(*--------------------------------------*)

val ASUI_DEF = Define
`ASUI p PathNALL CNs MTTRs  = (∑𝑻𝑳𝑶𝑨𝑫↯ p PathNALL CNs MTTRs)/(&(SUM CNs) * 8760)`;
(*--------------------------------------------------------------------------------------------------*)

				(*---------------------------------*)
				(* Power System CCD Energy Indices *)
				(*---------------------------------*)

(*---------------------*)
(* Energy Not Supplied *)
(*---------------------*)

val ENS_DEF = Define
`(ENS [] [] [] p = 0) /\ 
 (ENS (La::LaN) (PathN::PathNALL) (MTTR::MTTRs) p =
 La * (PROB_CCD_X  p PathN) * MTTR + (ENS LaN PathNALL MTTRs p))`;
(*--------------------------------------------------------------------------------------------------*)

(*--------------------------------------*)
(* Average Service Curtailment Index    *)
(*--------------------------------------*)

val ASCI_DEF = Define
`ASCI p PathNALL LaN MTTRs CNs = (ENS LaN PathNALL MTTRs p)/(&(SUM CNs))`;
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------*)
(* Loss of Load Expectation   *)
(*----------------------------*)

val LOLE_DEF = Define
`(LOLE [] [] p = 0) /\ 
 (LOLE (PathN::PathNALL) (tk::tks) p = (PROB_CCD_X p PathN) * tk + (LOLE PathNALL tks p))`;
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------*)
(* Loss of Energy Expectation *)
(*----------------------------*)

val LOEE_DEF = Define
`(LOEE [] [] p = 0) /\ 
 (LOEE (PathN::PathNALL) (Ek::Eks) p = (PROB_CCD_X p PathN) * Ek + (LOEE PathNALL Eks p))`;
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------*)
(* Energy Index of Reliability *)
(*-----------------------------*)

val EIR_DEF = Define
`EIR p PathNALL Eks ET = 1 - (LOEE PathNALL Eks p)/(ET)`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

				(*----------------------------*)  
				(*   SML Automatic Functions  *)
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
    print("SAIFI" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Interruptions / System Customer" ^  "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun SAIDI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("SAIDI" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Hours / System Customer" ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun CAIDI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("CAIDI" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Hours / Customer Interruption" ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun ASAI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("ASAI" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun ASUI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("ASUI" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun ENS X =
let
    val value = HOL4_EVALUATION  X;
in
    print("ENS" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "MWh" ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun ASCI X =
let
    val value = HOL4_EVALUATION  X;
in
    print("ASCI" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "KWh / Customer. Year" ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun LOLE X =
let
    val value = HOL4_EVALUATION  X;
in
    print("LOLE" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "Days / Year" ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun LOEE X =
let
    val value = HOL4_EVALUATION  X;
in
    print("LOEE p.u." ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun EIR X =
let
    val value = HOL4_EVALUATION  X;
in
    print("EIR" ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ " " ^ "\n\n")
end;

val _ = export_theory();

(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
	(*------------------------------------------------------------------------------*)
		       (*--------------------------------------------------*)
			         (*--------------------------------*)
					  (*---------------*)
						********
