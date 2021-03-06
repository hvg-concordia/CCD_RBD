(* ========================================================================= *)
(* File Name: CCD_RBD.sml	          	                             *)
(*---------------------------------------------------------------------------*)
(*          Description: Cause Consequence Diagram Reliability Analysis      *)
(*	    		 based on Reliability Block Diagrams and Event       *)
(*                       Trees using Theorem Proving	  		     *)
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
	  "real_sigmaTheory", "cardinalTheory", "FTreeTheory", "ETreeTheory", "RBDTheory", "CCD_FTTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax lebesgueTheory real_sigmaTheory cardinalTheory
     FTreeTheory ETreeTheory RBDTheory CCD_FTTheory;

val _ = new_theory "CCD_RBD";

(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Definitions   *)
(*------------------*)

val SUBSYSTEMS_SERIES_DEF = Define
`(SUBSYSTEMS_SERIES p [] = []) /\
 (SUBSYSTEMS_SERIES p (h::L) =
 rbd_struct p (series (rbd_list h))::SUBSYSTEMS_SERIES p L)`;

val COMPL_SUBSYSTEMS_SERIES_DEF = Define
`(COMPL_SUBSYSTEMS_SERIES p [] = []) /\
 (COMPL_SUBSYSTEMS_SERIES p (h::L) =
 (COMPL_PSPACE p (rbd_struct p (series (rbd_list h))))::COMPL_SUBSYSTEMS_SERIES p L)`;

val SUBSYSTEMS_PARALLEL_DEF = Define
`(SUBSYSTEMS_PARALLEL p [] = []) /\
 (SUBSYSTEMS_PARALLEL p (h::L) = rbd_struct p (parallel (rbd_list h))::SUBSYSTEMS_PARALLEL p L)`;

val COMPL_SUBSYSTEMS_PARALLEL_DEF = Define
`(COMPL_SUBSYSTEMS_PARALLEL p [] = []) /\
 (COMPL_SUBSYSTEMS_PARALLEL p (h::L) =
 (COMPL_PSPACE p (rbd_struct p (parallel (rbd_list h))))::COMPL_SUBSYSTEMS_PARALLEL p L)`;

val SUCCESS_LIST_DEF = Define
`(SUCCESS_LIST p [] t = []) /\
 (SUCCESS_LIST p (h::L) t = SUCCESS p h t:: SUCCESS_LIST p L t)`;

val EXP_ET_SUCCESS_DISTRIB_LIST_DEF = Define
` (EXP_ET_SUCCESS_DISTRIB_LIST p [] [] = T) /\
  (EXP_ET_SUCCESS_DISTRIB_LIST p (h::t) (x::xs) <=> (EXP_ET_SUCCESS_DISTRIB p h x) /\ EXP_ET_SUCCESS_DISTRIB_LIST p t xs) `;

(*------------------*)  
(*    Unicode       *)
(*------------------*)

val S 	  =  U 0x1D47A;
val s	  =  U 0x00073;
val r	  =  U 0x00072;
val dash  =  U 0x0005F;
val p 	  =  U 0x00070;
val a 	  =  U 0x00061;
val YES1  =  U 0x1D688;
val YES2  =  U 0x1D674;
val YES3  =  U 0x1D682;
val NO1   =  U 0x1D67D;
val NO2   =  U 0x1D67E;
val _ = Unicode.unicode_version {tmnm = "SUBSYSTEMS_SERIES", u = S^S^s^r^YES1^YES2^YES3};
val _ = Unicode.unicode_version {tmnm = "COMPL_SUBSYSTEMS_SERIES", u = S^S^s^r^NO1^NO2};
val _ = Unicode.unicode_version {tmnm = "SUBSYSTEMS_PARALLEL", u = S^S^p^a^YES1^YES2^YES3};
val _ = Unicode.unicode_version {tmnm = "COMPL_SUBSYSTEMS_PARALLEL", u = S^S^p^a^NO1^NO2};
(*---------------------------------------------------------------------------------------------------*)

val RBD_SERIES_IN_EVENTS = store_thm("RBD_SERIES_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p ) ==>
       (rbd_struct p (series (rbd_list L)) ??? events p)``,

GEN_TAC
\\ Induct
   >-( rw [rbd_list_def, rbd_struct_def]
       \\ metis_tac [EVENTS_SPACE])
\\ rw [rbd_list_def, rbd_struct_def]
\\ fs []
\\ metis_tac [EVENTS_INTER]);
(*---------------------------------------------------------------------------------------------------*)

val SUBSYSTEMS_SERIES_IN_EVENTS = store_thm("SUBSYSTEMS_SERIES_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) ==>
       (!x. MEM x (????????sr???????????? p L) ==> x ??? events p)``,

GEN_TAC
\\ Induct
   >-( rw [SUBSYSTEMS_SERIES_DEF])
\\ rw [SUBSYSTEMS_SERIES_DEF]
   >-( metis_tac [RBD_SERIES_IN_EVENTS])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val RBD_STRUCT_SERIES_EQ_PATH = store_thm("RBD_STRUCT_SERIES_EQ_PATH",
``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p ) ==>
        rbd_struct p (series (rbd_list L)) = PATH p L``,
GEN_TAC
\\ Induct
   >-( rw [rbd_list_def, rbd_struct_def, PATH_DEF]
       \\ metis_tac [EVENTS_SPACE])
\\  rw [rbd_list_def, rbd_struct_def, PATH_DEF]);
(*---------------------------------------------------------------------------------------------------*)
           	   
val PROB_PATH_INTER_PATH_OF_SUBSYSTEMS_SERIES = store_thm("PROB_PATH_INTER_PATH_OF_SUBSYSTEMS_SERIES",
``!p L L1. prob_space p /\ (!x. MEM x (FLAT (L1::L)) ==> x IN events p ) /\
           (!x. MEM x (L1::L) ==> ~NULL x) /\
           MUTUAL_INDEP p (FLAT (L1::L)) ==>
           prob p (PATH p L1 ??? PATH p (????????sr???????????? p L)) = prob p (PATH p L1) * prob p (PATH p (????????sr???????????? p L))``,

GEN_TAC
\\ Induct
   >-( rw [SUBSYSTEMS_SERIES_DEF, PATH_DEF]
       \\ rw [INTER_COMM]
       \\ DEP_REWRITE_TAC [INTER_PSPACE]
       \\ rw []
          >-(metis_tac [PATH_IN_EVENTS])
       \\ rw [PROB_UNIV])
\\ rw [SUBSYSTEMS_SERIES_DEF, PATH_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
\\ rw [INTER_ASSOC]
\\ sg `prob p (PATH p h ??? PATH p (????????sr???????????? p L)) =  prob p (PATH p h) * prob p (PATH p (????????sr???????????? p L))`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `L1`
	\\ rw [])
\\ POP_ORW
\\ sg `PATH p L1 ??? PATH p h ??? PATH p (????????sr???????????? p L) = PATH p (L1 ++ h) ??? PATH p (????????sr???????????? p L)`
   >-( DEP_REWRITE_TAC [PATH_APPEND]
       \\ rw []
	  >-(metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ ntac 3 (pop_assum mp_tac)
\\ first_x_assum (mp_tac o Q.SPECL [`L1 ++ h`]) 
\\ rw []
\\ sg ` (???x. x = L1 ??? h ??? MEM x L ??? ~NULL x)`
  >-( metis_tac [NULL, NULL_APPEND])
\\ sg `prob p (PATH p (L1 ??? h) ??? PATH p (????????sr???????????? p L)) = prob p (PATH p (L1 ??? h)) * prob p (PATH p (????????sr???????????? p L))`
   >-(metis_tac [])
\\ fs []
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH_APPEND]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `FLAT L`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 1     *)
(*------------------*)

val PROB_PATH_OF_SUBSYSTEMS_SERIES = store_thm("PROB_PATH_OF_SUBSYSTEMS_SERIES",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\ MUTUAL_INDEP p (FLAT L) /\
        (!x. MEM x L==> ~NULL x) ==>
        (prob p (PATH p (????????sr???????????? p L)) = ??? (MAP (\a. ??? (PROB_LIST p a)) L))``,

GEN_TAC
\\ Induct
   >-( rw [SUBSYSTEMS_SERIES_DEF, PATH_DEF, PROD_LIST_DEF]
       \\ metis_tac [PROB_UNIV])
\\ rw [SUBSYSTEMS_SERIES_DEF, PATH_DEF, PROD_LIST_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_PATH_OF_SUBSYSTEMS_SERIES] 
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ fs []
\\ sg ` MUTUAL_INDEP p (FLAT L)`
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `h`
	\\ rw [])
\\ fs []
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_PATH_OF_SUBSYSTEMS_SERIES = store_thm("PROB_CONSEQ_PATH_OF_SUBSYSTEMS_SERIES",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\ MUTUAL_INDEP p (FLAT L) /\
        (!x. MEM x L==> ~NULL x) ==>
        (prob p (CONSEQ_PATH p (????????sr???????????? p L)) = ??? (MAP (\a. ??? (PROB_LIST p a)) L))``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-(metis_tac [SUBSYSTEMS_SERIES_IN_EVENTS])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val COMPL_PATH_IN_EVENTS = store_thm("COMPL_PATH_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p ) ==>
        COMPL_PSPACE p (PATH p L) ??? events p``,

GEN_TAC
\\ Induct
   >-( rw [PATH_DEF, COMPL_PSPACE_DEF]
       \\ metis_tac [EVENTS_EMPTY])
\\ rw [PATH_DEF, COMPL_PSPACE_DEF]
\\ metis_tac [PATH_IN_EVENTS, EVENTS_INTER, EVENTS_COMPL]);
(*---------------------------------------------------------------------------------------------------*)

val COMPL_SUBSYSTEMS_SERIES_IN_EVENTS = store_thm("COMPL_SUBSYSTEMS_SERIES_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) ==>
       (!x. MEM x (????????sr???????? p L) ==> x ??? events p)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF])
\\ rw [COMPL_SUBSYSTEMS_SERIES_DEF]
   >-( rw [COMPL_PSPACE_DEF]
       \\ metis_tac [RBD_SERIES_IN_EVENTS, EVENTS_COMPL])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val PROB_COMPL_PATH = store_thm("PROB_COMPL_PATH",
``???p L.
         prob_space p ??? ~NULL L ??? (???x'. MEM x' L ??? x' ??? events p) ???
         MUTUAL_INDEP p L ???
         prob p (COMPL_PSPACE p (PATH p L)) = 1 - ??? (PROB_LIST p L)``,

rw [COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val PROB_COMPL_SPLIT = store_thm("PROB_COMPL_SPLIT",
``!p A B. prob_space p ??? A ??? events p ??? B ??? events p ==>
          prob p (COMPL_PSPACE p (A INTER B)) =
	  prob p (COMPL_PSPACE p A) + prob p (COMPL_PSPACE p B) ???
	  prob p ((COMPL_PSPACE p A) ??? (COMPL_PSPACE p B))``,

rw [COMPL_PSPACE_DEF]
\\ rw [DIFF_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ metis_tac [EVENTS_COMPL]);
(*---------------------------------------------------------------------------------------------------*)

val PROB_ELEMENT_PRODUCT_SPLIT = store_thm("PROB_ELEMENT_PRODUCT_SPLIT",
``!p h L. prob_space p ???  (!x. MEM x (h::L) ==> x IN events p ) /\ MUTUAL_INDEP p (h::L) ==>
          (1 ??? prob p h * ??? (PROB_LIST p L)) = prob p (COMPL_PSPACE p (h INTER PATH p L))``,

rw [COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw [] 
   >-( metis_tac [EVENTS_INTER, PATH_IN_EVENTS])
\\ sg `h ??? PATH p L = PATH p (h::L)` 
   >-( rw [PATH_DEF])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ metis_tac [PROB_LIST_DEF, PROD_LIST_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val PROB_ELEMENT_PATH_SPLIT = store_thm("PROB_ELEMENT_PATH_SPLIT",
``!p h L. prob_space p ???  (!x. MEM x (h::L) ==> x IN events p ) /\  ~NULL L /\
          MUTUAL_INDEP p (h::L ++ p_space p DIFF h::compl_list p L) ==>
  	  (1 ??? prob p h * ??? (PROB_LIST p L)) =  1 ??? prob p h + (1 ??? ??? (PROB_LIST p L)) ???
          (1 ??? prob p h) * (1 ??? ??? (PROB_LIST p L))``,

rw []
\\ DEP_REWRITE_TAC [PROB_ELEMENT_PRODUCT_SPLIT]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `p_space p DIFF h::compl_list p L`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ DEP_REWRITE_TAC [PROB_COMPL_SPLIT]
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS])
\\ rw [COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC[PROB_COMPL]
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS])
\\ sg `(p_space p DIFF h) = PATH p [p_space p DIFF h] `
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE])
\\ POP_ORW
\\ sg `(p_space p DIFF PATH p L) = NAND p L `
   >-( rw [NAND_DEF]
       \\ rw [FTree_def]
       \\ rw [AND_gate_eq_PATH])
\\ POP_ORW
\\ DEP_REWRITE_TAC [AND_INTER_NAND]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `(h::L)`
	\\ rw [])
\\ rw [PATH_DEF]
\\ sg `(p_space p DIFF h) ??? p_space p = (p_space p DIFF h)`
   >-( metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(  irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `[h]`
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `p_space p DIFF h::compl_list p L`
	\\ irule MUTUAL_INDEP_append_sym
	\\ rw [])
\\ DEP_REWRITE_TAC[PROB_COMPL]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_NAND]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `[h]`
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `p_space p DIFF h::compl_list p L`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 2     *)
(*------------------*)

val PROB_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_SERIES =
store_thm("PROB_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_SERIES",
``!p L2 L1. prob_space p /\ (!x. MEM x (L1 ++ FLAT L2) ==> x IN events p ) /\ ~NULL L1 /\
          MUTUAL_INDEP p (compl_list p (FLAT L2) ++ FLAT (L2) ++ L1 ++ compl_list p L1) ==>
     prob p (PATH p L1 ??? PATH p (????????sr???????? p L2)) =
     ??? (PROB_LIST p L1) * ??? (MAP (\a. (1 - ??? (PROB_LIST p a))) L2)``,


GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `PATH p L1 ??? p_space p = PATH p L1`
          >-( metis_tac [INTER_COMM, PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [PROB_PATH]
       \\ rw []
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       \\ rw [PATH_DEF]
       \\ rw [PROB_EMPTY])
\\ rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, SUBSYSTEMS_SERIES_IN_EVENTS, INTER_PSPACE,
                  COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, SUBSYSTEMS_SERIES_IN_EVENTS, INTER_PSPACE,
                  COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
\\ sg ` PATH p L1 ??? PATH p (????????sr???????? p L2) ??? (p_space p DIFF h') =
        PATH p (COMPL_PSPACE p h'::L1) ??? PATH p (????????sr???????? p L2)`
  >-( rw [PATH_DEF, COMPL_PSPACE_DEF]
      \\ rw [EXTENSION]
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (COMPL_PSPACE p h'::L1) ??? PATH p (????????sr???????? p L2)) =
       ??? (PROB_LIST p (COMPL_PSPACE p h'::L1)) * ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)`
   >-( ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`(COMPL_PSPACE p h'::L1)`])
       \\ rw []
       \\ sg `(???x.
             (x = COMPL_PSPACE p h' ??? MEM x L1) ??? MEM x (FLAT L2) ???
             x ??? events p) ` 
	  >-(metis_tac [EVENTS_COMPL, COMPL_PSPACE_DEF])	  
       \\ sg `MUTUAL_INDEP p (compl_list p (FLAT L2) ??? FLAT L2 ??? COMPL_PSPACE p h'::L1 ???
             		      compl_list p (COMPL_PSPACE p h'::L1))`
          >-( fs [compl_list_def, COMPL_PSPACE_DEF]
	      \\ fs [GSYM compl_list_def]
	      \\ sg `p_space p DIFF (p_space p DIFF h') = h'`
	         >-(metis_tac [P_SPACE_DIFF, EVENTS_COMPL, INTER_PSPACE, INTER_COMM])
              \\ POP_ORW
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
	      \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
              \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `compl_list p h`
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ Q.ABBREV_TAC `x = [p_space p DIFF h'] ??? compl_list p h ???
                                   compl_list p (FLAT L2)`
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `h`
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ Q.UNABBREV_TAC`x`
	      \\ sg `p_space p DIFF h'::
               	    (compl_list p h ??? compl_list p (FLAT L2) ??? [h'] ??? h ???
                    FLAT L2 ??? L1 ??? compl_list p L1) =
		    p_space p DIFF h'::
               	    (compl_list p h ??? compl_list p (FLAT L2) ??? h'::(h ??? FLAT L2) ???
                    L1 ??? compl_list p L1)  `
	            >-(rw [APPEND])
             \\ rw [])
	  \\ metis_tac [])   
\\ POP_ORW
\\ rw [COMPL_PSPACE_DEF, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p L1 ??? PATH p (????????sr???????? p L2) ??? (p_space p DIFF PATH p h) =
       PATH p L1 ??? ((p_space p DIFF rbd_struct p (series (rbd_list h))) ???
       PATH p (????????sr???????? p L2))` 
   >-(  DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
   	\\ rw [EXTENSION]
	\\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p L1 ???  ((p_space p DIFF rbd_struct p (series (rbd_list h))) ??? PATH p (????????sr???????? p L2))) =
            ??? (PROB_LIST p L1) *  ((1 ??? ??? (PROB_LIST p h)) * ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	\\ fs [compl_list_def]
	\\ fs [GSYM compl_list_def]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h']`
	\\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h']`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\  sg `p_space p DIFF h'::
               	    (compl_list p h ??? compl_list p (FLAT L2) ??? [h'] ??? h ???
                    FLAT L2 ??? L1 ??? compl_list p L1) =
		    p_space p DIFF h'::
               	    (compl_list p h ??? compl_list p (FLAT L2) ??? h'::(h ??? FLAT L2) ???
                    L1 ??? compl_list p L1)  `
	            >-(rw [APPEND])
        \\ rw [])
\\ POP_ORW
\\ sg `(p_space p DIFF h') ??? PATH p L1 ??? PATH p (????????sr???????? p L2) ??? (PATH p L1 ???
       ((p_space p DIFF rbd_struct p (series (rbd_list h))) ??? PATH p (????????sr???????? p L2))) =
	PATH p (COMPL_PSPACE p h'::L1) ??? ((p_space p DIFF rbd_struct p (series (rbd_list h))) ???
        PATH p (????????sr???????? p L2))`
   >-( rw [PATH_DEF, COMPL_PSPACE_DEF]
      \\ rw [EXTENSION]
      \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(COMPL_PSPACE p h'::L1)`])
\\ rw []
\\ sg ` (???x.
             (x = COMPL_PSPACE p h' ??? MEM x L1) ??? MEM x h ??? MEM x (FLAT L2) ???
             x ??? events p) `
   >-(metis_tac [EVENTS_COMPL, COMPL_PSPACE_DEF])
\\ sg `MUTUAL_INDEP p
          (compl_list p (h ??? FLAT L2) ??? h ??? FLAT L2 ??? COMPL_PSPACE p h'::L1 ???
           compl_list p (COMPL_PSPACE p h'::L1))`
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a]++b``,rw[]))]
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ fs [COMPL_PSPACE_DEF]
       \\ sg `p_space p DIFF (p_space p DIFF h') = h'`
	         >-(metis_tac [P_SPACE_DIFF, EVENTS_COMPL, INTER_PSPACE, INTER_COMM])
       \\ POP_ORW
       \\ Q.ABBREV_TAC `x = compl_list p h ??? compl_list p (FLAT L2) `
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `y = [p_space p DIFF h'] ??? x`
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `y`
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `p_space p DIFF h'::
               	    (compl_list p h ??? compl_list p (FLAT L2) ??? [h'] ??? h ???
                    FLAT L2 ??? L1 ??? compl_list p L1) =
		    p_space p DIFF h'::
               	    (compl_list p h ??? compl_list p (FLAT L2) ??? h'::(h ??? FLAT L2) ???
                    L1 ??? compl_list p L1)  `
	            >-(rw [APPEND])
        \\ rw [])
\\ sg `prob p
          (PATH p (COMPL_PSPACE p h'::L1) ???
           ((p_space p DIFF rbd_struct p (series (rbd_list h))) ???
            PATH p (????????sr???????? p L2))) =
        ??? (PROB_LIST p (COMPL_PSPACE p h'::L1)) *
        ((1 ??? ??? (PROB_LIST p h)) * ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)) ` 
   >-( metis_tac [])
\\ POP_ORW
\\ rw [COMPL_PSPACE_DEF, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [PROB_COMPL]
\\ ntac 3 (POP_ORW)
\\ pop_assum mp_tac
\\ POP_ORW
\\ ntac 2 (pop_assum mp_tac)
\\ POP_ORW
\\ rw []
\\ Induct_on`h`
   >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ rw []
\\ sg `(1 ??? prob p h' * ??? (PROB_LIST p (h''::h))) = 1 ??? prob p h' + (1 ??? ??? (PROB_LIST p (h''::h))) ???
        (1 ??? prob p h') * (1 ??? ??? (PROB_LIST p (h''::h)))`
   >-( DEP_REWRITE_TAC [PROB_ELEMENT_PATH_SPLIT]
       \\ rw []
       	  >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a] ++ [b] ++ c``,rw[]))]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a] ++ [b] ++ c``,rw[]))]
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ??? L1 ??? compl_list p L1`
       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? [h''] ??? h ??? FLAT L2 ??? L1 ??? compl_list p L1`
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg`p_space p DIFF h'::p_space p DIFF h''::
               (compl_list p h ??? compl_list p (FLAT L2) ??? [h'] ??? [h''] ??? h ???
                FLAT L2 ??? L1 ??? compl_list p L1) =
	     p_space p DIFF h'::p_space p DIFF h''::
               (compl_list p h ??? compl_list p (FLAT L2) ???
                h'::h''::(h ??? FLAT L2) ??? L1 ??? compl_list p L1)	`
          >-( rw [APPEND])
       \\ rw [])
 \\ POP_ORW
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 3     *)
(*------------------*)

val PROB_COMPL_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_SERIES =
store_thm("PROB_COMPL_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_SERIES",
``!p L1 L. prob_space p /\ (!x. MEM x (FLAT (L1::L)) ==> x IN events p ) /\
           MUTUAL_INDEP p (L1 ??? FLAT L ??? compl_list p (L1 ??? FLAT L)) ==>
           prob p (COMPL_PSPACE p (PATH p L1) ??? PATH p (????????sr???????? p L)) =
	   (1 - ??? (PROB_LIST p L1)) * ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ rw [PROB_UNIV, PROB_EMPTY])
\\ rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
\\ sg `PATH p (????????sr???????? p L) ??? (p_space p DIFF h) ??? (PATH p (????????sr???????? p L) ??? (p_space p DIFF PATH p L1)) =
       PATH p (????????sr???????? p L) ??? (p_space p DIFF h) ??? (p_space p DIFF PATH p L1)` 
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [GSYM COMPL_PSPACE_DEF]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg` prob p (COMPL_PSPACE p (PATH p L1) ??? PATH p (????????sr???????? p L)) =
       (1 ??? ??? (PROB_LIST p L1)) * ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L)`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h]`
	\\ rw []
	\\ sg `h::
               (L1 ??? FLAT L ??? [p_space p DIFF h] ??? compl_list p L1 ???
                compl_list p (FLAT L)) =
	       h::
               (L1 ??? FLAT L ???
                p_space p DIFF h::(compl_list p L1 ??? compl_list p (FLAT L)))` 
           >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW
\\ rw [COMPL_PSPACE_DEF]
\\ sg `(p_space p DIFF h) ??? PATH p (????????sr???????? p L) =
       PATH p [(p_space p DIFF h)] ??? PATH p (????????sr???????? p L)`
   >-( rw [PATH_DEF]
       \\ sg `(p_space p DIFF h) ??? p_space p = (p_space p DIFF h) `
          >-(metis_tac [P_SPACE_DIFF, EVENTS_COMPL, INTER_PSPACE, INTER_COMM])
       \\ POP_ORW
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ sg `p_space p DIFF (p_space p DIFF h) = h `
       	  >-(metis_tac [P_SPACE_DIFF, EVENTS_COMPL, INTER_PSPACE, INTER_COMM])
       \\ POP_ORW
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg ` h::
               (L1 ??? FLAT L ??? [p_space p DIFF h] ??? compl_list p L1 ???
                compl_list p (FLAT L))  =
	      h::
               (L1 ??? FLAT L ???
                p_space p DIFF h::(compl_list p L1 ??? compl_list p (FLAT L)))`
           >-( rw [APPEND])
	\\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [PROB_COMPL]
\\ sg `(p_space p DIFF PATH p L1) ??? (p_space p DIFF h) ???  PATH p (????????sr???????? p L) =
       COMPL_PSPACE p (PATH p L1) ??? PATH p (????????sr???????? p ([h]::L))` 
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       \\ rw [PATH_DEF]
       \\ rw [PATH_DEF]
       \\ sg `(p_space p DIFF h ??? p_space p) =  p_space p DIFF h`
          >-(metis_tac [P_SPACE_DIFF, EVENTS_COMPL, INTER_PSPACE, INTER_COMM])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`([h]::L)`])
\\ rw []
\\ sg `(???x. MEM x L1 ??? x = h ??? MEM x (FLAT L) ??? x ??? events p) `
   >-( metis_tac [])
\\ sg `MUTUAL_INDEP p (L1 ??? h::FLAT L ??? compl_list p (L1 ??? h::FLAT L)) `
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h] ??? L1 ??? FLAT L `
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `h::
               (L1 ??? FLAT L ??? [p_space p DIFF h] ??? compl_list p L1 ???
                compl_list p (FLAT L)) =
              h::
               (L1 ??? FLAT L ???
                p_space p DIFF h::(compl_list p L1 ??? compl_list p (FLAT L))) `
           >-( rw [APPEND])
	\\ rw [])
\\ sg `prob p (COMPL_PSPACE p (PATH p L1) ??? PATH p (????????sr???????? p ([h]::L))) =
        (1 ??? ??? (PROB_LIST p L1)) *
        ??? (1 ??? ??? (PROB_LIST p [h])::MAP (??a. 1 ??? ??? (PROB_LIST p a)) L) `
   >-(metis_tac [])
\\ POP_ORW
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ ntac 2 (pop_assum mp_tac)
\\ ntac 3 (POP_ORW)
\\ rw []
\\ Induct_on`L1`
   >-( rw [PROB_LIST_DEF, PROD_LIST_DEF])
\\ POP_ORW
\\ rw []
\\ sg `(1 ??? prob p h * ??? (PROB_LIST p (h'::L1))) = 1 ??? prob p h + (1 ??? ??? (PROB_LIST p (h'::L1))) ???
        (1 ??? prob p h) * (1 ??? ??? (PROB_LIST p (h'::L1)))`
   >-( DEP_REWRITE_TAC [PROB_ELEMENT_PATH_SPLIT]
       \\ rw []
       	  >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a] ++ [b] ++ c``,rw[]))]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a] ++ [b] ++ c``,rw[]))]
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [p_space p DIFF h'] ??? compl_list p L1 ??? [p_space p DIFF h]`
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.UNABBREV_TAC`x`
       \\ rw []
       \\ sg`h'::
               (L1 ??? [h] ??? FLAT L ??? [p_space p DIFF h'] ??? compl_list p L1 ???
                [p_space p DIFF h] ??? compl_list p (FLAT L)) =
             h'::
               (L1 ??? h::FLAT L ???
                p_space p DIFF h'::
                    (compl_list p L1 ???
                     p_space p DIFF h::compl_list p (FLAT L)))`
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 4     *)
(*------------------*)

val PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES = store_thm("PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\ 
        MUTUAL_INDEP p (FLAT L ++ compl_list p (FLAT L)) ==>
        (prob p (PATH p (????????sr???????? p L)) = ??? (MAP (\a. (1 - ??? (PROB_LIST p a))) L))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, PROD_LIST_DEF]
       \\ metis_tac [PROB_UNIV])
\\ rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, PROD_LIST_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_COMPL_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_PATH_OF_COMPL_SUBSYSTEMS_SERIES = store_thm("PROB_CONSEQ_PATH_OF_COMPL_SUBSYSTEMS_SERIES",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\ 
        MUTUAL_INDEP p (FLAT L ++ compl_list p (FLAT L))  ==>
        (prob p (CONSEQ_PATH p (????????sr???????? p L)) = ??? (MAP (\a. (1 - ??? (PROB_LIST p a))) L))``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-(metis_tac [COMPL_SUBSYSTEMS_SERIES_IN_EVENTS])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 5     *)
(*------------------*)

val PROB_PATH_OF_SUBSYSTEMS_SERIES_AND_PATH_OF_COMPL_SUBSYSTEMS_SERIES =
store_thm("PROB_PATH_OF_SUBSYSTEMS_SERIES_AND_PATH_OF_COMPL_SUBSYSTEMS_SERIES",
``!p L2 L1. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\
     	    (???x. MEM x L1 ??? ~NULL x) /\
            MUTUAL_INDEP p (FLAT L1 ++ FLAT L2 ++ compl_list p (FLAT L2)) ==>
     prob p (PATH p (????????sr???????????? p L1) ??? PATH p (????????sr???????? p L2)) =
     ??? (MAP (??a. ??? (PROB_LIST p a)) L1) *  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `PATH p (????????sr???????????? p L1) ??? p_space p = PATH p (????????sr???????????? p L1)`
          >-( metis_tac [INTER_COMM, SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
       \\ rw []
       \\ fs [compl_list_def])
\\ Induct_on `h`
   >-(  rw [COMPL_SUBSYSTEMS_SERIES_DEF, compl_list_def, PATH_DEF, COMPL_PSPACE_DEF,
            PROD_LIST_DEF, PROB_LIST_DEF]
     	\\ rw [rbd_list_def, rbd_struct_def]
	\\ rw [PROB_EMPTY])
\\ rw [COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
\\ rw [INTER_ASSOC]
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [PATH_DEF]
\\ rw [DIFF_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, SUBSYSTEMS_SERIES_IN_EVENTS,
                                COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, SUBSYSTEMS_SERIES_IN_EVENTS,
                                COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
\\ sg `PATH p (????????sr???????? p L2) ??? PATH p (????????sr???????????? p L1) ??? (p_space p DIFF h') =
       PATH p (????????sr???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????sr???????? p L2)`
   >-(  rw [SUBSYSTEMS_SERIES_DEF, COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF]
   	\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
	\\ rw [INTER_ASSOC]
	   >-(metis_tac [EVENTS_COMPL])
	\\ rw [PATH_DEF]
	\\ rw [EXTENSION]
	\\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????sr???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????sr???????? p L2)) =
        ??? (MAP (??a. ??? (PROB_LIST p a)) ([p_space p DIFF h']::L1)) *
	??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)`
   >-( ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L1)`])	
       \\ rw []
       \\ sg `(???x.
             (x = p_space p DIFF h' ??? MEM x (FLAT L1)) ??? MEM x (FLAT L2) ???
             x ??? events p)` 
          >-(metis_tac [EVENTS_COMPL])
       \\ sg `(???x. x = [p_space p DIFF h'] ??? MEM x L1 ??? ~NULL x)  `
          >-(metis_tac [NULL])
       \\ sg`MUTUAL_INDEP p (p_space p DIFF h'::(FLAT L1 ??? FLAT L2 ??? compl_list p (FLAT L2)))`
          >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
       	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
              \\ ntac 2 (POP_ORW)
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `compl_list p h`
       	      \\ once_rewrite_tac [APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `h'::h`
       	      \\ once_rewrite_tac [APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ sg `FLAT L1 ??? h'::h ??? FLAT L2 ??? [p_space p DIFF h'] ??? compl_list p h ???
              	     compl_list p (FLAT L2) =
		     FLAT L1 ??? h'::(h ??? FLAT L2) ???
           	     p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L2))`
                 >-( rw [APPEND])
              \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????sr???????? p L2) ??? PATH p (????????sr???????????? p L1) ???  (p_space p DIFF PATH p h) =
       PATH p (????????sr???????????? p L1) ??? PATH p (????????sr???????? p (h::L2)) `
   >-( rw [SUBSYSTEMS_SERIES_DEF, COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       \\ rw [INTER_ASSOC]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????sr???????????? p L1) ??? PATH p (????????sr???????? p (h::L2))) =
       ??? (MAP (??a. ??? (PROB_LIST p a)) L1) *
       ??? (1 ??? ??? (PROB_LIST p h)::MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2) ` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	\\ fs [compl_list_def]
        \\ fs [GSYM compl_list_def]
	\\ once_rewrite_tac[GSYM APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[p_space p DIFF h']`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	\\ irule MUTUAL_INDEP_FRONT_APPEND  
       	\\ Q.EXISTS_TAC `[h']`
	\\ once_rewrite_tac[APPEND_ASSOC]
	\\ irule MUTUAL_INDEP_APPEND1
	\\ rw []
	\\ sg `FLAT L1 ??? [h'] ??? h ??? FLAT L2 ??? [p_space p DIFF h'] ???
               compl_list p h ??? compl_list p (FLAT L2) =
	       FLAT L1 ??? h'::(h ??? FLAT L2) ???
               p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L2))`
           >-( rw [APPEND])
        \\ rw []) 
\\ POP_ORW  
\\ sg `PATH p (????????sr???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????sr???????? p L2) ???
       (PATH p (????????sr???????????? p L1) ??? PATH p (????????sr???????? p (h::L2))) =
       PATH p (????????sr???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????sr???????? p (h::L2))`
   >-( rw [SUBSYSTEMS_SERIES_DEF, COMPL_SUBSYSTEMS_SERIES_DEF, PATH_DEF, COMPL_PSPACE_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       \\ rw [INTER_ASSOC]
          >-( metis_tac [EVENTS_COMPL])
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????sr???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????sr???????? p (h::L2))) =
       ??? (MAP (??a. ??? (PROB_LIST p a)) ([p_space p DIFF h']::L1)) *
       ??? (1 ??? ??? (PROB_LIST p h)::MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)`
   >-( first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L1)`])	
       \\ rw []
       \\ sg `(???x. ((x = p_space p DIFF h' ??? MEM x (FLAT L1)) ??? MEM x h) ???
                    MEM x (FLAT L2) ??? x ??? events p) ` 
          >-(metis_tac [EVENTS_COMPL])
       \\ sg `(???x. x = [p_space p DIFF h'] ??? MEM x L1 ??? ~NULL x) ` 
          >-(metis_tac [NULL])
       \\ sg `MUTUAL_INDEP p
              (p_space p DIFF h'::
               (FLAT L1 ??? h ??? FLAT L2 ??? compl_list p (h ??? FLAT L2))) ` 
          >-( fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
       	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	      \\ ntac 3 (POP_ORW)
	      \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ Q.ABBREV_TAC `x = ([p_space p DIFF h'] ??? (compl_list p h ??? compl_list p (FLAT L2)))`
	      \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `[h']`
       	      \\ once_rewrite_tac [APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ Q.UNABBREV_TAC`x`
	      \\ rw []
	      \\ sg `FLAT L1 ??? [h'] ??? h ??? FLAT L2 ??? [p_space p DIFF h'] ???
              	    compl_list p h ??? compl_list p (FLAT L2) =
		    FLAT L1 ??? h'::(h ??? FLAT L2) ???
           	    p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L2))` 
                 >-( rw [APPEND])
       	      \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ ntac 4 (pop_assum mp_tac)
\\ ntac 2 (POP_ORW)
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ rw [PROB_COMPL]
\\ Induct_on`h`
   >-( rw [PROB_LIST_DEF, PROD_LIST_DEF]
       \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ rw []
\\ sg `(1 ??? prob p h' * ??? (PROB_LIST p (h''::h))) = 1 ??? prob p h' + (1 ??? ??? (PROB_LIST p (h''::h))) ???
        (1 ??? prob p h') * (1 ??? ??? (PROB_LIST p (h''::h)))`
   >-( DEP_REWRITE_TAC [PROB_ELEMENT_PATH_SPLIT]
       \\ rw []
       	  >-( metis_tac [])
	  >-( metis_tac [])
	  >-( metis_tac [])
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a] ++ [b] ++ c``,rw[]))]
       \\ once_rewrite_tac[(prove(``!a b c. a::b::c = [a] ++ [b] ++ c``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) `
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw []
       \\ sg`FLAT L1 ??? [h'] ??? [h''] ??? h ??? FLAT L2 ??? [p_space p DIFF h'] ???
             [p_space p DIFF h''] ??? compl_list p h ??? compl_list p (FLAT L2) =
	     FLAT L1 ??? h'::h''::(h ??? FLAT L2) ???
             p_space p DIFF h'::p_space p DIFF h''::(compl_list p h ??? compl_list p (FLAT L2))`
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_PATH_OF_MIX_SUBSYSTEMS_SERIES_AND_COMPL_SUBSYSTEMS_SERIES =
store_thm("PROB_CONSEQ_PATH_OF_MIX_SUBSYSTEMS_SERIES_AND_COMPL_SUBSYSTEMS_SERIES",
``!p L1 L2. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\
     	    (???x. MEM x L1 ??? ~NULL x) /\
            MUTUAL_INDEP p (FLAT L1 ++ FLAT L2 ++ compl_list p (FLAT L2)) ==>
     prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????sr???????????? p L1); CONSEQ_PATH p (????????sr???????? p L2)]) =
     ??? (MAP (??a. ??? (PROB_LIST p a)) L1) *  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p a)) L2)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-(metis_tac [SUBSYSTEMS_SERIES_IN_EVENTS])
   >-(metis_tac [COMPL_SUBSYSTEMS_SERIES_IN_EVENTS])
   >-(metis_tac [SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
   >-(metis_tac [COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, PATH_IN_EVENTS])
   >-(metis_tac [SUBSYSTEMS_SERIES_IN_EVENTS])
   >-(metis_tac [COMPL_SUBSYSTEMS_SERIES_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `PATH p (????????sr???????????? p L1) ??? (PATH p (????????sr???????? p L2) ??? p_space p) =
       PATH p (????????sr???????????? p L1) ??? PATH p (????????sr???????? p L2)`
   >-(metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE, COMPL_SUBSYSTEMS_SERIES_IN_EVENTS,
                 PATH_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES_AND_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val RBD_PARALLEL_IN_EVENTS = store_thm("RBD_PARALLEL_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p ) ==>
       (rbd_struct p (parallel (rbd_list L)) ??? events p)``,

GEN_TAC
\\ Induct
   >-( rw [rbd_list_def, rbd_struct_def]
       \\ metis_tac [EVENTS_EMPTY])
\\ rw [rbd_list_def, rbd_struct_def]
\\ fs []
\\ metis_tac [EVENTS_UNION]);
(*---------------------------------------------------------------------------------------------------*)

val RBD_STRUCT_PARALLEL_EQ_BIG_UNION = store_thm("RBD_STRUCT_PARALLEL_EQ_BIG_UNION",
``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p ) ==>
        rbd_struct p (parallel (rbd_list L)) =  BIG_UNION p L``,
GEN_TAC
\\ Induct
   >-( rw [rbd_list_def,rbd_struct_def,BIG_UNION_DEF])
\\ rw [rbd_list_def,rbd_struct_def,BIG_UNION_DEF]);
(*---------------------------------------------------------------------------------------------------*)

val SUBSYSTEMS_PARALLEL_IN_EVENTS = store_thm("SUBSYSTEMS_PARALLEL_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) ==>
       (!x. MEM x (????????pa???????????? p L) ==> x ??? events p)``,

GEN_TAC
\\ Induct
   >-( rw [SUBSYSTEMS_PARALLEL_DEF])
\\ rw [SUBSYSTEMS_PARALLEL_DEF]
   >-( metis_tac [RBD_PARALLEL_IN_EVENTS])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

val COMPL_BIG_UNION_IN_EVENTS = store_thm("COMPL_BIG_UNION_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x L ==> x IN events p ) ==>
        COMPL_PSPACE p (BIG_UNION p L) ??? events p``,

GEN_TAC
\\ Induct
   >-( rw [BIG_UNION_DEF, COMPL_PSPACE_DEF]
       \\ metis_tac [EVENTS_SPACE])
\\ rw [BIG_UNION_DEF, COMPL_PSPACE_DEF]
\\ metis_tac [BIG_UNION_IN_EVENTS, EVENTS_UNION, EVENTS_COMPL]);
(*---------------------------------------------------------------------------------------------------*)

val COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS = store_thm("COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) ==>
       (!x. MEM x (????????pa???????? p L) ==> x ??? events p)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF]
   >-( rw [COMPL_PSPACE_DEF]
       \\ metis_tac [RBD_PARALLEL_IN_EVENTS, EVENTS_COMPL])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 6     *)
(*------------------*)

val PROB_PATH_INTER_PATH_OF_SUBSYSTEMS_PARALLEL = store_thm("PROB_PATH_INTER_PATH_OF_SUBSYSTEMS_PARALLEL",
``!p L L1. prob_space p /\ (!x. MEM x (FLAT (L1::L)) ==> x IN events p ) /\ ~NULL L1 /\
           MUTUAL_INDEP p (FLAT (L1::L)) ==>
           prob p (PATH p L1 ??? PATH p (????????pa???????????? p L)) =
	   prob p (PATH p L1) * prob p (PATH p (????????pa???????????? p L))``,

GEN_TAC
\\ Induct
   >-( rw [SUBSYSTEMS_PARALLEL_DEF, PATH_DEF]
       \\ rw [INTER_COMM]
       \\ DEP_REWRITE_TAC [INTER_PSPACE]
       \\ rw []
          >-(metis_tac [PATH_IN_EVENTS])
       \\ rw [PROB_UNIV])
\\ Induct_on `h`       
   >-( rw [SUBSYSTEMS_PARALLEL_DEF, PATH_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_ASSOC, BIG_UNION_DEF]
       \\ rw [PROB_EMPTY])
\\ rw [SUBSYSTEMS_PARALLEL_DEF, PATH_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ fs [] 
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [INTER_COMM, BIG_UNION_DEF]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, BIG_UNION_IN_EVENTS,
                  SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, BIG_UNION_IN_EVENTS,
                  SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, BIG_UNION_IN_EVENTS,
                  SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
\\ sg `PATH p L1 ??? PATH p (????????pa???????????? p L) ??? h'  = PATH p (h'::L1) ??? PATH p (????????pa???????????? p L) `
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (h'::L1) ??? PATH p (????????pa???????????? p L)) =
       prob p (PATH p (h'::L1)) * prob p (PATH p (????????pa???????????? p L))` 
   >-( ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`(h'::L1)`])	
       \\ rw []
       \\ sg `(???x. (x = h' ??? MEM x L1) ??? MEM x (FLAT L) ??? x ??? events p) ` 
       	  >-(metis_tac [])
       \\ sg ` MUTUAL_INDEP p (h'::(L1 ??? FLAT L))`
       	  >-( once_rewrite_tac[(prove(``!a b c. a::c = [a] ++ c``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `h`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ sg `L1 ??? [h'] ??? h ??? FLAT L = L1 ??? h'::(h ??? FLAT L) `
	         >-( rw [APPEND])
	      \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p L1 ??? PATH p (????????pa???????????? p L) ??? BIG_UNION p h =
       PATH p L1 ??? PATH p (????????pa???????????? p (h::L))`
   >-( rw [SUBSYSTEMS_PARALLEL_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ fs [] 
       \\ rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg ` prob p (PATH p L1 ??? PATH p (????????pa???????????? p (h::L))) =
        prob p (PATH p L1) * prob p (PATH p (????????pa???????????? p (h::L)))`
   >-( first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `L1 ??? [h'] ??? h ??? FLAT L = L1 ??? h'::(h ??? FLAT L) `
	  >-( rw [APPEND])
       \\ rw [])       
\\ POP_ORW
\\ sg `PATH p (h'::L1) ??? PATH p (????????pa???????????? p L) ???
           (PATH p L1 ??? PATH p (????????pa???????????? p (h::L))) = PATH p (h'::L1) ??? PATH p (????????pa???????????? p (h::L))`
   >-( rw [SUBSYSTEMS_PARALLEL_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ fs [] 
       \\ rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac []) 
\\ POP_ORW
\\ sg `prob p (PATH p (h'::L1) ??? PATH p (????????pa???????????? p (h::L))) =
       prob p (PATH p (h'::L1)) * prob p (PATH p (????????pa???????????? p (h::L)))`
   >-( first_x_assum (mp_tac o Q.SPECL [`(h'::L1)`]) 
       \\ rw []
       \\ sg `(???x. ((x = h' ??? MEM x L1) ??? MEM x h) ??? MEM x (FLAT L) ??? x ??? events p) `
          >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (h'::(L1 ??? h ??? FLAT L)) `
      	  >-( once_rewrite_tac[(prove(``!a b c. a::c = [a] ++ c``,rw[]))]
	      \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ sg `L1 ??? [h'] ??? h ??? FLAT L = L1 ??? h'::(h ??? FLAT L) `
	         >-( rw [APPEND])
	      \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L) ??? BIG_UNION p h =  PATH p (????????pa???????????? p (h::L))` 
   >-( rw [SUBSYSTEMS_PARALLEL_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ fs [] 
       \\ rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac []) 
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L) ??? h' = PATH p [h'] ??? PATH p (????????pa???????????? p L)`
   >-(  rw [PATH_DEF]
       \\ sg `h' ??? p_space p = h'`
          >-( metis_tac [INTER_PSPACE, INTER_COMM])
       \\ POP_ORW  
       \\ rw [EXTENSION]
       \\ metis_tac []) 
\\ POP_ORW
\\ sg `prob p (PATH p [h'] ??? PATH p (????????pa???????????? p L)) =
       prob p (PATH p [h']) * prob p (PATH p (????????pa???????????? p L)) `
   >-( ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`[h']`])	
       \\ rw []
       \\ sg `(???x. x = h' ??? MEM x (FLAT L) ??? x ??? events p)`
       	  >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (h'::FLAT L)`
       	  >-( once_rewrite_tac[(prove(``!a b c. a::c = [a] ++ c``,rw[]))]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `h`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `L1`
	      \\ rw []
	      \\ sg `L1 ??? [h'] ??? h ??? FLAT L = L1 ??? h'::(h ??? FLAT L) `
	         >-( rw [APPEND])
	      \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p [h'] ??? PATH p (????????pa???????????? p L) ??? PATH p (????????pa???????????? p (h::L)) =
       PATH p [h'] ??? PATH p (????????pa???????????? p (h::L))`
   >-( rw [SUBSYSTEMS_PARALLEL_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ fs [] 
       \\ rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac []) 
\\ POP_ORW
\\ sg `prob p (PATH p [h'] ??? PATH p (????????pa???????????? p (h::L))) =
       prob p (PATH p [h']) * prob p (PATH p (????????pa???????????? p (h::L))) `
   >-( first_x_assum (mp_tac o Q.SPECL [`[h']`])	
       \\ rw []
       \\ sg `(???x. (x = h' ??? MEM x h) ??? MEM x (FLAT L) ??? x ??? events p)`
       	  >-(metis_tac [])
       \\ sg ` MUTUAL_INDEP p (h'::(h ??? FLAT L))`
       	  >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `L1`
	      \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p [h'] = h' ` 
   >-( rw [PATH_DEF]
       \\  metis_tac [INTER_PSPACE, INTER_COMM])
\\ POP_ORW  
\\ sg `prob p (PATH p (h'::L1)) = prob p h' * prob p (PATH p L1)`
   >-( DEP_REWRITE_TAC [PROB_PATH]
       \\ rw []
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-( once_rewrite_tac[(prove(``!a b c. a::c = [a] ++ c``,rw[]))]
	      \\ irule MUTUAL_INDEP_append_sym
	      \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	      \\ Q.EXISTS_TAC `(h ??? FLAT L)`
	      \\ irule MUTUAL_INDEP_append_sym
	      \\ rw []
	      \\ sg `L1 ??? [h'] ??? h ??? FLAT L = L1 ??? h'::(h ??? FLAT L) `
	         >-( rw [APPEND])
	      \\ rw [])
          >-(  irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `h'::(h ??? FLAT L)`
       	       \\ irule MUTUAL_INDEP_append_sym
       	       \\ rw [])
       \\ rw [PROB_LIST_DEF, PROD_LIST_DEF])
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 7     *)
(*------------------*)

val PROB_BIG_UNION_INTER_PATH_OF_SUBSYSTEMS_PARALLEL
= store_thm("PROB_BIG_UNION_INTER_PATH_OF_SUBSYSTEMS_PARALLEL",
``!p L1 L. prob_space p /\ (!x. MEM x (FLAT (L1::L)) ==> x IN events p ) /\
           MUTUAL_INDEP p (FLAT (L1::L)) ==>
	   prob p (BIG_UNION p L1 ??? PATH p (????????pa???????????? p L)) =
	   prob p (BIG_UNION p L1) * prob p (PATH p (????????pa???????????? p L))``,
      
GEN_TAC
\\ Induct
   >-( rw [BIG_UNION_DEF, PATH_DEF, PROD_LIST_DEF, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ rw [PROB_EMPTY])
\\ rw [BIG_UNION_DEF, PATH_DEF, PROD_LIST_DEF, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [PROB_COMPL]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [EVENTS_COMPL, EVENTS_INTER, SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [EVENTS_COMPL, BIG_UNION_IN_EVENTS, EVENTS_INTER,
                  SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-( metis_tac [BIG_UNION_IN_EVENTS])
\\ rw [INTER_COMM]
\\ sg `h ??? PATH p (????????pa???????????? p L) ??? (BIG_UNION p L1 ??? PATH p (????????pa???????????? p L)) =
       BIG_UNION p L1 ??? PATH p (????????pa???????????? p ([h]::L))`
   >-( rw [PATH_DEF, SUBSYSTEMS_PARALLEL_DEF]
       \\ rw [rbd_list_def, rbd_struct_def]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (BIG_UNION p L1 ??? PATH p (????????pa???????????? p L)) =
       prob p (BIG_UNION p L1) * prob p (PATH p (????????pa???????????? p L))` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h]`
       \\ rw [])
\\ POP_ORW
\\ sg `prob p (BIG_UNION p L1 ??? PATH p (????????pa???????????? p ([h]::L))) =
       prob p (BIG_UNION p L1) * prob p (PATH p (????????pa???????????? p ([h]::L)))`
   >-( first_x_assum (mp_tac o Q.SPECL [`([h]::L)`])	
       \\ rw []
       \\ sg `(???x. MEM x L1 ??? x = h ??? MEM x (FLAT L) ??? x ??? events p)  ` 
          >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (L1 ??? h::FLAT L) `
          >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ rw [PROD_LIST_DEF, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ rw [PATH_DEF, SUBSYSTEMS_PARALLEL_DEF, rbd_list_def, rbd_struct_def]
\\ sg `h ??? PATH p (????????pa???????????? p L) = PATH p [h] ??? PATH p (????????pa???????????? p L)`
   >-( rw [PATH_DEF]
       \\ sg `h ??? p_space p = h`
          >-( metis_tac [INTER_PSPACE, INTER_COMM])
       \\ POP_ORW  
       \\ rw [EXTENSION]
       \\ metis_tac []) 
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ sg `PATH p [h] = h ` 
   >-( rw [PATH_DEF]
       \\  metis_tac [INTER_PSPACE, INTER_COMM])
\\ POP_ORW
\\ sg `h ??? BIG_UNION p L1 =  BIG_UNION p [h] ??? BIG_UNION p L1` 
  >-( rw [BIG_UNION_DEF])
\\ POP_ORW
\\ DEP_REWRITE_TAC [OR_INTER_OR]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ rw [BIG_UNION_DEF]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 8     *)
(*------------------*)

val PROB_PATH_OF_SUBSYSTEMS_PARALLEL = store_thm("PROB_PATH_OF_SUBSYSTEMS_PARALLEL",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\ MUTUAL_INDEP p (FLAT L)  ==>
        (prob p (PATH p (????????pa???????????? p L)) =
	??? (MAP (\a. (1 - ??? (PROB_LIST p (compl_list p a)))) L))``,

GEN_TAC
\\ Induct
   >-( rw [SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, PROD_LIST_DEF]
       \\ metis_tac [PROB_UNIV])
\\ rw [SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, PROD_LIST_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_BIG_UNION_INTER_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ fs []
\\ sg `MUTUAL_INDEP p (FLAT L) `
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ rw [])
\\ sg `prob p (PATH p (????????pa???????????? p L)) =  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L) ` 
   >-(metis_tac [])
\\ POP_ORW
\\ rw [GSYM RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ disj2_tac
\\ POP_ORW
\\ ntac 3 (pop_assum mp_tac)
\\ POP_ORW
\\ rw []
\\ Induct_on `h`
   >-( rw [rbd_list_def, rbd_struct_def, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ metis_tac [PROB_EMPTY])
\\ rw []
\\ DEP_REWRITE_TAC [parallel_struct_thm]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [OR_lem7]
\\ rw []
   >-(metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_PATH_OF_SUBSYSTEMS_PARALLEL = store_thm("PROB_CONSEQ_PATH_OF_SUBSYSTEMS_PARALLEL",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\ MUTUAL_INDEP p (FLAT L) ==>
        (prob p (CONSEQ_PATH p (????????pa???????????? p L)) =  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L))``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-(metis_tac [SUBSYSTEMS_PARALLEL_IN_EVENTS])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 9     *)
(*------------------*)

val PROB_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL =
store_thm("PROB_PATH_INTER_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL",
``!p L2 L1. prob_space p /\ (!x. MEM x (L1 ++ FLAT L2) ==> x IN events p ) /\ ~NULL L1 /\
          MUTUAL_INDEP p (L1 ++ (FLAT L2)  ++ compl_list p (FLAT L2)) ==>
          prob p (PATH p L1 ??? PATH p (????????pa???????? p L2)) =
          ??? (PROB_LIST p L1) * ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L2)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ sg ` PATH p L1 ??? p_space p = PATH p L1`
          >-(metis_tac [PATH_IN_EVENTS, INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [PROB_PATH]
       \\ rw []
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, COMPL_PSPACE_DEF]
       \\ rw [rbd_list_def, rbd_struct_def, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg ` PATH p L1 ??? p_space p = PATH p L1`
          >-(metis_tac [PATH_IN_EVENTS, INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw []
       \\ rw [GSYM compl_list_def]
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
       \\ metis_tac []) 
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_ASSOC, PROB_LIST_DEF, PROD_LIST_DEF, BIG_UNION_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [INTER_COMM]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ sg `PATH p (????????pa???????? p L2) ??? PATH p L1 ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p ((p_space p DIFF h')::L1) ??? PATH p (????????pa???????? p (h::L2))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, COMPL_PSPACE_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(p_space p DIFF h'::L1)`])	
\\ rw []
\\ sg `(???x.
             (x = p_space p DIFF h' ??? MEM x L1) ??? MEM x h ??? MEM x (FLAT L2) ???
             x ??? events p) `
   >-(metis_tac [EVENTS_COMPL])
\\ sg `MUTUAL_INDEP p (p_space p DIFF h'::(L1 ??? h ??? FLAT L2 ??? compl_list p (h ??? FLAT L2)))`
   >-( fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (POP_ORW)
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])     
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `L1 ??? [h'] ??? h ??? FLAT L2 ??? [p_space p DIFF h'] ??? compl_list p h ???
              compl_list p (FLAT L2) =
	      L1 ??? h'::(h ??? FLAT L2) ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L2))`
          >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p (PATH p (p_space p DIFF h'::L1) ??? PATH p (????????pa???????? p (h::L2))) =
        ??? (PROB_LIST p (p_space p DIFF h'::L1)) *
        ??? (??? (PROB_LIST p (compl_list p h))::MAP (??a. ??? (PROB_LIST p (compl_list p a))) L2) `
   >-( metis_tac [])
\\ POP_ORW
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF, compl_list_def]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

val COMPL_BIG_UNION_EQ_PATH_COMPL_LIST = store_thm("COMPL_BIG_UNION_EQ_PATH_COMPL_LIST",
``! p L L1. prob_space p /\ (!x. MEM x (FLAT (L1::L)) ==> x IN events p ) ==>
            COMPL_PSPACE p (BIG_UNION p L1) ??? PATH p (????????pa???????? p L) =
            PATH p (compl_list p L1) ??? PATH p (????????pa???????? p L)``,

GEN_TAC
\\ Induct
   >-( rw [PATH_DEF, PATH_DEF, COMPL_SUBSYSTEMS_PARALLEL_DEF]
       \\ Induct_on `L1`
          >-( rw [compl_list_def, BIG_UNION_DEF, COMPL_PSPACE_DEF, PATH_DEF])
       \\ rw [compl_list_def, BIG_UNION_DEF, COMPL_PSPACE_DEF, PATH_DEF]
       \\  rw [OR_lem1]
       \\ rw [INTER_ASSOC]
       \\ rw [GSYM compl_list_def]
       \\ rw [GSYM COMPL_PSPACE_DEF]
       \\ rw [GSYM INTER_ASSOC])
\\ rw [PATH_DEF, PATH_DEF, COMPL_SUBSYSTEMS_PARALLEL_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_ASSOC, BIG_UNION_DEF]
\\ sg`  COMPL_PSPACE p (BIG_UNION p L1) ??? COMPL_PSPACE p (BIG_UNION p h) ???
        PATH p (????????pa???????? p L)  =
	(COMPL_PSPACE p (BIG_UNION p L1) ??? PATH p (????????pa???????? p L)) ??? COMPL_PSPACE p (BIG_UNION p h)`
       >-( rw [EXTENSION]
       	   \\ metis_tac [])
\\ POP_ORW
\\ sg `   COMPL_PSPACE p (BIG_UNION p L1) ??? PATH p (????????pa???????? p L) =
           PATH p (compl_list p L1) ??? PATH p (????????pa???????? p L) ` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-(metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ rw [EXTENSION]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 10    *)
(*------------------*)

val PROB_COMPL_BIG_UNION_INTER_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL =
store_thm("PROB_COMPL_BIG_UNION_INTER_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL",
``!p L L1. prob_space p /\ (!x. MEM x (FLAT (L1::L)) ==> x IN events p ) /\ ~NULL L1 /\
           MUTUAL_INDEP p (L1 ??? FLAT L ??? compl_list p (L1 ??? FLAT L)) ==>
           prob p (COMPL_PSPACE p (BIG_UNION p L1) ??? PATH p (????????pa???????? p L)) =
	   prob p (COMPL_PSPACE p (BIG_UNION p L1)) *  ??? (MAP (\a. ??? (PROB_LIST p (compl_list p a))) L)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, PROB_LIST_DEF, PROD_LIST_DEF, compl_list_def]
       \\ sg `COMPL_PSPACE p (BIG_UNION p L1) ??? p_space p = COMPL_PSPACE p (BIG_UNION p L1)`
          >-(rw [INTER_COMM, COMPL_PSPACE_DEF, BIG_UNION_IN_EVENTS, EVENTS_COMPL, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV])
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, COMPL_PSPACE_DEF]
       \\ rw [rbd_list_def, rbd_struct_def, compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ rw [INTER_ASSOC]
       \\ sg `(p_space p DIFF BIG_UNION p L1) ??? p_space p =  (p_space p DIFF BIG_UNION p L1)`
          >-(metis_tac [BIG_UNION_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [GSYM COMPL_PSPACE_DEF]
       \\ sg `p_space p ??? PATH p (????????pa???????? p L) =  PATH p (????????pa???????? p L) `
          >-( metis_tac [PATH_IN_EVENTS, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, EVENTS_INTER, INTER_PSPACE])
       \\ POP_ORW
       \\ sg `??? (MAP (??a. ??? (PROB_LIST p (MAP (??a. COMPL_PSPACE p a) a))) L) =
              ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L)`
          >-( REPEAT POP_ORW
	      \\ Induct_on `L`
                 >-( rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
              \\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
       \\ metis_tac []) 
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, PROB_LIST_DEF, PROD_LIST_DEF, compl_list_def]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_ASSOC, PROB_LIST_DEF, PROD_LIST_DEF, BIG_UNION_DEF]
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [INTER_COMM, COMPL_PSPACE_DEF]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ sg `PATH p (????????pa???????? p L) ??? (p_space p DIFF BIG_UNION p L1) ???
       (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       COMPL_PSPACE p (BIG_UNION p (h'::L1)) ??? PATH p (????????pa???????? p (h::L))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, BIG_UNION_DEF, COMPL_PSPACE_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [OR_lem1, PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       COMPL_PSPACE p (BIG_UNION p (h'::h)) ??? PATH p (????????pa???????? p L)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, BIG_UNION_DEF, COMPL_PSPACE_DEF]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [OR_lem1, PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
          (COMPL_PSPACE p (BIG_UNION p (h'::L1)) ??? PATH p (????????pa???????? p (h::L))) =
        prob p (COMPL_PSPACE p (BIG_UNION p (h'::L1))) *
        ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) (h::L))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`(h'::L1)`])	
       \\ rw []
       \\ sg `(???x. x = h' ??? (MEM x L1 ??? MEM x h) ??? MEM x (FLAT L) ??? x ??? events p)`
       	  >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (h'::(L1 ??? h ??? FLAT L ??? compl_list p (h'::(L1 ??? h ??? FLAT L)))) `
       	  >-( ntac 2 (POP_ORW)
       	      \\ fs [compl_list_def]
       	      \\ fs [GSYM compl_list_def]
       	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       	      \\ Q.ABBREV_TAC `x = [h'] ??? L1 ??? h ??? FLAT L`
       	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       	      \\ Q.UNABBREV_TAC`x`
       	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
       	      \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ rw []
       	      \\ sg `L1 ??? [h'] ??? h ??? FLAT L ??? compl_list p L1 ??? [p_space p DIFF h'] ???
                     compl_list p h ??? compl_list p (FLAT L) =
	      	     L1 ??? h'::(h ??? FLAT L) ??? compl_list p L1 ???
              	     p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L))`
                 >-(rw [APPEND])
              \\ rw [])
     \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (COMPL_PSPACE p (BIG_UNION p (h'::h)) ??? PATH p (????????pa???????? p L)) =
        prob p (COMPL_PSPACE p (BIG_UNION p (h'::h))) *
        ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L)`
   >-( ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`(h'::h)`])	
       \\ rw []
       \\ sg `(???x. x = h' ??? MEM x h ??? MEM x (FLAT L) ??? x ??? events p) `
       	  >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (h'::(h ??? FLAT L ??? compl_list p (h'::(h ??? FLAT L))))`
   	   >-(  fs [compl_list_def]
       		\\ fs [GSYM compl_list_def]
       		\\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       		\\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       		\\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L`
       		\\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       		\\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       		\\ Q.UNABBREV_TAC`x`
       		\\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       		\\ irule MUTUAL_INDEP_FRONT_APPEND  
       		\\ Q.EXISTS_TAC `compl_list p L1`
       		\\ once_rewrite_tac[APPEND_ASSOC]
       		\\ irule MUTUAL_INDEP_APPEND1
       		\\ irule MUTUAL_INDEP_FRONT_APPEND  
       		\\ Q.EXISTS_TAC `L1`
       		\\ rw []
       	        \\ sg `L1 ??? [h'] ??? h ??? FLAT L ??? compl_list p L1 ??? [p_space p DIFF h'] ???
                     compl_list p h ??? compl_list p (FLAT L) =
	      	     L1 ??? h'::(h ??? FLAT L) ??? compl_list p L1 ???
              	     p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L))`
                 >-(rw [APPEND])
                \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ rw [COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
   >-(metis_tac [BIG_UNION_DEF, EVENTS_UNION, BIG_UNION_IN_EVENTS, EVENTS_COMPL])
   >-(metis_tac [BIG_UNION_DEF, EVENTS_UNION, BIG_UNION_IN_EVENTS, EVENTS_COMPL])
\\ DEP_REWRITE_TAC [GSYM RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [parallel_struct_thm]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `(h ??? FLAT L) ??? MAP (??a. p_space p DIFF a) L1 ???
                         p_space p DIFF h'::
               		 (MAP (??a. p_space p DIFF a) h ???
                	 MAP (??a. p_space p DIFF a) (FLAT L))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg ` L1 ??? [h'] ??? h ??? FLAT L ??? MAP (??a. p_space p DIFF a) L1 ???
               p_space p DIFF h'::
               (MAP (??a. p_space p DIFF a) h ???
                MAP (??a. p_space p DIFF a) (FLAT L)) =
		L1 ??? h'::(h ??? FLAT L) ??? MAP (??a. p_space p DIFF a) L1 ???
               p_space p DIFF h'::
               (MAP (??a. p_space p DIFF a) h ???
                MAP (??a. p_space p DIFF a) (FLAT L))`
	  >-( rw [APPEND])
       \\ rw [])
    >-( irule MUTUAL_INDEP_FRONT_APPEND  
        \\ Q.EXISTS_TAC `h'::(h ??? FLAT L) ??? MAP (??a. p_space p DIFF a) L1 ???
           p_space p DIFF h'::
               (MAP (??a. p_space p DIFF a) h ???
                MAP (??a. p_space p DIFF a) (FLAT L))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ rw [one_minus_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [REAL_SUB_SUB2]
\\ rw [GSYM compl_list_def]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 11    *)
(*------------------*)

val PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL = store_thm("PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\
        MUTUAL_INDEP p (FLAT L ++ compl_list p (FLAT L))  ==>
        (prob p (PATH p (????????pa???????? p L)) = ??? (MAP (\a. ??? (PROB_LIST p (compl_list p a))) L))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, PROD_LIST_DEF]
       \\ metis_tac [PROB_UNIV])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, PROD_LIST_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw []
\\ Induct_on `h`
   >-( rw [BIG_UNION_DEF, COMPL_PSPACE_DEF, compl_list_def, PATH_DEF, PROB_LIST_DEF, PROD_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????pa???????? p L) = PATH p (????????pa???????? p L)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ sg ` ??? (MAP (??a. ??? (PROB_LIST p (MAP (??a. p_space p DIFF a) a))) L) =
               ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L)`
         >-( REPEAT POP_ORW
	      \\ Induct_on `L`
                 >-( rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
              \\ REWRITE_TAC [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
       \\ POP_ORW
       \\ fs []
       \\ sg `MUTUAL_INDEP p (FLAT L ??? compl_list p (FLAT L)) `
          >-( fs [GSYM compl_list_def])
       \\ metis_tac [])
\\ rw []
\\ DEP_REWRITE_TAC [PROB_COMPL_BIG_UNION_INTER_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ disj2_tac
\\ rw [COMPL_PSPACE_DEF]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
   >-( metis_tac [BIG_UNION_IN_EVENTS, EVENTS_UNION, BIG_UNION_DEF])
\\ DEP_REWRITE_TAC [GSYM RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [parallel_struct_thm]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L ??? compl_list p (h'::(h ??? FLAT L))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [parallel_rbd_lem1]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL =
store_thm("PROB_CONSEQ_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL",
``!p L. prob_space p /\ (!x. MEM x (FLAT L) ==> x IN events p ) /\
        MUTUAL_INDEP p (FLAT L ++ compl_list p (FLAT L)) ==>
        (prob p (CONSEQ_PATH p (????????pa???????? p L)) = ??? (MAP (\a. ??? (PROB_LIST p (compl_list p a))) L))``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-(metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*    Theorem 12    *)
(*------------------*)

val PROB_PATH_OF_SUBSYSTEMS_PARALLEL_AND_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL =
store_thm("PROB_PATH_OF_SUBSYSTEMS_PARALLEL_AND_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL",
``!p L2 L1. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\
            MUTUAL_INDEP p (FLAT L1 ++ FLAT L2 ++ compl_list p (FLAT (L1 ++ L2))) ==>
     prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????pa???????? p L2)) =
     ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L1) *
     ??? (MAP (\a. ??? (PROB_LIST p (compl_list p a))) L2)``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `PATH p (????????pa???????????? p L1) ??? p_space p = PATH p (????????pa???????????? p L1)`
          >-( metis_tac [INTER_COMM, SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ Induct_on `h`
   >-(  rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, compl_list_def, PATH_DEF, COMPL_PSPACE_DEF,
            PROD_LIST_DEF, PROB_LIST_DEF]
     	\\ rw [rbd_list_def, rbd_struct_def]
	\\ rw [INTER_ASSOC]
	\\ sg `PATH p (????????pa???????????? p L1) ??? p_space p = PATH p (????????pa???????????? p L1)`
          >-( metis_tac [INTER_COMM, SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ sg `??? (MAP (??a. 1 ??? ??? (PROB_LIST p (MAP (??a. p_space p DIFF a) a))) L1) =
              ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L1)`
          >-( REPEAT POP_ORW
	      \\ Induct_on `L1`
                 >-( rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
              \\ REWRITE_TAC [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
       \\ POP_ORW
       \\ sg ` ??? (MAP (??a. ??? (PROB_LIST p (MAP (??a. p_space p DIFF a) a))) L2) =
               ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L2)`
         >-( REPEAT POP_ORW
	      \\ Induct_on `L2`
                 >-( rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
              \\ REWRITE_TAC [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF, COMPL_PSPACE_DEF])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac []) 
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, compl_list_def, PATH_DEF, COMPL_PSPACE_DEF,
       PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [BIG_UNION_DEF]
\\ rw [INTER_COMM, COMPL_PSPACE_DEF]
\\ rw [OR_lem1]
\\ rw [INTER_ASSOC]
\\ rw [GSYM compl_list_def]
\\ sg `PATH p (????????pa???????????? p L1) ??? PATH p (????????pa???????? p L2) ???
              (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????pa???????? p (h::L2))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF, compl_list_def,
           PATH_DEF, COMPL_PSPACE_DEF]
        \\ rw [rbd_list_def, rbd_struct_def]
	\\ rw [INTER_ASSOC]
	\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
	\\ rw []
	\\ rw [EXTENSION]
	\\ metis_tac [])
\\ POP_ORW
\\ sg `prob p  (PATH p (????????pa???????????? p ([p_space p DIFF h']::L1)) ??? PATH p (????????pa???????? p (h::L2))) =
	    ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) ([p_space p DIFF h']::L1)) *
            ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) (h::L2))` 
  >-( first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L1)`])	
       \\ rw []
       \\ sg `(???x. x = p_space p DIFF h' ??? (MEM x (FLAT L1) ??? MEM x h) ??? MEM x (FLAT L2) ???
                x ??? events p) `
          >-(metis_tac [EVENTS_COMPL])
       \\ sg `MUTUAL_INDEP p
          (p_space p DIFF h'::
               (FLAT L1 ??? h ??? FLAT L2 ???
                compl_list p (p_space p DIFF h'::(FLAT L1 ??? h ??? FLAT L2)))) `
          >-( ntac 2 (POP_ORW)
	      \\ fs [compl_list_def]
	      \\ sg `p_space p DIFF (p_space p DIFF h') = h' `
	         >-( metis_tac [INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL, INTER_COMM])
	      \\ POP_ORW
	      \\ fs [GSYM compl_list_def]
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ Q.ABBREV_TAC `x =  [p_space p DIFF h'] ??? FLAT L1 ??? h ??? FLAT L2`
	      \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	      \\ Q.UNABBREV_TAC`x`
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
    	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ Q.ABBREV_TAC `x = compl_list p (FLAT L1) ??? ([p_space p DIFF h'] ???
	                           (compl_list p h ??? compl_list p (FLAT L2))) `
              \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ Q.UNABBREV_TAC`x`
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ rw []
       	      \\ sg `FLAT L1 ??? [h'] ??? h ??? FLAT L2 ??? compl_list p (FLAT L1) ???
                     [p_space p DIFF h'] ??? compl_list p h ??? compl_list p (FLAT L2) =
		     FLAT L1 ??? h'::(h ??? FLAT L2) ??? compl_list p (FLAT L1) ???
           	     p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L2))`
                 >-(rw [APPEND])
              \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ sg `p_space p DIFF (p_space p DIFF h') = h' `
   >-( metis_tac [INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL, INTER_COMM])
\\ POP_ORW
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

val PROB_CONSEQ_PATH_OF_MIX_SUBSYSTEMS_PARALLEL_AND_COMPL_SUBSYSTEMS_PARALLEL =
store_thm("PROB_CONSEQ_PATH_OF_MIX_SUBSYSTEMS_PARALLEL_AND_COMPL_SUBSYSTEMS_PARALLEL",
``!p L1 L2. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\
            MUTUAL_INDEP p (FLAT L1 ++ FLAT L2 ++ compl_list p (FLAT (L1 ++ L2))) ==>
     prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????????? p L1); CONSEQ_PATH p (????????pa???????? p L2)]) =
     ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L1) *
     ??? (MAP (\a. ??? (PROB_LIST p (compl_list p a))) L2)``,
rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-(metis_tac [SUBSYSTEMS_PARALLEL_IN_EVENTS])
   >-(metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS])
   >-(metis_tac [SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-(metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, PATH_IN_EVENTS])
   >-(metis_tac [SUBSYSTEMS_PARALLEL_IN_EVENTS])
   >-(metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `PATH p (????????pa???????????? p L1) ??? (PATH p (????????pa???????? p L2) ??? p_space p) =
       PATH p (????????pa???????????? p L1) ??? PATH p (????????pa???????? p L2)`
   >-(metis_tac [INTER_COMM, EVENTS_COMPL, INTER_PSPACE, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS,
                 PATH_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL_AND_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

        (*-----------------------------------------------------------------------------*)  
	(*    Mix Between CCD Subsystems Connected with RBDs Series and RBDs Parallel  *)
	(*-----------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES=
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES",
``!p L1 L2. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\ (???x. MEM x L2 ??? ~NULL x) /\
            MUTUAL_INDEP p (FLAT (L1 ++ L2) ++ compl_list p (FLAT (L1 ++ L2))) ==>
 prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p L2)) =
 prob p (PATH p (????????pa???????????? p L1)) * prob p (PATH p (????????sr???????????? p L2))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????????? p L2) = PATH p (????????sr???????????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV])
\\ Induct_on `h`
   >-(  rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ rw [PROB_EMPTY])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
\\ sg `PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????????? p L1) ??? h' =
       PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p ([h']::L2)) `
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `h' ??? p_space p = h'`
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p ([h']::L2))) =
       prob p (PATH p (????????pa???????????? p L1)) * prob p (PATH p (????????sr???????????? p ([h']::L2)))`
   >-(  ntac 5 (pop_assum mp_tac)
   	\\ first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`])	
   	\\ rw []
	\\ fs []
	\\ sg `(???x. MEM x (FLAT L1) ??? x = h' ??? MEM x (FLAT L2) ??? x ??? events p) `
	   >-(metis_tac [])
        \\ sg `(???x. x = [h'] ??? MEM x L2 ??? ~NULL x) `
	   >-(metis_tac [NULL])
        \\ sg`MUTUAL_INDEP p (FLAT L1 ??? h'::FLAT L2 ??? compl_list p (FLAT L1 ??? h'::FLAT L2)) `
           >-( fs [COMPL_LIST_SPLIT]
	       \\ fs [compl_list_def]
	       \\ fs [GSYM compl_list_def]
	       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `compl_list p h`
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `h`
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ rw []
	       \\ sg `h'::
               	     (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                     compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)) =
		     h'::
               	     (h ??? FLAT L1 ??? FLAT L2 ???
               	      p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
                  >-( rw [APPEND])
	       \\ rw [])
         \\ metis_tac [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ sg `PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????????? p L1) ??? BIG_UNION p h =
       PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p L2)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p L2)) =
       prob p (PATH p (????????pa???????????? p (h::L1))) * prob p (PATH p (????????sr???????????? p L2))` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-(metis_tac [])
          >-(metis_tac [])
          >-(metis_tac [])
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h']`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
             compl_list p h ??? compl_list p (FLAT L1) ???  compl_list p (FLAT L2)) =
	      h'::(h ??? FLAT L1 ??? FLAT L2 ??? p_space p DIFF h'::
	      (compl_list p h ??? compl_list p (FLAT L1) ??? compl_list p (FLAT L2)))` 
                  >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ sg `PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p ([h']::L2)) ???
       (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p L2)) =
       PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p ([h']::L2))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ sg `h' ??? p_space p = h'`
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p ([h']::L2))) =
       prob p (PATH p (????????pa???????????? p (h::L1))) * prob p (PATH p (????????sr???????????? p ([h']::L2)))`
   >-( first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`])	
   	\\ rw []
	\\ fs []
	\\ sg `(???x.
             (MEM x h ??? MEM x (FLAT L1)) ??? x = h' ??? MEM x (FLAT L2) ???  x ??? events p) `
	   >-(metis_tac [])
        \\ sg `(???x. x = [h'] ??? MEM x L2 ??? ~NULL x)`
	   >-(metis_tac [NULL])
        \\ sg `MUTUAL_INDEP p (h ??? FLAT L1 ??? h'::FLAT L2 ??? compl_list p (h ??? FLAT L1 ??? h'::FLAT L2)) `
           >-( fs [COMPL_LIST_SPLIT]
       	       \\ fs [compl_list_def]
       	       \\ fs [GSYM compl_list_def]
	       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	       
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ rw []
	       \\ sg `h'::
               	     (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                     compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)) =
		     h'::
               	     (h ??? FLAT L1 ??? FLAT L2 ???
               	      p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
                  >-( rw [APPEND])
	       \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L1) ??? h' = PATH p (????????pa???????????? p ([h']::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L1) ??? BIG_UNION p h = PATH p (????????pa???????????? p (h::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p ([h']::L1)) ??? PATH p (????????pa???????????? p (h::L1)) =
       PATH p (????????pa???????????? p ([h']::h::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW       
\\ ntac 4 (pop_assum mp_tac)
\\ ntac 2 (POP_ORW)
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h`
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	       
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h ??? FLAT L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-( rw [NULL])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*      Theorem 16      *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES  =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES",
``!p L1 L2. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2)) ??? x ??? events p) ???
            (???x. MEM x L2 ??? ~NULL x) ???
            MUTUAL_INDEP p (FLAT (L1 ??? L2) ??? compl_list p (FLAT (L1 ??? L2)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????????? p L1); CONSEQ_PATH p (????????sr???????????? p L2)])  =
  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L1) * ??? (MAP (\a. ??? (PROB_LIST p a)) L2)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `PATH p (????????pa???????????? p L1) ??? (PATH p (????????sr???????????? p L2) ??? p_space p) =
       PATH p (????????pa???????????? p L1) ??? (PATH p (????????sr???????????? p L2))`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1 ??? FLAT L2)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw [])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2 ??? compl_list p (FLAT L1 ??? FLAT L2)`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_NO =
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_NO",
``!p L1 L2. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\ (???x. MEM x L2 ??? ~NULL x) /\
            MUTUAL_INDEP p (FLAT (L1 ++ L2) ++ compl_list p (FLAT (L1 ++ L2))) ==>
 prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????? p L2)) =
 prob p (PATH p (????????pa???????????? p L1)) * prob p (PATH p (????????sr???????? p L2))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????? p L2) = PATH p (????????sr???????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV])
\\ Induct_on `h`
   >-(  rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ rw [PROB_EMPTY])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
\\ sg `PATH p (????????sr???????? p L2) ??? PATH p (????????pa???????????? p L1) ??? h' =
       PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????? p ([p_space p DIFF h']::L2)) `
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ rw [DIFF_INTER]
       \\ sg `p_space p DIFF (p_space p DIFF h') = h'`
          >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????? p ([p_space p DIFF h']::L2))) =
       prob p (PATH p (????????pa???????????? p L1)) * prob p (PATH p (????????sr???????? p ([p_space p DIFF h']::L2)))`
   >-(  ntac 5 (pop_assum mp_tac)
   	\\ first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L2)`])	
   	\\ rw []
	\\ fs []
	\\ sg `(???x. MEM x (FLAT L1) ??? x = p_space p DIFF h' ??? MEM x (FLAT L2) ??? x ??? events p) `
	   >-(metis_tac [EVENTS_COMPL])
        \\ sg `(???x. x = [p_space p DIFF h'] ??? MEM x L2 ??? ~NULL x) `
	   >-(metis_tac [NULL])
        \\ sg`MUTUAL_INDEP p (FLAT L1 ??? p_space p DIFF h'::FLAT L2 ???
                              compl_list p (FLAT L1 ??? p_space p DIFF h'::FLAT L2))`
           >-( fs [COMPL_LIST_SPLIT]
       	       \\ fs [compl_list_def]
       	       \\ fs [GSYM compl_list_def]
       	       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       	       \\ sg `p_space p DIFF (p_space p DIFF h') = h'`
               	   >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF])
               \\ POP_ORW
       	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       	       \\ irule MUTUAL_INDEP_FRONT_APPEND
       	       \\ Q.EXISTS_TAC `h`
       	       \\ once_rewrite_tac[APPEND_ASSOC]
       	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_FRONT_APPEND
       	       \\ Q.EXISTS_TAC `compl_list p h`
       	       \\ once_rewrite_tac[APPEND_ASSOC]
       	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ Q.ABBREV_TAC `x = [h'] ++ h`
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ Q.UNABBREV_TAC`x`
	       \\ rw []
	       \\ sg `h'::
               	         (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                          compl_list p h ??? compl_list p (FLAT L1) ???
                  	  compl_list p (FLAT L2)) =
	      	      h'::
			 (h ??? FLAT L1 ??? FLAT L2 ???
                         p_space p DIFF h'::
                    	 (compl_list p h ??? compl_list p (FLAT L1) ???
                     	 compl_list p (FLAT L2)))` 
                  >-( rw [APPEND])
              \\ rw [])
         \\ metis_tac [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ sg `PATH p (????????sr???????? p L2) ??? PATH p (????????pa???????????? p L1) ??? BIG_UNION p h =
       PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr????????  p L2)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????? p L2)) =
       prob p (PATH p (????????pa???????????? p (h::L1))) * prob p (PATH p (????????sr???????? p L2))` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-(metis_tac [])
          >-(metis_tac [])
          >-(metis_tac [])
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h']`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
             compl_list p h ??? compl_list p (FLAT L1) ???  compl_list p (FLAT L2)) =
	      h'::(h ??? FLAT L1 ??? FLAT L2 ??? p_space p DIFF h'::
	      (compl_list p h ??? compl_list p (FLAT L1) ??? compl_list p (FLAT L2)))` 
                  >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ sg `PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????? p ([p_space p DIFF h']::L2)) ???
       (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????? p L2)) =
       PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????? p ([p_space p DIFF h']::L2))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [DIFF_INTER]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????? p ([p_space p DIFF h']::L2))) =
       prob p (PATH p (????????pa???????????? p (h::L1))) * prob p (PATH p (????????sr???????? p ([p_space p DIFF h']::L2)))`
   >-( first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L2)`])	
   	\\ rw []
	\\ fs []
	\\ sg `(???x. (MEM x h ??? MEM x (FLAT L1)) ??? x = p_space p DIFF h' ???
                     MEM x (FLAT L2) ??? x ??? events p)`
	   >-(metis_tac [EVENTS_COMPL])
        \\ sg `(???x. x = [p_space p DIFF h'] ??? MEM x L2 ??? ~NULL x)`
	   >-(metis_tac [NULL])
        \\ sg `MUTUAL_INDEP p (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2 ???
                               compl_list p (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2)) `
           >-( ntac 3 (POP_ORW)
	       \\ fs [COMPL_LIST_SPLIT]
       	       \\ fs [compl_list_def]
       	       \\ fs [GSYM compl_list_def]
	       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	       \\  sg `p_space p DIFF (p_space p DIFF h') = h'`
               	   >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF])
               \\ POP_ORW
               \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ rw []
	       \\ sg `h'::
               	     (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                     compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)) =
		     h'::
               	     (h ??? FLAT L1 ??? FLAT L2 ???
               	      p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
                  >-( rw [APPEND])
	       \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L1) ??? h' = PATH p (????????pa???????????? p ([h']::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L1) ??? BIG_UNION p h = PATH p (????????pa???????????? p (h::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p ([h']::L1)) ??? PATH p (????????pa???????????? p (h::L1)) =
       PATH p (????????pa???????????? p ([h']::h::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW       
\\ ntac 4 (pop_assum mp_tac)
\\ ntac 2 (POP_ORW)
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h`
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	       
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])    
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [p_space p DIFF h'] ??? FLAT L2`
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\  Q.UNABBREV_TAC `x `
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\  sg `p_space p DIFF (p_space p DIFF h') = h'`
            >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF])
       \\ POP_ORW
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h']`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p h ??? compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
	      h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1))`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h'::(h ??? FLAT L1)`
       \\ sg `(h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                compl_list p (FLAT L2))) =
		h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
         >-(rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 17       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_NO  =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_NO",
``!p L1 L2. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2)) ??? x ??? events p) ???
            (???x. MEM x L2 ??? ~NULL x) ???
            MUTUAL_INDEP p (FLAT (L1 ??? L2) ??? compl_list p (FLAT (L1 ??? L2)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????????? p L1); CONSEQ_PATH p (????????sr????????  p L2)])  =
  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L1) * ??? (MAP (\a. 1 - ??? (PROB_LIST p a)) L2)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `PATH p (????????pa???????????? p L1) ??? (PATH p (????????sr???????? p L2) ??? p_space p) =
       PATH p (????????pa???????????? p L1) ??? (PATH p (????????sr???????? p L2))`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_NO]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ fs[COMPL_LIST_SPLIT])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2 ??? compl_list p (FLAT L1 ??? FLAT L2)`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_YES=
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_YES",
``!p L1 L2. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\ (???x. MEM x L2 ??? ~NULL x) /\
            MUTUAL_INDEP p (FLAT (L1 ++ L2) ++ compl_list p (FLAT (L1 ++ L2))) ==>
 prob p (PATH p (????????pa???????? p L1) ??? PATH p (????????sr???????????? p L2)) =
 prob p (PATH p (????????pa???????? p L1)) * prob p (PATH p (????????sr???????????? p L2))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????????? p L2) = PATH p (????????sr???????????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV])
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ sg `p_space p ??? PATH p (????????pa???????? p L1) = PATH p (????????pa???????? p L1)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac [])
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ rw [OR_lem1]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ???
       (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([p_space p DIFF h']::L2))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([[p_space p DIFF h']]))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([p_space p DIFF h']::L2))) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr???????????? p ([p_space p DIFF h']::L2)))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L2)`])	
       \\ rw []
       \\ sg `(???x.
             (MEM x h ??? MEM x (FLAT L1)) ??? x = p_space p DIFF h' ???
             MEM x (FLAT L2) ???
             x ??? events p) `
          >-(metis_tac [EVENTS_COMPL]) 
       \\ sg `(???x. x = [p_space p DIFF h'] ??? MEM x L2 ??? ~NULL x) ` 
       	   >-(metis_tac [NULL]) 
       \\ sg `MUTUAL_INDEP p
          (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2 ???
           compl_list p (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2)) `
         >-( fs [COMPL_LIST_SPLIT]
       	     \\ fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
       	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	     \\ ntac 3 (POP_ORW)
	     \\ sg `p_space p DIFF (p_space p DIFF h') = h'`
                >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF])
             \\ POP_ORW
       	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ rw []
	     \\ sg `h'::
                       (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                       compl_list p h ??? compl_list p (FLAT L1) ???
                       compl_list p (FLAT L2)) =  h'::
                       (h ??? FLAT L1 ??? FLAT L2 ???
               	        p_space p DIFF h'::
                    	(compl_list p h ??? compl_list p (FLAT L1) ???
                     	compl_list p (FLAT L2)))` 
                >-(rw [APPEND])
            \\ rw [])
   
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
          (PATH p (????????pa???????? p (h::L1)) ???
           PATH p (????????sr???????????? p [[p_space p DIFF h']])) =
      prob p (PATH p (????????pa???????? p (h::L1))) *
            prob p (PATH p (????????sr???????????? p [[p_space p DIFF h']]))` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [EVENTS_COMPL])
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\  sg `p_space p DIFF (p_space p DIFF h') = h'`
            >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF])
       \\ POP_ORW
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ fs [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2 ??? [p_space p DIFF h'] `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h'] ++ h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???  compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( rw [NULL])
   >-(metis_tac [])
   >-(metis_tac [EVENTS_COMPL])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1 ??? FLAT L2`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
    >-(
       irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC ` p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 18       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_YES  =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_YES",
``!p L1 L2. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2)) ??? x ??? events p) ???
            (???x. MEM x L2 ??? ~NULL x) ???
            MUTUAL_INDEP p (FLAT (L1 ??? L2) ??? compl_list p (FLAT (L1 ??? L2)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????? p L1); CONSEQ_PATH p (????????sr???????????? p L2)])  =
  ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L1) * ??? (MAP (\a. ??? (PROB_LIST p a)) L2)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `PATH p (????????pa???????? p L1) ??? (PATH p (????????sr???????????? p L2) ??? p_space p) =
       PATH p (????????pa???????? p L1) ??? (PATH p (????????sr???????????? p L2))`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_YES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1 ??? FLAT L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ fs[COMPL_LIST_SPLIT])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ fs[COMPL_LIST_SPLIT]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO =
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO",
``!p L1 L2. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2)) ==> x IN events p ) /\ (???x. MEM x L2 ??? ~NULL x) /\
            MUTUAL_INDEP p (FLAT (L1 ++ L2) ++ compl_list p (FLAT (L1 ++ L2))) ==>
 prob p (PATH p (????????pa???????? p L1) ??? PATH p (????????sr???????? p L2)) =
 prob p (PATH p (????????pa???????? p L1)) * prob p (PATH p (????????sr???????? p L2))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????? p L2) = PATH p (????????sr???????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV])
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ sg `p_space p ??? PATH p (????????pa???????? p L1) = PATH p (????????pa???????? p L1)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac [])
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ rw [OR_lem1]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p (????????sr???????? p L2) ??? PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ???
       (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([h']::L2))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ sg `p_space p DIFF h' ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([[h']]))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `(p_space p DIFF h' ??? p_space p) = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([h']::L2))) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr????????  p ([h']::L2)))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`])	
       \\ rw []
       \\ sg `(???x.
             (MEM x h ??? MEM x (FLAT L1)) ??? x =  h' ???
             MEM x (FLAT L2) ???
             x ??? events p) `
          >-(metis_tac [EVENTS_COMPL]) 
       \\ sg `(???x. x = [h'] ??? MEM x L2 ??? ~NULL x) ` 
       	   >-(metis_tac [NULL]) 
       \\ sg `MUTUAL_INDEP p (h ??? FLAT L1 ??? h'::FLAT L2 ??? compl_list p (h ??? FLAT L1 ??? h'::FLAT L2))`
         >-( ntac 3 (POP_ORW)
	     \\ fs [COMPL_LIST_SPLIT]
       	     \\ fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
       	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	  
       	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	     \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1 ??? FLAT L2 `
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ Q.UNABBREV_TAC `x`
	     \\ rw []
	     \\ sg `h'::
                       (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                       compl_list p h ??? compl_list p (FLAT L1) ???
                       compl_list p (FLAT L2)) =  h'::
                       (h ??? FLAT L1 ??? FLAT L2 ???
               	        p_space p DIFF h'::
                    	(compl_list p h ??? compl_list p (FLAT L1) ???
                     	compl_list p (FLAT L2)))` 
                >-(rw [APPEND])
            \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p [[h']])) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr???????? p [[h']]))` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [EVENTS_COMPL])
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ fs [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2 ??? [p_space p DIFF h'] `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ Q.ABBREV_TAC `x = [h'] ??? FLAT L2`
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ Q.UNABBREV_TAC `x`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p h ??? compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1 ??? FLAT L2`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2)) =
              h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC ` p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1))`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                compl_list p (FLAT L2)) =
	      h'::
               (h ??? FLAT L1 ??? FLAT L2 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)))	` 
          >-( rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 19       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO  =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO",
``!p L1 L2. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2)) ??? x ??? events p) ???
            (???x. MEM x L2 ??? ~NULL x) ???
            MUTUAL_INDEP p (FLAT (L1 ??? L2) ??? compl_list p (FLAT (L1 ??? L2)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????? p L1); CONSEQ_PATH p (????????sr???????? p L2)])  =
  ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L1) * ??? (MAP (\a. 1 - ??? (PROB_LIST p a)) L2)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `PATH p (????????pa???????? p L1) ??? (PATH p (????????sr???????? p L2) ??? p_space p) =
       PATH p (????????pa???????? p L1) ??? (PATH p (????????sr???????? p L2))`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ fs[COMPL_LIST_SPLIT])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ fs[COMPL_LIST_SPLIT]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES =
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES",
``!p L1 L2 L3. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2 ++ L3)) ==> x IN events p ) /\
               (???x. MEM x (L2 ++ L3) ??? ~NULL x) /\
               MUTUAL_INDEP p (FLAT (L1 ++ L2 ++ L3) ++ compl_list p (FLAT (L1 ++ L2 ++ L3))) ==>
 prob p (PATH p (????????pa???????? p L1) ??? PATH p (????????sr???????? p L2)  ??? PATH p (????????sr???????????? p L3)) =
 prob p (PATH p (????????pa???????? p L1)) * prob p (PATH p (????????sr???????? p L2)) * prob p (PATH p (????????sr???????????? p L3))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????? p L2) = PATH p (????????sr???????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV]
       \\ once_rewrite_tac [INTER_COMM]
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES_AND_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-( irule MUTUAL_INDEP_APPEND1
	      \\ fs [COMPL_LIST_SPLIT]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       	      \\ irule MUTUAL_INDEP_append_sym
	      \\ rw [])
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
       \\ rw []
          >-( irule MUTUAL_INDEP_FRONT_APPEND
	      \\ Q.EXISTS_TAC `FLAT L2`
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `compl_list p (FLAT L2 ??? FLAT L3)`
       	      \\ irule MUTUAL_INDEP_append_sym
	      \\ rw [])
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
       \\ rw []
          >-( fs [COMPL_LIST_SPLIT]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `FLAT L3`
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       	      \\ irule MUTUAL_INDEP_append_sym
	      \\ rw [])
       \\ REAL_ARITH_TAC)
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ sg `p_space p ??? PATH p (????????pa???????? p L1) = PATH p (????????pa???????? p L1)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ rw [OR_lem1]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p (????????sr???????????? p L3) ??? PATH p (????????sr???????? p L2) ??? PATH p (????????pa???????? p L1) ???
       (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([h']::L2)) ??? PATH p (????????sr???????????? p L3)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ sg `p_space p DIFF h' ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([[h']]))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `(p_space p DIFF h' ??? p_space p) = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([h']::L2)) ??? PATH p (????????sr???????????? p L3)) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr????????  p ([h']::L2))) *
       prob p (PATH p (????????sr???????????? p L3))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`, `L3`])	
       \\ rw []
       \\ sg `(???x.
             ((MEM x h ??? MEM x (FLAT L1)) ??? x = h' ??? MEM x (FLAT L2)) ???
             MEM x (FLAT L3) ??? x ??? events p) `
          >-(metis_tac [EVENTS_COMPL]) 
       \\ sg `(???x. (x = [h'] ??? MEM x L2) ??? MEM x L3 ??? ~NULL x)` 
       	   >-(metis_tac [NULL]) 
       \\ sg `MUTUAL_INDEP p (h ??? FLAT L1 ??? h'::FLAT L2 ??? FLAT L3 ???
                              compl_list p (h ??? FLAT L1 ??? h'::FLAT L2 ??? FLAT L3))`
         >-( ntac 3 (POP_ORW)
	     \\ fs [COMPL_LIST_SPLIT]
       	     \\ fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
       	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	  
       	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 `
	     \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ Q.UNABBREV_TAC `x`
	     \\ rw []
	     \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))`
                >-(rw [APPEND])
            \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p [[h']])) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr???????? p [[h']]))` 
   >-( DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [EVENTS_COMPL])	 
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ fs [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2  ??? FLAT L3 ??? [p_space p DIFF h'] `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ Q.ABBREV_TAC `x = [h'] ??? FLAT L2`
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ Q.UNABBREV_TAC `x`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p h ??? compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 6 (once_rewrite_tac[APPEND_ASSOC])
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1 ??? FLAT L2`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x`  
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2)) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `  FLAT L3 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1))`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
	      h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))	`
          >-( rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 20       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES  =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES",
``!p L1 L2 L3. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2 ??? L3)) ??? x ??? events p) ???
               (???x. MEM x (L2 ++ L3) ??? ~NULL x) ???
               MUTUAL_INDEP p (FLAT (L1 ??? L2 ??? L3) ??? compl_list p (FLAT (L1 ??? L2 ??? L3)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????? p L1); CONSEQ_PATH p (????????sr???????? p L2);
                         CONSEQ_PATH p (????????sr???????????? p L3)])  =
  ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L1) *
  ??? (MAP (\a. 1 - ??? (PROB_LIST p a)) L2) * ??? (MAP (\a. ??? (PROB_LIST p a)) L3)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ rw [INTER_ASSOC]
\\ sg `PATH p (????????sr???????????? p L3) ??? p_space p = PATH p (????????sr???????????? p L3)`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L3 ???  compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L1 ??? FLAT L2`
       \\ rw [])
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ fs[COMPL_LIST_SPLIT]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_SERIES_NO_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES =
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_SERIES_NO_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES",
``!p L1 L2 L3. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2 ++ L3)) ==> x IN events p ) /\
               (???x. MEM x (L2 ++ L3) ??? ~NULL x) /\
               MUTUAL_INDEP p (FLAT (L1 ++ L2 ++ L3) ++ compl_list p (FLAT (L1 ++ L2 ++ L3))) ==>
 prob p (PATH p (????????pa???????? p L1) ??? PATH p (????????sr???????? p L2)  ??? PATH p (????????pa???????????? p L3)) =
 prob p (PATH p (????????pa???????? p L1)) * prob p (PATH p (????????sr???????? p L2)) * prob p (PATH p (????????pa???????????? p L3))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????? p L2) = PATH p (????????sr???????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV]
       \\ once_rewrite_tac [INTER_COMM]
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_NO]
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
          >-( irule MUTUAL_INDEP_APPEND1
       	      \\ fs [COMPL_LIST_SPLIT]
       	      \\ irule MUTUAL_INDEP_append_sym
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ rw [])
       \\ REAL_ARITH_TAC)
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ sg `p_space p ??? PATH p (????????pa???????? p L1) = PATH p (????????pa???????? p L1)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ rw [OR_lem1]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p (????????pa???????????? p L3) ??? PATH p (????????sr???????? p L2) ??? PATH p (????????pa???????? p L1) ???
       (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([h']::L2)) ??? PATH p (????????pa???????????? p L3)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ sg `p_space p DIFF h' ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([[h']]))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `(p_space p DIFF h' ??? p_space p) = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([h']::L2)) ??? PATH p (????????pa???????????? p L3)) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr????????  p ([h']::L2))) *
       prob p (PATH p (????????pa???????????? p L3))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`, `L3`])	
       \\ rw []
       \\ sg `(???x.
             ((MEM x h ??? MEM x (FLAT L1)) ??? x = h' ??? MEM x (FLAT L2)) ???
             MEM x (FLAT L3) ??? x ??? events p) `
          >-(metis_tac [EVENTS_COMPL]) 
       \\ sg `(???x. (x = [h'] ??? MEM x L2) ??? MEM x L3 ??? ~NULL x)` 
       	   >-(metis_tac [NULL]) 
       \\ sg `MUTUAL_INDEP p (h ??? FLAT L1 ??? h'::FLAT L2 ??? FLAT L3 ???
                              compl_list p (h ??? FLAT L1 ??? h'::FLAT L2 ??? FLAT L3))`
         >-( ntac 3 (POP_ORW)
	     \\ fs [COMPL_LIST_SPLIT]
       	     \\ fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
       	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	  
       	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 6 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 `
	     \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ Q.UNABBREV_TAC `x`
	     \\ rw []
	     \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))`
                >-(rw [APPEND])
            \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p [[h']])) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr???????? p [[h']]))` 
   >-( DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [EVENTS_COMPL])	 
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ fs [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2  ??? FLAT L3 ??? [p_space p DIFF h'] `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ Q.ABBREV_TAC `x = [h'] ??? FLAT L2`
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ Q.UNABBREV_TAC `x`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p h ??? compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 6 (once_rewrite_tac[APPEND_ASSOC])
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1 ??? FLAT L2`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x`  
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2)) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `  FLAT L3 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1))`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
	      h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))	`
          >-( rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 21       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_SERIES_NO_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_SERIES_NO_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES",
``!p L1 L2 L3. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2 ??? L3)) ??? x ??? events p) ???
               (???x. MEM x (L2 ++ L3) ??? ~NULL x) ???
               MUTUAL_INDEP p (FLAT (L1 ??? L2 ??? L3) ??? compl_list p (FLAT (L1 ??? L2 ??? L3)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????? p L1); CONSEQ_PATH p (????????sr???????? p L2);
                         CONSEQ_PATH p (????????pa???????????? p L3)])  =
  ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L1) *
  ??? (MAP (\a. 1 - ??? (PROB_LIST p a)) L2) *
  ??? (MAP (??a. 1 - ??? (PROB_LIST p (compl_list p a))) L3)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ rw [INTER_ASSOC]
\\ sg `PATH p (????????pa???????????? p L3) ??? p_space p = PATH p (????????pa???????????? p L3)`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_SERIES_NO_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L3 ???  compl_list p (FLAT L1)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L1 ??? FLAT L2`
       \\ rw [])
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ fs[COMPL_LIST_SPLIT]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_SERIES_YES_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES =
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_SERIES_YES_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES",
``!p L1 L2 L3. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2 ++ L3)) ==> x IN events p ) /\
               (???x. MEM x (L2 ++ L3) ??? ~NULL x) /\
               MUTUAL_INDEP p (FLAT (L1 ++ L2 ++ L3) ++ compl_list p (FLAT (L1 ++ L2 ++ L3))) ==>
 prob p (PATH p (????????pa???????? p L1) ??? PATH p (????????sr???????????? p L2)  ??? PATH p (????????pa???????????? p L3)) =
 prob p (PATH p (????????pa???????? p L1)) * prob p (PATH p (????????sr???????????? p L2)) * prob p (PATH p (????????pa???????????? p L3))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????????? p L2) = PATH p (????????sr???????????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV]
       \\ once_rewrite_tac [INTER_COMM]
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES]
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
          >-( irule MUTUAL_INDEP_APPEND1
       	      \\ fs [COMPL_LIST_SPLIT]
       	      \\ irule MUTUAL_INDEP_append_sym
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ rw [])
       \\ REAL_ARITH_TAC)
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ sg `p_space p ??? PATH p (????????pa???????? p L1) = PATH p (????????pa???????? p L1)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ rw [OR_lem1]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p (????????pa???????????? p L3) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????? p L1) ???
       (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([p_space p DIFF h']::L2)) ??? PATH p (????????pa???????????? p L3)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([[h']]))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `(p_space p DIFF h' ??? p_space p) = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([p_space p DIFF h']::L2)) ???
       PATH p (????????pa???????????? p L3)) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr????????????  p ([p_space p DIFF h']::L2))) *
       prob p (PATH p (????????pa???????????? p L3))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L2)`, `L3`])	
       \\ rw []
       \\ sg `(???x.
             ((MEM x h ??? MEM x (FLAT L1)) ??? x = p_space p DIFF h' ??? MEM x (FLAT L2)) ???
             MEM x (FLAT L3) ??? x ??? events p) `
          >-(metis_tac [EVENTS_COMPL]) 
       \\ sg `(???x. (x = [p_space p DIFF h'] ??? MEM x L2) ??? MEM x L3 ??? ~NULL x)` 
       	   >-(metis_tac [NULL]) 
       \\ sg `MUTUAL_INDEP p (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2 ??? FLAT L3 ???
                             compl_list p (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2 ??? FLAT L3))`
         >-( ntac 3 (POP_ORW)
	     \\ fs [COMPL_LIST_SPLIT]
       	     \\ fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
       	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	  
       	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ sg `p_space p DIFF (p_space p DIFF h') = h'` 
	        >-(metis_tac [EVENTS_COMPL, P_SPACE_DIFF, INTER_COMM, INTER_PSPACE])
             \\ POP_ORW
	     \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
	     \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ Q.UNABBREV_TAC `x`
	     \\ rw []
	     \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))`
                >-(rw [APPEND])
            \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p [[h']])) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr???????? p [[h']]))` 
   >-( DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [EVENTS_COMPL])	 
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ fs [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ ntac 5 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2  ??? FLAT L3 ??? [p_space p DIFF h'] `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []      
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2)) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                   compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		   h'::(h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                   p_space p DIFF h'::
                   (compl_list p h ??? compl_list p (FLAT L1) ???
                   compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw [] 
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L3`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h'::(h ??? FLAT L1)`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                compl_list p h ??? compl_list p (FLAT L1) ???
                compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
	      h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))`	     
		     
          >-( rw [APPEND])
       \\ rw [])
     >-(metis_tac [NULL])
     >-(metis_tac [NULL])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `  FLAT L3 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                          compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
	      h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))	`
          >-( rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 22       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_SERIES_YES_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_SERIES_YES_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES",
``!p L1 L2 L3. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2 ??? L3)) ??? x ??? events p) ???
               (???x. MEM x (L2 ++ L3) ??? ~NULL x) ???
               MUTUAL_INDEP p (FLAT (L1 ??? L2 ??? L3) ??? compl_list p (FLAT (L1 ??? L2 ??? L3)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????? p L1); CONSEQ_PATH p (????????sr???????????? p L2);
                         CONSEQ_PATH p (????????pa???????????? p L3)])  =
  ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L1) *
  ??? (MAP (\a. ??? (PROB_LIST p a)) L2) *
  ??? (MAP (??a. 1 - ??? (PROB_LIST p (compl_list p a))) L3)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ rw [INTER_ASSOC]
\\ sg `PATH p (????????pa???????????? p L3) ??? p_space p = PATH p (????????pa???????????? p L3)`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_SERIES_YES_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L3 ???  compl_list p (FLAT L1) ++ compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L1 ??? FLAT L2`
       \\ rw [])
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ fs[COMPL_LIST_SPLIT]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES =
store_thm("PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES",
``!p L1 L2 L3. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2 ++ L3)) ==> x IN events p ) /\
               (???x. MEM x  (L2 ??? L3) ??? ~NULL x) /\
               MUTUAL_INDEP p (FLAT (L1 ++ L2 ++ L3) ++ compl_list p (FLAT (L1 ??? L2 ??? L3))) ==>
 prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p L2)  ??? PATH p (????????sr???????? p L3)) =
 prob p (PATH p (????????pa???????????? p L1)) * prob p (PATH p (????????sr???????????? p L2)) * prob p (PATH p (????????sr???????? p L3))``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????????? p L2) = PATH p (????????sr???????????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV]
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES_AND_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
       \\ rw []
          >-(metis_tac [])
	  >-(metis_tac [])
          >-(  fs [COMPL_LIST_SPLIT]
	       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
       	       \\ rw [])
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
       \\ rw []
          >-( irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `FLAT L3 ??? compl_list p (FLAT L2 ??? FLAT L3)`
	       \\ irule MUTUAL_INDEP_append_sym
	       \\ rw [])
       \\ disj2_tac
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
       \\ rw []
       \\ fs [COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2`
       \\ rw []) 
\\ Induct_on `h`
   >-(  rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ rw [PROB_EMPTY])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ fs []
\\ rw []
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
   >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, INTER_PSPACE, BIG_UNION_IN_EVENTS])
\\ sg `PATH p (????????sr???????? p L3) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????????? p L1) ??? h' =
       PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p ([h']::L2)) ??? PATH p (????????sr???????? p L3)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `h' ??? p_space p = h'`
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p ([h']::L2)) ??? PATH p (????????sr???????? p L3)) =
       prob p (PATH p (????????pa???????????? p L1)) * prob p (PATH p (????????sr???????????? p ([h']::L2))) * prob p (PATH p (????????sr???????? p L3))`
   >-(  ntac 5 (pop_assum mp_tac)
   	\\ first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`, `L3`])	
   	\\ rw []
	\\ fs []
	\\ sg `(???x. MEM x (FLAT L1) ??? x = h' ??? MEM x (FLAT L2) ??? MEM x (FLAT L3) ??? x ??? events p) `
	   >-(metis_tac [EVENTS_COMPL])
        \\ sg `(???x. x = [h'] ??? MEM x L2 ??? MEM x L3 ??? ~NULL x) `
	   >-(metis_tac [NULL])
        \\ sg`MUTUAL_INDEP p (FLAT L1 ??? h'::FLAT L2 ??? FLAT L3 ??? compl_list p (FLAT L1 ??? h'::FLAT L2 ??? FLAT L3))`
           >-( fs [COMPL_LIST_SPLIT]
	       \\ fs [compl_list_def]
	       \\ fs [GSYM compl_list_def]
	       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 2 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `compl_list p h`
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       	       \\ Q.EXISTS_TAC `h`
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ rw []
	       \\ sg `h'::
                      (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                      compl_list p h ??? compl_list p (FLAT L1) ???
                      compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		      h'::
               	      (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                      p_space p DIFF h'::
                      (compl_list p h ??? compl_list p (FLAT L1) ???
                      compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))`
                  >-( rw [APPEND])
	       \\ rw [])
         \\ metis_tac [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ sg `PATH p (????????sr???????? p L3) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????????? p L1) ??? BIG_UNION p h =
       PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p L2) ???  PATH p (????????sr???????? p L3)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????sr???????? p L3)) =
       prob p (PATH p (????????pa???????????? p (h::L1))) * prob p (PATH p (????????sr???????????? p L2)) * prob p (PATH p (????????sr???????? p L3))` 
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-(metis_tac [])
          >-(metis_tac [])
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[p_space p DIFF h']`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ rw []
       \\ sg `h'::
                      (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                      compl_list p h ??? compl_list p (FLAT L1) ???
                      compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		      h'::
               	      (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                      p_space p DIFF h'::
                      (compl_list p h ??? compl_list p (FLAT L1) ???
                      compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ fs [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ sg `PATH p (????????pa???????????? p L1) ??? PATH p (????????sr???????????? p ([h']::L2)) ??? PATH p (????????sr???????? p L3) ???
       (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????sr???????? p L3)) =
       PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p ([h']::L2)) ??? PATH p (????????sr???????? p L3)`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ sg `h' ??? p_space p = h'`
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????????? p (h::L1)) ??? PATH p (????????sr???????????? p ([h']::L2)) ??? PATH p (????????sr???????? p L3)) =
       prob p (PATH p (????????pa???????????? p (h::L1))) * prob p (PATH p (????????sr???????????? p ([h']::L2))) * prob p (PATH p (????????sr???????? p L3))`
   >-( first_x_assum (mp_tac o Q.SPECL [`([h']::L2)`, `L3`])	
   	\\ rw []
	\\ fs []
	\\ sg `(???x.
             (MEM x h ??? MEM x (FLAT L1)) ??? x = h' ??? MEM x (FLAT L2) ??? MEM x (FLAT L3)???  x ??? events p) `
	   >-(metis_tac [])
        \\ sg `(???x. (x = [h'] ??? MEM x L2) ??? MEM x L3 ??? ~NULL x)`
	   >-(metis_tac [NULL])
        \\ sg ` MUTUAL_INDEP p (h ??? FLAT L1 ??? h'::FLAT L2 ??? FLAT L3 ???
                                compl_list p (h ??? FLAT L1 ??? h'::FLAT L2 ??? FLAT L3))`
           >-( fs [COMPL_LIST_SPLIT]
       	       \\ fs [compl_list_def]
       	       \\ fs [GSYM compl_list_def]
	       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
	       \\ ntac 3 (POP_ORW)
	       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 3 (once_rewrite_tac[APPEND_ASSOC])
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ rw []
	       \\ sg `h'::
                      (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? [p_space p DIFF h'] ???
                      compl_list p h ??? compl_list p (FLAT L1) ???
                      compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) =
		      h'::
               	      (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                      p_space p DIFF h'::
                      (compl_list p h ??? compl_list p (FLAT L1) ???
                      compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
                  >-( rw [APPEND])
	       \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L1) ??? h' = PATH p (????????pa???????????? p ([h']::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p L1) ??? BIG_UNION p h = PATH p (????????pa???????????? p (h::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????????? p ([h']::L1)) ??? PATH p (????????pa???????????? p (h::L1)) =
       PATH p (????????pa???????????? p ([h']::h::L1))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW       
\\ ntac 4 (pop_assum mp_tac)
\\ ntac 2 (POP_ORW)
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2  ??? FLAT L3 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h`
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	       
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 ???  p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h ??? FLAT L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L3 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
   >-( rw [NULL])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L3 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3))`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `p_space p DIFF h':: (compl_list p h ??? compl_list p (FLAT L1) ??? compl_list p (FLAT L2))`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::(h ??? FLAT L1 ??? FLAT L2)`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2)) ??? compl_list p (FLAT L3)) =
	     h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ???
                p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*      Theorem 23      *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES   =
store_thm("PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES",
``!p L1 L2 L3. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2 ??? L3)) ??? x ??? events p) ???
               (???x. MEM x (L2 ??? L3) ??? ~NULL x) ???
               MUTUAL_INDEP p (FLAT (L1 ??? L2 ??? L3) ??? compl_list p (FLAT (L1 ??? L2 ??? L3)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????????? p L1); CONSEQ_PATH p (????????sr???????????? p L2);  CONSEQ_PATH p (????????sr???????? p L3)])  =
  ??? (MAP (??a. 1 ??? ??? (PROB_LIST p (compl_list p a))) L1) * ??? (MAP (\a. ??? (PROB_LIST p a)) L2) *
  ??? (MAP (\a. 1 - ??? (PROB_LIST p a)) L3)``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
\\ rw [PATH_DEF]
\\ sg `(PATH p (????????sr???????? p L3) ??? p_space p) = PATH p (????????sr???????? p L3)`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L3 ??? compl_list p (FLAT L1 ??? FLAT L2 ??? FLAT L3)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
   >-( fs [COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L1) ??? compl_list p (FLAT L2)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1 ??? FLAT L2 `
       \\ rw [])
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 ??? compl_list p (FLAT L1 ??? FLAT L2 ??? FLAT L3)`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_append_sym
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)

val PROB_PATH_OF_SUBSYSTEMS_SERIES_YES_NO_AND_SUBSYSTEMS_PARALLEL_YES_NO =
store_thm("PROB_PATH_OF_SUBSYSTEMS_SERIES_YES_NO_AND_SUBSYSTEMS_PARALLEL_YES_NO",
``!p L1 L2 L3 L4. prob_space p /\ (!x. MEM x (FLAT (L1 ++ L2 ++ L3 ++ L4)) ==> x IN events p ) /\
                  (???x. MEM x (L2 ++ L4) ??? ~NULL x) /\
               	  MUTUAL_INDEP p (FLAT (L1 ++ L2 ++ L3 ++ L4) ++ compl_list p (FLAT (L1 ++ L2 ++ L3 ++ L4))) ==>
 prob p (PATH p (????????pa???????? p L1) ??? PATH p (????????sr???????????? p L2)  ??? PATH p (????????pa???????????? p L3) ???  PATH p (????????sr???????? p L4)) =
 prob p (PATH p (????????pa???????? p L1)) * prob p (PATH p (????????sr???????????? p L2)) * prob p (PATH p (????????pa???????????? p L3)) *
 prob p (PATH p (????????sr???????? p L4)) ``,

GEN_TAC
\\ Induct
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
           COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
	   PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF]
       \\ sg `p_space p ??? PATH p (????????sr???????????? p L2) = PATH p (????????sr???????????? p L2)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [PROB_UNIV]
       \\ sg `PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????????? p L3) ??? PATH p (????????sr???????? p L4)  =
              PATH p (????????pa???????????? p L3) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????sr???????? p L4)`
          >-( rw [EXTENSION]
	      \\ metis_tac [])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES]
       \\ rw []
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
          >-( fs [COMPL_LIST_SPLIT]
	      \\ ntac 3 (once_rewrite_tac[GSYM APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw [])
       \\ disj2_tac
       \\ REAL_ARITH_TAC)
\\ Induct_on `h`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
	\\ sg `p_space p ??? PATH p (????????pa???????? p L1) = PATH p (????????pa???????? p L1)`
          >-( metis_tac [INTER_COMM, COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	                 COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS,
	                 PATH_IN_EVENTS, INTER_PSPACE])
       \\ POP_ORW
       \\ first_x_assum (match_mp_tac)
       \\ rw []
	  >-(metis_tac [])
          >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
	  >-(metis_tac [])
       \\ fs [GSYM compl_list_def]
       \\ rw [COMPL_LIST_SPLIT])
\\ rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
       COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       rbd_list_def, rbd_struct_def, compl_list_def]
\\ rw [OR_lem1]
\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ sg `PATH p (????????sr???????? p L4) ??? PATH p (????????pa???????????? p L3) ??? PATH p (????????sr???????????? p L2) ??? PATH p (????????pa???????? p L1) ???
       (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([p_space p DIFF h']::L2)) ??? PATH p (????????pa???????????? p L3) ???
       PATH p (????????sr???????? p L4) `
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw []
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p (????????pa???????? p L1) ??? (p_space p DIFF h') ??? (p_space p DIFF BIG_UNION p h) =
       PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p ([[h']]))`
   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF,
            COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_SERIES_DEF,
       	    PATH_DEF, COMPL_PSPACE_DEF, PROD_LIST_DEF, PROB_LIST_DEF,
       	    rbd_list_def, rbd_struct_def, compl_list_def]
       \\ sg `(p_space p DIFF h' ??? p_space p) = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ sg `(p_space p DIFF h') ??? p_space p = p_space p DIFF h'`
           >-( metis_tac [INTER_COMM, INTER_PSPACE, P_SPACE_DIFF, EVENTS_COMPL])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ rw [INTER_COMM]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????????? p ([p_space p DIFF h']::L2)) ???
       PATH p (????????pa???????????? p L3) ??? PATH p (????????sr???????? p L4)) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr????????????  p ([p_space p DIFF h']::L2))) *
       prob p (PATH p (????????pa???????????? p L3)) * prob p (PATH p (????????sr???????? p L4))` 
   >-( first_x_assum (mp_tac o Q.SPECL [`([p_space p DIFF h']::L2)`, `L3`, `L4`])	
       \\ rw []
       \\ sg `(???x.(((MEM x h ??? MEM x (FLAT L1)) ??? x = p_space p DIFF h' ???
                  MEM x (FLAT L2)) ??? MEM x (FLAT L3)) ??? MEM x (FLAT L4) ??? x ??? events p)`
          >-(metis_tac [EVENTS_COMPL]) 
       \\ sg `(???x. (x = [p_space p DIFF h'] ??? MEM x L2) ??? MEM x L4 ??? ~NULL x)`
       	   >-(metis_tac [NULL]) 
       \\ sg `MUTUAL_INDEP p  (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                               compl_list p  (h ??? FLAT L1 ??? p_space p DIFF h'::FLAT L2 ??? FLAT L3 ??? FLAT L4))`
         >-( ntac 3 (POP_ORW)
	     \\ fs [COMPL_LIST_SPLIT]
       	     \\ fs [compl_list_def]
       	     \\ fs [GSYM compl_list_def]
       	     \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]	  
       	     \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
	     \\ sg `p_space p DIFF (p_space p DIFF h') = h'` 
	        >-(metis_tac [EVENTS_COMPL, P_SPACE_DIFF, INTER_COMM, INTER_PSPACE])
             \\ POP_ORW
	     \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 9 (once_rewrite_tac[APPEND_ASSOC])
	     \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`	    
	     \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ ntac 7 (once_rewrite_tac[APPEND_ASSOC])
	     \\ ntac 5 (once_rewrite_tac[GSYM APPEND_ASSOC])
	     \\ irule MUTUAL_INDEP_APPEND1
	     \\ Q.UNABBREV_TAC `x`
	     \\ rw []
	     \\ sg `h'::
                    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    [p_space p DIFF h'] ??? compl_list p h ???
                    compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ???
                    compl_list p (FLAT L3) ??? compl_list p (FLAT L4)) =
		    h'::
               	    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ???
                     compl_list p (FLAT L4)))`
                >-(rw [APPEND])
            \\ rw [])
      \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (????????pa???????? p (h::L1)) ??? PATH p (????????sr???????? p [[h']])) =
       prob p (PATH p (????????pa???????? p (h::L1))) * prob p (PATH p (????????sr???????? p [[h']]))` 
   >-( DEP_REWRITE_TAC [PROB_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO]
       \\ rw []
          >-( metis_tac [])
          >-( metis_tac [])
	  >-( metis_tac [EVENTS_COMPL])	 
       \\ fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ ntac 2 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_APPEND1
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ irule MUTUAL_INDEP_append_sym
       \\ ntac 4 (once_rewrite_tac[APPEND_ASSOC])
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3  ??? FLAT L4`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ??? compl_list p (FLAT L4) `
       \\ irule MUTUAL_INDEP_append_sym
       \\ Q.UNABBREV_TAC `x`
       \\ rw []
       \\ sg `h'::
                    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    [p_space p DIFF h'] ??? compl_list p h ???
                    compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ???
                    compl_list p (FLAT L3) ??? compl_list p (FLAT L4)) =
		    h'::
               	    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ???
                     compl_list p (FLAT L4)))`
          >-( rw [APPEND])
       \\ rw [])
\\ POP_ORW
\\ fs [GSYM compl_list_def]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3)  ??? compl_list p (FLAT L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `[h']`
       \\ ntac 6 (once_rewrite_tac[APPEND_ASSOC])
       \\ Q.ABBREV_TAC `x = [h'] ??? h ??? FLAT L1`
       \\ ntac 4 (once_rewrite_tac[GSYM APPEND_ASSOC])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L2  ??? FLAT L3 ??? FLAT L4 ??? [p_space p DIFF h'] `
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ Q.UNABBREV_TAC `x `
       \\ rw []
       \\ sg `h'::
                    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    [p_space p DIFF h'] ??? compl_list p h ???
                    compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ???
                    compl_list p (FLAT L3) ??? compl_list p (FLAT L4)) =
		    h'::
               	    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ???
                     compl_list p (FLAT L4)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []      
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3  ??? FLAT L4`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2)) ??? compl_list p (FLAT L3) ??? compl_list p (FLAT L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw []
       \\ sg `h'::
                    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    [p_space p DIFF h'] ??? compl_list p h ???
                    compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ???
                    compl_list p (FLAT L3) ??? compl_list p (FLAT L4)) =
		    h'::
               	    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ???
                     compl_list p (FLAT L4)))` 
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw [] 
   >-(metis_tac [EVENTS_COMPL])
   >-(metis_tac [])
   >-( fs [COMPL_LIST_SPLIT]
       \\ fs [compl_list_def]
       \\ fs [GSYM compl_list_def]
       \\ once_rewrite_tac[(prove(``!a b c. a::b = [a] ++ b``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L3 ++ FLAT L4`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `(compl_list p h ??? compl_list p (FLAT L1) ???
                        compl_list p (FLAT L2) ??? compl_list p (FLAT L3)) ??? compl_list p (FLAT L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h'::(h ??? FLAT L1)`
       \\ rw []
       \\ sg `h'::
                    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    [p_space p DIFF h'] ??? compl_list p h ???
                    compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ???
                    compl_list p (FLAT L3) ??? compl_list p (FLAT L4)) =
		    h'::
               	    (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                    p_space p DIFF h'::
                    (compl_list p h ??? compl_list p (FLAT L1) ???
                     compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ???
                     compl_list p (FLAT L4)))`	     		     
          >-( rw [APPEND])
       \\ rw [])
     >-(metis_tac [NULL])
     >-(metis_tac [NULL])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `  FLAT L3 ??? FLAT L4 ??? p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                          compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ??? compl_list p (FLAT L4)`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `h'::h ??? FLAT L1`
       \\ rw []
       \\ sg `h'::
               (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
                p_space p DIFF h'::(compl_list p h ??? compl_list p (FLAT L1)) ???
                compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ???
                compl_list p (FLAT L4)) =
	      h':: (h ??? FLAT L1 ??? FLAT L2 ??? FLAT L3 ??? FLAT L4 ???
              p_space p DIFF h':: (compl_list p h ??? compl_list p (FLAT L1) ???
              compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ??? compl_list p (FLAT L4)))`
          >-( rw [APPEND])
       \\ rw [])
\\ rw [compl_list_def, PROB_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM compl_list_def]
\\ rw [PROB_COMPL]
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

(*----------------------*)  
(*     Theorem 24       *)
(*----------------------*)

val PROB_CONSEQ_PATH_OF_SUBSYSTEMS_SERIES_YES_NO_AND_SUBSYSTEMS_PARALLEL_YES_NO  =
store_thm("PROB_CONSEQ_PATH_OF_SUBSYSTEMS_SERIES_YES_NO_AND_SUBSYSTEMS_PARALLEL_YES_NO",
``!p L1 L2 L3 L4. prob_space p ??? (???x. MEM x (FLAT (L1 ??? L2 ??? L3 ++ L4)) ??? x ??? events p) ???
                  (???x. MEM x (L2 ++ L4) ??? ~NULL x) ???
               	  MUTUAL_INDEP p (FLAT (L1 ??? L2 ??? L3 ++ L4) ??? compl_list p (FLAT (L1 ??? L2 ??? L3 ++ L4)))  ==>
  prob p (CONSEQ_PATH p [CONSEQ_PATH p (????????pa???????? p L1); CONSEQ_PATH p (????????sr???????????? p L2);
                         CONSEQ_PATH p (????????pa???????????? p L3); CONSEQ_PATH p (????????sr???????? p L4);])  =
  ??? (MAP (??a. ??? (PROB_LIST p (compl_list p a))) L1) *
  ??? (MAP (\a. ??? (PROB_LIST p a)) L2) *
  ??? (MAP (??a. 1 - ??? (PROB_LIST p (compl_list p a))) L3) *
  ??? (MAP (\a. 1 - ??? (PROB_LIST p a)) L4) ``,

rw []
\\ DEP_REWRITE_TAC [CONSEQ_PATH_EQ_ET_PATH]
\\ rw []
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS])		  
\\ rw [PATH_DEF]
\\ rw [INTER_ASSOC]
\\ sg `PATH p (????????sr???????? p L4) ??? p_space p = PATH p (????????sr???????? p L4)`
   >-( metis_tac [COMPL_SUBSYSTEMS_PARALLEL_IN_EVENTS, SUBSYSTEMS_PARALLEL_IN_EVENTS,
	          COMPL_SUBSYSTEMS_SERIES_IN_EVENTS, SUBSYSTEMS_SERIES_IN_EVENTS, EVENTS_INTER,
	          PATH_IN_EVENTS, EVENTS_COMPL, INTER_COMM, INTER_PSPACE])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES_YES_NO_AND_SUBSYSTEMS_PARALLEL_YES_NO]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_SERIES]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L3 ??? FLAT L4 ???  compl_list p (FLAT L1) ++ compl_list p (FLAT L2) ??? compl_list p (FLAT L3)
                       ??? compl_list p (FLAT L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `FLAT L1`
       \\ rw []
       \\ fs [COMPL_LIST_SPLIT])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( fs[COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L4 ??? compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ??? compl_list p (FLAT L3)
                       ??? compl_list p (FLAT L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L1 ??? FLAT L2`
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_PARALLEL]
\\ rw []
   >-( fs [COMPL_LIST_SPLIT]
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `FLAT L2 ??? FLAT L3 ??? FLAT L4`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND  
       \\ Q.EXISTS_TAC `compl_list p (FLAT L2) ??? compl_list p (FLAT L3) ??? compl_list p (FLAT L4)`
       \\ irule MUTUAL_INDEP_append_sym
       \\ rw [])
\\ disj2_tac
\\ DEP_REWRITE_TAC [PROB_PATH_OF_COMPL_SUBSYSTEMS_SERIES]
\\ rw []
\\ fs[COMPL_LIST_SPLIT]
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `compl_list p (FLAT L1) ??? compl_list p (FLAT L2) ??? compl_list p (FLAT L3)`
\\ once_rewrite_tac[APPEND_ASSOC]
\\ irule MUTUAL_INDEP_APPEND1
\\ irule MUTUAL_INDEP_FRONT_APPEND  
\\ Q.EXISTS_TAC `FLAT L1 ??? FLAT L2 ??? FLAT L3`
\\ rw []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

			(*------------------------------------------*)  
			(*  Sandard Meta Language (SML) Functions   *)
			(*------------------------------------------*)

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

fun PROBABILITY CLASS X =
let 
    val value = HOL4_EVALUATION  X;
in
    print("Probability of " ^ " " ^ (term_to_string (CLASS)) ^ " " ^ "=" ^ " ");
    print(Real.toString (value) ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)


val _ = export_theory();

(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
		(*-----------------------------------------------------------------*)
			    (*-----------------------------------------*)
			               (*-------------------*)
					    (*--------*)