(* ========================================================================= *)
(* File Name: Smart_Power_Grid.sml	          	                     *)
(*---------------------------------------------------------------------------*)
(*          Description: Reliability Analysis of an Interconnected Microgrid *)
(*                       Renewable and Clean (MRG) Power Grids               *)
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
	  "real_sigmaTheory", "cardinalTheory", "FTreeTheory", "ETreeTheory",
	  "RBDTheory", "CCDTheory", "CCD_RBDTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax lebesgueTheory real_sigmaTheory cardinalTheory
     FTreeTheory ETreeTheory RBDTheory CCDTheory CCD_RBDTheory;

val _ = new_theory "Smart_Power_Grid";

(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val R_WTA_DEF = Define
` R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] =
  rbd_struct p (parallel (rbd_list [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]))`;

val R_WTB_DEF = Define
` R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] =
  rbd_struct p (parallel (rbd_list [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]))`;

val R_WTC_DEF = Define
` R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] =
  rbd_struct p (parallel (rbd_list [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]))`;

val R_WTD_DEF = Define
` R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] =
  rbd_struct p (parallel (rbd_list [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]))`;

val R_PVE_DEF = Define
` R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] =
  rbd_struct p (series (rbd_list [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]))`;

val R_PVF_DEF = Define
` R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] =
  rbd_struct p (series (rbd_list [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]))`;

val R_PVG_DEF = Define
` R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] =
  rbd_struct p (series (rbd_list [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]))`;

val R_PVH_DEF = Define
` R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] =
  rbd_struct p (series (rbd_list [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))`;
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_0_MW_SMART_GRID`` 
``(1 −
         (1 − prob p WT_A1) *
         ((1 − prob p WT_A2) *
          ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
        ((1 −
          (1 − prob p WT_B1) *
          ((1 − prob p WT_B2) *
           ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
         ((1 −
           (1 − prob p WT_C1) *
           ((1 − prob p WT_C2) *
            ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
          (1 −
           (1 − prob p WT_D1) *
           ((1 − prob p WT_D2) *
            ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) *
        (prob p PV_E1 *
         (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
         (prob p PV_F1 *
          (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
          (prob p PV_G1 *
           (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
           (prob p PV_H1 *
            (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5)))))))``
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_17_5_MW_SMART_GRID`` 
``(1 − prob p WT_A1) *
   ((1 − prob p WT_A2) *
    ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5)))) *
   (prob p PV_E1 *
    (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
    (prob p PV_F1 *
     (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
     (prob p PV_G1 *
      (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
      (prob p PV_H1 *
       (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))) *
   ((1 −
     (1 − prob p WT_B1) *
     ((1 − prob p WT_B2) *
      ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
    ((1 −
      (1 − prob p WT_C1) *
      ((1 − prob p WT_C2) *
       ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
     (1 −
      (1 − prob p WT_D1) *
      ((1 − prob p WT_D2) *
       ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) +
   ((1 − prob p WT_B1) *
    ((1 − prob p WT_B2) *
     ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5)))) *
    (prob p PV_E1 *
     (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
     (prob p PV_F1 *
      (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
      (prob p PV_G1 *
       (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
       (prob p PV_H1 *
        (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))) *
    ((1 −
      (1 − prob p WT_A1) *
      ((1 − prob p WT_A2) *
       ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
     ((1 −
       (1 − prob p WT_C1) *
       ((1 − prob p WT_C2) *
        ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
      (1 −
       (1 − prob p WT_D1) *
       ((1 − prob p WT_D2) *
        ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) +
    ((1 − prob p WT_C1) *
     ((1 − prob p WT_C2) *
      ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5)))) *
     (prob p PV_E1 *
      (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
      (prob p PV_F1 *
       (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
       (prob p PV_G1 *
        (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
        (prob p PV_H1 *
         (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))) *
     ((1 −
       (1 − prob p WT_A1) *
       ((1 − prob p WT_A2) *
        ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
      ((1 −
        (1 − prob p WT_B1) *
        ((1 − prob p WT_B2) *
         ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
       (1 −
        (1 − prob p WT_D1) *
        ((1 − prob p WT_D2) *
         ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) +
     ((1 − prob p WT_D1) *
      ((1 − prob p WT_D2) *
       ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5)))) *
      (prob p PV_E1 *
       (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
       (prob p PV_F1 *
        (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
        (prob p PV_G1 *
         (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
         (prob p PV_H1 *
          (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))) *
      ((1 −
        (1 − prob p WT_A1) *
        ((1 − prob p WT_A2) *
         ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
       ((1 −
         (1 − prob p WT_B1) *
         ((1 − prob p WT_B2) *
          ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
        (1 −
         (1 − prob p WT_C1) *
         ((1 − prob p WT_C2) *
          ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))))) +
      ((1 −
        (1 − prob p WT_A1) *
        ((1 − prob p WT_A2) *
         ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
       ((1 −
         (1 − prob p WT_B1) *
         ((1 − prob p WT_B2) *
          ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
        ((1 −
          (1 − prob p WT_C1) *
          ((1 − prob p WT_C2) *
           ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
         (1 −
          (1 − prob p WT_D1) *
          ((1 − prob p WT_D2) *
           ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) *
       (prob p PV_F1 *
        (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
        (prob p PV_G1 *
         (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
         (prob p PV_H1 *
          (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5)))))) *
       (1 −
        prob p PV_E1 *
        (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5)))) +
       ((1 −
         (1 − prob p WT_A1) *
         ((1 − prob p WT_A2) *
          ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
        ((1 −
          (1 − prob p WT_B1) *
          ((1 − prob p WT_B2) *
           ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
         ((1 −
           (1 − prob p WT_C1) *
           ((1 − prob p WT_C2) *
            ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
          (1 −
           (1 − prob p WT_D1) *
           ((1 − prob p WT_D2) *
            ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) *
        (prob p PV_E1 *
         (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
         (prob p PV_G1 *
          (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
          (prob p PV_H1 *
           (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5)))))) *
        (1 −
         prob p PV_F1 *
         (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5)))) +
        ((1 −
          (1 − prob p WT_A1) *
          ((1 − prob p WT_A2) *
           ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
         ((1 −
           (1 − prob p WT_B1) *
           ((1 − prob p WT_B2) *
            ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
          ((1 −
            (1 − prob p WT_C1) *
            ((1 − prob p WT_C2) *
             ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
           (1 −
            (1 − prob p WT_D1) *
            ((1 − prob p WT_D2) *
             ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) *
         (prob p PV_E1 *
          (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
          (prob p PV_F1 *
           (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
           (prob p PV_H1 *
            (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5)))))) *
         (1 −
          prob p PV_G1 *
          (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5)))) +
         (1 −
          (1 − prob p WT_A1) *
          ((1 − prob p WT_A2) *
           ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5))))) *
         ((1 −
           (1 − prob p WT_B1) *
           ((1 − prob p WT_B2) *
            ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5))))) *
          ((1 −
            (1 − prob p WT_C1) *
            ((1 − prob p WT_C2) *
             ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5))))) *
           (1 −
            (1 − prob p WT_D1) *
            ((1 − prob p WT_D2) *
             ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) *
         (prob p PV_E1 *
          (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5))) *
          (prob p PV_F1 *
           (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5))) *
           (prob p PV_G1 *
            (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5)))))) *
         (1 −
          prob p PV_H1 *
          (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))))))``
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_35_MW_SMART_GRID`` 
``(1 −
    (1 − prob p WT_A1 t) *
    ((1 − prob p WT_A2 t) *
     ((1 − prob p  WT_A3 t) *
      ((1 − prob p WT_A4 t) * (1 − prob p WT_A5 t))))) *
   ((1 −
     (1 − prob p WT_B1 t)) *
     ((1 − prob p WT_B2 t)) *
      ((1 − prob p WT_B3 t)) *
       ((1 − prob p WT_B4 t)) * (1 − prob p WT_B5 t)))))) *
    ((1 −
      (1 − prob p WT_C1 t)) *
      ((1 − prob p WT_C2 t)) *
       ((1 − prob p WT_C3 t)) *
        ((1 − prob p  WT_C4 t)) * (1 − prob p  WT_C5 t)))))) *
     (1 −
      (1 − prob p  WT_D1 t)) *
      ((1 − prob p  WT_D2 t)) *
       ((1 − prob p  WT_D3 t)) *
        ((1 − prob p  WT_D4 t)) * (1 − prob p  WT_D5 t)))))))) *
   (prob p  PV_E1 t) *
    (prob p  PV_E2 t) *
     (prob p  PV_E3 t) * (prob p  PV_E4 t) * prob p  PV_E5 t)))) *
    (prob p  PV_F1 t) *
     (prob p  PV_F2 t) *
      (prob p  PV_F3 t) * (prob p  PV_F4 t) * prob p  PV_F5 t)))) *
     (prob p  PV_G1 t) *
      (prob p  PV_G2 t) *
       (prob p  PV_G3 t) * (prob p  PV_G4 t) * prob p  PV_G5 t)))) *
      (prob p  PV_H1 t) *
       (prob p  PV_H2 t) *
        (prob p  PV_H3 t) *
         (prob p  PV_H4 t) * prob p PV_H5 t)))))))))``
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_70_MW_SMART_GRID`` 
``(1 − prob p WT_A1) *
   ((1 − prob p WT_A2) *
    ((1 − prob p WT_A3) * ((1 − prob p WT_A4) * (1 − prob p WT_A5)))) *
   ((1 − prob p WT_B1) *
    ((1 − prob p WT_B2) *
     ((1 − prob p WT_B3) * ((1 − prob p WT_B4) * (1 − prob p WT_B5)))) *
    ((1 − prob p WT_C1) *
     ((1 − prob p WT_C2) *
      ((1 − prob p WT_C3) * ((1 − prob p WT_C4) * (1 − prob p WT_C5)))) *
     ((1 − prob p WT_D1) *
      ((1 − prob p WT_D2) *
       ((1 − prob p WT_D3) * ((1 − prob p WT_D4) * (1 − prob p WT_D5))))))) *
   ((1 −
     prob p PV_E1 *
     (prob p PV_E2 * (prob p PV_E3 * (prob p PV_E4 * prob p PV_E5)))) *
    ((1 −
      prob p PV_F1 *
      (prob p PV_F2 * (prob p PV_F3 * (prob p PV_F4 * prob p PV_F5)))) *
     ((1 −
       prob p PV_G1 *
       (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5)))) *
      (1 −
       prob p PV_H1 *
       (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))))``
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_0_MW_SMART_GRID`` 
``  (1 −
         (1 − exp (-FR_WT_A1 * t)) *
         ((1 − exp (-FR_WT_A2 * t)) *
          ((1 − exp (-FR_WT_A3 * t)) *
           ((1 − exp (-FR_WT_A4 * t)) * (1 − exp (-FR_WT_A5 * t)))))) *
        ((1 −
          (1 − exp (-FR_WT_B1 * t)) *
          ((1 − exp (-FR_WT_B2 * t)) *
           ((1 − exp (-FR_WT_B3 * t)) *
            ((1 − exp (-FR_WT_B4 * t)) * (1 − exp (-FR_WT_B5 * t)))))) *
         ((1 −
           (1 − exp (-FR_WT_C1 * t)) *
           ((1 − exp (-FR_WT_C2 * t)) *
            ((1 − exp (-FR_WT_C3 * t)) *
             ((1 − exp (-FR_WT_C4 * t)) * (1 − exp (-FR_WT_C5 * t)))))) *
          (1 −
           (1 − exp (-FR_WT_D1 * t)) *
           ((1 − exp (-FR_WT_D2 * t)) *
            ((1 − exp (-FR_WT_D3 * t)) *
             ((1 − exp (-FR_WT_D4 * t)) * (1 − exp (-FR_WT_D5 * t)))))))) *
        (exp (-FR_PV_E1 * t) *
         (exp (-FR_PV_E2 * t) *
          (exp (-FR_PV_E3 * t) * (exp (-FR_PV_E4 * t) * exp (-FR_PV_E5 * t)))) *
         (exp (-FR_PV_F1 * t) *
          (exp (-FR_PV_F2 * t) *
           (exp (-FR_PV_F3 * t) *
            (exp (-FR_PV_F4 * t) * exp (-FR_PV_F5 * t)))) *
          (exp (-FR_PV_G1 * t) *
           (exp (-FR_PV_G2 * t) *
            (exp (-FR_PV_G3 * t) *
             (exp (-FR_PV_G4 * t) * exp (-FR_PV_G5 * t)))) *
           (exp (-FR_PV_H1 * t) *
            (exp (-FR_PV_H2 * t) *
             (exp (-FR_PV_H3 * t) *
              (exp (-FR_PV_H4 * t) * exp (-FR_PV_H5 * t)))))))))``
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_70_MW_SMART_GRID``
``(1 − exp (-FR_WT_A1 * t)) *
        ((1 − exp (-FR_WT_A2 * t)) *
         ((1 − exp (-FR_WT_A3 * t)) *
          ((1 − exp (-FR_WT_A4 * t)) * (1 − exp (-FR_WT_A5 * t))))) *
        ((1 − exp (-FR_WT_B1 * t)) *
         ((1 − exp (-FR_WT_B2 * t)) *
          ((1 − exp (-FR_WT_B3 * t)) *
           ((1 − exp (-FR_WT_B4 * t)) * (1 − exp (-FR_WT_B5 * t))))) *
         ((1 − exp (-FR_WT_C1 * t)) *
          ((1 − exp (-FR_WT_C2 * t)) *
           ((1 − exp (-FR_WT_C3 * t)) *
            ((1 − exp (-FR_WT_C4 * t)) * (1 − exp (-FR_WT_C5 * t))))) *
          ((1 − exp (-FR_WT_D1 * t)) *
           ((1 − exp (-FR_WT_D2 * t)) *
            ((1 − exp (-FR_WT_D3 * t)) *
             ((1 − exp (-FR_WT_D4 * t)) * (1 − exp (-FR_WT_D5 * t)))))))) *
        ((1 −
          exp (-FR_PV_E1 * t) *
          (exp (-FR_PV_E2 * t) *
           (exp (-FR_PV_E3 * t) *
            (exp (-FR_PV_E4 * t) * exp (-FR_PV_E5 * t))))) *
         ((1 −
           exp (-FR_PV_F1 * t) *
           (exp (-FR_PV_F2 * t) *
            (exp (-FR_PV_F3 * t) *
             (exp (-FR_PV_F4 * t) * exp (-FR_PV_F5 * t))))) *
          ((1 −
            exp (-FR_PV_G1 * t) *
            (exp (-FR_PV_G2 * t) *
             (exp (-FR_PV_G3 * t) *
              (exp (-FR_PV_G4 * t) * exp (-FR_PV_G5 * t))))) *
           (1 −
            exp (-FR_PV_H1 * t) *
            (exp (-FR_PV_H2 * t) *
             (exp (-FR_PV_H3 * t) *
              (exp (-FR_PV_H4 * t) * exp (-FR_PV_H5 * t)))))))))``
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_0_MW``
    ``(1 −
         (1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
        ((1 −
          (1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
         ((1 −
           (1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) *
             ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
          (1 −
           (1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) *
             ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) *
        (exp (-(11:real)/(100:real)) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) *
	    exp (-(11:real)/(100:real))))) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) *
           (exp (-(11:real)/(100:real)) *
            (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
          (exp (-(11:real)/(100:real)) *
           (exp (-(11:real)/(100:real)) *
            (exp (-(11:real)/(100:real)) *
             (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
           (exp (-(11:real)/(100:real) ) *
            (exp (-(11:real)/(100:real)) *
             (exp (-(11:real)/(100:real)) *
              (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))))))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_70_MW``
``(1 − exp (-(13:real)/(100:real) )) *
        ((1 − exp (-(13:real)/(100:real)  )) *
         ((1 − exp (-(13:real)/(100:real)  )) *
          ((1 − exp (-(13:real)/(100:real)  )) * (1 − exp (-(13:real)/(100:real) ))))) *
        ((1 − exp (-(13:real)/(100:real)  )) *
         ((1 − exp (-(13:real)/(100:real) )) *
          ((1 − exp (-(13:real)/(100:real)  )) *
           ((1 − exp (-(13:real)/(100:real) )) * (1 − exp (-(13:real)/(100:real) ))))) *
         ((1 − exp (-(13:real)/(100:real) )) *
          ((1 − exp (-(13:real)/(100:real)  )) *
           ((1 − exp (-(13:real)/(100:real)  )) *
            ((1 − exp (-(13:real)/(100:real) )) * (1 − exp (-(13:real)/(100:real) ))))) *
          ((1 − exp (-(13:real)/(100:real) )) *
           ((1 − exp (-(13:real)/(100:real) )) *
            ((1 − exp (-(13:real)/(100:real) )) *
             ((1 − exp (-(13:real)/(100:real) )) * (1 − exp (-(13:real)/(100:real) )))))))) *
        ((1 −
          exp (-(11:real)/(100:real)  ) *
          (exp (-(11:real)/(100:real)) *
           (exp (-(11:real)/(100:real)  ) *
            (exp (-(11:real)/(100:real)  ) * exp (-(11:real)/(100:real) ))))) *
         ((1 −
           exp (-(11:real)/(100:real)  ) *
           (exp (-(11:real)/(100:real) ) *
            (exp (-(11:real)/(100:real)) *
             (exp (-(11:real)/(100:real) ) * exp (-(11:real)/(100:real) ))))) *
          ((1 −
            exp (-(11:real)/(100:real) ) *
            (exp (-(11:real)/(100:real)  ) *
             (exp (-(11:real)/(100:real)  ) *
              (exp (-(11:real)/(100:real) ) * exp (-(11:real)/(100:real)  ))))) *
           (1 −
            exp (-(11:real)/(100:real)  ) *
            (exp (-(11:real)/(100:real)  ) *
             (exp (-(11:real)/(100:real) ) *
              (exp (-(11:real)/(100:real) ) * exp (-(11:real)/(100:real)  ))))))))``;
(*---------------------------------------------------------------------------------------------------*)

PROBABILITY ``COPT_17_5_MW``
   ``(1 − exp (-(13:real)/(100:real))) *
   ((1 − exp (-(13:real)/(100:real))) *
    ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real)))))) *
   (exp (-(11:real)/(100:real)) *
    (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
    (exp (-(11:real)/(100:real)) *
     (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
     (exp (-(11:real)/(100:real)) *
      (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
      (exp (-(11:real)/(100:real)) *
       (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))))))) *
   ((1 −
     (1 − exp (-(13:real)/(100:real))) *
     ((1 − exp (-(13:real)/(100:real))) *
      ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
    ((1 −
      (1 − exp (-(13:real)/(100:real))) *
      ((1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
     (1 −
      (1 − exp (-(13:real)/(100:real))) *
      ((1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) +
   ((1 − exp (-(13:real)/(100:real))) *
    ((1 − exp (-(13:real)/(100:real))) *
     ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real)))))) *
    (exp (-(11:real)/(100:real)) *
     (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
     (exp (-(11:real)/(100:real)) *
      (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
      (exp (-(11:real)/(100:real)) *
       (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
       (exp (-(11:real)/(100:real)) *
        (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))))))) *
    ((1 −
      (1 − exp (-(13:real)/(100:real))) *
      ((1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
     ((1 −
       (1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
      (1 −
       (1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) +
    ((1 − exp (-(13:real)/(100:real))) *
     ((1 − exp (-(13:real)/(100:real))) *
      ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real)))))) *
     (exp (-(11:real)/(100:real)) *
      (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
      (exp (-(11:real)/(100:real)) *
       (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
       (exp (-(11:real)/(100:real)) *
        (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
        (exp (-(11:real)/(100:real)) *
         (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))))))) *
     ((1 −
       (1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
      ((1 −
        (1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
       (1 −
        (1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) +
     ((1 − exp (-(13:real)/(100:real))) *
      ((1 − exp (-(13:real)/(100:real))) *
       ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real)))))) *
      (exp (-(11:real)/(100:real)) *
       (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
       (exp (-(11:real)/(100:real)) *
        (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
        (exp (-(11:real)/(100:real)) *
         (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))))))) *
      ((1 −
        (1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
       ((1 −
         (1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
        (1 −
         (1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) +
      ((1 −
        (1 − exp (-(13:real)/(100:real))) *
        ((1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
       ((1 −
         (1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
        ((1 −
          (1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
         (1 −
          (1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) *
       (exp (-(11:real)/(100:real)) *
        (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
        (exp (-(11:real)/(100:real)) *
         (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))))) *
       (1 −
        exp (-(11:real)/(100:real)) *
        (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))) +
       ((1 −
         (1 − exp (-(13:real)/(100:real))) *
         ((1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
        ((1 −
          (1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
         ((1 −
           (1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
          (1 −
           (1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) *
        (exp (-(11:real)/(100:real)) *
         (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
          (exp (-(11:real)/(100:real)) *
           (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))))) *
        (1 −
         exp (-(11:real)/(100:real)) *
         (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))) +
        ((1 −
          (1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
         ((1 −
           (1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
          ((1 −
            (1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) *
             ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
           (1 −
            (1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) *
             ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
          (exp (-(11:real)/(100:real)) *
           (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
           (exp (-(11:real)/(100:real)) *
            (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))))) *
         (1 −
          exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))) +
         (1 −
          (1 − exp (-(13:real)/(100:real))) *
          ((1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
         ((1 −
           (1 − exp (-(13:real)/(100:real))) *
           ((1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
          ((1 −
            (1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) *
             ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))) *
           (1 −
            (1 − exp (-(13:real)/(100:real))) *
            ((1 − exp (-(13:real)/(100:real))) *
             ((1 − exp (-(13:real)/(100:real))) * ((1 − exp (-(13:real)/(100:real))) * (1 − exp (-(13:real)/(100:real))))))))) *
         (exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
          (exp (-(11:real)/(100:real)) *
           (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))) *
           (exp (-(11:real)/(100:real)) *
            (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real)))))))) *
         (1 −
          exp (-(11:real)/(100:real)) *
          (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * (exp (-(11:real)/(100:real)) * exp (-(11:real)/(100:real))))))))))))``
(*---------------------------------------------------------------------------------------------------*)


val _ = export_theory();

(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)
		(*-----------------------------------------------------------------*)
			    (*-----------------------------------------*)
			               (*-------------------*)
					    (*--------*)