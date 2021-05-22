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

val LOAD_SHEDDING_12_5_SMART_GRID_DEF = Define
`LOAD_SHEDDING_12_5_SMART_GRID p
 [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]
 [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]
 [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]
 [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] =
 CONSEQ_BOX p [[DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))]]`;
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val LOAD_SHEDDING_87_5_SMART_GRID_DEF = Define
`LOAD_SHEDDING_87_5_SMART_GRID p
 [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]
 [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]
 [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]
 [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] =
 CONSEQ_BOX p [[DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
               [DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))]]`;
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_0_SMART_GRID = store_thm("PROB_LOAD_SHEDDING_0_SMART_GRID",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5.
         prob_space p ∧
         (∀y.
              MEM y
                [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5; WT_B1; WT_B2; WT_B3; WT_B4; WT_B5;
                 WT_C1; WT_C2; WT_C3; WT_C4; WT_C5; WT_D1; WT_D2; WT_D3; WT_D4; WT_D5;
                 PV_E1; PV_E2; PV_E3; PV_E4; PV_E5; PV_F1; PV_F2; PV_F3; PV_F4; PV_F5;
                 PV_G1; PV_G2; PV_G3; PV_G4; PV_G5; PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]⇒ y ∈ events p) /\
       disjoint
       {CONSEQ_PATH p
        [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
         R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
         R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
         R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
         R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
         R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
         R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
         R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]} /\

        MUTUAL_INDEP p
           (WT_A1::WT_A2::WT_A3::WT_A4::WT_A5::WT_B1::WT_B2::WT_B3::WT_B4::
                WT_B5::WT_C1::WT_C2::WT_C3::WT_C4::WT_C5::WT_D1::WT_D2::
                WT_D3::WT_D4::WT_D5::PV_E1::PV_E2::PV_E3::PV_E4::PV_E5::
                PV_F1::PV_F2::PV_F3::PV_F4::PV_F5::PV_G1::PV_G2::PV_G3::
                PV_G4::PV_G5::PV_H1::PV_H2::PV_H3::PV_H4::PV_H5::
                compl_list p
                  [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5; WT_B1; WT_B2; WT_B3;
                   WT_B4; WT_B5; WT_C1; WT_C2; WT_C3; WT_C4; WT_C5; WT_D1;
                   WT_D2; WT_D3; WT_D4; WT_D5; PV_E1; PV_E2; PV_E3; PV_E4;
                   PV_E5; PV_F1; PV_F2; PV_F3; PV_F4; PV_F5; PV_G1; PV_G2;
                   PV_G3; PV_G4; PV_G5; PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]) ==>
(prob p
    (CONSEQ_BOX p
           [[DECISION_BOX p 1
               (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
                COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
             DECISION_BOX p 1
               (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
                COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
             DECISION_BOX p 1
               (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
                COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
             DECISION_BOX p 1
               (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
                COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
             DECISION_BOX p 1
               (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
                COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
             DECISION_BOX p 1
               (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
                COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
             DECISION_BOX p 1
               (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
                COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
             DECISION_BOX p 1
               (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
                COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))]]) =
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
           (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
           (prob p PV_H1 *
            (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))))``, 

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw [PROB_SUM_DEF]
   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       \\ CONJ_TAC
          >-( rw []
       	      \\ metis_tac [])
       \\ CONJ_TAC
          >-( rw []
       	      \\ metis_tac [])
       \\ CONJ_TAC
          >-( rw []
              >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	          \\ rw []
	          \\ metis_tac [])
              >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	          \\ rw []
	          \\ metis_tac [])
              >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	          \\ rw []
	          \\ metis_tac [])
              >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	          \\ rw []
	          \\ metis_tac [])
              >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	  \\ rw []
	       	  \\ metis_tac [])
              >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	  \\ rw []
	       	  \\ metis_tac [])
              >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	  \\ rw []
	       	  \\ metis_tac [])
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	     \\ rw []
	     \\ metis_tac [])		  
      \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      \\ rw []
          >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
     \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     \\ rw []
     \\ metis_tac [])
\\ sg `CONSEQ_PATH p
        [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
         R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
         R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
         R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
         R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
         R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
         R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
         R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                                              [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
				 	      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
				 	      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]); 
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]])]` 

   >-( rw [SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_ALL_SUBSYSTEMS_SERIES_YES]
\\ sg `(∀x.
              MEM x
                (FLAT
                   ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                     [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                     [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                     [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                    [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                     [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                     [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                     [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]])) ⇒
              x ∈ events p) `
    >-( rw []
    	\\ metis_tac [])
\\ sg `(∀x.
              MEM x
                [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                 [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                 [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                 [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⇒
              ~NULL x) `
    >-( rw []
    	\\ metis_tac [NULL])
\\ fs []
\\ sg `∏
          [1 −
           ∏ (PROB_LIST p (compl_list p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
           1 −
           ∏ (PROB_LIST p (compl_list p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
           1 −
           ∏ (PROB_LIST p (compl_list p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
           1 −
           ∏ (PROB_LIST p (compl_list p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]))] *
        ∏
          [∏ (PROB_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
           ∏ (PROB_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
           ∏ (PROB_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
           ∏ (PROB_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])]  =
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
      (prob p PV_G2 * (prob p PV_G3 * (prob p PV_G4 * prob p PV_G5))) *
      (prob p PV_H1 *
       (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5)))))))`
       
  >-( rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def, PROB_COMPL]
      \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ CONJ_TAC
   >-( CONJ_TAC
       >-(  rw []
            \\ metis_tac [])
       \\ rw []  
       \\ metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_100_SMART_GRID = store_thm("PROB_LOAD_SHEDDING_100_SMART_GRID",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5.
         prob_space p ∧
         (∀y.
              MEM y
                [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5; WT_B1; WT_B2; WT_B3; WT_B4; WT_B5;
                 WT_C1; WT_C2; WT_C3; WT_C4; WT_C5; WT_D1; WT_D2; WT_D3; WT_D4; WT_D5;
                 PV_E1; PV_E2; PV_E3; PV_E4; PV_E5; PV_F1; PV_F2; PV_F3; PV_F4; PV_F5;
                 PV_G1; PV_G2; PV_G3; PV_G4; PV_G5; PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]⇒ y ∈ events p) /\
       disjoint
       {CONSEQ_PATH p
        [COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]);
         COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]);
         COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]);
         COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]);
         COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
         COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
         COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
         COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])]} /\

        MUTUAL_INDEP p
           (WT_A1::WT_A2::WT_A3::WT_A4::WT_A5::WT_B1::WT_B2::WT_B3::WT_B4::
                WT_B5::WT_C1::WT_C2::WT_C3::WT_C4::WT_C5::WT_D1::WT_D2::
                WT_D3::WT_D4::WT_D5::PV_E1::PV_E2::PV_E3::PV_E4::PV_E5::
                PV_F1::PV_F2::PV_F3::PV_F4::PV_F5::PV_G1::PV_G2::PV_G3::
                PV_G4::PV_G5::PV_H1::PV_H2::PV_H3::PV_H4::PV_H5::
                compl_list p
                  [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5; WT_B1; WT_B2; WT_B3;
                   WT_B4; WT_B5; WT_C1; WT_C2; WT_C3; WT_C4; WT_C5; WT_D1;
                   WT_D2; WT_D3; WT_D4; WT_D5; PV_E1; PV_E2; PV_E3; PV_E4;
                   PV_E5; PV_F1; PV_F2; PV_F3; PV_F4; PV_F5; PV_G1; PV_G2;
                   PV_G3; PV_G4; PV_G5; PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]) ==>
(prob p
    (CONSEQ_BOX p
           [[DECISION_BOX p 0
               (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
                COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
             DECISION_BOX p 0
               (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
                COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
             DECISION_BOX p 0
               (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
                COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
             DECISION_BOX p 0
               (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
                COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
             DECISION_BOX p 0
               (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
                COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
             DECISION_BOX p 0
               (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
                COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
             DECISION_BOX p 0
               (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
                COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
             DECISION_BOX p 0
               (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
                COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))]]) =
   (1 − prob p WT_A1) *
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
       (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))))``, 

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw [PROB_SUM_DEF]
   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       \\ CONJ_TAC
          >-( rw []
       	      \\ metis_tac [])
       \\ CONJ_TAC
          >-( rw []
       	      \\ metis_tac [])
       \\ CONJ_TAC
          >-( rw []   
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])		        
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	   \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   \\ rw []
	       	   \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])

               \\ rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])	       
      \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      \\ rw []
          >-(  rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-(  rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-(  rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-(  rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-( rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-( rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
          >-( rw [COMPL_PSPACE_DEF]
	       \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       \\ rw []
	       \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       \\ rw []
	       \\ metis_tac [])
     \\ rw [COMPL_PSPACE_DEF]
     \\ DEP_REWRITE_TAC [EVENTS_COMPL]
     \\ rw []
     \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     \\ rw []
     \\ metis_tac [])
\\ sg `CONSEQ_PATH p
        [COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]);
         COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]);
         COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]);
         COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]);
         COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
         COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
         COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
         COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝙽𝙾 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                                              [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
				 	      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
				 	      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]); 
		   CONSEQ_PATH p (𝑺𝑺sr𝙽𝙾 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]])]` 

   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, COMPL_SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_NO_AND_ALL_SUBSYSTEMS_SERIES_NO]
\\ sg `(∀x.
              MEM x
                (FLAT
                   ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                     [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                     [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                     [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                    [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                     [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                     [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                     [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]])) ⇒
              x ∈ events p) `
    >-( rw []
    	\\ metis_tac [])
\\ sg `(∀x.
              MEM x
                [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                 [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                 [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                 [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⇒
              ~NULL x) `
    >-( rw []
    	\\ metis_tac [NULL])
\\ fs []
\\ sg ` ∏
            [∏
                  (PROB_LIST p
                     (compl_list p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
                ∏
                  (PROB_LIST p
                     (compl_list p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
                ∏
                  (PROB_LIST p
                     (compl_list p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
                ∏
                  (PROB_LIST p
                     (compl_list p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]))] *
             ∏
               [1 − ∏ (PROB_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
                1 − ∏ (PROB_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
                1 − ∏ (PROB_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
                1 − ∏ (PROB_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])] =
   (1 − prob p WT_A1) *
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
       (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5)))))))`
       
  >-( rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def, PROB_COMPL]
      \\ DEP_REWRITE_TAC [PROB_COMPL]
      \\ rw []
      \\ REAL_ARITH_TAC)
\\ POP_ORW
\\ CONJ_TAC
   >-( CONJ_TAC
       >-(  rw []
            \\ metis_tac [])
       \\ rw []  
       \\ metis_tac [])
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_12_5_SMART_GRID = store_thm("PROB_LOAD_SHEDDING_12_5_SMART_GRID",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5.
    prob_space p /\
           (∀y.
              MEM y
                [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5; WT_B1; WT_B2; WT_B3; WT_B4; WT_B5;
                 WT_C1; WT_C2; WT_C3; WT_C4; WT_C5; WT_D1; WT_D2; WT_D3; WT_D4; WT_D5;
                 PV_E1; PV_E2; PV_E3; PV_E4; PV_E5; PV_F1; PV_F2; PV_F3; PV_F4; PV_F5;
                 PV_G1; PV_G2; PV_G3; PV_G4; PV_G5; PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]⇒ y ∈ events p) /\
    ALL_DISTINCT
      [CONSEQ_PATH p
         [COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]);
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]);
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]);
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]);
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
          R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
       CONSEQ_PATH p
         [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
          R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
          R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
          R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
          R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
          R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
          R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
          COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])]] ∧
    disjoint
      (set
         [CONSEQ_PATH p
            [COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]);
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]);
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]);
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]);
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
             R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]];
          CONSEQ_PATH p
            [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
             R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
             R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
             R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
             R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
             R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
             R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
             COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])]]) /\
    MUTUAL_INDEP p
          (FLAT
             ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]))) /\
MUTUAL_INDEP p
          (FLAT
             ([[WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]))) /\
MUTUAL_INDEP p
          (FLAT
             ([[WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]))) /\
MUTUAL_INDEP p
          (FLAT
             ([[WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]])))  /\
 MUTUAL_INDEP p
          (FLAT
             ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]] ⧺
              [[PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]] ⧺
                 [[PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]))) /\
        MUTUAL_INDEP p
          (FLAT
             ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]]))) /\
MUTUAL_INDEP p
          (FLAT
             ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]]))) /\
MUTUAL_INDEP p
          (FLAT
             ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
               [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
              [[PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
              [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]]) ⧺
           compl_list p
             (FLAT
                ([[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]] ⧺
                 [[PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] ⧺
                 [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]]))) ==>
   prob p (CONSEQ_BOX p [[DECISION_BOX p 0
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 0
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] ,
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 0
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 0
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 0
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 0
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 0
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 1
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))];
	       [DECISION_BOX p 1
                (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5],
	        COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]));
		DECISION_BOX p 1
                (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5],
	        COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]));
		DECISION_BOX p 1
                (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5],
	        COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]));
		DECISION_BOX p 1
                (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5],
	        COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]));
		DECISION_BOX p 1
                (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5],
	        COMPL_PSPACE p (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]));
		DECISION_BOX p 1
                (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5],
	        COMPL_PSPACE p (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]));
		DECISION_BOX p 1
                (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5],
	        COMPL_PSPACE p (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]));
		DECISION_BOX p 0
                (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5],
	        COMPL_PSPACE p (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]))]]) =
   (1 − prob p WT_A1) *
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
          (prob p PV_H2 * (prob p PV_H3 * (prob p PV_H4 * prob p PV_H5))))))))))``,

rw [DECISION_BOX_DEF]
\\ rw [CONSEQ_BOX_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ CONJ_TAC
   >-(CONJ_TAC
      >-(metis_tac [])
      \\ CONJ_TAC
	 >-(rw []
	    >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       		  \\ rw []
	       		  \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       		  \\ rw []
	       		  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])               
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                     \\DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
               \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	       \\ rw []
             	  >-(rw [COMPL_PSPACE_DEF]
	       	     \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	     \\ rw []
	       	     \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                  >-(DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                  >-(DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                 >-(DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
                 >-(DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
                 >-(DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
                 >-(DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
              \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	      \\ rw []
     	      \\ metis_tac [])
	   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       		  \\ rw []
	       		  \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       		  \\ rw []
	       		  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])               
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                     \\DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	     \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
             	>-(  rw [COMPL_PSPACE_DEF]
	       	     \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	     \\ rw []
	       	     \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])		     
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
           \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	   \\ rw []
     	   \\ metis_tac [])
	   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])  			  
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       		  \\ rw []
	       		  \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       		  \\ rw []
	       		  \\ metis_tac [])             
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                     \\DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	     \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])		     
             	>-(  rw [COMPL_PSPACE_DEF]
	       	     \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	     \\ rw []
	       	     \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])		     
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
           \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	   \\ rw []
     	   \\ metis_tac [])
	   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])			  
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       		  \\ rw []
	       		  \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       		  \\ rw []
	       		  \\ metis_tac [])             
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                     \\DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	     \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
             	>-(  rw [COMPL_PSPACE_DEF]
	       	     \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	     \\ rw []
	       	     \\ DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])		     
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
           \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	   \\ rw []
     	   \\ metis_tac [])
	   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   	  \\ rw []
	       	   	  \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	          \\ rw []
	       	   	  \\ metis_tac [])             
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                     \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	     \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	    \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	    \\ rw []
	       	    \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
           \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	   \\ rw []
     	   \\ metis_tac [])
	   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])			  
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   	  \\ rw []
	       	   	  \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	          \\ rw []
	       	   	  \\ metis_tac [])             
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                     \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	     \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])		    
               >-( rw [COMPL_PSPACE_DEF]
	       	    \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	    \\ rw []
	       	    \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
           \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	   \\ rw []
     	   \\ metis_tac [])
	   >-( rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	       \\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	       \\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	       \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
               \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])			  
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                      >-( rw [COMPL_PSPACE_DEF]
	       	      	  \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	   	  \\ rw []
	       	   	  \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	          \\ rw []
	       	   	  \\ metis_tac [])             
                     \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	             \\ rw []
	             \\ metis_tac [])		  
             \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	     \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])		    
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( rw [COMPL_PSPACE_DEF]
	       	    \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	    \\ rw []
	       	    \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
           \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
     	   \\ rw []
     	   \\ metis_tac [])
        \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       	\\ DEP_REWRITE_TAC[CONSEQ_PATH_EQ_ET_PATH]
       	\\ DEP_REWRITE_TAC [RBD_STRUCT_PARALLEL_EQ_BIG_UNION]
       	\\ DEP_REWRITE_TAC [RBD_STRUCT_SERIES_EQ_PATH]
       	\\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
        \\ CONJ_TAC
               	  >-( rw []
       	      	      \\ metis_tac [])
        \\ CONJ_TAC
               	  >-( rw []
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	              	  \\ rw []
	              	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	      	  \\ metis_tac [])			  
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])
                      >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	      	  \\ rw []
	       	     	  \\ metis_tac [])			  
                    \\ rw [COMPL_PSPACE_DEF]
	       	    \\ DEP_REWRITE_TAC [EVENTS_COMPL]
	       	    \\ rw []
	       	    \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		  
         \\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
      	 \\ rw []
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
                >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	     \\ rw []
	       	     \\ metis_tac [])
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])		     
               >-(  DEP_REWRITE_TAC [BIG_UNION_IN_EVENTS]
	       	    \\ rw []
	       	    \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])		    
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
               >-( DEP_REWRITE_TAC [PATH_IN_EVENTS]
	       	   \\ rw []
	       	   \\ metis_tac [])
        \\ rw [COMPL_PSPACE_DEF]
	\\ DEP_REWRITE_TAC [EVENTS_COMPL]
	\\ rw []
	\\ DEP_REWRITE_TAC [PATH_IN_EVENTS]
	\\ rw []
	\\ metis_tac [])
    \\ CONJ_TAC
       >-( rw []
       	   \\ metis_tac [])
    \\ rw []
    \\ metis_tac [])
\\ rw [PROB_SUM_DEF]
\\ sg `CONSEQ_PATH p
            [COMPL_PSPACE p (R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]);
              R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
              R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
              R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
              R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
              R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
              R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
              R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝙽𝙾  p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5]]); 
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
                   CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
				 	      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
				 	      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]])]` 

   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
              [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
               COMPL_PSPACE p (R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]);
               R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
               R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
               R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
               R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
               R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
               R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝙽𝙾  p [[WT_B1; WT_B2; WT_B3; WT_B4; WT_B5]]); 
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
                   CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
				 	      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
				 	      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]])]` 

   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
              [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                COMPL_PSPACE p (R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]);
                R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
                R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝙽𝙾  p [[WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]]); 
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
                   CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
		   	                      [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
				 	      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]])]` 

   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
                [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                 R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                 R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                 COMPL_PSPACE p (R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]);
                 R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                 R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                 R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                 R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝙽𝙾  p [[WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]); 
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
                   CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
		   	                      [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
					      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]])]` 

   >-( rw [COMPL_SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
                 [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                  R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                  R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                  R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
                  COMPL_PSPACE p
                    (R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]);
                  R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                  R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                  R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
		   	                      [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
					      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
					      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝙽𝙾  p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5]])]`

   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
                  [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                   R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                   R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                   R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
                   R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                   COMPL_PSPACE p
                     (R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]);
                   R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                   R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
		   	                      [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
					      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
					      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝙽𝙾  p [[PV_F1; PV_F2; PV_F3; PV_F4; PV_F5]])]`

   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
                   [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                    R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                    R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                    R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
                    R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                    R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                    COMPL_PSPACE p
                      (R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]);
                    R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
		   	                      [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
					      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
					      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
		                              [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];			
				 	      [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝙽𝙾  p [[PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]])]`

   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `CONSEQ_PATH p
                   [R_WTA p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
                    R_WTB p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
                    R_WTC p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
                    R_WTD p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5];
                    R_PVE p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
                    R_PVF p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];
                    R_PVG p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5];
                    COMPL_PSPACE p
                      (R_PVH p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5])] =
    CONSEQ_PATH p [CONSEQ_PATH p (𝑺𝑺pa𝚈𝙴𝚂 p [[WT_A1; WT_A2; WT_A3; WT_A4; WT_A5];
		   	                      [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5];
					      [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5];
					      [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝚈𝙴𝚂 p [[PV_E1; PV_E2; PV_E3; PV_E4; PV_E5];
		                              [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5];			
				 	      [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5]]);
		   CONSEQ_PATH p (𝑺𝑺sr𝙽𝙾  p [[PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]])]`

   >-( rw [COMPL_SUBSYSTEMS_SERIES_DEF, SUBSYSTEMS_PARALLEL_DEF, SUBSYSTEMS_SERIES_DEF]
       \\ rw [R_WTA_DEF, R_WTB_DEF, R_WTC_DEF, R_WTD_DEF, R_PVE_DEF, R_PVF_DEF, R_PVG_DEF, R_PVH_DEF]
       \\ rw [rbd_struct_def, rbd_list_def]
       \\ rw [COMPL_PSPACE_DEF, CONSEQ_PATH_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_PARALLEL_YES_AND_SOME_SUBSYSTEMS_SERIES_NO_AND_SUBSYSTEMS_SERIES_YES]
\\ DEP_REWRITE_TAC [PROB_CONSEQ_PATH_OF_ALL_SUBSYSTEMS_SERIES_YES_AND_SOME_SUBSYSTEMS_PARALLEL_NO_AND_SUBSYSTEMS_PARALLEL_YES]
\\ CONJ_TAC
    >-(  rw []
	 \\ metis_tac [NULL, EVENTS_COMPL])
\\ CONJ_TAC
    >-(  rw []
	 \\ metis_tac [NULL, EVENTS_COMPL])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF, compl_list_def, PROB_COMPL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw []
\\ REAL_ARITH_TAC);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_0_SMART_GRID_DISTRIBUTION =
store_thm("PROB_LOAD_SHEDDING_0_SMART_GRID_DISTRIBUTION",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5 t.
(prob_space p ∧
    (∀y.
         MEM y
           [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t; ↑ p WT_A5 t;
            ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t; ↑ p WT_B5 t;
            ↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t;
            ↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
            ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t; ↑ p PV_E5 t;
            ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t; ↑ p PV_F5 t;
            ↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t;
            ↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t] ⇒
         y ∈ events p) ∧
    disjoint
      {CONSEQ_PATH p
         [R_WTA p
            [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t; ↑ p WT_A5 t];
          R_WTB p
            [↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t; ↑ p WT_B5 t];
          R_WTC p
            [↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t];
          R_WTD p
            [↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t];
          R_PVE p
            [↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t; ↑ p PV_E5 t];
          R_PVF p
            [↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t; ↑ p PV_F5 t];
          R_PVG p
            [↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t];
          R_PVH p
            [↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t]]} ∧
    MUTUAL_INDEP p
      (↑ p WT_A1 t:: ↑ p WT_A2 t:: ↑ p WT_A3 t:: ↑ p WT_A4 t:: ↑ p WT_A5 t::
            ↑ p WT_B1 t:: ↑ p WT_B2 t:: ↑ p WT_B3 t:: ↑ p WT_B4 t::
            ↑ p WT_B5 t:: ↑ p WT_C1 t:: ↑ p WT_C2 t:: ↑ p WT_C3 t::
            ↑ p WT_C4 t:: ↑ p WT_C5 t:: ↑ p WT_D1 t:: ↑ p WT_D2 t::
            ↑ p WT_D3 t:: ↑ p WT_D4 t:: ↑ p WT_D5 t:: ↑ p PV_E1 t::
            ↑ p PV_E2 t:: ↑ p PV_E3 t:: ↑ p PV_E4 t:: ↑ p PV_E5 t::
            ↑ p PV_F1 t:: ↑ p PV_F2 t:: ↑ p PV_F3 t:: ↑ p PV_F4 t::
            ↑ p PV_F5 t:: ↑ p PV_G1 t:: ↑ p PV_G2 t:: ↑ p PV_G3 t::
            ↑ p PV_G4 t:: ↑ p PV_G5 t:: ↑ p PV_H1 t:: ↑ p PV_H2 t::
            ↑ p PV_H3 t:: ↑ p PV_H4 t:: ↑ p PV_H5 t::
           compl_list p
             [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
              ↑ p WT_A5 t; ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t;
              ↑ p WT_B4 t; ↑ p WT_B5 t; ↑ p WT_C1 t; ↑ p WT_C2 t;
              ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t; ↑ p WT_D1 t;
              ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
              ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
              ↑ p PV_E5 t; ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t;
              ↑ p PV_F4 t; ↑ p PV_F5 t; ↑ p PV_G1 t; ↑ p PV_G2 t;
              ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t; ↑ p PV_H1 t;
              ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t])) ==>
(prob p
    (CONSEQ_BOX p
           [[DECISION_BOX p 1
               (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t),
                COMPL_PSPACE p (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t)));
             DECISION_BOX p 1
               (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t),
                COMPL_PSPACE p (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t)));
             DECISION_BOX p 1
               (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] t),
                COMPL_PSPACE p (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]t)));
             DECISION_BOX p 1
               (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t),
                COMPL_PSPACE p (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t)));
             DECISION_BOX p 1
               (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t),
                COMPL_PSPACE p (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t)));
             DECISION_BOX p 1
               (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t),
                COMPL_PSPACE p (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t)));
             DECISION_BOX p 1
               (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t),
                COMPL_PSPACE p (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t)));
             DECISION_BOX p 1
               (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t),
                COMPL_PSPACE p (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t)))]]) =
    (1 −
    (1 − prob p (↑ p WT_A1 t)) *
    ((1 − prob p (↑ p WT_A2 t)) *
     ((1 − prob p (↑ p WT_A3 t)) *
      ((1 − prob p (↑ p WT_A4 t)) * (1 − prob p (↑ p WT_A5 t)))))) *
   ((1 −
     (1 − prob p (↑ p WT_B1 t)) *
     ((1 − prob p (↑ p WT_B2 t)) *
      ((1 − prob p (↑ p WT_B3 t)) *
       ((1 − prob p (↑ p WT_B4 t)) * (1 − prob p (↑ p WT_B5 t)))))) *
    ((1 −
      (1 − prob p (↑ p WT_C1 t)) *
      ((1 − prob p (↑ p WT_C2 t)) *
       ((1 − prob p (↑ p WT_C3 t)) *
        ((1 − prob p (↑ p WT_C4 t)) * (1 − prob p (↑ p WT_C5 t)))))) *
     (1 −
      (1 − prob p (↑ p WT_D1 t)) *
      ((1 − prob p (↑ p WT_D2 t)) *
       ((1 − prob p (↑ p WT_D3 t)) *
        ((1 − prob p (↑ p WT_D4 t)) * (1 − prob p (↑ p WT_D5 t)))))))) *
   (prob p (↑ p PV_E1 t) *
    (prob p (↑ p PV_E2 t) *
     (prob p (↑ p PV_E3 t) * (prob p (↑ p PV_E4 t) * prob p (↑ p PV_E5 t)))) *
    (prob p (↑ p PV_F1 t) *
     (prob p (↑ p PV_F2 t) *
      (prob p (↑ p PV_F3 t) * (prob p (↑ p PV_F4 t) * prob p (↑ p PV_F5 t)))) *
     (prob p (↑ p PV_G1 t) *
      (prob p (↑ p PV_G2 t) *
       (prob p (↑ p PV_G3 t) * (prob p (↑ p PV_G4 t) * prob p (↑ p PV_G5 t)))) *
      (prob p (↑ p PV_H1 t) *
       (prob p (↑ p PV_H2 t) *
        (prob p (↑ p PV_H3 t) *
         (prob p (↑ p PV_H4 t) * prob p (↑ p PV_H5 t)))))))))``,

rw [SUCCESS_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_LOAD_SHEDDING_0_SMART_GRID]
\\ rw []
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_100_SMART_GRID_DISTRIBUTION =
store_thm("PROB_LOAD_SHEDDING_100_SMART_GRID_DISTRIBUTION",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5 t.
(prob_space p ∧
    (∀y.
         MEM y
           [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t; ↑ p WT_A5 t;
            ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t; ↑ p WT_B5 t;
            ↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t;
            ↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
            ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t; ↑ p PV_E5 t;
            ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t; ↑ p PV_F5 t;
            ↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t;
            ↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t] ⇒
         y ∈ events p) ∧
    disjoint
      {CONSEQ_PATH p
         [COMPL_PSPACE p
            (R_WTA p
               [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
                ↑ p WT_A5 t]);
          COMPL_PSPACE p
            (R_WTB p
               [↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t;
                ↑ p WT_B5 t]);
          COMPL_PSPACE p
            (R_WTC p
               [↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t;
                ↑ p WT_C5 t]);
          COMPL_PSPACE p
            (R_WTD p
               [↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t;
                ↑ p WT_D5 t]);
          COMPL_PSPACE p
            (R_PVE p
               [↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
                ↑ p PV_E5 t]);
          COMPL_PSPACE p
            (R_PVF p
               [↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t;
                ↑ p PV_F5 t]);
          COMPL_PSPACE p
            (R_PVG p
               [↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t;
                ↑ p PV_G5 t]);
          COMPL_PSPACE p
            (R_PVH p
               [↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t;
                ↑ p PV_H5 t])]} ∧
    MUTUAL_INDEP p
      (↑ p WT_A1 t:: ↑ p WT_A2 t:: ↑ p WT_A3 t:: ↑ p WT_A4 t:: ↑ p WT_A5 t::
            ↑ p WT_B1 t:: ↑ p WT_B2 t:: ↑ p WT_B3 t:: ↑ p WT_B4 t::
            ↑ p WT_B5 t:: ↑ p WT_C1 t:: ↑ p WT_C2 t:: ↑ p WT_C3 t::
            ↑ p WT_C4 t:: ↑ p WT_C5 t:: ↑ p WT_D1 t:: ↑ p WT_D2 t::
            ↑ p WT_D3 t:: ↑ p WT_D4 t:: ↑ p WT_D5 t:: ↑ p PV_E1 t::
            ↑ p PV_E2 t:: ↑ p PV_E3 t:: ↑ p PV_E4 t:: ↑ p PV_E5 t::
            ↑ p PV_F1 t:: ↑ p PV_F2 t:: ↑ p PV_F3 t:: ↑ p PV_F4 t::
            ↑ p PV_F5 t:: ↑ p PV_G1 t:: ↑ p PV_G2 t:: ↑ p PV_G3 t::
            ↑ p PV_G4 t:: ↑ p PV_G5 t:: ↑ p PV_H1 t:: ↑ p PV_H2 t::
            ↑ p PV_H3 t:: ↑ p PV_H4 t:: ↑ p PV_H5 t::
           compl_list p
             [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
              ↑ p WT_A5 t; ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t;
              ↑ p WT_B4 t; ↑ p WT_B5 t; ↑ p WT_C1 t; ↑ p WT_C2 t;
              ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t; ↑ p WT_D1 t;
              ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
              ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
              ↑ p PV_E5 t; ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t;
              ↑ p PV_F4 t; ↑ p PV_F5 t; ↑ p PV_G1 t; ↑ p PV_G2 t;
              ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t; ↑ p PV_H1 t;
              ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t])) ==>
(prob p
    (CONSEQ_BOX p
           [[DECISION_BOX p 0
               (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t),
                COMPL_PSPACE p (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t)));
             DECISION_BOX p 0
               (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t),
                COMPL_PSPACE p (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t)));
             DECISION_BOX p 0
               (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] t),
                COMPL_PSPACE p (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]t)));
             DECISION_BOX p 0
               (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t),
                COMPL_PSPACE p (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t)));
             DECISION_BOX p 0
               (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t),
                COMPL_PSPACE p (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t)));
             DECISION_BOX p 0
               (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t),
                COMPL_PSPACE p (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t)));
             DECISION_BOX p 0
               (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t),
                COMPL_PSPACE p (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t)));
             DECISION_BOX p 0
               (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t),
                COMPL_PSPACE p (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t)))]]) =
     (1 − prob p (↑ p WT_A1 t)) *
   ((1 − prob p (↑ p WT_A2 t)) *
    ((1 − prob p (↑ p WT_A3 t)) *
     ((1 − prob p (↑ p WT_A4 t)) * (1 − prob p (↑ p WT_A5 t))))) *
   ((1 − prob p (↑ p WT_B1 t)) *
    ((1 − prob p (↑ p WT_B2 t)) *
     ((1 − prob p (↑ p WT_B3 t)) *
      ((1 − prob p (↑ p WT_B4 t)) * (1 − prob p (↑ p WT_B5 t))))) *
    ((1 − prob p (↑ p WT_C1 t)) *
     ((1 − prob p (↑ p WT_C2 t)) *
      ((1 − prob p (↑ p WT_C3 t)) *
       ((1 − prob p (↑ p WT_C4 t)) * (1 − prob p (↑ p WT_C5 t))))) *
     ((1 − prob p (↑ p WT_D1 t)) *
      ((1 − prob p (↑ p WT_D2 t)) *
       ((1 − prob p (↑ p WT_D3 t)) *
        ((1 − prob p (↑ p WT_D4 t)) * (1 − prob p (↑ p WT_D5 t)))))))) *
   ((1 −
     prob p (↑ p PV_E1 t) *
     (prob p (↑ p PV_E2 t) *
      (prob p (↑ p PV_E3 t) * (prob p (↑ p PV_E4 t) * prob p (↑ p PV_E5 t))))) *
    ((1 −
      prob p (↑ p PV_F1 t) *
      (prob p (↑ p PV_F2 t) *
       (prob p (↑ p PV_F3 t) * (prob p (↑ p PV_F4 t) * prob p (↑ p PV_F5 t))))) *
     ((1 −
       prob p (↑ p PV_G1 t) *
       (prob p (↑ p PV_G2 t) *
        (prob p (↑ p PV_G3 t) *
         (prob p (↑ p PV_G4 t) * prob p (↑ p PV_G5 t))))) *
      (1 −
       prob p (↑ p PV_H1 t) *
       (prob p (↑ p PV_H2 t) *
        (prob p (↑ p PV_H3 t) *
         (prob p (↑ p PV_H4 t) * prob p (↑ p PV_H5 t)))))))))``,

rw [SUCCESS_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_LOAD_SHEDDING_100_SMART_GRID]
\\ rw []
\\ metis_tac []);
(*---------------------------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_0_SMART_GRID_EXPONENTIAL_DISTRIBUTION =
store_thm("PROB_LOAD_SHEDDING_0_SMART_GRID_EXPONENTIAL_DISTRIBUTION",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5 t
     FR_WT_A1 FR_WT_A2 FR_WT_A3 FR_WT_A4 FR_WT_A5
     FR_WT_B1 FR_WT_B2 FR_WT_B3 FR_WT_B4 FR_WT_B5
     FR_WT_C1 FR_WT_C2 FR_WT_C3 FR_WT_C4 FR_WT_C5
     FR_WT_D1 FR_WT_D2 FR_WT_D3 FR_WT_D4 FR_WT_D5
     FR_PV_E1 FR_PV_E2 FR_PV_E3 FR_PV_E4 FR_PV_E5
     FR_PV_F1 FR_PV_F2 FR_PV_F3 FR_PV_F4 FR_PV_F5
     FR_PV_G1 FR_PV_G2 FR_PV_G3 FR_PV_G4 FR_PV_G5
     FR_PV_H1 FR_PV_H2 FR_PV_H3 FR_PV_H4 FR_PV_H5.
(prob_space p ∧
    (∀y.
         MEM y
           [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t; ↑ p WT_A5 t;
            ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t; ↑ p WT_B5 t;
            ↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t;
            ↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
            ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t; ↑ p PV_E5 t;
            ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t; ↑ p PV_F5 t;
            ↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t;
            ↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t] ⇒
         y ∈ events p) ∧
    disjoint
      {CONSEQ_PATH p
         [R_WTA p
            [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t; ↑ p WT_A5 t];
          R_WTB p
            [↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t; ↑ p WT_B5 t];
          R_WTC p
            [↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t];
          R_WTD p
            [↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t];
          R_PVE p
            [↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t; ↑ p PV_E5 t];
          R_PVF p
            [↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t; ↑ p PV_F5 t];
          R_PVG p
            [↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t];
          R_PVH p
            [↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t]]} ∧
    MUTUAL_INDEP p
      (↑ p WT_A1 t:: ↑ p WT_A2 t:: ↑ p WT_A3 t:: ↑ p WT_A4 t:: ↑ p WT_A5 t::
            ↑ p WT_B1 t:: ↑ p WT_B2 t:: ↑ p WT_B3 t:: ↑ p WT_B4 t::
            ↑ p WT_B5 t:: ↑ p WT_C1 t:: ↑ p WT_C2 t:: ↑ p WT_C3 t::
            ↑ p WT_C4 t:: ↑ p WT_C5 t:: ↑ p WT_D1 t:: ↑ p WT_D2 t::
            ↑ p WT_D3 t:: ↑ p WT_D4 t:: ↑ p WT_D5 t:: ↑ p PV_E1 t::
            ↑ p PV_E2 t:: ↑ p PV_E3 t:: ↑ p PV_E4 t:: ↑ p PV_E5 t::
            ↑ p PV_F1 t:: ↑ p PV_F2 t:: ↑ p PV_F3 t:: ↑ p PV_F4 t::
            ↑ p PV_F5 t:: ↑ p PV_G1 t:: ↑ p PV_G2 t:: ↑ p PV_G3 t::
            ↑ p PV_G4 t:: ↑ p PV_G5 t:: ↑ p PV_H1 t:: ↑ p PV_H2 t::
            ↑ p PV_H3 t:: ↑ p PV_H4 t:: ↑ p PV_H5 t::
           compl_list p
             [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
              ↑ p WT_A5 t; ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t;
              ↑ p WT_B4 t; ↑ p WT_B5 t; ↑ p WT_C1 t; ↑ p WT_C2 t;
              ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t; ↑ p WT_D1 t;
              ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
              ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
              ↑ p PV_E5 t; ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t;
              ↑ p PV_F4 t; ↑ p PV_F5 t; ↑ p PV_G1 t; ↑ p PV_G2 t;
              ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t; ↑ p PV_H1 t;
              ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t])) /\ 0 <= t /\
  EXP_ET_SUCCESS_DISTRIB_LIST p
    [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5;
     WT_B1; WT_B2; WT_B3; WT_B4; WT_B5;
     WT_C1; WT_C2; WT_C3; WT_C4; WT_C5;
     WT_D1; WT_D2; WT_D3; WT_D4; WT_D5;
     PV_E1; PV_E2; PV_E3; PV_E4; PV_E5;
     PV_F1; PV_F2; PV_F3; PV_F4; PV_F5;
     PV_G1; PV_G2; PV_G3; PV_G4; PV_G5;
     PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]
    [FR_WT_A1; FR_WT_A2; FR_WT_A3; FR_WT_A4; FR_WT_A5;
     FR_WT_B1; FR_WT_B2; FR_WT_B3; FR_WT_B4; FR_WT_B5;
     FR_WT_C1; FR_WT_C2; FR_WT_C3; FR_WT_C4; FR_WT_C5;
     FR_WT_D1; FR_WT_D2; FR_WT_D3; FR_WT_D4; FR_WT_D5;
     FR_PV_E1; FR_PV_E2; FR_PV_E3; FR_PV_E4; FR_PV_E5;
     FR_PV_F1; FR_PV_F2; FR_PV_F3; FR_PV_F4; FR_PV_F5;
     FR_PV_G1; FR_PV_G2; FR_PV_G3; FR_PV_G4; FR_PV_G5;
     FR_PV_H1; FR_PV_H2; FR_PV_H3; FR_PV_H4; FR_PV_H5] ==> 

(prob p
    (CONSEQ_BOX p
           [[DECISION_BOX p 1
               (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t),
                COMPL_PSPACE p (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t)));
             DECISION_BOX p 1
               (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t),
                COMPL_PSPACE p (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t)));
             DECISION_BOX p 1
               (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] t),
                COMPL_PSPACE p (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]t)));
             DECISION_BOX p 1
               (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t),
                COMPL_PSPACE p (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t)));
             DECISION_BOX p 1
               (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t),
                COMPL_PSPACE p (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t)));
             DECISION_BOX p 1
               (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t),
                COMPL_PSPACE p (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t)));
             DECISION_BOX p 1
               (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t),
                COMPL_PSPACE p (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t)));
             DECISION_BOX p 1
               (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t),
                COMPL_PSPACE p (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t)))]]) =
    (1 −
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
              (exp (-FR_PV_H4 * t) * exp (-FR_PV_H5 * t)))))))))``,


rw [EXP_ET_SUCCESS_DISTRIB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_LOAD_SHEDDING_0_SMART_GRID_DISTRIBUTION]
\\ CONJ_TAC
   >-( rw []
       \\ metis_tac [])   
\\ rw [SUCCESS_DEF]
\\ fs [EXP_ET_SUCCESS_DISTRIB_DEF]
\\ fs [RELIABILITY_DEF]
\\ fs [distribution_def]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)

val PROB_LOAD_SHEDDING_100_SMART_GRID_EXPONENTIAL_DISTRIBUTION =
store_thm("PROB_LOAD_SHEDDING_100_SMART_GRID_EXPONENTIAL_DISTRIBUTION",
``!p WT_A1 WT_A2 WT_A3 WT_A4 WT_A5 WT_B1 WT_B2 WT_B3 WT_B4 WT_B5 WT_C1 WT_C2 WT_C3 WT_C4 WT_C5
     WT_D1 WT_D2 WT_D3 WT_D4 WT_D5 PV_E1 PV_E2 PV_E3 PV_E4 PV_E5 PV_F1 PV_F2 PV_F3 PV_F4 PV_F5
     PV_G1 PV_G2 PV_G3 PV_G4 PV_G5 PV_H1 PV_H2 PV_H3 PV_H4 PV_H5 t
     FR_WT_A1 FR_WT_A2 FR_WT_A3 FR_WT_A4 FR_WT_A5
     FR_WT_B1 FR_WT_B2 FR_WT_B3 FR_WT_B4 FR_WT_B5
     FR_WT_C1 FR_WT_C2 FR_WT_C3 FR_WT_C4 FR_WT_C5
     FR_WT_D1 FR_WT_D2 FR_WT_D3 FR_WT_D4 FR_WT_D5
     FR_PV_E1 FR_PV_E2 FR_PV_E3 FR_PV_E4 FR_PV_E5
     FR_PV_F1 FR_PV_F2 FR_PV_F3 FR_PV_F4 FR_PV_F5
     FR_PV_G1 FR_PV_G2 FR_PV_G3 FR_PV_G4 FR_PV_G5
     FR_PV_H1 FR_PV_H2 FR_PV_H3 FR_PV_H4 FR_PV_H5.
 (prob_space p ∧
         (∀y.
              MEM y
                [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
                 ↑ p WT_A5 t; ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t;
                 ↑ p WT_B4 t; ↑ p WT_B5 t; ↑ p WT_C1 t; ↑ p WT_C2 t;
                 ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t; ↑ p WT_D1 t;
                 ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
                 ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
                 ↑ p PV_E5 t; ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t;
                 ↑ p PV_F4 t; ↑ p PV_F5 t; ↑ p PV_G1 t; ↑ p PV_G2 t;
                 ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t; ↑ p PV_H1 t;
                 ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t] ⇒
              y ∈ events p) ∧
         disjoint
           {CONSEQ_PATH p
              [COMPL_PSPACE p
                 (R_WTA p
                    [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
                     ↑ p WT_A5 t]);
               COMPL_PSPACE p
                 (R_WTB p
                    [↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t; ↑ p WT_B4 t;
                     ↑ p WT_B5 t]);
               COMPL_PSPACE p
                 (R_WTC p
                    [↑ p WT_C1 t; ↑ p WT_C2 t; ↑ p WT_C3 t; ↑ p WT_C4 t;
                     ↑ p WT_C5 t]);
               COMPL_PSPACE p
                 (R_WTD p
                    [↑ p WT_D1 t; ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t;
                     ↑ p WT_D5 t]);
               COMPL_PSPACE p
                 (R_PVE p
                    [↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
                     ↑ p PV_E5 t]);
               COMPL_PSPACE p
                 (R_PVF p
                    [↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t; ↑ p PV_F4 t;
                     ↑ p PV_F5 t]);
               COMPL_PSPACE p
                 (R_PVG p
                    [↑ p PV_G1 t; ↑ p PV_G2 t; ↑ p PV_G3 t; ↑ p PV_G4 t;
                     ↑ p PV_G5 t]);
               COMPL_PSPACE p
                 (R_PVH p
                    [↑ p PV_H1 t; ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t;
                     ↑ p PV_H5 t])]} ∧
         MUTUAL_INDEP p
           (↑ p WT_A1 t:: ↑ p WT_A2 t:: ↑ p WT_A3 t:: ↑ p WT_A4 t::
                 ↑ p WT_A5 t:: ↑ p WT_B1 t:: ↑ p WT_B2 t:: ↑ p WT_B3 t::
                 ↑ p WT_B4 t:: ↑ p WT_B5 t:: ↑ p WT_C1 t:: ↑ p WT_C2 t::
                 ↑ p WT_C3 t:: ↑ p WT_C4 t:: ↑ p WT_C5 t:: ↑ p WT_D1 t::
                 ↑ p WT_D2 t:: ↑ p WT_D3 t:: ↑ p WT_D4 t:: ↑ p WT_D5 t::
                 ↑ p PV_E1 t:: ↑ p PV_E2 t:: ↑ p PV_E3 t:: ↑ p PV_E4 t::
                 ↑ p PV_E5 t:: ↑ p PV_F1 t:: ↑ p PV_F2 t:: ↑ p PV_F3 t::
                 ↑ p PV_F4 t:: ↑ p PV_F5 t:: ↑ p PV_G1 t:: ↑ p PV_G2 t::
                 ↑ p PV_G3 t:: ↑ p PV_G4 t:: ↑ p PV_G5 t:: ↑ p PV_H1 t::
                 ↑ p PV_H2 t:: ↑ p PV_H3 t:: ↑ p PV_H4 t:: ↑ p PV_H5 t::
                compl_list p
                  [↑ p WT_A1 t; ↑ p WT_A2 t; ↑ p WT_A3 t; ↑ p WT_A4 t;
                   ↑ p WT_A5 t; ↑ p WT_B1 t; ↑ p WT_B2 t; ↑ p WT_B3 t;
                   ↑ p WT_B4 t; ↑ p WT_B5 t; ↑ p WT_C1 t; ↑ p WT_C2 t;
                   ↑ p WT_C3 t; ↑ p WT_C4 t; ↑ p WT_C5 t; ↑ p WT_D1 t;
                   ↑ p WT_D2 t; ↑ p WT_D3 t; ↑ p WT_D4 t; ↑ p WT_D5 t;
                   ↑ p PV_E1 t; ↑ p PV_E2 t; ↑ p PV_E3 t; ↑ p PV_E4 t;
                   ↑ p PV_E5 t; ↑ p PV_F1 t; ↑ p PV_F2 t; ↑ p PV_F3 t;
                   ↑ p PV_F4 t; ↑ p PV_F5 t; ↑ p PV_G1 t; ↑ p PV_G2 t;
                   ↑ p PV_G3 t; ↑ p PV_G4 t; ↑ p PV_G5 t; ↑ p PV_H1 t;
                   ↑ p PV_H2 t; ↑ p PV_H3 t; ↑ p PV_H4 t; ↑ p PV_H5 t])) /\ 0 <= t /\
  EXP_ET_SUCCESS_DISTRIB_LIST p
    [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5;
     WT_B1; WT_B2; WT_B3; WT_B4; WT_B5;
     WT_C1; WT_C2; WT_C3; WT_C4; WT_C5;
     WT_D1; WT_D2; WT_D3; WT_D4; WT_D5;
     PV_E1; PV_E2; PV_E3; PV_E4; PV_E5;
     PV_F1; PV_F2; PV_F3; PV_F4; PV_F5;
     PV_G1; PV_G2; PV_G3; PV_G4; PV_G5;
     PV_H1; PV_H2; PV_H3; PV_H4; PV_H5]
    [FR_WT_A1; FR_WT_A2; FR_WT_A3; FR_WT_A4; FR_WT_A5;
     FR_WT_B1; FR_WT_B2; FR_WT_B3; FR_WT_B4; FR_WT_B5;
     FR_WT_C1; FR_WT_C2; FR_WT_C3; FR_WT_C4; FR_WT_C5;
     FR_WT_D1; FR_WT_D2; FR_WT_D3; FR_WT_D4; FR_WT_D5;
     FR_PV_E1; FR_PV_E2; FR_PV_E3; FR_PV_E4; FR_PV_E5;
     FR_PV_F1; FR_PV_F2; FR_PV_F3; FR_PV_F4; FR_PV_F5;
     FR_PV_G1; FR_PV_G2; FR_PV_G3; FR_PV_G4; FR_PV_G5;
     FR_PV_H1; FR_PV_H2; FR_PV_H3; FR_PV_H4; FR_PV_H5] ==> 

(prob p
    (CONSEQ_BOX p
           [[DECISION_BOX p 0
               (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t),
                COMPL_PSPACE p (R_WTA p (SUCCESS_LIST p [WT_A1; WT_A2; WT_A3; WT_A4; WT_A5] t)));
             DECISION_BOX p 0
               (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t),
                COMPL_PSPACE p (R_WTB p (SUCCESS_LIST p [WT_B1; WT_B2; WT_B3; WT_B4; WT_B5] t)));
             DECISION_BOX p 0
               (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5] t),
                COMPL_PSPACE p (R_WTC p (SUCCESS_LIST p [WT_C1; WT_C2; WT_C3; WT_C4; WT_C5]t)));
             DECISION_BOX p 0
               (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t),
                COMPL_PSPACE p (R_WTD p (SUCCESS_LIST p [WT_D1; WT_D2; WT_D3; WT_D4; WT_D5] t)));
             DECISION_BOX p 0
               (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t),
                COMPL_PSPACE p (R_PVE p (SUCCESS_LIST p [PV_E1; PV_E2; PV_E3; PV_E4; PV_E5] t)));
             DECISION_BOX p 0
               (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t),
                COMPL_PSPACE p (R_PVF p (SUCCESS_LIST p [PV_F1; PV_F2; PV_F3; PV_F4; PV_F5] t)));
             DECISION_BOX p 0
               (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t),
                COMPL_PSPACE p (R_PVG p (SUCCESS_LIST p [PV_G1; PV_G2; PV_G3; PV_G4; PV_G5] t)));
             DECISION_BOX p 0
               (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t),
                COMPL_PSPACE p (R_PVH p (SUCCESS_LIST p [PV_H1; PV_H2; PV_H3; PV_H4; PV_H5] t)))]]) =
(1 − exp (-FR_WT_A1 * t)) *
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
              (exp (-FR_PV_H4 * t) * exp (-FR_PV_H5 * t)))))))))``,

rw [EXP_ET_SUCCESS_DISTRIB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_LOAD_SHEDDING_100_SMART_GRID_DISTRIBUTION]
\\ CONJ_TAC
   >-( rw []
       \\ metis_tac [])   
\\ rw [SUCCESS_DEF]
\\ fs [EXP_ET_SUCCESS_DISTRIB_DEF]
\\ fs [RELIABILITY_DEF]
\\ fs [distribution_def]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------*)  
(*  Evaluation of Some Verified  Load Shedding Safety Expressions  *)
(*-----------------------------------------------------------------*)

(*----------------------------------------*)   
(* Assume  FR_WT_A1   =   0.13 per year   *)
(* Assume  FR_WT_A2   =   0.13 per year   *)
(* Assume  FR_WT_A3   =   0.13 per year   *)
(* Assume  FR_WT_A4   =   0.13 per year   *)
(* Assume  FR_WT_A5   =   0.13 per year   *)
(* Assume  FR_WT_B1   =   0.13 per year   *)
(* Assume  FR_WT_B2   =   0.13 per year   *)
(* Assume  FR_WT_B3   =   0.13 per year   *)
(* Assume  FR_WT_B4   =   0.13 per year   *)
(* Assume  FR_WT_B5   =   0.13 per year   *)
(* Assume  FR_WT_C1   =   0.13 per year   *)
(* Assume  FR_WT_C2   =   0.13 per year   *)
(* Assume  FR_WT_C3   =   0.13 per year   *)
(* Assume  FR_WT_C4   =   0.13 per year   *)
(* Assume  FR_WT_C5   =   0.13 per year   *)
(* Assume  FR_WT_D1   =   0.13 per year   *)
(* Assume  FR_WT_D2   =   0.13 per year   *)
(* Assume  FR_WT_D3   =   0.13 per year   *)
(* Assume  FR_WT_D4   =   0.13 per year   *)
(* Assume  FR_WT_D5   =   0.13 per year   *)
(* Assume  FR_PV_E1   =   0.11 per year   *)
(* Assume  FR_PV_E2   =   0.11 per year   *)
(* Assume  FR_PV_E3   =   0.11 per year   *)
(* Assume  FR_PV_E4   =   0.11 per year   *)
(* Assume  FR_PV_E5   =   0.11 per year   *)
(* Assume  FR_PV_F1   =   0.11 per year   *)
(* Assume  FR_PV_F2   =   0.11 per year   *)
(* Assume  FR_PV_F3   =   0.11 per year   *)
(* Assume  FR_PV_F4   =   0.11 per year   *)
(* Assume  FR_PV_F5   =   0.11 per year   *)
(* Assume  FR_PV_G1   =   0.11 per year   *)
(* Assume  FR_PV_G2   =   0.11 per year   *)
(* Assume  FR_PV_G3   =   0.11 per year   *)
(* Assume  FR_PV_G4   =   0.11 per year   *)
(* Assume  FR_PV_G5   =   0.11 per year   *)
(* Assume  FR_PV_H1   =   0.11 per year   *)
(* Assume  FR_PV_H2   =   0.11 per year   *)
(* Assume  FR_PV_H3   =   0.11 per year   *)
(* Assume  FR_PV_H4   =   0.11 per year   *)
(* Assume  FR_PV_H5   =   0.11 per year   *)
(*----------------------------------------*)

PROBABILITY ``PROB_LOAD_SHEDDING_0``
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


PROBABILITY ``PROB_LOAD_SHEDDING_100``
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

PROBABILITY ``PROB_LOAD_SHEDDING_12_5``
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