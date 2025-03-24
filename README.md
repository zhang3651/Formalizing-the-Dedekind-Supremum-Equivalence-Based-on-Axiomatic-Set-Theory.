# Formalizing the Dedekind-Supremum Equivalence Based on Axiomatic Set Theory
The completeness theorems of real numbers constitute the foundation of calculus and mathematical analysis, with numerous equivalent formulations. Based on MK axiomatic set theory, we have completed the formal verification of the equivalence between Dedekind's fundamental theorem and the Supremum Principle using Coq.
Our work builds upon the MK axiomatic set theory and formal proofs in the foundations of analysis. Related links:
https://github.com/bbLeng/Formalization-of-number-systems
# Files
The proof is based on Morse-Kelley axiomatic set theory, which includes the following three .v files:

Pre_MK_Logic.v  

MK_Structure1.v  (*Depends on Pre_MK_Logic.v *)

MK_Theorems1.v  (* Depends on MK_Structure1.v *)

FA_R1.v  (* Depends on MK_Theorems1.v *)

Real_Completeness.v  (* Depends on FA_R1.v *)
# Authors
This project is implemented by Ce Zhang, Wensheng Yu.
