import ManuscriptIBAW.Library.FixedBasis
import ManuscriptIBAW.Library.FixedBasicSet
import ManuscriptIBAW.Library.EquivariantBijections
import ManuscriptIBAW.Library.TensorStabilizer
import ManuscriptIBAW.Library.MultiplierQuotient
import ManuscriptIBAW.Characters.CyclotomicOrdinaryLabels
import ManuscriptIBAW.Jordan.TypeBLocalized
import ManuscriptIBAW.Jordan.TypeCEven
import ManuscriptIBAW.TypeC.EvenApplicationLowRank
import ManuscriptIBAW.TypeC.Theorem
import ManuscriptIBAW.TypeB.AllPrimes
import ManuscriptIBAW.TypeB.DefectEight
import ManuscriptIBAW.Preliminaries
import ManuscriptIBAW.Main

/-!
# Lean companion to the manuscript

This module exports the general arguments, preliminary statements, Jordan
restriction lemmas and the Type C, Type B and sporadic applications. The
main theorem and its finite group consequence use the specified groups,
covering maps, character values and block families.

Published results, computations and structural interpretations remain
explicit assumptions. The companion distinguishes these assumptions from the
deductions checked in Lean. This is a formalisation of selected arguments
under those assumptions, not an unconditional verification of the entire
manuscript.
-/

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's companion and source audit.
-/
