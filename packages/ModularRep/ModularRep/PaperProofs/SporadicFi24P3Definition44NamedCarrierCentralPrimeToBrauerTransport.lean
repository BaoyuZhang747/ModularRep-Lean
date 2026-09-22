import ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeRegularLifting

/-!
# Canonical quotient roots and nonzero specified block images

The original root determines the quotient realisation. Orthogonality and
idempotence make distinct nonzero block images distinguishable.
-/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport

open ModularRep
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierPrimeRegularLifting

universe u v w

theorem canonicalQuotientRealisation
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [Group G] [Fintype G]
    (iota : PrimeRegularRootEmbedding p k K G)
    (Z : Subgroup G) [Z.Normal] :
    QuotientRealisationSource Z iota (quotientRoot iota Z) := by
  refine ⟨?_, ?_⟩
  · intro zeta
    let inc : rootsOfUnity (primeRegularExponent p G) k :=
      PrimeRegularRootEmbedding.rootsOfUnityInclusion
        (quotientExponent_dvd (p := p) Z) zeta
    calc
      iota.lift (((zeta : kˣ) : k)) = iota.liftRoot inc := iota.lift_coe inc
      _ = (quotientRoot iota Z).liftRoot zeta := rfl
      _ = (quotientRoot iota Z).lift (((zeta : kˣ) : k)) :=
        ((quotientRoot iota Z).lift_coe zeta).symm
  · exact primeRegularElement_map_surjective_of_surjective
      iota.prime (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)

theorem blockIndex_eq_of_map_eq_of_ne_zero
    {A : Type u} {B : Type v} {I : Type w}
    [Ring A] [Ring B] [Fintype I]
    {e : I → A} (D : BlockIdempotentDecomposition e)
    (F : A →+* B) (i j : I)
    (hij : F (e i) = F (e j)) (hi : F (e i) ≠ 0) : i = j := by
  by_contra hne
  apply hi
  calc
    F (e i) = F (e i * e i) := congrArg F (D.primitive i).idempotent.eq.symm
    _ = F (e i) * F (e i) := map_mul F _ _
    _ = F (e i) * F (e j) := congrArg (fun x => F (e i) * x) hij
    _ = F (e i * e j) := (map_mul F _ _).symm
    _ = 0 := by rw [D.complete.ortho hne, map_zero]

theorem nonzeroBlockImage_injective
    {A : Type u} {B : Type v} {I : Type w}
    [Ring A] [Ring B] [Fintype I]
    {e : I → A} (D : BlockIdempotentDecomposition e) (F : A →+* B) :
    Function.Injective (fun i : {i : I // F (e i) ≠ 0} => F (e i.1)) := by
  intro i j hij
  apply Subtype.ext
  exact blockIndex_eq_of_map_eq_of_ne_zero D F i.1 j.1 hij i.2

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
