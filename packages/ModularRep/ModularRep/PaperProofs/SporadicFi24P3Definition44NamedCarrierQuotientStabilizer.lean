import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPacketValues

/-!
# The automorphism stabilizer on the original centreless group

The canonical central quotient map is bijective. Its actual inflation
equation identifies fixedness of the two character functions, even when
their root embeddings were chosen independently. This identifies the
stabilizer in Spath's ambient packet with Aut(X)_phi.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientStabilizer

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel

universe u

theorem twist_fixed_iff_of_values
    {R G H : Type u} [Group G] [Group H] {p : ℕ}
    (e : G ≃* H) (chi : PrimeRegularClassFunction R G p)
    (chi' : PrimeRegularClassFunction R H p)
    (hval : ∀ x : PrimeRegularElement (G := G) p,
      chi' (PrimeRegularElement.map e.toMonoidHom x) = chi x)
    (a : MulAut G) :
    chi.twist a = chi ↔ chi'.twist (MulAut.congr e a) = chi' := by
  have hsquare (x : PrimeRegularElement (G := G) p) :
      PrimeRegularElement.map (MulAut.congr e a).toMonoidHom
          (PrimeRegularElement.map e.toMonoidHom x) =
        PrimeRegularElement.map e.toMonoidHom (PrimeRegularElement.map a.toMonoidHom x) := by
    apply Subtype.ext
    change e (a (e.symm (e x.1))) = e (a x.1)
    rw [e.symm_apply_apply]
  constructor
  · intro h
    apply PrimeRegularClassFunction.ext
    intro y
    obtain ⟨x, rfl⟩ := (PrimeRegularElement.equiv e).surjective y
    change chi' (PrimeRegularElement.map (MulAut.congr e a).toMonoidHom
        (PrimeRegularElement.map e.toMonoidHom x)) =
      chi' (PrimeRegularElement.map e.toMonoidHom x)
    calc
      _ = chi' (PrimeRegularElement.map e.toMonoidHom
          (PrimeRegularElement.map a.toMonoidHom x)) := congrArg chi' (hsquare x)
      _ = chi (PrimeRegularElement.map a.toMonoidHom x) := hval _
      _ = chi x := congrArg (fun f => f x) h
      _ = chi' (PrimeRegularElement.map e.toMonoidHom x) := (hval x).symm
  · intro h
    apply PrimeRegularClassFunction.ext
    intro x
    change chi (PrimeRegularElement.map a.toMonoidHom x) = chi x
    calc
      _ = chi' (PrimeRegularElement.map e.toMonoidHom
          (PrimeRegularElement.map a.toMonoidHom x)) := (hval _).symm
      _ = chi' (PrimeRegularElement.map (MulAut.congr e a).toMonoidHom
          (PrimeRegularElement.map e.toMonoidHom x)) := congrArg chi' (hsquare x).symm
      _ = chi' (PrimeRegularElement.map e.toMonoidHom x) :=
        congrArg (fun f => f (PrimeRegularElement.map e.toMonoidHom x)) h
      _ = chi x := hval x

def quotientStabilizerEquiv
    (P : Definition35Problem.{u}) (hc : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P) (q : CentralQuotientBrauerSource P reference psi) :
    MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 ≃*
      QuotientBrauerAutomorphismStabilizer P reference psi q := by
  let e : P.H ≃* CentralCharacterQuotient P reference :=
    MulEquiv.ofBijective (centralCharacterQuotientMap P reference)
      (centralCharacterQuotientMap_bijective_of_centerless P hc reference)
  let E := MulEquiv.op (MulAut.congr e)
  let S := MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1
  let T := QuotientBrauerAutomorphismStabilizer P reference psi q
  have hval (x : PrimeRegularElement (G := P.H) P.p) :
      q.brauer.1 (PrimeRegularElement.map e.toMonoidHom x) = psi.1.1 x :=
    congrArg (fun chi => chi x) q.inflation
  have hfixed (a : (MulAut P.H)ᵐᵒᵖ) : a ∈ S ↔ E a ∈ T := by
    change a • psi.1 = psi.1 ↔ E a • q.brauer = q.brauer
    constructor
    · intro h
      apply Subtype.ext
      have hfun : psi.1.1.twist a.unop = psi.1.1 := congrArg Subtype.val h
      exact (twist_fixed_iff_of_values e psi.1.1 q.brauer.1 hval a.unop).mp hfun
    · intro h
      apply Subtype.ext
      have hfun : q.brauer.1.twist (MulAut.congr e a.unop) = q.brauer.1 := congrArg Subtype.val h
      exact (twist_fixed_iff_of_values e psi.1.1 q.brauer.1 hval a.unop).mpr hfun
  have hmap : S.map E.toMonoidHom = T := by
    apply Subgroup.ext
    intro b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hfixed a).mp ha
    · intro hb
      refine ⟨E.symm b, ?_, E.apply_symm_apply b⟩
      apply (hfixed (E.symm b)).mpr
      simpa only [E.apply_symm_apply] using hb
  exact (E.subgroupMap S).trans (MulEquiv.subgroupCongr hmap)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
