import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

/-!
# Constancy on qW's kernel from the global central character

This nonmanifest experimental module is kernel checked relative to its
explicit inputs. The central character is the
ordinary linear character nu of Z(X), as in Lemma 5.2. We set Z0 equal to
its kernel in X. The ordinary lies-over formula on this same centre gives
constancy on the actual kernel of qW by its previously proved description.

No local modular representation, independently chosen local root lift, or
comparison of two central characters is introduced. The ordinary lies-over
formula is supplied by the preceding central-sector argument. Binding nu to
the central character of the global Brauer character remains a separate
obligation. Neither qW-kernel constancy nor representation-kernel containment
is a source premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.CentralEllPrimeWeightLocalCharacterConstancyDirect

open ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

universe u

theorem character_constant_on_qW_ker_of_global_central_character
    {K X : Type u} [Field K] [CharZero K] [Group X] [Finite X]
    (Q : Subgroup X) (nu : Subgroup.center X →* Kˣ)
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0 : Z0 = nu.ker.map (Subgroup.center X).subtype)
    (theta : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (hLiesOver : ∀ z : Subgroup.center X,
      theta (QuotientGroup.mk'
          (Q.subgroupOf (Subgroup.normalizer (Q : Set X)))
          (⟨z.1, Subgroup.center_le_normalizer (Q : Set X) z.2⟩ :
            Subgroup.normalizer (Q : Set X))) =
        theta (1 : NormalizerQuotient Q) * (nu z : K)) :
    ∀ x : (qW Z0 Q).ker,
      theta (x : NormalizerQuotient Q) = theta (1 : NormalizerQuotient Q) := by
  have hZ0central : Z0 ≤ Subgroup.center X := by
    rw [hZ0]
    rintro x ⟨z, _hz, rfl⟩
    exact z.2
  intro x
  have hx : (x : NormalizerQuotient Q) ∈
      (Z0.subgroupOf (Subgroup.normalizer (Q : Set X))).map
        (QuotientGroup.mk'
          (Q.subgroupOf (Subgroup.normalizer (Q : Set X)))) := by
    rw [← qW_ker_eq_localCentralKernel_map Z0 Q hZ0central]
    exact x.2
  rcases hx with ⟨y, hy, hxy⟩
  change (y : X) ∈ Z0 at hy
  rw [hZ0] at hy
  rcases hy with ⟨z, hz, hzy⟩
  let zN : Subgroup.normalizer (Q : Set X) :=
    ⟨z.1, Subgroup.center_le_normalizer (Q : Set X) z.2⟩
  have hzN : zN = y := by
    apply Subtype.ext
    exact hzy
  have hxz : QuotientGroup.mk'
      (Q.subgroupOf (Subgroup.normalizer (Q : Set X))) zN =
        (x : NormalizerQuotient Q) := by
    rw [hzN]
    exact hxy
  have hnu : nu z = 1 := MonoidHom.mem_ker.mp hz
  calc
    theta (x : NormalizerQuotient Q) =
        theta (QuotientGroup.mk'
          (Q.subgroupOf (Subgroup.normalizer (Q : Set X))) zN) :=
      congrArg theta hxz.symm
    _ = theta (1 : NormalizerQuotient Q) * (nu z : K) := hLiesOver z
    _ = theta (1 : NormalizerQuotient Q) := by rw [hnu]; simp

end ModularRep.PaperProofs.CentralEllPrimeWeightLocalCharacterConstancyDirect


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
