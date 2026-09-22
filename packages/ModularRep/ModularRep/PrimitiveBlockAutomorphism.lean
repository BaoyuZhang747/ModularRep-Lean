import Mathlib.Algebra.MonoidAlgebra.MapDomain
import ModularRep.BlockIdempotentDecomposition
import ModularRep.CentralCharacterBlockSector
import ModularRep.GroupAlgebraCentralFunctions

/-!
# Automorphisms of literal block idempotents

An automorphism of a finite group acts on its modular group algebra by
transporting the group basis.  This file restricts that ring automorphism to
the literal subtype of primitive central idempotents and constructs the
opposite automorphism action used by the manuscript's right-action convention.
-/

open scoped MonoidAlgebra

noncomputable section

namespace ModularRep

/-- The literal carrier of block idempotents in a group algebra. -/
abbrev LiteralPrimitiveBlock (k X : Type*) [Field k] [Group X] :=
  {b : k[X] // IsPrimitiveCentralIdempotent b}

/-- Transporting the group basis by the inverse automorphism carries the
central character idempotent of `nu` to that of `nu ∘ alpha` on the
centre. -/
theorem centralCharacterIdempotent_mapDomainRingEquiv_center
    {k X : Type*} [Field k] [Group X]
    [Fintype (Subgroup.center X)]
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    (alpha : MulAut X) (nu : Subgroup.center X →* kˣ) :
    MonoidAlgebra.mapDomainRingEquiv k alpha.symm
        (centralCharacterIdempotent (Subgroup.center X) nu) =
      centralCharacterIdempotent (Subgroup.center X)
        (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  change
    (MonoidAlgebra.mapDomainRingEquiv k alpha.symm
      (centralCharacterIdempotent (Subgroup.center X) nu)).coeff x =
    (centralCharacterIdempotent (Subgroup.center X)
      (nu.comp (Subgroup.centerCongr alpha).toMonoidHom)).coeff x
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]
  change
    (centralCharacterIdempotent (Subgroup.center X) nu).coeff (alpha x) =
      (centralCharacterIdempotent (Subgroup.center X)
        (nu.comp (Subgroup.centerCongr alpha).toMonoidHom)).coeff x
  by_cases hx : x ∈ Subgroup.center X
  · let z : Subgroup.center X := ⟨x, hx⟩
    change
      (centralCharacterIdempotent (Subgroup.center X) nu).coeff
          (alpha (z : X)) =
        (centralCharacterIdempotent (Subgroup.center X)
          (nu.comp (Subgroup.centerCongr alpha).toMonoidHom)).coeff (z : X)
    rw [← Subgroup.centerCongr_apply_coe alpha z,
      centralCharacterIdempotent_coeff_coe,
      centralCharacterIdempotent_coeff_coe]
    rfl
  · have hax : alpha x ∉ Subgroup.center X := by
      intro h
      apply hx
      exact (MulEquivClass.apply_mem_center_iff alpha).mp h
    rw [centralCharacterIdempotent_coeff_of_not_mem
        (Subgroup.center X) nu hax,
      centralCharacterIdempotent_coeff_of_not_mem
        (Subgroup.center X)
        (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) hx]

/-- The central character sector of a primitive block is transported by
pullback along the group automorphism when its group algebra basis is
transported by the inverse automorphism. -/
theorem IsPrimitiveCentralIdempotent.centralCharacterSector_mapDomainRingEquiv_center
    {k X : Type*} [Field k] [Group X]
    [Fintype (Subgroup.center X)] [IsAlgClosed k]
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    {b : k[X]} (hb : IsPrimitiveCentralIdempotent b)
    (alpha : MulAut X) :
    (hb.mapRingEquiv
      (MonoidAlgebra.mapDomainRingEquiv k alpha.symm)).centralCharacterSector
        (Subgroup.center X) le_rfl =
      (hb.centralCharacterSector (Subgroup.center X) le_rfl).comp
        (Subgroup.centerCongr alpha).toMonoidHom := by
  let sigma : k[X] ≃+* k[X] :=
    MonoidAlgebra.mapDomainRingEquiv k alpha.symm
  let nu : Subgroup.center X →* kˣ :=
    hb.centralCharacterSector (Subgroup.center X) le_rfl
  change
    (hb.mapRingEquiv sigma).centralCharacterSector
        (Subgroup.center X) le_rfl =
      nu.comp (Subgroup.centerCongr alpha).toMonoidHom
  have hmap :
      sigma (centralCharacterIdempotent (Subgroup.center X) nu) =
        centralCharacterIdempotent (Subgroup.center X)
          (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) := by
    simpa only [sigma] using
      centralCharacterIdempotent_mapDomainRingEquiv_center alpha nu
  have hbase :
      b * centralCharacterIdempotent (Subgroup.center X) nu = b := by
    simpa only [nu] using
      hb.mul_centralCharacterSector (Subgroup.center X) le_rfl
  have hmul :
      sigma b * centralCharacterIdempotent (Subgroup.center X)
          (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) =
        sigma b := by
    rw [← hmap, ← sigma.map_mul, hbase]
  have hsector :
      IsCentralCharacterSector (Subgroup.center X) (sigma b)
        (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) := by
    refine ⟨hmul, ?_⟩
    intro mu hmu
    calc
      sigma b * centralCharacterIdempotent (Subgroup.center X) mu =
          (sigma b * centralCharacterIdempotent (Subgroup.center X)
            (nu.comp (Subgroup.centerCongr alpha).toMonoidHom)) *
              centralCharacterIdempotent (Subgroup.center X) mu := by
                rw [hmul]
      _ = sigma b *
          (centralCharacterIdempotent (Subgroup.center X)
            (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) *
              centralCharacterIdempotent (Subgroup.center X) mu) :=
        mul_assoc _ _ _
      _ = 0 := by
        rw [centralCharacterIdempotent_mul_eq_zero
          (Subgroup.center X)
          (nu.comp (Subgroup.centerCongr alpha).toMonoidHom) mu
          (Ne.symm hmu), mul_zero]
  exact ((hb.mapRingEquiv sigma).centralCharacterSector_unique
    (Subgroup.center X) le_rfl hsector).symm

namespace LiteralPrimitiveBlock

variable {k X : Type*} [Field k] [Group X]

/-- Coefficients of a central group algebra element are constant on conjugacy
classes. -/
theorem central_coeff_conjugate {b : k[X]} (hb : IsMulCentral b)
    (g x : X) : b.coeff (g * x * g⁻¹) = b.coeff x := by
  let z : GroupAlgebraCenter k X :=
    ⟨b, by
      rw [Subalgebra.mem_center_iff]
      intro y
      exact (hb.comm y).eq.symm⟩
  change (z : k[X]).coeff (g * x * g⁻¹) = (z : k[X]).coeff x
  exact GroupAlgebraCenter.coeff_conjugate z g x

/-- Right transport of a literal block by a group automorphism.  The inverse
on the group basis is forced by the right-action convention on characters. -/
def rightTwistBlock (b : LiteralPrimitiveBlock k X) (alpha : MulAut X) :
    LiteralPrimitiveBlock k X :=
  ⟨MonoidAlgebra.mapDomainRingEquiv k alpha.symm b.1,
    b.2.mapRingEquiv (MonoidAlgebra.mapDomainRingEquiv k alpha.symm)⟩

@[simp]
theorem rightTwistBlock_val (b : LiteralPrimitiveBlock k X)
    (alpha : MulAut X) :
    (rightTwistBlock b alpha).1 =
      MonoidAlgebra.mapDomainRingEquiv k alpha.symm b.1 :=
  rfl

/-- Canonical opposite-automorphism action on literal block idempotents. -/
@[instance_reducible]
noncomputable instance rightMulAction :
    MulAction (MulAut X)ᵐᵒᵖ (LiteralPrimitiveBlock k X) where
  smul alpha b := rightTwistBlock b (MulOpposite.unop alpha)
  one_smul b := by
    apply Subtype.ext
    change MonoidAlgebra.mapDomainRingEquiv k
      (MulOpposite.unop (1 : (MulAut X)ᵐᵒᵖ)).symm b.1 = b.1
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    change (MonoidAlgebra.mapDomainRingEquiv k
      (MulOpposite.unop (1 : (MulAut X)ᵐᵒᵖ)).symm b.1).coeff x = b.1.coeff x
    rw [MonoidAlgebra.coeff_mapDomainRingEquiv,
      Finsupp.equivMapDomain_apply]
    rfl
  mul_smul alpha beta b := by
    apply Subtype.ext
    change MonoidAlgebra.mapDomainRingEquiv k
        (MulOpposite.unop (alpha * beta)).symm b.1 =
      MonoidAlgebra.mapDomainRingEquiv k (MulOpposite.unop alpha).symm
        (MonoidAlgebra.mapDomainRingEquiv k (MulOpposite.unop beta).symm b.1)
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    change (MonoidAlgebra.mapDomainRingEquiv k
        (MulOpposite.unop (alpha * beta)).symm b.1).coeff x =
      (MonoidAlgebra.mapDomainRingEquiv k (MulOpposite.unop alpha).symm
        (MonoidAlgebra.mapDomainRingEquiv k
          (MulOpposite.unop beta).symm b.1)).coeff x
    rw [MonoidAlgebra.coeff_mapDomainRingEquiv,
      MonoidAlgebra.coeff_mapDomainRingEquiv,
      MonoidAlgebra.coeff_mapDomainRingEquiv,
      Finsupp.equivMapDomain_apply,
      Finsupp.equivMapDomain_apply,
      Finsupp.equivMapDomain_apply]
    rfl

@[simp]
theorem rightMulAction_smul_val (alpha : (MulAut X)ᵐᵒᵖ)
    (b : LiteralPrimitiveBlock k X) :
    (alpha • b).1 =
      MonoidAlgebra.mapDomainRingEquiv k (MulOpposite.unop alpha).symm b.1 :=
  rfl

/-- The canonical right action on literal primitive blocks transports their
central character sectors by pullback along the underlying automorphism. -/
theorem rightMulAction_smul_centralCharacterSector
    [Fintype (Subgroup.center X)] [IsAlgClosed k]
    [Invertible (Fintype.card (Subgroup.center X) : k)]
    (alpha : (MulAut X)ᵐᵒᵖ) (b : LiteralPrimitiveBlock k X) :
    (alpha • b).2.centralCharacterSector (Subgroup.center X) le_rfl =
      (b.2.centralCharacterSector (Subgroup.center X) le_rfl).comp
        (Subgroup.centerCongr (MulOpposite.unop alpha)).toMonoidHom := by
  change
    (b.2.mapRingEquiv
      (MonoidAlgebra.mapDomainRingEquiv k
        (MulOpposite.unop alpha).symm)).centralCharacterSector
        (Subgroup.center X) le_rfl =
      _
  exact b.2.centralCharacterSector_mapDomainRingEquiv_center
    (MulOpposite.unop alpha)

/-- Inner automorphisms fix every literal block idempotent. -/
theorem inner_smul (g : X) (b : LiteralPrimitiveBlock k X) :
    MulOpposite.op (MulAut.conj g⁻¹) • b = b := by
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingEquiv k
    (MulAut.conj g⁻¹).symm b.1 = b.1
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  change (MonoidAlgebra.mapDomainRingEquiv k
    (MulAut.conj g⁻¹).symm b.1).coeff x = b.1.coeff x
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]
  change b.1.coeff (g⁻¹ * x * (g⁻¹)⁻¹) = b.1.coeff x
  exact central_coeff_conjugate b.2.central g⁻¹ x

end LiteralPrimitiveBlock

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
