import ModularRep.GroupAlgebraCentralBrauerMap

/-!
# Interval-valued central Brauer maps

The central Brauer map to `C_G(P)` can be followed by the literal group algebra
embedding into `k[H]` whenever `C_G(P) ≤ H`.  If also `H ≤ N_G(P)`, the
particular image of a globally central element remains central in `k[H]`.

This does not define a map from the whole centre of `k[C_G(P)]` to the centre
of `k[H]`: centrality here depends on the globally central source element.
-/

namespace ModularRep

open MonoidAlgebra

noncomputable section

variable {p : Nat} {k G : Type*}
variable [CommSemiring k] [Group G]
variable [Finite G] [Fact p.Prime] [CharP k p]

local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

/-- The literal group algebra embedding induced by `C_G(P) ≤ H`.

This map alone makes no claim that its image is central in `k[H]`. -/
def centralizerAlgebraMapTo
    (P H : Subgroup G) (hCH : centralizerOf P ≤ H) :
    k[centralizerOf P] →ₐ[k] k[H] :=
  MonoidAlgebra.mapDomainAlgHom k k (Subgroup.inclusion hCH)

private noncomputable def centralBrauerMapToRaw
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H) :
    GroupAlgebraCenter k G →ₐ[k] k[H] :=
  (centralizerAlgebraMapTo (k := k) P H hCH).comp
    ((Subalgebra.val (GroupAlgebraCenter k (centralizerOf P))).comp
      (centralBrauerMap (k := k) (p := p) P hP))

omit [Finite G] in
private theorem normalizer_le_normalizer_centralizerOf
    (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (centralizerOf P : Set G) := by
  let _ :
      ((centralizerOf P).subgroupOf
        (Subgroup.normalizer (P : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (P : Set G)
  exact Subgroup.le_normalizer_of_normal_subgroupOf
    (Subgroup.centralizer_le_normalizer (P : Set G))

private theorem centralBrauerMapToRaw_coeff
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (z : GroupAlgebraCenter k G) (h : H) :
    (centralBrauerMapToRaw (k := k) (p := p) P H hP hCH z).coeff h =
      if (h : G) ∈ centralizerOf P then
        (z : k[G]).coeff (h : G)
      else 0 := by
  classical
  by_cases hc : (h : G) ∈ centralizerOf P
  · simp only [if_pos hc]
    let c : centralizerOf P := ⟨(h : G), hc⟩
    have hinc : Subgroup.inclusion hCH c = h := by
      apply Subtype.ext
      rfl
    change
      Finsupp.mapDomain (Subgroup.inclusion hCH)
          (((centralBrauerMap (k := k) (p := p) P hP z :
            GroupAlgebraCenter k (centralizerOf P)) :
              k[centralizerOf P])).coeff h =
        (z : k[G]).coeff (h : G)
    rw [← hinc, Finsupp.mapDomain_apply
      (Subgroup.inclusion_injective hCH)]
    exact centralBrauerRestriction_coeff (k := k) P z c
  · simp only [if_neg hc]
    have hrange : h ∉ Set.range (Subgroup.inclusion hCH) := by
      rintro ⟨c, rfl⟩
      exact hc c.property
    change
      Finsupp.mapDomain (Subgroup.inclusion hCH)
          (((centralBrauerMap (k := k) (p := p) P hP z :
            GroupAlgebraCenter k (centralizerOf P)) :
              k[centralizerOf P])).coeff h = 0
    exact Finsupp.mapDomain_of_notMem_range _ _ hrange

private theorem centralBrauerMapToRaw_coeff_conjugate
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (z : GroupAlgebraCenter k G) (h x : H) :
    (centralBrauerMapToRaw (k := k) (p := p) P H hP hCH z).coeff
        (h * x * h⁻¹) =
      (centralBrauerMapToRaw (k := k) (p := p) P H hP hCH z).coeff x := by
  have hHC : H ≤ Subgroup.normalizer (centralizerOf P : Set G) :=
    hHN.trans (normalizer_le_normalizer_centralizerOf P)
  have hmem :
      (x : G) ∈ centralizerOf P ↔
        (((h * x * h⁻¹ : H) : G) ∈ centralizerOf P) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (Subgroup.mem_normalizer_iff.mp (hHC h.property) (x : G))
  by_cases hx : (x : G) ∈ centralizerOf P
  · have hconj : ((h * x * h⁻¹ : H) : G) ∈ centralizerOf P :=
      hmem.mp hx
    calc
      (centralBrauerMapToRaw (k := k) (p := p) P H hP hCH z).coeff
          (h * x * h⁻¹) =
          (z : k[G]).coeff (((h * x * h⁻¹ : H) : G)) := by
            rw [centralBrauerMapToRaw_coeff, if_pos hconj]
      _ = (z : k[G]).coeff (x : G) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
          GroupAlgebraCenter.coeff_conjugate z (h : G) (x : G)
      _ = (centralBrauerMapToRaw
          (k := k) (p := p) P H hP hCH z).coeff x := by
        rw [centralBrauerMapToRaw_coeff, if_pos hx]
  · have hconj : ((h * x * h⁻¹ : H) : G) ∉ centralizerOf P := by
      intro hconj
      exact hx (hmem.mpr hconj)
    calc
      (centralBrauerMapToRaw (k := k) (p := p) P H hP hCH z).coeff
          (h * x * h⁻¹) = 0 := by
            rw [centralBrauerMapToRaw_coeff, if_neg hconj]
      _ = (centralBrauerMapToRaw
          (k := k) (p := p) P H hP hCH z).coeff x := by
        rw [centralBrauerMapToRaw_coeff, if_neg hx]

private theorem centralBrauerMapToRaw_mem_center
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (z : GroupAlgebraCenter k G) :
    centralBrauerMapToRaw (k := k) (p := p) P H hP hCH z
      ∈ GroupAlgebraCenter k H := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [add_mul, mul_add, ha, hb]
  | single h r =>
      ext x
      have hc := centralBrauerMapToRaw_coeff_conjugate
        (k := k) (p := p) P H hP hCH hHN z h (h⁻¹ * x)
      simpa [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply, mul_assoc,
        inv_mul_cancel_left, mul_comm] using
        congrArg (fun a ↦ r * a) hc.symm

/-- The central Brauer map with target any subgroup in the interval
`C_G(P) ≤ H ≤ N_G(P)`. -/
noncomputable def centralBrauerMapTo
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) :
    GroupAlgebraCenter k G →ₐ[k] GroupAlgebraCenter k H :=
  (centralBrauerMapToRaw (k := k) (p := p) P H hP hCH).codRestrict
    (GroupAlgebraCenter k H)
    (fun z ↦ centralBrauerMapToRaw_mem_center
      (k := k) (p := p) P H hP hCH hHN z)

@[simp]
theorem centralBrauerMapTo_apply
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (z : GroupAlgebraCenter k G) :
    ((centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN z :
        GroupAlgebraCenter k H) : k[H]) =
      centralizerAlgebraMapTo (k := k) P H hCH
        (centralBrauerMap (k := k) (p := p) P hP z) :=
  rfl

/-- The canonical `H = N_G(P)` instance of `centralBrauerMapTo`. -/
noncomputable def normalizerCentralBrauerMap
    (P : Subgroup G) (hP : IsPGroup p P) :
    GroupAlgebraCenter k G →ₐ[k]
      GroupAlgebraCenter k (Subgroup.normalizer (P : Set G)) :=
  centralBrauerMapTo (k := k) (p := p) P
    (Subgroup.normalizer (P : Set G)) hP
    (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
