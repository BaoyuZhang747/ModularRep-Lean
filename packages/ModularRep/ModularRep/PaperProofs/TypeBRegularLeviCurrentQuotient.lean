import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers

/-!
# The direct quotient and field deduction in the current regular-Levi lemma

Manuscript inference: `lem:type-b-regular-levi-orbits`, numbered clause (3),
with the source boundary and geometric carriers specified below.
The carriers below are the existing literal geometric subgroups and their
fixed points: L0 = [Lbar,Lbar]^F, L = Lbar^F, M = (Lbar Z(A))^F.

E1 source boundary: A is the point group of the chosen regular overgroup;
Gbar and Lbar are the same actual geometric original group and Levi, with
Lbar <= Gbar and F-stable Lbar. In odd defining characteristic the actual
geometric centre of the simply connected type B group Gbar has order two
(Malle--Testerman, Proposition 9.15 and Table 9.2, pp. 71--72).
The point Frobenius is bijective; no inverse algebraic morphism is asserted.
Identifying the subgroup commutator with algebraic derived points retains
the existing point-carrier source boundary.

For a specified field endomorphism sigma, only point injectivity, its
literal commutation with F, forward preservation of Lbar and of Z(A), and
finiteness of A^F are used. These are the narrow standard point consequences
of the field source (Geck--Malle, Definition 1.4.1 and Section 1.4.5).
The finite fixed-point automorphism and every chain map equality are K.

K: extract x = a*z from membership in the actual geometric paired Levi;
derive a^-1*F(a) = z*F(z)^-1 in the actual centre of Gbar; use its order to
derive rationality of a^2 and z^2. This proves square membership in the
literal L C_M(L) and then the actual quotient exponent. Normal inclusions
and the abelian quotient are reused and joined in the final clause (3).
No ambient square covering, ambient quotient exponent, geometric paired
intersection, rational factorisation, quotient exponent, or finite field
action is an input. This is a point-source deduction for arbitrary regular
embeddings, not a specialization of all regular embeddings to Clifford.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRegularLeviCurrentQuotient

open scoped Pointwise commutatorElement
open TypeBRegularLeviRationalCarriers TypeBRegularLeviOrbitLemma46Relative

section DirectSquares

variable {A : Type*} [Group A]

/-- The geometric centre order is used only on an element of the actual
intersection Gbar with the ambient centre. -/
theorem central_intersection_square (Gbar : Subgroup A)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2)
    (t : A) (htG : t ∈ Gbar) (htZ : t ∈ Subgroup.center A) :
    t ^ 2 = 1 := by
  have central : (⟨t, htG⟩ : Gbar) ∈ Subgroup.center Gbar := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp htZ g.val
  let z : Subgroup.center Gbar := ⟨⟨t, htG⟩, central⟩
  have h := pow_card_eq_one' (x := z)
  rw [centreOrder] at h
  exact congrArg (fun u : Subgroup.center Gbar => u.val.val) h

/-- For the actual geometric factors of a rational paired-Levi element,
the Frobenius defect lies in Z(Gbar), and both factor squares are rational. -/
theorem factor_defect_and_squares (Frob : MulAut A) (Gbar Lbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2)
    (a z : A) (ha : a ∈ Lbar) (hz : z ∈ Subgroup.center A)
    (fixed : Frob (a * z) = a * z) :
    a⁻¹ * Frob a = z * (Frob z)⁻¹ ∧
      a⁻¹ * Frob a ∈ (Subgroup.center Gbar).map Gbar.subtype ∧
      (a⁻¹ * Frob a) ^ 2 = 1 ∧
      Frob (a ^ 2) = a ^ 2 ∧ Frob (z ^ 2) = z ^ 2 := by
  have hF : Frob a * Frob z = a * z := by
    simpa only [map_mul] using fixed
  let t := a⁻¹ * Frob a
  have htG : t ∈ Gbar :=
    levi_le_original (Lbar.mul_mem (Lbar.inv_mem ha) (levi_stable a ha))
  have htEq : t = z * (Frob z)⁻¹ := by
    calc
      t = a⁻¹ * (Frob a * Frob z) * (Frob z)⁻¹ := by dsimp [t]; group
      _ = a⁻¹ * (a * z) * (Frob z)⁻¹ := by rw [hF]
      _ = z * (Frob z)⁻¹ := by group
  have hFz : Frob z ∈ Subgroup.center A := by
    have h := Subgroup.mem_map_of_mem Frob.toMonoidHom hz
    rw [automorphism_center_map] at h
    exact h
  have htZ : t ∈ Subgroup.center A := by
    rw [htEq]
    exact (Subgroup.center A).mul_mem hz ((Subgroup.center A).inv_mem hFz)
  have htOriginal : (⟨t, htG⟩ : Gbar) ∈ Subgroup.center Gbar := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp htZ g.val
  have htTwo : t ^ 2 = 1 := central_intersection_square Gbar centreOrder t htG htZ
  have hFa : Frob a = a * t := by dsimp [t]; group
  have hFzEq : Frob z = t⁻¹ * z := by rw [htEq]; group
  have hat : Commute a t := Subgroup.mem_center_iff.mp htZ a
  have htz : Commute t⁻¹ z :=
    (Subgroup.mem_center_iff.mp ((Subgroup.center A).inv_mem htZ) z).symm
  have haFixed : Frob (a ^ 2) = a ^ 2 := by
    rw [map_pow, hFa, hat.mul_pow, htTwo, mul_one]
  have hzFixed : Frob (z ^ 2) = z ^ 2 := by
    rw [map_pow, hFzEq, htz.mul_pow]
    simp only [inv_pow, htTwo, inv_one, one_mul]
  exact ⟨htEq, ⟨⟨t, htG⟩, htOriginal, rfl⟩, htTwo, haFixed, hzFixed⟩

/-- Square factorisation is derived locally from x in (Lbar Z(A))^F;
the two returned factors are genuine rational Levi and geometric-centre points. -/
theorem rational_square_factors (Frob : MulAut A) (Gbar Lbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2)
    (x : M Frob.toMonoidHom Lbar) :
    ∃ a : L Frob.toMonoidHom Lbar,
      ∃ z : rationalSubgroup Frob.toMonoidHom (Subgroup.center A),
        x.val ^ 2 = a.val * z.val := by
  have hx : x.val.val ∈ (Lbar : Set A) * (Subgroup.center A : Set A) := by
    rw [← Subgroup.mul_normal]
    exact x.property
  obtain ⟨a, ha, z, hz, hax⟩ := hx
  change a * z = x.val.val at hax
  have fixed : Frob (a * z) = a * z := by
    rw [hax]
    exact x.val.property
  obtain ⟨_, _, _, haFixed, hzFixed⟩ :=
    factor_defect_and_squares Frob Gbar Lbar levi_le_original levi_stable
      centreOrder a z ha hz fixed
  refine ⟨⟨⟨a ^ 2, haFixed⟩, Lbar.pow_mem ha 2⟩,
    ⟨⟨z ^ 2, hzFixed⟩, (Subgroup.center A).pow_mem hz 2⟩, ?_⟩
  apply Subtype.ext
  change x.val.val ^ 2 = a ^ 2 * z ^ 2
  rw [← hax]
  exact (show Commute a z from Subgroup.mem_center_iff.mp hz a).mul_pow 2

/-- Both rational square factors lie in the literal L C_M(L). -/
theorem square_mem_literal_effectiveKernel (Frob : MulAut A) (Gbar Lbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2)
    (x : M Frob.toMonoidHom Lbar) :
    x ^ 2 ∈ effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) := by
  obtain ⟨a, z, hx⟩ := rational_square_factors Frob Gbar Lbar
    levi_le_original levi_stable centreOrder x
  let aM : M Frob.toMonoidHom Lbar :=
    ⟨a.val, L_le_M Frob.toMonoidHom Lbar a.property⟩
  let zM : M Frob.toMonoidHom Lbar :=
    ⟨z.val, rationalSubgroup_mono Frob.toMonoidHom (center_le_paired Lbar) z.property⟩
  have ha : aM ∈ effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) := by
    apply (show (L Frob.toMonoidHom Lbar).comap (M Frob.toMonoidHom Lbar).subtype ≤
      effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) from le_sup_left)
    exact a.property
  have hz : zM ∈ effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) := by
    apply (show (Subgroup.centralizer (L Frob.toMonoidHom Lbar : Set (fixedPoints Frob.toMonoidHom))).comap
      (M Frob.toMonoidHom Lbar).subtype ≤
      effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) from le_sup_right)
    exact Subgroup.center_le_centralizer _ (rational_center_le_center Frob.toMonoidHom z.property)
  have hxM : x ^ 2 = aM * zM := Subtype.ext hx
  rw [hxM]
  exact (effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar)).mul_mem ha hz

/-- The current direct square proof on the exact rational effective quotient. -/
theorem local_effective_quotient_exponent_two (Frob : MulAut A) (Gbar Lbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2) :
    letI := effectiveKernel_normal_of_le_normalizer
      (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) (L_le_M Frob.toMonoidHom Lbar)
      (rational_le_normalizer Frob.toMonoidHom (pairedLevi Lbar) Lbar
        (paired_le_Levi_normalizer Lbar))
    ∀ q : M Frob.toMonoidHom Lbar ⧸
      effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar), q ^ 2 = 1 := by
  letI := effectiveKernel_normal_of_le_normalizer
    (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) (L_le_M Frob.toMonoidHom Lbar)
    (rational_le_normalizer Frob.toMonoidHom (pairedLevi Lbar) Lbar
      (paired_le_Levi_normalizer Lbar))
  exact quotient_exponent_two_of_squares_mem _
    (square_mem_literal_effectiveKernel Frob Gbar Lbar levi_le_original levi_stable centreOrder)

end DirectSquares

section FieldEndomorphism

variable {A : Type*} [Group A]

/-- Restrict the specified endomorphism, before asserting it is an automorphism. -/
def fixedEndomorphism (Frob sigma : A →* A)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x)) :
    fixedPoints Frob →* fixedPoints Frob where
  toFun x := ⟨sigma x.val, (commutes x.val).trans (congrArg sigma x.property)⟩
  map_one' := Subtype.ext sigma.map_one
  map_mul' x y := Subtype.ext (sigma.map_mul x.val y.val)

theorem fixedEndomorphism_injective (Frob sigma : A →* A)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
    (injective : Function.Injective sigma) :
    Function.Injective (fixedEndomorphism Frob sigma commutes) := by
  intro x y h
  apply Subtype.ext
  exact injective (congrArg Subtype.val h)

/-- Point injectivity makes the induced map on the finite fixed group bijective. -/
def fixedPointAutomorphism (Frob sigma : A →* A)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
    (injective : Function.Injective sigma) [Finite (fixedPoints Frob)] :
    MulAut (fixedPoints Frob) :=
  MulEquiv.ofBijective (fixedEndomorphism Frob sigma commutes)
    ⟨fixedEndomorphism_injective Frob sigma commutes injective,
      Finite.surjective_of_injective (fixedEndomorphism_injective Frob sigma commutes injective)⟩

@[simp] theorem fixedPointAutomorphism_value (Frob sigma : A →* A)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
    (injective : Function.Injective sigma) [Finite (fixedPoints Frob)]
    (x : fixedPoints Frob) :
    (fixedPointAutomorphism Frob sigma commutes injective x).val = sigma x.val := rfl

/-- Forward geometric preservation gives setwise preservation of the finite
rational subgroup; inverse geometric preservation is not an input. -/
theorem fixedPointAutomorphism_preserves (Frob sigma : A →* A)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
    (injective : Function.Injective sigma) [Finite (fixedPoints Frob)]
    (U : Subgroup A) (stable : ∀ x ∈ U, sigma x ∈ U) :
    (rationalSubgroup Frob U).map (fixedPointAutomorphism Frob sigma commutes injective).toMonoidHom =
      rationalSubgroup Frob U := by
  let fU : rationalSubgroup Frob U → rationalSubgroup Frob U :=
    fun x => ⟨fixedEndomorphism Frob sigma commutes x.val, stable x.val.val x.property⟩
  have fU_injective : Function.Injective fU := by
    intro x y h
    apply Subtype.ext
    exact fixedEndomorphism_injective Frob sigma commutes injective (congrArg Subtype.val h)
  have fU_surjective := Finite.surjective_of_injective fU_injective
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact stable x.val hx
  · intro x hx
    obtain ⟨y, hy⟩ := fU_surjective ⟨x, hx⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩

/-- The same constructed finite automorphism preserves the entire chain. -/
theorem endomorphism_preserves_chain (Frob sigma : A →* A)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
    (injective : Function.Injective sigma) [Finite (fixedPoints Frob)]
    (Lbar : Subgroup A) (levi_stable : ∀ x ∈ Lbar, sigma x ∈ Lbar)
    (centre_stable : ∀ z ∈ Subgroup.center A, sigma z ∈ Subgroup.center A) :
    (L0 Frob Lbar).map (fixedPointAutomorphism Frob sigma commutes injective).toMonoidHom = L0 Frob Lbar ∧
      (L Frob Lbar).map (fixedPointAutomorphism Frob sigma commutes injective).toMonoidHom = L Frob Lbar ∧
      (M Frob Lbar).map (fixedPointAutomorphism Frob sigma commutes injective).toMonoidHom = M Frob Lbar := by
  have hL : Lbar.map sigma ≤ Lbar := by
    rintro y ⟨x, hx, rfl⟩
    exact levi_stable x hx
  have hZ : (Subgroup.center A).map sigma ≤ Subgroup.center A := by
    rintro y ⟨x, hx, rfl⟩
    exact centre_stable x hx
  have hD : (derivedLevi Lbar).map sigma ≤ derivedLevi Lbar := by
    change (⁅Lbar, Lbar⁆ : Subgroup A).map sigma ≤ ⁅Lbar, Lbar⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hL hL
  have hM : (pairedLevi Lbar).map sigma ≤ pairedLevi Lbar := by
    change (Lbar ⊔ Subgroup.center A).map sigma ≤ Lbar ⊔ Subgroup.center A
    rw [Subgroup.map_sup]
    exact sup_le_sup hL hZ
  exact ⟨fixedPointAutomorphism_preserves Frob sigma commutes injective (derivedLevi Lbar)
      (fun x hx => hD (Subgroup.mem_map_of_mem sigma hx)),
    fixedPointAutomorphism_preserves Frob sigma commutes injective Lbar levi_stable,
    fixedPointAutomorphism_preserves Frob sigma commutes injective (pairedLevi Lbar)
      (fun x hx => hM (Subgroup.mem_map_of_mem sigma hx))⟩

end FieldEndomorphism

/-- Full current numbered clause (3), on the same original rational groups:
normal inclusions, abelian quotient, direct effective exponent, and the
literal finite automorphism induced by the specified field endomorphism. -/
theorem regular_levi_clause_three {A : Type*} [Group A]
    (Frob : MulAut A) (Gbar Lbar : Subgroup A)
    (levi_le_original : Lbar ≤ Gbar)
    (levi_stable : ∀ a ∈ Lbar, Frob a ∈ Lbar)
    (centreOrder : Nat.card (Subgroup.center Gbar) = 2)
    (sigma : A →* A) (injective : Function.Injective sigma)
    (commutes : ∀ x, Frob (sigma x) = sigma (Frob x))
    (sigma_levi : ∀ a ∈ Lbar, sigma a ∈ Lbar)
    (sigma_centre : ∀ z ∈ Subgroup.center A, sigma z ∈ Subgroup.center A)
    [Finite (fixedPoints Frob.toMonoidHom)] :
    L0 Frob.toMonoidHom Lbar ≤ L Frob.toMonoidHom Lbar ∧
      L Frob.toMonoidHom Lbar ≤ M Frob.toMonoidHom Lbar ∧
      ((L0 Frob.toMonoidHom Lbar).subgroupOf (L Frob.toMonoidHom Lbar)).Normal ∧
      ((L Frob.toMonoidHom Lbar).subgroupOf (M Frob.toMonoidHom Lbar)).Normal ∧
      (letI := L0_normal_M Frob.toMonoidHom Lbar
       IsMulCommutative (M Frob.toMonoidHom Lbar ⧸
         (L0 Frob.toMonoidHom Lbar).subgroupOf (M Frob.toMonoidHom Lbar))) ∧
      (letI := effectiveKernel_normal_of_le_normalizer
         (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar) (L_le_M Frob.toMonoidHom Lbar)
         (rational_le_normalizer Frob.toMonoidHom (pairedLevi Lbar) Lbar
           (paired_le_Levi_normalizer Lbar))
       ∀ q : M Frob.toMonoidHom Lbar ⧸
         effectiveKernel (M Frob.toMonoidHom Lbar) (L Frob.toMonoidHom Lbar), q ^ 2 = 1) ∧
      (∀ x : fixedPoints Frob.toMonoidHom,
        (fixedPointAutomorphism Frob.toMonoidHom sigma commutes injective x).val = sigma x.val) ∧
      (L0 Frob.toMonoidHom Lbar).map
        (fixedPointAutomorphism Frob.toMonoidHom sigma commutes injective).toMonoidHom = L0 Frob.toMonoidHom Lbar ∧
      (L Frob.toMonoidHom Lbar).map
        (fixedPointAutomorphism Frob.toMonoidHom sigma commutes injective).toMonoidHom = L Frob.toMonoidHom Lbar ∧
      (M Frob.toMonoidHom Lbar).map
        (fixedPointAutomorphism Frob.toMonoidHom sigma commutes injective).toMonoidHom = M Frob.toMonoidHom Lbar := by
  obtain ⟨hL0, hL, hM⟩ := endomorphism_preserves_chain Frob.toMonoidHom sigma
    commutes injective Lbar sigma_levi sigma_centre
  exact ⟨L0_le_L Frob.toMonoidHom Lbar, L_le_M Frob.toMonoidHom Lbar,
    L0_normal_L Frob.toMonoidHom Lbar, L_normal_M Frob.toMonoidHom Lbar,
    M_quotient_L0_abelian Frob.toMonoidHom Lbar,
    local_effective_quotient_exponent_two Frob Gbar Lbar levi_le_original levi_stable centreOrder,
    fixedPointAutomorphism_value Frob.toMonoidHom sigma commutes injective, hL0, hL, hM⟩

end ModularRep.PaperProofs.TypeBRegularLeviCurrentQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
