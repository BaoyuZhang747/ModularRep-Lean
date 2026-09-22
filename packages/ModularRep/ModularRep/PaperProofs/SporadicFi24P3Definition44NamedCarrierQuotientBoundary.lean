import ModularRep.CyclicExtension

/-!
# The next window: direct quotient descent is not character extension

An--Dietrich, p. 330 (verbatim extraction lines 323--324), associates an
obstruction class on `G/N` to an invariant Brauer character of `N`.
Definition 4.4(3d), p. 332, compares such classes. In contrast, the existing
`CyclicExtensionProjectiveModel` asks for an honest representation of the
quotient. Its current fields contain no association with the selected base
character. This file does not import that model or conclude clause (3d).

The precise direct-descent obstruction is elementary: an ambient extension
which factors through `G/N` has trivial restriction to `N`. The stored
restriction equivalence therefore forces the selected base representation
itself to be trivial. This is a diagnostic theorem, not a claim that the
intended obstruction classes are nontrivial or cannot be compared.
-/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBoundary

universe u

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (N : Subgroup G) [N.Normal] (rho : Representation k N V)

/-- Factoring an extension through the quotient forces its base to be trivial. -/
theorem base_trivial_of_extension_quotient_descent
    (E : Representation.Extension N rho)
    (sigma : Representation k (G ⧸ N) V)
    (hfactor : E.representation = sigma.pullback (QuotientGroup.mk' N)) :
    ∀ n : N, rho n = 1 := by
  intro n
  have hkill : E.representation (n : G) = 1 := by
    rw [hfactor]
    change sigma (QuotientGroup.mk' N (n : G)) = 1
    have hq : QuotientGroup.mk' N (n : G) = 1 := by
      exact (QuotientGroup.eq_one_iff _).mpr n.2
    rw [hq, map_one]
  ext v
  obtain ⟨w, rfl⟩ := E.restrictionEquiv.surjective v
  have h := E.map_restriction n w
  rw [hkill] at h
  exact h.symm

/-- A selected base with nonidentity action obstructs this direct extraction. -/
theorem nontrivial_base_prevents_quotient_descent
    (E : Representation.Extension N rho)
    (hbase : ∃ n : N, rho n ≠ 1) :
    ¬ ∃ sigma : Representation k (G ⧸ N) V,
      E.representation = sigma.pullback (QuotientGroup.mk' N) := by
  rintro ⟨sigma, hfactor⟩
  obtain ⟨n, hn⟩ := hbase
  exact hn (base_trivial_of_extension_quotient_descent N rho E sigma hfactor n)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBoundary


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
