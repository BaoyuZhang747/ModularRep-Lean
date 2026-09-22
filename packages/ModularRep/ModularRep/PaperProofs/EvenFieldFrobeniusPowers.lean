import ModularRep.PaperProofs.EvenFieldSourceShaped

/-!
# Frobenius powers in the even-field argument

In manuscript Lemma 3.6 the defining endomorphism is `F' = F₂^[a]`
and every field automorphism under consideration is a power `F₂^[j]` of
the same standard Frobenius endomorphism.  This file derives their
commutation and the induced endomorphism of the finite fixed-point group.
The commutation is therefore no longer an independent application input.
-/

namespace ModularRep.PaperProofs.EvenFieldFrobeniusPowers

open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G : Type u} [Group G]

/-- The `n`-fold iterate of a group endomorphism, again regarded as a group
endomorphism.  The superscript here denotes functional iteration rather than
the pointwise power operation on homomorphisms. -/
def iterateMonoidHom (F₂ : G →* G) (n : ℕ) : G →* G where
  toFun := (F₂ : G → G)^[n]
  map_one' := iterate_map_one F₂ n
  map_mul' := iterate_map_mul F₂ n

@[simp]
theorem iterateMonoidHom_apply (F₂ : G →* G) (n : ℕ) (x : G) :
    iterateMonoidHom F₂ n x = (F₂ : G → G)^[n] x :=
  rfl

/-- Any two powers of the same Frobenius endomorphism commute. -/
theorem iterateMonoidHom_commute (F₂ : G →* G) (a j : ℕ) (x : G) :
    iterateMonoidHom F₂ a (iterateMonoidHom F₂ j x) =
      iterateMonoidHom F₂ j (iterateMonoidHom F₂ a x) := by
  exact (Function.Commute.iterate_iterate_self (F₂ : G → G) a j).eq x

/-- The `j`th Frobenius power restricts to the fixed points of the `a`th
power. -/
def fieldPowerOnFixedSubgroup (F₂ : G →* G) (a j : ℕ) :
    frobeniusFixedSubgroup (iterateMonoidHom F₂ a) →*
      frobeniusFixedSubgroup (iterateMonoidHom F₂ a) :=
  frobeniusFixedSubgroupHom (iterateMonoidHom F₂ a)
    (iterateMonoidHom F₂ j) (iterateMonoidHom_commute F₂ a j)

@[simp]
theorem fieldPowerOnFixedSubgroup_apply (F₂ : G →* G) (a j : ℕ)
    (x : frobeniusFixedSubgroup (iterateMonoidHom F₂ a)) :
    (fieldPowerOnFixedSubgroup F₂ a j x : G) =
      iterateMonoidHom F₂ j (x : G) :=
  rfl

/-- On the fixed-point subgroup, adding a multiple of the defining exponent
does not change the induced field power. -/
theorem fieldPowerOnFixedSubgroup_add_definingExponent
    (F₂ : G →* G) (a j : ℕ)
    (x : frobeniusFixedSubgroup (iterateMonoidHom F₂ a)) :
    fieldPowerOnFixedSubgroup F₂ a (j + a) x =
      fieldPowerOnFixedSubgroup F₂ a j x := by
  apply Subtype.ext
  change (F₂ : G → G)^[j + a] (x : G) = (F₂ : G → G)^[j] (x : G)
  rw [Function.iterate_add_apply]
  exact congrArg ((F₂ : G → G)^[j]) x.property

/-- Composition of two induced field powers is the field power whose
exponent is their sum. -/
theorem fieldPowerOnFixedSubgroup_add
    (F₂ : G →* G) (a i j : ℕ)
    (x : frobeniusFixedSubgroup (iterateMonoidHom F₂ a)) :
    fieldPowerOnFixedSubgroup F₂ a i
        (fieldPowerOnFixedSubgroup F₂ a j x) =
      fieldPowerOnFixedSubgroup F₂ a (i + j) x := by
  apply Subtype.ext
  change (F₂ : G → G)^[i] ((F₂ : G → G)^[j] (x : G)) =
    (F₂ : G → G)^[i + j] (x : G)
  exact (Function.iterate_add_apply (F₂ : G → G) i j (x : G)).symm

end ModularRep.PaperProofs.EvenFieldFrobeniusPowers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
