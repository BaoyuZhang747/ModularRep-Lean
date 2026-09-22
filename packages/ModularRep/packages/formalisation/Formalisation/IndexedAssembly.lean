import Formalisation.FibreTransport

/-!
# Construction of equivariant fibre equivalences

This file formalises the general mechanism for combining bijections indexed by blocks,
central character sectors, or any other `A`-set.  Equivariant maps `pX : X → I` and
`pY : Y → I` divide the two total spaces into fibres over the same index set.  A family of
equivalences between corresponding fibres combines into an equivalence `X ≃ Y`.  If the
family commutes with transport by every element of `A`, the resulting equivalence is
`A`-equivariant.

The transport compatibility is an explicit hypothesis.  In applications it must be proved
from stabiliser equivariance on orbit representatives, or supplied by a construction such as
the one in `Formalisation.FibreTransport`.  Thus this module does not assume the desired global
equivalence or any representation theoretic bijection.
-/

namespace Formalisation

section IndexedAssembly

variable {A I X Y : Type*} [Group A]
variable [MulAction A I] [MulAction A X] [MulAction A Y]

/-- Reindex a fibre along an equality of indices.  The underlying element is unchanged. -/
def reindexFibre (p : X → I) {i j : I} (h : i = j) : Fibre p i ≃ Fibre p j where
  toFun x := ⟨x.1, x.2.trans h⟩
  invFun x := ⟨x.1, x.2.trans h.symm⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

@[simp]
theorem reindexFibre_coe (p : X → I) {i j : I} (h : i = j) (x : Fibre p i) :
    (reindexFibre p h x).1 = x.1 := by
  rfl

/-- A dependent family of fibre equivalences commutes with reindexing along an equality. -/
theorem fibreEquiv_reindex
    (pX : X → I) (pY : Y → I)
    (f : ∀ i : I, Fibre pX i ≃ Fibre pY i)
    {i j : I} (h : i = j) (x : Fibre pX i) :
    reindexFibre pY h (f i x) = f j (reindexFibre pX h x) := by
  cases h
  rfl

/-- Fibrewise equivalences that commute with transport by `A`. -/
structure EquivariantFibreEquiv
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y) where
  /-- The equivalence over each index. -/
  fibreEquiv : ∀ i : I, Fibre pX i ≃ Fibre pY i
  /-- Transporting to another fibre before applying its equivalence agrees with first applying
  the equivalence and then transporting. -/
  map_actFibre : ∀ (a : A) (i : I) (x : Fibre pX i),
    fibreEquiv (a • i) (actFibre pX hpX a i x) =
      actFibre pY hpY a i (fibreEquiv i x)

namespace EquivariantFibreEquiv

variable {pX : X → I} {pY : Y → I}
variable {hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x}
variable {hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y}

/-- If the index type has at most one element, an equivariant equivalence of
the total spaces restricts to an equivariant equivalence on every fibre. -/
def ofEquiv_of_subsingleton [Subsingleton I]
    (e : X ≃ Y)
    (he : ∀ (a : A) (x : X), e (a • x) = a • e x) :
    EquivariantFibreEquiv pX pY hpX hpY where
  fibreEquiv i :=
    { toFun := fun x => ⟨e x.1, Subsingleton.elim _ i⟩
      invFun := fun y => ⟨e.symm y.1, Subsingleton.elim _ i⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y.1 }
  map_actFibre a _i x := by
    apply Subtype.ext
    exact he a x.1

/-- Combine the indexed equivalences into one equivalence of the total spaces. -/
def assemble (f : EquivariantFibreEquiv pX pY hpX hpY) : X ≃ Y :=
  Equiv.ofFiberEquiv f.fibreEquiv

@[simp]
theorem assemble_apply (f : EquivariantFibreEquiv pX pY hpX hpY) (x : X) :
    f.assemble x = (f.fibreEquiv (pX x) ⟨x, rfl⟩).1 := by
  rfl

@[simp]
theorem assemble_symm_apply (f : EquivariantFibreEquiv pX pY hpX hpY) (y : Y) :
    f.assemble.symm y = ((f.fibreEquiv (pY y)).symm ⟨y, rfl⟩).1 := by
  rfl

/-- The resulting equivalence maps the fibre over `i` to the fibre over the same `i`. -/
theorem assemble_preserves_base (f : EquivariantFibreEquiv pX pY hpX hpY) (x : X) :
    pY (f.assemble x) = pX x :=
  Equiv.ofFiberEquiv_map f.fibreEquiv x

/-- The inverse resulting equivalence also preserves the base index. -/
theorem assemble_symm_preserves_base (f : EquivariantFibreEquiv pX pY hpX hpY) (y : Y) :
    pX (f.assemble.symm y) = pY y := by
  rw [assemble_symm_apply]
  exact ((f.fibreEquiv (pY y)).symm ⟨y, rfl⟩).2

/-- Transport compatibility of the fibre equivalences makes their construction `A`-equivariant. -/
theorem assemble_equivariant (f : EquivariantFibreEquiv pX pY hpX hpY)
    (a : A) (x : X) :
    f.assemble (a • x) = a • f.assemble x := by
  let z : Fibre pX (pX (a • x)) := ⟨a • x, rfl⟩
  let transported : Fibre pX (a • pX x) := actFibre pX hpX a (pX x) ⟨x, rfl⟩
  have hz : reindexFibre pX (hpX a x) z = transported := by
    apply Subtype.ext
    rfl
  have hreindex := fibreEquiv_reindex pX pY f.fibreEquiv (hpX a x) z
  have hleft : (f.fibreEquiv (pX (a • x)) z).1 =
      (f.fibreEquiv (a • pX x) transported).1 := by
    have := congrArg Subtype.val hreindex
    simpa [hz] using this
  have htransport := congrArg Subtype.val (f.map_actFibre a (pX x) ⟨x, rfl⟩)
  calc
    f.assemble (a • x) = (f.fibreEquiv (pX (a • x)) z).1 := rfl
    _ = (f.fibreEquiv (a • pX x) transported).1 := hleft
    _ = a • (f.fibreEquiv (pX x) ⟨x, rfl⟩).1 := by
      simpa [transported, actFibre] using htransport
    _ = a • f.assemble x := rfl

/-- Equivariance can equivalently be stated for the inverse construction. -/
theorem assemble_symm_equivariant (f : EquivariantFibreEquiv pX pY hpX hpY)
    (a : A) (y : Y) :
    f.assemble.symm (a • y) = a • f.assemble.symm y := by
  apply f.assemble.injective
  rw [Equiv.apply_symm_apply, f.assemble_equivariant, Equiv.apply_symm_apply]

end EquivariantFibreEquiv

end IndexedAssembly

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
