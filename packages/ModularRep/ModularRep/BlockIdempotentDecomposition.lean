import ModularRep.CentralCharacterBlockSector
import ModularRep.RepresentationCentralSupport

/-!
# Decompositions by block idempotents

A finite block decomposition is represented here by a complete orthogonal
family of primitive central idempotents.  This file proves that every simple
module belongs to a unique member of such a family and that, for a group
algebra, the central character sector of that member is the central character
of the module.

The existence of the block decomposition of a finite group algebra is not
proved here.  It can therefore be supplied by later block theory without
being hidden in the present interface.
-/

open scoped MonoidAlgebra

namespace ModularRep

/-- A finite complete orthogonal family of primitive central idempotents.
For a finite-dimensional algebra, its block idempotents are the intended
example. -/
structure BlockIdempotentDecomposition {A ι : Type*} [Ring A] [Fintype ι]
    (b : ι → A) : Prop where
  /-- The idempotents are central, pairwise orthogonal, and sum to one. -/
  complete : CompleteOrthogonalCentralIdempotents b
  /-- Every member of the family is primitive among central idempotents. -/
  primitive : ∀ i, IsPrimitiveCentralIdempotent (b i)

namespace BlockIdempotentDecomposition

section LiteralBlocks

variable {A ι : Type*} [Ring A] [Fintype ι]
variable {b : ι → A}

/-- An index in a complete block decomposition, regarded as its literal
primitive central idempotent. -/
def primitiveBlockOfIndex
    (D : BlockIdempotentDecomposition b) (i : ι) :
    {c : A // IsPrimitiveCentralIdempotent c} :=
  ⟨b i, D.primitive i⟩

@[simp]
theorem primitiveBlockOfIndex_val
    (D : BlockIdempotentDecomposition b) (i : ι) :
    (primitiveBlockOfIndex D i).1 = b i :=
  rfl

/-- Orthogonality and nonzeroness make the literal block map injective. -/
theorem primitiveBlockOfIndex_injective
    (D : BlockIdempotentDecomposition b) :
    Function.Injective (primitiveBlockOfIndex D) := by
  intro i j hij
  by_contra hne
  have hvalues : b i = b j := congrArg Subtype.val hij
  apply (D.primitive i).ne_zero
  calc
    b i = b i * b i := (D.primitive i).idempotent.eq.symm
    _ = b i * b j := by rw [hvalues]
    _ = 0 := D.complete.ortho hne

/-- Completeness and primitivity make the literal block map surjective onto
all primitive central idempotents. -/
theorem primitiveBlockOfIndex_surjective
    (D : BlockIdempotentDecomposition b) :
    Function.Surjective (primitiveBlockOfIndex D) := by
  intro actual
  let i : ι := actual.2.support D.complete
  refine ⟨i, Subtype.ext ?_⟩
  have hsupport : actual.1 * b i = actual.1 :=
    actual.2.mul_support D.complete
  have hzeroOrEqual :=
    (D.primitive i).eq_zero_or_eq_self actual.1
      actual.2.idempotent actual.2.central hsupport
  exact (hzeroOrEqual.resolve_left actual.2.ne_zero).symm

/-- A complete block decomposition indexes all literal primitive central
idempotents. -/
noncomputable def primitiveBlockEquiv
    (D : BlockIdempotentDecomposition b) :
    ι ≃ {c : A // IsPrimitiveCentralIdempotent c} :=
  Equiv.ofBijective (primitiveBlockOfIndex D)
    ⟨primitiveBlockOfIndex_injective D,
      primitiveBlockOfIndex_surjective D⟩

@[simp]
theorem primitiveBlockEquiv_apply
    (D : BlockIdempotentDecomposition b) (i : ι) :
    primitiveBlockEquiv D i = primitiveBlockOfIndex D i :=
  rfl

end LiteralBlocks

variable {A V ι : Type*} [Ring A] [Fintype ι]
variable [AddCommGroup V] [Module A V] [IsSimpleModule A V]
variable {b : ι → A}

/-- The unique block index supporting a simple module. -/
noncomputable def moduleBlock (D : BlockIdempotentDecomposition b) : ι :=
  D.complete.support (V := V)

/-- The selected block idempotent acts as the identity and every other block
idempotent acts as zero. -/
theorem moduleBlock_isSupport (D : BlockIdempotentDecomposition b) :
    CompleteOrthogonalCentralIdempotents.IsSupport
      (V := V) b (D.moduleBlock (V := V)) :=
  D.complete.support_isSupport (V := V)

@[simp]
theorem moduleBlock_smul (D : BlockIdempotentDecomposition b) (v : V) :
    b (D.moduleBlock (V := V)) • v = v :=
  (D.moduleBlock_isSupport (V := V)).1 v

theorem smul_eq_zero_of_ne_moduleBlock
    (D : BlockIdempotentDecomposition b) {i : ι}
    (hi : i ≠ D.moduleBlock (V := V)) (v : V) :
    b i • v = 0 :=
  (D.moduleBlock_isSupport (V := V)).2 i hi v

/-- A block index is determined by the property that its idempotent acts as
the identity on the simple module. -/
theorem moduleBlock_eq_of_smul_eq_self
    (D : BlockIdempotentDecomposition b) {i : ι}
    (hi : ∀ v : V, b i • v = v) :
    i = D.moduleBlock (V := V) := by
  apply D.complete.support_unique (V := V)
  refine ⟨hi, ?_⟩
  intro j hji v
  calc
    b j • v = b j • (b i • v) := by rw [hi]
    _ = (b j * b i) • v := by rw [mul_smul]
    _ = 0 := by rw [D.complete.ortho hji, zero_smul]

/-- Linearly equivalent simple modules have the same supporting block in a
fixed block-idempotent decomposition. -/
theorem moduleBlock_eq_of_linearEquiv
    {W : Type*} [AddCommGroup W] [Module A W] [IsSimpleModule A W]
    (D : BlockIdempotentDecomposition b) (e : V ≃ₗ[A] W) :
    D.moduleBlock (V := V) = D.moduleBlock (V := W) := by
  symm
  apply D.moduleBlock_eq_of_smul_eq_self (V := V)
  intro v
  apply e.injective
  calc
    e (b (D.moduleBlock (V := W)) • v) =
        b (D.moduleBlock (V := W)) • e v := e.map_smul _ _
    _ = e v := D.moduleBlock_smul (V := W) (e v)

variable {k G : Type*} [Field k] [Group G]

/-- The central character sector of one member of a block-idempotent
decomposition of a group algebra. -/
noncomputable def centralCharacterSector
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)] (i : ι) : Z →* kˣ :=
  (D.primitive i).centralCharacterSector Z hZ

theorem centralCharacterSector_isSector
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)] (i : ι) :
    IsCentralCharacterSector Z (b i) (D.centralCharacterSector Z hZ i) :=
  (D.primitive i).centralCharacterSector_isSector Z hZ

end BlockIdempotentDecomposition

end ModularRep

namespace Representation

open ModularRep

variable {k G V W ι : Type*} [Field k] [Group G] [Fintype ι]
variable [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The sector of the block supporting an irreducible representation is its
central character. -/
theorem moduleBlockSector_eq_centralCharacter
    (rho : Representation k G V) [rho.IsIrreducible]
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) :
    D.centralCharacterSector Z hZ
        (D.moduleBlock (V := rho.asModule)) =
      rho.centralCharacter Z hZ :=
  rho.primitiveCentralIdempotentSector_eq_centralCharacter Z hZ
    (D.primitive (D.moduleBlock (V := rho.asModule)))
    (D.moduleBlock_isSupport (V := rho.asModule)).1

/-- Two irreducible representations belonging to the same block in a fixed
block-idempotent decomposition have the same central character. -/
theorem centralCharacter_eq_of_moduleBlock_eq
    (rho : Representation k G V) [rho.IsIrreducible]
    (sigma : Representation k G W) [sigma.IsIrreducible]
    {b : ι → k[G]} (D : BlockIdempotentDecomposition b)
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G)
    (hblock : D.moduleBlock (V := rho.asModule) =
      D.moduleBlock (V := sigma.asModule)) :
    rho.centralCharacter Z hZ = sigma.centralCharacter Z hZ := by
  rw [← rho.moduleBlockSector_eq_centralCharacter D Z hZ,
    ← sigma.moduleBlockSector_eq_centralCharacter D Z hZ, hblock]

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
