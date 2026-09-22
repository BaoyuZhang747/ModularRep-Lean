import ModularRep.BlockIdempotentDecomposition
import ModularRep.CentralIdempotentBlockExpansion
import ModularRep.GroupAlgebraCentralBrauerMapTo

/-!
# Local block expansion of an interval central Brauer image

This file expands the interval central Brauer image of one raw ambient
primitive central idempotent in a separately supplied local primitive
idempotent family.  It proves only the canonical finite support, its exact
sum, its uniqueness as a finite index set, and the conditional equivalence
between nonzero image and nonempty support.
-/

open scoped BigOperators MonoidAlgebra

namespace ModularRep

noncomputable section

variable {p : Nat} {k G LocalBlock : Type*}
variable [Field k] [Group G] [Finite G] [Fact p.Prime] [CharP k p]
variable [Fintype LocalBlock]

private def ambientPrimitiveInCenter
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b}) :
    GroupAlgebraCenter k G :=
  ⟨B.1, by
    rw [Subalgebra.mem_center_iff]
    intro x
    exact (B.2.central.comm x).eq.symm⟩

/-- The raw local group algebra image of an ambient primitive central
idempotent under the interval central Brauer map. -/
noncomputable def centralBrauerMapToPrimitiveImage
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b}) : k[H] :=
  ((centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN
      (ambientPrimitiveInCenter B) : GroupAlgebraCenter k H) : k[H])

/-- The canonical local indices supporting the interval central Brauer
image. -/
noncomputable def centralBrauerMapToLocalSupport
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent) :
    Finset LocalBlock :=
  localBlocks.complete.centralIdempotentSupport
    (centralBrauerMapToPrimitiveImage P H hP hCH hHN B)

private theorem centralBrauerMapToPrimitiveImage_idempotent_central
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b}) :
    IsIdempotentElem (centralBrauerMapToPrimitiveImage P H hP hCH hHN B) ∧
      IsMulCentral (centralBrauerMapToPrimitiveImage P H hP hCH hHN B) := by
  let imageInCenter : GroupAlgebraCenter k H :=
    centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN
      (ambientPrimitiveInCenter B)
  have hAmbient :
      ambientPrimitiveInCenter B * ambientPrimitiveInCenter B =
        ambientPrimitiveInCenter B := by
    apply Subtype.ext
    exact B.2.idempotent.eq
  have hImage : imageInCenter * imageInCenter = imageInCenter := by
    calc
      imageInCenter * imageInCenter =
          centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN
            (ambientPrimitiveInCenter B * ambientPrimitiveInCenter B) := by
        exact (map_mul
          (centralBrauerMapTo (k := k) (p := p) P H hP hCH hHN)
          (ambientPrimitiveInCenter B) (ambientPrimitiveInCenter B)).symm
      _ = imageInCenter := by rw [hAmbient]
  refine ⟨?_, ?_⟩
  · change (imageInCenter : k[H]) * (imageInCenter : k[H]) =
      (imageInCenter : k[H])
    exact congrArg (fun z : GroupAlgebraCenter k H ↦ (z : k[H])) hImage
  · change IsMulCentral (imageInCenter : k[H])
    have hCenter := imageInCenter.property
    rw [Subalgebra.mem_center_iff] at hCenter
    refine ⟨fun x ↦ (hCenter x).symm, ?_, ?_⟩
    · intro x y
      exact (mul_assoc (imageInCenter : k[H]) x y).symm
    · intro x y
      exact mul_assoc x y (imageInCenter : k[H])

@[simp]
theorem mem_centralBrauerMapToLocalSupport
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (C : LocalBlock) :
    C ∈ centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks ↔
      localBlockIdempotent C *
          centralBrauerMapToPrimitiveImage P H hP hCH hHN B ≠ 0 := by
  simpa only [centralBrauerMapToLocalSupport] using
    localBlocks.complete.mem_centralIdempotentSupport
      (centralBrauerMapToPrimitiveImage P H hP hCH hHN B) C

/-- A local primitive idempotent is supported exactly when right
multiplication by the image fixes it. -/
theorem mem_centralBrauerMapToLocalSupport_iff_mul_eq_self
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (C : LocalBlock) :
    C ∈ centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks ↔
      localBlockIdempotent C *
          centralBrauerMapToPrimitiveImage P H hP hCH hHN B =
        localBlockIdempotent C := by
  obtain ⟨hIdempotent, hCentral⟩ :=
    centralBrauerMapToPrimitiveImage_idempotent_central
      P H hP hCH hHN B
  simpa only [centralBrauerMapToLocalSupport] using
    localBlocks.complete.mem_centralIdempotentSupport_iff_mul_eq_self
      localBlocks.primitive hIdempotent hCentral C

/-- A local primitive idempotent is supported exactly when left
multiplication by the image fixes it. -/
theorem mem_centralBrauerMapToLocalSupport_iff_left_mul_eq_self
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (C : LocalBlock) :
    C ∈ centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks ↔
      centralBrauerMapToPrimitiveImage P H hP hCH hHN B *
          localBlockIdempotent C =
        localBlockIdempotent C := by
  obtain ⟨hIdempotent, hCentral⟩ :=
    centralBrauerMapToPrimitiveImage_idempotent_central
      P H hP hCH hHN B
  simpa only [centralBrauerMapToLocalSupport] using
    localBlocks.complete.mem_centralIdempotentSupport_iff_left_mul_eq_self
      localBlocks.primitive hIdempotent hCentral C

/-- The sum of the supported local primitive idempotents is exactly the
interval central Brauer image. -/
theorem sum_centralBrauerMapToLocalSupport_eq
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent) :
    (∑ C ∈ centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks,
        localBlockIdempotent C) =
      centralBrauerMapToPrimitiveImage P H hP hCH hHN B := by
  obtain ⟨hIdempotent, hCentral⟩ :=
    centralBrauerMapToPrimitiveImage_idempotent_central
      P H hP hCH hHN B
  simpa only [centralBrauerMapToLocalSupport] using
    localBlocks.complete.sum_centralIdempotentSupport_eq
      localBlocks.primitive hIdempotent hCentral

/-- The support is the unique finite set of local indices whose family sum
is the interval central Brauer image. -/
theorem eq_centralBrauerMapToLocalSupport_of_sum_eq
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (s : Finset LocalBlock)
    (hs : (∑ C ∈ s, localBlockIdempotent C) =
      centralBrauerMapToPrimitiveImage P H hP hCH hHN B) :
    s = centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks := by
  obtain ⟨hIdempotent, hCentral⟩ :=
    centralBrauerMapToPrimitiveImage_idempotent_central
      P H hP hCH hHN B
  simpa only [centralBrauerMapToLocalSupport] using
    localBlocks.complete.eq_centralIdempotentSupport_of_sum_eq
      localBlocks.primitive hIdempotent hCentral s hs

/-- The image is nonzero exactly when its canonical local support is
nonempty.  This does not assert either condition unconditionally. -/
theorem centralBrauerMapToPrimitiveImage_ne_zero_iff_support_nonempty
    (P H : Subgroup G) (hP : IsPGroup p P)
    (hCH : centralizerOf P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : {b : k[G] // IsPrimitiveCentralIdempotent b})
    {localBlockIdempotent : LocalBlock → k[H]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent) :
    centralBrauerMapToPrimitiveImage P H hP hCH hHN B ≠ 0 ↔
      (centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks).Nonempty := by
  constructor
  · intro hImage
    by_contra hSupport
    have hEmpty :
        centralBrauerMapToLocalSupport P H hP hCH hHN B localBlocks = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hSupport
    have hSum := sum_centralBrauerMapToLocalSupport_eq
      P H hP hCH hHN B localBlocks
    rw [hEmpty, Finset.sum_empty] at hSum
    exact hImage hSum.symm
  · rintro ⟨C, hC⟩ hImage
    have hMul :
        localBlockIdempotent C *
            centralBrauerMapToPrimitiveImage P H hP hCH hHN B ≠ 0 :=
      (mem_centralBrauerMapToLocalSupport
        P H hP hCH hHN B localBlocks C).1 hC
    apply hMul
    rw [hImage, mul_zero]

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
