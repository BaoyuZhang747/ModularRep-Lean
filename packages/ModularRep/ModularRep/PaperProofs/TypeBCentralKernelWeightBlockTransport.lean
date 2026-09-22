import ModularRep.PaperProofs.TypeBCentralKernelWeightTransport
import ModularRep.PaperProofs.TypeBCentralKernelBlockSource
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.GroupAlgebraClassSums

/-!
# Specified block induction across a central ell-kernel

The only weight-dependent source join is equality of the actual normalizer
block idempotents under the quotient algebra map, for the local character
already transported by `TypeBCentralKernelWeightTransport`.  No ambient
weight-block equality or principal-weight equivalence is assumed.

Coefficient restriction commutes with a quotient on a saturated subgroup.
Block central character catalogues then identify the induced ambient block
by its value on a single specified idempotent.  Surjectivity on algebra
centres is neither assumed nor needed.

Source boundary: Navarro 3.18 (pp. 61--62), 3.3 (p. 50), 3.11
(pp. 55--56), and 3.13(b) (p. 58) authenticate the local reduction and its
literal normalizer block; 4.14 (pp. 87--88) supplies definedness of block
induction.  The central quotient primitive-block theorem is retained in
`TypeBCentralKernelBlockSource`.  All deductions below are kernel proofs.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelWeightBlockTransport

open CharacterWeight
open TypeBCentralKernelWeightTransport
open TypeBCentralKernelBlockSource

universe u

section Algebra

variable {k G H : Type u} [Field k] [Group G] [Group H]

/-- The group-basis algebra map for the displayed homomorphism. -/
def algebraMapOf (f : G →* H) : k[G] →ₐ[k] k[H] :=
  MonoidAlgebra.mapDomainAlgHom k k f

@[simp] theorem algebraMapOf_single (f : G →* H) (g : G) (a : k) :
    algebraMapOf f (MonoidAlgebra.single g a) = MonoidAlgebra.single (f g) a := by
  simp [algebraMapOf]

/-- A surjective group map carries central group algebra elements to
central elements.  This does not claim surjectivity on the centres. -/
def centerMap (f : G →* H) (hf : Function.Surjective f) :
    GroupAlgebraCenter k G →ₐ[k] GroupAlgebraCenter k H where
  toFun z := ⟨algebraMapOf f z.val, by
    rw [Subalgebra.mem_center_iff]
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, ha, hb]
    | single h a =>
      obtain ⟨g, rfl⟩ := hf h
      have hz := Subalgebra.mem_center_iff.mp z.property (MonoidAlgebra.single g a)
      simpa only [map_mul, algebraMapOf_single] using congrArg (algebraMapOf f) hz⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' a := Subtype.ext ((algebraMapOf f).commutes a)

@[simp] theorem centerMap_val (f : G →* H) (hf : Function.Surjective f)
    (z : GroupAlgebraCenter k G) :
    (centerMap f hf z).val = algebraMapOf f z.val := rfl

variable [Fintype G] [Fintype H]

/-- The coefficient-restriction square on a full subgroup preimage.  It
is proved on actual single group algebra terms before restricting to centres. -/
theorem coefficient_restriction_square
    (f : G →* H) (U : Subgroup G) (V : Subgroup H)
    (fU : U →* V) (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V) (z : k[G]) :
    algebraMapOf fU (coeffRestrict U z) =
      coeffRestrict V (algebraMapOf f z) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g a =>
    rw [algebraMapOf_single]
    by_cases hg : g ∈ U
    · have hfg : f g ∈ V := (saturated g).mp hg
      simp only [coeffRestrict_single, dif_pos hg, dif_pos hfg, algebraMapOf_single]
      congr 1
      exact Subtype.ext (square ⟨g, hg⟩)
    · have hfg : f g ∉ V := fun h => hg ((saturated g).mpr h)
      simp only [coeffRestrict_single, dif_neg hg, dif_neg hfg, map_zero]

theorem center_restriction_square
    (f : G →* H) (hf : Function.Surjective f)
    (U : Subgroup G) (V : Subgroup H)
    (fU : U →* V) (hfU : Function.Surjective fU)
    (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V)
    (z : GroupAlgebraCenter k G) :
    centerMap fU hfU (centerCoeffRestrict U z) =
      centerCoeffRestrict V (centerMap f hf z) := by
  apply Subtype.ext
  exact coefficient_restriction_square f U V fU square saturated z.val

end Algebra

section CentralCharacters

variable {k G H I J : Type u} [Field k] [IsAlgClosed k]
  [Group G] [Group H] [Fintype G] [Fintype H] [Fintype I] [Fintype J]
  {eG : I → k[G]} {eH : J → k[H]}
  {dG : BlockIdempotentDecomposition eG} {dH : BlockIdempotentDecomposition eH}

/-- Equality of the specified idempotents under q# forces the corresponding
central character pullback law.  Catalogue exhaustivity and delta suffice. -/
theorem centralCharacter_pullback
    (f : G →* H) (hf : Function.Surjective f)
    (cG : BlockCentralCharacterCatalogue dG)
    (cH : BlockCentralCharacterCatalogue dH)
    (b : I) (c : J) (physical : algebraMapOf f (eG b) = eH c)
    (z : GroupAlgebraCenter k G) :
    cH.centralCharacter c (centerMap f hf z) = cG.centralCharacter b z := by
  let lambda := (cH.centralCharacter c).comp (centerMap f hf)
  obtain ⟨b', hb'⟩ := cG.exhaustive lambda
  have hcenter : centerMap f hf (dG.blockIdempotentInCenter b) =
      dH.blockIdempotentInCenter c := Subtype.ext physical
  have heq : b' = b := by
    by_contra hne
    have hv := congrArg (fun l : GroupAlgebraCenter k G →ₐ[k] k =>
      l (dG.blockIdempotentInCenter b)) hb'
    change cG.centralCharacter b' (dG.blockIdempotentInCenter b) =
      cH.centralCharacter c (centerMap f hf (dG.blockIdempotentInCenter b)) at hv
    rw [cG.centralCharacter_other hne, hcenter, cH.centralCharacter_own] at hv
    exact zero_ne_one hv
  subst b'
  exact (congrArg (fun l : GroupAlgebraCenter k G →ₐ[k] k => l z) hb').symm

end CentralCharacters

section Induction

variable {k G H BU BD LU LD : Type u} [Field k] [IsAlgClosed k]
  [Group G] [Group H] [Fintype G] [Fintype H]
  [Fintype BU] [Fintype BD] [Fintype LU] [Fintype LD]

variable (U : Subgroup G) (V : Subgroup H)
local instance : Fintype U := Fintype.ofFinite _
local instance : Fintype V := Fintype.ofFinite _

variable {eGU : BU → k[G]} {eHD : BD → k[H]}
  {eU : LU → k[U]} {eV : LD → k[V]}
  {dGU : BlockIdempotentDecomposition eGU} {dHD : BlockIdempotentDecomposition eHD}
  {dU : BlockIdempotentDecomposition eU} {dV : BlockIdempotentDecomposition eV}

/-- Block induction is transported using actual q# idempotent equalities.
The target induced function is evaluated at q#B, and its catalogue delta
law identifies the block.  No ambient-block matching is a source premise. -/
theorem blockInducesTo_map
    (f : G →* H) (hf : Function.Surjective f)
    (fU : U →* V) (hfU : Function.Surjective fU)
    (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V)
    (cGU : BlockCentralCharacterCatalogue dGU) (cHD : BlockCentralCharacterCatalogue dHD)
    (cU : BlockCentralCharacterCatalogue dU) (cV : BlockCentralCharacterCatalogue dV)
    (bU : LU) (bV : LD) (BU' : BU) (BD' : BD)
    (localPhysical : algebraMapOf fU (eU bU) = eV bV)
    (globalPhysical : algebraMapOf f (eGU BU') = eHD BD')
    (upInduces : BlockInducesTo U cU cGU bU BU')
    (downDefined : IsBlockInductionDefined V (cV.centralCharacter bV)) :
    BlockInducesTo V cV cHD bV BD' := by
  obtain ⟨hup, hequp⟩ := upInduces
  let B := inducedBlock V cV cHD bV downDefined
  have hcenter : centerMap f hf (dGU.blockIdempotentInCenter BU') =
      dHD.blockIdempotentInCenter BD' := Subtype.ext globalPhysical
  have hvalue : cHD.centralCharacter B (dHD.blockIdempotentInCenter BD') = 1 := by
    rw [inducedBlock_centralCharacter V cV cHD bV downDefined]
    change cV.centralCharacter bV
      (centerCoeffRestrict V (dHD.blockIdempotentInCenter BD')) = 1
    rw [← hcenter, ← center_restriction_square f hf U V fU hfU square saturated]
    rw [centralCharacter_pullback fU hfU cU cV bU bV localPhysical]
    change inducedCentralCharacter U (cU.centralCharacter bU) hup
      (dGU.blockIdempotentInCenter BU') = 1
    rw [hequp, cGU.centralCharacter_own]
  have hB : B = BD' := by
    by_contra hne
    rw [cHD.centralCharacter_other hne] at hvalue
    exact zero_ne_one hvalue
  rw [← hB]
  exact inducedBlock_spec V cV cHD bV downDefined

end Induction

section ActualWeights

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G]
variable (P : Subgroup G) [P.Normal] [Fintype (G ⧸ P)]
  (hP : IsPGroup p P)

include hP in
private theorem quotient_kernel : IsPGroup p (QuotientGroup.mk' P).ker := by
  rw [QuotientGroup.ker_mk']
  exact hP

/-- The same literal descended weight as in the proved weight equivalence. -/
abbrev weightDown (W : CharacterWeight p K G) : CharacterWeight p K (G ⧸ P) :=
  TypeBCentralKernelWeightTransport.descend (QuotientGroup.mk' P)
    (QuotientGroup.mk'_surjective P) (quotient_kernel P hP) W

/-- The specified normalizer block selected from the given ordinary local
character.  Its value belongs to the actual normalizer group algebra. -/
def ownNormalizerBlock
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
    (W : CharacterWeight p K G) : InflatedNormalizerBlock (k := k) W.subgroup :=
  O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

/-- Exact remaining local source join, before ambient block induction.
The normalizer homomorphism and both local ordinary characters are fixed
constructions.  Authentication uses guarded root-compatible reductions;
the unrestricted arbitrary-root normalizer law is not asserted here. -/
def LocalNormalizerCompatibility
    (OU : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G ⧸ P)
      (Block := LiteralPrimitiveBlock k (G ⧸ P))) : Prop :=
  ∀ W : CharacterWeight p K G,
    algebraMapOf (normalizerMap (QuotientGroup.mk' P) W.subgroup)
      (ownNormalizerBlock OU W).val =
        (ownNormalizerBlock OD (weightDown P hP W)).val

variable (central : P ≤ Subgroup.center G)
  (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ P))
  (blocks : NavarroCentralBlockPrinciple p k)

theorem rawWeightBlock_map
    (OU : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G ⧸ P)
      (Block := LiteralPrimitiveBlock k (G ⧸ P)))
    (upLiteral : ∀ b, OU.ambientBlockData.blockIdempotent b = b.val)
    (downLiteral : ∀ b, OD.ambientBlockData.blockIdempotent b = b.val)
    (localPhysical : LocalNormalizerCompatibility P hP OU OD)
    (W : CharacterWeight p K G) :
    OD.rawWeightBlock (weightDown P hP W) =
      blockEquiv P hP central iotaDown blocks (OU.rawWeightBlock W) := by
  let q := QuotientGroup.mk' P
  let WD := weightDown P hP W
  let U := Subgroup.normalizer (W.subgroup : Set G)
  let V := Subgroup.normalizer (WD.subgroup : Set (G ⧸ P))
  let qN : U →* V := normalizerMap q W.subgroup
  have hker : q.ker ≤ W.subgroup :=
    kernel_le_radical q (quotient_kernel P hP) W
  have hqN : Function.Surjective qN :=
    normalizerMap_surjective q (QuotientGroup.mk'_surjective P) W.subgroup hker
  have hNmap : U.map q = V :=
    map_normalizer_eq_of_surjective_of_ker_le q
      (QuotientGroup.mk'_surjective P) W.subgroup hker
  have hpreimage : V.comap q = U := by
    rw [← hNmap]
    exact Subgroup.comap_map_eq_self (hker.trans W.subgroup.le_normalizer)
  have saturated : ∀ g : G, g ∈ U ↔ q g ∈ V := by
    intro g
    change g ∈ U ↔ g ∈ V.comap q
    rw [hpreimage]
  letI : Fintype (LiteralPrimitiveBlock k G) := OU.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k (G ⧸ P)) := OD.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    (OU.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) WD.subgroup) :=
    (OD.inflatedNormalizerBlockData WD.subgroup).fintypeBlock
  have hup : BlockInducesTo U
      (OU.inflatedNormalizerBlockData W.subgroup).catalogue
      OU.ambientBlockData.catalogue (ownNormalizerBlock OU W)
      (OU.rawWeightBlock W) :=
    inducedBlock_spec U (OU.inflatedNormalizerBlockData W.subgroup).catalogue
      OU.ambientBlockData.catalogue (ownNormalizerBlock OU W) (OU.blockInductionDefined W)
  have hphysical : algebraMapOf q
      (OU.ambientBlockData.blockIdempotent (OU.rawWeightBlock W)) =
      OD.ambientBlockData.blockIdempotent
        (blockEquiv P hP central iotaDown blocks (OU.rawWeightBlock W)) := by
    rw [upLiteral, downLiteral]
    rfl
  have hdown := blockInducesTo_map U V q (QuotientGroup.mk'_surjective P)
    qN hqN (fun _ => rfl) saturated
    OU.ambientBlockData.catalogue OD.ambientBlockData.catalogue
    (OU.inflatedNormalizerBlockData W.subgroup).catalogue
    (OD.inflatedNormalizerBlockData WD.subgroup).catalogue
    (ownNormalizerBlock OU W) (ownNormalizerBlock OD WD)
    (OU.rawWeightBlock W)
    (blockEquiv P hP central iotaDown blocks (OU.rawWeightBlock W))
    (localPhysical W) hphysical hup (OD.blockInductionDefined WD)
  exact (eq_inducedBlock_of_blockInducesTo V
    (OD.inflatedNormalizerBlockData WD.subgroup).catalogue
    OD.ambientBlockData.catalogue (ownNormalizerBlock OD WD)
    (OD.blockInductionDefined WD) hdown).symm

variable
    (SU : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
    (SD : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G ⧸ P)
      (Block := LiteralPrimitiveBlock k (G ⧸ P)))
    (upLiteral : ∀ b, SU.operations.ambientBlockData.blockIdempotent b = b.val)
    (downLiteral : ∀ b, SD.operations.ambientBlockData.blockIdempotent b = b.val)
    (localPhysical : LocalNormalizerCompatibility P hP SU.operations SD.operations)

include upLiteral downLiteral localPhysical in
/-- The specified raw-block equality descends through local isomorphism and
ambient conjugacy to the existing actual weight-class map. -/
theorem weightBlock_map
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    SD.weightBlock (quotientConjugacyClassEquiv (K := K) P hP w) =
      blockEquiv P hP central iotaDown blocks (SU.weightBlock w) := by
  refine Quotient.inductionOn w ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W
  change SD.operations.rawWeightBlock (weightDown P hP W) =
    blockEquiv P hP central iotaDown blocks (SU.operations.rawWeightBlock W)
  exact rawWeightBlock_map P hP central iotaDown blocks
    SU.operations SD.operations upLiteral downLiteral localPhysical W

/-- Restriction to a specified block fibre is constructed only after the
normalizer and ambient block squares have been proved. -/
def weightBlockEquiv (b : LiteralPrimitiveBlock k G) :
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) //
      SU.weightBlock w = b} ≃
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G ⧸ P) //
      SD.weightBlock w = blockEquiv P hP central iotaDown blocks b} :=
  (quotientConjugacyClassEquiv (K := K) P hP).subtypeEquiv (by
    intro w
    rw [weightBlock_map P hP central iotaDown blocks SU SD
      upLiteral downLiteral localPhysical]
    exact (blockEquiv P hP central iotaDown blocks).injective.eq_iff.symm)

include central iotaDown blocks upLiteral downLiteral localPhysical in
theorem weightBlock_principal_iff
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    IsPrincipal (SD.weightBlock (quotientConjugacyClassEquiv (K := K) P hP w)) ↔
      IsPrincipal (SU.weightBlock w) := by
  rw [weightBlock_map P hP central iotaDown blocks SU SD
    upLiteral downLiteral localPhysical]
  exact blockEquiv_principal_iff P hP central iotaDown blocks (SU.weightBlock w)

/-- Principal weight fibres inherit the already proved actual equivalence.
Principal membership is tested by the trivial representation on the actual
primitive block; it is not an input matching predicate. -/
def principalWeightEquiv :
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) //
      IsPrincipal (SU.weightBlock w)} ≃
    {w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G ⧸ P) //
      IsPrincipal (SD.weightBlock w)} :=
  (quotientConjugacyClassEquiv (K := K) P hP).subtypeEquiv (fun w =>
    (weightBlock_principal_iff P hP central iotaDown blocks SU SD
      upLiteral downLiteral localPhysical w).symm)

end ActualWeights

end ModularRep.PaperProofs.TypeBCentralKernelWeightBlockTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
