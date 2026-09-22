import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks
import ModularRep.PaperProofs.TypeBCentralKernelWeightBlockTransport
import ModularRep.PaperProofs.TypeBCentralKernelLocalReduction
import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily
import ModularRep.BrauerCharacterCommonRootCompatibility

/-!
# Binding the specified normalizer blocks for a central prime kernel

The quotient normalizer map is the actual `normalizerMap`. Its primitive
block image is derived from the central-kernel theorem on its kernel and the
canonical first isomorphism. The same affording representation identifies
the image block with the block of the descended Brauer character.

Both local reductions are constructed from Navarro 3.18 on the ordinary
characters already related by the checked local quotient equivalence. Their
normalizer roots come from one downstairs quotient root. The only remaining
root data are the displayed agreements with the two fixed global modular
systems. The existing guarded local block laws are applied at these roots.
No normalizer block-image equality, ambient block matching, or weight
correspondence is an external premise of the final theorem.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelLocalBlockBinding

open CharacterWeight FDRepSimpleClassKZero
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelWeightTransport TypeBCentralKernelWeightBlockTransport
open TypeBCentralKernelLocalReduction TypeBFixedRootDefinitionFamily

universe u

section Surjection

variable {p : ℕ} {k K X Y : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X] [Group Y] [Finite Y]

/-- The canonical first isomorphism factors the literal group algebra map. -/
theorem quotient_algebra_factor (f : X →* Y) (hf : Function.Surjective f)
    (b : k[X]) :
    MonoidAlgebra.domCongr k k (QuotientGroup.quotientKerEquivOfSurjective f hf)
        (quotientAlgebraMap f.ker b) = algebraMapOf f b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | single x a =>
    simp [quotientAlgebraMap, algebraMapOf,
      QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.quotientKerEquivOfRightInverse]
    rfl

/-- The published quotient statement applies to an arbitrary displayed
central prime-kernel surjection through its actual first isomorphism. -/
theorem primitive_image (f : X →* Y) (hf : Function.Surjective f)
    (hp : p.Prime) (hker : IsPGroup p f.ker)
    (central : f.ker ≤ Subgroup.center X)
    (source : NavarroCentralBlockPrinciple p k) (b : LiteralPrimitiveBlock k X) :
    IsPrimitiveCentralIdempotent (algebraMapOf f b.val) := by
  have h := (source X f.ker hp hker central).1 b
  have hmap := h.mapRingEquiv
    (MonoidAlgebra.domCongr k k
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).toRingEquiv
  change IsPrimitiveCentralIdempotent
    (MonoidAlgebra.domCongr k k (QuotientGroup.quotientKerEquivOfSurjective f hf)
      (quotientAlgebraMap f.ker b.val)) at hmap
  rw [quotient_algebra_factor] at hmap
  exact hmap

theorem algebra_action_map (f : X →* Y) {V : Type u}
    [AddCommGroup V] [Module k V] (rho : Representation k Y V) (b : k[X]) :
    (rho.pullback f).asAlgebraHom b = rho.asAlgebraHom (algebraMapOf f b) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | single x a => simp [algebraMapOf, Representation.asAlgebraHom_single]

variable [Fintype (LiteralPrimitiveBlock k X)] [Fintype (LiteralPrimitiveBlock k Y)]

/-- Literal Brauer block transport is proved from the same affording
representation, rather than supplied as a local source conclusion. -/
theorem brauer_block_map (f : X →* Y) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (central : f.ker ≤ Subgroup.center X)
    (source : NavarroCentralBlockPrinciple p k)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (DX : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k X => b.val))
    (DY : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k Y => b.val))
    (phiX : IBr iotaX) (phiY : IBr iotaY)
    (roots : iotaX.lift = iotaY.lift)
    (values : phiX.val = PrimeRegularClassFunction.pullback f phiY.val) :
    algebraMapOf f (block iotaX DX phiX).val = (block iotaY DY phiY).val := by
  obtain ⟨V, hV, hchar⟩ := phiY.property
  let rho : Representation k X V := Representation.pullback V.ρ f
  have hrho : Representation.IsIrreducible rho := hV.pullback f hf
  have hcharX : phiX.val = Representation.brauerCharacterOfRootEmbedding rho iotaX := by
    rw [values, hchar]
    exact (Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
      V.ρ iotaY iotaX f roots).symm
  letI : IsSimpleModule k[X] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hrho
  have hblock : block iotaX DX phiX = DX.moduleBlock (V := rho.asModule) :=
    block_of_affording iotaX DX phiX (FDRep.of rho) hrho hcharX
  have hsupp : rho.asAlgebraHom (block iotaX DX phiX).val = 1 := by
    rw [hblock]
    apply LinearMap.ext
    intro v
    change rho.asAlgebraHom (DX.moduleBlock (V := rho.asModule)).val v = v
    have hs := DX.moduleBlock_smul (V := rho.asModule) (rho.asModuleEquiv.symm v)
    have heq := congrArg rho.asModuleEquiv hs
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using heq
  let imageBlock : LiteralPrimitiveBlock k Y :=
    ⟨algebraMapOf f (block iotaX DX phiX).val,
      primitive_image f hf iotaX.prime hker central source _⟩
  have hsupported : Supported iotaY imageBlock phiY := by
    refine ⟨V, hV, hchar, ?_⟩
    change Representation.asAlgebraHom V.ρ
      (algebraMapOf f (block iotaX DX phiX).val) = 1
    rw [← algebra_action_map]
    exact hsupp
  exact (congrArg Subtype.val
    ((supported_iff_block iotaY DY imageBlock phiY).mp hsupported)).symm

end Surjection

section Weights

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G]
variable (P : Subgroup G) [P.Normal] [Fintype (G ⧸ P)] (hP : IsPGroup p P)

include hP in
theorem quotient_kernel : IsPGroup p (QuotientGroup.mk' P).ker := by
  rw [QuotientGroup.ker_mk']
  exact hP

theorem normalizer_kernel_central (central : P ≤ Subgroup.center G)
    (W : CharacterWeight p K G) :
    (normalizerMap (QuotientGroup.mk' P) W.subgroup).ker ≤
      Subgroup.center (Subgroup.normalizer (W.subgroup : Set G)) := by
  intro x hx
  have hxq : QuotientGroup.mk' P (x : G) = 1 := congrArg Subtype.val hx
  have hxP : (x : G) ∈ P := by
    rw [← QuotientGroup.ker_mk' P]
    exact hxq
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (central hxP) (y : G)

variable
    (iotaU : PrimeRegularRootEmbedding p k K G)
    (iotaD : PrimeRegularRootEmbedding p k K (G ⧸ P))
    (OU : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G ⧸ P)
      (Block := LiteralPrimitiveBlock k (G ⧸ P)))

/-- One actual downstairs local root prescribes the upstairs local root by
the proved local quotient isomorphism. These guards retain precisely its
identification with the fixed ambient modular systems. They contain no
character, block map, or compatibility conclusion. -/
structure LocalRootData (W : CharacterWeight p K G) where
  quotientDown : PrimeRegularRootEmbedding p k K
    (NormalizerQuotient (weightDown P hP W).subgroup)
  up_agrees : NormalizerRootAgreement iotaU W.subgroup
    (normalizerRoot W (quotientDown.alongMulEquiv
      (localEquiv (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
        (quotient_kernel P hP) W).symm))
  down_agrees : NormalizerRootAgreement iotaD (weightDown P hP W).subgroup
    (normalizerRoot (weightDown P hP W) quotientDown)

/-- Application of the guarded local laws to separately exhibited actual
reductions. The character equation under qN is deduced from those reductions
and the checked transport of the same ordinary local character. -/
theorem normalizer_block_map_of_reductions
    (central : P ≤ Subgroup.center G) (blocks : NavarroCentralBlockPrinciple p k)
    (guardU : GuardedBlockCompatibility iotaU OU)
    (guardD : GuardedBlockCompatibility iotaD OD)
    (W : CharacterWeight p K G)
    (iotaNU : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (W.subgroup : Set G)))
    (iotaND : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer ((weightDown P hP W).subgroup : Set (G ⧸ P))))
    (phiU : IBr iotaNU) (phiD : IBr iotaND)
    (roots : iotaNU.lift = iotaND.lift)
    (agreeU : NormalizerRootAgreement iotaU W.subgroup iotaNU)
    (agreeD : NormalizerRootAgreement iotaD (weightDown P hP W).subgroup iotaND)
    (reduceU : NormalizerInflatedReduction W.subgroup W.localCharacter iotaNU phiU)
    (reduceD : NormalizerInflatedReduction (weightDown P hP W).subgroup
      (weightDown P hP W).localCharacter iotaND phiD) :
    algebraMapOf (normalizerMap (QuotientGroup.mk' P) W.subgroup)
        (ownNormalizerBlock OU W).val =
      (ownNormalizerBlock OD (weightDown P hP W)).val := by
  let q := QuotientGroup.mk' P
  let WD := weightDown P hP W
  let qN := normalizerMap q W.subgroup
  have hqN : Function.Surjective qN := normalizerMap_surjective q
    (QuotientGroup.mk'_surjective P) W.subgroup
    (kernel_le_radical q (quotient_kernel P hP) W)
  have hvalues : phiU.val = PrimeRegularClassFunction.pullback qN phiD.val := by
    ext x
    exact normalizer_reduction_quotient_square W q
      (QuotientGroup.mk'_surjective P) (quotient_kernel P hP)
      iotaNU iotaND phiU phiD reduceU reduceD x
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    (OU.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) WD.subgroup) :=
    (OD.inflatedNormalizerBlockData WD.subgroup).fintypeBlock
  have hU := guardU.normalizer_block_of_reduction W iotaNU phiU agreeU reduceU
  have hD := guardD.normalizer_block_of_reduction WD iotaND phiD agreeD reduceD
  change block iotaNU (OU.inflatedNormalizerBlockData W.subgroup).blocks phiU =
    ownNormalizerBlock OU W at hU
  change block iotaND (OD.inflatedNormalizerBlockData WD.subgroup).blocks phiD =
    ownNormalizerBlock OD WD at hD
  rw [← hU, ← hD]
  exact brauer_block_map
    (Y := Subgroup.normalizer (WD.subgroup : Set (G ⧸ P))) qN hqN
    (normalizerMap_ker_isPGroup q W.subgroup (quotient_kernel P hP))
    (normalizer_kernel_central P central W) blocks iotaNU iotaND
    (OU.inflatedNormalizerBlockData W.subgroup).blocks
    (OD.inflatedNormalizerBlockData WD.subgroup).blocks phiU phiD roots hvalues

/-- The remaining normalizer compatibility is now a deduction from the
central primitive theorem, Navarro 3.18, guarded specified local block laws,
and explicit roots. Neither of the two normalizer Brauer characters is
supplied by this interface: both are constructed from the same transported
ordinary weight. -/
theorem localNormalizerCompatibility [IsAlgClosed K]
    (central : P ≤ Subgroup.center G) (blocks : NavarroCentralBlockPrinciple p k)
    (reduction : Navarro318Certificate p k K)
    (guardU : GuardedBlockCompatibility iotaU OU)
    (guardD : GuardedBlockCompatibility iotaD OD)
    (rootData : ∀ W : CharacterWeight p K G, LocalRootData P hP iotaU iotaD W) :
    LocalNormalizerCompatibility P hP OU OD := by
  intro W
  let WD := weightDown P hP W
  let r := rootData W
  let iotaQD := r.quotientDown
  let e := localEquiv (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
    (quotient_kernel P hP) W
  let iotaQU := iotaQD.alongMulEquiv e.symm
  obtain ⟨phiU, reduceU⟩ := exists_normalizer_reduction W iotaQU reduction
  obtain ⟨phiD, reduceD⟩ := exists_normalizer_reduction WD iotaQD reduction
  have roots : (normalizerRoot W iotaQU).lift = (normalizerRoot WD iotaQD).lift := by
    ext z
    calc
      (normalizerRoot W iotaQU).lift z = iotaQU.lift z :=
        PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ z
      _ = iotaQD.lift z := iotaQD.alongMulEquiv_lift e.symm z
      _ = (normalizerRoot WD iotaQD).lift z :=
        (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ z).symm
  exact normalizer_block_map_of_reductions P hP iotaU iotaD OU OD central blocks
    guardU guardD W (normalizerRoot W iotaQU) (normalizerRoot WD iotaQD)
    phiU phiD roots r.up_agrees r.down_agrees reduceU reduceD

end Weights

section CanonicalRoots

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G]

/-- Restriction of the prescribed ambient root equivalence. -/
def subgroupRoot (iota : PrimeRegularRootEmbedding p k K G) (H : Subgroup G) :
    PrimeRegularRootEmbedding p k K H :=
  PrimeRegularRootEmbedding.ofCommonRoot iota.prime iota.toMulEquiv
    (by simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card H) p)

theorem subgroupRoot_agrees (iota : PrimeRegularRootEmbedding p k K G)
    (H : Subgroup G) (z : rootsOfUnity (primeRegularExponent p H) k) :
    (subgroupRoot iota H).lift (((z : kˣ) : k)) = iota.lift (((z : kˣ) : k)) := by
  let hdiv : primeRegularExponent p H ∣ primeRegularExponent p G :=
    Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card H) p
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion hdiv z
  calc
    (subgroupRoot iota H).lift (((z : kˣ) : k)) =
        (subgroupRoot iota H).liftRoot z := (subgroupRoot iota H).lift_coe z
    _ = iota.liftRoot included := rfl
    _ = iota.lift (((included : kˣ) : k)) := (iota.lift_coe included).symm
    _ = iota.lift (((z : kˣ) : k)) := rfl

/-- The local quotient root is transported from the actual normalizer
restriction using equality of prime regular exponents for its prime kernel. -/
def weightQuotientRoot (iota : PrimeRegularRootEmbedding p k K G)
    (W : CharacterWeight p K G) :
    PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup) :=
  PrimeRegularRootEmbeddingPQuotient.transport
    (subgroupRoot iota (Subgroup.normalizer (W.subgroup : Set G)))
    (PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq W.prime
      (normalizerKernel W) (normalizerKernel_isPGroup W)).symm

theorem normalizerRoot_weightQuotientRoot_agrees
    (iota : PrimeRegularRootEmbedding p k K G) (W : CharacterWeight p K G) :
    NormalizerRootAgreement iota W.subgroup
      (normalizerRoot W (weightQuotientRoot iota W)) := by
  intro z
  calc
    (normalizerRoot W (weightQuotientRoot iota W)).lift (((z : kˣ) : k)) =
        (weightQuotientRoot iota W).lift (((z : kˣ) : k)) :=
      PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ _
    _ = (subgroupRoot iota (Subgroup.normalizer (W.subgroup : Set G))).lift
        (((z : kˣ) : k)) := PrimeRegularRootEmbeddingPQuotient.transport_lift _ _ _
    _ = iota.lift (((z : kˣ) : k)) := subgroupRoot_agrees iota _ z

variable (P : Subgroup G) [P.Normal] [Fintype (G ⧸ P)] (hP : IsPGroup p P)
  (iotaD : PrimeRegularRootEmbedding p k K (G ⧸ P))

/-- The local root guards for the actual quotient application are proved;
they are not an additional source hypothesis. -/
def canonicalRootData (W : CharacterWeight p K G) :
    LocalRootData P hP (TypeBCentralKernelBrauerInflation.upRoot P hP iotaD) iotaD W where
  quotientDown := weightQuotientRoot iotaD (weightDown P hP W)
  down_agrees := normalizerRoot_weightQuotientRoot_agrees iotaD (weightDown P hP W)
  up_agrees := by
    let WD := weightDown P hP W
    let iotaQD := weightQuotientRoot iotaD WD
    let e := localEquiv (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
      (quotient_kernel P hP) W
    let iotaQU := iotaQD.alongMulEquiv e.symm
    have hNU : primeRegularExponent p (NormalizerQuotient W.subgroup) =
        primeRegularExponent p (Subgroup.normalizer (W.subgroup : Set G)) :=
      PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq W.prime
        (normalizerKernel W) (normalizerKernel_isPGroup W)
    have hND : primeRegularExponent p (NormalizerQuotient WD.subgroup) =
        primeRegularExponent p (Subgroup.normalizer (WD.subgroup : Set (G ⧸ P))) :=
      PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq WD.prime
        (normalizerKernel WD) (normalizerKernel_isPGroup WD)
    have hQ : primeRegularExponent p (NormalizerQuotient W.subgroup) =
        primeRegularExponent p (NormalizerQuotient WD.subgroup) :=
      congrArg (fun n : ℕ => ordCompl[p] n) (Nat.card_congr e.toEquiv)
    have hN := hNU.symm.trans (hQ.trans hND)
    intro z
    let zD : rootsOfUnity
        (primeRegularExponent p (Subgroup.normalizer (WD.subgroup : Set (G ⧸ P)))) k :=
      ⟨z.val, by change z.val ^ _ = 1; rw [← hN]; exact z.property⟩
    change (normalizerRoot W iotaQU).lift (((z : kˣ) : k)) = _
    calc
      (normalizerRoot W iotaQU).lift (((z : kˣ) : k)) =
          iotaQU.lift (((z : kˣ) : k)) :=
        PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ _
      _ = iotaQD.lift (((z : kˣ) : k)) := iotaQD.alongMulEquiv_lift e.symm _
      _ = (normalizerRoot WD iotaQD).lift (((z : kˣ) : k)) :=
        (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift _ _ _ _).symm
      _ = iotaD.lift (((z : kˣ) : k)) :=
        normalizerRoot_weightQuotientRoot_agrees iotaD WD zD
      _ = (TypeBCentralKernelBrauerInflation.upRoot P hP iotaD).lift
          (((z : kˣ) : k)) :=
        (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift P hP iotaD _).symm

/-- Source-instantiated specified normalizer compatibility on the prescribed
quotient root and its canonical upstairs root. Every local carrier, root,
ordinary character, reduction and algebra map is now constructed. The only
external inputs are the cited uniform routine theorems and the two existing
guarded specified local-block laws for this modular system. -/
theorem localNormalizerCompatibility_canonicalRoots [IsAlgClosed K]
    (OU : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
    (OD : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G ⧸ P)
      (Block := LiteralPrimitiveBlock k (G ⧸ P)))
    (central : P ≤ Subgroup.center G) (blocks : NavarroCentralBlockPrinciple p k)
    (reduction : Navarro318Certificate p k K)
    (guardU : GuardedBlockCompatibility
      (TypeBCentralKernelBrauerInflation.upRoot P hP iotaD) OU)
    (guardD : GuardedBlockCompatibility iotaD OD) :
    LocalNormalizerCompatibility P hP OU OD :=
  localNormalizerCompatibility P hP (TypeBCentralKernelBrauerInflation.upRoot P hP iotaD)
    iotaD OU OD central blocks reduction guardU guardD (canonicalRootData P hP iotaD)

end CanonicalRoots

end ModularRep.PaperProofs.TypeBCentralKernelLocalBlockBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
