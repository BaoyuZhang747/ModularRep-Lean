import ModularRep.PaperProofs.TypeBCurrentBrauerSourceActions

/-!
# Proposition 4.13 on the actual Spin and special Clifford carriers

The source records retain the actual regular embedding, minimal proper Levi,
common roots, constituent geometry, and the published modular Jordan bijection.
They do not contain a representative, stabilizer equality, extension, or the
assumption of the Jordan reduction. Original type A/B2/Spin representatives,
component return, Clifford transfer, the diagonal quotient, full-field
promotion, cyclic extension and exhaustive orbit coverage are Lean deductions.

The external geometric boundary is Malle--Testerman, Theorems 21.7 and 22.5;
Ruhstorfer, Lemma 4.5(a)--(b); and Feng--Li--Zhang, Lemma 5.1, the proof
of Proposition 5.2, Proposition 5.6 and Theorem 5.7. The Jordan equivalence is
on the complete literal idempotent packets and retains its block correspondence.
Its source interpretation on these precise algebraic groups is an explicit U
identification, as are the common coefficient and root identifications.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis

open ModularRep FDRepSimpleClassKZero TypeBCliffordCarriers
open TypeBRegularLeviRationalCarriers TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLemma47LeviApplication
open TypeBCharacteristicTwoConstituentSource TypeBRankThreeJordanPacketCarriers
open TypeBCurrentBrauerTransport TypeBCurrentLeviAssembly
open TypeBCurrentJordanCliffordCarriers
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {n p f : ℕ} {F A k K : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field A] [Algebra F A]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {normF : NormSource n F} {normA : NormSource n A}
variable {parameters : OddFieldParameters F p f}
variable [Finite (SpecialClifford n F)] [NeZero f]
variable (fs : FieldActionSource n F p f parameters normF)
variable (iotaG : PrimeRegularRootEmbedding 2 k K (Spin n F normF))
variable {BG : Type} [Fintype BG] {bG : BG → k[Spin n F normF]}
variable (blocksG : BlockIdempotentDecomposition bG)
variable (parametersG : ParameterSource fs (k := k))
variable (Frob : MulAut (SpecialClifford n A))
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable (points : CliffordFixedPointSource n p f F A normF normA Frob)

namespace LeviSource

variable {fs iotaG blocksG parametersG Frob points}
variable {s : SemisimpleIndex (n := n) (p := p) (F := F)}
variable (source : LeviSource fs iotaG blocksG parametersG Frob points s)

/-- The same retained Levi character yields the ambient representative,
same-field-stabilizer equality and the prescribed literal block correspondence. -/
theorem selected_jordan
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k) :
    letI : Fintype source.BL := source.finiteBL
    ∀ (psi0 : Packet (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL),
    letI := ambientBrauerAction (H Frob source.Lbar) (rootH Frob source.Lbar source.iotaL)
    letI := ambientBrauerAction (N Frob source.Lbar) (rootN Frob source.Lbar source.iotaN)
    letI := fieldBrauerAction (H Frob source.Lbar) (rootH Frob source.Lbar source.iotaL)
      source.field.fieldOnGamma source.field.H_stable
    letI := fieldCharacters (fs := fs) (iotaG := iotaG) (parametersG := parametersG) (s := s)
    letI := diagonalAction iotaG
    ∃ (theta0 theta : IBr (rootN Frob source.Lbar source.iotaN))
      (y : Gamma Frob source.Lbar)
      (psi : Packet (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL),
      psi.val = y • psi0.val ∧ theta = y • theta0 ∧
      Occurs (H Frob source.Lbar) (N Frob source.Lbar) (N_le_H Frob source.Lbar)
        (rootH Frob source.Lbar source.iotaL) (rootN Frob source.Lbar source.iotaN) psi.val theta ∧
      source.jordanCharacter psi ∈ MulAction.orbit (SpecialClifford n F) (source.jordanCharacter psi0) ∧
      MulAction.stabilizer (parametersG.stabilizer s) (source.jordanCharacter psi) =
        MulAction.stabilizer (parametersG.stabilizer s) psi.val ∧
      supportingBlock iotaG blocksG (source.jordanCharacter psi) =
        (source.blockCorrespondence
          ⟨supportingBlock (rootH Frob source.Lbar source.iotaL) source.blocksL psi.val,
            psi.property⟩).val ∧
      Representative fs iotaG (source.jordanCharacter psi) := by
  letI : Fintype source.BL := source.finiteBL
  intro psi0
  letI := ambientBrauerAction (H Frob source.Lbar) (rootH Frob source.Lbar source.iotaL)
  letI := ambientBrauerAction (N Frob source.Lbar) (rootN Frob source.Lbar source.iotaN)
  letI := fieldBrauerAction (H Frob source.Lbar) (rootH Frob source.Lbar source.iotaL)
    source.field.fieldOnGamma source.field.H_stable
  letI := packetMulAction (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL
    (MulAut.conjNormal (H := H Frob source.Lbar)) source.gammaInvariant
  letI := packetMulAction (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL
    (restrictAutomorphismHom (H Frob source.Lbar) source.field.fieldOnGamma source.field.H_stable)
    source.fieldInvariant
  letI := diagonalAction iotaG
  letI := fieldAction fs iotaG
  letI := source.gammaCharacters
  letI := fieldCharacters (fs := fs) (iotaG := iotaG) (parametersG := parametersG) (s := s)
  obtain ⟨theta0, occurs0⟩ := source.constituent psi0
  obtain ⟨theta, y, psiH, hpsi, htheta, occurs, levi⟩ :=
    TypeBCurrentLeviAssembly.same_y_representative Frob source.Lbar source.leviStable source.field
      source.iotaL source.iotaN source.iotaGamma source.clifford psi0.val theta0 occurs0
      (source.components psi0 theta0 occurs0)
  have packet : InPacket (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL psiH := by
    rw [hpsi]
    exact inPacket_smul (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL
      (MulAut.conjNormal (H := H Frob source.Lbar)) source.gammaInvariant y psi0.val psi0.property
  let psi : Packet (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL := ⟨psiH, packet⟩
  have packetLevi : ProductStabilizerFactorization (D := Gamma Frob source.Lbar)
      (E := parametersG.stabilizer s) psi := by
    intro g e
    constructor
    · intro h
      have hval : g • (e • psiH) = psiH := congrArg Subtype.val h
      obtain ⟨hg, he⟩ := (levi ⟨g, e⟩).mp hval
      exact ⟨Subtype.ext hg, Subtype.ext he⟩
    · rintro ⟨hg, he⟩
      rw [he, hg]
  have imageLevi := TypeBRankThreeJordanPacketTransport.product_factorization_of_injective_equivariant
    source.jordanCharacter source.jordanCharacter_injective source.gamma_equivariant
    source.field_equivariant psi packetLevi
  have ambient : ProductStabilizerFactorization (D := SpecialClifford n F)
      (E := parametersG.stabilizer s) (source.jordanCharacter psi) :=
    TypeBRankThreeJordanOvergroup.product_factorization_of_levi
      (gammaEmbedding points source.Lbar) (SpinSubgroup n F normF)
      (TypeBCurrentJordanFiniteProduct.finite_product points source.Lbar
        source.levi_le_spin source.decomposition source.intersection source.lang)
      (subgroup_element_fixes_brauer_character (SpinSubgroup n F normF) iotaG)
      (fun _ _ => rfl) (source.jordanCharacter psi) imageLevi
  have samePacket := TypeBRankThreeJordanPacketTransport.field_stabilizer_eq
    source.jordanCharacter source.jordanCharacter_injective source.field_equivariant psi
  have sameValue : MulAction.stabilizer (parametersG.stabilizer s) psi =
      MulAction.stabilizer (parametersG.stabilizer s) psi.val :=
    Formalisation.stabilizer_eq_of_injective_equivariant
      (f := fun x : Packet (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL => x.val)
      Subtype.val_injective (fun _ _ => rfl) psi
  have horbit : source.jordanCharacter psi ∈
      MulAction.orbit (SpecialClifford n F) (source.jordanCharacter psi0) := by
    refine MulAction.mem_orbit_iff.mpr ⟨gammaEmbedding points source.Lbar y, ?_⟩
    have hp : y • psi0 = psi := Subtype.ext hpsi.symm
    change gammaEmbedding points source.Lbar y • (source.jordan psi0).val = (source.jordan psi).val
    rw [← source.gamma_equivariant y psi0]
    exact congrArg source.jordanCharacter hp
  refine ⟨theta0, theta, y, psi, hpsi, htheta, occurs, horbit,
    samePacket.trans sameValue, source.block_equation psi, ?_⟩
  apply representative_of_product fs iotaG cyclic
  apply parametersG.full_field_factorization iotaG blocksG s (source.jordanCharacter psi)
    (source.jordan psi).property
  exact ambient

end LeviSource

section AllOrbits

open TypeBCurrentPrincipalResults TypeBCentralKernelBlockSource
open TypeBSpinPrincipalDecompositionBinding TypeBCentralKernelBrauerBlocks

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F normF))]
variable [Finite (OrdinaryIrreducibleCharacter.Irr K (Spin n F normF))]
variable [Fintype (LiteralPrimitiveBlock k (Spin n F normF))]
variable {rank : 3 ≤ n} {Msys : ModularSystem 2 K O k}
variable {principalBlock : LiteralPrimitiveBlock k (Spin n F normF)}

/-- Current Proposition 4.13. The proof exhausts the prime-field case and
the principal/nonprincipal alternatives for every original Brauer character.
The nonprincipal source supplies only Levi/Jordan and raw factor geometry. -/
theorem proposition_4_12
    (D : GGGRContext parameters rank Msys iotaG principalBlock)
    (principalRaw : RankSources D) (principalField : FieldSources D fs)
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (levis : ∀ b : LiteralPrimitiveBlock k (Spin n F normF),
      ¬ IsPrincipal b →
        Nonempty (LeviSource fs iotaG D.blocks parametersG Frob points (parametersG.blockParameter b))) :
    BrauerHypothesis fs iotaG := by
  classical
  by_cases hf : f = 1
  · exact prime_field fs iotaG cyclic hf
  letI := diagonalAction iotaG
  intro psi0
  by_cases principal : Supported iotaG principalBlock psi0
  · refine ⟨psi0, MulAction.mem_orbit_self psi0, ?_⟩
    apply representative_of_field_fixed fs iotaG cyclic psi0
    intro e
    exact principalBrauer_fixed D principalRaw fs principalField e psi0 principal
  · let b := supportingBlock iotaG D.blocks psi0
    have nonprincipal : ¬ IsPrincipal b := by
      intro hb
      have eq : b = principalBlock :=
        TypeBCentralKernelPrincipalStability.principal_unique D.blocks b principalBlock hb D.principal
      apply principal
      apply (supported_iff_block iotaG D.blocks principalBlock psi0).mpr
      exact eq
    let source := Classical.choice (levis b nonprincipal)
    have packet : InPacket iotaG D.blocks (parametersG.idempotent (parametersG.blockParameter b)) psi0 :=
      (parametersG.in_packet_iff iotaG D.blocks _ psi0).mpr rfl
    let start := source.jordan.symm ⟨psi0, packet⟩
    obtain ⟨theta0, theta, y, psi, _, _, _, horbit, _, _, representative⟩ :=
      source.selected_jordan cyclic start
    refine ⟨source.jordanCharacter psi, ?_, representative⟩
    have initial : source.jordanCharacter start = psi0 :=
      congrArg Subtype.val (source.jordan.apply_symm_apply ⟨psi0, packet⟩)
    simpa only [initial] using horbit

end AllOrbits
end ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
