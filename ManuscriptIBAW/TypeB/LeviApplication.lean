import ManuscriptIBAW.TypeB.LeviSources

/-!
# Brauer representatives from the current principal and Levi sources

The principal branch uses the basis proved with the two upper families.
Every Spin factor of a proper Levi uses the same current principal theorem.
The component, Clifford and Jordan transport steps preserve their original
characters, roots, block correspondence and field stabilisers.

The geometric and published Jordan assumptions are unchanged. No final
representative or field fixation is supplied by a source record.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeB.LeviSources

open ModularRep ModularRep.PaperProofs FDRepSimpleClassKZero TypeBCliffordCarriers
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

namespace Source

variable {fs iotaG blocksG parametersG Frob points}
variable {s : SemisimpleIndex (n := n) (p := p) (F := F)}
variable (source : Source fs iotaG blocksG parametersG Frob points s)

@[instance_reducible] def gammaCharacters :
    MulAction (Gamma Frob source.Lbar) (IBr iotaG) :=
  letI := diagonalAction iotaG
  MulAction.compHom _ (gammaEmbedding points source.Lbar)

@[instance_reducible] def fieldCharacters :
    MulAction (parametersG.stabilizer s) (IBr iotaG) :=
  letI := fieldAction fs iotaG
  MulAction.compHom _ (parametersG.stabilizer s).subtype

/-- The injection used by stabilizer transport is derived from the bijection
on the complete sets of characters belonging to the specified series idempotents.
Its values are the original ambient characters. -/
def jordanCharacter :
    letI : Fintype source.BL := source.finiteBL
    Packet (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL → IBr iotaG :=
  fun psi => (source.jordan psi).val

theorem jordanCharacter_injective : Function.Injective source.jordanCharacter := by
  intro x y h
  exact source.jordan.injective (Subtype.ext h)



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
  let : Fintype source.BL := source.finiteBL
  intro psi0
  let := ambientBrauerAction (H Frob source.Lbar) (rootH Frob source.Lbar source.iotaL)
  let := ambientBrauerAction (N Frob source.Lbar) (rootN Frob source.Lbar source.iotaN)
  let := fieldBrauerAction (H Frob source.Lbar) (rootH Frob source.Lbar source.iotaL)
    source.field.fieldOnGamma source.field.H_stable
  let := packetMulAction (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL
    (MulAut.conjNormal (H := H Frob source.Lbar)) source.gammaInvariant
  let := packetMulAction (rootH Frob source.Lbar source.iotaL) source.blocksL source.eL
    (restrictAutomorphismHom (H Frob source.Lbar) source.field.fieldOnGamma source.field.H_stable)
    source.fieldInvariant
  let := diagonalAction iotaG
  let := fieldAction fs iotaG
  let := source.gammaCharacters
  let := fieldCharacters (fs := fs) (iotaG := iotaG) (parametersG := parametersG) (s := s)
  obtain ⟨theta0, occurs0⟩ := source.constituent psi0
  obtain ⟨theta, y, psiH, hpsi, htheta, occurs, levi⟩ :=
    ManuscriptIBAW.TypeB.LeviSources.same_y_representative Frob source.Lbar source.leviStable source.field
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

end Source

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

/-- Proposition 4.13. The proof exhausts the prime-field case and
the principal/nonprincipal alternatives for every original Brauer character.
The nonprincipal source supplies only Levi/Jordan and raw factor geometry. -/
theorem brauerHypothesis
    (D : GGGRContext parameters rank Msys iotaG principalBlock)
    (principalRaw : GGGRSources.RankSources D) (principalField : FieldSources D fs)
    (cyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (levis : ∀ b : LiteralPrimitiveBlock k (Spin n F normF),
      ¬ IsPrincipal b →
        Nonempty (Source fs iotaG D.blocks parametersG Frob points (parametersG.blockParameter b))) :
    BrauerHypothesis fs iotaG := by
  classical
  by_cases hf : f = 1
  · exact prime_field fs iotaG cyclic hf
  let := diagonalAction iotaG
  intro psi0
  by_cases principal : Supported iotaG principalBlock psi0
  · refine ⟨psi0, MulAction.mem_orbit_self psi0, ?_⟩
    apply representative_of_field_fixed fs iotaG cyclic psi0
    intro e
    exact GGGRBasis.principalBrauer_fixed D principalRaw fs principalField e psi0 principal
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
end ManuscriptIBAW.TypeB.LeviSources

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
