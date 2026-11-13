module

public import BlockBand.Coarea.Native.BlockBand.Analysis.ProjectedWegnerAveraging
public import BlockBand.Coarea.Native.BlockBand.Analysis.BoundaryFatou
public import Mathlib.Probability.IdentDistrib

/-!
# Physical conditioning assembly for projected Wegner averaging

This file isolates the probability-law input in the proof of the projected
Wegner lemma.  After conditioning
on the exterior and all diagonal blocks except the exposed one, its Schur
resolvent must have the law of a deterministically deformed `GUE_W(1/W)` block
with an arbitrary positive-semidefinite absorber.  The exterior is allowed to
be random and is integrated out explicitly.

The structure below records only this disintegration/identical-distribution
statement and joint measurability.  Nonnegativity is transferred from the
proved absorbed-resolvent identity, rather than stored as an assumption.  It
does not assert that `GaussianRing.Law` constructs these data.
Consequently the final theorem here is conditional on that structure.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexOrder ENNReal NNReal Topology

universe u v w

/-- The one-block dimension family used to expose a single physical block of
width `W` to the PSSS estimate. -/
def singletonBlockSize (W : ℕ) : Fin 1 → ℕ := fun _ => W

/-- A positive physical width gives a nonempty singleton block family. -/
theorem singletonBlockSize_pos {W : ℕ} (hW : 0 < W) :
    ∀ j, 0 < singletonBlockSize W j := fun _ => hW

/-- The PSSS index space of a singleton width-`W` family has cardinality
exactly `W`; no normalized trace or hidden block factor occurs. -/
theorem card_singletonBlockIndex (W : ℕ) :
    Fintype.card (BlockGUE.Index (singletonBlockSize W)) = W := by
  rw [blockGUE_dimension]
  simp [singletonBlockSize]

/-- The conditional absorbed trace on the product of exterior randomness and
one freshly exposed diagonal GUE block. -/
def conditionedAbsorbedTrace
    {W : ℕ} (hW : 0 < W)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (M : BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (singletonBlockSize W)))
    (Q : Ξ → Matrix (BlockGUE.Index (singletonBlockSize W))
      (BlockGUE.Index (singletonBlockSize W)) ℂ)
    (η : ℝ) (p : Ξ × M.Ω) : ℝ :=
  BlockGUE.absorbedTrace M (A₀ p.1) (Q p.1) η p.2

/-- Physical conditioning data for a family of retained blocks.

For block `j`, `Ξ j` carries the conditioned exterior, `ν j` is its probability
law, and `M j` is the independent exposed `GUE_W(1/W)` law.  `identDistrib`
is the tower/disintegration statement identifying the physical block
trace `g j` with the product-space Schur trace.  `absorber_pos` is precisely
the output supplied by `schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef`
once the physical block decomposition and its invertibility have been built.
No expectation estimate is stored as a field. -/
structure PhysicalBlockConditioning
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    (g : β → Ω → ℝ) (W : ℕ) (hW : 0 < W)
    (η : ℝ)
    (Ξ : β → Type v) [∀ _j, MeasurableSpace (Ξ _j)]
    (ν : ∀ j, Measure (Ξ j)) [∀ j, IsProbabilityMeasure (ν j)]
    (M : ∀ _j, BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW)) where
  background : ∀ j, Ξ j →
    HermitianMatrix (BlockGUE.Index (singletonBlockSize W))
  absorber : ∀ j, Ξ j →
    Matrix (BlockGUE.Index (singletonBlockSize W))
      (BlockGUE.Index (singletonBlockSize W)) ℂ
  absorber_pos : ∀ j ξ, (absorber j ξ).PosSemidef
  joint_measurable : ∀ j,
    Measurable (conditionedAbsorbedTrace hW (M j)
      (background j) (absorber j) η)
  identDistrib : ∀ j,
    IdentDistrib (g j)
      (conditionedAbsorbedTrace hW (M j)
        (background j) (absorber j) η)
      μ ((ν j).prod (M j).P)

/-- The Schur-complement positivity theorem supplies exactly the absorber
positivity field required by `PhysicalBlockConditioning`.  This declaration
records the physical source of that field without assuming commutativity. -/
theorem conditionedSchur_absorber_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] {η : ℝ} (hη : 0 ≤ η)
    (him :
      (matrixImaginaryPart (Matrix.fromBlocks A B C D) -
        (η : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef) :
    (matrixImaginaryPart (schurComplement₂₂ A B C D) -
      (η : ℂ) • (1 : Matrix m m ℂ)).PosSemidef :=
  schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef
    A B C D hη him

/-- The exposed diagonal block of the inverse is the absorbed GUE trace once
the conditioned Schur complement has been identified with the displayed
`GUE + background + i(absorber + ηI)` matrix.  This is the exact deterministic
bridge used inside the `identDistrib` field above. -/
theorem exposedBlock_trace_eq_conditionedAbsorbedTrace
    {W : ℕ} (hW : 0 < W)
    (M : BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (A₀ : HermitianMatrix (BlockGUE.Index (singletonBlockSize W)))
    (Q : Matrix (BlockGUE.Index (singletonBlockSize W))
      (BlockGUE.Index (singletonBlockSize W)) ℂ)
    (ω : M.Ω)
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (BlockGUE.Index (singletonBlockSize W))
      (BlockGUE.Index (singletonBlockSize W)) ℂ)
    (B : Matrix (BlockGUE.Index (singletonBlockSize W)) n ℂ)
    (C : Matrix n (BlockGUE.Index (singletonBlockSize W)) ℂ)
    (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)]
    (η : ℝ)
    (hschur : schurComplement₂₂ A B C D =
      (BlockGUE.deformed M A₀ ω : Matrix _ _ ℂ) +
        Complex.I • (Q + η • (1 : Matrix _ _ ℂ))) :
    -((((Matrix.fromBlocks A B C D)⁻¹).submatrix
      Sum.inl Sum.inl).trace).im =
      BlockGUE.absorbedTrace M A₀ Q η ω := by
  rw [neg_im_trace_submatrix_nonsing_inv_fromBlocks_eq_schurComplement₂₂
    A B C D, hschur]
  rfl

/-- Joint integrability of a conditioned physical slice.  This is the second
Tonelli step: the inner integral is controlled uniformly by `π C W`, while
the exterior law has total mass one. -/
theorem integrable_conditionedAbsorbedTrace
    (input : PSSSInput.{u})
    {W : ℕ} (hW : 0 < W)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (M : BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (singletonBlockSize W)))
    (Q : Ξ → Matrix (BlockGUE.Index (singletonBlockSize W))
      (BlockGUE.Index (singletonBlockSize W)) ℂ)
    (hQ : ∀ ξ, (Q ξ).PosSemidef)
    {η : ℝ} (hη : 0 < η)
    (hmeas : Measurable (conditionedAbsorbedTrace hW M A₀ Q η)) :
    Integrable (conditionedAbsorbedTrace hW M A₀ Q η)
      (ν.prod M.P) := by
  let K : ℝ := Real.pi * input.C * (W : ℝ)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards with ξ
    exact (blockGUE_absorbedTrace_integrable_and_integral_le
      input (singletonBlockSize_pos hW) M (A₀ ξ) (Q ξ) (hQ ξ) hη).1
  · have hinner : AEStronglyMeasurable
        (fun ξ => ∫ ω, ‖conditionedAbsorbedTrace hW M A₀ Q η (ξ, ω)‖ ∂M.P) ν :=
      hmeas.aestronglyMeasurable.norm.integral_prod_right'
    apply (integrable_const K).mono' hinner
    filter_upwards with ξ
    have hnonneg : ∀ ω,
        0 ≤ conditionedAbsorbedTrace hW M A₀ Q η (ξ, ω) := fun ω =>
      blockGUE_absorbedTrace_nonneg (singletonBlockSize_pos hW)
        M (A₀ ξ) (Q ξ) (hQ ξ) hη ω
    have heq : (∫ ω, ‖conditionedAbsorbedTrace hW M A₀ Q η (ξ, ω)‖ ∂M.P) =
        ∫ ω, conditionedAbsorbedTrace hW M A₀ Q η (ξ, ω) ∂M.P := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
    rw [heq]
    have hint : 0 ≤ ∫ ω,
        conditionedAbsorbedTrace hW M A₀ Q η (ξ, ω) ∂M.P :=
      integral_nonneg hnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hint]
    simpa only [conditionedAbsorbedTrace, K, card_singletonBlockIndex] using
      (blockGUE_absorbedTrace_integrable_and_integral_le
        input (singletonBlockSize_pos hW) M (A₀ ξ) (Q ξ) (hQ ξ) hη).2

/-- Integrating out the conditioned exterior preserves the sharp one-block
constant `π C W`. -/
theorem integral_conditionedAbsorbedTrace_le
    (input : PSSSInput.{u})
    {W : ℕ} (hW : 0 < W)
    {Ξ : Type v} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (M : BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (singletonBlockSize W)))
    (Q : Ξ → Matrix (BlockGUE.Index (singletonBlockSize W))
      (BlockGUE.Index (singletonBlockSize W)) ℂ)
    (hQ : ∀ ξ, (Q ξ).PosSemidef)
    {η : ℝ} (hη : 0 < η)
    (hmeas : Measurable (conditionedAbsorbedTrace hW M A₀ Q η)) :
    ∫ p, conditionedAbsorbedTrace hW M A₀ Q η p ∂(ν.prod M.P) ≤
      Real.pi * input.C * (W : ℝ) := by
  let F := conditionedAbsorbedTrace hW M A₀ Q η
  let K : ℝ := Real.pi * input.C * (W : ℝ)
  have hprod : Integrable F (ν.prod M.P) :=
    integrable_conditionedAbsorbedTrace input hW ν M A₀ Q hQ hη hmeas
  rw [integral_prod F hprod]
  have hinner : Integrable (fun ξ => ∫ ω, F (ξ, ω) ∂M.P) ν :=
    hprod.integral_prod_left
  calc
    (∫ ξ, ∫ ω, F (ξ, ω) ∂M.P ∂ν) ≤ ∫ _ξ, K ∂ν := by
      apply integral_mono hinner (integrable_const K)
      intro ξ
      simpa only [F, conditionedAbsorbedTrace, K, card_singletonBlockIndex] using
        (blockGUE_absorbedTrace_integrable_and_integral_le
          input (singletonBlockSize_pos hW) M (A₀ ξ) (Q ξ) (hQ ξ) hη).2
    _ = K := integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
    _ = Real.pi * input.C * (W : ℝ) := rfl

/-- Physical conditioning data construct the exact
`SingleBlockAveraging` value required by the finite-block summation theorem. -/
theorem PhysicalBlockConditioning.singleBlockAveraging
    (input : PSSSInput.{u})
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    (g : β → Ω → ℝ) {W : ℕ} (hW : 0 < W)
    {η : ℝ} (hη : 0 < η)
    (Ξ : β → Type v) [∀ _j, MeasurableSpace (Ξ _j)]
    (ν : ∀ j, Measure (Ξ j)) [∀ j, IsProbabilityMeasure (ν j)]
    (M : ∀ _j, BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (hcond : PhysicalBlockConditioning μ g W hW η Ξ ν M) :
    SingleBlockAveraging μ g input.C (W : ℝ) where
  integrable j := by
    have hp := integrable_conditionedAbsorbedTrace input hW (ν j) (M j)
      (hcond.background j) (hcond.absorber j) (hcond.absorber_pos j)
      hη (hcond.joint_measurable j)
    exact (hcond.identDistrib j).symm.integrable_snd hp
  nonneg j := by
    apply (hcond.identDistrib j).symm.ae_snd measurableSet_Ici
    filter_upwards with p
    exact blockGUE_absorbedTrace_nonneg (singletonBlockSize_pos hW)
      (M j) (hcond.background j p.1) (hcond.absorber j p.1)
      (hcond.absorber_pos j p.1) hη p.2
  oneBlock j := by
    rw [(hcond.identDistrib j).integral_eq]
    exact integral_conditionedAbsorbedTrace_le input hW (ν j) (M j)
      (hcond.background j) (hcond.absorber j) (hcond.absorber_pos j)
      hη (hcond.joint_measurable j)

/-- Conditional physical projected-Wegner estimate, with the
unnormalized trace and exact constant `π C W |B|`.  Constructing
`PhysicalBlockConditioning` from `GaussianRing.Law` is a separate
disintegration statement. -/
theorem projectedWegner_physical_of_conditioning
    (input : PSSSInput.{u})
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    (g : β → Ω → ℝ) {W : ℕ} (hW : 0 < W)
    {η : ℝ} (hη : 0 < η)
    (Ξ : β → Type v) [∀ _j, MeasurableSpace (Ξ _j)]
    (ν : ∀ j, Measure (Ξ j)) [∀ j, IsProbabilityMeasure (ν j)]
    (M : ∀ _j, BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (hcond : PhysicalBlockConditioning μ g W hW η Ξ ν M)
    (B : Finset β) (hproj : ProjectedTraceDecomposition g B) :
    ∫ ω, hproj.projectedTrace ω ∂μ ≤
      Real.pi * input.C * (W : ℝ) * (B.card : ℝ) := by
  exact projectedWegner_of_singleBlock μ g input.C (W : ℝ)
    (hcond.singleBlockAveraging input μ g hW hη Ξ ν M) B hproj

/-- The regulated physical resolvent
`(H - eI + i(Γ + ηI))⁻¹` on block coordinates. -/
def physicalAbsorbedResolvent
    {Ω β : Type*} [Fintype β] [DecidableEq β] {W : ℕ}
    (H Γ : Ω → Matrix (β × Fin W) (β × Fin W) ℂ)
    (e η : ℝ) (ω : Ω) :
    Matrix (β × Fin W) (β × Fin W) ℂ :=
  (H ω - (e : ℂ) • (1 : Matrix (β × Fin W) (β × Fin W) ℂ) +
    Complex.I •
      (Γ ω + η • (1 : Matrix (β × Fin W) (β × Fin W) ℂ)))⁻¹

/-- Canonical retained-block form of the conditional physical theorem.
Here `R ω` is the absorbed physical resolvent on block coordinates
`β × Fin W`, and the left side is the sum of the unnormalized
diagonal-block traces `-Im Tr P_j R`. -/
theorem projectedWegner_physical_blocks_of_conditioning
    (input : PSSSInput.{u})
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    {W : ℕ} (hW : 0 < W) {η : ℝ} (hη : 0 < η)
    (R : Ω → Matrix (β × Fin W) (β × Fin W) ℂ)
    (Ξ : β → Type v) [∀ _j, MeasurableSpace (Ξ _j)]
    (ν : ∀ j, Measure (Ξ j)) [∀ j, IsProbabilityMeasure (ν j)]
    (M : ∀ _j, BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (hcond : PhysicalBlockConditioning μ
      (fun j ω => blockNegativeImaginaryTrace (R ω) j)
      W hW η Ξ ν M)
    (B : Finset β) :
    ∫ ω, ∑ j ∈ B, blockNegativeImaginaryTrace (R ω) j ∂μ ≤
      Real.pi * input.C * (W : ℝ) * (B.card : ℝ) := by
  exact projectedWegner_physical_of_conditioning input μ
    (fun j ω => blockNegativeImaginaryTrace (R ω) j)
    hW hη Ξ ν M hcond B
    (projectedTraceDecomposition_of_blocks R B)

/-- Direct regulated-resolvent specialization.  The hypothesis `hcond` asserts
that, after conditioning the physical Hamiltonian
`H = D + ⨁ A_j` and absorber `Γ`, each displayed diagonal-block trace has the
corresponding exposed Schur/GUE product law. -/
theorem projectedWegner_physical_resolvent_of_conditioning
    (input : PSSSInput.{u})
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    {W : ℕ} (hW : 0 < W) (e : ℝ) {η : ℝ} (hη : 0 < η)
    (H Γ : Ω → Matrix (β × Fin W) (β × Fin W) ℂ)
    (Ξ : β → Type v) [∀ _j, MeasurableSpace (Ξ _j)]
    (ν : ∀ j, Measure (Ξ j)) [∀ j, IsProbabilityMeasure (ν j)]
    (M : ∀ _j, BlockGUE.Law.{u} (singletonBlockSize W)
      (singletonBlockSize_pos hW))
    (hcond : PhysicalBlockConditioning μ
      (fun j ω => blockNegativeImaginaryTrace
        (physicalAbsorbedResolvent H Γ e η ω) j)
      W hW η Ξ ν M)
    (B : Finset β) :
    ∫ ω, ∑ j ∈ B, blockNegativeImaginaryTrace
        (physicalAbsorbedResolvent H Γ e η ω) j ∂μ ≤
      Real.pi * input.C * (W : ℝ) * (B.card : ℝ) :=
  projectedWegner_physical_blocks_of_conditioning input μ hW hη
    (physicalAbsorbedResolvent H Γ e η) Ξ ν M hcond B

/-- Boundary-value specialization of the physical finite-height assembly.
For each regulator height the caller may use
`PhysicalBlockConditioning.singleBlockAveraging`; the only other input is
the almost-everywhere boundary convergence.  Fatou preserves the
same exact constant `π C W |B|`. -/
theorem projectedWegner_boundary_of_singleBlockAveraging
    (input : PSSSInput.{u})
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    (g : ℕ → β → Ω → ℝ) (W : ℝ)
    (havg : ∀ n, SingleBlockAveraging μ (g n) input.C W)
    (B : Finset β)
    (hproj : ∀ n, ProjectedTraceDecomposition (g n) B)
    (boundary : Ω → ℝ≥0∞)
    (htendsto : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ENNReal.ofReal ((hproj n).projectedTrace ω))
      atTop (𝓝 (boundary ω))) :
    ∫⁻ ω, boundary ω ∂μ ≤
      ENNReal.ofReal
        (Real.pi * input.C * W * (B.card : ℝ)) := by
  have hint (n : ℕ) :
      Integrable (hproj n).projectedTrace μ :=
    (hproj n).integrable μ (havg n)
  have hnonneg (n : ℕ) :
      0 ≤ᵐ[μ] (hproj n).projectedTrace := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ g n j ω :=
      ae_all_iff.mpr (havg n).nonneg
    filter_upwards [hall] with ω hω
    rw [(hproj n).eq_sum]
    exact Finset.sum_nonneg fun j _hj => hω j
  apply lintegral_boundary_le_of_tendsto μ
    (fun n ω => ENNReal.ofReal ((hproj n).projectedTrace ω))
    boundary
    (ENNReal.ofReal
      (Real.pi * input.C * W * (B.card : ℝ)))
  · intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hint n).aestronglyMeasurable.aemeasurable
  · exact htendsto
  · intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal
      (projectedWegner_of_singleBlock μ (g n) input.C W
        (havg n) B (hproj n))

end CoareaNative.BlockBand
