module

public import BlockBand.Endpoints.Sine.MicroscopicTagStepsPalm
public import BlockBand.Endpoints.Sine.MicroscopicTagStepsCommonPort

/-!
# The one-block normalizer is the Palm mass

Step 2 of the proof of the microscopic tag comparison, with the one-block normalizer
`Z₀(e) = 𝒜⁰_e(1)`.

* `mts_negativeCount_eq`, `mts_measurableSet_negativeCount`: `N_-` is the number of negative
  increasing eigenvalues on Hermitian matrices, hence Borel (`measurable_rawIncreasingEigenvalue`,
  `measurableSet_isHermitian`).
* `mts_blockNormalizer_eq_sum`: `Z₀(e) = Σ_{ℓ < W} 𝒜⁰_{ℓ,e}[1]` for a measurable frame (the
  sector indicators sum to one since `N_-` of a `(W-1)`-matrix is `≤ W - 1`).
* `mts_blockNormalizer_eq_palmMass`: with `FreshEigenpairDensityContract` and the one-block Palm
  reduction, `Z₀(e) = ofReal(palmMass (reindex σ σ F(e)) c e)` for `H_R` Hermitian.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal

/-!
## Measurability of the negative count
-/

section Count

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mts_negativeCount_eq (M : Matrix ι ι ℂ) :
    negativeCount M = if M.IsHermitian then
      (Finset.univ.filter fun i : Fin (Fintype.card ι) => rawIncreasingEigenvalue i M < 0).card
      else 0 := by
  unfold negativeCount
  by_cases hM : M.IsHermitian
  · simp only [hM, dite_true, ite_true]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine (Fintype.card_congr (BlockBand.Foundations.Spectral.increasingIndex.subtypeEquiv
      fun i => ?_)).symm
    rw [rawIncreasingEigenvalue_eq i M hM,
      BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
  · simp [hM]

theorem mts_negativeCount_le (M : Matrix ι ι ℂ) : negativeCount M ≤ Fintype.card ι := by
  rw [mts_negativeCount_eq]
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · exact Nat.zero_le _

theorem mts_measurable_negativeCount_real :
    Measurable (fun M : Matrix ι ι ℂ => (negativeCount M : ℝ)) := by
  have h : (fun M : Matrix ι ι ℂ => (negativeCount M : ℝ)) = fun M =>
      if M.IsHermitian then ∑ i : Fin (Fintype.card ι),
        (if rawIncreasingEigenvalue i M < 0 then (1 : ℝ) else 0) else 0 := by
    funext M
    rw [mts_negativeCount_eq]
    split_ifs
    · rw [Finset.card_filter]; push_cast; rfl
    · simp
  rw [h]
  refine Measurable.ite (BlockBand.Model.Construction.measurableSet_isHermitian (ι := ι)) (Finset.measurable_sum _ fun i _ => ?_)
    measurable_const
  exact Measurable.ite (measurableSet_lt (measurable_rawIncreasingEigenvalue i) measurable_const)
    measurable_const measurable_const

theorem mts_measurableSet_negativeCount (ℓ : ℕ) :
    MeasurableSet {M : Matrix ι ι ℂ | negativeCount M = ℓ} := by
  have : {M : Matrix ι ι ℂ | negativeCount M = ℓ} =
      (fun M : Matrix ι ι ℂ => (negativeCount M : ℝ)) ⁻¹' {(ℓ : ℝ)} := by
    ext M; simp
  rw [this]
  exact mts_measurable_negativeCount_real (measurableSet_singleton _)

end Count

/-!
## `Z₀ = Σ_ℓ 𝒜⁰_ℓ[1]`
-/

section Normalizer

variable (p : Parameters) (k : ZMod p.n)

theorem mts_measurable_regressionFactor {ι : Type*} [Fintype ι] (t e : ℝ)
    (F : Matrix ι ι ℂ) : Measurable (fun v : ι → ℂ => regressionFactor t e v F) := by
  have hc : Continuous (fun v : ι → ℂ => regressionFactor t e v F) := by
    unfold regressionFactor l2Norm
    fun_prop
  exact hc.measurable

theorem mts_measurable_blockFrameM
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (e : ℝ) :
    Measurable (fun q : (BlockSite p k → ℂ) ×
        Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => blockFrameM p k U ω e q.1 q.2) := by
  have hUq : Measurable (fun q : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => U q.1) := hU.comp measurable_fst
  unfold blockFrameM
  exact measurable_mat_sub (measurable_mat_add (measurable_mat_mul (measurable_mat_mul
    (measurable_conjTranspose''.comp hUq) measurable_const) hUq) measurable_snd) measurable_const

/-- The density of `𝒜⁰_{ℓ,e}` (`ℓ` fixed, test `1`). -/
def mts_sectorDensity (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (coareaConstant p.W (blockTime p) *
    regressionFactor (blockTime p) e v (blockF p k ω e) *
    Complex.normSq (blockFrameM p k U ω e v G').det)

theorem mts_measurable_sectorTerm
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) {α : Type*} [MeasurableSpace α]
    {vv : α → BlockSite p k → ℂ} {GG : α → Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ}
    (hv : Measurable vv) (hG : Measurable GG) :
    Measurable (fun a => mts_sectorDensity p k U ω e (vv a) (GG a) *
      (if negativeCount (blockFrameM p k U ω e (vv a) (GG a)) = ℓ then (1 : ℝ≥0∞) else 0) * 1) := by
  have hUq : Measurable (fun a => U (vv a)) := hU.comp hv
  have hM : Measurable (fun a => blockFrameM p k U ω e (vv a) (GG a)) := by
    unfold blockFrameM
    exact measurable_mat_sub (measurable_mat_add (measurable_mat_mul (measurable_mat_mul
      (measurable_conjTranspose''.comp hUq) measurable_const) hUq) hG) measurable_const
  have hdens : Measurable (fun a => mts_sectorDensity p k U ω e (vv a) (GG a)) := by
    unfold mts_sectorDensity
    refine ENNReal.measurable_ofReal.comp (Measurable.mul (measurable_const.mul
      ((mts_measurable_regressionFactor _ e _).comp hv)) ?_)
    exact Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hind : Measurable (fun a =>
      (if negativeCount (blockFrameM p k U ω e (vv a) (GG a)) = ℓ then (1 : ℝ≥0∞) else 0)) :=
    Measurable.ite ((mts_measurableSet_negativeCount ℓ).preimage hM) measurable_const
      measurable_const
  exact (hdens.mul hind).mul measurable_const

/-- `Z₀(e) = Σ_{ℓ < W} 𝒜⁰_{ℓ,e}[1]` for every measurable frame. -/
theorem mts_blockNormalizer_eq_sum
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (e : ℝ) :
    blockNormalizer p k U ω e =
      ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p k U ω e ℓ (fun _ => 1) := by
  classical
  have := passDeriv_isProbabilityMeasure_gue (BlockFrameIndex p) (blockTime p)
  have hsum1 : ∀ v G', ∑ ℓ ∈ Finset.range p.W,
      (if negativeCount (blockFrameM p k U ω e v G') = ℓ then (1 : ℝ≥0∞) else 0) = 1 := by
    intro v G'
    rw [Finset.sum_ite_eq]
    have h1 := mts_negativeCount_le (blockFrameM p k U ω e v G')
    have h2 : Fintype.card (BlockFrameIndex p) < p.W := by
      simp only [Fintype.card_fin]; have := p.W_pos; omega
    rw [ite_eq_left (Finset.mem_range.2 (lt_of_le_of_lt h1 h2))]
  have hin : ∀ ℓ : ℕ, ∀ v, Measurable (fun G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      mts_sectorDensity p k U ω e v G' *
        (if negativeCount (blockFrameM p k U ω e v G') = ℓ then (1 : ℝ≥0∞) else 0) * 1) :=
    fun ℓ v => mts_measurable_sectorTerm p k U hU ω e ℓ measurable_const measurable_id
  have hq : ∀ ℓ : ℕ, Measurable (fun q : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      mts_sectorDensity p k U ω e q.1 q.2 *
        (if negativeCount (blockFrameM p k U ω e q.1 q.2) = ℓ then (1 : ℝ≥0∞) else 0) * 1) :=
    fun ℓ => mts_measurable_sectorTerm p k U hU ω e ℓ measurable_fst measurable_snd
  have hout : ∀ ℓ : ℕ, Measurable (fun v : BlockSite p k → ℂ =>
      ∫⁻ G', mts_sectorDensity p k U ω e v G' *
        (if negativeCount (blockFrameM p k U ω e v G') = ℓ then (1 : ℝ≥0∞) else 0) * 1
        ∂gueMeasure (BlockFrameIndex p) (blockTime p)) :=
    fun ℓ => (hq ℓ).lintegral_prod_right'
  have hinner : ∀ v, (∫⁻ G', mts_sectorDensity p k U ω e v G'
      ∂gueMeasure (BlockFrameIndex p) (blockTime p)) =
      ∑ ℓ ∈ Finset.range p.W, ∫⁻ G', mts_sectorDensity p k U ω e v G' *
        (if negativeCount (blockFrameM p k U ω e v G') = ℓ then (1 : ℝ≥0∞) else 0) * 1
        ∂gueMeasure (BlockFrameIndex p) (blockTime p) := by
    intro v
    rw [← lintegral_finsetSum _ fun ℓ _ => hin ℓ v]
    refine lintegral_congr fun G' => ?_
    simp only [mul_one]
    rw [← Finset.mul_sum, hsum1, mul_one]
  show (∫⁻ v, ∫⁻ G', mts_sectorDensity p k U ω e v G'
      ∂gueMeasure (BlockFrameIndex p) (blockTime p) ∂projectiveHaar (BlockSite p k)) =
    ∑ ℓ ∈ Finset.range p.W, ∫⁻ v, ∫⁻ G', mts_sectorDensity p k U ω e v G' *
        (if negativeCount (blockFrameM p k U ω e v G') = ℓ then (1 : ℝ≥0∞) else 0) * 1
        ∂gueMeasure (BlockFrameIndex p) (blockTime p) ∂projectiveHaar (BlockSite p k)
  rw [← lintegral_finsetSum _ fun ℓ _ => hout ℓ]
  exact lintegral_congr fun v => hinner v

/-- **`Z₀(e) = ofReal(Palm mass)`.** Hypothesis: `FreshEigenpairDensityContract`. For
`σ : BlockSite p k ≃ Fin N` (`N = W`), a measurable block frame and `H_R` Hermitian:
`blockNormalizer = ofReal(palmMass (reindex σ σ F(e)) c e)`. -/
theorem mts_blockNormalizer_eq_palmMass (hFED : FreshEigenpairDensityContract) {N : ℕ}
    (hN : N = p.W) (σ : BlockSite p k ≃ Fin N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) :
    blockNormalizer p k U ω e =
      ENNReal.ofReal (palmMass (Matrix.reindex σ σ (blockF p k ω e)) p.c e) := by
  have h := mts_sum_blockSectorFiber_eq_palmExpect p k hFED hN σ U hU ω hω e (fun _ => 1)
    (fun _ => zero_le_one) (C := 1) (fun _ => le_rfl) (fun _ => 1) measurable_const
    (fun _ => rfl)
  simp only [ENNReal.ofReal_one] at h
  rw [mts_blockNormalizer_eq_sum p k U hU.1 ω e]
  have hsum : ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p k U ω e ℓ (fun _ => 1) =
      ∑ ℓ : Fin N, blockSectorFiber p k U ω e ℓ.val (fun _ => 1) := by
    subst hN
    exact (Fin.sum_univ_eq_sum_range (fun ℓ => blockSectorFiber p k U ω e ℓ (fun _ => 1)) _).symm
  rw [hsum, h]
  congr 1
  by_cases hZ : palmMass (Matrix.reindex σ σ (blockF p k ω e)) p.c e = 0
  · rw [hZ, zero_mul]
  · unfold palmExpect
    simp only [mul_one]
    rw [show (∑ ℓ : Fin N, ∫ A0, palmWeight (Matrix.reindex σ σ (blockF p k ω e)) p.c e ℓ A0
        ∂freshTracelessLaw N p.c) = palmMass (Matrix.reindex σ σ (blockF p k ω e)) p.c e from rfl,
      div_self hZ, mul_one]

end Normalizer

end BlockBand.Endpoints
