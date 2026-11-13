module

public import BlockBand.SourceProcess.RawTag.StepScalar
public import BlockBand.SourceProcess.FullSource.BirthZero
public import BlockBand.SourceProcess.ComplexSourceLaw.Algebra

/-!
# Tools for the birth values of the raw forms

At birth the raw forms are controlled by the uniform fresh inverse estimate.
* `lintegral_of_three`: a form bounded by a product of three factors with `L^{16m}` bounds has
  bounded `4m`-th moment;
* `momBd_firstInverse`: `‖‖G_1‖‖_{L^r} ≤ C` for the one-block path (from
  `GaussianAbsorptionContract`, `W ≥ r/ε₁`);
* `momBd_nearL_of_frame`, `momBd_nearR_of_frame`: the near frames are dominated by the frame
  (`‖ι*‖ ≤ 1`, `𝕊` unitary a.s.).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Three-factor moment bound.** -/
theorem lintegral_of_three {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {x : α → ℂ}
    {F₁ F₂ F₃ : α → ℝ} {m : ℕ} (hm : 1 ≤ m) {B₁ B₂ B₃ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hB₃ : 0 ≤ B₃) (h0 : ∀ a, 0 ≤ F₁ a * F₂ a * F₃ a)
    (hx : ∀ᵐ a ∂μ, ‖x a‖ ≤ F₁ a * F₂ a * F₃ a) (h₁ : MomBd μ F₁ (16 * m) B₁)
    (h₂ : MomBd μ F₂ (16 * m) B₂) (h₃ : MomBd μ F₃ (16 * m) B₃) :
    ∫⁻ a, ENNReal.ofReal ((‖x a‖ ^ 2) ^ (2 * m)) ∂μ ≤
      ENNReal.ofReal ((B₁ * B₂ * B₃) ^ (4 * m)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h12 := (show MomBd μ F₁ (2 * (8 * m)) B₁ by
      rw [show (2 : ℝ) * (8 * m) = 16 * m by ring]; exact h₁).mul (by linarith)
    (show MomBd μ F₂ (2 * (8 * m)) B₂ by rw [show (2 : ℝ) * (8 * m) = 16 * m by ring]; exact h₂)
    hB₁
  have h123 := (show MomBd μ _ (2 * (4 * m)) _ by
      rw [show (2 : ℝ) * (4 * m) = 8 * m by ring]; exact h12).mul (by linarith)
    (show MomBd μ F₃ (2 * (4 * m)) B₃ by
      rw [show (2 : ℝ) * (4 * m) = 8 * m by ring]; exact h₃.exponent_mono (by linarith))
    (by positivity)
  have hI := lintegral_pow_le_of_momBd' (n := 4 * m) (by omega) (by exact_mod_cast h123)
    (by positivity) h0
  refine le_trans (lintegral_mono_ae ?_) hI
  filter_upwards [hx] with a ha
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← pow_mul, show 2 * (2 * m) = 4 * m by ring]
  exact pow_le_pow_left₀ (norm_nonneg _) ha _

/-- **Moments of the first inverse** `‖G_1‖` (one-block path, layer `.oneBlockTwoPorts`). -/
theorem momBd_firstInverse (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {r : ℝ} (hr : 1 ≤ r) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      MomBd (growthPathLaw W b) (fun ω => ‖fullInverse b E W 1 ω‖) r C := by
  obtain ⟨ε₁, C, hε₁, hC, hGA'⟩ := hGA b hb0 hb (etaLow b κ) 2 (etaLow_pos (by linarith) hκ)
  refine ⟨C, ⌈r / ε₁⌉₊ + 1, hC.le, fun W hW E hE => ?_⟩
  have hW0 : 0 < W := by omega
  have hpW : r ≤ ε₁ * W := by
    have h1 := Nat.le_ceil (r / ε₁)
    have h2 : (((⌈r / ε₁⌉₊ + 1 : ℕ)) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    rw [div_le_iff₀ hε₁] at h1
    nlinarith
  obtain ⟨-, hmom⟩ := hGA' W hW0 .oneBlockTwoPorts
    (0 : Matrix (PhysSite W .oneBlockTwoPorts) (PhysSite W .oneBlockTwoPorts) ℂ)
    Matrix.isHermitian_zero E (boundaryZ b E) (etaLow_le (by linarith) hκ hE)
    (bulk_norm_z hb0 hb hκ hE)
  have hm := hmom r hr hpW
  have hmG : Measurable fun s : LayerSample W .oneBlockTwoPorts =>
      ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖ :=
    (measurable_layerResolvent_two E _).norm
  have e : (fun ω => ‖fullInverse b E W 1 ω‖) =
      (fun s => ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖) ∘ sampleOne := by
    funext ω; rw [Function.comp_apply, fullInverse, fullPathMatrix_one_eq]; rfl
  rw [e]
  refine ⟨(hmG.comp measurable_sampleOne).aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_map_measure (by rw [growthPathLaw_map_sampleOne]; exact hmG.aestronglyMeasurable)
    measurable_sampleOne.aemeasurable, growthPathLaw_map_sampleOne]
  exact hm

theorem vecNorm_mulVec_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ)
    (hS : Sᴴ * S = 1) (v : ι → ℂ) : vecNorm (S *ᵥ v) = vecNorm v := by
  have hsq : ∀ u : ι → ℂ, vecNorm u ^ 2 = (star u ⬝ᵥ u).re := by
    intro u
    rw [vecNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), dotProduct,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have h : star (S *ᵥ v) ⬝ᵥ (S *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hS, one_mulVec]
  have h2 : vecNorm (S *ᵥ v) ^ 2 = vecNorm v ^ 2 := by rw [hsq, hsq, h]
  exact (pow_left_inj₀ (vecNorm_nonneg _) (vecNorm_nonneg _) two_ne_zero).mp h2

theorem momBd_nearL_of_frame {b E : ℝ} {l β : ℕ} {Γ : Type} [MeasurableSpace Γ]
    {ν : Measure Γ} [IsProbabilityMeasure ν] {g : Γ → Fin W → ℂ} (hg : Measurable g) {r A : ℝ}
    (hf : MomBd ((growthPathLaw W b).prod ν) (fun w => vecNorm (frame b E W l β w.1 (g w.2))) r A) :
    MomBd ((growthPathLaw W b).prod ν) (fun w => vecNorm (nearL b E W l β w.1 (g w.2))) r A := by
  refine hf.mono ?_ (Filter.Eventually.of_forall fun w => ?_)
  · have := measurable_nearL (W := W) b E l β measurable_fst (hg.comp measurable_snd)
    unfold vecNorm; exact (by fun_prop : Measurable _).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm_nonneg _)]
    exact vecNorm_nearSel_mulVec_le _

theorem momBd_nearR_of_frame {b E : ℝ} {l β : ℕ}
    {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} [IsProbabilityMeasure ν]
    {g : Γ → Fin W → ℂ} (hg : Measurable g) {r A : ℝ}
    (hf : MomBd ((growthPathLaw W b).prod ν) (fun w => vecNorm (frame b E W l β w.1 (g w.2))) r A) :
    MomBd ((growthPathLaw W b).prod ν) (fun w => vecNorm (nearR b E W l β w.1 (g w.2))) r A := by
  refine hf.mono ?_ ?_
  · have := measurable_nearR (W := W) b E l β measurable_fst (hg.comp measurable_snd)
    unfold vecNorm; exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b) (ν := ν)).ae
      (ae_growth_isHermitian W b)] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm_nonneg _), nearR]
    refine (vecNorm_nearSel_mulVec_le _).trans (le_of_eq ?_)
    exact vecNorm_mulVec_unitary _
      (BlockBand.SourceProcess.ComplexSourceLaw.conjTranspose_mul_scattering b E l w.1 hw) _

end BlockBand.SourceProcess.RawTag
