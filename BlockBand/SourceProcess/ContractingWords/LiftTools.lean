module

public import BlockBand.SourceProcess.ContractingWords.SummedTools
public import BlockBand.SourceProcess.ContractingWords.SummedPath
public import BlockBand.SourceProcess.ContractingWords.StepMean
public import BlockBand.Transmission.PathJet.JetPathStep
public import BlockBand.Transmission.PathScalar.AbsorbedRecursion

/-!
# `L²` tools for lifting one-layer bounds to the path

Hölder and Minkowski inequalities in `L²`, and moment bounds for powers of the path error.

* `eLpNorm_mul_le_four`: Hölder `‖fg‖₂ ≤ ‖f‖₄‖g‖₄` (measurable `f, g`);
* `eLpNorm_listSum_le`: Minkowski over a finite list;
* `eLpNorm_pow_le_of`: `‖f^n‖₂ ≤ B^n` from `‖f‖_{2n} ≤ B` (`f ≥ 0` measurable);
and the path moment `pathErr_pow_le`: the path error `e_j = δ₀ + δ₁ + |g|/W + W⁻¹`
(`errMoments`) has `‖e_j^n‖₂ ≤ (C_n/W)^n` for `n ≥ 1`, uniformly as in `errMoments`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem holderTriple_four_four_two : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  rw [ENNReal.holderTriple_iff, ← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp),
    ENNReal.toReal_add (by simp) (by simp)]
  simp; norm_num

/-- Hölder `‖fg‖₂ ≤ ‖f‖₄‖g‖₄`. -/
theorem eLpNorm_mul_le_four {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => f ω * g ω) 2 μ ≤ eLpNorm f 4 μ * eLpNorm g 4 μ := by
  have := holderTriple_four_four_two
  exact eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hf hg

/-- Minkowski over a finite list. -/
theorem eLpNorm_listSum_le {ι : Type*} (L : List ι) (f : ι → Ω → ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun ω => (L.map fun i => f i ω).sum) p μ ≤ (L.map fun i => eLpNorm (f i) p μ).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (eLpNorm_add_le (f := f i) (g := fun ω => (L.map fun i => f i ω).sum) hp).trans
      (add_le_add le_rfl ih)

/-- `‖f^n‖₂ ≤ B^n` from `‖f‖_{2n} ≤ B`. -/
theorem eLpNorm_pow_le_of {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (hfm : AEStronglyMeasurable f μ)
    {n : ℕ} (hn : 1 ≤ n) {B : ℝ≥0∞} (h : eLpNorm f ((2 * n : ℕ) : ℝ≥0∞) μ ≤ B) :
    eLpNorm (fun ω => f ω ^ n) 2 μ ≤ B ^ n := by
  rw [eLpNorm_two_pow f hf hfm n]
  have hl := lintegral_pow_le_of_eLpNorm hf hfm (by omega : 1 ≤ 2 * n) h
  calc (∫⁻ ω, ENNReal.ofReal (f ω) ^ (2 * n) ∂μ) ^ (1 / 2 : ℝ) ≤ (B ^ (2 * n)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hl (by norm_num)
    _ = B ^ n := by
        rw [show 2 * n = n * 2 by ring, pow_mul, ← ENNReal.rpow_natCast (B ^ n) 2,
          ← ENNReal.rpow_mul]
        norm_num

end Abstract

variable {W : ℕ}

/-- The path error `e_j = δ₀ + δ₁ + |g|/W + W⁻¹` of `errMoments`. -/
def pathErr (b E : ℝ) (s : ℂ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  jetDistance0 b E (pathX b E W r ω) + jetDistance1 b E s (pathX b E W r ω) +
    |pathConductance b E W r ω| / W + (W : ℝ)⁻¹

theorem pathErr_nonneg (b E : ℝ) (s : ℂ) (W r : ℕ) (ω : GrowthPath W) : 0 ≤ pathErr b E s W r ω := by
  unfold pathErr jetDistance0 jetDistance1; positivity

theorem aesm_pathErr {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (r : ℕ) :
    AEStronglyMeasurable (pathErr b E s W r) (growthPathLaw W b) := by
  have hXm := BlockBand.Transmission.PathJet.measurable_pathX (W := W) b E r
  have h0 : AEStronglyMeasurable (fun ω => jetDistance0 b E (pathX b E W r ω))
      (growthPathLaw W b) :=
    ((BlockBand.Transmission.PathScalar.measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  have h1' : AEStronglyMeasurable (fun ω => jetDistance1 b E s (pathX b E W r ω))
      (growthPathLaw W b) :=
    (BlockBand.Transmission.PathJet.measurable_pathJetV b E s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (BlockBand.Transmission.PathJet.pathJet1_ae_eq (W := W) hb h1 h2 s r))
  have hg : AEStronglyMeasurable (fun ω => |pathConductance b E W r ω| / W) (growthPathLaw W b) :=
    ((BlockBand.Transmission.SourceMixing.measurable_pathConductance b E r).abs.div_const
      _).aestronglyMeasurable
  exact ((h0.add h1').add hg).add aestronglyMeasurable_const

/-- **Path moments of powers of the error.** -/
theorem pathErr_pow_le (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {ε T : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        AEStronglyMeasurable (pathErr b E s W r) (growthPathLaw W b) ∧
        eLpNorm (fun ω => pathErr b E s W r ω ^ n) 2 (growthPathLaw W b) ≤
          ENNReal.ofReal ((C / W) ^ n) := by
  obtain ⟨C, W₀, hC, h⟩ := errMoments hMT hGA hLp hb0 hb hκ (T := T) hε
    (p := ((2 * n : ℕ) : ℝ)) (by exact_mod_cast (by omega : 1 ≤ 2 * n))
  refine ⟨C, W₀, hC, fun W hW E hE s hs r hr1 hr2 => ?_⟩
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hm := aesm_pathErr (W := W) (b := b) (E := E) (by linarith) hE1 hE2 s r
  refine ⟨hm, ?_⟩
  have h' := h W hW E hE s hs r hr1 hr2
  rw [ENNReal.ofReal_natCast] at h'
  refine (eLpNorm_pow_le_of (pathErr_nonneg b E s W r) hm hn h').trans ?_
  rw [ENNReal.ofReal_pow (by positivity)]

end BlockBand.SourceProcess.ContractingWords
