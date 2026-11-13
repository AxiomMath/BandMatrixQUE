module

public import BlockBand.SourceProcess.RankFree.BirthConstraint
public import BlockBand.SourceProcess.RankFree.LocMartBound

/-!
# Birth columns stay zero until their birth

`sharpFrame_mul_single_zero`: for every birth `k`, almost surely the column `col_k` of the frame
without positive-time births vanishes at `τ_k`. Proof: before `τ_k` this column is the column of
`X`, so `‖Y♯_t E‖²` (`E = E_{col_k col_k}`) has zero Itô drift on `[0, τ_k)`
(`sdeGenerator_normSq_mul_eq_zero`); it starts at `‖ξE‖² = 0`; stopped at `τ_k` it is a nonnegative
`LocMart` with zero drift, so its mean stays `0` (`LocMart.lintegral_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {nb : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- Before its birth, a birth column of `X` is the column of the frame without positive births. -/
theorem mul_single_eq_sharpFrame {Ω : Type*} (X : ℝ≥0 → Ω → Matrix ι c ℂ)
    (τ : Fin nb → Ω → ℝ≥0) {col : Fin nb → c} (hcol : Function.Injective col)
    (w : Fin nb → Ω → ι → ℂ) (k : Fin nb) (x : Ω) (s : ℝ≥0) (hs : s < τ k x) :
    X s x * Matrix.single (col k) (col k) (1 : ℂ) =
      sharpFrame X τ col w s x * Matrix.single (col k) (col k) (1 : ℂ) := by
  rw [X_eq_sharpFrame_add X τ col w s x, Matrix.add_mul, Matrix.sum_mul]
  rw [Finset.sum_eq_zero fun l _ => ?_, add_zero]
  split_ifs with hl
  · rw [birthMat_mul_single]
    split_ifs with he
    · exact absurd ((hcol he) ▸ hl) (not_le.2 hs)
    · rfl
  · exact Matrix.zero_mul _

theorem ae_ne_toNNReal (a : ℝ≥0) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), s.toNNReal ≠ a := by
  have h : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (a : ℝ) := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ioi] with s hs hs0 he
  exact hs (by rw [← he, Real.coe_toNNReal _ (le_of_lt hs0)])

/-- **Birth columns are zero at their birth.** -/
theorem sharpFrame_mul_single_zero {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x))
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ}
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k))
    (hcol : Function.Injective col) (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0)
    (hξcol : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ x i (col k) = 0)
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) (k : Fin nb) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      sharpFrame X τ col w (τ k x) x * Matrix.single (col k) (col k) (1 : ℂ) = 0 := by
  set E := Matrix.single (col k) (col k) (1 : ℂ)
  have hTP := twoProjection_born hD0 hP hD hξ hξ0 hDcol hξcol hX
  have hN := (isNative_sharpFrame hτ hw hX).map_clm ((mulBil (l := ι) (m := c) (n := c)).flip E)
  simp only [ContinuousLinearMap.flip_apply, mulBil_apply] at hN
  have hZ := hN.locMart_disc (contDiff_normSq (k := 2)) 0
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, zero_add] at hZ
  have hS := hZ.stop (hτ k)
  have hS' := hS.congr_drift (β' := fun _ _ => 0) (by
    filter_upwards [hTP] with x hx
    filter_upwards [ae_ne_toNNReal (τ k x)] with s hs
    simp only [switchAfter]
    split_ifs with hle
    · have hlt : s.toNNReal < τ k x := lt_of_le_of_ne (WithTop.coe_le_coe.1 hle) hs
      rw [← mul_single_eq_sharpFrame X τ hcol w k x _ hlt,
        sdeGenerator_normSq_mul_eq_zero hD0.le hP (hx _) E]
    · rfl)
  have hnn : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t,
      0 ≤ stoppedProcess (fun t x => ‖sharpFrame X τ col w t x * E‖ ^ 2) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
        t x := ae_of_all _ fun x t => sq_nonneg _
  have h0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      stoppedProcess (fun t x => ‖sharpFrame X τ col w t x * E‖ ^ 2) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
        0 x = 0 := by
    filter_upwards [sharpFrame_zero hX, hξcol] with x h1 h2
    have hst : stopTime ((τ k x : ℝ≥0) : WithTop ℝ≥0) 0 = 0 :=
      le_antisymm (stopTime_le _ 0) zero_le
    rw [stoppedProcess_eq_stopTime, hst]
    simp only [h1]
    have hzero : ξ x * E = 0 := by
      ext i l
      rw [mul_single_diag_apply, h2 k i]
      simp
    rw [hzero, norm_zero]
    norm_num
  have hn : ∀ n : ℕ, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      stoppedProcess (fun t x => ‖sharpFrame X τ col w t x * E‖ ^ 2) (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
        (n : ℝ≥0) x = 0 := by
    intro n
    have hb := hS'.lintegral_le hnn (ae_of_all _ fun _ t => by simp)
      (hS'.prog.stronglyAdapted 0) n
    have hR : ∫⁻ x, ENNReal.ofReal (stoppedProcess (fun t x => ‖sharpFrame X τ col w t x * E‖ ^ 2)
        (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) 0 x) ∂driverLaw (κ := SourceNoise ι) μ = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [h0] with x hx
      rw [hx, ENNReal.ofReal_zero]
    rw [hR] at hb
    have hm : AEMeasurable (fun x => ENNReal.ofReal (stoppedProcess (fun t x => ‖sharpFrame X τ col w t x * E‖ ^ 2)
        (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) (n : ℝ≥0) x)) (driverLaw (κ := SourceNoise ι) μ) :=
      (ENNReal.measurable_ofReal.comp ((hS'.prog.stronglyAdapted (n : ℝ≥0)).mono
        ((driverAugmented (κ := SourceNoise ι) μ).le _)).measurable).aemeasurable
    have := (lintegral_eq_zero_iff' hm).1 (le_antisymm hb zero_le)
    filter_upwards [this, hnn] with x h1 h2
    exact le_antisymm (ENNReal.ofReal_eq_zero.1 h1) (h2 _)
  filter_upwards [ae_all_iff.2 hn] with x hx
  obtain ⟨n, hnτ⟩ := exists_nat_ge (τ k x : ℝ)
  have hle : τ k x ≤ (n : ℝ≥0) := by exact_mod_cast hnτ
  have h := hx n
  rw [stoppedProcess_eq_stopTime, stopTime_coe, min_eq_right hle] at h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

end BlockBand.SourceProcess.RankFree
