module

public import BlockBand.SourceProcess.FullSource.TagIter

/-!
# Removing the stops: the tag moment at one width

* `crude_tag_iter`: `E t_{k+1+m}^q ≤ (C_N^{2q})^m E t_{k+1}^q`;
* `stop_removal`: `E t_j^n ≤ E[1_{G_j}Z_j] + (E t_j^{2n})^{1/2} μ(G_jᶜ)^{1/2}` (Hölder).

Proved in the sibling module from these:
* `superexp_absorbs`: `⌊TW⌋ e^{-cW log W} A^m B ≤ 1` for `m ≤ RW` and `W` large;
* `tag_moment_bound`: the `n`-th moment of a tag at one width from the stopped recursion,
  the crude growth and a bound on `μ(G_jᶜ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem crude_tag_iter {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {q k : ℕ} (hW : 1 ≤ W) (hq : 1 ≤ q) {CN : ℝ} (hCN : 0 ≤ CN)
    (hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * q : ℕ) : ℝ))
        (freshLaw W b) ≤ ENNReal.ofReal CN) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + m) k ω ^ q) ∂growthPathLaw W b ≤
      ENNReal.ofReal (CN ^ (2 * q)) ^ m *
        ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ q) ∂growthPathLaw W b := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k + 1 + (m + 1) = k + 1 + m + 1 by omega]
    refine (crude_tag_step hb0 hb hE1 hE2 (k := k) (j := k + 1 + m) hW hq (by omega) hCN hN).trans ?_
    rw [pow_succ, mul_comm (ENNReal.ofReal _ ^ m), mul_assoc]
    exact mul_le_mul_of_nonneg_left ih zero_le

theorem tagMass_nonneg (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) : 0 ≤ tagMass b E W j k ω := by
  rw [tagMass_eq_past]; exact mul_nonneg (by positivity) (trace_factor_re_nonneg _)

theorem measurableSet_stopEv (b E : ℝ) (k : ℕ) (d : ℝ) (j : ℕ) :
    MeasurableSet (stopEv b E W k d j) := by
  rw [stopEv_eq]; exact (measurableSet_stopPast b E k d j).preimage (measurable_pastCoords W j)

/-- **Removing the stops** by Hölder. -/
theorem stop_removal (b E : ℝ) {k n : ℕ} {K : ℝ} (hK : 0 ≤ K) (d : ℝ) (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ n) ∂growthPathLaw W b ≤
      ∫⁻ ω, (stopEv b E W k d j).indicator (tagWeight b E W k n K j) ω ∂growthPathLaw W b +
        (∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ (2 * n)) ∂growthPathLaw W b) ^ (1 / 2 : ℝ) *
          growthPathLaw W b (stopEv b E W k d j)ᶜ ^ (1 / 2 : ℝ) := by
  set μ := growthPathLaw W b
  set A := stopEv b E W k d j
  set f : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal (tagMass b E W j k ω ^ n)
  have hA := measurableSet_stopEv (W := W) b E k d j
  have hmf : Measurable f := ((measurable_tagMass b E j k).pow_const n).ennreal_ofReal
  have htm : ∀ ω, 0 ≤ tagMass b E W j k ω := tagMass_nonneg b E j k
  have hsplit : (fun ω => f ω) = fun ω => A.indicator f ω + Aᶜ.indicator f ω := by
    funext ω; rw [Set.indicator_self_add_compl_apply]
  rw [show (∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ n) ∂μ) = ∫⁻ ω, f ω ∂μ from rfl, hsplit,
    lintegral_add_left (hmf.indicator hA)]
  have hle : ∀ ω, f ω ≤ tagWeight b E W k n K j ω := by
    intro ω
    refine ENNReal.ofReal_le_ofReal ?_
    have hδ : 0 ≤ pathDelta b E W j ω := norm_nonneg _
    have := pow_nonneg (htm ω) n
    nlinarith [mul_nonneg hK hδ]
  refine add_le_add (lintegral_mono fun ω => Set.indicator_le_indicator (hle ω)) ?_
  · have hg : Measurable (Aᶜ.indicator fun _ : GrowthPath W => (1 : ℝ≥0∞)) :=
      measurable_const.indicator hA.compl
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      hg.aemeasurable hmf.aemeasurable
    have e1 : (fun ω => Aᶜ.indicator f ω) = (Aᶜ.indicator fun _ => (1 : ℝ≥0∞)) * f := by
      funext ω; by_cases h : ω ∈ Aᶜ <;> simp [Set.indicator, h]
    have e2 : ∫⁻ ω, (Aᶜ.indicator fun _ => (1 : ℝ≥0∞)) ω ^ (2 : ℝ) ∂μ = μ Aᶜ := by
      rw [← lintegral_indicator_one hA.compl]
      congr 1; funext ω
      by_cases h : ω ∈ Aᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ENNReal.one_rpow, Pi.one_apply]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
          ENNReal.zero_rpow_of_pos (by norm_num)]
    have e3 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ (2 * n)) ∂μ := by
      congr 1; funext ω
      simp only [f]
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (pow_nonneg (htm ω) n), ← pow_mul, mul_comm]
    rw [e1]
    refine hH.trans (le_of_eq ?_)
    rw [e2, e3, mul_comm]

end BlockBand.SourceProcess.FullSource
