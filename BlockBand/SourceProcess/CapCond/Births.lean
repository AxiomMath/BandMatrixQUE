module

public import BlockBand.SourceProcess.CapCond.Riemann
public import BlockBand.SourceProcess.SourceProcessLaw.Sampling

/-!
# Birth laws: grid sampling against `birthTimeLaw`

For a source test `q` on `[s,T]` (`0 < s`):
* `tendsto_gridMass`: `gridMass W ⌊WT⌋ q → sourceMass s T q` (`m = Σ_j q_j/W → ∫_s^T q`);
* `tendsto_integral_tagSample` (`m > 0`): for continuous `f`, the grid birth time `(k+1)/W` of a
  tag `k ~ tagSampleLaw W ⌊WT⌋ q` satisfies `E f((k+1)/W) → ∫ f d birthTimeLaw s T q`
  (sampling probabilities `q_j/(Wm)`; continuum density `q/m`);
* `gridMass_eq_zero` (`m = 0`): the test vanishes on `[s,T]`, so every grid mass is `0` and the
  tag law is `δ₀` (the model law is `δ_s`, and the probe weight `d_* m/M` is `0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal

variable {s T : ℝ} {q : ℝ → ℝ}

/-- **Grid masses converge to the source mass.** -/
theorem tendsto_gridMass (hq : IsSourceTest s T q) (hs : 0 < s) (hsT : s ≤ T) :
    Tendsto (fun W : ℕ => gridMass W ⌊(W : ℝ) * T⌋₊ q) atTop (𝓝 (sourceMass s T q)) :=
  tendsto_gridSum hs hsT hq.2.2 hq.2.1

theorem measurable_sourceTest (hq : IsSourceTest s T q) : Measurable q := by
  classical
  have e : q = (Set.Icc s T).piecewise q (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ Set.Icc s T
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, hq.2.1 x hx]
  rw [e]
  exact hq.2.2.measurable_piecewise continuousOn_const measurableSet_Icc

/-- The integral against the model birth law (`m > 0`). -/
theorem integral_birthTimeLaw (hq : IsSourceTest s T q) (hm : 0 < sourceMass s T q)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂birthTimeLaw s T q = (∫ x in Set.Icc s T, q x * f x) / sourceMass s T q := by
  rw [birthTimeLaw, ite_eq_left hm, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (q x / sourceMass s T q))
    (ENNReal.measurable_ofReal.comp ((measurable_sourceTest hq).div_const _))
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (hq.1 x) hm.le)]
  ring

/-- The integral against the tag law (`gridMass > 0`). -/
theorem integral_tagSampleLaw {W n : ℕ} (hq0 : ∀ x, 0 ≤ q x) (hg : 0 < gridMass W n q)
    (F : ℕ → ℝ) :
    ∫ k, F k ∂tagSampleLaw W n q =
      (∑ k ∈ Finset.range n, q (((k + 1 : ℕ) : ℝ) / W) * F k / W) / gridMass W n q := by
  rw [tagSampleLaw, ite_eq_left hg, integral_finsetSum_measure fun k _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  have hW : (0 : ℝ) < W := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · simp [gridMass, h0] at hg
    · exact_mod_cast h0
  rw [ENNReal.toReal_ofReal (div_nonneg (hq0 _) (mul_nonneg hW.le hg.le))]
  field_simp

/-- **Birth laws converge** (`m > 0`): `E f((k+1)/W) → ∫ f d birthTimeLaw`. -/
theorem tendsto_integral_tagSample (hq : IsSourceTest s T q) (hs : 0 < s) (hsT : s ≤ T)
    (hm : 0 < sourceMass s T q) {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun W : ℕ => ∫ k, f (((k + 1 : ℕ) : ℝ) / W) ∂tagSampleLaw W ⌊(W : ℝ) * T⌋₊ q)
      atTop (𝓝 (∫ x, f x ∂birthTimeLaw s T q)) := by
  have hG := tendsto_gridMass hq hs hsT
  have hS := tendsto_gridSum (g := fun x => q x * f x) hs hsT (hq.2.2.mul hf.continuousOn)
    (fun x hx => by simp [hq.2.1 x hx])
  rw [integral_birthTimeLaw hq hm]
  refine (hS.div hG hm.ne').congr' ?_
  filter_upwards [hG.eventually (lt_mem_nhds hm)] with W hW
  rw [integral_tagSampleLaw hq.1 hW]
  rfl

/-- **Zero mass**: the test vanishes on `[s,T]`, hence everywhere, and every grid mass is `0`. -/
theorem eq_zero_of_sourceMass (hq : IsSourceTest s T q) (hsT : s < T)
    (hm : sourceMass s T q = 0) (x : ℝ) : q x = 0 := by
  by_cases hx : x ∈ Set.Icc s T
  · have hae : q =ᵐ[volume.restrict (Set.Icc s T)] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hq.1)
        ((hq.2.2.integrableOn_compact isCompact_Icc))).1 hm
    have := Measure.eqOn_Icc_of_ae_eq (μ := volume) hsT.ne hae hq.2.2 continuousOn_const
    exact this hx
  · exact hq.2.1 x hx

theorem gridMass_eq_zero (hq : IsSourceTest s T q) (hsT : s < T) (hm : sourceMass s T q = 0)
    (W n : ℕ) : gridMass W n q = 0 := by
  simp [gridMass, eq_zero_of_sourceMass hq hsT hm]

end BlockBand.SourceProcess.CapCond
