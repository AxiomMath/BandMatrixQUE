module

public import BlockBand.SourceProcess.SmallLeak.LeakSum
public import BlockBand.SourceProcess.FullSourceStops.SupMoments

/-!
# The exits of the summed leakage recursion

* `omittedLeak_nonneg`, `omittedLeak_le_trace`: `0 ≤ ℓ ≤ Tr Q`;
* `exit_pointwise`: `1_{S_nᶜ} ℓ_n ≤ M²/K` pointwise, `M = sup Tr Q_j`, hence
  `E[1_{S_{n_T}ᶜ} ℓ_{n_T}] ≤ E[M²]/K` ("source trace exits are paid by fixed moments … a second
  moment pays their final contribution");
* `intervalSource_start`: at `n_s` only the source born at `n_s - 1` can be present.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingLeak
open scoped ENNReal Matrix

variable {W : ℕ}

theorem omittedLeak_nonneg {b E h s : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (j : ℕ)
    (ω : GrowthPath W) : 0 ≤ omittedLeak b E h s q W j ω := by
  obtain ⟨R, hR⟩ := BlockBand.Transmission.PassiveCovariance.exists_conjTranspose_mul_self
    (intervalSource_psd b E j hq ω)
  have hF : (farOmitted b E h s W ω)ᴴ = farOmitted b E h s W ω := farOmitted_conjTranspose _ _ _ _ _ _
  have hF2 : farOmitted b E h s W ω * farOmitted b E h s W ω = farOmitted b E h s W ω := by
    rw [farOmitted, farEmbed_mul, omittedProj_mul_self]
  rw [omittedLeak, ← trace_proj_sandwich hF2, hR]
  have : farOmitted b E h s W ω * (Rᴴ * R) * farOmitted b E h s W ω =
      (R * farOmitted b E h s W ω)ᴴ * (R * farOmitted b E h s W ω) := by
    simp only [Matrix.conjTranspose_mul, hF, Matrix.mul_assoc]
  rw [this]; exact FullSource.trace_factor_re_nonneg _

theorem omittedLeak_le_trace {b E h s : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (j : ℕ)
    (ω : GrowthPath W) :
    omittedLeak b E h s q W j ω ≤ (intervalSource b E W j q ω).trace.re := by
  have hF2 : farOmitted b E h s W ω * farOmitted b E h s W ω = farOmitted b E h s W ω := by
    rw [farOmitted, farEmbed_mul, omittedProj_mul_self]
  exact re_trace_proj_mul_le hF2 (farOmitted_conjTranspose _ _ _ _ _ _)
    (intervalSource_psd b E j hq ω)

/-- **The trace exit**: pointwise `1_{Sᶜ} ℓ_n ≤ M²/K` when the sup `M` covers `[n_s, n]`. -/
theorem exit_pointwise {b E h s : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K : ℝ} (hK : 0 < K)
    {n : ℕ} (ω : GrowthPath W) (M : ℝ≥0∞)
    (hM : ∀ i, ⌊(W : ℝ) * s⌋₊ ≤ i → i ≤ n → ENNReal.ofReal (intervalSource b E W i q ω).trace.re ≤ M) :
    (traceStopEv b E s q K W n)ᶜ.indicator (fun ω => ENNReal.ofReal (omittedLeak b E h s q W n ω)) ω ≤
      M ^ 2 / ENNReal.ofReal K := by
  by_cases hω : ω ∈ (traceStopEv b E s q K W n)ᶜ
  · rw [Set.indicator_of_mem hω]
    simp only [traceStopEv, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨i, hi1, hi2, hK'⟩ := hω
    have hKM : ENNReal.ofReal K ≤ M :=
      (ENNReal.ofReal_le_ofReal hK'.le).trans (hM i hi1 hi2)
    have hn : ⌊(W : ℝ) * s⌋₊ ≤ n := hi1.trans hi2
    have hℓ : ENNReal.ofReal (omittedLeak b E h s q W n ω) ≤ M :=
      (ENNReal.ofReal_le_ofReal (omittedLeak_le_trace hq n ω)).trans (hM n hn le_rfl)
    refine hℓ.trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hK)) (Or.inl ENNReal.ofReal_ne_top), sq]
    exact mul_le_mul_right hKM M
  · rw [Set.indicator_of_notMem hω]; exact zero_le

/-- At `n_s` only the source born at `n_s - 1` can be present: `Tr Q_{n_s} ≤ (Q/W²)Tr Y_{n_s;n_s-1}`. -/
theorem intervalSource_start {b E s T : ℝ} {q : ℝ → ℝ} (hq : IsSourceTest s T q) {Q : ℝ}
    (hQ : ∀ x, q x ≤ Q) (hW : 1 ≤ W) (hn : 1 ≤ ⌊(W : ℝ) * s⌋₊) (ω : GrowthPath W) :
    (intervalSource b E W ⌊(W : ℝ) * s⌋₊ q ω).trace.re ≤
      Q / (W : ℝ) ^ 2 * (tagResponse b E W ⌊(W : ℝ) * s⌋₊ (⌊(W : ℝ) * s⌋₊ - 1) ω).trace.re := by
  set n := ⌊(W : ℝ) * s⌋₊
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [re_trace_intervalSource]
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hm, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, show m + 1 - 1 = m by omega]
  · have hY : 0 ≤ (tagResponse b E W (m + 1) m ω).trace.re := by
      rw [FullSource.tagResponse_eq_factor]; exact FullSource.trace_factor_re_nonneg _
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hQ _) (by positivity)) hY
  · intro k hk
    have hk' : k + 1 < m + 1 := by simpa using Finset.mem_range.mp hk
    have hlt : ((k + 1 : ℕ) : ℝ) / W < s := by
      rw [div_lt_iff₀ hW0]
      have h1 : ((k + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by rw [hm]; exact_mod_cast hk'
      have h2 : (n : ℝ) ≤ W * s := Nat.floor_le (by
        rcases le_or_gt 0 s with h | h
        · positivity
        · exfalso; have : (W : ℝ) * s < 0 := mul_neg_of_pos_of_neg hW0 h
          have := Nat.floor_eq_zero.mpr (by linarith : (W : ℝ) * s < 1); omega)
      linarith
    rw [hq.2.1 _ (fun h => absurd h.1 (not_le.mpr hlt)), zero_div, zero_mul]

end BlockBand.SourceProcess.SmallLeak
