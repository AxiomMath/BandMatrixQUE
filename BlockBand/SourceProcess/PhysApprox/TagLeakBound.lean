module

public import BlockBand.SourceProcess.SmallLeak.LeakExit

/-!
# One tag as an interval source at one width; the summed leakage recursion

The one-step pieces `leak_stopped_step`, `leakBnd_mean_le`, `exit_pointwise` of the leakage
recursion take any nonnegative weight function `q`; only the summation `leak_bound_at` uses the
source-test structure (for its start term). At one width `W`, a single normalized tag born at `k`
is the interval source of the spike `tagTest W k` (value `W` at `(k + 1)/W`, `0` elsewhere):
`Q_n(tagTest W k) = W⁻¹ Y_{n;k}` for `k < n` and `0` otherwise (`intervalSource_tagTest`).

* `tag_leak_bound_at`: the telescoping of `leak_bound_at` for a nonnegative `q` whose source
  vanishes at `n_s`, with a uniform birth weight `c`:
  `E ℓ_{n_T} ≤ (n_T − n_s)P + C_sup/K` in `lintegral` form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.SmallLeak
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The spike weight of one tag born at birth index `k`: `W` at `(k + 1)/W`, `0` elsewhere. -/
def tagTest (W k : ℕ) (x : ℝ) : ℝ := if x = ((k + 1 : ℕ) : ℝ) / W then (W : ℝ) else 0

theorem tagTest_nonneg (W k : ℕ) (x : ℝ) : 0 ≤ tagTest W k x := by
  unfold tagTest; split_ifs <;> positivity

theorem tagTest_le (W k : ℕ) (x : ℝ) : tagTest W k x ≤ W := by
  unfold tagTest; split_ifs <;> simp

theorem tagTest_grid (hW : 1 ≤ W) (k j : ℕ) :
    tagTest W k (((j + 1 : ℕ) : ℝ) / W) = if j = k then (W : ℝ) else 0 := by
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold tagTest
  by_cases hj : j = k
  · subst hj; simp
  · rw [ite_eq_right hj, ite_eq_right]
    intro heq
    have h1 := (div_left_inj' hW0).mp heq
    have h2 : j + 1 = k + 1 := by exact_mod_cast h1
    exact hj (by omega)

/-- **One tag is the interval source of its spike**: `Q_n(tagTest W k) = W⁻¹ Y_{n;k}` if `k < n`,
and `0` otherwise. -/
theorem intervalSource_tagTest (b E : ℝ) (hW : 1 ≤ W) (k n : ℕ) (ω : GrowthPath W) :
    intervalSource b E W n (tagTest W k) ω =
      if k < n then (((W : ℝ)⁻¹ : ℝ) : ℂ) • tagResponse b E W n k ω else 0 := by
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : ∀ j ∈ Finset.range n,
      ((tagTest W k (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) • tagResponse b E W n j ω =
        if j = k then (((W : ℝ)⁻¹ : ℝ) : ℂ) • tagResponse b E W n j ω else 0 := by
    intro j _
    rw [tagTest_grid hW k j]
    by_cases hj : j = k
    · rw [ite_eq_left hj, ite_eq_left hj]
      congr 2
      rw [sq, div_mul_eq_div_div, div_self hW0, one_div]
    · rw [ite_eq_right hj, ite_eq_right hj]; simp
  rw [intervalSource, Finset.sum_congr rfl hc]
  simp only [Finset.sum_ite_eq', Finset.mem_range]

/-- The omitted leakage of the spike is the tag's leakage `Re Tr(F Y_{n;k})/W` for `k < n`. -/
theorem omittedLeak_tagTest {b E h s : ℝ} (hW : 1 ≤ W) {k n : ℕ} (hkn : k < n)
    (ω : GrowthPath W) :
    omittedLeak b E h s (tagTest W k) W n ω =
      (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) * tagResponse b E W n k ω).trace.re /
        W := by
  rw [omittedLeak, intervalSource_tagTest b E hW k n ω, ite_eq_left hkn, farOmitted,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, div_eq_inv_mul]

/-- The trace of the spike source: `W⁻¹ Tr Y_{n;k}` for `k < n`, and `0` otherwise. -/
theorem re_trace_intervalSource_tagTest (b E : ℝ) (hW : 1 ≤ W) (k n : ℕ) (ω : GrowthPath W) :
    (intervalSource b E W n (tagTest W k) ω).trace.re =
      if k < n then (W : ℝ)⁻¹ * (tagResponse b E W n k ω).trace.re else 0 := by
  rw [intervalSource_tagTest b E hW k n ω]
  split_ifs
  · rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  · simp

theorem birthWeight_tagTest_le (hW : 1 ≤ W) (k j : ℕ) :
    birthWeight (tagTest W k) W j ≤ (W : ℝ)⁻¹ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold birthWeight
  calc tagTest W k (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 ≤ (W : ℝ) / (W : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (tagTest_le W k _) (sq_nonneg _)
    _ = (W : ℝ)⁻¹ := by rw [sq, div_mul_eq_div_div, div_self hW0.ne', one_div]

/-- **The summed leakage recursion at one width, for a nonnegative weight without start term.**
The telescoping of `leak_bound_at` with the start replaced by `ℓ_{n_s} = 0` and a uniform birth
weight bound `c`. -/
theorem tag_leak_bound_at {b E h s T : ℝ} {q : ℝ → ℝ} (hq0 : ∀ y, 0 ≤ q y) (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    (hn1 : 1 ≤ ⌊(W : ℝ) * s⌋₊) (hnT : ⌊(W : ℝ) * s⌋₊ ≤ ⌊(W : ℝ) * T⌋₊)
    {K Cm Cf B c D x Csup : ℝ} (hK : 0 < K) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (hB : 0 ≤ B)
    (hc : ∀ j, birthWeight q W j ≤ c) (hD : 0 ≤ D) (hCsup : 0 ≤ Csup)
    (hΔb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      (∀ x y, Integrable (fun f => freshDelta b E X f x y) (freshLaw W b)) ∧
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) ∧
        ∀ u v : Fin W → ℂ, eLpNorm (fun f => bilinear u (freshDelta b E X f -
            matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal 2)
            (freshLaw W b) ≤
          ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u * vecNorm v))
    (hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      Integrable (fun f => ‖freshTransport b E XX f‖ ^ 2) (freshLaw W b))
    (hBb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Integrable (fun f => (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2) (freshLaw W b) ∧
        ∫ f, (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2 ∂freshLaw W b ≤ B)
    (hδ : ∀ j, ⌊(W : ℝ) * s⌋₊ ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
      MomBd (growthPathLaw W b) (pathDelta b E W j) ((4 : ℕ) : ℝ) D)
    (hx : ∀ j, ⌊(W : ℝ) * s⌋₊ ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
      ∫ ω, omittedFlux b E h s W j ω ∂growthPathLaw W b ≤ x)
    (M : GrowthPath W → ℝ≥0∞)
    (hM : ∀ ω i, ⌊(W : ℝ) * s⌋₊ ≤ i → i ≤ ⌊(W : ℝ) * T⌋₊ →
      ENNReal.ofReal (intervalSource b E W i q ω).trace.re ≤ M ω)
    (hMs : ∫⁻ ω, M ω ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal Csup)
    (hstart : ∀ ω, omittedLeak b E h s q W ⌊(W : ℝ) * s⌋₊ ω = 0) :
    ∫⁻ ω, ENNReal.ofReal (omittedLeak b E h s q W ⌊(W : ℝ) * T⌋₊ ω) ∂growthPathLaw W b ≤
      ENNReal.ofReal ((⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * s⌋₊ : ℕ) *
        (K * (Cm / etaZ b E) * (D * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
          K * ((Cm ^ 2 + Cf ^ 2) / etaZ b E ^ 2) * (D ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
          c * B * x / (4 * etaZ b E ^ 2)) + Csup / K) := by
  set μ := growthPathLaw W b
  set ns := ⌊(W : ℝ) * s⌋₊
  set nT := ⌊(W : ℝ) * T⌋₊
  set P := K * (Cm / etaZ b E) * (D * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
    K * ((Cm ^ 2 + Cf ^ 2) / etaZ b E ^ 2) * (D ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
    c * B * x / (4 * etaZ b E ^ 2)
  set L : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, (traceStopEv b E s q K W m).indicator
    (fun ω => ENNReal.ofReal (omittedLeak b E h s q W m ω)) ω ∂μ
  have hbw0 : ∀ j, 0 ≤ birthWeight q W j := fun j => div_nonneg (hq0 _) (sq_nonneg _)
  have hc0 : 0 ≤ c := (hbw0 0).trans (hc 0)
  -- the telescoping
  have htel : ∀ i, ns + i ≤ nT → L (ns + i) ≤ L ns + i * ENNReal.ofReal P := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hstep := leak_stopped_step (h := h) (s := s) q hq0 hb0 hb hE1 hE2 hW (j := ns + i)
        (by omega) (by omega) (K := K) (Cm := Cm) (Cf := Cf) (B := B) hCf hΔb hN hBb
      have hmean := leakBnd_mean_le (h := h) (s := s) (j := ns + i) (K := K) (Cm := Cm) (Cf := Cf)
        (B := B) (c := c) (D := D) (x := x) q hb hE1 hE2 hW (by omega) hK.le hCm hB
        hD (hbw0 _) (hc _) (hδ _ (by omega) (by omega)) (hx _ (by omega) (by omega))
      calc L (ns + (i + 1)) = L (ns + i + 1) := rfl
        _ ≤ L (ns + i) + ENNReal.ofReal P := hstep.trans (add_le_add le_rfl hmean)
        _ ≤ L ns + i * ENNReal.ofReal P + ENNReal.ofReal P := add_le_add (ih (by omega)) le_rfl
        _ = L ns + ((i + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal P := by push_cast; ring
  -- the start
  have hstart' : L ns = 0 := by simp [L, hstart]
  -- the exit
  have hexit : ∫⁻ ω, (traceStopEv b E s q K W nT)ᶜ.indicator
      (fun ω => ENNReal.ofReal (omittedLeak b E h s q W nT ω)) ω ∂μ ≤
        ENNReal.ofReal (Csup / K) := by
    calc _ ≤ ∫⁻ ω, M ω ^ 2 / ENNReal.ofReal K ∂μ :=
          lintegral_mono fun ω => exit_pointwise hq0 hK ω (M ω) (fun i h1 h2 => hM ω i h1 h2)
      _ = (∫⁻ ω, M ω ^ 2 ∂μ) * (ENNReal.ofReal K)⁻¹ := by
          simp only [div_eq_mul_inv]; rw [lintegral_mul_const' _ _ (by simpa using hK)]
      _ ≤ ENNReal.ofReal Csup * (ENNReal.ofReal K)⁻¹ := mul_le_mul_left hMs _
      _ = ENNReal.ofReal (Csup / K) := by
          rw [ENNReal.ofReal_div_of_pos hK, div_eq_mul_inv]
  -- the split
  have hsplit : ∫⁻ ω, ENNReal.ofReal (omittedLeak b E h s q W nT ω) ∂μ ≤
      L nT + ENNReal.ofReal (Csup / K) := by
    refine le_trans ?_ (add_le_add le_rfl hexit)
    rw [← lintegral_add_left ((Measurable.ennreal_ofReal
      (measurable_omittedLeak b E h s q nT)).indicator (measurableSet_traceStopEv b E s q K nT))]
    refine lintegral_mono fun ω => ?_
    by_cases hm : ω ∈ traceStopEv b E s q K W nT
    · simp only [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hm),
        add_zero]; exact le_rfl
    · simp only [Set.indicator_of_notMem hm, Set.indicator_of_mem (Set.mem_compl hm), zero_add]
      exact le_rfl
  have hP0 : 0 ≤ P := by
    have := Real.sqrt_nonneg x
    have : 0 ≤ x := by
      have := hx ns le_rfl hnT
      exact (integral_nonneg fun ω => omittedFlux_nonneg b E h s W ns ω).trans this
    have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
    positivity
  have hfin := htel (nT - ns) (by omega)
  rw [show ns + (nT - ns) = nT by omega, hstart', zero_add] at hfin
  calc _ ≤ L nT + ENNReal.ofReal (Csup / K) := hsplit
    _ ≤ ((nT - ns : ℕ) : ℝ≥0∞) * ENNReal.ofReal P + ENNReal.ofReal (Csup / K) :=
        add_le_add hfin le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end BlockBand.SourceProcess.PhysApprox
