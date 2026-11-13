module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegLimit
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegCompYMain
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerIdent
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerLimit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Almost sure convergence of the regularized Euler schemes

Setting: a `DegSetup c W P`; `degX S m t = X^{m, nSel S m}_t`, the Euler scheme of grid `m`
driven by the Brownian motion `Bd (nSel S m)` (`DegLimit`).

* `ae_cauchySeq_of_sq_le`: `E|X_{m+1} - X_m|² ≤ K 2^{-m}` gives a.s. Cauchy sequences.
* **`tendsto_degLim`**: for every `t`, a.s. `degX S m t → degLim S t` (`lintegral_degX_sub_le`
  with `degErrX_le`, `degErr_nSel_le`).
* **`degLim_eq_of_le`**: for every `t`, a.s. on `{t ≤ τ}`, `degLim S t = Y_t`
  (Fatou with `lintegral_degX_stop_sub_le`).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

variable {d : ℕ} {c : LipCoef d} {W : Set (Fin d → ℝ)} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A.s. Cauchy sequences from geometric `L²` increments.** -/
theorem ae_cauchySeq_of_sq_le {X : ℕ → Ω → Fin d → ℝ} (hX : ∀ m, Measurable (X m)) {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ m, ∫⁻ ω, ∑ i, ‖X (m + 1) ω i - X m ω i‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (K / 2 ^ m)) : ∀ᵐ ω ∂P, CauchySeq fun m => X m ω := by
  set Z : ℕ → Ω → ℝ≥0∞ := fun m ω => ‖X (m + 1) ω - X m ω‖ₑ
  have hZm : ∀ m, Measurable (Z m) := fun m => ((hX (m + 1)).sub (hX m)).enorm
  set a : ℕ → ℝ := fun m => √K * (1 / √2) ^ m
  have ha0 : ∀ m, 0 ≤ a m := fun m => by positivity
  have hsq2 : (0 : ℝ) < √2 := by positivity
  have ha : Summable a := (summable_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one hsq2]; exact Real.one_lt_sqrt_two)).mul_left _
  have hbound : ∀ m, ∫⁻ ω, Z m ω ∂P ≤ ENNReal.ofReal (a m) := fun m => by
    have h1 := NativeSDE.lintegral_sq_le_measure_mul (m := P) (hZm m).aemeasurable
    rw [measure_univ, one_mul] at h1
    have h2 : ∫⁻ ω, Z m ω ^ 2 ∂P ≤ ENNReal.ofReal (K / 2 ^ m) :=
      (lintegral_mono fun ω => enorm_le_of_sq _).trans (h m)
    have h3 : ENNReal.ofReal (K / 2 ^ m) = ENNReal.ofReal (a m) ^ 2 := by
      rw [← ENNReal.ofReal_pow (ha0 m)]
      congr 1
      simp only [a]
      rw [mul_pow, Real.sq_sqrt hK, ← pow_mul, mul_comm m 2, pow_mul, div_pow, one_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_pow, div_eq_mul_inv]
    rw [h3] at h2
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 (h1.trans h2)
  have hsum : ∫⁻ ω, ∑' m, Z m ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun m => (hZm m).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 ha]
    exact ENNReal.ofReal_ne_top
  have hTm : Measurable fun ω => ∑' m, Z m ω := by
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact .iSup fun s => s.measurable_fun_sum fun i _ => hZm i
  filter_upwards [ae_lt_top hTm hsum] with ω hω
  have hs : Summable fun m => dist (X m ω) (X m.succ ω) := by
    have := ENNReal.summable_toReal hω.ne
    refine this.congr fun m => ?_
    simp only [Z, toReal_enorm]
    rw [dist_comm, dist_eq_norm]
  exact cauchySeq_of_summable_dist hs

/-- The `m`-th regularized Euler scheme. -/
def degX (S : DegSetup c W P) (m : ℕ) (t : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  eulX c m S.ξ (S.Bd (nSel S m)) t ω

theorem measurable_degX (S : DegSetup c W P) (m : ℕ) (t : ℝ≥0) : Measurable (degX S m t) := by
  have hBm := S.measW (nSel S m)
  exact measurable_eulX c m (fun t => (hBm t).mono (S.𝓕.le t) le_rfl)
    (fun j => (measurable_eulE c m hBm S.hξ j).mono (S.𝓕.le _) le_rfl) t

theorem ofReal_div_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    ENNReal.ofReal (a / 2 ^ m) + ENNReal.ofReal (b / 2 ^ m) = ENNReal.ofReal ((a + b) / 2 ^ m) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_div]

theorem lintegral_degX_succ_le (S : DegSetup c W P) {N m : ℕ} (hNm : N ≤ m) {t : ℝ≥0}
    (ht : t ≤ N) : ∫⁻ ω, ∑ i, ‖degX S (m + 1) t ω i - degX S m t ω i‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (gronCI N (degLip c) * ((2 * (N * eulDelta c) + 4) / 2 ^ m)) := by
  have hδ := eulDelta_nonneg c
  have hG := gronCI_nonneg (N : ℝ≥0) (degLip c)
  refine (lintegral_degX_sub_le S (m + 1) m (nSel S (m + 1)) (nSel S m) N t ht).trans ?_
  rw [ENNReal.ofReal_mul hG]
  gcongr
  have e1 : ENNReal.ofReal (N * (eulDelta c / 2 ^ (m + 1))) ≤
      ENNReal.ofReal (N * eulDelta c / 2 ^ m) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc]
    gcongr
    · norm_num
    · omega
  have e2 : degErrX S (nSel S (m + 1)) (nSel S m) N ≤
      ENNReal.ofReal (2 / 2 ^ m) + ENNReal.ofReal (2 / 2 ^ m) := by
    refine (degErrX_le S _ _ N).trans ?_
    have h1 := degErr_nSel_le S (N := N) (m := m + 1) (by omega)
    have h2 := degErr_nSel_le S (N := N) (m := m) hNm
    have h3 : ENNReal.ofReal (1 / 2 ^ (m + 1)) ≤ ENNReal.ofReal (1 / 2 ^ m) :=
      ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega)))
    have h4 : 2 * ENNReal.ofReal (1 / 2 ^ m) = ENNReal.ofReal (2 / 2 ^ m) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), mul_one_div]
    calc 2 * degErr S (nSel S (m + 1)) N + 2 * degErr S (nSel S m) N
        ≤ 2 * ENNReal.ofReal (1 / 2 ^ m) + 2 * ENNReal.ofReal (1 / 2 ^ m) := by
          gcongr
          exact h1.trans h3
      _ = _ := by rw [h4]
  have e3 : ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) = ENNReal.ofReal (N * eulDelta c / 2 ^ m) := by
    rw [mul_div_assoc]
  calc ENNReal.ofReal (N * (eulDelta c / 2 ^ (m + 1))) + ENNReal.ofReal (N * (eulDelta c / 2 ^ m)) +
        degErrX S (nSel S (m + 1)) (nSel S m) N
      ≤ ENNReal.ofReal (N * eulDelta c / 2 ^ m) + ENNReal.ofReal (N * eulDelta c / 2 ^ m) +
          (ENNReal.ofReal (2 / 2 ^ m) + ENNReal.ofReal (2 / 2 ^ m)) := by
        rw [e3]; gcongr
    _ = _ := by
        rw [ofReal_div_add _ _ (by positivity) (by positivity),
          ofReal_div_add _ _ (by positivity) (by positivity),
          ofReal_div_add _ _ (by positivity) (by positivity)]
        congr 2; ring

/-- The limit of the regularized Euler schemes. -/
def degLim (S : DegSetup c W P) (t : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  limUnder atTop fun m => degX S m t ω

theorem natCeil_ge (t : ℝ≥0) : t ≤ ((⌈(t : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _

/-- **The regularized Euler schemes converge almost surely.** -/
theorem tendsto_degLim (S : DegSetup c W P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun m => degX S m t ω) atTop (𝓝 (degLim S t ω)) := by
  set N := ⌈(t : ℝ)⌉₊
  have htN := natCeil_ge t
  set K : ℝ := gronCI N (degLip c) * (2 * (N * eulDelta c) + 4)
  have hK : 0 ≤ K := mul_nonneg (gronCI_nonneg _ _) (by have := eulDelta_nonneg c; positivity)
  have hC := ae_cauchySeq_of_sq_le (P := P) (X := fun m => degX S (N + m) t)
    (fun m => measurable_degX S _ t) hK fun m => by
      refine (lintegral_degX_succ_le S (m := N + m) (by omega) htN).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_left hK (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
  filter_upwards [hC] with ω hω
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hω
  have hv' : Tendsto (fun m => degX S (m + N) t ω) atTop (𝓝 v) := by
    simpa only [add_comm] using hv
  exact tendsto_nhds_limUnder ⟨v, (tendsto_add_atTop_iff_nat N).1 hv'⟩

/-- **The limit is the stopped solution before `τ`.** -/
theorem degLim_eq_of_le (S : DegSetup c W P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (t : WithTop ℝ≥0) ≤ S.τ ω → degLim S t ω = S.Y t ω := by
  set N := ⌈(t : ℝ)⌉₊
  have htN := natCeil_ge t
  have hG : MeasurableSet {ω | (t : WithTop ℝ≥0) ≤ S.τ ω} := measurableSet_le measurable_const
    S.hτ.measurable'
  set f : ℕ → Ω → ℝ≥0∞ := fun m => {ω | (t : WithTop ℝ≥0) ≤ S.τ ω}.indicator
    fun ω => ∑ i, ‖degX S m t ω i - S.Y t ω i‖ₑ ^ 2
  have hfm : ∀ m, Measurable (f m) := fun m => Measurable.indicator
    (Finset.measurable_sum _ fun i _ => ((((measurable_pi_apply i).comp
      (measurable_degX S m t)).sub ((measurable_pi_apply i).comp (S.hYm t))).enorm
        |>.pow_const 2)) hG
  have hbd : ∀ m, N ≤ m → ∫⁻ ω, f m ω ∂P ≤ ENNReal.ofReal (gronCI N (degLip c)) *
      ENNReal.ofReal ((N * eulDelta c + 1) / 2 ^ m) := fun m hm => by
    have h1 := lintegral_degX_stop_sub_le S m (nSel S m) N t htN
    have h2 := degErr_nSel_le S hm
    refine le_trans (lintegral_mono fun ω => ?_) (h1.trans ?_)
    · simp only [f, indicator_apply, mem_ofPred_eq]
      split_ifs with h
      · rw [stopTime_of_le h]; rfl
      · exact zero_le
    · gcongr
      rw [← ofReal_div_add _ _ (by have := eulDelta_nonneg c; positivity) (by norm_num),
        mul_div_assoc]
      gcongr
  have hlim : ∀ᵐ ω ∂P, liminf (fun m => f m ω) atTop = {ω | (t : WithTop ℝ≥0) ≤ S.τ ω}.indicator
      (fun ω => ∑ i, ‖degLim S t ω i - S.Y t ω i‖ₑ ^ 2) ω := by
    filter_upwards [tendsto_degLim S t] with ω hω
    refine Tendsto.liminf_eq ?_
    simp only [f, indicator_apply, mem_ofPred_eq]
    split_ifs
    · refine tendsto_finsetSum _ fun i _ => ?_
      have h1 : Tendsto (fun m => degX S m t ω i - S.Y t ω i) atTop
          (𝓝 (degLim S t ω i - S.Y t ω i)) :=
        ((continuous_apply i).continuousAt.tendsto.comp hω).sub_const _
      exact (ENNReal.continuous_pow 2).continuousAt.tendsto.comp
        (continuous_enorm.continuousAt.tendsto.comp h1)
    · exact tendsto_const_nhds
  have h0 : ∫⁻ ω, liminf (fun m => f m ω) atTop ∂P = 0 := by
    refine le_antisymm ((lintegral_liminf_le hfm).trans ?_) zero_le
    refine (liminf_le_liminf (eventually_atTop.2 ⟨N, hbd⟩)).trans ?_
    rw [(tendsto_const_div_two_pow _ _).liminf_eq]
  rw [lintegral_eq_zero_iff (Measurable.liminf hfm)] at h0
  filter_upwards [h0, hlim] with ω h1 h2 ht
  rw [h2] at h1
  simp only [Pi.zero_apply, indicator_apply, mem_ofPred_eq, ht, ite_true] at h1
  rw [Finset.sum_eq_zero_iff] at h1
  funext i
  have := h1 i (Finset.mem_univ i)
  rw [pow_eq_zero_iff two_ne_zero, enorm_eq_zero, sub_eq_zero] at this
  exact this

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
