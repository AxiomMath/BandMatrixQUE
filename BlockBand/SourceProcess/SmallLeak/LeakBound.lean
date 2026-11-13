module

public import BlockBand.SourceProcess.SmallLeak.LeakExit

/-!
# The summed leakage recursion at one width

`leak_bound_at`: telescoping `leak_stopped_step` over `[n_s, n_T)` with `leakBnd_mean_le`, the
start `intervalSource_start` and the exit `exit_pointwise`:
`E ℓ_{n_T} ≤ (Q/W)C_tag + (n_T − n_s)P + C_sup/K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.Bridge
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The summed leakage recursion at one width.** -/
theorem leak_bound_at {b E h s T : ℝ} {q : ℝ → ℝ} (hq : IsSourceTest s T q) (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    (hn1 : 1 ≤ ⌊(W : ℝ) * s⌋₊) (hnT : ⌊(W : ℝ) * s⌋₊ ≤ ⌊(W : ℝ) * T⌋₊)
    {K Cm Cf B Q D x Ctag Csup : ℝ} (hK : 0 < K) (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (hB : 0 ≤ B)
    (hQ0 : 0 ≤ Q) (hQ : ∀ y, q y ≤ Q) (hD : 0 ≤ D) (hCtag : 0 ≤ Ctag) (hCsup : 0 ≤ Csup)
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
    (htag : ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * (tagResponse b E W ⌊(W : ℝ) * s⌋₊
      (⌊(W : ℝ) * s⌋₊ - 1) ω).trace.re) ∂growthPathLaw W b ≤ ENNReal.ofReal Ctag) :
    ∫ ω, omittedLeak b E h s q W ⌊(W : ℝ) * T⌋₊ ω ∂growthPathLaw W b ≤
      Q / W * Ctag + (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * s⌋₊ : ℕ) *
        (K * (Cm / etaZ b E) * (D * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
          K * ((Cm ^ 2 + Cf ^ 2) / etaZ b E ^ 2) * (D ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
          Q / (W : ℝ) ^ 2 * B * x / (4 * etaZ b E ^ 2)) + Csup / K := by
  set μ := growthPathLaw W b
  set ns := ⌊(W : ℝ) * s⌋₊
  set nT := ⌊(W : ℝ) * T⌋₊
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set P := K * (Cm / etaZ b E) * (D * Real.sqrt x + Real.sqrt x * (W : ℝ)⁻¹) +
    K * ((Cm ^ 2 + Cf ^ 2) / etaZ b E ^ 2) * (D ^ 2 * Real.sqrt (W * x) + x * (W : ℝ)⁻¹) +
    Q / (W : ℝ) ^ 2 * B * x / (4 * etaZ b E ^ 2)
  set L : ℕ → ℝ≥0∞ := fun m => ∫⁻ ω, (traceStopEv b E s q K W m).indicator
    (fun ω => ENNReal.ofReal (omittedLeak b E h s q W m ω)) ω ∂μ
  have hq0 : ∀ y, 0 ≤ q y := hq.1
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
        (B := B) (c := Q / (W : ℝ) ^ 2) (D := D) (x := x) q hb hE1 hE2 hW (by omega) hK.le hCm hB
        hD (div_nonneg (hq0 _) (sq_nonneg _)) (div_le_div_of_nonneg_right (hQ _) (sq_nonneg _))
        (hδ _ (by omega) (by omega)) (hx _ (by omega) (by omega))
      calc L (ns + (i + 1)) = L (ns + i + 1) := rfl
        _ ≤ L (ns + i) + ENNReal.ofReal P := hstep.trans (add_le_add le_rfl hmean)
        _ ≤ L ns + i * ENNReal.ofReal P + ENNReal.ofReal P := add_le_add (ih (by omega)) le_rfl
        _ = L ns + ((i + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal P := by push_cast; ring
  -- the start
  have hstart : L ns ≤ ENNReal.ofReal (Q / W * Ctag) := by
    calc L ns ≤ ∫⁻ ω, ENNReal.ofReal (Q / W * ((W : ℝ)⁻¹ * (tagResponse b E W ns (ns - 1) ω).trace.re))
          ∂μ := by
          refine lintegral_mono fun ω => ?_
          refine (Set.indicator_le_self _ _ ω).trans (ENNReal.ofReal_le_ofReal ?_)
          refine (omittedLeak_le_trace hq0 ns ω).trans ((intervalSource_start hq hQ hW hn1 ω).trans
            (le_of_eq ?_))
          field_simp
          rfl
      _ = ENNReal.ofReal (Q / W) * ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ *
          (tagResponse b E W ns (ns - 1) ω).trace.re) ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1; funext ω; rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Q / W) * ENNReal.ofReal Ctag := mul_le_mul_right htag _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  -- the exit
  have hexit : ∫⁻ ω, (traceStopEv b E s q K W nT)ᶜ.indicator
      (fun ω => ENNReal.ofReal (omittedLeak b E h s q W nT ω)) ω ∂μ ≤ ENNReal.ofReal (Csup / K) := by
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
    rw [← lintegral_add_left ((Measurable.ennreal_ofReal (measurable_omittedLeak b E h s q nT)).indicator
      (measurableSet_traceStopEv b E s q K nT))]
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
  rw [show ns + (nT - ns) = nT by omega] at hfin
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (omittedLeak_nonneg hq0 nT))
    (measurable_omittedLeak b E h s q nT).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ L nT + ENNReal.ofReal (Csup / K) := hsplit
    _ ≤ ENNReal.ofReal (Q / W * Ctag) + ((nT - ns : ℕ) : ℝ≥0∞) * ENNReal.ofReal P +
          ENNReal.ofReal (Csup / K) := add_le_add (hfin.trans (add_le_add hstart le_rfl)) le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end BlockBand.SourceProcess.SmallLeak
