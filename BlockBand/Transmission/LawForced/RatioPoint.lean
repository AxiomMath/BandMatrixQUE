module

public import BlockBand.Transmission.LawForced.RatioLin
public import BlockBand.Transmission.Generator.StepInputs

/-!
# The `κ ≡ 0` one-layer `F_z` drift: combination of the exact means

One fresh layer at a deterministic passive `X`, `T = T(X)`, `t = ts_lam hT`, `U = LL*`,
`Ū = E U`, `S = sand T U`, `B̄ = sand T Ū − diag t`, `a = D₀/(2W)`, `Λ_k = Λ_z(t_k)`,
`M = |linR z t S| + ‖S − diag t‖_HS` (`ratioMf`).
* `measurable_logRatio`;
* `freshU_hp2` (the `(i,i),(m,m)` covariance products are integrable);
* `ratio_combine` (real algebra);
* **`ratio_layer_split`**: `|E F_z(T(X₊)) − F_z(T) − ratioDrift D₀ E 0 u z μ_T / W|` is at most
  `441(1+quadK+cubK)³E(M³+M⁹)` plus the five deterministic brackets
  `|linB B̄ − a(Σt)ΣtΛ|`, `|quadB B̄|`, `(linB B̄)²/2`,
  `|quadMean − aΣ_i(x_i²/2·quadMain(x_i) − y_i²/2·quadMain(−y_i))|`,
  `|Re covV/2 − aΣt²(1−t)Λ²|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {p W : ℕ}

/-- `M = |linR| + ‖S − diag t‖_HS`. -/
def ratioMf {n : Type*} [Fintype n] [DecidableEq n] (z : DualCoord p) (t : n → ℝ)
    (S : Matrix n n ℂ) : ℝ :=
  |linR z t S| + Real.sqrt (frobSq (S - dmat t))

theorem measurable_ellW {n : Type*} [Fintype n] [DecidableEq n] (w : ℝ) :
    Measurable (ellW (n := n) w) := by
  unfold ellW
  refine Real.measurable_log.comp (Complex.measurable_re.comp ?_)
  have hc : Continuous fun M : Matrix n n ℂ => (1 + (w : ℂ) • M) :=
    continuous_const.add (continuous_const_smul _)
  exact hc.matrix_det.measurable

theorem measurable_logRatio {n : Type*} [Fintype n] [DecidableEq n] (z : DualCoord p) :
    Measurable (logRatio (n := n) z) := by
  unfold logRatio
  exact Finset.measurable_sum _ fun i _ => (measurable_ellW _).sub (measurable_ellW _)

/-- The diagonal covariance products are integrable. -/
theorem freshU_hp2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUm : Measurable U) (h2 : Integrable (fun ω => ‖U ω‖ ^ 2) μ) (i m : Fin W) :
    Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i i *
      ts_ent hT (U ω - matrixExpect μ U) m m) μ := by
  have hZ : Measurable fun ω => U ω - matrixExpect μ U := hUm.sub_const _
  refine Integrable.mono' ((h2.const_mul 2).add (integrable_const (2 * ‖matrixExpect μ U‖ ^ 2)))
    ((ts_measurable_ent hT hZ i i).mul (ts_measurable_ent hT hZ m m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  show ‖_ * _‖ ≤ 2 * ‖U ω‖ ^ 2 + 2 * ‖matrixExpect μ U‖ ^ 2
  rw [norm_mul]
  have a1 := ts_norm_ent_le hT (U ω - matrixExpect μ U) i i
  have a2 := ts_norm_ent_le hT (U ω - matrixExpect μ U) m m
  have a3 := norm_sub_le (U ω) (matrixExpect μ U)
  have := mul_le_mul a1 a2 (norm_nonneg _) (norm_nonneg _)
  have := mul_le_mul a3 a3 (norm_nonneg _) (by positivity)
  nlinarith [norm_nonneg (U ω), norm_nonneg (matrixExpect μ U),
    sq_nonneg (‖U ω‖ - ‖matrixExpect μ U‖)]

/-- The real combination behind `ratio_layer_split`. -/
theorem ratio_combine {Fs FD EY lb qb qm cv a gL QM V R1 : ℝ} (hF0 : 0 ≤ FD) (hF1 : FD ≤ 1)
    (h1 : |Fs - FD - FD * EY| ≤ R1) (hY : EY = lb + qb + lb ^ 2 / 2 + qm + cv / 2) :
    |Fs - FD - FD * (a * (gL + QM + V))| ≤
      R1 + (|lb - a * gL| + |qb| + lb ^ 2 / 2 + |qm - a * QM| + |cv / 2 - a * V|) := by
  have e : Fs - FD - FD * (a * (gL + QM + V)) = (Fs - FD - FD * EY) +
      FD * ((lb - a * gL) + qb + lb ^ 2 / 2 + (qm - a * QM) + (cv / 2 - a * V)) := by
    rw [hY]; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add h1 ?_)
  rw [abs_mul, abs_of_nonneg hF0]
  have hs : |(lb - a * gL) + qb + lb ^ 2 / 2 + (qm - a * QM) + (cv / 2 - a * V)| ≤
      |lb - a * gL| + |qb| + lb ^ 2 / 2 + |qm - a * QM| + |cv / 2 - a * V| := by
    have := abs_add_le ((lb - a * gL) + qb + lb ^ 2 / 2 + (qm - a * QM)) (cv / 2 - a * V)
    have := abs_add_le ((lb - a * gL) + qb + lb ^ 2 / 2) (qm - a * QM)
    have := abs_add_le ((lb - a * gL) + qb) (lb ^ 2 / 2)
    have := abs_add_le (lb - a * gL) qb
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ lb ^ 2 / 2)] at *
    linarith
  calc FD * |_| ≤ 1 * |(lb - a * gL) + qb + lb ^ 2 / 2 + (qm - a * QM) + (cv / 2 - a * V)| :=
        mul_le_mul_of_nonneg_right hF1 (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hs

/-- The five deterministic brackets of the one-layer mean. -/
def ratioBr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : Matrix (Fin W) (Fin W) ℂ}
    (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ) (z : DualCoord p) (a : ℝ) : ℝ :=
  |linB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT)) -
      a * ((∑ k, ts_lam hT k) * ∑ k, ts_lam hT k * dualLam z (ts_lam hT k))| +
    |quadB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT))| +
    linB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT)) ^ 2 / 2 +
    |quadMean μ hT U z - a * ∑ i, (z.1 i ^ 2 / 2 * quadMain (ts_lam hT) (z.1 i) -
      z.2 i ^ 2 / 2 * quadMain (ts_lam hT) (-z.2 i))| +
    |(covV μ hT U z).re / 2 -
      a * ∑ k, ts_lam hT k ^ 2 * (1 - ts_lam hT k) * dualLam z (ts_lam hT k) ^ 2|

/-- **The one-layer `F_z` drift, split into the expansion remainder and five brackets.** -/
theorem ratio_layer_split {z : DualCoord p} (hz : z ∈ dualChamber p) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hW : 1 ≤ W) (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) (hT : (passiveTransmission b E X).PosSemidef)
    (hUi : ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b))
    (hU2 : Integrable (fun ω => ‖freshU b E X ω‖ ^ 2) (freshLaw W b))
    (hM : Integrable (fun ω => ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 3 +
      ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 9) (freshLaw W b)) (u : ℝ) :
    |∫ ω, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (freshSchur E X ω)))
        ∂freshLaw W b - transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) -
        ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E X)) / W| ≤
      441 * (1 + quadK z + cubK z) ^ 3 *
          ∫ ω, (ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 3 +
            ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 9) ∂freshLaw W b +
        ratioBr (freshLaw W b) hT (freshU b E X) z (transportD0 b E / (2 * W)) := by
  have hzr : IsRatioRange z.1 z.2 := IsRatioParameter.isRatioRange hz
  set μ := freshLaw W b
  set U := freshU b E X
  set t := ts_lam hT
  have h1T := one_sub_passiveTransmission_posSemidef b E X
  have ht1 : ∀ k, t k ≤ 1 := ts_lam_le_one hT h1T
  have ht0 : ∀ k, 0 ≤ t k := ts_lam_nonneg hT
  have hUm : Measurable U := measurable_freshU b E X
  have hUH : ∀ ω, (U ω).IsHermitian := fun ω => (posSemidef_self_mul_conjTranspose _).1
  obtain ⟨hYi, hYe⟩ := integral_ratio_terms hT U hUi hUH (freshU_hp hT U hUm hU2)
    (freshU_hp2 hT U hUm hU2) z
  have hFD : transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) =
      Real.exp (logDiag z t) := transmissionRatio_eq_exp_logDiag hzr hT h1T
  have hae := ae_fresh_transmissionRatio hzr hb0 hb hW h1 h2 hX hT
  have hSm : Measurable fun ω => sand hT (U ω) := (continuous_sand hT).measurable.comp hUm
  have hFSm : Measurable fun ω => Real.exp (logRatio z (sand hT (U ω))) :=
    Real.measurable_exp.comp ((measurable_logRatio z).comp hSm)
  have hFSi : Integrable (fun ω => Real.exp (logRatio z (sand hT (U ω)))) μ := by
    refine Integrable.of_bound hFSm.aestronglyMeasurable 1 ?_
    filter_upwards [hae] with ω ⟨hS, hS1, _⟩
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (logRatio_nonpos hzr hS hS1)
  have hint : ∫ ω, transmissionRatio z.1 z.2
      (traceMeasure (passiveTransmission b E (freshSchur E X ω))) ∂μ =
      ∫ ω, Real.exp (logRatio z (sand hT (U ω))) ∂μ :=
    integral_congr_ae (hae.mono fun ω h => h.2.2)
  set FD := Real.exp (logDiag z t)
  have hpt : ∀ᵐ ω ∂μ, |(Real.exp (logRatio z (sand hT (U ω))) - FD) -
      FD * (linR z t (sand hT (U ω)) + quadR z t (sand hT (U ω)) +
        linR z t (sand hT (U ω)) ^ 2 / 2)| ≤
      441 * (1 + quadK z + cubK z) ^ 3 * (ratioMf z t (sand hT (U ω)) ^ 3 +
        ratioMf z t (sand hT (U ω)) ^ 9) := by
    filter_upwards [hae] with ω ⟨hS, hS1, _⟩
    exact ratio_step hzr hS hS1 ht0 ht1
  have hR1 : |∫ ω, Real.exp (logRatio z (sand hT (U ω))) ∂μ - FD -
      FD * ∫ ω, (linR z t (sand hT (U ω)) + quadR z t (sand hT (U ω)) +
        linR z t (sand hT (U ω)) ^ 2 / 2) ∂μ| ≤
      441 * (1 + quadK z + cubK z) ^ 3 * ∫ ω, (ratioMf z t (sand hT (U ω)) ^ 3 +
        ratioMf z t (sand hT (U ω)) ^ 9) ∂μ := by
    have i1 : Integrable (fun ω => Real.exp (logRatio z (sand hT (U ω))) - FD) μ :=
      hFSi.sub (integrable_const _)
    have i2 : Integrable (fun ω => FD * (linR z t (sand hT (U ω)) + quadR z t (sand hT (U ω)) +
        linR z t (sand hT (U ω)) ^ 2 / 2)) μ := hYi.const_mul FD
    have e : ∫ ω, Real.exp (logRatio z (sand hT (U ω))) ∂μ - FD -
        FD * ∫ ω, (linR z t (sand hT (U ω)) + quadR z t (sand hT (U ω)) +
          linR z t (sand hT (U ω)) ^ 2 / 2) ∂μ =
        ∫ ω, ((Real.exp (logRatio z (sand hT (U ω))) - FD) -
          FD * (linR z t (sand hT (U ω)) + quadR z t (sand hT (U ω)) +
            linR z t (sand hT (U ω)) ^ 2 / 2)) ∂μ := by
      rw [integral_sub i1 i2, integral_sub hFSi (integrable_const _), integral_const,
        probReal_univ, one_smul, integral_const_mul]
    rw [e, ← integral_const_mul]
    exact (abs_integral_le_integral_abs).trans (integral_mono_ae (i1.sub i2).abs
      (hM.const_mul _) hpt)
  rw [hint, ← ratio_main_term hz hT h1T (transportD0 b E) E u W, hFD]
  exact ratio_combine (Real.exp_pos _).le (Real.exp_le_one_iff.2 (logDiag_nonpos hzr ht0 ht1))
    hR1 hYe

end BlockBand.Transmission.LawForced
