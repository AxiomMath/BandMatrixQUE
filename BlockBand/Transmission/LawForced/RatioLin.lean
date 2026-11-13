module

public import BlockBand.Transmission.LawForced.RatioMain

/-!
# The deterministic first-order mean `linB B̄` against the weighted mean of `ubarMean_bulk`

With `t = ts_lam hT`, `Λ_k = Λ_z(t_k)`, `G = gW hT Λ` (`⪰ 0` on the chamber range,
`gW_dualLam_posSemidef`) and any `Ū`, `c`:
* `linB_mean_eq`: `linB z t (sand T Ū − diag t) = −Re(Tr(GŪ) − Tr G)`;
* **`abs_linB_mean_sub_le`**:
  `|linB z t (sand T Ū − diag t) − (1 − c)Σ_k t_kΛ_k| ≤ ‖Tr(GŪ) − c·Tr G‖`.
The right side is exactly what part (b) of `ubarMean_bulk` bounds by `C·wmErr b E X G`.

The two ends of the one-layer step in the `RatioStep` variables:
* `transmissionRatio_eq_exp_logDiag`: `F_z(traceMeasure T) = exp(logDiag z (ts_lam hT))`;
* **`ae_fresh_transmissionRatio`**: one fresh layer at a passive `X`, a.s.
  `F_z(traceMeasure T(X₊)) = exp(logRatio z S)` with `S = sand T (LL*)`, `0 ⪯ S ⪯ I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality
open BlockBand.Transmission.Generator BlockBand.Transmission.SourceMixing
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open MeasureTheory
open scoped ComplexOrder

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

theorem dualLam_nonneg {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ dualLam z t := by
  unfold dualLam
  refine add_nonneg (Finset.sum_nonneg fun i _ => div_nonneg (hz.1 i) (pos_x (hz.1 i) ht0).le)
    (Finset.sum_nonneg fun i _ => div_nonneg (hz.2 i).1 ?_)
  have := pos_y (hz.2 i).2 (hz.2 i).1 ht1
  rw [neg_mul, ← sub_eq_add_neg] at this; exact this.le

theorem gW_dualLam_posSemidef {z : DualCoord p} (hz : IsRatioRange z.1 z.2)
    (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) :
    (gW hT fun k => dualLam z (ts_lam hT k)).PosSemidef :=
  gW_posSemidef hT fun k => dualLam_nonneg hz (ts_lam_nonneg hT k) (ht1 k)

theorem linB_mean_eq (z : DualCoord p) (hT : T.PosSemidef) (Ub : Matrix (Fin W) (Fin W) ℂ) :
    linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT)) =
      -((gW hT fun k => dualLam z (ts_lam hT k)) * Ub -
        gW hT fun k => dualLam z (ts_lam hT k)).trace.re := by
  rw [linB_eq_dualLam, Matrix.trace_sub, trace_gW_mul, trace_gW, Complex.sub_re, Complex.re_sum,
    Complex.ofReal_re, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, sand_apply, Real.mul_self_sqrt (ts_lam_nonneg hT k), dmat,
    Matrix.diagonal_apply_eq, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    Complex.ofReal_re]
  ring

/-- **The first-order mean against the weighted mean of `Ū`.** -/
theorem abs_linB_mean_sub_le (z : DualCoord p) (hT : T.PosSemidef)
    (Ub : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) :
    |linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT)) -
        (1 - c) * ∑ k, ts_lam hT k * dualLam z (ts_lam hT k)| ≤
      ‖((gW hT fun k => dualLam z (ts_lam hT k)) * Ub).trace -
        (c : ℂ) * (gW hT fun k => dualLam z (ts_lam hT k)).trace‖ := by
  set G := gW hT fun k => dualLam z (ts_lam hT k)
  have hG : G.trace = ((∑ k, ts_lam hT k * dualLam z (ts_lam hT k) : ℝ) : ℂ) := trace_gW hT _
  have e : linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT)) -
      (1 - c) * ∑ k, ts_lam hT k * dualLam z (ts_lam hT k) =
      -((G * Ub).trace - (c : ℂ) * G.trace).re := by
    rw [linB_mean_eq, Matrix.trace_sub, Complex.sub_re, Complex.sub_re, hG, Complex.re_ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [e, abs_neg]
  exact Complex.abs_re_le_norm _

theorem transmissionRatio_eq_exp_logDiag {z : DualCoord p} (hz : IsRatioRange z.1 z.2)
    (hT : T.PosSemidef) (h1 : (1 - T).PosSemidef) :
    transmissionRatio z.1 z.2 (traceMeasure T) = Real.exp (logDiag z (ts_lam hT)) := by
  rw [transmissionRatio_traceMeasure_exp hz hT h1, logRatio_eq_sum hz hT h1]
  rfl

/-- **The fresh-layer value of `F_z` in the `RatioStep` variables.** -/
theorem ae_fresh_transmissionRatio {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ} (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, (sand hT (freshU b E X ω)).PosSemidef ∧
      (1 - sand hT (freshU b E X ω)).PosSemidef ∧
      transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (freshSchur E X ω))) =
        Real.exp (logRatio z (sand hT (freshU b E X ω))) := by
  filter_upwards [ae_fresh_ratio hb0 hb hW h1 h2 hY hT, ae_transmission_fresh hb0 hb hW h1 h2 hY]
    with ω ⟨hS, hS1, hell⟩ hTp
  refine ⟨hS, hS1, ?_⟩
  have hP : (passiveTransmission b E (freshSchur E X ω)).PosSemidef := by
    rw [hTp]; exact hT.conjTranspose_mul_mul_same _
  rw [transmissionRatio_traceMeasure_exp hz hP (one_sub_passiveTransmission_posSemidef b E _)]
  congr 1
  unfold logRatio
  simp only [hell]

end BlockBand.Transmission.LawForced
