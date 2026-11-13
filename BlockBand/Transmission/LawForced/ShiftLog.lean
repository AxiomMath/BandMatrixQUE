module

public import BlockBand.Transmission.LawForced.RatioPoint
public import BlockBand.Transmission.LawForced.RatioLip

/-!
# The first-order shift of `F_z` between two contractions

For `0 ⪯ T, T' ⪯ I` (`W × W`), `t` the eigenvalues of `T`, `g = Re Tr T`, `‖T' − T‖ ≤ n₁`,
`R = Σ_i (x_i + y_i)`:
* `eigConj` (`V*MV` in the eigenbasis of `T`), `eigConj_self` (`V*TV = diag t`), invariance of
  `ℓ_w` and of `Tr`;
* **`logRatio_shift_le`**: `|log F(T') − log F(T) + R Re Tr(T' − T)| ≤ shiftErr`,
  `shiftErr = lamLip·g·n₁ + quadK·n₁²W + cubK·(n₁²W)^{3/2}` (`logRatio_expand` at
  `S = V*T'V`; the linear term is `−Σ_kΛ_z(t_k)Re(T'−T)'_{kk}` and `|Λ_z(t) − R| ≤ lamLip·t`);
* **`ratio_shift_le`**: `|F(T') − F(T) + R F(T) Re Tr(T' − T)| ≤ e + M²/2 + 4M³`,
  `e = shiftErr`, `M = R|Re Tr(T' − T)| + e` (`abs_exp_step_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

/-- `V*MV`, `V` the eigenbasis of `T`. -/
def eigConj (hT : T.PosSemidef) (M : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  star (ts_U hT) * M * ts_U hT

theorem eigConj_self (hT : T.PosSemidef) : eigConj hT T = dmat (ts_lam hT) := by
  unfold eigConj
  have h := congrArg (fun M => star (ts_U hT) * M * ts_U hT) (ts_spectral hT)
  rw [h]
  simp only [← Matrix.mul_assoc, ts_U_star_mul hT, Matrix.one_mul]
  rw [Matrix.mul_assoc, ts_U_star_mul hT, Matrix.mul_one]
  rfl

theorem eigConj_sub (hT : T.PosSemidef) (M N : Matrix (Fin W) (Fin W) ℂ) :
    eigConj hT (M - N) = eigConj hT M - eigConj hT N := by
  unfold eigConj; rw [Matrix.mul_sub, Matrix.sub_mul]

theorem eigConj_posSemidef (hT : T.PosSemidef) {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.PosSemidef) : (eigConj hT M).PosSemidef := by
  have h := hM.conjTranspose_mul_mul_same (ts_U hT)
  rwa [← Matrix.star_eq_conjTranspose] at h

theorem one_sub_eigConj (hT : T.PosSemidef) (M : Matrix (Fin W) (Fin W) ℂ) :
    1 - eigConj hT M = eigConj hT (1 - M) := by
  unfold eigConj; rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ts_U_star_mul hT]

theorem ellW_eigConj (hT : T.PosSemidef) (w : ℝ) (M : Matrix (Fin W) (Fin W) ℂ) :
    ellW w (eigConj hT M) = ellW w M := by
  unfold ellW eigConj
  have e : 1 + (w : ℂ) • (star (ts_U hT) * M * ts_U hT) =
      star (ts_U hT) * (1 + (w : ℂ) • M) * ts_U hT := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ts_U_star_mul hT, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm (star (ts_U hT)).det, mul_assoc,
    ← Matrix.det_mul, ts_U_star_mul hT, Matrix.det_one, mul_one]

theorem logRatio_eigConj (hT : T.PosSemidef) (z : DualCoord p) (M : Matrix (Fin W) (Fin W) ℂ) :
    logRatio z (eigConj hT M) = logRatio z M := by
  unfold logRatio; simp only [ellW_eigConj]

theorem trace_eigConj (hT : T.PosSemidef) (M : Matrix (Fin W) (Fin W) ℂ) :
    (eigConj hT M).trace = M.trace := by
  unfold eigConj
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ts_U_mul_star hT, Matrix.one_mul]

theorem norm_eigConj_le (hT : T.PosSemidef) (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖eigConj hT M‖ ≤ ‖M‖ := by
  unfold eigConj
  have h1 : ‖ts_U hT‖ ≤ 1 := norm_unitary_le (ts_U_star_mul hT)
  have h2 : ‖star (ts_U hT)‖ ≤ 1 := norm_unitary_le (by rw [star_star]; exact ts_U_mul_star hT)
  refine (norm_mul_le _ _).trans ?_
  have h3 : ‖star (ts_U hT) * M‖ ≤ ‖M‖ :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg M, norm_nonneg (star (ts_U hT))])
  nlinarith [norm_nonneg (star (ts_U hT) * M), norm_nonneg (ts_U hT)]

theorem dualLam_zero (z : DualCoord p) : dualLam z 0 = ∑ i, (z.1 i + z.2 i) := by
  simp [dualLam, Finset.sum_add_distrib]

/-- The error of the first-order shift of `log F`. -/
def shiftErr (z : DualCoord p) (g n₁ : ℝ) (W : ℕ) : ℝ :=
  lamLip z * g * n₁ + quadK z * (n₁ ^ 2 * W) +
    cubK z * (Real.sqrt (n₁ ^ 2 * W) * (n₁ ^ 2 * W))

theorem shiftErr_nonneg {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {g n₁ : ℝ} (hg : 0 ≤ g)
    (hn : 0 ≤ n₁) : 0 ≤ shiftErr z g n₁ W := by
  unfold shiftErr
  have := lamLip_nonneg hz; have := quadK_nonneg z; have := cubK_nonneg hz
  positivity

/-- The linear term of the shift. -/
theorem linR_shift_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (hT1 : (1 - T).PosSemidef) (T' : Matrix (Fin W) (Fin W) ℂ) {n₁ : ℝ} (hn : ‖T' - T‖ ≤ n₁) :
    |linR z (ts_lam hT) (eigConj hT T') + (∑ i, (z.1 i + z.2 i)) * (T' - T).trace.re| ≤
      lamLip z * T.trace.re * n₁ := by
  set t := ts_lam hT
  set B := eigConj hT (T' - T)
  have hB : eigConj hT T' - dmat t = B := by
    show eigConj hT T' - dmat (ts_lam hT) = eigConj hT (T' - T)
    rw [eigConj_sub, eigConj_self]
  have htr : (T' - T).trace.re = ∑ k, (B k k).re := by
    rw [← trace_eigConj hT, Matrix.trace, Complex.re_sum]; rfl
  have e : linR z t (eigConj hT T') + (∑ i, (z.1 i + z.2 i)) * (T' - T).trace.re =
      ∑ k, (dualLam z 0 - dualLam z (t k)) * (B k k).re := by
    rw [show linR z t (eigConj hT T') = linB z t (eigConj hT T' - dmat t) from rfl, hB,
      linB_eq_dualLam, htr, ← dualLam_zero, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, ← ts_sum_lam hT, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hm := eigenvalues_mem hT hT1 k
  have h1 : |dualLam z 0 - dualLam z (t k)| ≤ lamLip z * t k := by
    rw [abs_sub_comm]; exact abs_dualLam_sub_le hz hm.1 hm.2
  have h2 : |(B k k).re| ≤ n₁ :=
    ((Complex.abs_re_le_norm _).trans (norm_entry_le B k k)).trans
      ((norm_eigConj_le hT _).trans hn)
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (lamLip_nonneg hz) hm.1)

/-- **The first-order shift of `log F_z`.** -/
theorem logRatio_shift_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (hT1 : (1 - T).PosSemidef) {T' : Matrix (Fin W) (Fin W) ℂ} (hT' : T'.PosSemidef)
    (hT1' : (1 - T').PosSemidef) {n₁ : ℝ} (hn : ‖T' - T‖ ≤ n₁) :
    |logRatio z T' - logRatio z T + (∑ i, (z.1 i + z.2 i)) * (T' - T).trace.re| ≤
      shiftErr z T.trace.re n₁ W := by
  set t := ts_lam hT
  set S := eigConj hT T'
  have hS : S.PosSemidef := eigConj_posSemidef hT hT'
  have hS1 : (1 - S).PosSemidef := by rw [one_sub_eigConj]; exact eigConj_posSemidef hT hT1'
  have hm := eigenvalues_mem hT hT1
  have hexp := logRatio_expand hz hS hS1 (t := t) (fun k => (hm k).1) (fun k => (hm k).2)
  have hquad := abs_quadR_le hz (S := S) (t := t) (fun k => (hm k).1) (fun k => (hm k).2)
  have hlin := linR_shift_le hz hT hT1 T' hn
  have hD : logRatio z T = logDiag z t := by
    show logRatio (z.1, z.2) T = _
    rw [logRatio_eq_sum hz hT hT1]; rfl
  have hfr : frobSq (S - dmat t) ≤ n₁ ^ 2 * W := by
    rw [show S - dmat t = eigConj hT (T' - T) by rw [eigConj_sub, eigConj_self]]
    refine (frobSq_le_card _).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg W))
    have := norm_eigConj_le hT (T' - T)
    exact pow_le_pow_left₀ (norm_nonneg _) (this.trans hn) 2
  have hfr0 := frobSq_nonneg (S - dmat t)
  have hc3 : Real.sqrt (frobSq (S - dmat t)) * frobSq (S - dmat t) ≤
      Real.sqrt (n₁ ^ 2 * W) * (n₁ ^ 2 * W) :=
    mul_le_mul (Real.sqrt_le_sqrt hfr) hfr hfr0 (Real.sqrt_nonneg _)
  have e : logRatio z T' - logRatio z T + (∑ i, (z.1 i + z.2 i)) * (T' - T).trace.re =
      (logRatio z S - logDiag z t - linR z t S - quadR z t S) +
        (linR z t S + (∑ i, (z.1 i + z.2 i)) * (T' - T).trace.re) + quadR z t S := by
    rw [logRatio_eigConj, hD]; ring
  rw [e]
  have k1 := mul_le_mul_of_nonneg_left hc3 (cubK_nonneg hz)
  have k2 := mul_le_mul_of_nonneg_left hfr (quadK_nonneg z)
  unfold shiftErr
  have := abs_add_three (logRatio z S - logDiag z t - linR z t S - quadR z t S)
    (linR z t S + (∑ i, (z.1 i + z.2 i)) * (T' - T).trace.re) (quadR z t S)
  linarith

/-- **The first-order shift of `F_z`.** -/
theorem ratio_shift_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (hT1 : (1 - T).PosSemidef) {T' : Matrix (Fin W) (Fin W) ℂ} (hT' : T'.PosSemidef)
    (hT1' : (1 - T').PosSemidef) {n₁ : ℝ} (hn : ‖T' - T‖ ≤ n₁) :
    |transmissionRatio z.1 z.2 (traceMeasure T') - transmissionRatio z.1 z.2 (traceMeasure T) +
        (∑ i, (z.1 i + z.2 i)) * transmissionRatio z.1 z.2 (traceMeasure T) *
          (T' - T).trace.re| ≤
      shiftErr z T.trace.re n₁ W +
        ((∑ i, (z.1 i + z.2 i)) * |(T' - T).trace.re| + shiftErr z T.trace.re n₁ W) ^ 2 / 2 +
        4 * ((∑ i, (z.1 i + z.2 i)) * |(T' - T).trace.re| +
          shiftErr z T.trace.re n₁ W) ^ 3 := by
  set R := ∑ i, (z.1 i + z.2 i)
  set e := shiftErr z T.trace.re n₁ W
  set τ := (T' - T).trace.re
  set L := logRatio z T
  set L' := logRatio z T'
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => by
    have := hz.1 i; have := (hz.2 i).1; linarith
  have hL := logRatio_nonpos hz hT hT1
  have hL' := logRatio_nonpos hz hT' hT1'
  have hF : transmissionRatio z.1 z.2 (traceMeasure T) = Real.exp L :=
    transmissionRatio_traceMeasure_exp hz hT hT1
  have hF' : transmissionRatio z.1 z.2 (traceMeasure T') = Real.exp L' :=
    transmissionRatio_traceMeasure_exp hz hT' hT1'
  set Δ := L' - L
  have hE' : Real.exp L' = Real.exp L * Real.exp Δ := by rw [← Real.exp_add]; congr 1; ring
  have hlog := logRatio_shift_le hz hT hT1 hT' hT1' hn
  have hΔ : |Δ| ≤ R * |τ| + e := by
    have : |Δ| ≤ |Δ + R * τ| + |R * τ| := by
      have := abs_sub (Δ + R * τ) (R * τ); simp only [add_sub_cancel_right] at this; exact this
    rw [abs_mul, abs_of_nonneg hR] at this; linarith
  have hF0 : 0 ≤ Real.exp L := (Real.exp_pos _).le
  have hF1 : Real.exp L ≤ 1 := Real.exp_le_one_iff.2 hL
  have hstep := abs_exp_step_le hF0 hF1 (by rw [← hE']; exact Real.exp_le_one_iff.2 hL')
  rw [hF, hF', hE']
  have e2 : Real.exp L * Real.exp Δ - Real.exp L + R * Real.exp L * τ =
      (Real.exp L * Real.exp Δ - Real.exp L - Real.exp L * (Δ + Δ ^ 2 / 2)) +
        Real.exp L * (Δ + R * τ) + Real.exp L * (Δ ^ 2 / 2) := by ring
  rw [e2]
  have a2 : |Real.exp L * (Δ + R * τ)| ≤ e := by
    rw [abs_mul, abs_of_nonneg hF0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hF1).trans hlog
  have hM0 : 0 ≤ R * |τ| + e := le_trans (abs_nonneg _) hΔ
  have hsq : Δ ^ 2 ≤ (R * |τ| + e) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  have hcb : |Δ| ^ 3 ≤ (R * |τ| + e) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hΔ 3
  have a3 : |Real.exp L * (Δ ^ 2 / 2)| ≤ (R * |τ| + e) ^ 2 / 2 := by
    rw [abs_mul, abs_of_nonneg hF0, abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_left (by positivity) hF1).trans (by linarith)
  have := abs_add_three (Real.exp L * Real.exp Δ - Real.exp L - Real.exp L * (Δ + Δ ^ 2 / 2))
    (Real.exp L * (Δ + R * τ)) (Real.exp L * (Δ ^ 2 / 2))
  linarith

end BlockBand.Transmission.LawForced
