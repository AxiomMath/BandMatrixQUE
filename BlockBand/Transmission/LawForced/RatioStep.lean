module

public import BlockBand.Transmission.LawForced.RatioLog
public import BlockBand.Transmission.LawForced.LayerScalar
public import BlockBand.Transmission.PassiveCovariance.LayerBlocks

/-!
# The pointwise second-order expansion of `F_z` about a diagonal state

Fix `t : n → ℝ` with `0 ≤ t ≤ 1`, `D = diag t`, a matrix `0 ⪯ S ⪯ I`, `B = S − D`,
`R_w = (I + wD)⁻¹` and `h = ‖B‖_HS`. On the range `x ≥ 0`, `0 ≤ y < 1`:
* `logDiag z t = Σ_iΣ_k [log(1−y_it_k) − log(1+x_it_k)]` (`= log F_z(diag t)`);
* `linR z t S = Σ_i [−y_i Re Tr(R_{−y_i}B) − x_i Re Tr(R_{x_i}B)]` (`= −Σ_k Λ_z(t_k) Re B_kk`,
  `linR_eq_linB`, `linB_eq_dualLam`);
* `quadR z t S = Σ_i [(x_i²/2) Re Tr(R_{x_i}BR_{x_i}B) − (y_i²/2) Re Tr(R_{−y_i}BR_{−y_i}B)]`.

Results:
* **`logRatio_expand`**: `|logRatio z S − logDiag z t − linR − quadR| ≤ cubK z · h³`
  (`logDet_sand_expand` at `w = x_i` and `w = −y_i`);
* `abs_quadR_le`: `|quadR| ≤ quadK z · h²`;
* `scalar_step`: the real inequality behind the exponential step;
* **`ratio_step`**: with `F_S = exp(logRatio z S)`, `F_D = exp(logDiag z t)`, `M = |linR| + h`,
  `|F_S − F_D − F_D(linR + quadR + linR²/2)| ≤ 441(1 + quadK + cubK)³(M³ + M⁹)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality
open BlockBand.Transmission.Generator BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}

/-- `log F_z(diag t)`. -/
def logDiag (z : DualCoord p) (t : n → ℝ) : ℝ :=
  ∑ i, ∑ k, (Real.log (1 - z.2 i * t k) - Real.log (1 + z.1 i * t k))

/-- The first-order term. -/
def linR (z : DualCoord p) (t : n → ℝ) (S : Matrix n n ℂ) : ℝ :=
  ∑ i, (-z.2 i * (rres (-z.2 i) t * (S - dmat t)).trace.re -
    z.1 i * (rres (z.1 i) t * (S - dmat t)).trace.re)

/-- The second-order term. -/
def quadR (z : DualCoord p) (t : n → ℝ) (S : Matrix n n ℂ) : ℝ :=
  ∑ i, (z.1 i ^ 2 / 2 * (rres (z.1 i) t * (S - dmat t) * rres (z.1 i) t * (S - dmat t)).trace.re -
    z.2 i ^ 2 / 2 * (rres (-z.2 i) t * (S - dmat t) * rres (-z.2 i) t * (S - dmat t)).trace.re)

/-- The cubic constant. -/
def cubK (z : DualCoord p) : ℝ :=
  ∑ i, (9 * (1 + z.1 i) * z.1 i ^ 3 + 9 / (1 - z.2 i) * (z.2 i / (1 - z.2 i)) ^ 3)

/-- The quadratic constant. -/
def quadK (z : DualCoord p) : ℝ := ∑ i, (z.1 i ^ 2 / 2 + z.2 i ^ 2 / 2 * ((1 - z.2 i)⁻¹) ^ 2)

theorem cubK_nonneg {z : DualCoord p} (hz : IsRatioRange z.1 z.2) : 0 ≤ cubK z :=
  Finset.sum_nonneg fun i _ => by
    have := hz.1 i; have := (hz.2 i).1; have h1 : 0 < 1 - z.2 i := by linarith [(hz.2 i).2]
    positivity

theorem quadK_nonneg (z : DualCoord p) : 0 ≤ quadK z :=
  Finset.sum_nonneg fun i _ => by positivity

/-!
### One log-determinant at `w = x ≥ 0` and at `w = −y`
-/

theorem sqrt_cube_eq {w ρ F : ℝ} (hρ : 0 ≤ ρ) :
    Real.sqrt (w ^ 2 * ρ ^ 2 * F) * (w ^ 2 * ρ ^ 2 * F) =
      (|w| * ρ) ^ 3 * (Real.sqrt F * F) := by
  rw [show w ^ 2 * ρ ^ 2 * F = (|w| * ρ) ^ 2 * F by rw [mul_pow, sq_abs],
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (abs_nonneg _) hρ)]
  ring

theorem ell_x_expand {S : Matrix n n ℂ} (hS : S.PosSemidef) {t : n → ℝ} (ht0 : ∀ k, 0 ≤ t k)
    (ht1 : ∀ k, t k ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    |ellW x S - ∑ k, Real.log (1 + x * t k) - x * (rres x t * (S - dmat t)).trace.re +
        x ^ 2 / 2 * (rres x t * (S - dmat t) * rres x t * (S - dmat t)).trace.re| ≤
      9 * (1 + x) * x ^ 3 * (Real.sqrt (frobSq (S - dmat t)) * frobSq (S - dmat t)) := by
  have hd : ∀ k, 0 < 1 + x * t k := fun k => pos_x hx (ht0 k)
  have hm : ∀ k, (1 + x)⁻¹ ≤ (1 + x * t k)⁻¹ := fun k =>
    inv_anti₀ (hd k) (by nlinarith [ht1 k])
  have hρ : ∀ k, (1 + x * t k)⁻¹ ≤ 1 := fun k =>
    inv_le_one_of_one_le₀ (by nlinarith [ht0 k])
  have hx1 : 0 < 1 + x := by linarith
  have hP : (1 + (x : ℂ) • S - ((1 : ℝ) : ℂ) • 1).PosSemidef := by
    rw [Complex.ofReal_one, one_smul, add_sub_cancel_left]
    exact hS.smul (by exact_mod_cast hx)
  have h := logDet_sand_expand (w := x) hS.1 hd hm hρ zero_le_one (by rw [one_mul]; positivity)
    (by rw [one_mul]; exact inv_le_one_of_one_le₀ (by linarith)) hP
  rw [sqrt_cube_eq zero_le_one, abs_of_nonneg hx, mul_one] at h
  unfold ellW
  refine h.trans (le_of_eq ?_)
  field_simp

theorem ell_y_expand {S : Matrix n n ℂ} (hS : S.PosSemidef) (hS1 : (1 - S).PosSemidef)
    {t : n → ℝ} (ht0 : ∀ k, 0 ≤ t k) (ht1 : ∀ k, t k ≤ 1) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    |ellW (-y) S - ∑ k, Real.log (1 - y * t k) - (-y) * (rres (-y) t * (S - dmat t)).trace.re +
        y ^ 2 / 2 * (rres (-y) t * (S - dmat t) * rres (-y) t * (S - dmat t)).trace.re| ≤
      9 / (1 - y) * (y / (1 - y)) ^ 3 *
        (Real.sqrt (frobSq (S - dmat t)) * frobSq (S - dmat t)) := by
  have hy : 0 < 1 - y := by linarith
  have hd : ∀ k, 0 < 1 + -y * t k := fun k => pos_y hy1 hy0 (ht1 k)
  have hm : ∀ k, 1 ≤ (1 + -y * t k)⁻¹ := fun k =>
    one_le_inv₀ (hd k) |>.2 (by nlinarith [ht0 k])
  have hρ : ∀ k, (1 + -y * t k)⁻¹ ≤ (1 - y)⁻¹ := fun k =>
    inv_anti₀ hy (by nlinarith [ht1 k])
  have hP : (1 + ((-y : ℝ) : ℂ) • S - ((1 - y : ℝ) : ℂ) • 1).PosSemidef := by
    have e : 1 + ((-y : ℝ) : ℂ) • S - ((1 - y : ℝ) : ℂ) • 1 = (y : ℂ) • (1 - S) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      push_cast; split_ifs <;> ring
    rw [e]; exact hS1.smul (by exact_mod_cast hy0)
  have h := logDet_sand_expand (w := -y) hS.1 hd hm hρ hy.le (by rw [mul_one]; exact hy)
    (by rw [mul_one]; linarith) hP
  rw [sqrt_cube_eq (inv_nonneg.2 hy.le), abs_neg, abs_of_nonneg hy0, mul_one, neg_sq] at h
  unfold ellW
  have e2 : ∀ k, Real.log (1 + -y * t k) = Real.log (1 - y * t k) := fun k => by
    rw [neg_mul, ← sub_eq_add_neg]
  simp only [e2] at h
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv y]; ring

/-- **The second-order expansion of `log F_z` about `diag t`.** -/
theorem logRatio_expand {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {S : Matrix n n ℂ}
    (hS : S.PosSemidef) (hS1 : (1 - S).PosSemidef) {t : n → ℝ} (ht0 : ∀ k, 0 ≤ t k)
    (ht1 : ∀ k, t k ≤ 1) :
    |logRatio z S - logDiag z t - linR z t S - quadR z t S| ≤
      cubK z * (Real.sqrt (frobSq (S - dmat t)) * frobSq (S - dmat t)) := by
  set H := Real.sqrt (frobSq (S - dmat t)) * frobSq (S - dmat t)
  have e : logRatio z S - logDiag z t - linR z t S - quadR z t S =
      ∑ i, ((ellW (-z.2 i) S - ∑ k, Real.log (1 - z.2 i * t k) -
          (-z.2 i) * (rres (-z.2 i) t * (S - dmat t)).trace.re +
          z.2 i ^ 2 / 2 * (rres (-z.2 i) t * (S - dmat t) * rres (-z.2 i) t *
            (S - dmat t)).trace.re) -
        (ellW (z.1 i) S - ∑ k, Real.log (1 + z.1 i * t k) -
          z.1 i * (rres (z.1 i) t * (S - dmat t)).trace.re +
          z.1 i ^ 2 / 2 * (rres (z.1 i) t * (S - dmat t) * rres (z.1 i) t *
            (S - dmat t)).trace.re)) := by
    unfold logRatio logDiag linR quadR
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib]; ring
  rw [e, cubK, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (abs_sub _ _).trans ?_
  rw [add_mul, add_comm]
  exact add_le_add (ell_x_expand hS ht0 ht1 (hz.1 i))
    (ell_y_expand hS hS1 ht0 ht1 (hz.2 i).1 (hz.2 i).2)

/-- `|Re Tr(R B R B)| ≤ ρ²‖B‖²_HS` for `R = diag r`, `0 ≤ r ≤ ρ`. -/
theorem abs_re_trace_rBrB_le {w : ℝ} {t : n → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hd : ∀ k, 0 < 1 + w * t k) (hρ : ∀ k, (1 + w * t k)⁻¹ ≤ ρ) (B : Matrix n n ℂ) :
    |(rres w t * B * rres w t * B).trace.re| ≤ ρ ^ 2 * frobSq B := by
  have hn : ‖rres w t‖ ≤ ρ := norm_diagonal_le _ hρ0 fun k => by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hd k).le)]; exact hρ k
  have h := norm_trace_XBYB_le (rres w t) (rres w t) B
  rw [← Matrix.mul_assoc] at h
  refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
  have := norm_nonneg (rres w t)
  have := frobSq_nonneg B
  rw [sq]; gcongr

theorem abs_quadR_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {S : Matrix n n ℂ}
    {t : n → ℝ} (ht0 : ∀ k, 0 ≤ t k) (ht1 : ∀ k, t k ≤ 1) :
    |quadR z t S| ≤ quadK z * frobSq (S - dmat t) := by
  rw [quadR, quadK, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hx := hz.1 i
  have hy0 := (hz.2 i).1
  have hy : 0 < 1 - z.2 i := by linarith [(hz.2 i).2]
  have h1 := abs_re_trace_rBrB_le zero_le_one (fun k => pos_x hx (ht0 k))
    (fun k => inv_le_one_of_one_le₀ (by nlinarith [ht0 k])) (S - dmat t)
  have h2 := abs_re_trace_rBrB_le (inv_nonneg.2 hy.le)
    (fun k => pos_y (hz.2 i).2 hy0 (ht1 k)) (fun k => inv_anti₀ hy (by nlinarith [ht1 k]))
    (S - dmat t)
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ z.1 i ^ 2 / 2),
    abs_of_nonneg (by positivity : 0 ≤ z.2 i ^ 2 / 2), add_mul]
  rw [one_pow, one_mul] at h1
  have hF := frobSq_nonneg (S - dmat t)
  refine add_le_add (by gcongr) ?_
  calc z.2 i ^ 2 / 2 * |_| ≤ z.2 i ^ 2 / 2 * ((1 - z.2 i)⁻¹ ^ 2 * frobSq (S - dmat t)) := by
        gcongr
    _ = _ := by ring

/-!
### The exponential step
-/

theorem pow_le_three_nine {M : ℝ} (hM : 0 ≤ M) {k : ℕ} (h3 : 3 ≤ k) (h9 : k ≤ 9) :
    M ^ k ≤ M ^ 3 + M ^ 9 := by
  rcases le_total M 1 with h | h
  · have := pow_le_pow_of_le_one hM h h3
    linarith [pow_nonneg hM 9]
  · have := pow_le_pow_right₀ h h9
    linarith [pow_nonneg hM 3]

theorem cube_add_le (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : (u + v) ^ 3 ≤ 4 * (u ^ 3 + v ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hu hv) (sq_nonneg (u - v))]

/-- **The scalar exponential step.** -/
theorem scalar_step {F a l q h Kq Kc M A : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hFa : F * Real.exp a ≤ 1) (hh : 0 ≤ h)
    (hq : |q| ≤ Kq * h ^ 2) (he : |a - l - q| ≤ Kc * h ^ 3) (hlM : |l| ≤ M) (hhM : h ≤ M)
    (hA : 1 ≤ A) (hqA : Kq ≤ A) (hcA : Kc ≤ A) :
    |F * Real.exp a - F - F * (l + q + l ^ 2 / 2)| ≤ 441 * A ^ 3 * (M ^ 3 + M ^ 9) := by
  have hM : 0 ≤ M := hh.trans hhM
  have h3 := pow_nonneg hM 3
  have h9 := pow_nonneg hM 9
  have hM2 : M ^ 2 ≤ M + M ^ 3 := by nlinarith [mul_nonneg hM (sq_nonneg (M - 1 / 2))]
  have hM1 : M ≤ M + M ^ 3 := by linarith
  have hM3 : M ^ 3 ≤ M + M ^ 3 := by linarith
  have hq' : |q| ≤ A * (M + M ^ 3) :=
    hq.trans ((mul_le_mul hqA (pow_le_pow_left₀ hh hhM 2) (sq_nonneg _) (by linarith)).trans
      (mul_le_mul_of_nonneg_left hM2 (by linarith)))
  have hqs : |q| ≤ A * M ^ 2 :=
    hq.trans (mul_le_mul hqA (pow_le_pow_left₀ hh hhM 2) (sq_nonneg _) (by linarith))
  generalize hed : a - l - q = e at he
  have he' : |e| ≤ A * M ^ 3 :=
    he.trans (mul_le_mul hcA (pow_le_pow_left₀ hh hhM 3) (pow_nonneg hh 3) (by linarith))
  have he'' : |e| ≤ A * (M + M ^ 3) := he'.trans (mul_le_mul_of_nonneg_left hM3 (by linarith))
  have hlA : |l| ≤ A * (M + M ^ 3) :=
    hlM.trans (by nlinarith [mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ M + M ^ 3)])
  have ha : a = l + q + e := by linarith
  have hX : 0 ≤ M + M ^ 3 := by linarith
  -- `|a| ≤ 3A(M + M³)`
  have hab : |a| ≤ 3 * A * (M + M ^ 3) := by
    rw [ha]
    have : |l + q + e| ≤ |l| + |q| + |e| := (abs_add_le _ _).trans (by
      gcongr; exact abs_add_le _ _)
    linarith
  have ha3 : |a| ^ 3 ≤ 108 * A ^ 3 * (M ^ 3 + M ^ 9) := by
    calc |a| ^ 3 ≤ (3 * A * (M + M ^ 3)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hab 3
      _ = 27 * A ^ 3 * (M + M ^ 3) ^ 3 := by ring
      _ ≤ 27 * A ^ 3 * (4 * (M ^ 3 + (M ^ 3) ^ 3)) := by
          gcongr; exact cube_add_le _ _ hM h3
      _ = _ := by ring
  -- `|a² − l²| ≤ 24A²(M³ + M⁹)`
  have hqe : |q + e| ≤ A * (M ^ 2 + M ^ 3) := by
    have := abs_add_le q e
    nlinarith
  have hsum : |2 * l + q + e| ≤ 4 * A * (M + M ^ 3) := by
    have : |2 * l + q + e| ≤ 2 * |l| + |q| + |e| := by
      rw [add_assoc]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two, add_assoc]; gcongr; exact abs_add_le _ _
    linarith
  have hsq : |a ^ 2 - l ^ 2| ≤ 16 * A ^ 2 * (M ^ 3 + M ^ 9) := by
    have e2 : a ^ 2 - l ^ 2 = (q + e) * (2 * l + q + e) := by rw [ha]; ring
    rw [e2, abs_mul]
    have h4 := pow_le_three_nine hM (k := 4) (by norm_num) (by norm_num)
    have h5 := pow_le_three_nine hM (k := 5) (by norm_num) (by norm_num)
    have h6 := pow_le_three_nine hM (k := 6) (by norm_num) (by norm_num)
    have hA0 : 0 ≤ A := by linarith
    calc |q + e| * |2 * l + q + e| ≤ (A * (M ^ 2 + M ^ 3)) * (4 * A * (M + M ^ 3)) :=
          mul_le_mul hqe hsum (abs_nonneg _) (by positivity)
      _ = 4 * A ^ 2 * (M ^ 3 + M ^ 4 + M ^ 5 + M ^ 6) := by ring
      _ ≤ 4 * A ^ 2 * (4 * (M ^ 3 + M ^ 9)) := by gcongr; linarith
      _ = _ := by ring
  have hstep := abs_exp_step_le hF0 hF1 hFa
  have e3 : F * Real.exp a - F - F * (l + q + l ^ 2 / 2) =
      (F * Real.exp a - F - F * (a + a ^ 2 / 2)) + F * e + F * ((a ^ 2 - l ^ 2) / 2) := by
    rw [ha]; ring
  rw [e3]
  have hA2 : A ^ 2 ≤ A ^ 3 := by
    have := mul_le_mul_of_nonneg_left hA (sq_nonneg A); rw [mul_one] at this
    calc A ^ 2 ≤ A ^ 2 * A := this
      _ = A ^ 3 := by ring
  have hA1 : A ≤ A ^ 3 := by
    have : A ≤ A ^ 2 := by nlinarith
    linarith
  have hFe : |F * e| ≤ A ^ 3 * (M ^ 3 + M ^ 9) := by
    rw [abs_mul, abs_of_nonneg hF0]
    calc F * |e| ≤ 1 * (A * M ^ 3) := mul_le_mul hF1 he' (abs_nonneg _) zero_le_one
      _ ≤ A ^ 3 * (M ^ 3 + M ^ 9) := by
          rw [one_mul]; exact mul_le_mul hA1 (by linarith) h3 (by positivity)
  have hFs : |F * ((a ^ 2 - l ^ 2) / 2)| ≤ 8 * A ^ 3 * (M ^ 3 + M ^ 9) := by
    rw [abs_mul, abs_of_nonneg hF0, abs_div, abs_two]
    calc F * (|a ^ 2 - l ^ 2| / 2) ≤ 1 * (16 * A ^ 2 * (M ^ 3 + M ^ 9) / 2) :=
          mul_le_mul hF1 (by linarith) (by positivity) zero_le_one
      _ ≤ 8 * A ^ 3 * (M ^ 3 + M ^ 9) := by
          have := mul_le_mul_of_nonneg_right hA2 (by positivity : 0 ≤ M ^ 3 + M ^ 9)
          linarith
  have hb : |F * Real.exp a - F - F * (a + a ^ 2 / 2)| ≤ 4 * (108 * A ^ 3 * (M ^ 3 + M ^ 9)) :=
    hstep.trans (by linarith)
  calc |(F * Real.exp a - F - F * (a + a ^ 2 / 2)) + F * e + F * ((a ^ 2 - l ^ 2) / 2)|
      ≤ |F * Real.exp a - F - F * (a + a ^ 2 / 2)| + |F * e| + |F * ((a ^ 2 - l ^ 2) / 2)| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ 432 * A ^ 3 * (M ^ 3 + M ^ 9) + A ^ 3 * (M ^ 3 + M ^ 9) +
        8 * A ^ 3 * (M ^ 3 + M ^ 9) := by linarith
    _ = _ := by ring

theorem logRatio_nonpos {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {S : Matrix n n ℂ}
    (hS : S.PosSemidef) (hS1 : (1 - S).PosSemidef) : logRatio z S ≤ 0 := by
  rw [show logRatio z S = logRatio (z.1, z.2) S from rfl, logRatio_eq_sum hz hS hS1]
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun k _ => ?_
  obtain ⟨h0, h1⟩ := eigenvalues_mem hS hS1 k
  have a := pos_y (hz.2 i).2 (hz.2 i).1 h1
  rw [neg_mul, ← sub_eq_add_neg] at a
  have b1 := Real.log_nonpos a.le (by nlinarith [(hz.2 i).1])
  have b2 := Real.log_nonneg (show 1 ≤ 1 + z.1 i * hS.1.eigenvalues k by nlinarith [hz.1 i])
  linarith

omit [DecidableEq n] in
theorem logDiag_nonpos {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {t : n → ℝ}
    (ht0 : ∀ k, 0 ≤ t k) (ht1 : ∀ k, t k ≤ 1) : logDiag z t ≤ 0 := by
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun k _ => ?_
  have a := pos_y (hz.2 i).2 (hz.2 i).1 (ht1 k)
  rw [neg_mul, ← sub_eq_add_neg] at a
  have b1 := Real.log_nonpos a.le (by nlinarith [(hz.2 i).1, ht0 k])
  have b2 := Real.log_nonneg (show 1 ≤ 1 + z.1 i * t k by nlinarith [hz.1 i, ht0 k])
  linarith

/-- **The pointwise one-step expansion of `F_z`.** -/
theorem ratio_step {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {S : Matrix n n ℂ}
    (hS : S.PosSemidef) (hS1 : (1 - S).PosSemidef) {t : n → ℝ} (ht0 : ∀ k, 0 ≤ t k)
    (ht1 : ∀ k, t k ≤ 1) :
    |Real.exp (logRatio z S) - Real.exp (logDiag z t) -
        Real.exp (logDiag z t) * (linR z t S + quadR z t S + linR z t S ^ 2 / 2)| ≤
      441 * (1 + quadK z + cubK z) ^ 3 *
        ((|linR z t S| + Real.sqrt (frobSq (S - dmat t))) ^ 3 +
          (|linR z t S| + Real.sqrt (frobSq (S - dmat t))) ^ 9) := by
  set h := Real.sqrt (frobSq (S - dmat t))
  have hF := frobSq_nonneg (S - dmat t)
  have hh2 : h ^ 2 = frobSq (S - dmat t) := Real.sq_sqrt hF
  have hh3 : h ^ 3 = h * frobSq (S - dmat t) := by rw [pow_succ', hh2]
  have e : Real.exp (logRatio z S) =
      Real.exp (logDiag z t) * Real.exp (logRatio z S - logDiag z t) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hq := quadK_nonneg z
  have hc := cubK_nonneg hz
  refine scalar_step (Real.exp_pos _).le (Real.exp_le_one_iff.2 (logDiag_nonpos hz ht0 ht1))
    (by rw [← e]; exact Real.exp_le_one_iff.2 (logRatio_nonpos hz hS hS1)) (Real.sqrt_nonneg _)
    (by rw [hh2]; exact abs_quadR_le hz ht0 ht1) ?_ (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    (le_add_of_nonneg_left (abs_nonneg _)) (by linarith) (by linarith) (by linarith)
  rw [hh3]
  have := logRatio_expand hz hS hS1 ht0 ht1
  convert this using 2

end BlockBand.Transmission.LawForced
