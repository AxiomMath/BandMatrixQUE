module

public import BlockBand.Endpoints.Clock.DetLaplace
public import BlockBand.Endpoints.Clock.DetClockCovariance

/-!
# The deterministic-clock lemma: the transported determinant and its second-order Taylor remainder

We prove the following deterministic estimate used in the deterministic-clock lemma.

> The determinant lemma expresses the transported ratio as
> `F_a(L*QL)/F_a(Q) = det(I + A_a^{1/2} U A_a^{1/2})⁻¹`. [...] On the event where its full
> Hilbert–Schmidt norm is at most 1/2 and its trace has modulus at most one, the logarithm and
> exponential Taylor expansions through second order have remainder bounded by
> `C F_a(Q)(‖A_a^{1/2}UA_a^{1/2}‖_HS³ + |Tr(A_aU)|³)`.

For `Q ⪰ 0`, `a ≥ 0`, any `L`, `U = LL* - I`,
`A = A_a = aQ(I + aQ)⁻¹` (`resolventWeight`):

* `det_transport`: `det(I + aL*QL) = det(I + aQ) det(I + AU)` (Sylvester and
  `I + aQ(I + U) = (I + aQ)(I + AU)`);
* `psdSqrt`: the square root `S = A^{1/2}` of `A ⪰ 0` from the spectral theorem;
  `det(I + AU) = det(I + SUS)`, `Tr(AU) = Tr(SUS)`, `Tr(AUAU) = Tr((SUS)²)`, `SUS` Hermitian;
* `prod_inv_taylor` (scalar core): for real `μ` with `Σμ² ≤ 1/16`, `|Σμ| ≤ 1/4`,
  `|∏(1+μ_i)⁻¹ - (1 - t + t²/2 + s/2)| ≤ 10((√s)³ + |t|³)`, `t = Σμ`, `s = Σμ²`;
* `det_inv_taylor`: the same for a Hermitian `M` (`t = Re Tr M`, `s = Re Tr M²`,
  `√s = ‖M‖_HS`);
* `detLaplace_transport_taylor`: with `τ = Re Tr(AU)`, `σ = Re Tr(AUAU) = ‖A^{1/2}UA^{1/2}‖_HS²`,
  on `σ ≤ 1/16`, `|τ| ≤ 1/4`:
  `|F_a(L*QL) - F_a(Q)(1 - τ + τ²/2 + σ/2)| ≤ 10 F_a(Q)((√σ)³ + |τ|³)`;
* `detLaplace_injection` (the positive injection): for `P, B ⪰ 0`, `a ≥ 0`,
  `|F_a(P + B) - F_a(P) + a F_a(P) Tr B| ≤ a²((Tr B)² + ‖B‖ Tr P)` (second directional
  derivative `≤ a²(Tr B)²`; replacing `(I + aP)⁻¹` by `I` costs `a²‖B‖ Tr P`; in the lemma
  `P = L*QL`, `B = q C₊/W²`).

The event thresholds `1/16`, `1/4` (HS norm `≤ 1/4`, trace `≤ 1/4`) are smaller than
`1/2`, `1`; the thresholds are internal to the proof (the complement is paid by Markov at a
fixed moment order for any fixed thresholds), so this does not change the lemma.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace DetClockTaylor

open ClockMixingAlg

/-!
## 1. The scalar Taylor estimate
-/

theorem cube_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

theorem sq_mul_le_cube_add {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) : h ^ 2 * t ≤ h ^ 3 + t ^ 3 := by
  rcases le_total t h with hth | hth
  · nlinarith [mul_nonneg (mul_nonneg hh hh) (sub_nonneg.mpr hth), pow_nonneg ht 3]
  · nlinarith [mul_nonneg ht (mul_nonneg (sub_nonneg.mpr hth) (add_nonneg hh ht)),
      pow_nonneg hh 3]

/-- **Scalar core of the Taylor remainder**. -/
theorem prod_inv_taylor {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hs : ∑ i, μ i ^ 2 ≤ 1 / 16)
    (ht : |∑ i, μ i| ≤ 1 / 4) :
    |∏ i, (1 + μ i)⁻¹ - (1 - ∑ i, μ i + (∑ i, μ i) ^ 2 / 2 + (∑ i, μ i ^ 2) / 2)| ≤
      10 * (Real.sqrt (∑ i, μ i ^ 2) ^ 3 + |∑ i, μ i| ^ 3) := by
  set t := ∑ i, μ i with htdef
  set s := ∑ i, μ i ^ 2 with hsdef
  set h := Real.sqrt s with hhdef
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  have hhs : h ^ 2 = s := Real.sq_sqrt hs0
  have hh4 : h ≤ 1 / 4 := by
    have : Real.sqrt (1 / 16) = 1 / 4 := by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this]; exact Real.sqrt_le_sqrt hs
  have hμh : ∀ i, |μ i| ≤ h := fun i => by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (μ j))
      (Finset.mem_univ i))
  have hμ1 : ∀ i, |μ i| < 1 := fun i => (hμh i).trans_lt (by linarith)
  have hpos : ∀ i, 0 < 1 + μ i := fun i => by
    have := neg_abs_le (μ i); linarith [hμh i]
  -- the logarithm remainder
  set ρ : ι → ℝ := fun i => Real.log (1 + μ i) - μ i + μ i ^ 2 / 2 with hρdef
  have hρ : ∀ i, |ρ i| ≤ 2 * |μ i| ^ 3 := by
    intro i
    have h1 := Real.abs_log_sub_add_sum_range_le (x := -μ i) (by rw [abs_neg]; exact hμ1 i) 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, abs_neg] at h1
    have he : ρ i = (-μ i) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-μ i) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        Real.log (1 - -μ i) := by
      simp only [hρdef]; push_cast; ring_nf
    rw [he]
    have hμ34 : |μ i| ≤ 1 / 4 := (hμh i).trans hh4
    have hden : 3 / 4 ≤ 1 - |μ i| := by linarith
    refine h1.trans ?_
    rw [show |μ i| ^ (2 + 1) = |μ i| ^ 3 by norm_num, div_le_iff₀ (by linarith)]
    have := pow_nonneg (abs_nonneg (μ i)) 3
    nlinarith [mul_le_mul_of_nonneg_left hden this]
  set r := ∑ i, ρ i with hrdef
  have hcube : ∑ i, |μ i| ^ 3 ≤ h ^ 3 := by
    calc ∑ i, |μ i| ^ 3 ≤ ∑ i, h * μ i ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [show |μ i| ^ 3 = |μ i| * μ i ^ 2 by rw [← sq_abs (μ i)]; ring]
          exact mul_le_mul_of_nonneg_right (hμh i) (sq_nonneg _)
      _ = h ^ 3 := by rw [← Finset.mul_sum, ← hsdef, ← hhs]; ring
  have hr : |r| ≤ 2 * h ^ 3 := by
    calc |r| ≤ ∑ i, |ρ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 * |μ i| ^ 3 := Finset.sum_le_sum fun i _ => hρ i
      _ ≤ 2 * h ^ 3 := by rw [← Finset.mul_sum]; linarith
  have hlog : ∑ i, Real.log (1 + μ i) = t - s / 2 + r := by
    simp only [hrdef, hρdef, Finset.sum_add_distrib, Finset.sum_sub_distrib, htdef, hsdef,
      Finset.sum_div]
    ring
  have hprod : ∏ i, (1 + μ i)⁻¹ = Real.exp (-(t - s / 2 + r)) := by
    rw [← hlog, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_neg, Real.exp_log (hpos i)]
  rw [hprod]
  set x := -(t - s / 2 + r) with hxdef
  have hat : |t| ≤ 1 / 4 := ht
  have hrh : |r| ≤ h ^ 2 / 2 := by nlinarith [pow_nonneg hh0 2]
  have hx : |x| ≤ |t| + h := by
    have : |x| ≤ |t| + s / 2 + |r| := by
      rw [hxdef, abs_neg]
      have h1 : |t - s / 2| ≤ |t| + |s / 2| := abs_sub t (s / 2)
      have h2 : |s / 2| = s / 2 := abs_of_nonneg (by linarith)
      calc |t - s / 2 + r| ≤ |t - s / 2| + |r| := abs_add_le _ _
        _ ≤ |t| + s / 2 + |r| := by linarith
    nlinarith [pow_nonneg hh0 2]
  have hx1 : |x| ≤ 1 := by linarith
  have hexp := Real.exp_bound hx1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial,
    Nat.cast_one, div_one, pow_one, Nat.succ_eq_add_one] at hexp
  norm_num at hexp
  have hfirst : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ h ^ 3 + |t| ^ 3 := by
    have hc := cube_add_le (abs_nonneg t) hh0
    have hx3 : |x| ^ 3 ≤ (|t| + h) ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
    have : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * (2 / 9) := by
      convert hexp using 2
    linarith [pow_nonneg hh0 3, pow_nonneg (abs_nonneg t) 3]
  have hsecond : |(1 + x + x ^ 2 / 2) - (1 - t + t ^ 2 / 2 + s / 2)| ≤ 3.5 * h ^ 3 + |t| ^ 3 := by
    have hid : (1 + x + x ^ 2 / 2) - (1 - t + t ^ 2 / 2 + s / 2) =
        -r + ((s / 2 - r) * (-2 * t + s / 2 - r)) / 2 := by
      rw [hxdef]; ring
    rw [hid]
    have hA : |s / 2 - r| ≤ h ^ 2 := by
      calc |s / 2 - r| ≤ |s / 2| + |r| := abs_sub _ _
        _ ≤ h ^ 2 := by rw [abs_of_nonneg (by linarith), ← hhs]; linarith
    have hB : |-2 * t + s / 2 - r| ≤ 2 * |t| + h := by
      calc |-2 * t + s / 2 - r| ≤ |-2 * t| + |s / 2 - r| := by
            rw [show -2 * t + s / 2 - r = -2 * t + (s / 2 - r) by ring]; exact abs_add_le _ _
        _ ≤ 2 * |t| + h ^ 2 := by rw [abs_mul]; norm_num; linarith
        _ ≤ 2 * |t| + h := by nlinarith
    have hprodb : |(s / 2 - r) * (-2 * t + s / 2 - r)| ≤ h ^ 2 * (2 * |t| + h) := by
      rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (pow_nonneg hh0 2)
    have hy := sq_mul_le_cube_add hh0 (abs_nonneg t)
    calc |-r + (s / 2 - r) * (-2 * t + s / 2 - r) / 2|
        ≤ |-r| + |(s / 2 - r) * (-2 * t + s / 2 - r) / 2| := abs_add_le _ _
      _ = |r| + |(s / 2 - r) * (-2 * t + s / 2 - r)| / 2 := by rw [abs_neg, abs_div]; norm_num
      _ ≤ 2 * h ^ 3 + h ^ 2 * (2 * |t| + h) / 2 := by linarith
      _ ≤ 3.5 * h ^ 3 + |t| ^ 3 := by nlinarith
  calc |Real.exp x - (1 - t + t ^ 2 / 2 + s / 2)|
      ≤ |Real.exp x - (1 + x + x ^ 2 / 2)| + |(1 + x + x ^ 2 / 2) - (1 - t + t ^ 2 / 2 + s / 2)| :=
        abs_sub_le _ _ _
    _ ≤ (h ^ 3 + |t| ^ 3) + (3.5 * h ^ 3 + |t| ^ 3) := add_le_add hfirst hsecond
    _ ≤ 10 * (h ^ 3 + |t| ^ 3) := by nlinarith [pow_nonneg hh0 3, pow_nonneg (abs_nonneg t) 3]

/-!
## 2. Hermitian matrices
-/

section Matrix

variable {n : ℕ}

/-- **Taylor remainder for a Hermitian matrix**: with `t = Re Tr M`,
`s = Re Tr M² = ‖M‖_HS²`, on `s ≤ 1/16`, `|t| ≤ 1/4`:
`|det(I + M)⁻¹ - (1 - t + t²/2 + s/2)| ≤ 10((√s)³ + |t|³)`. -/
theorem det_inv_taylor {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    (hs : (M * M).trace.re ≤ 1 / 16) (ht : |M.trace.re| ≤ 1 / 4) :
    |((1 + M).det.re)⁻¹ - (1 - M.trace.re + M.trace.re ^ 2 / 2 + (M * M).trace.re / 2)| ≤
      10 * (Real.sqrt ((M * M).trace.re) ^ 3 + |M.trace.re| ^ 3) := by
  have hdet : (1 + M).det.re = ∏ i, (1 + hM.eigenvalues i) := by
    have h := det_one_add_smul_eq_prod hM 1
    rw [Complex.ofReal_one, one_smul] at h
    rw [h, Complex.ofReal_re]
    simp
  have htr : M.trace.re = ∑ i, hM.eigenvalues i := trace_re_eq_sum hM
  have hsq : (M * M).trace.re = ∑ i, hM.eigenvalues i ^ 2 := by
    rw [DetClockCov.trace_mul_self_eq_sum hM, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
  rw [hdet, ← Finset.prod_inv_distrib, htr, hsq]
  rw [htr] at ht
  rw [hsq] at hs
  exact prod_inv_taylor hM.eigenvalues hs ht

/-- The square root `S = A^{1/2}` of a positive semidefinite `A` (spectral theorem). -/
def psdSqrt {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℂ :=
  eU hA * diagonal (fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)) * star (eU hA)

theorem psdSqrt_mul_self {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    psdSqrt hA.1 * psdSqrt hA.1 = A := by
  unfold psdSqrt
  conv_rhs => rw [spec hA.1]
  calc eU hA.1 * diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) * star (eU hA.1) *
        (eU hA.1 * diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) *
          star (eU hA.1))
      = eU hA.1 * diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) *
          (star (eU hA.1) * eU hA.1) *
          diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) * star (eU hA.1) := by
        simp only [Matrix.mul_assoc]
    _ = eU hA.1 * (diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ)) *
          diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i) : ℝ) : ℂ))) * star (eU hA.1) := by
        rw [eU_star_mul hA.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = eU hA.1 * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * star (eU hA.1) := by
        rw [diagonal_mul_diagonal]
        congr 3
        funext i
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]

theorem psdSqrt_isHermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (psdSqrt hA).IsHermitian := by
  unfold psdSqrt Matrix.IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose]
  have : star (fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)) =
      fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) := by
    funext i; simp
  rw [this, ← star_eq_conjTranspose, Matrix.mul_assoc]

/-- **The transported determinant**: for `Q ⪰ 0`, `a ≥ 0` and any `L`,
`det(I + aL*QL) = det(I + aQ) det(I + A_a(LL* - I))`. -/
theorem det_transport {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (L : Matrix (Fin n) (Fin n) ℂ) :
    (1 + (a : ℂ) • (Lᴴ * Q * L)).det =
      (1 + (a : ℂ) • Q).det * (1 + resolventWeight Q a * (L * Lᴴ - 1)).det := by
  set N := (a : ℂ) • Q with hN
  set P := 1 + N with hP
  have hPu : IsUnit P.det := by
    have h1 := one_le_re_det_one_add_smul hQ ha
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, Complex.zero_re] at h1; linarith
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hcomm : P * N = N * P := by rw [hP, add_mul, mul_add, one_mul, mul_one]
  have hA : P * (N * P⁻¹) = N := by
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h1 : (a : ℂ) • (Lᴴ * Q * L) = Lᴴ * (N * L) := by
    rw [hN, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have h2 : 1 + N * L * Lᴴ = P * (1 + N * P⁻¹ * (L * Lᴴ - 1)) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hA, hP, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, h2, Matrix.det_mul]
  rfl

/-- **Taylor remainder of the transported Laplace function**: for `Q ⪰ 0`,
`a ≥ 0`, any `L`, `U = LL* - I`, `A = A_a`, `τ = Re Tr(AU)`, `σ = Re Tr(AUAU)`; on
`σ ≤ 1/16`, `|τ| ≤ 1/4`:
`|F_a(L*QL) - F_a(Q)(1 - τ + τ²/2 + σ/2)| ≤ 10 F_a(Q)((√σ)³ + |τ|³)`. -/
theorem detLaplace_transport_taylor {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) (L : Matrix (Fin n) (Fin n) ℂ)
    (hs : (resolventWeight Q a * (L * Lᴴ - 1) * resolventWeight Q a * (L * Lᴴ - 1)).trace.re ≤
      1 / 16)
    (ht : |(resolventWeight Q a * (L * Lᴴ - 1)).trace.re| ≤ 1 / 4) :
    |detLaplace (Lᴴ * Q * L) a - detLaplace Q a *
        (1 - (resolventWeight Q a * (L * Lᴴ - 1)).trace.re +
          (resolventWeight Q a * (L * Lᴴ - 1)).trace.re ^ 2 / 2 +
          (resolventWeight Q a * (L * Lᴴ - 1) * resolventWeight Q a * (L * Lᴴ - 1)).trace.re / 2)| ≤
      10 * detLaplace Q a *
        (Real.sqrt ((resolventWeight Q a * (L * Lᴴ - 1) * resolventWeight Q a *
          (L * Lᴴ - 1)).trace.re) ^ 3 + |(resolventWeight Q a * (L * Lᴴ - 1)).trace.re| ^ 3) := by
  set A := resolventWeight Q a with hAdef
  set U := L * Lᴴ - 1 with hUdef
  have hApsd : A.PosSemidef := resolventWeight_posSemidef hQ ha
  set S := psdSqrt hApsd.1 with hSdef
  have hSS : S * S = A := psdSqrt_mul_self hApsd
  have hSh : S.IsHermitian := psdSqrt_isHermitian hApsd.1
  have hUh : U.IsHermitian := by
    rw [hUdef]
    exact (isHermitian_mul_conjTranspose_self L).sub isHermitian_one
  set M := S * U * S with hMdef
  have hMh : M.IsHermitian := by
    rw [hMdef, Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul, hSh.eq, hUh.eq,
      Matrix.mul_assoc]
  have hdetM : (1 + A * U).det = (1 + M).det := by
    rw [← hSS, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, hMdef, Matrix.mul_assoc]
  have htrM : (A * U).trace = M.trace := by
    rw [hMdef, ← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hsqM : (A * U * A * U).trace = (M * M).trace := by
    rw [hMdef, ← hSS]
    calc (S * S * U * (S * S) * U).trace = (S * (S * U * (S * S) * U)).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((S * U * (S * S) * U) * S).trace := Matrix.trace_mul_comm _ _
      _ = (S * U * S * (S * U * S)).trace := by simp only [Matrix.mul_assoc]
  have hT := det_transport hQ ha L
  have hdetQ_im : (1 + (a : ℂ) • Q).det.im = 0 := im_det_one_add_smul hQ.1 a
  have hdetM_im : (1 + M).det.im = 0 := by
    have h := det_one_add_smul_eq_prod hMh 1
    rw [Complex.ofReal_one, one_smul] at h
    rw [h, Complex.ofReal_im]
  have hF : detLaplace (Lᴴ * Q * L) a = detLaplace Q a * ((1 + M).det.re)⁻¹ := by
    unfold detLaplace
    rw [hT, hdetM, Complex.mul_re, hdetQ_im, hdetM_im, mul_zero, sub_zero, mul_inv]
  have hFpos : 0 < detLaplace Q a := detLaplace_pos hQ ha
  rw [hsqM] at hs
  rw [htrM] at ht
  rw [htrM, hsqM]
  rw [hF]
  have key := det_inv_taylor hMh hs ht
  calc |detLaplace Q a * ((1 + M).det.re)⁻¹ - detLaplace Q a *
        (1 - M.trace.re + M.trace.re ^ 2 / 2 + (M * M).trace.re / 2)|
      = detLaplace Q a * |((1 + M).det.re)⁻¹ -
          (1 - M.trace.re + M.trace.re ^ 2 / 2 + (M * M).trace.re / 2)| := by
        rw [← mul_sub, abs_mul, abs_of_pos hFpos]
    _ ≤ detLaplace Q a * (10 * (Real.sqrt ((M * M).trace.re) ^ 3 + |M.trace.re| ^ 3)) :=
        mul_le_mul_of_nonneg_left key hFpos.le
    _ = 10 * detLaplace Q a * (Real.sqrt ((M * M).trace.re) ^ 3 + |M.trace.re| ^ 3) := by ring

/-!
## 3. The positive injection
-/

/-- `∏(1 + β_i) ≥ 1 + Σβ_i` for `β ≥ 0`. -/
theorem one_add_sum_le_prod {ι : Type*} [Fintype ι] (β : ι → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    1 + ∑ i, β i ≤ ∏ i, (1 + β i) := by
  classical
  have key : ∀ s : Finset ι, 1 + ∑ i ∈ s, β i ≤ ∏ i ∈ s, (1 + β i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj]
      have h0 : 0 ≤ ∑ i ∈ s, β i := Finset.sum_nonneg fun i _ => hβ i
      have := hβ j
      nlinarith
  exact key Finset.univ

/-- `0 ≤ ∏(1+β_i)⁻¹ - 1 + Σβ_i ≤ (Σβ_i)²` for `β ≥ 0`. -/
theorem prod_inv_first_order {ι : Type*} [Fintype ι] (β : ι → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    |∏ i, (1 + β i)⁻¹ - 1 + ∑ i, β i| ≤ (∑ i, β i) ^ 2 := by
  set σ := ∑ i, β i
  have hσ : 0 ≤ σ := Finset.sum_nonneg fun i _ => hβ i
  have hlow : 1 - σ ≤ ∏ i, (1 + β i)⁻¹ := by
    have h1 : Real.exp (-σ) ≤ ∏ i, (1 + β i)⁻¹ := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      refine Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) (fun i _ => ?_)
      rw [Real.exp_neg]
      exact inv_anti₀ (by linarith [hβ i]) (by linarith [Real.add_one_le_exp (β i)])
    linarith [Real.add_one_le_exp (-σ)]
  have hup : ∏ i, (1 + β i)⁻¹ ≤ 1 - σ + σ ^ 2 := by
    rw [Finset.prod_inv_distrib]
    have hp := one_add_sum_le_prod β hβ
    have h1 : (∏ i, (1 + β i))⁻¹ ≤ (1 + σ)⁻¹ := inv_anti₀ (by linarith) hp
    have h2 : (1 + σ)⁻¹ ≤ 1 - σ + σ ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith [pow_nonneg hσ 3]
    linarith
  rw [abs_le]; constructor <;> nlinarith

/-- **The positive injection**: for `P, B ⪰ 0` and `a ≥ 0`,
`|F_a(P + B) - F_a(P) + a F_a(P) Tr B| ≤ a²((Tr B)² + ‖B‖ Tr P)` (second directional
derivative at most `a²(Tr B)²`; replacing `(I + aP)⁻¹` by `I` in the first derivative costs
`a²‖B‖ Tr P`). -/
theorem detLaplace_injection {P B : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef)
    (hB : B.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    |detLaplace (P + B) a - detLaplace P a + a * detLaplace P a * B.trace.re| ≤
      a ^ 2 * (B.trace.re ^ 2 + ‖B‖ * P.trace.re) := by
  have ha' : (0 : ℂ) ≤ (a : ℂ) := Complex.zero_le_real.mpr ha
  set Q := 1 + (a : ℂ) • P with hQdef
  have hQ : Q.PosSemidef := PosSemidef.one.add (hP.smul ha')
  have hQu : IsUnit Q.det := by
    have h1 := one_le_re_det_one_add_smul hP ha
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [← hQdef, h0, Complex.zero_re] at h1; linarith
  set R := Q⁻¹ with hRdef
  have hR : R.PosSemidef := hQ.inv
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv Q hQu
  set S := psdSqrt hR.1 with hSdef
  have hSS : S * S = R := psdSqrt_mul_self hR
  have hSh : S.IsHermitian := psdSqrt_isHermitian hR.1
  set M := S * ((a : ℂ) • B) * S with hMdef
  have hM : M.PosSemidef := by
    have := (hB.smul ha').conjTranspose_mul_mul_same S
    rwa [hSh.eq] at this
  -- determinant factorization
  have hdet : (1 + (a : ℂ) • (P + B)).det = Q.det * (1 + M).det := by
    have h1 : 1 + (a : ℂ) • (P + B) = Q * (1 + R * ((a : ℂ) • B)) := by
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hQR, Matrix.one_mul, smul_add,
        hQdef, add_assoc]
    rw [h1, Matrix.det_mul, ← hSS, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, hMdef]
  have hQim : Q.det.im = 0 := im_det_one_add_smul hP.1 a
  have hdetM := det_one_add_smul_eq_prod hM.1 1
  rw [Complex.ofReal_one, one_smul] at hdetM
  have hMim : (1 + M).det.im = 0 := by rw [hdetM, Complex.ofReal_im]
  set β := hM.1.eigenvalues
  have hβ : ∀ i, 0 ≤ β i := hM.eigenvalues_nonneg
  have hMre : (1 + M).det.re = ∏ i, (1 + β i) := by rw [hdetM, Complex.ofReal_re]; simp [β]
  have hF : detLaplace (P + B) a = detLaplace P a * ∏ i, (1 + β i)⁻¹ := by
    unfold detLaplace
    rw [hdet, Complex.mul_re, hQim, hMim, mul_zero, sub_zero, mul_inv, hMre,
      Finset.prod_inv_distrib]
  -- the trace of `M`
  have hTrM : ∑ i, β i = a * (R * B).trace.re := by
    rw [← trace_re_eq_sum hM.1, hMdef, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS,
      Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  -- `I - R = A_a(P)`
  have hIR : 1 - R = resolventWeight P a := by
    have e1 : resolventWeight P a = (a : ℂ) • P * R := rfl
    have : (a : ℂ) • P = Q - 1 := by rw [hQdef]; abel
    rw [e1, this, Matrix.sub_mul, Matrix.one_mul, hQR]
  have hAw := resolventWeight_posSemidef hP ha
  have hAB : (resolventWeight P a * B).trace.re = B.trace.re - (R * B).trace.re := by
    rw [← hIR, Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re]
  have hAB0 : 0 ≤ (resolventWeight P a * B).trace.re := by
    set T := psdSqrt hAw.1
    have hTT : T * T = resolventWeight P a := psdSqrt_mul_self hAw
    have hTh : T.IsHermitian := psdSqrt_isHermitian hAw.1
    have hpsd : (T * B * T).PosSemidef := by
      have := hB.conjTranspose_mul_mul_same T; rwa [hTh.eq] at this
    rw [← hTT, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc]
    exact trace_re_nonneg hpsd
  have hAB1 : (resolventWeight P a * B).trace.re ≤ ‖B‖ * (a * P.trace.re) := by
    have h1 := norm_trace_mul_le hAw B
    have h2 := re_trace_resolventWeight_le hP ha
    have h3 := Complex.re_le_norm (resolventWeight P a * B).trace
    have := mul_le_mul_of_nonneg_left h2 (norm_nonneg B)
    linarith
  have hFP0 : 0 < detLaplace P a := detLaplace_pos hP ha
  have hFP1 : detLaplace P a ≤ 1 := detLaplace_le_one hP ha
  have hfirst := prod_inv_first_order β hβ
  set σ := ∑ i, β i with hσdef
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun i _ => hβ i
  have hσle : σ ≤ a * B.trace.re := by
    rw [hTrM]; exact mul_le_mul_of_nonneg_left (by linarith) ha
  have hdecomp : detLaplace (P + B) a - detLaplace P a + a * detLaplace P a * B.trace.re =
      detLaplace P a * (∏ i, (1 + β i)⁻¹ - 1 + σ) +
        detLaplace P a * (a * (resolventWeight P a * B).trace.re) := by
    rw [hF, hAB, hTrM]; ring
  rw [hdecomp]
  have hTB0 : 0 ≤ B.trace.re := trace_re_nonneg hB
  have hTP0 : 0 ≤ P.trace.re := trace_re_nonneg hP
  calc |detLaplace P a * (∏ i, (1 + β i)⁻¹ - 1 + σ) +
        detLaplace P a * (a * (resolventWeight P a * B).trace.re)|
      ≤ |detLaplace P a * (∏ i, (1 + β i)⁻¹ - 1 + σ)| +
          |detLaplace P a * (a * (resolventWeight P a * B).trace.re)| := abs_add_le _ _
    _ ≤ 1 * σ ^ 2 + 1 * (a * (‖B‖ * (a * P.trace.re))) := by
        rw [abs_mul, abs_mul, abs_of_pos hFP0, abs_of_nonneg (mul_nonneg ha hAB0)]
        gcongr
    _ ≤ a ^ 2 * (B.trace.re ^ 2 + ‖B‖ * P.trace.re) := by
        have : σ ^ 2 ≤ (a * B.trace.re) ^ 2 := pow_le_pow_left₀ hσ0 hσle 2
        nlinarith

end Matrix

end DetClockTaylor

end BlockBand.Endpoints.Clock
