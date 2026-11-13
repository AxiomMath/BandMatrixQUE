module

public import BlockBand.Endpoints.Clock.ZeroEntranceForms

/-!
# The zero-entrance lemma: uniform invertibility of `I - ΘA` and exponential decay

We prove the generic singular-value bound and the exponential conjugation estimate used in Step 6
of the proof of the zero-entrance lemma.

* `ZeroEntrance.lower_bound_ThetaA` (the singular-value bound): if the real symmetric `A`
  satisfies `xᵀAx ≤ |x|²` and `|x|² + xᵀAx ≥ δ_* |x|²`, and `Θ` is a diagonal unitary with
  `|1 - Θ_i| ≥ δ`, then `|(I - ΘA)x| ≥ κ₀ |x|` with `κ₀ = min(δ/2, δ² δ_*/16)`.
  The argument: `‖Ax‖ ≥ 1 - ε`, `‖(I - A)x‖² ≤ (2/δ_*)(1 - ‖Ax‖²) ≤ 4ε/δ_*`,
  `δ ≤ ‖(I - Θ)x‖ ≤ ε + 2√(ε/δ_*)`.
* `ZeroEntrance.decay_commutator`: conjugation by `diag(e^{t pos_i})` for a tridiagonal `A`
  (`A_ij ≠ 0 ⇒ |pos_i - pos_j| ≤ 1`) with `‖A|x|‖ ≤ ‖x‖` changes `I - ΘA` by at most `e^t - 1`
  in norm (`t ≥ 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

namespace ZeroEntrance

variable {ι : Type*} [Fintype ι]

theorem cnorm_smul_real (r : ℝ) (hr : 0 ≤ r) (x : ι → ℂ) :
    cnorm (fun i => (r : ℂ) * x i) = r * cnorm x := by
  unfold cnorm cnsq
  have : ∑ i, ‖(r : ℂ) * x i‖ ^ 2 = r ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]; ring
  rw [this, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

/-- **Step 6**, the uniform lower bound on the smallest singular value of `I - ΘA`. -/
theorem lower_bound_ThetaA {A : ι → ι → ℝ} (hsym : ∀ i j, A i j = A j i) {δs δΘ : ℝ}
    (hδs : 0 < δs) (hδΘ : 0 < δΘ)
    (hup : ∀ x, bf A x x ≤ nsq x) (hlow : ∀ x, δs * nsq x ≤ nsq x + bf A x x)
    {Θ : ι → ℂ} (hΘ1 : ∀ i, ‖Θ i‖ = 1) (hΘ : ∀ i, δΘ ≤ ‖1 - Θ i‖) (x : ι → ℂ) :
    min (δΘ / 2) (δΘ ^ 2 * δs / 16) * cnorm x ≤ cnorm (fun i => x i - Θ i * cmv A x i) := by
  set X := cnorm x
  set ε := cnorm (fun i => x i - Θ i * cmv A x i)
  set s := cnorm (fun i => x i - cmv A x i)
  set N := cnorm (cmv A x)
  have hX0 : 0 ≤ X := cnorm_nonneg _
  have hε0 : 0 ≤ ε := cnorm_nonneg _
  have hs0 : 0 ≤ s := cnorm_nonneg _
  have hN0 : 0 ≤ N := cnorm_nonneg _
  -- (i) `δ X ≤ ‖(I - Θ)x‖`
  have h1 : δΘ * X ≤ cnorm (fun i => (1 - Θ i) * x i) := by
    rw [← cnorm_smul_real δΘ hδΘ.le]
    refine cnorm_le_of_pointwise fun i => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδΘ.le]
    exact mul_le_mul_of_nonneg_right (hΘ i) (norm_nonneg _)
  -- (ii) `‖(I - Θ)x‖ ≤ ε + s`
  have h2 : cnorm (fun i => (1 - Θ i) * x i) ≤ ε + s := by
    have heq : (fun i => (1 - Θ i) * x i) =
        (fun i => x i - Θ i * cmv A x i) - (fun i => Θ i * (x i - cmv A x i)) := by
      funext i; simp only [Pi.sub_apply]; ring
    rw [heq]
    refine (cnorm_sub_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    exact cnorm_eq_of_pointwise fun i => by rw [norm_mul, hΘ1, one_mul]
  -- (iii) the spectral inequality
  have h3 : s ^ 2 ≤ 2 / δs * (X ^ 2 - N ^ 2) := by
    simp only [s, X, N, cnorm_sq]
    exact spectral_ineq_complex hsym hδs hup hlow x
  -- (iv) `X ≤ ε + N`
  have h4 : X ≤ ε + N := by
    have heq : x = (fun i => x i - Θ i * cmv A x i) + (fun i => Θ i * cmv A x i) := by
      funext i; simp
    have hN : cnorm (fun i => Θ i * cmv A x i) = N :=
      cnorm_eq_of_pointwise fun i => by rw [norm_mul, hΘ1, one_mul]
    calc X = cnorm ((fun i => x i - Θ i * cmv A x i) + (fun i => Θ i * cmv A x i)) := by
          rw [← heq]
      _ ≤ ε + cnorm (fun i => Θ i * cmv A x i) := cnorm_add_le _ _
      _ = ε + N := by rw [hN]
  have hN2 : X ^ 2 - 2 * ε * X ≤ N ^ 2 := by
    rcases le_or_gt X ε with hXe | hXe
    · nlinarith [sq_nonneg N]
    · have : X - ε ≤ N := by linarith
      nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ X - ε) this 2]
  -- conclusion
  by_contra hcon
  push Not at hcon
  have hκ1 : min (δΘ / 2) (δΘ ^ 2 * δs / 16) ≤ δΘ / 2 := min_le_left _ _
  have hκ2 : min (δΘ / 2) (δΘ ^ 2 * δs / 16) ≤ δΘ ^ 2 * δs / 16 := min_le_right _ _
  have hXpos : 0 < X := by
    by_contra h0
    have : X = 0 := le_antisymm (not_lt.mp h0) hX0
    rw [this, mul_zero] at hcon
    linarith
  have hεlt1 : ε < δΘ / 2 * X := lt_of_lt_of_le hcon (mul_le_mul_of_nonneg_right hκ1 hX0)
  have hεlt2 : ε < δΘ ^ 2 * δs / 16 * X :=
    lt_of_lt_of_le hcon (mul_le_mul_of_nonneg_right hκ2 hX0)
  have hslow : δΘ / 2 * X < s := by nlinarith
  have hsq1 : (δΘ / 2 * X) ^ 2 < s ^ 2 := by
    have : 0 ≤ δΘ / 2 * X := by positivity
    nlinarith
  have hsq2 : s ^ 2 ≤ 4 / δs * (ε * X) := by
    refine h3.trans ?_
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδs]
    nlinarith
  have hsq3 : 4 / δs * (ε * X) < (δΘ / 2 * X) ^ 2 := by
    have : ε * X < δΘ ^ 2 * δs / 16 * X * X := mul_lt_mul_of_pos_right hεlt2 hXpos
    calc 4 / δs * (ε * X) < 4 / δs * (δΘ ^ 2 * δs / 16 * X * X) :=
          mul_lt_mul_of_pos_left this (by positivity)
      _ = (δΘ / 2 * X) ^ 2 := by field_simp; ring
  linarith

theorem abs_exp_sub_one_le {t : ℝ} (ht : 0 ≤ t) {p q : ℕ} (h1 : p ≤ q + 1) (h2 : q ≤ p + 1) :
    |Real.exp (t * ((p : ℝ) - q)) - 1| ≤ Real.exp t - 1 := by
  have hp : (p : ℝ) ≤ q + 1 := by exact_mod_cast h1
  have hq : (q : ℝ) ≤ p + 1 := by exact_mod_cast h2
  have hlo : -t ≤ t * ((p : ℝ) - q) := by nlinarith
  have hhi : t * ((p : ℝ) - q) ≤ t := by nlinarith
  rw [abs_le]
  constructor
  · -- `1 - e^{-t} ≤ e^t - 1`
    have h := Real.exp_le_exp.mpr hlo
    have hprod : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos t
    have := Real.exp_pos (-t)
    nlinarith [sq_nonneg (Real.exp t - 1)]
  · linarith [Real.exp_le_exp.mpr hhi]

/-- **Step 6**, exponential conjugation: for `t ≥ 0` and `w = diag(e^{t pos}) x`,
`|(I - ΘA) w| ≤ |diag(e^{t pos}) (I - ΘA) x| + (e^t - 1) |w|`. -/
theorem decay_commutator {A : ι → ι → ℝ} (hA : ∀ i j, 0 ≤ A i j) (pos : ι → ℕ)
    (htri : ∀ i j, A i j ≠ 0 → pos i ≤ pos j + 1 ∧ pos j ≤ pos i + 1)
    (hschur : ∀ x : ι → ℝ, ∑ i, (∑ j, A i j * |x j|) ^ 2 ≤ ∑ j, x j ^ 2)
    {Θ : ι → ℂ} (hΘ1 : ∀ i, ‖Θ i‖ = 1) {t : ℝ} (ht : 0 ≤ t) (x : ι → ℂ) :
    cnorm (fun i => (Real.exp (t * pos i) : ℂ) * x i -
        Θ i * cmv A (fun j => (Real.exp (t * pos j) : ℂ) * x j) i) ≤
      cnorm (fun i => (Real.exp (t * pos i) : ℂ) * (x i - Θ i * cmv A x i)) +
        (Real.exp t - 1) * cnorm (fun i => (Real.exp (t * pos i) : ℂ) * x i) := by
  set E : ι → ℝ := fun i => Real.exp (t * pos i) with hE
  set w : ι → ℂ := fun i => (E i : ℂ) * x i with hw
  have hEt : 0 ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  -- the commutator vector
  set g : ι → ℂ := fun i => Θ i * ((E i : ℂ) * cmv A x i - cmv A w i) with hg
  have hsplit : (fun i => w i - Θ i * cmv A w i) =
      (fun i => (E i : ℂ) * (x i - Θ i * cmv A x i)) + g := by
    funext i; simp only [hg, Pi.add_apply, hw]; ring
  have hgi : ∀ i, ‖g i‖ ≤ (Real.exp t - 1) * ∑ j, A i j * ‖w j‖ := by
    intro i
    simp only [hg, norm_mul, hΘ1, one_mul]
    have hexp : (E i : ℂ) * cmv A x i - cmv A w i =
        ∑ j, (A i j : ℂ) * (((Real.exp (t * ((pos i : ℝ) - pos j)) - 1 : ℝ) : ℂ) * w j) := by
      unfold cmv
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hw, hE]
      have : Real.exp (t * ((pos i : ℝ) - pos j)) * Real.exp (t * pos j) =
          Real.exp (t * pos i) := by rw [← Real.exp_add]; ring_nf
      rw [← this]; push_cast; ring
    rw [hexp, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hA i j),
      Real.norm_eq_abs]
    by_cases h0 : A i j = 0
    · rw [h0]; simp
    · obtain ⟨h1, h2⟩ := htri i j h0
      have := abs_exp_sub_one_le ht h1 h2
      have := norm_nonneg (w j)
      have := hA i j
      calc A i j * (|Real.exp (t * ((pos i : ℝ) - pos j)) - 1| * ‖w j‖)
          ≤ A i j * ((Real.exp t - 1) * ‖w j‖) := by gcongr
        _ = (Real.exp t - 1) * (A i j * ‖w j‖) := by ring
  have hgn : cnorm g ≤ (Real.exp t - 1) * cnorm w := by
    have hsch := hschur (fun j => ‖w j‖)
    simp only [abs_norm] at hsch
    unfold cnorm cnsq
    rw [← Real.sqrt_sq hEt, ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖g i‖ ^ 2 ≤ ∑ i, ((Real.exp t - 1) * ∑ j, A i j * ‖w j‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hgi i) 2
      _ = (Real.exp t - 1) ^ 2 * ∑ i, (∑ j, A i j * ‖w j‖) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (Real.exp t - 1) ^ 2 * ∑ i, ‖w i‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsch (sq_nonneg _)
  change cnorm (fun i => w i - Θ i * cmv A w i) ≤ _
  rw [hsplit]
  exact (cnorm_add_le _ _).trans (add_le_add le_rfl hgn)

end ZeroEntrance

end BlockBand.Endpoints.Clock
