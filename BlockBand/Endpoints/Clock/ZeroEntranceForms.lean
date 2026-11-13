module

public import BlockBand.Endpoints.Clock.CavityMeanMap
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The zero-entrance lemma: generic quadratic-form facts

We prove the generic quadratic-form facts used in Steps 5–6 of the proof of the zero-entrance
lemma.

* `ZeroEntrance.schur_identity`: for a positive vector `φ` and `s² = 1`,
  `½ Σ_{ij} A_ij φ_i φ_j (x_i/φ_i + s x_j/φ_j)² = Σ_i x_i² (Aφ)_i/φ_i + s xᵀAx`.
* `ZeroEntrance.qf_le_of_subinvariant`, `ZeroEntrance.qf_ge_of_subinvariant`: with
  `(Aφ)_i ≤ ρ_i φ_i`, `xᵀAx ≤ Σ ρ_i x_i²` and `xᵀAx ≥ Σ (2A_ii - ρ_i) x_i²` (the
  subinvariant-vector argument and its diagonal splitting `vᵀAv ≥ -|v|ᵀA|v| + 2 Σ A_ii v_i²`).
* `ZeroEntrance.schur_norm_le`: `‖A|x|‖ ≤ ‖x‖` when `ρ ≤ 1` (Schur test).
* `ZeroEntrance.spectral_ineq`: if `xᵀAx ≤ |x|²` and `|x|² + xᵀAx ≥ δ |x|²` for all real `x`,
  then `|(I - A)x|² ≤ (2/δ)(|x|² - |Ax|²)` (proved without the spectral
  theorem, by the Cauchy–Schwarz inequality for the positive form of `I - A`); the complex
  version `ZeroEntrance.spectral_ineq_complex`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

namespace ZeroEntrance

variable {ι : Type*} [Fintype ι]

/-- `(Ax)_i = Σ_j A_ij x_j`. -/
def mv (A : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ := ∑ j, A i j * x j

/-- `xᵀ A y = Σ_{ij} A_ij x_i y_j`. -/
def bf (A : ι → ι → ℝ) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * y j

/-- `|x|² = Σ_i x_i²`. -/
def nsq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

theorem nsq_nonneg (x : ι → ℝ) : 0 ≤ nsq x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem bf_eq_sum_mv (A : ι → ι → ℝ) (x y : ι → ℝ) : bf A x y = ∑ i, x i * mv A y i := by
  unfold bf mv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem bf_comm (A : ι → ι → ℝ) (hsym : ∀ i j, A i j = A j i) (x y : ι → ℝ) :
    bf A x y = bf A y x := by
  unfold bf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym]; ring

theorem bf_add_smul (A : ι → ι → ℝ) (hsym : ∀ i j, A i j = A j i) (x w : ι → ℝ) (t : ℝ) :
    bf A (fun i => x i + t * w i) (fun i => x i + t * w i) =
      bf A w w * (t * t) + 2 * bf A x w * t + bf A x x := by
  have h1 : bf A (fun i => x i + t * w i) (fun i => x i + t * w i) =
      bf A x x + t * bf A x w + t * bf A w x + t * t * bf A w w := by
    unfold bf
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, bf_comm A hsym w x]; ring

/-- Cauchy–Schwarz for a positive semidefinite symmetric form. -/
theorem bf_cs (A : ι → ι → ℝ) (hsym : ∀ i j, A i j = A j i) (hpos : ∀ x, 0 ≤ bf A x x)
    (x w : ι → ℝ) : bf A x w ^ 2 ≤ bf A x x * bf A w w := by
  have h := discrim_le_zero (fun t => by
    rw [← bf_add_smul A hsym x w t]; exact hpos _)
  unfold discrim at h
  nlinarith

/-!
## The subinvariant vector (Step 5)
-/

/-- The Schur identity. -/
theorem schur_identity (A : ι → ι → ℝ) (hsym : ∀ i j, A i j = A j i) (φ : ι → ℝ)
    (hφ : ∀ i, 0 < φ i) (x : ι → ℝ) {s : ℝ} (hs : s ^ 2 = 1) :
    (1 / 2) * ∑ i, ∑ j, A i j * φ i * φ j * (x i / φ i + s * x j / φ j) ^ 2 =
      ∑ i, x i ^ 2 * mv A φ i / φ i + s * bf A x x := by
  have hterm : ∀ i j, A i j * φ i * φ j * (x i / φ i + s * x j / φ j) ^ 2 =
      A i j * φ j * x i ^ 2 / φ i + A i j * φ i * x j ^ 2 / φ j + 2 * s * (A i j * x i * x j) := by
    intro i j
    have h1 := (hφ i).ne'
    have h2 := (hφ j).ne'
    field_simp
    linear_combination (A i j * x j ^ 2 * φ i ^ 2) * hs
  simp only [hterm, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j, A i j * φ i * x j ^ 2 / φ j = ∑ i, ∑ j, A i j * φ j * x i ^ 2 / φ i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym]
  have hT : ∑ i, ∑ j, A i j * φ j * x i ^ 2 / φ i = ∑ i, x i ^ 2 * mv A φ i / φ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold mv
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hB : ∑ i, ∑ j, 2 * s * (A i j * x i * x j) = 2 * s * bf A x x := by
    unfold bf; simp only [Finset.mul_sum]
  rw [hswap, hT, hB]; ring

variable {A : ι → ι → ℝ} {φ ρ : ι → ℝ}

theorem sub_term_le (hφ : ∀ i, 0 < φ i) (hsub : ∀ i, mv A φ i ≤ ρ i * φ i) (x : ι → ℝ) :
    ∑ i, x i ^ 2 * mv A φ i / φ i ≤ ∑ i, ρ i * x i ^ 2 := by
  refine Finset.sum_le_sum fun i _ => ?_
  rw [div_le_iff₀ (hφ i)]
  nlinarith [mul_le_mul_of_nonneg_left (hsub i) (sq_nonneg (x i))]

/-- `xᵀAx ≤ Σ ρ_i x_i²` for a subinvariant `φ > 0`, `(Aφ)_i ≤ ρ_i φ_i`. -/
theorem qf_le_of_subinvariant (hsym : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    (hφ : ∀ i, 0 < φ i) (hsub : ∀ i, mv A φ i ≤ ρ i * φ i) (x : ι → ℝ) :
    bf A x x ≤ ∑ i, ρ i * x i ^ 2 := by
  have h := schur_identity A hsym φ hφ x (s := -1) (by norm_num)
  have h0 : 0 ≤ (1 / 2) * ∑ i, ∑ j, A i j * φ i * φ j * (x i / φ i + -1 * x j / φ j) ^ 2 := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    have := hφ i; have := hφ j; have := hA i j; positivity
  have := sub_term_le hφ hsub x
  linarith

/-- `xᵀAx ≥ Σ (2 A_ii - ρ_i) x_i²` for a subinvariant `φ > 0`. -/
theorem qf_ge_of_subinvariant (hsym : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    (hφ : ∀ i, 0 < φ i) (hsub : ∀ i, mv A φ i ≤ ρ i * φ i) (x : ι → ℝ) :
    ∑ i, (2 * A i i - ρ i) * x i ^ 2 ≤ bf A x x := by
  classical
  have h := schur_identity A hsym φ hφ x (s := 1) (by norm_num)
  have hdiag : ∑ i, 2 * A i i * x i ^ 2 ≤
      (1 / 2) * ∑ i, ∑ j, A i j * φ i * φ j * (x i / φ i + 1 * x j / φ j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsingle : A i i * φ i * φ i * (x i / φ i + 1 * x i / φ i) ^ 2 ≤
        ∑ j, A i j * φ i * φ j * (x i / φ i + 1 * x j / φ j) ^ 2 := by
      refine Finset.single_le_sum (f := fun j => A i j * φ i * φ j * (x i / φ i + 1 * x j / φ j) ^ 2)
        (fun j _ => ?_) (Finset.mem_univ i)
      have := hφ i; have := hφ j; have := hA i j; positivity
    have heq : A i i * φ i * φ i * (x i / φ i + 1 * x i / φ i) ^ 2 = 4 * (A i i * x i ^ 2) := by
      have := (hφ i).ne'; field_simp; ring
    nlinarith
  have := sub_term_le hφ hsub x
  have hsplit : ∑ i, (2 * A i i - ρ i) * x i ^ 2 =
      ∑ i, 2 * A i i * x i ^ 2 - ∑ i, ρ i * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- Schur test: `Σ_i (Σ_j A_ij |x_j|)² ≤ Σ_j x_j²` when `(Aφ)_i ≤ φ_i`. -/
theorem schur_norm_le (hsym : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    (hφ : ∀ i, 0 < φ i) (hsub : ∀ i, mv A φ i ≤ φ i) (x : ι → ℝ) :
    ∑ i, (∑ j, A i j * |x j|) ^ 2 ≤ ∑ j, x j ^ 2 := by
  have hrow : ∀ i, (∑ j, A i j * |x j|) ^ 2 ≤ φ i * ∑ j, A i j * (x j ^ 2 / φ j) := by
    intro i
    have h := CavityMean.weighted_cs (A i) (fun j => Real.sqrt (φ j))
      (fun j => |x j| / Real.sqrt (φ j)) (hA i)
    have e1 : ∑ j, A i j * Real.sqrt (φ j) * (|x j| / Real.sqrt (φ j)) = ∑ j, A i j * |x j| := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have := Real.sqrt_pos.mpr (hφ j)
      field_simp
    have e2 : ∑ j, A i j * Real.sqrt (φ j) ^ 2 = mv A φ i := by
      unfold mv
      exact Finset.sum_congr rfl fun j _ => by rw [Real.sq_sqrt (hφ j).le]
    have e3 : ∑ j, A i j * (|x j| / Real.sqrt (φ j)) ^ 2 = ∑ j, A i j * (x j ^ 2 / φ j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow, sq_abs, Real.sq_sqrt (hφ j).le]
    beta_reduce at h
    rw [e1, e2, e3] at h
    have h0 : 0 ≤ ∑ j, A i j * (x j ^ 2 / φ j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (div_nonneg (sq_nonneg _) (hφ j).le)
    exact h.trans (mul_le_mul_of_nonneg_right (hsub i) h0)
  refine (Finset.sum_le_sum fun i _ => hrow i).trans ?_
  have : ∑ i, φ i * ∑ j, A i j * (x j ^ 2 / φ j) = ∑ j, (x j ^ 2 / φ j) * mv A φ j := by
    unfold mv
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hsym i j]; ring
  rw [this]
  refine Finset.sum_le_sum fun j _ => ?_
  have hj := hφ j
  calc x j ^ 2 / φ j * mv A φ j ≤ x j ^ 2 / φ j * φ j :=
        mul_le_mul_of_nonneg_left (hsub j) (div_nonneg (sq_nonneg _) hj.le)
    _ = x j ^ 2 := by field_simp

/-!
## The spectral-type inequality (Step 6)
-/

/-- If `xᵀAx ≤ |x|²` and `|x|² + xᵀAx ≥ δ |x|²` for every real `x` (`A` symmetric, `0 < δ`),
then `|(I - A)x|² ≤ (2/δ)(|x|² - |Ax|²)`. -/
theorem spectral_ineq (hsym : ∀ i j, A i j = A j i) {δ : ℝ} (hδ : 0 < δ)
    (hup : ∀ x, bf A x x ≤ nsq x) (hlow : ∀ x, δ * nsq x ≤ nsq x + bf A x x) (x : ι → ℝ) :
    nsq (fun i => x i - mv A x i) ≤ 2 / δ * (nsq x - nsq (mv A x)) := by
  classical
  -- the positive form `P = I - A`
  set P : ι → ι → ℝ := fun i j => (if i = j then 1 else 0) - A i j with hP
  have hPsym : ∀ i j, P i j = P j i := fun i j => by
    simp only [hP, hsym i j]; by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hmvP : ∀ y i, mv P y i = y i - mv A y i := by
    intro y i
    unfold mv
    simp only [hP, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hbfP : ∀ y, bf P y y = nsq y - bf A y y := by
    intro y
    rw [bf_eq_sum_mv, bf_eq_sum_mv]
    unfold nsq
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hmvP]; ring
  have hpos : ∀ y, 0 ≤ bf P y y := fun y => by rw [hbfP]; linarith [hup y]
  set px : ι → ℝ := fun i => x i - mv A x i with hpx
  have hpxP : px = mv P x := funext fun i => (hmvP x i).symm
  -- `B(x, Px) = |Px|²`
  have hB1 : bf P x px = nsq px := by
    rw [bf_comm P hPsym, bf_eq_sum_mv, ← hpxP]
    unfold nsq; exact Finset.sum_congr rfl fun i _ => by ring
  have hcs := bf_cs P hPsym hpos x px
  rw [hB1] at hcs
  have hBpx : bf P px px ≤ (2 - δ) * nsq px := by
    rw [hbfP]; linarith [hlow px]
  have hB0 := hpos x
  have hn0 := nsq_nonneg px
  have hkey : nsq px ≤ (2 - δ) * bf P x x := by
    rcases hn0.lt_or_eq with hlt | heq
    · have : nsq px ^ 2 ≤ bf P x x * ((2 - δ) * nsq px) :=
        hcs.trans (mul_le_mul_of_nonneg_left hBpx hB0)
      nlinarith
    · rw [← heq]
      have hBle : bf P x x ≤ (2 - δ) * nsq x := by rw [hbfP]; linarith [hlow x]
      by_cases h2 : 0 ≤ 2 - δ
      · exact mul_nonneg h2 hB0
      · push Not at h2
        have : (2 - δ) * nsq x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2.le (nsq_nonneg x)
        have : bf P x x = 0 := le_antisymm (by linarith) hB0
        rw [this, mul_zero]
  -- `|x|² - |Ax|² = 2 B(x,x) - |Px|²`
  have hAx : nsq (mv A x) = nsq x - 2 * bf P x x + nsq px := by
    rw [hbfP, bf_eq_sum_mv]
    unfold nsq
    simp only [hpx]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  change nsq px ≤ 2 / δ * (nsq x - nsq (mv A x))
  rw [hAx, div_mul_eq_mul_div, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ 2 + δ),
    mul_nonneg (sq_nonneg δ) hB0]

/-!
## Complex vectors
-/

/-- `(Ax)_i` for a complex vector. -/
def cmv (A : ι → ι → ℝ) (x : ι → ℂ) (i : ι) : ℂ := ∑ j, (A i j : ℂ) * x j

/-- `|x|² = Σ_i |x_i|²` for a complex vector. -/
def cnsq (x : ι → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

theorem cnsq_nonneg (x : ι → ℂ) : 0 ≤ cnsq x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cnsq_eq (x : ι → ℂ) : cnsq x = nsq (fun i => (x i).re) + nsq (fun i => (x i).im) := by
  unfold cnsq nsq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem cmv_re (A : ι → ι → ℝ) (x : ι → ℂ) (i : ι) :
    (cmv A x i).re = mv A (fun j => (x j).re) i := by
  unfold cmv mv; rw [Complex.re_sum]; simp

theorem cmv_im (A : ι → ι → ℝ) (x : ι → ℂ) (i : ι) :
    (cmv A x i).im = mv A (fun j => (x j).im) i := by
  unfold cmv mv; rw [Complex.im_sum]; simp

/-- The complex version of `spectral_ineq` (real and imaginary parts separately). -/
theorem spectral_ineq_complex (hsym : ∀ i j, A i j = A j i) {δ : ℝ} (hδ : 0 < δ)
    (hup : ∀ x, bf A x x ≤ nsq x) (hlow : ∀ x, δ * nsq x ≤ nsq x + bf A x x) (x : ι → ℂ) :
    cnsq (fun i => x i - cmv A x i) ≤ 2 / δ * (cnsq x - cnsq (cmv A x)) := by
  have h1 := spectral_ineq hsym hδ hup hlow (fun j => (x j).re)
  have h2 := spectral_ineq hsym hδ hup hlow (fun j => (x j).im)
  rw [cnsq_eq, cnsq_eq, cnsq_eq]
  have e1 : (fun i => (x i - cmv A x i).re) = fun i => (x i).re - mv A (fun j => (x j).re) i :=
    funext fun i => by rw [Complex.sub_re, cmv_re]
  have e2 : (fun i => (x i - cmv A x i).im) = fun i => (x i).im - mv A (fun j => (x j).im) i :=
    funext fun i => by rw [Complex.sub_im, cmv_im]
  have e3 : (fun i => (cmv A x i).re) = mv A (fun j => (x j).re) := funext fun i => cmv_re A x i
  have e4 : (fun i => (cmv A x i).im) = mv A (fun j => (x j).im) := funext fun i => cmv_im A x i
  rw [e1, e2, e3, e4]
  linarith

/-- The `ℓ²` norm of a complex vector. -/
def cnorm (x : ι → ℂ) : ℝ := Real.sqrt (cnsq x)

theorem cnorm_eq (x : ι → ℂ) : cnorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq, WithLp.ofLp_toLp]; rfl

theorem cnorm_nonneg (x : ι → ℂ) : 0 ≤ cnorm x := Real.sqrt_nonneg _

theorem cnorm_sq (x : ι → ℂ) : cnorm x ^ 2 = cnsq x := Real.sq_sqrt (cnsq_nonneg x)

theorem cnorm_add_le (x y : ι → ℂ) : cnorm (x + y) ≤ cnorm x + cnorm y := by
  rw [cnorm_eq, cnorm_eq, cnorm_eq, WithLp.toLp_add]; exact norm_add_le _ _

theorem cnorm_sub_le (x y : ι → ℂ) : cnorm (x - y) ≤ cnorm x + cnorm y := by
  rw [cnorm_eq, cnorm_eq, cnorm_eq, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem cnorm_le_of_pointwise {x y : ι → ℂ} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : cnorm x ≤ cnorm y :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2)

theorem cnorm_eq_of_pointwise {x y : ι → ℂ} (h : ∀ i, ‖x i‖ = ‖y i‖) : cnorm x = cnorm y :=
  le_antisymm (cnorm_le_of_pointwise fun i => (h i).le) (cnorm_le_of_pointwise fun i => (h i).ge)

theorem norm_le_cnorm (x : ι → ℂ) (k : ι) : ‖x k‖ ≤ cnorm x := by
  rw [← Real.sqrt_sq (norm_nonneg (x k))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ k))

end ZeroEntrance

end BlockBand.Endpoints.Clock
