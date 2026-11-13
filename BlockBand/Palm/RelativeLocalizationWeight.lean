module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Relative localization, Step 1: the weight `ψ` and `φ = e^{νψ}`

No measure, no limit in `N`. Parameters: a centre `E`, a smoothing distance `d > 0` and a
cap `R > 0` (the use sites take `d ≤ R`; no theorem here assumes it), and a rate `ν ≥ 0`.

* `rlG d y = d - √(y² + d²)` (the profile `d - √((x-E)²+d²)` of the paper),
* `rlTheta R y = T(y) (y + R) - R` with `T(y) = smoothTransition((y + 2R)/R)`: equal to `y`
  for `y ≥ -R`, to `-R` for `y ≤ -2R`, `y ≤ Θ(y) ≤ max(y, -R)`,
* `rlPsi E d R x = Θ(g(x - E))`, `rlPhi ν E d R x = exp(ν ψ(x))`.

Proved: explicit first and second derivatives, the bounds `|ψ'| ≤ C₀`,
`|ψ''| ≤ C₀/R + C₀/d` with an absolute constant `C₀` (from `smoothTransition`),
`|φ'| ≤ ν C₀ φ`, `|φ''| ≤ (ν C₀/R + ν C₀/d + ν² C₀²) φ`, `0 < φ ≤ 1`,
`φ(x) ≥ exp(-ν|x-E|)`, `φ(x) ≤ exp(-ν min(|x-E| - d, R))`, flatness (`ψ = -R`, `ψ' = 0`)
on `|x - E| > d + 2R`, the comparison `φ(y) ≤ exp(ν C₀ |y-x|) φ(x)`, and the second-order
Taylor bound used in Step 3. This replaces the paper's even/nonincreasing smooth choice; only
the listed properties are used downstream.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Real Set Filter Topology
open scoped ContDiff

/-!
### Derivatives of `smoothTransition`
-/

/-- First derivative of `smoothTransition`. -/
def st1 : ℝ → ℝ := deriv Real.smoothTransition

/-- Second derivative of `smoothTransition`. -/
def st2 : ℝ → ℝ := deriv st1

theorem st_contDiff : ContDiff ℝ ∞ Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := ⊤)

theorem st1_contDiff : ContDiff ℝ ∞ st1 :=
  (contDiff_infty_iff_deriv.mp st_contDiff).2

theorem st_hasDerivAt (x : ℝ) : HasDerivAt Real.smoothTransition (st1 x) x :=
  ((contDiff_infty_iff_deriv.mp st_contDiff).1 x).hasDerivAt

theorem st1_hasDerivAt (x : ℝ) : HasDerivAt st1 (st2 x) x :=
  ((contDiff_infty_iff_deriv.mp st1_contDiff).1 x).hasDerivAt

theorem st2_continuous : Continuous st2 :=
  st1_contDiff.continuous_deriv (by simp)

theorem st1_continuous : Continuous st1 := st1_contDiff.continuous

theorem st1_eq_zero_of_not_mem {x : ℝ} (hx : x < 0 ∨ 1 < x) : st1 x = 0 := by
  rcases hx with hx | hx
  · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    simp [st1, this.deriv_eq]
  · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    simp [st1, this.deriv_eq]

theorem st2_eq_zero_of_not_mem {x : ℝ} (hx : x < 0 ∨ 1 < x) : st2 x = 0 := by
  rcases hx with hx | hx
  · have : st1 =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact st1_eq_zero_of_not_mem (Or.inl hy)
    simp [st2, this.deriv_eq]
  · have : st1 =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact st1_eq_zero_of_not_mem (Or.inr hy)
    simp [st2, this.deriv_eq]

/-- A global bound on `|st1|` and `|st2|` (absolute constant). -/
theorem exists_st_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |st1 x| ≤ M ∧ |st2 x| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    st1_continuous.continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    st2_continuous.continuousOn
  refine ⟨max (max M₁ M₂) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact ⟨(hM₁ x hx).trans (le_max_left _ _ |>.trans (le_max_left _ _)),
      (hM₂ x hx).trans (le_max_right _ _ |>.trans (le_max_left _ _))⟩
  · have hx' : x < 0 ∨ 1 < x := by
      simp only [mem_Icc, not_and_or, not_le] at hx; exact hx
    rw [st1_eq_zero_of_not_mem hx', st2_eq_zero_of_not_mem hx']
    simp

/-- The absolute constant `C₀ = 1 + 3M` of the weight bounds. -/
def weightConst : ℝ := 1 + 3 * Classical.choose exists_st_bound

theorem weightM_nonneg : 0 ≤ Classical.choose exists_st_bound :=
  (Classical.choose_spec exists_st_bound).1

theorem abs_st1_le (x : ℝ) : |st1 x| ≤ Classical.choose exists_st_bound :=
  ((Classical.choose_spec exists_st_bound).2 x).1

theorem abs_st2_le (x : ℝ) : |st2 x| ≤ Classical.choose exists_st_bound :=
  ((Classical.choose_spec exists_st_bound).2 x).2

theorem one_le_weightConst : 1 ≤ weightConst := by
  unfold weightConst; linarith [weightM_nonneg]

theorem weightConst_pos : 0 < weightConst := lt_of_lt_of_le one_pos one_le_weightConst

/-!
### The cap `Θ`
-/

variable {R d ν E : ℝ}

/-- `T(y) = smoothTransition((y + 2R)/R)`. -/
def rlT (R y : ℝ) : ℝ := Real.smoothTransition ((y + 2 * R) / R)

/-- The cap `Θ(y) = T(y)(y + R) - R`. -/
def rlTheta (R y : ℝ) : ℝ := rlT R y * (y + R) - R

/-- `Θ'`. -/
def rlTheta1 (R y : ℝ) : ℝ := st1 ((y + 2 * R) / R) / R * (y + R) + rlT R y

/-- `Θ''`. -/
def rlTheta2 (R y : ℝ) : ℝ :=
  st2 ((y + 2 * R) / R) / R / R * (y + R) + 2 * (st1 ((y + 2 * R) / R) / R)

theorem rl_affine_hasDerivAt (y : ℝ) :
    HasDerivAt (fun y : ℝ => (y + 2 * R) / R) (1 / R) y :=
  ((hasDerivAt_id' y).add_const (2 * R)).div_const R

theorem rlT_hasDerivAt (hR : 0 < R) (y : ℝ) :
    HasDerivAt (rlT R) (st1 ((y + 2 * R) / R) / R) y := by
  have h := (st_hasDerivAt ((y + 2 * R) / R)).comp y (rl_affine_hasDerivAt (R := R) y)
  exact h.congr_deriv (by field_simp)

theorem rlT1_hasDerivAt (hR : 0 < R) (y : ℝ) :
    HasDerivAt (fun y => st1 ((y + 2 * R) / R) / R) (st2 ((y + 2 * R) / R) / R / R) y := by
  have h := ((st1_hasDerivAt ((y + 2 * R) / R)).comp y (rl_affine_hasDerivAt (R := R) y)).div_const R
  exact h.congr_deriv (by field_simp)

theorem rlTheta_hasDerivAt (hR : 0 < R) (y : ℝ) :
    HasDerivAt (rlTheta R) (rlTheta1 R y) y := by
  have h := ((rlT_hasDerivAt hR y).mul ((hasDerivAt_id' y).add_const R)).sub_const R
  exact h.congr_deriv (by simp only [rlTheta1]; ring)

theorem rlTheta1_hasDerivAt (hR : 0 < R) (y : ℝ) :
    HasDerivAt (rlTheta1 R) (rlTheta2 R y) y := by
  have h := ((rlT1_hasDerivAt hR y).mul ((hasDerivAt_id' y).add_const R)).add (rlT_hasDerivAt hR y)
  exact h.congr_deriv (by simp only [rlTheta2]; ring)

theorem rlT_nonneg (y : ℝ) : 0 ≤ rlT R y := Real.smoothTransition.nonneg _
theorem rlT_le_one (y : ℝ) : rlT R y ≤ 1 := Real.smoothTransition.le_one _

theorem rlT_eq_one (hR : 0 < R) {y : ℝ} (hy : -R ≤ y) : rlT R y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hR]; linarith

theorem rlT_eq_zero (hR : 0 < R) {y : ℝ} (hy : y ≤ -2 * R) : rlT R y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hR.le; linarith

theorem rlTheta_eq_self (hR : 0 < R) {y : ℝ} (hy : -R ≤ y) : rlTheta R y = y := by
  simp [rlTheta, rlT_eq_one hR hy]

theorem rlTheta_eq_neg (hR : 0 < R) {y : ℝ} (hy : y ≤ -2 * R) : rlTheta R y = -R := by
  simp [rlTheta, rlT_eq_zero hR hy]

theorem le_rlTheta (hR : 0 < R) (y : ℝ) : y ≤ rlTheta R y := by
  by_cases hy : -R ≤ y
  · rw [rlTheta_eq_self hR hy]
  · push Not at hy
    have h1 := rlT_le_one (R := R) y
    unfold rlTheta
    nlinarith

theorem rlTheta_le_max (hR : 0 < R) (y : ℝ) : rlTheta R y ≤ max y (-R) := by
  by_cases hy : -R ≤ y
  · rw [rlTheta_eq_self hR hy]; exact le_max_left _ _
  · push Not at hy
    have h0 := rlT_nonneg (R := R) y
    unfold rlTheta
    have : rlT R y * (y + R) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
    exact le_trans (by linarith) (le_max_right _ _)

/-- On the support of `st1(·)`, `|y + R| ≤ R`. -/
theorem abs_add_le_of_st (hR : 0 < R) {y : ℝ} (hy : (y + 2 * R) / R ∈ Icc (0 : ℝ) 1) :
    |y + R| ≤ R := by
  rw [mem_Icc, le_div_iff₀ hR, div_le_iff₀ hR] at hy
  rw [abs_le]; constructor <;> linarith

theorem abs_rlTheta1_le (hR : 0 < R) (y : ℝ) : |rlTheta1 R y| ≤ weightConst := by
  have hM := weightM_nonneg
  have key : |st1 ((y + 2 * R) / R) / R * (y + R)| ≤ Classical.choose exists_st_bound := by
    by_cases hy : (y + 2 * R) / R ∈ Icc (0 : ℝ) 1
    · rw [abs_mul, abs_div, abs_of_pos hR]
      have h1 := abs_st1_le ((y + 2 * R) / R)
      have h2 := abs_add_le_of_st hR hy
      calc |st1 ((y + 2 * R) / R)| / R * |y + R|
          ≤ |st1 ((y + 2 * R) / R)| / R * R :=
            mul_le_mul_of_nonneg_left h2 (div_nonneg (abs_nonneg _) hR.le)
        _ = |st1 ((y + 2 * R) / R)| := by field_simp
        _ ≤ _ := h1
    · have hy' : (y + 2 * R) / R < 0 ∨ 1 < (y + 2 * R) / R := by
        simp only [mem_Icc, not_and_or, not_le] at hy; exact hy
      simp [st1_eq_zero_of_not_mem hy', hM]
  have hT : |rlT R y| ≤ 1 := by
    rw [abs_of_nonneg (rlT_nonneg y)]; exact rlT_le_one y
  unfold rlTheta1 weightConst
  calc |st1 ((y + 2 * R) / R) / R * (y + R) + rlT R y|
      ≤ |st1 ((y + 2 * R) / R) / R * (y + R)| + |rlT R y| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem abs_rlTheta2_le (hR : 0 < R) (y : ℝ) : |rlTheta2 R y| ≤ weightConst / R := by
  have hM := weightM_nonneg
  set M := Classical.choose exists_st_bound
  have key : |rlTheta2 R y| ≤ 3 * M / R := by
    by_cases hy : (y + 2 * R) / R ∈ Icc (0 : ℝ) 1
    · have h1 := abs_st1_le ((y + 2 * R) / R)
      have h2 := abs_st2_le ((y + 2 * R) / R)
      have h3 := abs_add_le_of_st hR hy
      unfold rlTheta2
      have e1 : |st2 ((y + 2 * R) / R) / R / R * (y + R)| ≤ M / R := by
        rw [abs_mul, abs_div, abs_div, abs_of_pos hR]
        calc |st2 ((y + 2 * R) / R)| / R / R * |y + R|
            ≤ |st2 ((y + 2 * R) / R)| / R / R * R :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = |st2 ((y + 2 * R) / R)| / R := by field_simp
          _ ≤ M / R := div_le_div_of_nonneg_right h2 hR.le
      have e2 : |2 * (st1 ((y + 2 * R) / R) / R)| ≤ 2 * M / R := by
        rw [abs_mul, abs_div, abs_of_pos hR, abs_two, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hR.le) (by norm_num)
      calc _ ≤ |st2 ((y + 2 * R) / R) / R / R * (y + R)| + |2 * (st1 ((y + 2 * R) / R) / R)| :=
            abs_add_le _ _
        _ ≤ M / R + 2 * M / R := add_le_add e1 e2
        _ = 3 * M / R := by ring
    · have hy' : (y + 2 * R) / R < 0 ∨ 1 < (y + 2 * R) / R := by
        simp only [mem_Icc, not_and_or, not_le] at hy; exact hy
      simp only [rlTheta2, st1_eq_zero_of_not_mem hy', st2_eq_zero_of_not_mem hy']
      simp; positivity
  refine key.trans (div_le_div_of_nonneg_right ?_ hR.le)
  unfold weightConst; linarith

theorem rlTheta1_eq_zero (hR : 0 < R) {y : ℝ} (hy : y < -2 * R) : rlTheta1 R y = 0 := by
  have hu : (y + 2 * R) / R < 0 := div_neg_of_neg_of_pos (by linarith) hR
  simp [rlTheta1, st1_eq_zero_of_not_mem (Or.inl hu), rlT_eq_zero hR hy.le]

/-!
### The profile `g(y) = d - √(y² + d²)`
-/

/-- `g(y) = d - √(y² + d²)`. -/
def rlG (d y : ℝ) : ℝ := d - Real.sqrt (y ^ 2 + d ^ 2)

/-- `g'(y) = -y/√(y²+d²)`. -/
def rlG1 (d y : ℝ) : ℝ := -(y / Real.sqrt (y ^ 2 + d ^ 2))

/-- `g''(y) = -d²/((y²+d²)√(y²+d²))`. -/
def rlG2 (d y : ℝ) : ℝ := -(d ^ 2 / ((y ^ 2 + d ^ 2) * Real.sqrt (y ^ 2 + d ^ 2)))

theorem rl_sq_add_pos (hd : 0 < d) (y : ℝ) : 0 < y ^ 2 + d ^ 2 := by positivity

theorem rl_sqrt_pos (hd : 0 < d) (y : ℝ) : 0 < Real.sqrt (y ^ 2 + d ^ 2) :=
  Real.sqrt_pos.mpr (rl_sq_add_pos hd y)

theorem rl_sqrt_hasDerivAt (hd : 0 < d) (y : ℝ) :
    HasDerivAt (fun y => Real.sqrt (y ^ 2 + d ^ 2)) (y / Real.sqrt (y ^ 2 + d ^ 2)) y := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2 + d ^ 2) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).add_const (d ^ 2)
    exact this.congr_deriv (by ring)
  have h2 := h.sqrt (rl_sq_add_pos hd y).ne'
  have hs := rl_sqrt_pos hd y
  exact h2.congr_deriv (by field_simp)

theorem rlG_hasDerivAt (hd : 0 < d) (y : ℝ) : HasDerivAt (rlG d) (rlG1 d y) y := by
  have h := (rl_sqrt_hasDerivAt hd y).const_sub d
  exact h.congr_deriv (by simp [rlG1])

theorem rlG1_hasDerivAt (hd : 0 < d) (y : ℝ) : HasDerivAt (rlG1 d) (rlG2 d y) y := by
  have hs := rl_sqrt_pos hd y
  have h := ((hasDerivAt_id' y).div (rl_sqrt_hasDerivAt hd y) hs.ne').neg
  refine h.congr_deriv ?_
  have hsq : Real.sqrt (y ^ 2 + d ^ 2) ^ 2 = y ^ 2 + d ^ 2 :=
    Real.sq_sqrt (rl_sq_add_pos hd y).le
  simp only [rlG2]
  field_simp
  rw [hsq]; ring

theorem abs_rlG1_le (hd : 0 < d) (y : ℝ) : |rlG1 d y| ≤ 1 := by
  have hs := rl_sqrt_pos hd y
  rw [rlG1, abs_neg, abs_div, abs_of_pos hs, div_le_one hs]
  exact Real.abs_le_sqrt (by nlinarith)

theorem abs_rlG2_le (hd : 0 < d) (y : ℝ) : |rlG2 d y| ≤ 1 / d := by
  have hs := rl_sqrt_pos hd y
  have hq := rl_sq_add_pos hd y
  have hds : d ≤ Real.sqrt (y ^ 2 + d ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [rlG2, abs_neg, abs_div, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hd]
  have : d ^ 2 ≤ y ^ 2 + d ^ 2 := by nlinarith
  calc d ^ 2 * d ≤ (y ^ 2 + d ^ 2) * Real.sqrt (y ^ 2 + d ^ 2) :=
        mul_le_mul this hds hd.le hq.le
    _ = 1 * ((y ^ 2 + d ^ 2) * Real.sqrt (y ^ 2 + d ^ 2)) := by ring

theorem rlG_nonpos (y : ℝ) : rlG d y ≤ 0 := by
  have : d ≤ Real.sqrt (y ^ 2 + d ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  unfold rlG; linarith

theorem rlG_le (y : ℝ) : rlG d y ≤ d - |y| := by
  have : |y| ≤ Real.sqrt (y ^ 2 + d ^ 2) := Real.abs_le_sqrt (by nlinarith)
  unfold rlG; linarith

theorem neg_abs_le_rlG (hd : 0 < d) (y : ℝ) : -|y| ≤ rlG d y := by
  have h : Real.sqrt (y ^ 2 + d ^ 2) ≤ |y| + d := by
    rw [Real.sqrt_le_left (by positivity)]
    have := abs_nonneg y
    nlinarith [sq_abs y]
  unfold rlG; linarith

/-!
### The weight `ψ` and `φ = e^{νψ}`
-/

/-- `ψ(x) = Θ(g(x - E))`. -/
def rlPsi (E d R x : ℝ) : ℝ := rlTheta R (rlG d (x - E))

/-- `ψ'`. -/
def rlPsi1 (E d R x : ℝ) : ℝ := rlTheta1 R (rlG d (x - E)) * rlG1 d (x - E)

/-- `ψ''`. -/
def rlPsi2 (E d R x : ℝ) : ℝ :=
  rlTheta2 R (rlG d (x - E)) * rlG1 d (x - E) ^ 2 + rlTheta1 R (rlG d (x - E)) * rlG2 d (x - E)

/-- `φ(x) = exp(ν ψ(x))`. -/
def rlPhi (ν E d R x : ℝ) : ℝ := Real.exp (ν * rlPsi E d R x)

/-- `φ' = ν ψ' φ`. -/
def rlPhi1 (ν E d R x : ℝ) : ℝ := ν * rlPsi1 E d R x * rlPhi ν E d R x

/-- `φ'' = (ν ψ'' + ν² ψ'²) φ`. -/
def rlPhi2 (ν E d R x : ℝ) : ℝ :=
  (ν * rlPsi2 E d R x + ν ^ 2 * rlPsi1 E d R x ^ 2) * rlPhi ν E d R x

theorem rlGE_hasDerivAt (hd : 0 < d) (x : ℝ) :
    HasDerivAt (fun x => rlG d (x - E)) (rlG1 d (x - E)) x :=
  HasDerivAt.comp_sub_const x E (rlG_hasDerivAt hd (x - E))

theorem rlG1E_hasDerivAt (hd : 0 < d) (x : ℝ) :
    HasDerivAt (fun x => rlG1 d (x - E)) (rlG2 d (x - E)) x :=
  HasDerivAt.comp_sub_const x E (rlG1_hasDerivAt hd (x - E))

theorem rlPsi_hasDerivAt (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    HasDerivAt (rlPsi E d R) (rlPsi1 E d R x) x :=
  (rlTheta_hasDerivAt hR _).comp x (rlGE_hasDerivAt hd x)

theorem rlPsi1_hasDerivAt (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    HasDerivAt (rlPsi1 E d R) (rlPsi2 E d R x) x := by
  have hT := (rlTheta1_hasDerivAt hR (rlG d (x - E))).comp x (rlGE_hasDerivAt (E := E) hd x)
  have h := hT.mul (rlG1E_hasDerivAt (E := E) hd x)
  exact h.congr_deriv (by simp only [rlPsi2, Function.comp_apply]; ring)

theorem rlPhi_hasDerivAt (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    HasDerivAt (rlPhi ν E d R) (rlPhi1 ν E d R x) x := by
  have h := ((rlPsi_hasDerivAt (E := E) hd hR x).const_mul ν).exp
  exact h.congr_deriv (by simp only [rlPhi1, rlPhi]; ring)

theorem rlPhi1_hasDerivAt (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    HasDerivAt (rlPhi1 ν E d R) (rlPhi2 ν E d R x) x := by
  have h := ((rlPsi1_hasDerivAt (E := E) hd hR x).const_mul ν).mul
    (rlPhi_hasDerivAt (ν := ν) (E := E) hd hR x)
  exact h.congr_deriv (by simp only [rlPhi2, rlPhi1]; ring)

theorem rlPsi_contDiff (hd : 0 < d) (hR : 0 < R) : ContDiff ℝ 2 (rlPsi E d R) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (rlPsi_hasDerivAt hd hR x).differentiableAt, by simp, ?_⟩
  have hder : deriv (rlPsi E d R) = rlPsi1 E d R :=
    funext fun x => (rlPsi_hasDerivAt hd hR x).deriv
  rw [hder, contDiff_one_iff_deriv]
  refine ⟨fun x => (rlPsi1_hasDerivAt hd hR x).differentiableAt, ?_⟩
  have hder2 : deriv (rlPsi1 E d R) = rlPsi2 E d R :=
    funext fun x => (rlPsi1_hasDerivAt hd hR x).deriv
  rw [hder2]
  -- `rlPsi2` is an explicit continuous expression
  have hG : Continuous fun x => rlG d (x - E) :=
    continuous_iff_continuousAt.mpr fun x => (rlGE_hasDerivAt hd x).continuousAt
  have hG1 : Continuous fun x => rlG1 d (x - E) :=
    continuous_iff_continuousAt.mpr fun x => (rlG1E_hasDerivAt hd x).continuousAt
  have hG2 : Continuous fun x => rlG2 d (x - E) := by
    unfold rlG2
    refine (Continuous.div (by fun_prop) (by fun_prop) fun x => ?_).neg
    exact (mul_pos (rl_sq_add_pos hd _) (rl_sqrt_pos hd _)).ne'
  have hT1 : Continuous (rlTheta1 R) :=
    continuous_iff_continuousAt.mpr fun y => (rlTheta1_hasDerivAt hR y).continuousAt
  have hT2 : Continuous (rlTheta2 R) := by
    unfold rlTheta2
    have hu : Continuous fun y : ℝ => (y + 2 * R) / R := by fun_prop
    exact ((st2_continuous.comp hu).div_const R |>.div_const R |>.mul (by fun_prop)).add
      (((st1_continuous.comp hu).div_const R).const_mul 2)
  exact ((hT2.comp hG).mul (hG1.pow 2)).add ((hT1.comp hG).mul hG2)

theorem rlPhi_contDiff (hd : 0 < d) (hR : 0 < R) : ContDiff ℝ 2 (rlPhi ν E d R) :=
  ((rlPsi_contDiff hd hR).const_smul ν).exp

theorem abs_rlPsi1_le (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    |rlPsi1 E d R x| ≤ weightConst := by
  rw [rlPsi1, abs_mul]
  calc |rlTheta1 R (rlG d (x - E))| * |rlG1 d (x - E)| ≤ weightConst * 1 :=
        mul_le_mul (abs_rlTheta1_le hR _) (abs_rlG1_le hd _) (abs_nonneg _)
          weightConst_pos.le
    _ = weightConst := mul_one _

theorem abs_rlPsi2_le (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    |rlPsi2 E d R x| ≤ weightConst / R + weightConst / d := by
  rw [rlPsi2]
  have h1 : |rlG1 d (x - E) ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_rlG1_le hd _)
  calc _ ≤ |rlTheta2 R (rlG d (x - E)) * rlG1 d (x - E) ^ 2| +
        |rlTheta1 R (rlG d (x - E)) * rlG2 d (x - E)| := abs_add_le _ _
    _ ≤ weightConst / R * 1 + weightConst * (1 / d) := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul (abs_rlTheta2_le hR _) h1 (abs_nonneg _) (by
            have := weightConst_pos; positivity))
          (mul_le_mul (abs_rlTheta1_le hR _) (abs_rlG2_le hd _) (abs_nonneg _)
            weightConst_pos.le)
    _ = _ := by ring

theorem rlPhi_pos (x : ℝ) : 0 < rlPhi ν E d R x := Real.exp_pos _

theorem rlPsi_nonpos (hR : 0 < R) (x : ℝ) : rlPsi E d R x ≤ 0 := by
  have := rlTheta_le_max hR (rlG d (x - E))
  have := rlG_nonpos (d := d) (x - E)
  unfold rlPsi
  exact le_trans (by assumption) (max_le this (by linarith))

theorem rlPhi_le_one (hν : 0 ≤ ν) (hR : 0 < R) (x : ℝ) : rlPhi ν E d R x ≤ 1 := by
  rw [rlPhi, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hν (rlPsi_nonpos hR x)

theorem neg_abs_le_rlPsi (hd : 0 < d) (hR : 0 < R) (x : ℝ) : -|x - E| ≤ rlPsi E d R x :=
  (neg_abs_le_rlG hd _).trans (le_rlTheta hR _)

theorem rlPsi_le (hR : 0 < R) (x : ℝ) :
    rlPsi E d R x ≤ -min (|x - E| - d) R := by
  have h1 := rlTheta_le_max hR (rlG d (x - E))
  have h2 := rlG_le (d := d) (x - E)
  unfold rlPsi
  refine h1.trans (max_le ?_ ?_)
  · have : -min (|x - E| - d) R ≥ -(|x - E| - d) := neg_le_neg (min_le_left _ _)
    linarith
  · exact neg_le_neg (min_le_right _ _)

/-- Final weight: `φ(x) ≥ exp(-ν|x - E|)`. -/
theorem exp_neg_le_rlPhi (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    Real.exp (-(ν * |x - E|)) ≤ rlPhi ν E d R x := by
  rw [rlPhi, Real.exp_le_exp]
  have := neg_abs_le_rlPsi (E := E) hd hR x
  nlinarith

/-- Initial weight: `φ(x) ≤ exp(-ν min(|x-E| - d, R))`. -/
theorem rlPhi_le_exp (hν : 0 ≤ ν) (hR : 0 < R) (x : ℝ) :
    rlPhi ν E d R x ≤ Real.exp (-(ν * min (|x - E| - d) R)) := by
  rw [rlPhi, Real.exp_le_exp]
  have := rlPsi_le (E := E) (d := d) hR x
  nlinarith

theorem abs_rlPhi1_le (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    |rlPhi1 ν E d R x| ≤ ν * weightConst * rlPhi ν E d R x := by
  rw [rlPhi1, abs_mul, abs_mul, abs_of_nonneg hν, abs_of_pos (rlPhi_pos x)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_rlPsi1_le hd hR x) hν) (rlPhi_pos x).le

theorem abs_rlPhi2_le (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    |rlPhi2 ν E d R x| ≤
      (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) * rlPhi ν E d R x := by
  rw [rlPhi2, abs_mul, abs_of_pos (rlPhi_pos x)]
  refine mul_le_mul_of_nonneg_right ?_ (rlPhi_pos x).le
  calc _ ≤ |ν * rlPsi2 E d R x| + |ν ^ 2 * rlPsi1 E d R x ^ 2| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hν, abs_of_nonneg (pow_nonneg hν 2), abs_pow]
      have h1 := abs_rlPsi1_le (E := E) hd hR x
      have h2 := abs_rlPsi2_le (E := E) hd hR x
      have h3 : |rlPsi1 E d R x| ^ 2 ≤ weightConst ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact add_le_add (mul_le_mul_of_nonneg_left h2 hν)
        (mul_le_mul_of_nonneg_left h3 (by positivity))

/-- Flatness: `ψ = -R` on `|x - E| > d + 2R`. -/
theorem rlPsi_eq_of_far (hR : 0 < R) {x : ℝ} (hx : d + 2 * R < |x - E|) :
    rlPsi E d R x = -R := by
  unfold rlPsi
  apply rlTheta_eq_neg hR
  have := rlG_le (d := d) (x - E); linarith

theorem rlPsi1_eq_zero_of_far (hR : 0 < R) {x : ℝ} (hx : d + 2 * R < |x - E|) :
    rlPsi1 E d R x = 0 := by
  unfold rlPsi1
  rw [rlTheta1_eq_zero hR (by have := rlG_le (d := d) (x - E); linarith), zero_mul]

theorem rlPhi_eq_of_far (hR : 0 < R) {x : ℝ} (hx : d + 2 * R < |x - E|) :
    rlPhi ν E d R x = Real.exp (-(ν * R)) := by
  rw [rlPhi, rlPsi_eq_of_far hR hx]; ring_nf

theorem rlPhi1_eq_zero_of_far (hR : 0 < R) {x : ℝ} (hx : d + 2 * R < |x - E|) :
    rlPhi1 ν E d R x = 0 := by
  rw [rlPhi1, rlPsi1_eq_zero_of_far hR hx]; ring

/-- Comparison: `φ(y) ≤ exp(ν C₀ |y - x|) φ(x)`. -/
theorem rlPhi_le_exp_mul (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (x y : ℝ) :
    rlPhi ν E d R y ≤ Real.exp (ν * weightConst * |y - x|) * rlPhi ν E d R x := by
  have hlip : ‖rlPsi E d R y - rlPsi E d R x‖ ≤ weightConst * ‖y - x‖ :=
    (convex_univ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (rlPsi_hasDerivAt hd hR z).hasDerivWithinAt)
      (fun z _ => by rw [Real.norm_eq_abs]; exact abs_rlPsi1_le hd hR z) (mem_univ _) (mem_univ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  rw [rlPhi, rlPhi, ← Real.exp_add, Real.exp_le_exp]
  have := (abs_le.mp hlip).2
  nlinarith

/-!
### Second-order Taylor bound
-/

/-- If `f' = f1`, `f1' = f2` everywhere and `|f2| ≤ M` on the segment `[x, y]`, then
`|f y - f x - f1 x (y - x)| ≤ M (y - x)²`. -/
theorem abs_taylor2_le {f f1 f2 : ℝ → ℝ} (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z) {x y M : ℝ} (hM : ∀ z ∈ uIcc x y, |f2 z| ≤ M) :
    |f y - f x - f1 x * (y - x)| ≤ M * (y - x) ^ 2 := by
  have hconv : Convex ℝ (uIcc x y) := convex_uIcc x y
  have hx : x ∈ uIcc x y := left_mem_uIcc
  have hy : y ∈ uIcc x y := right_mem_uIcc
  -- first: |f1 z - f1 x| ≤ M |z - x| on the segment
  have h1 : ∀ z ∈ uIcc x y, |f1 z - f1 x| ≤ M * |y - x| := by
    intro z hz
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w _ => (hf1 w).hasDerivWithinAt) (fun w hw => by rw [Real.norm_eq_abs]; exact hM w hw)
      hx hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    refine this.trans ?_
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
    refine mul_le_mul_of_nonneg_left ?_ hM0
    rw [mem_uIcc] at hz
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have h2 := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - f1 x * z) (f' := fun z => f1 z - f1 x)
    (fun w _ => ((hf w).sub ((hasDerivAt_id w).const_mul (f1 x))).hasDerivWithinAt.congr_deriv
      (by simp))
    (fun w hw => by rw [Real.norm_eq_abs]; exact h1 w hw) hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h2
  calc |f y - f x - f1 x * (y - x)| = |f y - f1 x * y - (f x - f1 x * x)| := by ring_nf
    _ ≤ M * |y - x| * |y - x| := h2
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end BlockBand.Palm.RelativeLocalization
