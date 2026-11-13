module

public import BlockBand.Internal.Contracts.CoareaPalm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Cauchy-kernel smoothing and the diagonal bound of the regular class

Deterministic support for the global weighted-density bound.

* `posSemidef_gammaShape`: `c (XᴴX)⁻¹ ⪰ 0` for every square `X` and `c ≥ 0` (so `freshGamma` is
  positive semidefinite).
* `cauchyKernel ε x = ε / (π (x² + ε²))` (the Poisson kernel of the upper half-plane at
  height `ε`), with `cauchyKernel_eq_im_inv`: `P_ε(x - λ) = π⁻¹ Im (λ - (x + iε))⁻¹` for real
  `x, λ` and `ε > 0`.
* `le_of_forall_lintegral_cauchyKernel_le`: a continuous nonnegative `ρ : ℝ → ℝ` all of
  whose Cauchy averages `∫ P_ε(x - e) ρ(e) de` (every `ε > 0`, Lebesgue measure) are at most
  `K ≥ 0` satisfies `ρ x ≤ K`. This is the passage from positive height to the pointwise
  density in the global weighted-density bound. The hypothesis `0 ≤ K` is needed: for `K < 0`
  and `ρ ≡ 0` the averages are `0 = ofReal K`.
* `quadForm_gammaShape_le`: for every Hermitian `F` (no norm bound), real `e, η`, `c > 0` and
  `Im m > 0`, with `X = F - e - c m`:
  `(F-e+iη) c(XᴴX)⁻¹ (F-e-iη) ⪯ c (2 + (2c²|m|² + η²)/(c² (Im m)²)) I` as quadratic forms
  (Euclidean norm). This is the bound `sup_λ c((λ-e)²+η²)/|λ-e-cm|² ≤ C`, obtained by
  diagonalizing `F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.WeightedDensity

open MeasureTheory Matrix Filter Topology
open scoped ENNReal ComplexOrder

/-!
## The Cauchy kernel
-/

/-- Cauchy (Poisson) kernel `P_ε(x) = ε / (π (x² + ε²))`. -/
def cauchyKernel (ε x : ℝ) : ℝ := ε / (Real.pi * (x ^ 2 + ε ^ 2))

theorem cauchyKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : 0 ≤ cauchyKernel ε x := by
  unfold cauchyKernel
  positivity

theorem continuous_cauchyKernel {ε : ℝ} (hε : 0 < ε) : Continuous (cauchyKernel ε) := by
  unfold cauchyKernel
  refine continuous_const.div (continuous_const.mul ((continuous_pow 2).add continuous_const))
    fun x => ?_
  have : 0 < x ^ 2 + ε ^ 2 := by positivity
  exact (mul_pos Real.pi_pos this).ne'

theorem measurable_cauchyKernel (ε : ℝ) : Measurable (cauchyKernel ε) := by
  unfold cauchyKernel
  fun_prop

/-- Resolvent form of the Cauchy kernel: `P_ε(x - λ) = π⁻¹ Im (λ - (x + iε))⁻¹`. -/
theorem cauchyKernel_eq_im_inv {ε : ℝ} (hε : 0 < ε) (x lam : ℝ) :
    cauchyKernel ε (x - lam) = Real.pi⁻¹ * ((((lam : ℂ) - (⟨x, ε⟩ : ℂ))⁻¹).im) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  unfold cauchyKernel
  have h1 : 0 < (x - lam) ^ 2 + ε ^ 2 := by positivity
  have h2 : (lam - x) * (lam - x) + (0 - ε) * (0 - ε) = (x - lam) ^ 2 + ε ^ 2 := by ring
  rw [h2]
  field_simp
  ring

/-- `∫_{x-d}^{x+d} P_ε(x - e) de = (2/π) arctan(d/ε)`. -/
theorem integral_cauchyKernel_window {ε : ℝ} (hε : 0 < ε) (x d : ℝ) :
    ∫ e in (x - d)..(x + d), cauchyKernel ε (x - e) =
      2 / Real.pi * Real.arctan (d / ε) := by
  have hderiv : ∀ e : ℝ, HasDerivAt (fun e => -(Real.pi⁻¹ * Real.arctan ((x - e) / ε)))
      (cauchyKernel ε (x - e)) e := by
    intro e
    have h1 : HasDerivAt (fun e : ℝ => (x - e) / ε) (-1 / ε) e := by
      have := ((hasDerivAt_id e).const_sub x).div_const ε
      simpa using this
    have h2 := ((Real.hasDerivAt_arctan ((x - e) / ε)).comp e h1).const_mul Real.pi⁻¹
    refine h2.neg.congr_deriv ?_
    unfold cauchyKernel
    have hp : 0 < Real.pi := Real.pi_pos
    have h4 : 0 < (x - e) ^ 2 + ε ^ 2 := by positivity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun e _ => hderiv e)]
  · simp only [sub_add_cancel_left, neg_div, Real.arctan_neg]
    ring_nf
  · exact ((continuous_cauchyKernel hε).comp (continuous_const.sub continuous_id)).intervalIntegrable
      _ _

/-- **Approximate-identity lower bound.** A continuous nonnegative `ρ` all of whose Cauchy
averages at `x` are at most `K ≥ 0` satisfies `ρ x ≤ K`. -/
theorem le_of_forall_lintegral_cauchyKernel_le {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {x K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → ∫⁻ e, ENNReal.ofReal (cauchyKernel ε (x - e) * ρ e) ≤ ENNReal.ofReal K) :
    ρ x ≤ K := by
  by_contra hlt
  rw [not_le] at hlt
  set a : ℝ := (K + ρ x) / 2 with ha
  set b : ℝ := (a + ρ x) / 2 with hb
  have hKa : K < a := by rw [ha]; linarith
  have hab : a < b := by rw [hb]; linarith
  have hbx : b < ρ x := by rw [hb]; linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- continuity window
  obtain ⟨δ, hδ, hδρ⟩ := Metric.continuous_iff.1 hρ x (ρ x - b) (by linarith)
  set d : ℝ := δ / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hwin : ∀ e ∈ Set.Icc (x - d) (x + d), b ≤ ρ e := by
    intro e he
    have hde : dist e x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [he.1, he.2]
    have := hδρ e hde
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  -- choose ε with (2/π) arctan(d/ε) > a/b
  set θ : ℝ := Real.pi / 2 * (a / b) with hθ
  have hab1 : a / b < 1 := (div_lt_one hb0).2 hab
  have hab0 : 0 < a / b := div_pos ha0 hb0
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ < Real.pi / 2 := by
    rw [hθ]; nlinarith [Real.pi_pos]
  set y : ℝ := Real.tan θ with hy
  have hy0 : 0 < y := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  set ε : ℝ := d / (y + 1) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hdε : d / ε = y + 1 := by rw [hε]; field_simp
  have harc : θ < Real.arctan (d / ε) := by
    rw [hdε]
    have : Real.arctan y = θ := by
      rw [hy]; exact Real.arctan_tan (by linarith) hθ1
    rw [← this]
    exact Real.arctan_strictMono (by linarith)
  have hmass : a / b < 2 / Real.pi * Real.arctan (d / ε) := by
    have hp : 0 < Real.pi := Real.pi_pos
    have : 2 / Real.pi * θ = a / b := by rw [hθ]; field_simp
    rw [← this]
    exact mul_lt_mul_of_pos_left harc (by positivity)
  -- lower bound for the lintegral
  have hP : ∀ e, 0 ≤ cauchyKernel ε (x - e) := fun e => cauchyKernel_nonneg hε0.le _
  have hPc : Continuous fun e => cauchyKernel ε (x - e) :=
    (continuous_cauchyKernel hε0).comp (continuous_const.sub continuous_id)
  have hS : MeasurableSet (Set.Icc (x - d) (x + d)) := measurableSet_Icc
  have hint : ∫ e in Set.Icc (x - d) (x + d), cauchyKernel ε (x - e) =
      2 / Real.pi * Real.arctan (d / ε) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_cauchyKernel_window hε0]
  have hlow : ENNReal.ofReal (b * (2 / Real.pi * Real.arctan (d / ε))) ≤
      ∫⁻ e, ENNReal.ofReal (cauchyKernel ε (x - e) * ρ e) := by
    calc ENNReal.ofReal (b * (2 / Real.pi * Real.arctan (d / ε)))
        = ENNReal.ofReal b * ∫⁻ e in Set.Icc (x - d) (x + d),
            ENNReal.ofReal (cauchyKernel ε (x - e)) := by
          rw [ENNReal.ofReal_mul hb0.le, ← hint,
            ofReal_integral_eq_lintegral_ofReal (hPc.integrableOn_Icc)
              (Eventually.of_forall hP)]
      _ = ∫⁻ e in Set.Icc (x - d) (x + d), ENNReal.ofReal (cauchyKernel ε (x - e) * b) := by
          rw [← lintegral_const_mul _ hPc.measurable.ennreal_ofReal]
          refine lintegral_congr fun e => ?_
          rw [ENNReal.ofReal_mul (hP e), mul_comm]
      _ ≤ ∫⁻ e in Set.Icc (x - d) (x + d), ENNReal.ofReal (cauchyKernel ε (x - e) * ρ e) :=
          setLIntegral_mono' hS fun e he =>
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hwin e he) (hP e))
      _ ≤ ∫⁻ e, ENNReal.ofReal (cauchyKernel ε (x - e) * ρ e) := setLIntegral_le_lintegral _ _
  have hfin := hlow.trans (h ε hε0)
  rw [ENNReal.ofReal_le_ofReal_iff hK] at hfin
  have : a < b * (2 / Real.pi * Real.arctan (d / ε)) := by
    have := mul_lt_mul_of_pos_left hmass hb0
    rwa [mul_div_cancel₀ _ hb0.ne'] at this
  linarith

/-!
## Positivity of the `Γ`-shape
-/

/-- `c (XᴴX)⁻¹` is positive semidefinite for every square `X` and `c ≥ 0`. -/
theorem posSemidef_gammaShape {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • (Xᴴ * X)⁻¹).PosSemidef :=
  (posSemidef_conjTranspose_mul_self X).inv.smul (by exact_mod_cast hc)

/-!
## Diagonalization
-/

section Diag

variable {N : ℕ}

/-- `U diag(g) U*`. -/
def diagConj (U : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  U * diagonal g * star U

variable {U : Matrix (Fin N) (Fin N) ℂ}

theorem diagConj_mul (hU : star U * U = 1) (g h : Fin N → ℂ) :
    diagConj U g * diagConj U h = diagConj U (g * h) := by
  unfold diagConj
  calc U * diagonal g * star U * (U * diagonal h * star U)
      = U * diagonal g * (star U * U) * diagonal h * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * diagonal (g * h) * star U := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; rfl

theorem diagConj_sub (g h : Fin N → ℂ) :
    diagConj U g - diagConj U h = diagConj U (g - h) := by
  unfold diagConj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rfl

theorem diagConj_smul (c : ℂ) (g : Fin N → ℂ) :
    c • diagConj U g = diagConj U (c • g) := by
  unfold diagConj
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem smul_one_eq_diagConj (hU : U * star U = 1) (w : ℂ) :
    w • (1 : Matrix (Fin N) (Fin N) ℂ) = diagConj U (fun _ => w) := by
  unfold diagConj
  have : diagonal (fun _ : Fin N => w) = w • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j; by_cases hij : i = j <;> simp [hij]
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

theorem conjTranspose_diagConj (g : Fin N → ℂ) :
    (diagConj U g)ᴴ = diagConj U (star g) := by
  unfold diagConj
  rw [conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star U), star_star,
    diagonal_conjTranspose, ← star_eq_conjTranspose, Matrix.mul_assoc]

theorem inv_diagConj (hU : star U * U = 1) (hU' : U * star U = 1) {g : Fin N → ℂ}
    (hg : ∀ i, g i ≠ 0) : (diagConj U g)⁻¹ = diagConj U g⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [diagConj_mul hU]
  have : g * g⁻¹ = fun _ => (1 : ℂ) := by
    funext i; simp [hg i]
  rw [this, ← smul_one_eq_diagConj hU', one_smul]

/-- `Re q*(U diag(r) U*)q ≤ C ‖q‖²` for real `r ≤ C`. -/
theorem quad_diagConj_le (hU' : U * star U = 1) {r : Fin N → ℝ} {C : ℝ} (hr : ∀ i, r i ≤ C)
    (q : Fin N → ℂ) :
    (star q ⬝ᵥ (diagConj U (fun i => (r i : ℂ)) *ᵥ q)).re ≤ C * ∑ a, ‖q a‖ ^ 2 := by
  set p : Fin N → ℂ := star U *ᵥ q with hp
  have hsq : star q ᵥ* U = star p := by
    rw [hp, star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hform : star q ⬝ᵥ (diagConj U (fun i => (r i : ℂ)) *ᵥ q) =
      star p ⬝ᵥ (diagonal (fun i => (r i : ℂ)) *ᵥ p) := by
    unfold diagConj
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hsq, hp]
  have hnorm : ∑ a, ‖p a‖ ^ 2 = ∑ a, ‖q a‖ ^ 2 := by
    have h1 : star p ⬝ᵥ p = star q ⬝ᵥ q := by
      rw [← hsq, ← dotProduct_mulVec, hp, mulVec_mulVec, hU', one_mulVec]
    have h2 : ∀ v : Fin N → ℂ, (star v ⬝ᵥ v).re = ∑ a, ‖v a‖ ^ 2 := by
      intro v
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.mul_re]
    rw [← h2, ← h2, h1]
  rw [hform, ← hnorm]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have : (star (p a) * ((r a : ℂ) * p a)).re = r a * ‖p a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hr a) (sq_nonneg _)

end Diag

/-- Scalar ratio bound `c((λ-e)²+η²)/|λ-e-cm|² ≤ c(2 + (2c²|m|²+η²)/(c² (Im m)²))`. -/
theorem ratio_gammaShape_le {c : ℝ} (hc : 0 < c) (e η lam : ℝ) {m : ℂ} (hm : 0 < m.im) :
    c * (Complex.normSq ((lam : ℂ) - ((e : ℂ) + (η : ℂ) * Complex.I)) /
        Complex.normSq ((lam : ℂ) - ((e : ℂ) + (c : ℂ) * m))) ≤
      c * (2 + (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / (c ^ 2 * m.im ^ 2)) := by
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.mul_im]
  have hnm : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  set s : ℝ := lam - (e + (c * m.re - 0 * m.im)) with hs
  set t : ℝ := c * m.im with ht
  have ht0 : 0 < t := mul_pos hc hm
  have hden : (lam - (e + (c * m.re - 0 * m.im))) * (lam - (e + (c * m.re - 0 * m.im))) +
      (0 - (0 + (c * m.im + 0 * m.re))) * (0 - (0 + (c * m.im + 0 * m.re))) = s ^ 2 + t ^ 2 := by
    rw [hs, ht]; ring
  have hnum : (lam - (e + (η * 0 - 0 * 1))) * (lam - (e + (η * 0 - 0 * 1))) +
      (0 - (0 + (η * 1 + 0 * 0))) * (0 - (0 + (η * 1 + 0 * 0))) =
      (s + c * m.re) ^ 2 + η ^ 2 := by
    rw [hs]; ring
  rw [hden, hnum]
  have hD : 0 < s ^ 2 + t ^ 2 := by positivity
  have hmt : c ^ 2 * m.im ^ 2 = t ^ 2 := by rw [ht]; ring
  rw [hmt, div_le_iff₀ hD]
  have hkey : (s + c * m.re) ^ 2 + η ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) + (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) := by
    rw [hnm]; nlinarith [sq_nonneg (s - c * m.re), sq_nonneg t, sq_nonneg (c * m.im)]
  have hfrac : (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) ≤
      (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / t ^ 2 * (s ^ 2 + t ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 0 ≤ 2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2 := by positivity
    nlinarith [sq_nonneg s]
  nlinarith [hkey, hfrac]

open BlockBand.Internal.Contracts.CoareaPalm in
/-- **Diagonal bound of the regular class.** For Hermitian `F`, `X = F - e - cm`,
`B = F - e - iη`: `Re (Bq)* c(XᴴX)⁻¹ (Bq) ≤ c (2 + (2c²|m|²+η²)/(c² (Im m)²)) ‖q‖²`. -/
theorem quadForm_gammaShape_le {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {c : ℝ} (hc : 0 < c) (e η : ℝ) {m : ℂ} (hm : 0 < m.im) (q : Fin N → ℂ) :
    quadForm ((c : ℂ) • ((F - ((e : ℂ) + (c : ℂ) * m) • 1)ᴴ * (F - ((e : ℂ) + (c : ℂ) * m) • 1))⁻¹)
        ((F - ((e : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q) ≤
      c * (2 + (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / (c ^ 2 * m.im ^ 2)) * ∑ a, ‖q a‖ ^ 2 := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hF.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem hF.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := Unitary.star_mul_self_of_mem hF.eigenvectorUnitary.2
  set lam : Fin N → ℂ := fun i => ((hF.eigenvalues i : ℝ) : ℂ)
  have hspec : F = diagConj U lam := by
    have h := hF.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  set w : ℂ := (e : ℂ) + (c : ℂ) * m
  set v : ℂ := (e : ℂ) + (η : ℂ) * Complex.I
  set aV : Fin N → ℂ := lam - fun _ => w
  set bV : Fin N → ℂ := lam - fun _ => v
  have hX : F - w • 1 = diagConj U aV := by
    rw [hspec, smul_one_eq_diagConj hU1, diagConj_sub]
  have hB : F - v • 1 = diagConj U bV := by
    rw [hspec, smul_one_eq_diagConj hU1, diagConj_sub]
  have ha0 : ∀ i, aV i ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp [aV, lam, w] at this
    rcases this with h1 | h1
    · exact hc.ne' h1
    · exact hm.ne' h1
  have hXX : (F - w • 1)ᴴ * (F - w • 1) = diagConj U (star aV * aV) := by
    rw [hX, conjTranspose_diagConj, diagConj_mul hU2]
  have hXXinv : ((F - w • 1)ᴴ * (F - w • 1))⁻¹ = diagConj U (star aV * aV)⁻¹ := by
    rw [hXX, inv_diagConj hU2 hU1]
    intro i
    simp only [Pi.mul_apply, Pi.star_apply]
    exact mul_ne_zero (star_ne_zero.2 (ha0 i)) (ha0 i)
  set r : Fin N → ℝ := fun i => c * (Complex.normSq (bV i) / Complex.normSq (aV i))
  have hmat : (diagConj U bV)ᴴ * ((c : ℂ) • diagConj U (star aV * aV)⁻¹) * diagConj U bV =
      diagConj U (fun i => (r i : ℂ)) := by
    rw [conjTranspose_diagConj, diagConj_smul, diagConj_mul hU2, diagConj_mul hU2]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.star_apply, Pi.smul_apply, Pi.inv_apply, smul_eq_mul, r]
    have hb := Complex.normSq_eq_conj_mul_self (z := bV i)
    have ha := Complex.normSq_eq_conj_mul_self (z := aV i)
    push_cast
    rw [hb, ha]
    simp only [Complex.star_def]
    have : (starRingEnd ℂ) (aV i) * aV i ≠ 0 := by
      rw [← ha]; exact_mod_cast (Complex.normSq_pos.2 (ha0 i)).ne'
    field_simp
  have hr : ∀ i, r i ≤ c * (2 + (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / (c ^ 2 * m.im ^ 2)) := by
    intro i
    exact ratio_gammaShape_le hc e η (hF.eigenvalues i) hm
  unfold quadForm
  rw [hXXinv, hB, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hmat]
  exact quad_diagConj_le hU1 hr q

end BlockBand.Critical.WeightedDensity
