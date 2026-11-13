module

public import BlockBand.SourceProcess.ProjSeparator.Layer

/-!
# Arithmetic of `ProjGammaMean`

* `sum_cross_sub_le`: summing the opposite-sign tensor `(σ/W)(x*y)(q_j*q_j)` over the columns of `Q`
  gives `(σ/W)(x*y)·frob Q`, with the summed error `K‖x‖‖y‖ frob Q`;
* `dZero_g_eq`: `D₀g/(2W) = σ₊ (g/(4η²))/W` (`σ₊ = 2η²D₀`);
* `mean_arith`: `min(η⁻², S)(C_M(δ₀+w²))² + C_O·covErr·S ≤ (2C_M² + C_O)H(δ₀² + gw² + gw(δ₀+δ₁+gw))`
  for `S = g/(4η²)`, `η⁻² ≤ H`, `0 ≤ w ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder

variable {W : ℕ}

theorem bilinear_one_self {n : Type*} [Fintype n] [DecidableEq n] (q : n → ℂ) :
    bilinear q 1 q = ((vecNorm q ^ 2 : ℝ) : ℂ) := by
  rw [bilinear, Matrix.one_mulVec, star_self_eq]

/-- The summed opposite-sign tensor and its error. -/
theorem sum_cross_sub_le {n : Type*} [Fintype n] [DecidableEq n] (x y : n → ℂ)
    (q : Fin W → n → ℂ) (a : Fin W → ℂ) (σ K : ℝ)
    (h : ∀ j, ‖a j - (σ : ℂ) / W * (bilinear x 1 y * bilinear (q j) 1 (q j))‖ ≤
      K * fourNorm x (q j) y (q j)) :
    ‖∑ j, a j - (σ : ℂ) / W * (∑ j, vecNorm (q j) ^ 2 : ℝ) * bilinear x 1 y‖ ≤
      K * vecNorm x * vecNorm y * ∑ j, vecNorm (q j) ^ 2 := by
  have e : ∑ j, a j - (σ : ℂ) / W * (∑ j, vecNorm (q j) ^ 2 : ℝ) * bilinear x 1 y =
      ∑ j, (a j - (σ : ℂ) / W * (bilinear x 1 y * bilinear (q j) 1 (q j))) := by
    simp only [bilinear_one_self, Finset.sum_sub_distrib, Complex.ofReal_sum, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (h j).trans (le_of_eq ?_))
  rw [fourNorm]; ring

/-- `D₀g/(2W) = σ₊(g/(4η²))/W`. -/
theorem dZero_g_eq {b E : ℝ} (hb0 : 0 < b) (h1 : -2 < E) (h2 : E < 2) (hη : etaZ b E ≠ 0)
    (g : ℝ) (W : ℝ) :
    transportD0 b E * g / (2 * W) = sigmaPlus b * (g / (4 * etaZ b E ^ 2)) / W := by
  rw [sigmaPlus_eq b E hb0 h1 h2]
  by_cases hW : W = 0
  · simp [hW]
  field_simp
  ring

/-- **The real arithmetic of `ProjGammaMean`.** -/
theorem mean_arith {δ₀ δ₁ g w η CM CO H nM : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hg : 0 ≤ g)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hη : 0 < η) (hCO : 0 ≤ CO) (hH : η⁻¹ ^ 2 ≤ H)
    (hnM0 : 0 ≤ nM) (hnM : nM ≤ CM * (δ₀ + w ^ 2)) :
    min (η⁻¹ ^ 2) (g / (4 * η ^ 2)) * nM ^ 2 +
        CO * (w ^ 2 + w * (δ₀ + δ₁ + g * w)) * (g / (4 * η ^ 2)) ≤
      (2 * CM ^ 2 + CO) * H * (δ₀ ^ 2 + g * w ^ 2 + g * w * (δ₀ + δ₁ + g * w)) := by
  have hS : g / (4 * η ^ 2) ≤ H * g := by
    have : g / (4 * η ^ 2) = η⁻¹ ^ 2 * g / 4 := by field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hH hg
    have h0 : 0 ≤ η⁻¹ ^ 2 * g := by positivity
    linarith
  have hS0 : 0 ≤ g / (4 * η ^ 2) := by positivity
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hn2 : nM ^ 2 ≤ 2 * CM ^ 2 * δ₀ ^ 2 + 2 * CM ^ 2 * w ^ 4 := by
    have := pow_le_pow_left₀ hnM0 hnM 2
    nlinarith [sq_nonneg (δ₀ - w ^ 2), sq_nonneg CM]
  have hw4 : w ^ 4 ≤ w ^ 2 := by
    have : w ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg w]
  set m := min (η⁻¹ ^ 2) (g / (4 * η ^ 2))
  have hm0 : 0 ≤ m := le_min (by positivity) hS0
  have hm1 : m ≤ H := (min_le_left _ _).trans hH
  have hm2 : m ≤ H * g := (min_le_right _ _).trans hS
  have T1 : m * nM ^ 2 ≤ 2 * CM ^ 2 * H * δ₀ ^ 2 + 2 * CM ^ 2 * H * (g * w ^ 2) := by
    have a1 : m * nM ^ 2 ≤ m * (2 * CM ^ 2 * δ₀ ^ 2) + m * (2 * CM ^ 2 * w ^ 4) := by
      nlinarith
    have a2 : m * (2 * CM ^ 2 * δ₀ ^ 2) ≤ H * (2 * CM ^ 2 * δ₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hm1 (by positivity)
    have a3 : m * (2 * CM ^ 2 * w ^ 4) ≤ H * g * (2 * CM ^ 2 * w ^ 2) :=
      mul_le_mul hm2 (by gcongr) (by positivity) (by positivity)
    nlinarith
  have hc0 : 0 ≤ w ^ 2 + w * (δ₀ + δ₁ + g * w) := by positivity
  have T2 : CO * (w ^ 2 + w * (δ₀ + δ₁ + g * w)) * (g / (4 * η ^ 2)) ≤
      CO * H * (g * w ^ 2 + g * w * (δ₀ + δ₁ + g * w)) := by
    have := mul_le_mul_of_nonneg_left hS (mul_nonneg hCO hc0)
    nlinarith
  have hP : 0 ≤ δ₀ ^ 2 + g * w ^ 2 + g * w * (δ₀ + δ₁ + g * w) := by positivity
  have hQ : 0 ≤ g * w * (δ₀ + δ₁ + g * w) := by positivity
  have hR : 0 ≤ H * (g * w ^ 2) := by positivity
  nlinarith [mul_nonneg hCO hH0, mul_nonneg (mul_nonneg hCO hH0) (sq_nonneg δ₀),
    mul_nonneg (mul_nonneg (sq_nonneg CM) hH0) hQ]

end BlockBand.SourceProcess.ProjSeparator
