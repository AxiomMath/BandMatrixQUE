module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GeneralVectorMDESpectralDomain
public import Mathlib

/-!
# `κ`-dependent stability of the ER `Ξ` multiplier

This module proves the deterministic spectral-domain stability of the ER `Ξ` kernel
for an arbitrary norm cutoff `C₀`.  The only input beyond the spectral parameters
being nonreal and in the same open half-plane is the `κ` clause of ER (2.9),
`κ ≤ |(m/|m|)² - 1|`, i.e. `κ |m| ≤ 2 |Im m|`.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, ER (2.9), (2.10), (2.18).
Normalization: `S = varianceProfile p` (row sums `1`, cyclic block symbol
`1 - 2b(1 - cos θ) ∈ [1 - 4b, 1]`), `m = erSemicircleStieltjes`, and
`Ξ = aS(1 - aS)⁻¹` with `a = m(z₁) m(z₂)`.

Mathematical content.  For `a = m(z₁) m(z₂)` with `z₁, z₂` on the ER domain in one
open half-plane, and every real `t ∈ [1 - 4b, 1]`,
`‖1 - a t‖ ≥ δ(κ,b) := min (κ²/2) (min 1 (2 - 4b))`
(`xiKappaMargin_le_norm_one_sub_mul`).  The proof splits on `Re a`: for `Re a ≤ 0`
the bound is `≥ 1` (or `≥ 2 - 4b` when `t ≤ 0`), while for `Re a > 0` the `κ` phase
condition gives `|Im a| ≥ (κ²/2)|a|`, and `|w| |1 - w| ≥ |Im w|` finishes.  The
contracting recurrence root then satisfies `1 - |ρ| ≥ γ := min (1/2) (δ/(3b))`, the
source jump satisfies `|J| ≥ δ`, and the two-path formula gives
`‖G_Ξ(k,l)‖ ≤ (2/(γ δ)) e^{-γ d(k,l)}`.

Quantifiers and uniformity: every `Params p` (every `n ≥ 4`, both parities,
every `W ≥ 1`, every `b ∈ (0,1/2)`), every `κ > 0`, every `ηExp` and every `C₀`.
The constants `xiKappaMargin κ b`, `xiKappaRate κ b`, `xiKappaConstant κ b` depend
only on `κ` and `b`, and are independent of `n`, `W`, `ηExp`, `C₀` and the spectral
parameters.  No limit is taken.

For ER clause (i) at an arbitrary cutoff, the `Ξ` half is proved for every `C₀`
(`norm_erXi_le_xi_kappa_control`), and the `Θ` half with a decay independent of `C₀`
at every height `min |Im z₁| |Im z₂| ≤ 1` (`norm_erTheta_le_control_of_height_le_one`).
At heights `> 1` the `Θ` block rate grows only like `log η`, while the control's block
rate is `a √η`; there the decay is chosen after `C₀`
(`ERGeneralVectorMDEThetaDomain.norm_erTheta_le_domain_control`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERGeneralVectorMDEXiKappa

open scoped BigOperators
open ERGeneralVectorMDE ERGeneralVectorMDECyclic ERCyclicDecay ERJumpNormalization ERPhysicalBridge ERHerglotz ERClause1 ERFourierInverse ERNearestNeighbor ERDiscreteFourier ERFourierAlgebra ERGeneralVectorMDESpectralDomain

local instance (p : Params) : NeZero p.n := p.nNeZero

/-!
### Explicit constants
-/

/-- The `κ`-dependent lower bound `δ(κ,b) = min (κ²/2) (min 1 (2 - 4b))` for the
`Ξ` stability multiplier on the cyclic symbol range `[1 - 4b, 1]`. -/
def xiKappaMargin (κ b : ℝ) : ℝ := min (κ ^ 2 / 2) (xiJumpMargin b)

/-- The `κ`-dependent block decay rate `γ(κ,b) = min (1/2) (δ(κ,b) / (3b))`. -/
def xiKappaRate (κ b : ℝ) : ℝ := min (1 / 2) (xiKappaMargin κ b / (3 * b))

/-- The `κ`-dependent prefactor `2 / (γ(κ,b) δ(κ,b))` of the `Ξ` Green kernel. -/
def xiKappaConstant (κ b : ℝ) : ℝ := 2 / (xiKappaRate κ b * xiKappaMargin κ b)

theorem xiKappaMargin_pos {κ b : ℝ} (hκ : 0 < κ) (hb : b < 1 / 2) :
    0 < xiKappaMargin κ b :=
  lt_min (by positivity) (xiJumpMargin_pos hb)

theorem xiKappaMargin_le_xiJumpMargin (κ b : ℝ) :
    xiKappaMargin κ b ≤ xiJumpMargin b := min_le_right _ _

theorem xiKappaMargin_le_one (κ b : ℝ) : xiKappaMargin κ b ≤ 1 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem xiKappaRate_pos {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    0 < xiKappaRate κ b :=
  lt_min (by norm_num) (div_pos (xiKappaMargin_pos hκ hb) (by positivity))

theorem xiKappaConstant_pos {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    0 < xiKappaConstant κ b :=
  div_pos (by norm_num)
    (mul_pos (xiKappaRate_pos hκ hb0 hb) (xiKappaMargin_pos hκ hb))

/-!
### The phase input
-/

/-- The `κ` clause of ER (2.9) in polar-free form: `κ |m| ≤ 2 |Im m|`. -/
theorem kappa_mul_norm_le_two_abs_im {κ : ℝ} {m : ℂ} (hm : m ≠ 0)
    (hκ : κ ≤ ‖(m / ‖m‖) ^ 2 - 1‖) :
    κ * ‖m‖ ≤ 2 * |m.im| := by
  have hR : (0 : ℝ) < ‖m‖ := norm_pos_iff.mpr hm
  have hRc : ((‖m‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hrw : (m / (‖m‖ : ℂ)) ^ 2 - 1 =
      m * (m - starRingEnd ℂ m) / ((‖m‖ : ℂ) ^ 2) := by
    have hconj : m * starRingEnd ℂ m = ((‖m‖ : ℂ)) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    field_simp
    linear_combination hconj
  have hsub : ‖m - starRingEnd ℂ m‖ = 2 * |m.im| := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  have hnorm : ‖(m / (‖m‖ : ℂ)) ^ 2 - 1‖ = 2 * |m.im| / ‖m‖ := by
    rw [hrw, norm_div, norm_mul, hsub, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    field_simp
  rw [hnorm] at hκ
  exact (le_div_iff₀ hR).1 hκ

/-- In one open half-plane, a positive real part of `m₁ m₂` forces its imaginary
part to dominate `(κ²/2) |m₁ m₂|`. -/
theorem kappa_sq_half_mul_norm_le_abs_im_mul {κ : ℝ} {m₁ m₂ : ℂ} (hκ : 0 ≤ κ)
    (h₁ : κ * ‖m₁‖ ≤ 2 * |m₁.im|) (h₂ : κ * ‖m₂‖ ≤ 2 * |m₂.im|)
    (hsame : 0 < m₁.im * m₂.im) (hre : 0 < (m₁ * m₂).re) :
    κ ^ 2 / 2 * ‖m₁ * m₂‖ ≤ |(m₁ * m₂).im| := by
  rw [Complex.mul_re] at hre
  rw [Complex.mul_im, norm_mul]
  set x₁ := m₁.re
  set y₁ := m₁.im
  set x₂ := m₂.re
  set y₂ := m₂.im
  have hxx : y₁ * y₂ < x₁ * x₂ := by linarith
  have hsq : (2 * (y₁ * y₂)) ^ 2 ≤ (x₁ * y₂ + x₂ * y₁) ^ 2 := by
    nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁)]
  have hlow : 2 * (y₁ * y₂) ≤ |x₁ * y₂ + x₂ * y₁| := by
    have := sq_le_sq.mp hsq
    rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * (y₁ * y₂))] at this
    exact this
  have hy : y₁ * y₂ = |y₁| * |y₂| := by
    rw [← abs_mul, abs_of_pos hsame]
  have hprod : (κ * ‖m₁‖) * (κ * ‖m₂‖) ≤ (2 * |y₁|) * (2 * |y₂|) :=
    mul_le_mul h₁ h₂ (by positivity) (by positivity)
  rw [show x₁ * y₂ + y₁ * x₂ = x₁ * y₂ + x₂ * y₁ by ring]
  calc κ ^ 2 / 2 * (‖m₁‖ * ‖m₂‖) = ((κ * ‖m₁‖) * (κ * ‖m₂‖)) / 2 := by ring
    _ ≤ ((2 * |y₁|) * (2 * |y₂|)) / 2 := by linarith
    _ = 2 * (y₁ * y₂) := by rw [hy]; ring
    _ ≤ _ := hlow

/-- `|w| |1 - w| ≥ |Im w|`, from the identity
`|w|² |1 - w|² = (Im w)² + (|w|² - Re w)²`. -/
theorem abs_im_le_norm_mul_norm_one_sub (w : ℂ) :
    |w.im| ≤ ‖w‖ * ‖1 - w‖ := by
  have hkey : (‖w‖ * ‖1 - w‖) ^ 2 =
      w.im ^ 2 + (Complex.normSq w - w.re) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hsq : w.im ^ 2 ≤ (‖w‖ * ‖1 - w‖) ^ 2 := by
    rw [hkey]
    nlinarith [sq_nonneg (Complex.normSq w - w.re)]
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ * ‖1 - w‖)] at this

/-- **`κ`-dependent stability of the `Ξ` multiplier on the cyclic symbol range.**
For `‖α‖ < 1` with either `Re α ≤ 0` or `(κ²/2)|α| ≤ |Im α|`, and every real
`t ∈ [1 - 4b, 1]`, `‖1 - α t‖ ≥ δ(κ,b)`. -/
theorem xiKappaMargin_le_norm_one_sub_mul (p : Params) {κ : ℝ} {α : ℂ}
    (hα : ‖α‖ < 1) (hphase : α.re ≤ 0 ∨ κ ^ 2 / 2 * ‖α‖ ≤ |α.im|)
    {t : ℝ} (ht0 : 1 - 4 * p.b ≤ t) (_ht1 : t ≤ 1) :
    xiKappaMargin κ p.b ≤ ‖1 - α * t‖ := by
  have hjump1 : xiJumpMargin p.b ≤ 1 := min_le_left _ _
  have hmarg := xiKappaMargin_le_xiJumpMargin κ p.b
  rcases le_or_gt t 0 with htn | htp
  · have hrev := ERJumpNormalization.one_sub_norm_le_norm_one_sub (α * (t : ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos htn] at hrev
    have h2 : xiJumpMargin p.b ≤ 2 - 4 * p.b := min_le_right _ _
    have : 1 + t ≤ 1 - ‖α‖ * -t := by nlinarith [norm_nonneg α]
    linarith
  · rcases hphase with hre | him
    · have hreal : 1 ≤ (1 - α * (t : ℂ)).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        nlinarith
      have := hreal.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
      linarith
    · by_cases hα0 : α = 0
      · simp only [hα0, zero_mul, sub_zero, norm_one]
        exact (xiKappaMargin_le_one κ p.b)
      · have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
        have hw := abs_im_le_norm_mul_norm_one_sub (α * (t : ℂ))
        have him' : (α * (t : ℂ)).im = α.im * t := by
          simp [Complex.mul_im]
        rw [him', abs_mul, abs_of_pos htp, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htp] at hw
        have hmain : κ ^ 2 / 2 * (‖α‖ * t) ≤ (‖α‖ * t) * ‖1 - α * (t : ℂ)‖ := by
          nlinarith
        have hk : κ ^ 2 / 2 ≤ ‖1 - α * (t : ℂ)‖ := by
          have hpos : 0 < ‖α‖ * t := mul_pos hαpos htp
          nlinarith
        exact (min_le_left _ _).trans hk

/-- A uniform multiplier lower bound on the symbol range `[1 - 4b, 1]` forces the
contracting recurrence root to stay `min (1/2) (δ/(3b))` inside the unit disk. -/
theorem min_half_margin_div_le_one_sub_norm_contractingRoot (p : Params)
    {α : ℂ} {δ : ℝ} (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (H : ∀ t : ℝ, 1 - 4 * p.b ≤ t → t ≤ 1 → δ ≤ ‖1 - α * t‖) :
    min (1 / 2) (δ / (3 * p.b)) ≤ 1 - ‖contractingRecurrenceRoot p α‖ := by
  set ρ := contractingRecurrenceRoot p α with hρdef
  have hρ0 : ρ ≠ 0 := contractingRecurrenceRoot_ne_zero p hα0
  have hρlt : ‖ρ‖ < 1 := norm_contractingRecurrenceRoot_lt_one p hα0 hα
  by_cases hr : ‖ρ‖ ≤ 1 / 2
  · exact (min_le_left _ _).trans (by linarith)
  · rw [not_le] at hr
    set r := ‖ρ‖ with hrdef
    have hrpos : 0 < r := by linarith
    have hchar := contractingRecurrenceRoot_characteristic p hα0
    rw [← hρdef] at hchar
    have hrec :
        recurrenceDiagonal p α = recurrenceBond p α * (ρ + ρ⁻¹) := by
      apply (mul_right_cancel₀ hρ0)
      field_simp [hρ0]
      linear_combination -hchar
    have hone :
        (1 : ℂ) = α * ((p.c : ℂ) + p.b * ρ + p.b * ρ⁻¹) := by
      rw [show (1 : ℂ) = recurrenceDiagonal p α + α * p.c by
        unfold recurrenceDiagonal; ring, hrec]
      unfold recurrenceBond
      ring
    have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    set u : ℂ := ρ / (r : ℂ) with hudef
    have hunorm : ‖u‖ = 1 := by
      rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
        ← hrdef, div_self hrpos.ne']
    have hu0 : u ≠ 0 := by
      intro h; rw [h, norm_zero] at hunorm; norm_num at hunorm
    have hconj : starRingEnd ℂ u = u⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hunorm]
      simp
    have huinv : u⁻¹ = (r : ℂ) * ρ⁻¹ := by
      rw [hudef]; field_simp
    have hure : |u.re| ≤ 1 := (Complex.abs_re_le_norm u).trans hunorm.le
    rw [abs_le] at hure
    have hc : p.c = 1 - 2 * p.b := by linarith [p.c_add_two_b]
    set t : ℝ := p.c + 2 * p.b * u.re with htdef
    have ht0 : 1 - 4 * p.b ≤ t := by rw [htdef, hc]; nlinarith [p.b_pos]
    have ht1 : t ≤ 1 := by rw [htdef, hc]; nlinarith [p.b_pos]
    have htC : ((t : ℝ) : ℂ) = (p.c : ℂ) + p.b * (u + u⁻¹) := by
      rw [← hconj, Complex.add_conj, htdef]
      push_cast
      ring
    have hdiff : 1 - α * (t : ℂ) =
        α * p.b * ((ρ - u) + (ρ⁻¹ - u⁻¹)) := by
      rw [htC]
      linear_combination hone
    have hρu : ρ - u = ρ * (((1 - r⁻¹ : ℝ)) : ℂ) := by
      rw [hudef]; push_cast; field_simp
    have hρu' : ρ⁻¹ - u⁻¹ = ρ⁻¹ * (((1 - r : ℝ)) : ℂ) := by
      rw [huinv]; push_cast; ring
    have hrinv : 1 < r⁻¹ := one_lt_inv_iff₀.mpr ⟨hrpos, hρlt⟩
    have hrinv2 : r⁻¹ < 2 := by
      rw [inv_lt_comm₀ hrpos (by norm_num)]; linarith
    have hn1 : ‖ρ - u‖ = 1 - r := by
      rw [hρu, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith), ← hrdef]
      field_simp
      ring
    have hn2 : ‖ρ⁻¹ - u⁻¹‖ = r⁻¹ * (1 - r) := by
      rw [hρu', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), ← hrdef]
    have hbound : δ ≤ 3 * p.b * (1 - r) := by
      have h := H t ht0 ht1
      rw [hdiff, norm_mul, norm_mul] at h
      have hb : ‖(p.b : ℂ)‖ = p.b := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos p.b_pos]
      rw [hb] at h
      have htri := norm_add_le (ρ - u) (ρ⁻¹ - u⁻¹)
      rw [hn1, hn2] at htri
      have hX : ‖(ρ - u) + (ρ⁻¹ - u⁻¹)‖ ≤ 3 * (1 - r) := by
        nlinarith
      have hαb : ‖α‖ * p.b ≤ p.b := by nlinarith [p.b_pos, norm_nonneg α]
      calc δ ≤ ‖α‖ * p.b * ‖(ρ - u) + (ρ⁻¹ - u⁻¹)‖ := h
        _ ≤ p.b * (3 * (1 - r)) :=
          mul_le_mul hαb hX (norm_nonneg _) p.b_pos.le
        _ = 3 * p.b * (1 - r) := by ring
    have hden : 0 < 3 * p.b := by linarith [p.b_pos]
    exact (min_le_right _ _).trans ((div_le_iff₀ hden).2 (by linarith))

/-- The same multiplier lower bound controls the exact recurrence source jump:
its square is `(1 - α)(1 - α(1 - 4b))`, a product of two multipliers on the
symbol range. -/
theorem margin_le_norm_recurrenceJump (p : Params) {α : ℂ} {δ : ℝ}
    (hα0 : α ≠ 0) (hδ : 0 ≤ δ)
    (H : ∀ t : ℝ, 1 - 4 * p.b ≤ t → t ≤ 1 → δ ≤ ‖1 - α * t‖) :
    δ ≤ ‖recurrenceJump p α (contractingRecurrenceRoot p α)‖ := by
  have hsq := recurrenceJump_sq_eq_discriminant p
    (contractingRecurrenceRoot_ne_zero p hα0)
    (contractingRecurrenceRoot_characteristic p hα0)
  have hc : p.c - 2 * p.b = 1 - 4 * p.b := by linarith [p.c_add_two_b]
  have h1 : δ ≤ ‖1 - α‖ := by
    have := H 1 (by linarith [p.b_pos]) le_rfl
    simpa using this
  have h2 : δ ≤ ‖1 - α * ((p.c - 2 * p.b : ℝ) : ℂ)‖ :=
    H _ (by rw [hc]) (by rw [hc]; linarith [p.b_pos])
  have hJ : δ ^ 2 ≤
      ‖recurrenceJump p α (contractingRecurrenceRoot p α)‖ ^ 2 := by
    rw [← norm_pow, hsq, recurrenceDiscriminant_factor, norm_mul, sq]
    exact mul_le_mul h1 h2 hδ (norm_nonneg _)
  nlinarith [norm_nonneg (recurrenceJump p α (contractingRecurrenceRoot p α))]

/-- Cyclic exponential bound for the scalar Green kernel under a uniform
multiplier lower bound `δ` on the symbol range: with `γ = min (1/2) (δ/(3b))`,
`‖G(k,l)‖ ≤ 2 e^{-γ d(k,l)} / (γ δ)`. -/
theorem norm_fourierGreenKernel_le_of_symbolMargin (p : Params) {α : ℂ} {δ : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) (hδ : 0 < δ)
    (H : ∀ t : ℝ, 1 - 4 * p.b ≤ t → t ≤ 1 → δ ≤ ‖1 - α * t‖)
    (x y : ZMod p.n) :
    ‖fourierGreenKernel p α x y‖ ≤
      2 * Real.exp (-(min (1 / 2) (δ / (3 * p.b))) * cyclicBlockDistance p x y) /
        (min (1 / 2) (δ / (3 * p.b)) * δ) := by
  set γ := min (1 / 2) (δ / (3 * p.b)) with hγdef
  let ρ := contractingRecurrenceRoot p α
  have hbase := norm_fourierGreenKernel_le_twoPath p hα0 hα x y
  have hρ := norm_contractingRecurrenceRoot_lt_one p hα0 hα
  have hgap : γ ≤ 1 - ‖ρ‖ :=
    min_half_margin_div_le_one_sub_norm_contractingRoot p hα0 hα H
  have hγ0 : 0 < γ := lt_min (by norm_num) (div_pos hδ (by linarith [p.b_pos]))
  have hpowers := twoPathPowers_le_twice_shorter
    (r := ‖ρ‖) (n := p.n) (d := orientedBlockDistance p x y)
    (norm_nonneg ρ) hρ.le
  have hexp0 := pow_le_exp_neg_gap (norm_nonneg ρ) (cyclicBlockDistance p x y)
  have hexp : ‖ρ‖ ^ cyclicBlockDistance p x y ≤
      Real.exp (-γ * cyclicBlockDistance p x y) := by
    refine hexp0.trans (Real.exp_le_exp.mpr ?_)
    have hd : 0 ≤ (cyclicBlockDistance p x y : ℝ) := by positivity
    nlinarith
  have hden : γ ≤ ‖1 - ρ ^ p.n‖ :=
    hgap.trans (one_sub_norm_le_norm_one_sub_pow p hρ)
  have hjump := margin_le_norm_recurrenceJump p hα0 hδ.le H
  dsimp only [ρ] at hbase hpowers hexp hden hjump
  calc
    ‖fourierGreenKernel p α x y‖ ≤
        (‖contractingRecurrenceRoot p α‖ ^ orientedBlockDistance p x y +
          ‖contractingRecurrenceRoot p α‖ ^ (p.n - orientedBlockDistance p x y)) /
          (‖1 - contractingRecurrenceRoot p α ^ p.n‖ *
            ‖recurrenceJump p α (contractingRecurrenceRoot p α)‖) := hbase
    _ ≤ (2 * ‖contractingRecurrenceRoot p α‖ ^ cyclicBlockDistance p x y) /
          (‖1 - contractingRecurrenceRoot p α ^ p.n‖ *
            ‖recurrenceJump p α (contractingRecurrenceRoot p α)‖) :=
      div_le_div_of_nonneg_right hpowers (by positivity)
    _ ≤ (2 * Real.exp (-γ * cyclicBlockDistance p x y)) /
          (‖1 - contractingRecurrenceRoot p α ^ p.n‖ *
            ‖recurrenceJump p α (contractingRecurrenceRoot p α)‖) := by
      gcongr
    _ ≤ (2 * Real.exp (-γ * cyclicBlockDistance p x y)) / (γ * δ) := by
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos hγ0 hδ)
      exact mul_le_mul hden hjump hδ.le (norm_nonneg _)

/-!
### Specialization to the ER spectral domain
-/

theorem erSemicircleStieltjes_ne_zero (z : ℂ) : erSemicircleStieltjes z ≠ 0 := by
  intro hm
  have h := erSemicircleStieltjes_dyson z
  simp [hm] at h

/-- On the ER domain (any `C₀`), in one open half-plane, the `Ξ` multiplier
`m(z₁) m(z₂)` either has nonpositive real part or satisfies the `κ` phase bound
`(κ²/2) |m₁ m₂| ≤ |Im (m₁ m₂)|`. -/
theorem xi_phase_of_spectralDomain (p : Params) {κ ηExp C₀ : ℝ} (hκ : 0 < κ)
    {z₁ z₂ : ℂ} (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂) (hsame : ERSameHalfPlane z₁ z₂) :
    (erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂).re ≤ 0 ∨
      κ ^ 2 / 2 * ‖erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂‖ ≤
        |(erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂).im| := by
  have hz₁ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have hk₁ := kappa_mul_norm_le_two_abs_im (erSemicircleStieltjes_ne_zero z₁) h₁.2.2
  have hk₂ := kappa_mul_norm_le_two_abs_im (erSemicircleStieltjes_ne_zero z₂) h₂.2.2
  have hs₁ := erSemicircleStieltjes_same_sign hz₁
  have hs₂ := erSemicircleStieltjes_same_sign hz₂
  have himprod : 0 < (erSemicircleStieltjes z₁).im * (erSemicircleStieltjes z₂).im := by
    dsimp only [ERSameHalfPlane] at hsame
    rcases lt_or_gt_of_ne hz₁ with hneg | hpos
    · have hz₂' : z₂.im < 0 := by nlinarith
      have hm₁ : (erSemicircleStieltjes z₁).im < 0 := by nlinarith
      have hm₂ : (erSemicircleStieltjes z₂).im < 0 := by nlinarith
      exact mul_pos_of_neg_of_neg hm₁ hm₂
    · have hz₂' : 0 < z₂.im := by nlinarith
      have hm₁ : 0 < (erSemicircleStieltjes z₁).im := by nlinarith
      have hm₂ : 0 < (erSemicircleStieltjes z₂).im := by nlinarith
      positivity
  rcases le_or_gt (erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂).re 0 with hre | hre
  · exact Or.inl hre
  · exact Or.inr (kappa_sq_half_mul_norm_le_abs_im_mul hκ.le hk₁ hk₂ himprod hre)

theorem norm_xiMultiplier_lt_one {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
    ‖erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂‖ < 1 := by
  rw [norm_mul]
  have hm₁ := norm_erSemicircleStieltjes_lt_one hz₁
  have hm₂ := norm_erSemicircleStieltjes_lt_one hz₂
  nlinarith [norm_nonneg (erSemicircleStieltjes z₁),
    norm_nonneg (erSemicircleStieltjes z₂)]

/-- **`κ`-stability of the `Ξ` multiplier on the ER domain.**  For `z₁, z₂`
in `ERSpectralDomain p κ ηExp C₀` (any `C₀`, any `ηExp`) and in one open half-plane,
`‖1 - m(z₁) m(z₂) t‖ ≥ xiKappaMargin κ b` for every real `t ∈ [1 - 4b, 1]`. -/
theorem xiKappaMargin_le_norm_one_sub_xiMultiplier (p : Params) {κ ηExp C₀ : ℝ}
    (hκ : 0 < κ) {z₁ z₂ : ℂ} (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂) (hsame : ERSameHalfPlane z₁ z₂)
    {t : ℝ} (ht0 : 1 - 4 * p.b ≤ t) (ht1 : t ≤ 1) :
    xiKappaMargin κ p.b ≤
      ‖1 - erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂ * t‖ :=
  xiKappaMargin_le_norm_one_sub_mul p
    (norm_xiMultiplier_lt_one (ERDeterministicMDECore.spectralDomain_im_ne_zero h₁)
      (ERDeterministicMDECore.spectralDomain_im_ne_zero h₂))
    (xi_phase_of_spectralDomain p hκ h₁ h₂ hsame) ht0 ht1

/-- **`κ`-dependent exponential bound for the `Ξ` Green kernel.**
On `ERSpectralDomain p κ ηExp C₀` with same half-plane, for every pair of blocks,
`‖G_{m(z₁)m(z₂)}(x,y)‖ ≤ xiKappaConstant κ b · exp(-xiKappaRate κ b · d(x,y))`,
`d` the cyclic block distance.  Constants depend only on `κ` and `b`. -/
theorem norm_fourierGreenKernel_le_xi_kappa (p : Params) {κ ηExp C₀ : ℝ} (hκ : 0 < κ)
    {z₁ z₂ : ℂ} (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂) (hsame : ERSameHalfPlane z₁ z₂)
    (x y : ZMod p.n) :
    ‖fourierGreenKernel p (erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂) x y‖ ≤
      xiKappaConstant κ p.b *
        Real.exp (-(xiKappaRate κ p.b) * cyclicBlockDistance p x y) := by
  have hz₁ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have h := norm_fourierGreenKernel_le_of_symbolMargin p
    (mul_ne_zero (erSemicircleStieltjes_ne_zero z₁) (erSemicircleStieltjes_ne_zero z₂))
    (norm_xiMultiplier_lt_one hz₁ hz₂) (xiKappaMargin_pos hκ p.b_lt_half)
    (fun t ht0 ht1 => xiKappaMargin_le_norm_one_sub_xiMultiplier p hκ h₁ h₂ hsame ht0 ht1)
    x y
  refine h.trans (le_of_eq ?_)
  unfold xiKappaConstant xiKappaRate
  ring

/-- Sitewise `Ξ` bound on `ERSpectralDomain p κ ηExp C₀`, same half-plane:
`‖Ξ(z₁,z₂)_xy‖ ≤ (xiKappaConstant κ b + 1) e^{-xiKappaRate κ b · d(x.1,y.1)} / W`. -/
theorem norm_erXi_le_xi_kappa (p : Params) {κ ηExp C₀ : ℝ} (hκ : 0 < κ)
    {z₁ z₂ : ℂ} (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂) (hsame : ERSameHalfPlane z₁ z₂)
    (x y : Site p.n p.W) :
    ‖erXi p z₁ z₂ x y‖ ≤
      (xiKappaConstant κ p.b + 1) *
        Real.exp (-(xiKappaRate κ p.b) * cyclicBlockDistance p x.1 y.1) / (p.W : ℝ) := by
  have hz₁ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₁
  have hz₂ := ERDeterministicMDECore.spectralDomain_im_ne_zero h₂
  have hgreen := norm_fourierGreenKernel_le_xi_kappa p hκ h₁ h₂ hsame x.1 y.1
  rw [erXi_apply_eq_siteGreenKernel_sub_identity p hz₁ hz₂ x y,
    norm_siteGreenKernel_sub_identity]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hC := (xiKappaConstant_pos hκ p.b_pos p.b_lt_half).le
  by_cases hb : x.1 = y.1
  · have hd0 : cyclicBlockDistance p x.1 y.1 = 0 := by
      rw [hb]; simp [cyclicBlockDistance, orientedBlockDistance]
    rw [hd0] at hgreen ⊢
    simp only [hb, ite_true, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at hgreen ⊢
    calc ‖fourierGreenKernel p (erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂)
          y.1 y.1 - 1‖ ≤
        ‖fourierGreenKernel p (erSemicircleStieltjes z₁ * erSemicircleStieltjes z₂)
          y.1 y.1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ xiKappaConstant κ p.b + 1 := by rw [norm_one]; linarith
  · simp only [hb, ite_false, sub_zero]
    refine hgreen.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The explicit `κ`-dependent clause-(i) coefficient for `Ξ`. -/
def xiKappaControlConstant (κ b : ℝ) : ℝ :=
  (xiKappaConstant κ b + 1) * Real.exp (xiKappaRate κ b)

theorem xiKappaControlConstant_pos {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b)
    (hb : b < 1 / 2) : 0 < xiKappaControlConstant κ b :=
  mul_pos (by linarith [xiKappaConstant_pos hκ hb0 hb]) (Real.exp_pos _)

/-- **`Ξ` half of ER clause (i), ER (2.18), for an arbitrary norm cutoff `C₀`.**
On `ERSpectralDomain p κ ηExp C₀` with same half-plane,
`‖Ξ(z₁,z₂)_xy‖ ≤ xiKappaControlConstant κ b · Υ_1(x,y)` where
`Υ = erManuscriptCyclicControl p (xiKappaRate κ b) 8` (height `1`, decay
`xiKappaRate κ b`, polynomial floor exponent `8`).  Constants depend only on
`κ, b`. -/
theorem norm_erXi_le_xi_kappa_control (p : Params) {κ ηExp C₀ : ℝ} (hκ : 0 < κ)
    {z₁ z₂ : ℂ} (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂) (hsame : ERSameHalfPlane z₁ z₂)
    (x y : Site p.n p.W) :
    ‖erXi p z₁ z₂ x y‖ ≤
      xiKappaControlConstant κ p.b *
        erManuscriptCyclicControl p (xiKappaRate κ p.b) 8 1 x y := by
  set a := xiKappaRate κ p.b
  have ha0 : 0 < a := xiKappaRate_pos hκ p.b_pos p.b_lt_half
  have hsite := norm_erXi_le_xi_kappa p hκ h₁ h₂ hsame x y
  have hdist :
      (erSiteDistance p x y : ℝ) ≤
        (p.W : ℝ) * cyclicBlockDistance p x.1 y.1 + p.W := by
    exact_mod_cast siteDistance_le_width_mul_cyclicBlockDistance_add_width p x y
  have hW := p.real_W_pos
  have hexp :
      Real.exp (-a * cyclicBlockDistance p x.1 y.1) ≤
        Real.exp a * Real.exp (-a * (erSiteDistance p x y : ℝ) / p.W) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled : a * (erSiteDistance p x y : ℝ) / p.W ≤
        a * cyclicBlockDistance p x.1 y.1 + a := by
      apply (div_le_iff₀ hW).2
      nlinarith [mul_le_mul_of_nonneg_left hdist ha0.le]
    have : -a * (erSiteDistance p x y : ℝ) / p.W =
        -(a * (erSiteDistance p x y : ℝ) / p.W) := by ring
    rw [this]
    linarith
  have hcontrol := exp_branch_le_erManuscriptCyclicControl_one p a x y
  have hC : 0 ≤ xiKappaConstant κ p.b + 1 := by
    linarith [xiKappaConstant_pos hκ p.b_pos p.b_lt_half]
  calc ‖erXi p z₁ z₂ x y‖ ≤
        (xiKappaConstant κ p.b + 1) *
          Real.exp (-a * cyclicBlockDistance p x.1 y.1) / (p.W : ℝ) := hsite
    _ ≤ (xiKappaConstant κ p.b + 1) *
          (Real.exp a * Real.exp (-a * (erSiteDistance p x y : ℝ) / p.W)) /
            (p.W : ℝ) := by gcongr
    _ = xiKappaControlConstant κ p.b *
          ((1 / (p.W : ℝ)) * Real.exp (-a * (erSiteDistance p x y : ℝ) / p.W)) := by
      unfold xiKappaControlConstant
      ring
    _ ≤ xiKappaControlConstant κ p.b *
          erManuscriptCyclicControl p a 8 1 x y :=
      mul_le_mul_of_nonneg_left hcontrol
        (xiKappaControlConstant_pos hκ p.b_pos p.b_lt_half).le

/-!
### Packaging into ER clause (i) for an arbitrary cutoff `C₀`
-/

/-- Sitewise corrected-`Θ` bound in the cyclic-control normalization `erManuscriptCyclicControl` at
every height `η = min |Im z₁| |Im z₂| ≤ 1`, for every decay `a ≤ 1/2` and with no
norm cutoff on `z₁, z₂` (the argument of
`ERClause1.norm_erTheta_le_fixedBond_control` with the cutoff `‖z‖ ≤ 1` replaced by
the height bound it was used for). -/
theorem norm_erTheta_le_control_of_height_le_one
    (p : Params) {a : ℝ} (ha : a ≤ 1 / 2) {z₁ z₂ : ℂ}
    (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (hη1 : min |z₁.im| |z₂.im| ≤ 1)
    (x y : Site p.n p.W) :
    ‖erTheta p z₁ z₂ x y‖ ≤
      (32 * Real.exp (1 / 2) /
        Real.sqrt (jumpBondMargin p)) *
      erManuscriptCyclicControl p a 8
        (min |z₁.im| |z₂.im|) x y := by
  let η : ℝ := min |z₁.im| |z₂.im|
  let α : ℂ := erSemicircleStieltjes z₁ *
    starRingEnd ℂ (erSemicircleStieltjes z₂)
  have hη0 : 0 < η := by
    dsimp only [η]
    exact lt_min (abs_pos.mpr hz₁) (abs_pos.mpr hz₂)
  have hη1 : η ≤ 1 := hη1
  have hm₁0 : erSemicircleStieltjes z₁ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₁
    simp [hm] at h
  have hm₂0 : erSemicircleStieltjes z₂ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₂
    simp [hm] at h
  have hα0 : α ≠ 0 :=
    mul_ne_zero hm₁0 ((map_ne_zero (starRingEnd ℂ)).2 hm₂0)
  have hα : ‖α‖ < 1 := by
    dsimp only [α]
    exact norm_thetaMultiplier_lt_one
      (norm_erSemicircleStieltjes_lt_one hz₁)
      (norm_erSemicircleStieltjes_lt_one hz₂)
  have hmargin : η / 4 ≤ 1 - ‖α‖ := by
    have h := thetaMultiplier_height_margin hz₁ hz₂
    dsimp only [η, α]
    rw [min_eq_right (by nlinarith)] at h
    exact h
  have hgreen :=
    norm_fourierGreenKernel_le_theta_height p hα0 hα hη0 hη1
      hmargin x.1 y.1
  have hbridge :=
    erTheta_apply_eq_siteGreenKernel_sub_identity p hz₁ hz₂ x y
  have hsite := norm_siteGreenKernel_sub_identity p α x y
  have hmpos :
      0 < min 1 ((p.n : ℝ) * Real.sqrt η) := by
    exact lt_min (by norm_num)
      (mul_pos (by exact_mod_cast p.n_pos) (Real.sqrt_pos.2 hη0))
  have hspos : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hgpos : 0 < Real.sqrt (jumpBondMargin p) :=
    Real.sqrt_pos.2 (jumpBondMargin_pos p)
  let den : ℝ :=
    min 1 ((p.n : ℝ) * Real.sqrt η) *
      Real.sqrt η * Real.sqrt (jumpBondMargin p)
  have hdenpos : 0 < den := by
    dsimp only [den]
    positivity
  have hdelta :
      ‖fourierGreenKernel p α x.1 y.1 -
          (if x.1 = y.1 then 1 else 0)‖ ≤
        32 * Real.exp (-(Real.sqrt η / 2) *
          cyclicBlockDistance p x.1 y.1) / den := by
    by_cases hb : x.1 = y.1
    · have hd0 : cyclicBlockDistance p x.1 y.1 = 0 := by
        rw [hb]
        simp [cyclicBlockDistance, orientedBlockDistance]
      have hdenle : den ≤ 1 := by
        have hmle : min 1 ((p.n : ℝ) * Real.sqrt η) ≤ 1 :=
          min_le_left _ _
        have hsle : Real.sqrt η ≤ 1 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hη1
        have hgle : Real.sqrt (jumpBondMargin p) ≤ 1 := by
          rw [← Real.sqrt_one]
          apply Real.sqrt_le_sqrt
          unfold jumpBondMargin
          exact sub_le_self _ (abs_nonneg _)
        dsimp only [den]
        nlinarith [hmpos.le, hspos.le, hgpos.le,
          mul_nonneg hmpos.le hspos.le,
          mul_le_mul hmle hsle hspos.le (by norm_num : (0 : ℝ) ≤ 1)]
      have hone : 1 ≤ 16 / den := by
        apply (le_div_iff₀ hdenpos).2
        nlinarith
      have hgreen' :
          ‖fourierGreenKernel p α x.1 y.1‖ ≤ 16 / den := by
        change ‖fourierGreenKernel p α x.1 y.1‖ ≤
          16 * Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p x.1 y.1) / den at hgreen
        rw [hd0] at hgreen
        norm_num at hgreen
        exact hgreen
      have hite :
          (if x.1 = y.1 then (1 : ℂ) else 0) = 1 := by
        simp [hb]
      rw [hite, hd0]
      norm_num
      calc
        ‖fourierGreenKernel p α x.1 y.1 - 1‖ ≤
            ‖fourierGreenKernel p α x.1 y.1‖ + 1 := by
          simpa using norm_sub_le
            (fourierGreenKernel p α x.1 y.1) (1 : ℂ)
        _ ≤ 16 / den + 1 := by
          simpa [add_comm] using add_le_add_right hgreen' 1
        _ ≤ 32 / den := by
          calc
            16 / den + 1 ≤ 16 / den + 16 / den :=
              (by simpa [add_comm] using
                add_le_add_left hone (16 / den))
            _ = 32 / den := by ring
    · simp only [hb, ite_false, sub_zero]
      exact hgreen.trans (by
        apply div_le_div_of_nonneg_right _ hdenpos.le
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Real.exp_pos _).le)
  have hnorm :
      (p.W : ℝ) *
          (min 1 ((p.n : ℝ) * Real.sqrt η) * Real.sqrt η) =
        erLocalizationLength p η * η :=
    width_mul_wrap_sqrt_eq_localization_mul p hη0
  have hellηpos : 0 < erLocalizationLength p η * η := by
    rw [← hnorm]
    exact mul_pos p.real_W_pos (mul_pos hmpos hspos)
  have hdennorm :
      den * (p.W : ℝ) =
        (erLocalizationLength p η * η) *
          Real.sqrt (jumpBondMargin p) := by
    dsimp only [den]
    calc
      (min 1 ((p.n : ℝ) * Real.sqrt η) *
          Real.sqrt η * Real.sqrt (jumpBondMargin p)) * (p.W : ℝ) =
        ((p.W : ℝ) *
          (min 1 ((p.n : ℝ) * Real.sqrt η) * Real.sqrt η)) *
            Real.sqrt (jumpBondMargin p) := by ring
      _ = (erLocalizationLength p η * η) *
            Real.sqrt (jumpBondMargin p) := by rw [hnorm]
  have hexp := theta_block_exp_le_site_exp p
    (a := a) hη0 hη1
    ha x y
  have hcontrol := exp_branch_le_erManuscriptCyclicControl p hη0
    a x y
  rw [hbridge, hsite]
  change ‖fourierGreenKernel p α x.1 y.1 -
      (if x.1 = y.1 then 1 else 0)‖ / (p.W : ℝ) ≤ _
  calc
    ‖fourierGreenKernel p α x.1 y.1 -
        (if x.1 = y.1 then 1 else 0)‖ / (p.W : ℝ) ≤
      (32 * Real.exp (-(Real.sqrt η / 2) *
        cyclicBlockDistance p x.1 y.1) / den) / (p.W : ℝ) := by
          gcongr
    _ = (32 / Real.sqrt (jumpBondMargin p)) *
        ((1 / (erLocalizationLength p η * η)) *
          Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p x.1 y.1)) := by
      rw [div_div, hdennorm]
      field_simp [ne_of_gt hellηpos, ne_of_gt hgpos]
    _ ≤ (32 / Real.sqrt (jumpBondMargin p)) *
        ((1 / (erLocalizationLength p η * η)) *
          (Real.exp (1 / 2) *
            Real.exp (-a *
              (erSiteDistance p x y : ℝ) /
                erLocalizationLength p η))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp
          (one_div_nonneg.mpr hellηpos.le))
        (by positivity)
    _ = (32 * Real.exp (1 / 2) /
          Real.sqrt (jumpBondMargin p)) *
        ((1 / (erLocalizationLength p η * η)) *
          Real.exp (-a *
            (erSiteDistance p x y : ℝ) /
              erLocalizationLength p η)) := by ring
    _ ≤ (32 * Real.exp (1 / 2) /
          Real.sqrt (jumpBondMargin p)) *
        erManuscriptCyclicControl p a 8 η x y :=
      mul_le_mul_of_nonneg_left hcontrol (by positivity)

/-- The cyclic control `erManuscriptCyclicControl` is antitone in its decay parameter. -/
theorem erManuscriptCyclicControl_anti_decay (p : Params) {a a' : ℝ} (h : a' ≤ a)
    (D : ℝ) {η : ℝ} (hη : 0 < η) (x y : Site p.n p.W) :
    erManuscriptCyclicControl p a D η x y ≤ erManuscriptCyclicControl p a' D η x y := by
  have hell : 0 < erLocalizationLength p η := by
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη)) p.real_L_pos
  unfold erManuscriptCyclicControl
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ (erSiteDistance p x y : ℝ) / erLocalizationLength p η := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  nlinarith

end ERGeneralVectorMDEXiKappa
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
