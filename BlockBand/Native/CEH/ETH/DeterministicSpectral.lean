module

public import BlockBand.Native.CEH.ETH.DeterministicWard

/-!
# CEH ETH: spectral-sum bounds for CEH Lemma 5.6 (diagonal model)

**Diagonal model.** `f : Fin N → ℝ` is the spectrum of the deformation `F`, `ζ₁, ζ₂` are the
effective spectral parameters (`ζᵢ = zᵢ + s mᵢ` in the application), `Θᵢ = Im ζᵢ > 0`, and
`Dᵢ = diag dᵢ`, `dᵢ(k) = (f k - ζᵢ)⁻¹` (`resEntry`). Every MDE solution is of this form in an
eigenbasis of `F` (`eq_spectralLift_entry_of_isSolution`). Notation: `tᵢ = Im⟨Dᵢ⟩`,
`aᵢ = ⟨DᵢDᵢᴴ⟩ = tᵢ/Θᵢ` (Ward), `P = Re⟨Im D₁ A Im D₂ Aᴴ⟩`; `A` is `(z₁,z₂)`-regular:
`⟨D₁ A D₂ᴴ⟩ = 0` (CEH Def. 4.1 with `θ = 1`). No further hypothesis on `A`.

## Main results

Core bounds (the numerators of `⟨M^A⟩` in the four constellations):
* `(+,+)`: `|⟨D₁AD₂⟩| ≤ 2 √P √(t₂/Θ₁)` (`norm_NTrace_pp_le`);
* `(-,-)`: `|⟨D₁ᴴAD₂ᴴ⟩| ≤ 2 √P √(t₁/Θ₂)` (`norm_NTrace_mm_le`);
* `(-,+)`: `|⟨D₁ᴴAD₂⟩| ≤ 2 |ζ₁ - ζ₂| √P √(a₁/(Θ₁Θ₂))` (`norm_NTrace_mp_le`);
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## Entries
-/

/-- The diagonal resolvent entry `(f k - ζ)⁻¹`. -/
def resEntry (f : Fin N → ℝ) (ζ : ℂ) (k : Fin N) : ℂ := ((f k : ℂ) - ζ)⁻¹

theorem entry_eq_resEntry (f : Fin N → ℝ) (s : ℝ) (z m : ℂ) :
    CEHNative.BlockBand.CEH.entry f s z m = resEntry f (z + (s : ℂ) * m) := by
  funext k
  simp only [CEHNative.BlockBand.CEH.entry, resEntry, sub_sub]

theorem sub_ne_zero_of_im_pos (f : Fin N → ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) (k : Fin N) :
    (f k : ℂ) - ζ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- Entry Ward identity: `Im d = Θ |d|²`. No hypothesis. -/
theorem resEntry_im (f : Fin N → ℝ) (ζ : ℂ) (k : Fin N) :
    (resEntry f ζ k).im = ζ.im * ‖resEntry f ζ k‖ ^ 2 := by
  rw [resEntry, Complex.inv_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_inv]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  rw [div_eq_mul_inv]

theorem resEntry_im_nonneg (f : Fin N → ℝ) {ζ : ℂ} (hζ : 0 ≤ ζ.im) (k : Fin N) :
    0 ≤ (resEntry f ζ k).im := by
  rw [resEntry_im]; positivity

/-- Entry resolvent identity: `d₁ - d₂ = (ζ₁ - ζ₂) d₁ d₂`. -/
theorem resEntry_sub (f : Fin N → ℝ) {ζ₁ ζ₂ : ℂ} (k : Fin N) (h₁ : (f k : ℂ) - ζ₁ ≠ 0)
    (h₂ : (f k : ℂ) - ζ₂ ≠ 0) :
    resEntry f ζ₁ k - resEntry f ζ₂ k = (ζ₁ - ζ₂) * resEntry f ζ₁ k * resEntry f ζ₂ k := by
  simp only [resEntry]
  field_simp
  ring

theorem star_resEntry (f : Fin N → ℝ) (ζ : ℂ) (k : Fin N) :
    star (resEntry f ζ k) = resEntry f (conj ζ) k := by
  simp [resEntry, Complex.conj_ofReal]

/-!
## Traces of diagonal words
-/

theorem NTrace_diag_mul_mul_diag (a b : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (diagonal a * A * diagonal b) = (N : ℂ)⁻¹ * ∑ k, a k * A k k * b k := by
  simp only [NTrace, Conventions.normalizedTrace, Matrix.trace, Matrix.diag,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem NTrace_diagonal' (a : Fin N → ℂ) :
    NTrace (diagonal a) = (N : ℂ)⁻¹ * ∑ k, a k := by
  simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_diagonal]

theorem im_NTrace_diagonal (a : Fin N → ℂ) :
    (NTrace (diagonal a)).im = (N : ℝ)⁻¹ * ∑ k, (a k).im := by
  rw [NTrace_diagonal', ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul,
    Complex.im_sum]

theorem wardMass_diagonal (a : Fin N → ℂ) :
    wardMass (diagonal a) = (N : ℝ)⁻¹ * ∑ k, ‖a k‖ ^ 2 := by
  rw [wardMass, diagonal_conjTranspose, diagonal_mul_diagonal, NTrace_diagonal',
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.star_apply]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- Diagonal Ward: `a = t/Θ`, i.e. `Θ a(D) = Im⟨D⟩`. -/
theorem im_mul_wardMass_resEntry (f : Fin N → ℝ) (ζ : ℂ) :
    ζ.im * wardMass (diagonal (resEntry f ζ)) = (NTrace (diagonal (resEntry f ζ))).im := by
  rw [wardMass_diagonal, im_NTrace_diagonal, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resEntry_im]; ring

/-- The positive chain `P = Re⟨Im D₁ A Im D₂ Aᴴ⟩` dominates its diagonal part. -/
theorem diag_sum_le_positiveChain (d₁ d₂ : Fin N → ℂ) (h₁ : ∀ k, 0 ≤ (d₁ k).im)
    (h₂ : ∀ k, 0 ≤ (d₂ k).im) (A : Matrix (Fin N) (Fin N) ℂ) :
    (N : ℝ)⁻¹ * ∑ k, (d₁ k).im * (d₂ k).im * ‖A k k‖ ^ 2 ≤
      (NTrace (matrixImaginaryPart (diagonal d₁) * A * matrixImaginaryPart (diagonal d₂) *
        Aᴴ)).re := by
  rw [matrixImaginaryPart_diagonal, matrixImaginaryPart_diagonal,
    NTrace_diagonal_mul_mul_diagonal_mul_adj, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun i _ => ?_
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ (d₁ i).im * (d₂ j).im * ‖A i j‖ ^ 2 :=
    fun j _ => mul_nonneg (mul_nonneg (h₁ i) (h₂ j)) (sq_nonneg _)
  exact Finset.single_le_sum hnn (Finset.mem_univ i)

/-- Weighted Cauchy–Schwarz: if `‖xₖ‖² ≤ wₖ vₖ` with `w, v ≥ 0`, then
`|N⁻¹ Σ xₖ aₖ| ≤ √(N⁻¹ Σ wₖ |aₖ|²) √(N⁻¹ Σ vₖ)`. -/
theorem norm_avg_mul_le (x a : Fin N → ℂ) (w v : Fin N → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hv : ∀ k, 0 ≤ v k) (hx : ∀ k, ‖x k‖ ^ 2 ≤ w k * v k) :
    ‖(N : ℂ)⁻¹ * ∑ k, x k * a k‖ ≤
      Real.sqrt ((N : ℝ)⁻¹ * ∑ k, w k * ‖a k‖ ^ 2) * Real.sqrt ((N : ℝ)⁻¹ * ∑ k, v k) := by
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hpt : ∀ k, ‖x k * a k‖ ≤ (Real.sqrt (w k) * ‖a k‖) * Real.sqrt (v k) := by
    intro k
    rw [norm_mul]
    have : ‖x k‖ ≤ Real.sqrt (w k) * Real.sqrt (v k) := by
      rw [← Real.sqrt_mul (hw k)]
      exact Real.le_sqrt_of_sq_le (hx k)
    calc ‖x k‖ * ‖a k‖ ≤ Real.sqrt (w k) * Real.sqrt (v k) * ‖a k‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring
  have hcs : ‖∑ k, x k * a k‖ ≤
      Real.sqrt (∑ k, w k * ‖a k‖ ^ 2) * Real.sqrt (∑ k, v k) := by
    calc ‖∑ k, x k * a k‖ ≤ ∑ k, ‖x k * a k‖ := norm_sum_le _ _
      _ ≤ ∑ k, (Real.sqrt (w k) * ‖a k‖) * Real.sqrt (v k) :=
          Finset.sum_le_sum fun k _ => hpt k
      _ ≤ Real.sqrt (∑ k, (Real.sqrt (w k) * ‖a k‖) ^ 2) *
            Real.sqrt (∑ k, Real.sqrt (v k) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by
          congr 2
          · refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_pow, Real.sq_sqrt (hw k)]
          · exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hv k)
  rw [norm_mul, norm_inv, Complex.norm_natCast, Real.sqrt_mul hN, Real.sqrt_mul hN]
  have hsq : (N : ℝ)⁻¹ = Real.sqrt (N : ℝ)⁻¹ * Real.sqrt (N : ℝ)⁻¹ :=
    (Real.mul_self_sqrt hN).symm
  calc (N : ℝ)⁻¹ * ‖∑ k, x k * a k‖ ≤
      (N : ℝ)⁻¹ * (Real.sqrt (∑ k, w k * ‖a k‖ ^ 2) * Real.sqrt (∑ k, v k)) :=
        mul_le_mul_of_nonneg_left hcs hN
    _ = _ := by nth_rewrite 1 [hsq]; ring

/-!
## The numerator bounds
-/

section Numerators

variable (f : Fin N → ℝ) {ζ₁ ζ₂ : ℂ} (hΘ₁ : 0 < ζ₁.im) (hΘ₂ : 0 < ζ₂.im)
  (A : Matrix (Fin N) (Fin N) ℂ)
  (hreg : NTrace (diagonal (resEntry f ζ₁) * A * (diagonal (resEntry f ζ₂))ᴴ) = 0)
include hΘ₁ hΘ₂ hreg

/-- The positive chain of the diagonal model. -/
abbrev chainP (f : Fin N → ℝ) (ζ₁ ζ₂ : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (NTrace (matrixImaginaryPart (diagonal (resEntry f ζ₁)) * A *
    matrixImaginaryPart (diagonal (resEntry f ζ₂)) * Aᴴ)).re

omit hreg in
theorem diag_weight_le_chainP :
    (N : ℝ)⁻¹ * ∑ k, ((resEntry f ζ₁ k).im * (resEntry f ζ₂ k).im) * ‖A k k‖ ^ 2 ≤
      chainP f ζ₁ ζ₂ A :=
  diag_sum_le_positiveChain _ _ (resEntry_im_nonneg f hΘ₁.le) (resEntry_im_nonneg f hΘ₂.le) A

/-- **Numerator `(+,+)`**: `|⟨D₁AD₂⟩| ≤ 2 √P √(t₂/Θ₁)`. -/
theorem norm_NTrace_pp_le :
    ‖NTrace (diagonal (resEntry f ζ₁) * A * diagonal (resEntry f ζ₂))‖ ≤
      2 * Real.sqrt (chainP f ζ₁ ζ₂ A) *
        Real.sqrt ((NTrace (diagonal (resEntry f ζ₂))).im / ζ₁.im) := by
  set d₁ := resEntry f ζ₁
  set d₂ := resEntry f ζ₂
  have hrep : NTrace (diagonal d₁ * A * diagonal d₂) =
      (N : ℂ)⁻¹ * ∑ k, (d₁ k * (d₂ k - star (d₂ k))) * A k k := by
    have h0 := hreg
    rw [diagonal_conjTranspose, NTrace_diag_mul_mul_diag] at h0
    rw [NTrace_diag_mul_mul_diag, ← sub_zero ((N : ℂ)⁻¹ * _), ← h0, ← mul_sub,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.star_apply]
    ring
  rw [hrep]
  set w : Fin N → ℝ := fun k => (d₁ k).im * (d₂ k).im
  set v : Fin N → ℝ := fun k => 4 * (d₂ k).im / ζ₁.im
  have hw : ∀ k, 0 ≤ w k := fun k =>
    mul_nonneg (resEntry_im_nonneg f hΘ₁.le k) (resEntry_im_nonneg f hΘ₂.le k)
  have hv : ∀ k, 0 ≤ v k := fun k => by
    have := resEntry_im_nonneg f hΘ₂.le k
    positivity
  have hx : ∀ k, ‖d₁ k * (d₂ k - star (d₂ k))‖ ^ 2 ≤ w k * v k := by
    intro k
    have hsub : d₂ k - star (d₂ k) = ((2 * (d₂ k).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp; ring
    have hW := resEntry_im f ζ₁ k
    rw [norm_mul, hsub, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      mul_pow, sq_abs]
    apply le_of_eq
    simp only [w, v]
    rw [hW]
    field_simp
    ring
  refine (norm_avg_mul_le _ _ w v hw hv hx).trans ?_
  have hP := diag_weight_le_chainP f hΘ₁ hΘ₂ A
  have hV : (N : ℝ)⁻¹ * ∑ k, v k =
      4 * ((NTrace (diagonal (resEntry f ζ₂))).im / ζ₁.im) := by
    rw [im_NTrace_diagonal]
    simp only [v, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [hV, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have := Real.sqrt_le_sqrt hP
  have h0 := Real.sqrt_nonneg ((NTrace (diagonal (resEntry f ζ₂))).im / ζ₁.im)
  nlinarith

/-- **Numerator `(-,-)`**: `|⟨D₁ᴴAD₂ᴴ⟩| ≤ 2 √P √(t₁/Θ₂)`. -/
theorem norm_NTrace_mm_le :
    ‖NTrace ((diagonal (resEntry f ζ₁))ᴴ * A * (diagonal (resEntry f ζ₂))ᴴ)‖ ≤
      2 * Real.sqrt (chainP f ζ₁ ζ₂ A) *
        Real.sqrt ((NTrace (diagonal (resEntry f ζ₁))).im / ζ₂.im) := by
  set d₁ := resEntry f ζ₁
  set d₂ := resEntry f ζ₂
  have hrep : NTrace ((diagonal d₁)ᴴ * A * (diagonal d₂)ᴴ) =
      (N : ℂ)⁻¹ * ∑ k, ((star (d₁ k) - d₁ k) * star (d₂ k)) * A k k := by
    have h0 := hreg
    rw [diagonal_conjTranspose, NTrace_diag_mul_mul_diag] at h0
    rw [diagonal_conjTranspose, diagonal_conjTranspose, NTrace_diag_mul_mul_diag,
      ← sub_zero ((N : ℂ)⁻¹ * _), ← h0, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.star_apply]
    ring
  rw [hrep]
  set w : Fin N → ℝ := fun k => (d₁ k).im * (d₂ k).im
  set v : Fin N → ℝ := fun k => 4 * (d₁ k).im / ζ₂.im
  have hw : ∀ k, 0 ≤ w k := fun k =>
    mul_nonneg (resEntry_im_nonneg f hΘ₁.le k) (resEntry_im_nonneg f hΘ₂.le k)
  have hv : ∀ k, 0 ≤ v k := fun k => by
    have := resEntry_im_nonneg f hΘ₁.le k
    positivity
  have hx : ∀ k, ‖(star (d₁ k) - d₁ k) * star (d₂ k)‖ ^ 2 ≤ w k * v k := by
    intro k
    have hsub : star (d₁ k) - d₁ k = ((-2 * (d₁ k).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp; ring
    have hW := resEntry_im f ζ₂ k
    rw [norm_mul, hsub, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      norm_star, mul_pow, sq_abs]
    apply le_of_eq
    simp only [w, v]
    change (-2 * (d₁ k).im) ^ 2 * ‖d₂ k‖ ^ 2 = (d₁ k).im * (d₂ k).im * (4 * (d₁ k).im / ζ₂.im)
    rw [hW]
    field_simp
    ring
  refine (norm_avg_mul_le _ _ w v hw hv hx).trans ?_
  have hP := diag_weight_le_chainP f hΘ₁ hΘ₂ A
  have hV : (N : ℝ)⁻¹ * ∑ k, v k =
      4 * ((NTrace (diagonal (resEntry f ζ₁))).im / ζ₂.im) := by
    rw [im_NTrace_diagonal]
    simp only [v, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [hV, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have := Real.sqrt_le_sqrt hP
  have h0 := Real.sqrt_nonneg ((NTrace (diagonal (resEntry f ζ₁))).im / ζ₂.im)
  nlinarith

/-- **Numerator `(-,+)`**: `|⟨D₁ᴴAD₂⟩| ≤ 2 |ζ₁ - ζ₂| √P √(a₁/(Θ₁Θ₂))`, `a₁ = ⟨D₁D₁ᴴ⟩`. -/
theorem norm_NTrace_mp_le :
    ‖NTrace ((diagonal (resEntry f ζ₁))ᴴ * A * diagonal (resEntry f ζ₂))‖ ≤
      2 * ‖ζ₁ - ζ₂‖ * Real.sqrt (chainP f ζ₁ ζ₂ A) *
        Real.sqrt (wardMass (diagonal (resEntry f ζ₁)) / (ζ₁.im * ζ₂.im)) := by
  set d₁ := resEntry f ζ₁
  set d₂ := resEntry f ζ₂
  have hrep : NTrace ((diagonal d₁)ᴴ * A * diagonal d₂) =
      (N : ℂ)⁻¹ * ∑ k, (star (d₁ k) * d₂ k - d₁ k * star (d₂ k)) * A k k := by
    have h0 := hreg
    rw [diagonal_conjTranspose, NTrace_diag_mul_mul_diag] at h0
    rw [diagonal_conjTranspose, NTrace_diag_mul_mul_diag,
      ← sub_zero ((N : ℂ)⁻¹ * _), ← h0, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.star_apply]
    ring
  rw [hrep]
  set w : Fin N → ℝ := fun k => (d₁ k).im * (d₂ k).im
  set v : Fin N → ℝ := fun k => 4 * ‖ζ₁ - ζ₂‖ ^ 2 * ‖d₁ k‖ ^ 2 / (ζ₁.im * ζ₂.im)
  have hw : ∀ k, 0 ≤ w k := fun k =>
    mul_nonneg (resEntry_im_nonneg f hΘ₁.le k) (resEntry_im_nonneg f hΘ₂.le k)
  have hv : ∀ k, 0 ≤ v k := fun k => by positivity
  have hx : ∀ k, ‖star (d₁ k) * d₂ k - d₁ k * star (d₂ k)‖ ^ 2 ≤ w k * v k := by
    intro k
    have hne₁ := sub_ne_zero_of_im_pos f hΘ₁ k
    have hne₂ := sub_ne_zero_of_im_pos f hΘ₂ k
    -- `d₂ = d₁ + (ζ₂ - ζ₁) d₁ d₂`
    have hres : d₂ k = d₁ k + (ζ₂ - ζ₁) * d₁ k * d₂ k := by
      have := resEntry_sub f k hne₂ hne₁
      simp only [d₁, d₂] at this ⊢
      linear_combination this
    set u := (ζ₂ - ζ₁) * d₂ k with hu
    have hid : star (d₁ k) * d₂ k - d₁ k * star (d₂ k) =
        ((‖d₁ k‖ ^ 2 : ℝ) : ℂ) * (u - star u) := by
      have hn : ((‖d₁ k‖ ^ 2 : ℝ) : ℂ) = star (d₁ k) * d₁ k := by
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hn]
      have h2 : star (d₂ k) = star (d₁ k) + star (ζ₂ - ζ₁) * star (d₁ k) * star (d₂ k) := by
        conv_lhs => rw [hres]
        simp only [star_add, star_mul']
      rw [hu, star_mul']
      calc star (d₁ k) * d₂ k - d₁ k * star (d₂ k)
          = star (d₁ k) * (d₁ k + (ζ₂ - ζ₁) * d₁ k * d₂ k) -
              d₁ k * (star (d₁ k) + star (ζ₂ - ζ₁) * star (d₁ k) * star (d₂ k)) := by
            rw [← hres, ← h2]
        _ = _ := by ring
    have hu' : ‖u - star u‖ ≤ 2 * (‖ζ₁ - ζ₂‖ * ‖d₂ k‖) := by
      calc ‖u - star u‖ ≤ ‖u‖ + ‖star u‖ := norm_sub_le _ _
        _ = 2 * ‖u‖ := by rw [norm_star]; ring
        _ = 2 * (‖ζ₁ - ζ₂‖ * ‖d₂ k‖) := by rw [hu, norm_mul, norm_sub_rev]
    have hW₁ := resEntry_im f ζ₁ k
    have hW₂ := resEntry_im f ζ₂ k
    rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hb : (‖d₁ k‖ ^ 2 * ‖u - star u‖) ^ 2 ≤
        (‖d₁ k‖ ^ 2 * (2 * (‖ζ₁ - ζ₂‖ * ‖d₂ k‖))) ^ 2 := by
      gcongr
    refine hb.trans (le_of_eq ?_)
    simp only [w, v]
    rw [hW₁, hW₂]
    field_simp
    ring
  refine (norm_avg_mul_le _ _ w v hw hv hx).trans ?_
  have hP := diag_weight_le_chainP f hΘ₁ hΘ₂ A
  have hV : (N : ℝ)⁻¹ * ∑ k, v k =
      (2 * ‖ζ₁ - ζ₂‖) ^ 2 * (wardMass (diagonal d₁) / (ζ₁.im * ζ₂.im)) := by
    rw [wardMass_diagonal]
    simp only [v, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  rw [hV, Real.sqrt_mul (sq_nonneg (2 * ‖ζ₁ - ζ₂‖)), Real.sqrt_sq (by positivity)]
  have := Real.sqrt_le_sqrt hP
  have h0 := Real.sqrt_nonneg (wardMass (diagonal d₁) / (ζ₁.im * ζ₂.im))
  have h1 := norm_nonneg (ζ₁ - ζ₂)
  nlinarith [mul_nonneg h1 h0]

end Numerators

end BlockBand.Native.CEH.ETH
