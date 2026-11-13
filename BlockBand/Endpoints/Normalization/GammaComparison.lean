module

public import BlockBand.Internal.Contracts.ClocksCommonPort

/-!
# Loewner comparison of the fresh covariance with the matched-scalar covariance

Replacing the stationary scalar by its matched value changes the fresh covariance with relative
Loewner error `O(η)`.

## Vocabulary

* `gammaMatched F c₀ E = gammaAt F c₀ E (conj (matchedA E))`, the covariance with the matched
  scalar `conj a(E) = (-E + i√(4-E²))/2`;
* `matchedIm E = √(4-E²)/2 = Im conj a(E)` (`im_conj_matchedA`), and the explicit constant
  `gammaConst E = 8 / matchedIm E`.

## Main results (all deterministic; no measure is involved)

Domain: every `N`, every Hermitian `F : Matrix (Fin N) (Fin N) ℂ`, every `c₀ > 0`, every
`E ∈ (-2, 2)`, every `m : ℂ` and `η` with `‖m - conj a(E)‖ ≤ η ≤ ρ/2`, `ρ = matchedIm E` (so `η ≥ 0`).
Norm: the complex modulus on the scalar; Loewner order (`PosSemidef` of the difference) on the
matrices, with real scalars cast to `ℂ`. Constant: `C = gammaConst E = 8/ρ`, uniform in `N`,
`F`, `c₀`, `m`, `η`.

* `gammaAt_loewner`: `(1 + Cη) Γ_ā - Γ_m ⪰ 0` and `Γ_m - (1 - Cη) Γ_ā ⪰ 0`.
* `freshGamma_loewner`: the same for `freshGamma F c₀ E` under
  `‖freshDyson F c₀ E - conj a(E)‖ ≤ η`.
* `pairS_eq_of_b`, `c_eq_of_b`: `pairS p = min b (1 - 2b)` and `p.c = 1 - 2b` when `p.b = b`.
* `pairRegular_freshGamma_loewner`, `blockRegular_freshGamma_loewner`: the comparison on the
  regular prior events `IsPairRegular` (variance `pairS p`) and `IsBlockRegular` (variance
  `p.c`) of `ClocksCommonPort`; Hermiticity of the deformation is read off `FreshClass`.

Also: `gammaAt_eq_diag` (the spectral form `U diag(c₀/|fᵢ - E - c₀m|²) Uᴴ` whenever no
`fᵢ - E - c₀m` vanishes; it is applied here when `c₀ > 0` and `Im m > 0`), and
`gammaAt_posSemidef`. Here `ρ = √(4-E²)/2 = Im conj(a)` is `π` times the semicircle density
(`matchedIm`), not the density itself.

Method: `F = U diag(f) Uᴴ` (Mathlib spectral theorem, as for `detLaplace`); both covariances are `U diag(·) Uᴴ`; with
`α = fᵢ - E - c₀ā`, `β = fᵢ - E - c₀m`: `|α| ≥ c₀ρ`, `||α| - |β|| ≤ c₀η ≤ |α|/2`, whence
`|α|²/|β|² ∈ [1 - 8c₀η/|α|, 1 + 8c₀η/|α|] ⊂ [1 - Cη, 1 + Cη]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ComplexConjugate ComplexOrder Matrix

variable {N : ℕ}

/-!
## Definitions
-/

/-- `Γ_m = c₀ ((F - (E + c₀ m))ᴴ (F - (E + c₀ m)))⁻¹`: the fresh covariance of `freshGamma`
with the scalar `m` left free. -/
def gammaAt (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (m : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (c₀ : ℂ) • ((F - ((E : ℂ) + (c₀ : ℂ) * m) • 1)ᴴ * (F - ((E : ℂ) + (c₀ : ℂ) * m) • 1))⁻¹

/-- The covariance with the matched scalar `conj a(E)`: `c₀ |F - E - c₀ conj a(E)|^{-2}`. -/
def gammaMatched (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  gammaAt F c₀ E (conj (matchedA E))

/-- `ρ(E) = √(4-E²)/2`, the imaginary part of `conj a(E)`. -/
def matchedIm (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / 2

/-- The explicit comparison constant `C(E) = 8/ρ(E)`. -/
def gammaConst (E : ℝ) : ℝ := 8 / matchedIm E

/-- `freshGamma` is `gammaAt` at the fresh Dyson root. -/
theorem freshGamma_eq_gammaAt (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) :
    freshGamma F c₀ E = gammaAt F c₀ E (freshDyson F c₀ E) := rfl

theorem im_conj_matchedA (E : ℝ) : (conj (matchedA E)).im = matchedIm E := by
  simp [matchedA, matchedIm, neg_div]

theorem matchedIm_pos {E : ℝ} (h1 : -2 < E) (h2 : E < 2) : 0 < matchedIm E := by
  unfold matchedIm
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem gammaConst_pos {E : ℝ} (h1 : -2 < E) (h2 : E < 2) : 0 < gammaConst E := by
  have := matchedIm_pos h1 h2
  unfold gammaConst; positivity

/-!
## Conjugated diagonals
-/

section Conj

variable (U : Matrix (Fin N) (Fin N) ℂ)

private lemma cd_mul (hU : star U * U = 1) (a b : Fin N → ℂ) :
    (U * diagonal a * star U) * (U * diagonal b * star U)
      = U * diagonal (fun i => a i * b i) * star U := by
  calc (U * diagonal a * star U) * (U * diagonal b * star U)
      = U * diagonal a * (star U * U) * diagonal b * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U (diagonal a) (diagonal b),
          diagonal_mul_diagonal]

private lemma cd_sub (a b : Fin N → ℂ) :
    U * diagonal a * star U - U * diagonal b * star U
      = U * diagonal (fun i => a i - b i) * star U := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]

private lemma cd_smul (r : ℂ) (a : Fin N → ℂ) :
    r • (U * diagonal a * star U) = U * diagonal (fun i => r * a i) * star U := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private lemma cd_conjTranspose (a : Fin N → ℂ) :
    (U * diagonal a * star U)ᴴ = U * diagonal (fun i => star (a i)) * star U := by
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose,
    conjTranspose_conjTranspose, ← Matrix.mul_assoc]
  rfl

private lemma cd_scalar (hU : U * star U = 1) (z : ℂ) :
    z • (1 : Matrix (Fin N) (Fin N) ℂ) = U * diagonal (fun _ => z) * star U := by
  have hd : diagonal (fun _ : Fin N => z) = z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

private lemma cd_inv (hU1 : star U * U = 1) (hU2 : U * star U = 1) (a : Fin N → ℂ)
    (h : ∀ i, a i ≠ 0) :
    (U * diagonal a * star U)⁻¹ = U * diagonal (fun i => (a i)⁻¹) * star U := by
  apply Matrix.inv_eq_left_inv
  rw [cd_mul U hU1]
  have : (fun i => (a i)⁻¹ * a i) = fun _ => (1 : ℂ) :=
    funext fun i => inv_mul_cancel₀ (h i)
  rw [this, diagonal_one, Matrix.mul_one, hU2]

private lemma cd_posSemidef (r : Fin N → ℝ) (h : ∀ i, 0 ≤ r i) :
    (U * diagonal (fun i => (r i : ℂ)) * star U).PosSemidef := by
  rw [star_eq_conjTranspose]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U
  rw [posSemidef_diagonal_iff]
  intro i
  exact Complex.zero_le_real.mpr (h i)

private lemma cd_posSemidef_of_eq (d : Fin N → ℂ) (r : Fin N → ℝ) (hd : ∀ i, d i = (r i : ℂ))
    (h : ∀ i, 0 ≤ r i) : (U * diagonal d * star U).PosSemidef := by
  have : d = fun i => (r i : ℂ) := funext hd
  rw [this]
  exact cd_posSemidef U r h

end Conj

/-!
## Spectral form of `Γ_m`
-/

section Spectral

variable {F : Matrix (Fin N) (Fin N) ℂ}

/-- The unitary of the spectral theorem for Hermitian `F`. -/
abbrev specU (hF : F.IsHermitian) : Matrix (Fin N) (Fin N) ℂ :=
  (hF.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

private lemma spectral_data (hF : F.IsHermitian) :
    F = specU hF * diagonal (fun i => (hF.eigenvalues i : ℂ)) * star (specU hF) := by
  conv_lhs => rw [hF.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

private lemma u1 (hF : F.IsHermitian) : star (specU hF) * specU hF = 1 :=
  Unitary.coe_star_mul_self _

private lemma u2 (hF : F.IsHermitian) : specU hF * star (specU hF) = 1 :=
  Unitary.coe_mul_star_self _

/-- The shifted fresh matrix in the eigenbasis of `F`. -/
private lemma shift_eq (hF : F.IsHermitian) (z : ℂ) :
    F - z • 1 = specU hF * diagonal (fun i => (hF.eigenvalues i : ℂ) - z) * star (specU hF) := by
  conv_lhs => rw [spectral_data hF]
  rw [cd_scalar _ (u2 hF) z, cd_sub]

/-- **Spectral form.** For Hermitian `F` and every scalar `m` with `fᵢ ≠ E + c₀ m` for all
eigenvalues `fᵢ`: `Γ_m = U diag(c₀/|fᵢ - E - c₀m|²) Uᴴ`. -/
theorem gammaAt_eq_diag (hF : F.IsHermitian) (c₀ E : ℝ) (m : ℂ)
    (h : ∀ i, (hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m) ≠ 0) :
    gammaAt F c₀ E m = specU hF * diagonal (fun i =>
      ((c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ ^ 2 : ℝ) : ℂ))
        * star (specU hF) := by
  unfold gammaAt
  rw [shift_eq hF, cd_conjTranspose, cd_mul _ (u1 hF)]
  have hsq : (fun i => star ((hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)) *
      ((hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m))) = fun i =>
      ((‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ ^ 2 : ℝ) : ℂ) := by
    funext i
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  rw [hsq, cd_inv _ (u1 hF) (u2 hF), cd_smul]
  · refine congrArg (fun d => specU hF * diagonal d * star (specU hF)) (funext fun i => ?_)
    push_cast
    rw [div_eq_mul_inv]
  · intro i
    have := h i
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr this)

/-- A spectral entry is bounded below by `c₀ Im m`: `|fᵢ - E - c₀ m| ≥ c₀ Im m`. -/
theorem le_norm_shift (f c₀ E : ℝ) (m : ℂ) :
    c₀ * m.im ≤ ‖(f : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ := by
  have h := Complex.abs_im_le_norm ((f : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m))
  have him : ((f : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)).im = -(c₀ * m.im) := by simp
  rw [him, abs_neg] at h
  exact (le_abs_self _).trans h

/-- `Γ_m` is positive semidefinite whenever `c₀ > 0` and `Im m > 0`. -/
theorem gammaAt_posSemidef (hF : F.IsHermitian) {c₀ : ℝ} (hc : 0 < c₀) (E : ℝ) {m : ℂ}
    (hm : 0 < m.im) : (gammaAt F c₀ E m).PosSemidef := by
  have hne : ∀ i, (hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m) ≠ 0 := fun i h0 => by
    have := le_norm_shift (hF.eigenvalues i) c₀ E m
    rw [h0, norm_zero] at this
    nlinarith [mul_pos hc hm]
  rw [gammaAt_eq_diag hF c₀ E m hne]
  exact cd_posSemidef _ _ fun i => by positivity

end Spectral

/-!
## The scalar comparison
-/

/-- Scalar core: if `A > 0`, `|A - B| ≤ d`, `2d ≤ A`, `8d ≤ tA`, `t ≥ 0`, `c₀ > 0`, then
`c₀/B² ≤ (1+t) c₀/A²` and `(1-t) c₀/A² ≤ c₀/B²`. -/
theorem scalar_ratio {A B d t c₀ : ℝ} (hA : 0 < A) (hAB : |A - B| ≤ d) (hd : 2 * d ≤ A)
    (ht : 8 * d ≤ t * A) (ht0 : 0 ≤ t) (hc : 0 < c₀) :
    c₀ / B ^ 2 ≤ (1 + t) * (c₀ / A ^ 2) ∧ (1 - t) * (c₀ / A ^ 2) ≤ c₀ / B ^ 2 := by
  have h1 := (abs_le.mp hAB).1
  have h2 := (abs_le.mp hAB).2
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hAB
  have hB : A - d ≤ B := by linarith
  have hB' : B ≤ A + d := by linarith
  have hAd : 0 < A - d := by linarith
  have hBpos : 0 < B := by linarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hB2 : 0 < B ^ 2 := by positivity
  constructor
  · -- `A² ≤ (1+t) B²`
    have key : A ^ 2 ≤ (1 + t) * B ^ 2 := by
      have hsq : (A - d) ^ 2 ≤ B ^ 2 := by nlinarith
      have hpoly : A * A ^ 2 ≤ (A + 8 * d) * (A - d) ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg hd0 (by linarith : 0 ≤ A - 2 * d))
          (by linarith : 0 ≤ 6 * A - 3 * d), mul_nonneg hd0 (mul_nonneg hd0 hd0)]
      have hpoly2 : A * A ^ 2 ≤ A * ((1 + t) * (A - d) ^ 2) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ t * A - 8 * d) (sq_nonneg (A - d))]
      have : A ^ 2 ≤ (1 + t) * (A - d) ^ 2 := le_of_mul_le_mul_left hpoly2 hA
      nlinarith
    rw [mul_div_assoc', div_le_div_iff₀ hB2 hA2]
    nlinarith
  · rcases le_or_gt (1 - t) 0 with h | h
    · have : (1 - t) * (c₀ / A ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (by positivity)
      exact this.trans (by positivity)
    · have key : (1 - t) * B ^ 2 ≤ A ^ 2 := by
        have hsq : B ^ 2 ≤ (A + d) ^ 2 := by nlinarith
        have hpoly : (A - 8 * d) * (A + d) ^ 2 ≤ A * A ^ 2 := by
          nlinarith [mul_nonneg hd0 (mul_nonneg hd0 hd0), mul_nonneg hd0 (mul_nonneg hd0 hA.le),
            mul_nonneg hd0 (mul_nonneg hA.le hA.le)]
        have hpoly2 : A * ((1 - t) * (A + d) ^ 2) ≤ A * A ^ 2 := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ t * A - 8 * d) (sq_nonneg (A + d))]
        have : (1 - t) * (A + d) ^ 2 ≤ A ^ 2 := le_of_mul_le_mul_left hpoly2 hA
        nlinarith
      rw [mul_div_assoc', div_le_div_iff₀ hA2 hB2]
      nlinarith

/-!
## The Loewner comparison
-/

/-- **Covariance comparison.** For Hermitian `F`, `c₀ > 0`, `-2 < E < 2`,
`m : ℂ` and `η ≥ 0` with `‖m - conj a(E)‖ ≤ η ≤ ρ/2`, `ρ = matchedIm E = √(4-E²)/2`, and the
explicit constant `C = gammaConst E = 8/ρ`:
`(1 + Cη) Γ_ā - Γ_m ⪰ 0` and `Γ_m - (1 - Cη) Γ_ā ⪰ 0` (the stationary
scalar approximation changes the covariance with relative Loewner error `O(η)`). -/
theorem gammaAt_loewner {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c₀ E : ℝ}
    (hc : 0 < c₀) (hE1 : -2 < E) (hE2 : E < 2) {m : ℂ} {η : ℝ}
    (hm : ‖m - conj (matchedA E)‖ ≤ η) (hηρ : η ≤ matchedIm E / 2) :
    ((((1 + gammaConst E * η : ℝ) : ℂ) • gammaMatched F c₀ E - gammaAt F c₀ E m).PosSemidef ∧
      (gammaAt F c₀ E m - (((1 - gammaConst E * η : ℝ) : ℂ)) • gammaMatched F c₀ E).PosSemidef) := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hm
  set a := conj (matchedA E) with ha
  set ρ := matchedIm E with hρdef
  have hρ : 0 < ρ := matchedIm_pos hE1 hE2
  have haim : a.im = ρ := im_conj_matchedA E
  -- `Im m ≥ ρ/2 > 0`
  have hmim : ρ / 2 ≤ m.im := by
    have h := Complex.abs_im_le_norm (m - a)
    rw [Complex.sub_im, haim] at h
    have := (abs_le.mp (h.trans hm)).1
    linarith
  have hmpos : 0 < m.im := by linarith
  -- non-vanishing spectral entries
  have hne : ∀ w : ℂ, 0 < w.im → ∀ i,
      (hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * w) ≠ 0 := fun w hw i h0 => by
    have := le_norm_shift (hF.eigenvalues i) c₀ E w
    rw [h0, norm_zero] at this
    nlinarith [mul_pos hc hw]
  have hapos : 0 < a.im := by rw [haim]; exact hρ
  unfold gammaMatched
  rw [← ha, gammaAt_eq_diag hF c₀ E m (hne m hmpos), gammaAt_eq_diag hF c₀ E a (hne a hapos),
    cd_smul, cd_smul, cd_sub, cd_sub]
  -- entrywise scalar bounds
  have hscal : ∀ i,
      c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ ^ 2 ≤
          (1 + gammaConst E * η) * (c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * a)‖ ^ 2)
        ∧ (1 - gammaConst E * η) *
            (c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * a)‖ ^ 2) ≤
          c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ ^ 2 := by
    intro i
    set α := (hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * a)
    set β := (hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)
    have hαlow : c₀ * ρ ≤ ‖α‖ := by
      have := le_norm_shift (hF.eigenvalues i) c₀ E a
      rwa [haim] at this
    have hαβ : α - β = (c₀ : ℂ) * (m - a) := by simp only [α, β]; ring
    have hdist : |‖α‖ - ‖β‖| ≤ c₀ * η := by
      refine (abs_norm_sub_norm_le α β).trans ?_
      rw [hαβ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hm hc.le
    have hA : 0 < ‖α‖ := lt_of_lt_of_le (mul_pos hc hρ) hαlow
    refine scalar_ratio hA hdist ?_ ?_ (by unfold gammaConst; positivity) hc
    · nlinarith
    · -- `8 c₀ η ≤ (8/ρ) η ‖α‖`
      have h8 : gammaConst E * η * ‖α‖ = 8 * η * (‖α‖ / ρ) := by
        unfold gammaConst; rw [← hρdef]; field_simp
      have hq : c₀ ≤ ‖α‖ / ρ := by rw [le_div_iff₀ hρ]; linarith
      rw [h8]
      nlinarith
  constructor
  · refine cd_posSemidef_of_eq _ _ (fun i => (1 + gammaConst E * η) *
        (c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * a)‖ ^ 2) -
        c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ ^ 2)
      (fun i => by push_cast; ring) (fun i => sub_nonneg.mpr (hscal i).1)
  · refine cd_posSemidef_of_eq _ _ (fun i =>
        c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * m)‖ ^ 2 -
        (1 - gammaConst E * η) *
          (c₀ / ‖(hF.eigenvalues i : ℂ) - ((E : ℂ) + (c₀ : ℂ) * a)‖ ^ 2))
      (fun i => by push_cast; ring) (fun i => sub_nonneg.mpr (hscal i).2)

/-- **Corollary (i).** The comparison for the covariance `freshGamma F c₀ E` under
`‖freshDyson F c₀ E - conj a(E)‖ ≤ η ≤ ρ/2` (Hermitian `F`, `c₀ > 0`, `-2 < E < 2`).
-/
theorem freshGamma_loewner {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c₀ E : ℝ}
    (hc : 0 < c₀) (hE1 : -2 < E) (hE2 : E < 2) {η : ℝ}
    (hm : ‖freshDyson F c₀ E - conj (matchedA E)‖ ≤ η) (hηρ : η ≤ matchedIm E / 2) :
    ((((1 + gammaConst E * η : ℝ) : ℂ) • gammaMatched F c₀ E - freshGamma F c₀ E).PosSemidef ∧
      (freshGamma F c₀ E - (((1 - gammaConst E * η : ℝ) : ℂ)) • gammaMatched F c₀ E).PosSemidef) :=
  gammaAt_loewner hF hc hE1 hE2 hm hηρ

/-!
## Parameter rewrites and the regular prior events
-/

/-- `pairS p = min b (1 - 2b)` when `p.b = b`. -/
theorem pairS_eq_of_b (p : Parameters) {b : ℝ} (h : p.b = b) : pairS p = min b (1 - 2 * b) := by
  simp [pairS, Parameters.c, h]

/-- `p.c = 1 - 2b` when `p.b = b`. -/
theorem c_eq_of_b (p : Parameters) {b : ℝ} (h : p.b = b) : p.c = 1 - 2 * b := by
  simp [Parameters.c, h]

private theorem c_pos' (p : Parameters) : 0 < p.c := by
  have := p.b_lt_half; unfold Parameters.c; linarith

private theorem pairS_pos (p : Parameters) : 0 < pairS p := lt_min p.b_pos (c_pos' p)

/-- **Pair form.** On the pair regular event
`IsPairRegular p i σ A r₀ s₀ v₀ η e ω`, for
`-2 < e < 2` and `η ≤ ρ(e)/2`, the fresh covariance of the pair deformation at variance
`pairS p` is within relative Loewner error `C(e) η` of the matched-scalar covariance. -/
theorem pairRegular_freshGamma_loewner (p : Parameters) (i : ZMod p.n)
    (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i))) {A r₀ s₀ v₀ η e : ℝ}
    {ω : SplitState p i} (hreg : IsPairRegular p i σ A r₀ s₀ v₀ η e ω)
    (he1 : -2 < e) (he2 : e < 2) (hηρ : η ≤ matchedIm e / 2) :
    ((((1 + gammaConst e * η : ℝ) : ℂ) • gammaMatched (pairDeformation p i σ ω e) (pairS p) e -
        freshGamma (pairDeformation p i σ ω e) (pairS p) e).PosSemidef ∧
      (freshGamma (pairDeformation p i σ ω e) (pairS p) e -
        (((1 - gammaConst e * η : ℝ) : ℂ)) •
          gammaMatched (pairDeformation p i σ ω e) (pairS p) e).PosSemidef) :=
  freshGamma_loewner hreg.1.1 (pairS_pos p) he1 he2 hreg.2 hηρ

/-- **Corollary (iii), one-block form.** On the block regular event
`IsBlockRegular p k σ A r₀ s₀ v₀ η e ω` (variance `p.c = 1 - 2b`), the same comparison for the
block deformation. -/
theorem blockRegular_freshGamma_loewner (p : Parameters) (k : ZMod p.n)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) {A r₀ s₀ v₀ η e : ℝ}
    {ω : BlockState p k} (hreg : IsBlockRegular p k σ A r₀ s₀ v₀ η e ω)
    (he1 : -2 < e) (he2 : e < 2) (hηρ : η ≤ matchedIm e / 2) :
    ((((1 + gammaConst e * η : ℝ) : ℂ) • gammaMatched (blockDeformation p k σ ω e) p.c e -
        freshGamma (blockDeformation p k σ ω e) p.c e).PosSemidef ∧
      (freshGamma (blockDeformation p k σ ω e) p.c e -
        (((1 - gammaConst e * η : ℝ) : ℂ)) •
          gammaMatched (blockDeformation p k σ ω e) p.c e).PosSemidef) :=
  freshGamma_loewner hreg.1.1 (c_pos' p) he1 he2 hreg.2 hηρ

end BlockBand.Endpoints.Normalization
