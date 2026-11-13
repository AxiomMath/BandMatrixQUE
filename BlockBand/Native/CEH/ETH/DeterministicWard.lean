module

public import BlockBand.Native.CEH.ETH.DeterministicApprox
public import BlockBand.Native.CEH.Phase1.Characteristic

/-!
# CEH ETH: Ward-identity bounds for the hybrid approximation

The inputs are MDE solutions `IsManuscriptMDE s F z M`, i.e. `M = (F - ζ)⁻¹` with
`ζ = z + s⟨M⟩`. Hypotheses: `s ≥ 0`, `Im zᵢ ≠ 0`, `0 ≤ σ ≤ s`, and `N > 0` for
`half_mul_sq_le_norm_one_sub_mde`. Normalized trace `⟨X⟩ = N⁻¹ tr X`; all statements are
deterministic.

## Main results

* `mul_norm_NTrace_lt_one_mde`: `s |⟨M₁^{(*)} M₂^{(*)}⟩| < 1` in every adjoint constellation
  (Cauchy–Schwarz), so all hybrid denominators are nonzero for `σ ∈ [0, s]`;
* `norm_hybridDen_le_two_mul_mde`: `|1 - σc| ≤ 2|1 - σ'c|`, `0 ≤ σ' ≤ σ ≤ s`, every
  constellation `c = ⟨M₁^{(*)}M₂^{(*)}⟩`;
* `norm_NTrace_twoResApprox_one_le_mde`: `|⟨M^I_σ⟩| ≤ ½(πρ₁/η_{1,σ} + πρ₂/η_{2,σ})` in every
  constellation;
* `half_mul_sq_le_norm_one_sub_mde`: `s (Im m₁ + Im m₂)² / 2 ≤ |1 - s⟨M₁M₂⟩|`, for
  arbitrary nonreal `z₁, z₂` (any `F₁, F₂`), from
  `2 Re(1 - s⟨M₁M₂⟩) = (1 - s a₁) + (1 - s a₂) + s⟨|M₁ - M₂ᴴ|²⟩ ≥ s |⟨M₁ - M₂ᴴ⟩|²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Internal.Contracts.Inputs (IsManuscriptMDE)
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## Generic trace inequalities
-/

/-- `NTrace` is the normalized trace `External.CEH.normalizedTrace`. -/
theorem NTrace_eq_normalizedTrace (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace X = BlockBand.External.CEH.normalizedTrace X := rfl

/-- The Ward mass `a(X) = Re⟨X Xᴴ⟩ = N⁻¹ ‖X‖²_HS`. -/
def wardMass (X : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (NTrace (X * Xᴴ)).re

theorem wardMass_nonneg (X : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ wardMass X :=
  Phase1.normalizedTrace_mul_conjTranspose_self_re_nonneg X

theorem NTrace_conjTranspose_mul_self (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (Xᴴ * X) = NTrace (X * Xᴴ) := by
  simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_mul_comm Xᴴ X]

@[simp] theorem wardMass_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) :
    wardMass Xᴴ = wardMass X := by
  rw [wardMass, wardMass, conjTranspose_conjTranspose, NTrace_conjTranspose_mul_self]

theorem wardMass_chooseAdjoint (c : AdjointChoice) (X : Matrix (Fin N) (Fin N) ℂ) :
    wardMass (chooseAdjoint c X) = wardMass X := by
  cases c <;> simp

/-- Cauchy–Schwarz: `|⟨X Y⟩| ≤ √a(X) √a(Y)`. -/
theorem norm_NTrace_mul_le_wardMass (X Y : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace (X * Y)‖ ≤ Real.sqrt (wardMass X) * Real.sqrt (wardMass Y) := by
  have h := Phase1.norm_normalizedTrace_mul_le X Y
  rw [← NTrace_eq_normalizedTrace, ← NTrace_eq_normalizedTrace,
    ← NTrace_eq_normalizedTrace, NTrace_conjTranspose_mul_self] at h
  exact h

/-- `|⟨X⟩|² ≤ a(X)` for `N > 0`. -/
theorem norm_NTrace_sq_le_wardMass (hN : 0 < N) (X : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace X‖ ^ 2 ≤ wardMass X := by
  have h := norm_NTrace_mul_le_wardMass X 1
  have h1 : wardMass (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have : NeZero N := ⟨hN.ne'⟩
    simp [wardMass, NTrace, Conventions.normalizedTrace, Matrix.trace_one]
  rw [Matrix.mul_one, h1, Real.sqrt_one, mul_one] at h
  calc ‖NTrace X‖ ^ 2 ≤ Real.sqrt (wardMass X) ^ 2 := by
        gcongr
    _ = wardMass X := Real.sq_sqrt (wardMass_nonneg X)

/-- The scalar core of the `M^I_σ` bound: if `|c| ≤ √a₁√a₂`, `aᵢ ≥ 0`, `σ ≥ 0`, `σ aᵢ < 1`, then
`|c / (1 - σc)| ≤ ½ (a₁/(1 - σa₁) + a₂/(1 - σa₂))`. (Convexity of `x ↦ x/(1 - σx)` and AM–GM.) -/
theorem norm_div_one_sub_le_half_add {c : ℂ} {σ a₁ a₂ : ℝ} (hσ : 0 ≤ σ) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (h₁ : σ * a₁ < 1) (h₂ : σ * a₂ < 1)
    (hc : ‖c‖ ≤ Real.sqrt a₁ * Real.sqrt a₂) :
    ‖c / (1 - (σ : ℂ) * c)‖ ≤ (a₁ / (1 - σ * a₁) + a₂ / (1 - σ * a₂)) / 2 := by
  set m := (a₁ + a₂) / 2 with hm
  have hg : Real.sqrt a₁ * Real.sqrt a₂ ≤ m := by
    have := sq_nonneg (Real.sqrt a₁ - Real.sqrt a₂)
    have e1 := Real.sq_sqrt ha₁
    have e2 := Real.sq_sqrt ha₂
    nlinarith
  have hcm : ‖c‖ ≤ m := hc.trans hg
  have hσm : σ * m < 1 := by rw [hm]; nlinarith
  have hw : 0 < 1 - σ * m := by linarith
  have hlow := one_sub_mul_norm_le_norm_one_sub c hσ
  have hcn := norm_nonneg c
  have hden : 1 - σ * m ≤ ‖1 - (σ : ℂ) * c‖ := by nlinarith
  have hdpos : 0 < ‖1 - (σ : ℂ) * c‖ := lt_of_lt_of_le hw hden
  have step1 : ‖c / (1 - (σ : ℂ) * c)‖ ≤ m / (1 - σ * m) := by
    rw [norm_div, div_le_div_iff₀ hdpos hw]
    nlinarith
  have hu₁ : 0 < 1 - σ * a₁ := by linarith
  have hu₂ : 0 < 1 - σ * a₂ := by linarith
  have step2 : (a₁ / (1 - σ * a₁) + a₂ / (1 - σ * a₂)) / 2 - m / (1 - σ * m) =
      σ * (a₁ - a₂) ^ 2 / (4 * (1 - σ * a₁) * (1 - σ * a₂) * (1 - σ * m)) := by
    have hw' := hw.ne'
    have hu₁' := hu₁.ne'
    have hu₂' := hu₂.ne'
    rw [div_add_div _ _ hu₁' hu₂', div_div, div_sub_div _ _ (by positivity) hw',
      div_eq_div_iff (by positivity) (by positivity)]
    rw [hm]
    ring
  have step3 : 0 ≤ σ * (a₁ - a₂) ^ 2 / (4 * (1 - σ * a₁) * (1 - σ * a₂) * (1 - σ * m)) := by
    positivity
  linarith

/-!
## The MDE Ward mass
-/

section MDE

variable {s : ℝ} {F : BlockBand.External.CEH.SourceHermitian N} {z : ℂ}
  {M : BlockBand.External.CEH.SourceMatrix N}

private theorem div_eq_abs_div_abs {x y : ℝ} (hxy : 0 ≤ x * y) :
    x / y = |x| / |y| := by
  rw [← abs_div]
  refine (abs_of_nonneg ?_).symm
  rcases eq_or_ne y 0 with hy | hy
  · simp [hy]
  · have : x / y = x * y / y ^ 2 := by field_simp
    rw [this]
    positivity

/-- **The MDE Ward mass**: `a(M) = Re⟨M Mᴴ⟩ = |Im m| / (|Im z| + s |Im m|)`. -/
theorem wardMass_mde (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    wardMass M = |(NTrace M).im| / (|z.im| + s * |(NTrace M).im|) := by
  have hW := Phase1.mde_imaginaryPart_eq h hz hs
  set ζ := z + (s : ℂ) * BlockBand.External.CEH.normalizedTrace M with hζ
  have hζne : ζ.im ≠ 0 := Phase1.mde_im_spectral_ne h hz hs
  have htr := congrArg BlockBand.External.CEH.normalizedTrace hW
  rw [Phase1.mde_normalizedTrace_imaginaryPart, Phase1.normalizedTrace_smul] at htr
  have hre := congrArg Complex.re htr
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre
  have hmass : wardMass M = (NTrace M).im / ζ.im := by
    rw [wardMass, eq_div_iff hζne, mul_comm]
    exact hre.symm
  rw [hmass, show |z.im| + s * |(NTrace M).im| = |ζ.im| from
    (Phase1.mde_abs_im_spectral h hs).symm]
  apply div_eq_abs_div_abs
  have h1 := Phase1.mde_im_mul_im_nonneg h
  have h2 := Phase1.mde_im_mul_im_spectral_pos h hz hs
  have h3 : 0 ≤ ((z.im * (NTrace M).im) * (z.im * ζ.im)) := mul_nonneg h1 h2.le
  have h4 : 0 < z.im ^ 2 := by positivity
  have : ((z.im * (NTrace M).im) * (z.im * ζ.im)) = z.im ^ 2 * ((NTrace M).im * ζ.im) := by
    ring
  rw [this] at h3
  exact (mul_nonneg_iff_of_pos_left h4).1 h3

/-- `s a(M) < 1` for the MDE solution at a nonreal `z`. -/
theorem mul_wardMass_mde_lt_one (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) :
    s * wardMass M < 1 := by
  rw [wardMass_mde h hz hs]
  have hz' : 0 < |z.im| := abs_pos.2 hz
  have ht := abs_nonneg (NTrace M).im
  have hD : 0 < |z.im| + s * |(NTrace M).im| := by positivity
  rw [mul_div_assoc', div_lt_one hD]
  linarith

/-- For `0 ≤ σ ≤ s`: `a(M) / (1 - σ a(M)) = |Im m| / (|Im z| + (s - σ)|Im m|)`. -/
theorem wardMass_div_mde (h : IsManuscriptMDE s F z M) (hz : z.im ≠ 0) (hs : 0 ≤ s) {σ : ℝ}
    (hσs : σ ≤ s) :
    wardMass M / (1 - σ * wardMass M) =
      |(NTrace M).im| / (|z.im| + (s - σ) * |(NTrace M).im|) := by
  rw [wardMass_mde h hz hs]
  have hz' : 0 < |z.im| := abs_pos.2 hz
  have ht := abs_nonneg (NTrace M).im
  have hD : 0 < |z.im| + s * |(NTrace M).im| := by positivity
  have hD' : 0 < |z.im| + (s - σ) * |(NTrace M).im| := by
    have : 0 ≤ (s - σ) * |(NTrace M).im| := mul_nonneg (by linarith) ht
    linarith
  field_simp
  ring

end MDE

/-!
## Constellation bounds for MDE pairs
-/

section Pair

variable {s : ℝ} {F₁ F₂ : BlockBand.External.CEH.SourceHermitian N} {z₁ z₂ : ℂ}
  {M₁ M₂ : BlockBand.External.CEH.SourceMatrix N}

/-- **`s |⟨M₁^{(*)}M₂^{(*)}⟩| < 1`** in every adjoint constellation (Cauchy–Schwarz and Ward). -/
theorem mul_norm_NTrace_lt_one_mde (h₁ : IsManuscriptMDE s F₁ z₁ M₁)
    (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s)
    (c₁ c₂ : AdjointChoice) :
    s * ‖NTrace (chooseAdjoint c₁ M₁ * chooseAdjoint c₂ M₂)‖ < 1 := by
  have hcs := norm_NTrace_mul_le_wardMass (chooseAdjoint c₁ M₁) (chooseAdjoint c₂ M₂)
  rw [wardMass_chooseAdjoint, wardMass_chooseAdjoint] at hcs
  have ha₁ := mul_wardMass_mde_lt_one h₁ hz₁ hs
  have ha₂ := mul_wardMass_mde_lt_one h₂ hz₂ hs
  have n₁ := wardMass_nonneg M₁
  have n₂ := wardMass_nonneg M₂
  have e₁ := Real.sq_sqrt n₁
  have e₂ := Real.sq_sqrt n₂
  have r₁ := Real.sqrt_nonneg (wardMass M₁)
  have r₂ := Real.sqrt_nonneg (wardMass M₂)
  -- `s √a₁ √a₂ < 1` since `(s √a₁ √a₂)² = (s a₁)(s a₂) < 1`
  have hprod : s * (Real.sqrt (wardMass M₁) * Real.sqrt (wardMass M₂)) < 1 := by
    have hsq : (s * (Real.sqrt (wardMass M₁) * Real.sqrt (wardMass M₂))) ^ 2 < 1 := by
      have : (s * (Real.sqrt (wardMass M₁) * Real.sqrt (wardMass M₂))) ^ 2 =
          (s * wardMass M₁) * (s * wardMass M₂) := by
        rw [mul_pow, mul_pow, e₁, e₂]; ring
      rw [this]
      have p₁ : 0 ≤ s * wardMass M₁ := mul_nonneg hs n₁
      have p₂ : 0 ≤ s * wardMass M₂ := mul_nonneg hs n₂
      nlinarith
    have hnn : 0 ≤ s * (Real.sqrt (wardMass M₁) * Real.sqrt (wardMass M₂)) := by positivity
    nlinarith
  calc s * ‖NTrace (chooseAdjoint c₁ M₁ * chooseAdjoint c₂ M₂)‖
      ≤ s * (Real.sqrt (wardMass M₁) * Real.sqrt (wardMass M₂)) :=
        mul_le_mul_of_nonneg_left hcs hs
    _ < 1 := hprod

/-- **Denominator transfer for MDE pairs**: for `0 ≤ σ' ≤ σ ≤ s` and every
constellation, `|1 - σ⟨M₁^{(*)}M₂^{(*)}⟩| ≤ 2 |1 - σ'⟨M₁^{(*)}M₂^{(*)}⟩|`. -/
theorem norm_hybridDen_le_two_mul_mde (h₁ : IsManuscriptMDE s F₁ z₁ M₁)
    (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s)
    (c₁ c₂ : AdjointChoice) {σ σ' : ℝ} (h0 : 0 ≤ σ') (h1 : σ' ≤ σ) (h2 : σ ≤ s) :
    ‖hybridDen σ (chooseAdjoint c₁ M₁) (chooseAdjoint c₂ M₂)‖ ≤
      2 * ‖hybridDen σ' (chooseAdjoint c₁ M₁) (chooseAdjoint c₂ M₂)‖ := by
  have hlt := mul_norm_NTrace_lt_one_mde h₁ h₂ hz₁ hz₂ hs c₁ c₂
  apply norm_one_sub_le_two_mul _ h0 h1
  exact (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans hlt.le

/-- The hybrid denominators do not vanish for `0 ≤ σ ≤ s`. -/
theorem hybridDen_ne_zero_mde (h₁ : IsManuscriptMDE s F₁ z₁ M₁)
    (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s)
    (c₁ c₂ : AdjointChoice) {σ : ℝ} (h0 : 0 ≤ σ) (h2 : σ ≤ s) :
    hybridDen σ (chooseAdjoint c₁ M₁) (chooseAdjoint c₂ M₂) ≠ 0 := by
  have hlt := mul_norm_NTrace_lt_one_mde h₁ h₂ hz₁ hz₂ hs c₁ c₂
  have := norm_one_sub_pos (NTrace (chooseAdjoint c₁ M₁ * chooseAdjoint c₂ M₂)) h0
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) hlt)
  exact norm_pos_iff.1 this

/-- **The `A = I` approximation**: for `0 ≤ σ ≤ s` and every constellation,
`|⟨M^I_σ⟩| ≤ ½ (|Im m₁| / η_{1,σ} + |Im m₂| / η_{2,σ})`, with
`η_{i,σ} = |Im zᵢ| + (s - σ) |Im mᵢ|` and `|Im mᵢ| = π ρᵢ`. -/
theorem norm_NTrace_twoResApprox_one_le_mde (h₁ : IsManuscriptMDE s F₁ z₁ M₁)
    (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s)
    (c₁ c₂ : AdjointChoice) {σ : ℝ} (h0 : 0 ≤ σ) (h2 : σ ≤ s) :
    ‖NTrace (twoResApprox σ (chooseAdjoint c₁ M₁) 1 (chooseAdjoint c₂ M₂))‖ ≤
      (|(NTrace M₁).im| / (|z₁.im| + (s - σ) * |(NTrace M₁).im|) +
        |(NTrace M₂).im| / (|z₂.im| + (s - σ) * |(NTrace M₂).im|)) / 2 := by
  rw [NTrace_twoResApprox_one σ _ _ (hybridDen_ne_zero_mde h₁ h₂ hz₁ hz₂ hs c₁ c₂ h0 h2),
    ← wardMass_div_mde h₁ hz₁ hs h2, ← wardMass_div_mde h₂ hz₂ hs h2]
  have hcs := norm_NTrace_mul_le_wardMass (chooseAdjoint c₁ M₁) (chooseAdjoint c₂ M₂)
  rw [wardMass_chooseAdjoint, wardMass_chooseAdjoint] at hcs
  have ha₁ : σ * wardMass M₁ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 (wardMass_nonneg _))
      (mul_wardMass_mde_lt_one h₁ hz₁ hs)
  have ha₂ : σ * wardMass M₂ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 (wardMass_nonneg _))
      (mul_wardMass_mde_lt_one h₂ hz₂ hs)
  exact norm_div_one_sub_le_half_add h0 (wardMass_nonneg _) (wardMass_nonneg _) ha₁ ha₂ hcs

/-!
## The target stable denominator
-/

/-- **Lower bound on the stable denominator** (generic form): for `N > 0`, `s ≥ 0`
and matrices with `s a(Mᵢ) ≤ 1`,
`s (Im⟨M₁⟩ + Im⟨M₂⟩)² / 2 ≤ |1 - s⟨M₁M₂⟩|`.
Proof: `2 Re(1 - s⟨M₁M₂⟩) = (1 - s a₁) + (1 - s a₂) + s a(M₁ - M₂ᴴ)` and
`a(M₁ - M₂ᴴ) ≥ |⟨M₁ - M₂ᴴ⟩|² ≥ (Im m₁ + Im m₂)²`. -/
theorem half_mul_sq_le_norm_one_sub (hN : 0 < N) (hs : 0 ≤ s)
    (X₁ X₂ : Matrix (Fin N) (Fin N) ℂ) (h₁ : s * wardMass X₁ ≤ 1) (h₂ : s * wardMass X₂ ≤ 1) :
    s * ((NTrace X₁).im + (NTrace X₂).im) ^ 2 / 2 ≤ ‖1 - (s : ℂ) * NTrace (X₁ * X₂)‖ := by
  set D := X₁ - X₂ᴴ with hD
  have hexp : wardMass D = wardMass X₁ + wardMass X₂ - 2 * (NTrace (X₁ * X₂)).re := by
    have hm : D * Dᴴ = X₁ * X₁ᴴ - X₁ * X₂ - X₂ᴴ * X₁ᴴ + X₂ᴴ * X₂ := by
      rw [hD, conjTranspose_sub, conjTranspose_conjTranspose]
      noncomm_ring
    have hstar : NTrace (X₂ᴴ * X₁ᴴ) = star (NTrace (X₁ * X₂)) := by
      rw [← conjTranspose_mul]
      simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_conjTranspose, star_mul',
        star_inv₀, star_natCast]
    rw [wardMass, hm, NTrace_add, NTrace_sub, NTrace_sub, hstar, NTrace_conjTranspose_mul_self]
    simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
    rw [wardMass, wardMass]
    ring
  have hcs := norm_NTrace_sq_le_wardMass hN D
  have hIm : (NTrace D).im = (NTrace X₁).im + (NTrace X₂).im := by
    rw [hD, NTrace_sub]
    simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_conjTranspose]
    simp [Complex.mul_im]
  have him : |(NTrace D).im| ≤ ‖NTrace D‖ := Complex.abs_im_le_norm _
  have hsq : ((NTrace X₁).im + (NTrace X₂).im) ^ 2 ≤ wardMass D := by
    rw [← hIm, ← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) him 2).trans hcs
  have hre : (1 - (s : ℂ) * NTrace (X₁ * X₂)).re ≤ ‖1 - (s : ℂ) * NTrace (X₁ * X₂)‖ :=
    Complex.re_le_norm _
  rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul] at hre
  have : s * ((NTrace X₁).im + (NTrace X₂).im) ^ 2 ≤ s * wardMass D :=
    mul_le_mul_of_nonneg_left hsq hs
  nlinarith

/-- **Lower bound on the stable denominator, MDE form**: for the MDE solutions at arbitrary
nonreal `z₁, z₂` and `N > 0`, `s (Im m₁ + Im m₂)² / 2 ≤ |1 - s⟨M₁M₂⟩|`. -/
theorem half_mul_sq_le_norm_one_sub_mde (hN : 0 < N) (h₁ : IsManuscriptMDE s F₁ z₁ M₁)
    (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s) :
    s * ((NTrace M₁).im + (NTrace M₂).im) ^ 2 / 2 ≤ ‖1 - (s : ℂ) * NTrace (M₁ * M₂)‖ :=
  half_mul_sq_le_norm_one_sub hN hs M₁ M₂ (mul_wardMass_mde_lt_one h₁ hz₁ hs).le
    (mul_wardMass_mde_lt_one h₂ hz₂ hs).le

/-- **Lower bound on the stable denominator, window form**: if `κ ≤ Im mᵢ` (density `≥ κ/π`)
then `2 s κ² ≤ |1 - s⟨M₁M₂⟩|`; with `κ = π/K` (density `≥ 1/K`) this is `2 s π²/K²`. -/
theorem two_mul_sq_le_norm_one_sub_mde (hN : 0 < N) (h₁ : IsManuscriptMDE s F₁ z₁ M₁)
    (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκ₁ : κ ≤ (NTrace M₁).im) (hκ₂ : κ ≤ (NTrace M₂).im) :
    2 * s * κ ^ 2 ≤ ‖1 - (s : ℂ) * NTrace (M₁ * M₂)‖ := by
  refine le_trans ?_ (half_mul_sq_le_norm_one_sub_mde hN h₁ h₂ hz₁ hz₂ hs)
  have : 2 * κ ≤ (NTrace M₁).im + (NTrace M₂).im := by linarith
  have h4 : (2 * κ) ^ 2 ≤ ((NTrace M₁).im + (NTrace M₂).im) ^ 2 :=
    pow_le_pow_left₀ (by linarith) this 2
  nlinarith

end Pair

end BlockBand.Native.CEH.ETH
