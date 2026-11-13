module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHRectangularGridFinalPackaging

/-!
# CEH ETH: the hybrid deterministic two-resolvent approximation

**Hybrid setting.** The matrices `M₁, M₂` are fixed (in the application, the
target MDE solutions `Mᵢ = M(zᵢ)` at variance `s`, or their adjoints in any constellation); the
variance `σ ∈ [0, s]` enters only through the scalar denominator `1 - σ⟨M₁M₂⟩` and the
prefactor `σ`:

`M^A_σ = M₁ A M₂ + σ ⟨M₁AM₂⟩ (1 - σ⟨M₁M₂⟩)⁻¹ M₁ M₂`   (CEH (5.22) with `λ² ↦ σ`).

All statements are finite-dimensional algebra; no probability, no limit.

## Main results

* the σ-derivative identity `d/dσ ⟨M^A_σ B⟩ = ⟨M^A_σ⟩ ⟨M^B_σ(z₂, z₁)⟩`
  (`hasDerivAt_NTrace_twoResApprox_mul`);
* the denominator transfer `|1 - σc| ≤ 2 |1 - σ'c|` for `0 ≤ σ' ≤ σ`, `σ|c| ≤ 1`
  (`norm_one_sub_le_two_mul`);
* the hybrid control `s₂(σ)` (`sTwoAt`) and its monotonicity (`sTwoAt_mono`).
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
## The hybrid deterministic approximation
-/

/-- The hybrid stability denominator `1 - σ ⟨M₁ M₂⟩`. -/
def hybridDen (σ : ℝ) (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  1 - (σ : ℂ) * NTrace (M₁ * M₂)

/-- **The hybrid deterministic two-resolvent approximation** (CEH (5.22), variance `σ`, `M`'s
fixed at the target): `M^A_σ = M₁AM₂ + σ⟨M₁AM₂⟩(1 - σ⟨M₁M₂⟩)⁻¹ M₁M₂`. The adjoint
constellations are obtained by passing `Mᵢᴴ` for `Mᵢ`. -/
def twoResApprox (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  M₁ * A * M₂ + ((σ : ℂ) * (NTrace (M₁ * A * M₂) / hybridDen σ M₁ M₂)) • (M₁ * M₂)

/-- Relation to the approximation: for any `l` with `l² = σ`, `twoResApprox σ` is the
`twoResolventApprox l`.
-/
theorem twoResApprox_eq_twoResolventApprox (σ : ℝ) (l : ℂ) (hl : l ^ 2 = σ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    twoResApprox σ M₁ A M₂ = twoResolventApprox l M₁ A M₂ := by
  simp only [twoResApprox, twoResolventApprox, hybridDen, stabilityDenominator, hl, NTrace]

/-- Relation to the approximation at `λ = √σ`, `σ ≥ 0`. -/
theorem twoResApprox_eq_twoResolventApprox_sqrt {σ : ℝ} (hσ : 0 ≤ σ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    twoResApprox σ M₁ A M₂ = twoResolventApprox (Real.sqrt σ : ℂ) M₁ A M₂ :=
  twoResApprox_eq_twoResolventApprox σ _ (by rw [← Complex.ofReal_pow, Real.sq_sqrt hσ]) _ _ _

theorem hybridDen_eq_stabilityDenominator {σ : ℝ} (hσ : 0 ≤ σ)
    (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) :
    hybridDen σ M₁ M₂ = stabilityDenominator (Real.sqrt σ : ℂ) (NTrace (M₁ * M₂)) := by
  rw [hybridDen, stabilityDenominator, ← Complex.ofReal_pow, Real.sq_sqrt hσ]

/-- `⟨M^A_σ B⟩ = ⟨M₁AM₂B⟩ + σ ⟨M₁AM₂⟩/(1-σ⟨M₁M₂⟩) · ⟨M₁M₂B⟩`, with no hypothesis. -/
theorem NTrace_twoResApprox_mul (σ : ℝ) (M₁ A M₂ B : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (twoResApprox σ M₁ A M₂ * B) =
      NTrace (M₁ * A * M₂ * B) +
        (σ : ℂ) * (NTrace (M₁ * A * M₂) / hybridDen σ M₁ M₂) * NTrace (M₁ * M₂ * B) := by
  rw [twoResApprox, Matrix.add_mul, NTrace_add, Matrix.smul_mul, NTrace_smul]

/-- `⟨M^A_σ⟩ = ⟨M₁AM₂⟩ / (1 - σ⟨M₁M₂⟩)` when the denominator is nonzero. -/
theorem NTrace_twoResApprox (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hden : hybridDen σ M₁ M₂ ≠ 0) :
    NTrace (twoResApprox σ M₁ A M₂) = NTrace (M₁ * A * M₂) / hybridDen σ M₁ M₂ := by
  have h := NTrace_twoResApprox_mul σ M₁ A M₂ 1
  simp only [Matrix.mul_one] at h
  rw [h]
  have hd : hybridDen σ M₁ M₂ = 1 - (σ : ℂ) * NTrace (M₁ * M₂) := rfl
  field_simp
  rw [hd]
  ring

/-- `⟨M^I_σ⟩ = ⟨M₁M₂⟩ / (1 - σ⟨M₁M₂⟩)`. -/
theorem NTrace_twoResApprox_one (σ : ℝ) (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hden : hybridDen σ M₁ M₂ ≠ 0) :
    NTrace (twoResApprox σ M₁ 1 M₂) = NTrace (M₁ * M₂) / hybridDen σ M₁ M₂ := by
  rw [NTrace_twoResApprox σ M₁ 1 M₂ hden, Matrix.mul_one]

/-- The denominator is symmetric: `⟨M₂M₁⟩ = ⟨M₁M₂⟩`. -/
theorem hybridDen_comm (σ : ℝ) (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ) :
    hybridDen σ M₂ M₁ = hybridDen σ M₁ M₂ := by
  simp only [hybridDen, NTrace, Conventions.normalizedTrace, Matrix.trace_mul_comm M₂ M₁]

/-!
## The σ-derivative identity
-/

/-- **σ-derivative of the hybrid approximation**: for all matrices
`M₁ A M₂ B` (any adjoint constellation) and every `σ` with `1 - σ⟨M₁M₂⟩ ≠ 0`,
`d/dσ ⟨M^A_σ(z₁,z₂) B⟩ = ⟨M^A_σ(z₁,z₂)⟩ ⟨M^B_σ(z₂,z₁)⟩`, where
`M^B_σ(z₂,z₁) = twoResApprox σ M₂ B M₁`. This is the deterministic counterpart of the drift
`⟨R₁AR₂⟩⟨R₂BR₁⟩` of `⟨R₁AR₂B⟩` along the characteristic flow. -/
theorem hasDerivAt_NTrace_twoResApprox_mul (M₁ A M₂ B : Matrix (Fin N) (Fin N) ℂ) (σ : ℝ)
    (hden : hybridDen σ M₁ M₂ ≠ 0) :
    HasDerivAt (fun τ : ℝ => NTrace (twoResApprox τ M₁ A M₂ * B))
      (NTrace (twoResApprox σ M₁ A M₂) * NTrace (twoResApprox σ M₂ B M₁)) σ := by
  set c := NTrace (M₁ * M₂) with hc
  set w := NTrace (M₁ * A * M₂) with hw
  set p := NTrace (M₁ * M₂ * B) with hp
  have hfun : (fun τ : ℝ => NTrace (twoResApprox τ M₁ A M₂ * B)) =
      fun τ : ℝ => NTrace (M₁ * A * M₂ * B) + (τ : ℂ) * (w / (1 - (τ : ℂ) * c)) * p := by
    funext τ
    rw [NTrace_twoResApprox_mul]
    rfl
  have hden' : (1 : ℂ) - (σ : ℂ) * c ≠ 0 := hden
  have hid : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 σ := by
    simpa using (hasDerivAt_id σ).ofReal_comp
  have hD : HasDerivAt (fun τ : ℝ => (1 : ℂ) - (τ : ℂ) * c) (-c) σ := by
    simpa using (hid.mul_const c).const_sub 1
  have hq : HasDerivAt (fun τ : ℝ => w / (1 - (τ : ℂ) * c))
      (w * c / (1 - (σ : ℂ) * c) ^ 2) σ := by
    have := (hD.inv hden').const_mul w
    convert this using 1
    · funext τ
      rw [div_eq_mul_inv]
      rfl
    · ring
  have hmain := (((hid.mul hq).mul_const p).const_add (NTrace (M₁ * A * M₂ * B)))
  rw [hfun]
  convert hmain using 1
  -- identify the value
  have h21 : hybridDen σ M₂ M₁ = 1 - (σ : ℂ) * c := by rw [hybridDen_comm]; rfl
  rw [NTrace_twoResApprox σ M₁ A M₂ hden, NTrace_twoResApprox σ M₂ B M₁ (by rw [h21]; exact hden'),
    h21]
  have hcyc : NTrace (M₂ * B * M₁) = p := by
    simp only [hp, NTrace, Conventions.normalizedTrace]
    rw [Matrix.trace_mul_comm (M₂ * B) M₁, Matrix.mul_assoc]
  rw [hcyc]
  change w / (1 - (σ : ℂ) * c) * (p / (1 - (σ : ℂ) * c)) = _
  field_simp
  ring

/-!
## The denominator transfer
-/

/-- **Denominator transfer.** For `c ∈ ℂ` and `0 ≤ σ' ≤ σ` with `σ |c| ≤ 1`,
`|1 - σc| ≤ 2 |1 - σ'c|`. Proof: `|1 - σc| ≤ |1 - σ'c| + (σ - σ')|c|` and
`|1 - σ'c| ≥ 1 - σ'|c| ≥ (σ - σ')|c|`. -/
theorem norm_one_sub_le_two_mul (c : ℂ) {σ σ' : ℝ} (h0 : 0 ≤ σ') (h1 : σ' ≤ σ)
    (h : σ * ‖c‖ ≤ 1) :
    ‖1 - (σ : ℂ) * c‖ ≤ 2 * ‖1 - (σ' : ℂ) * c‖ := by
  have htri : ‖1 - (σ : ℂ) * c‖ ≤ ‖1 - (σ' : ℂ) * c‖ + (σ - σ') * ‖c‖ := by
    have : (1 : ℂ) - (σ : ℂ) * c = (1 - (σ' : ℂ) * c) - ((σ - σ' : ℝ) : ℂ) * c := by
      push_cast; ring
    rw [this]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hlow : 1 - σ' * ‖c‖ ≤ ‖1 - (σ' : ℂ) * c‖ := by
    have h2 := norm_sub_norm_le (1 : ℂ) ((σ' : ℂ) * c)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0] at h2
    exact h2
  have hc := norm_nonneg c
  nlinarith

/-- The reverse form used along the flow: for `0 ≤ σ ≤ s` and `s |c| ≤ 1`,
`|1 - sc| ≤ 2 |1 - σc|`. -/
theorem norm_one_sub_target_le_two_mul (c : ℂ) {σ s : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ s)
    (h : s * ‖c‖ ≤ 1) :
    ‖1 - (s : ℂ) * c‖ ≤ 2 * ‖1 - (σ : ℂ) * c‖ :=
  norm_one_sub_le_two_mul c h0 h1 h

/-- For `0 ≤ σ` and `σ |c| < 1`, the denominator does not vanish: `|1 - σc| ≥ 1 - σ|c| > 0`. -/
theorem one_sub_mul_norm_le_norm_one_sub (c : ℂ) {σ : ℝ} (h0 : 0 ≤ σ) :
    1 - σ * ‖c‖ ≤ ‖1 - (σ : ℂ) * c‖ := by
  have h2 := norm_sub_norm_le (1 : ℂ) ((σ : ℂ) * c)
  rwa [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0] at h2

theorem norm_one_sub_pos (c : ℂ) {σ : ℝ} (h0 : 0 ≤ σ) (h : σ * ‖c‖ < 1) :
    0 < ‖1 - (σ : ℂ) * c‖ :=
  lt_of_lt_of_le (by linarith) (one_sub_mul_norm_le_norm_one_sub c h0)

/-- The scalar monotonicity behind `sTwoAt`: for `0 ≤ σ' ≤ σ` and `σ |c| ≤ 1`,
`σ' |1 - σc| ≤ σ |1 - σ'c|`, i.e. `σ ↦ σ / |1 - σc|` is monotone. -/
theorem mul_norm_one_sub_le (c : ℂ) {σ σ' : ℝ} (h0 : 0 ≤ σ') (h1 : σ' ≤ σ)
    (h : σ * ‖c‖ ≤ 1) :
    σ' * ‖1 - (σ : ℂ) * c‖ ≤ σ * ‖1 - (σ' : ℂ) * c‖ := by
  have hσ : 0 ≤ σ := h0.trans h1
  -- compare squares: `|σ' - σσ'c|² ≤ |σ - σσ'c|²`
  have hre : σ * c.re ≤ 1 := by
    have := Complex.re_le_norm c
    nlinarith
  have hsq : ‖(σ' : ℂ) - (σ * σ' : ℝ) * c‖ ^ 2 ≤ ‖(σ : ℂ) - (σ * σ' : ℝ) * c‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) h0, mul_nonneg (sub_nonneg.2 h1) hσ]
  have e1 : σ' * ‖1 - (σ : ℂ) * c‖ = ‖(σ' : ℂ) - (σ * σ' : ℝ) * c‖ := by
    rw [show (σ' : ℂ) - ((σ * σ' : ℝ) : ℂ) * c = (σ' : ℂ) * (1 - (σ : ℂ) * c) by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have e2 : σ * ‖1 - (σ' : ℂ) * c‖ = ‖(σ : ℂ) - (σ * σ' : ℝ) * c‖ := by
    rw [show (σ : ℂ) - ((σ * σ' : ℝ) : ℂ) * c = (σ : ℂ) * (1 - (σ' : ℂ) * c) by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ]
  rw [e1, e2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-!
## The hybrid control `s₂` (CEH (5.27))
-/

/-- The base term `⟨Γ₁ A Γ₂ A*⟩` (real part) of the CEH control, `Γᵢ = Im Mᵢ / ⟨Im Mᵢ⟩`. -/
def sTwoBase (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (NTrace (gammaMatrix M₁ * A * gammaMatrix M₂ * Aᴴ)).re

/-- The product of the two stable numerators `|⟨M₁AΓ₂⟩⟨Γ₁A*M₂⟩|`. -/
def sTwoNum (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ‖NTrace (M₁ * A * gammaMatrix M₂) * NTrace (gammaMatrix M₁ * Aᴴ * M₂)‖

/-- **The hybrid CEH control** with prefactor `p` and variance `σ`:
`⟨Γ₁AΓ₂A*⟩ + p |⟨M₁AΓ₂⟩⟨Γ₁A*M₂⟩ / (1 - σ⟨M₁M₂⟩)|`, with `M₁ = M(z₁⁺)`, `M₂ = M(z₂⁺)`.
CEH (5.27) in variance time is `p = s` (target `λ² = s`), the time-dependent control is `p = σ`. -/
def sTwoSqHybrid (p σ : ℝ) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sTwoBase M₁ M₂ A + p * ‖NTrace (M₁ * A * gammaMatrix M₂) *
    NTrace (gammaMatrix M₁ * Aᴴ * M₂) / hybridDen σ M₁ M₂‖

/-- The time-dependent control `s₂(σ) = √(sTwoSqHybrid σ σ)` (variance time). -/
def sTwoAt (σ : ℝ) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (sTwoSqHybrid σ σ M₁ M₂ A)

theorem sTwoSqHybrid_eq (p σ : ℝ) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoSqHybrid p σ M₁ M₂ A =
      sTwoBase M₁ M₂ A + p * sTwoNum M₁ M₂ A / ‖hybridDen σ M₁ M₂‖ := by
  rw [sTwoSqHybrid, sTwoNum, norm_div, mul_div_assoc]

/-- At the target, the hybrid control is the `sTwoSq 1 (√s)` used by E1 (θ = 1). -/
theorem sTwoSqHybrid_target {s : ℝ} (hs : 0 ≤ s) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoSqHybrid s s M₁ M₂ A = sTwoSq 1 (Real.sqrt s : ℂ) M₁ M₂ A := by
  simp only [sTwoSqHybrid, sTwoSq, sTwoBase, hybridDen_eq_stabilityDenominator hs]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hs]
  ring

/-- **`s₂(s)` is the `sTwo`** at `θ = 1`, `λ = √s`. -/
theorem sTwoAt_target {s : ℝ} (hs : 0 ≤ s) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoAt s M₁ M₂ A = sTwo 1 (Real.sqrt s : ℂ) M₁ M₂ A := by
  rw [sTwoAt, sTwo, sTwoSqHybrid_target hs]

/-- `sTwoSqHybrid p σ ≥ ⟨Γ₁AΓ₂A*⟩` for `p ≥ 0`. -/
theorem sTwoBase_le_sTwoSqHybrid {p : ℝ} (hp : 0 ≤ p) (σ : ℝ)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoBase M₁ M₂ A ≤ sTwoSqHybrid p σ M₁ M₂ A := by
  rw [sTwoSqHybrid]
  have := norm_nonneg (NTrace (M₁ * A * gammaMatrix M₂) *
    NTrace (gammaMatrix M₁ * Aᴴ * M₂) / hybridDen σ M₁ M₂)
  nlinarith

/-- **`s₂(σ)² ≥ ⟨Γ₁AΓ₂A*⟩`** for every `σ ≥ 0` (in particular `σ = 0`),
with no hypothesis on the matrices. -/
theorem sTwoBase_le_sTwoAt_sq {σ : ℝ} (hσ : 0 ≤ σ) (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoBase M₁ M₂ A ≤ sTwoAt σ M₁ M₂ A ^ 2 := by
  rw [sTwoAt, Real.sq_sqrt' ]
  exact le_max_of_le_left (sTwoBase_le_sTwoSqHybrid hσ σ M₁ M₂ A)

/-- At `σ = 0` the time-dependent control is the base term (when it is nonnegative). -/
theorem sTwoSqHybrid_zero (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoSqHybrid 0 0 M₁ M₂ A = sTwoBase M₁ M₂ A := by
  simp [sTwoSqHybrid]

/-- **Monotonicity of the time-dependent control** `σ ↦ s₂(σ)²` on `[0, σ]` when `σ |⟨M₁M₂⟩| < 1`. -/
theorem sTwoSqHybrid_mono {σ σ' : ℝ} (h0 : 0 ≤ σ') (h1 : σ' ≤ σ)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) (h : σ * ‖NTrace (M₁ * M₂)‖ < 1) :
    sTwoSqHybrid σ' σ' M₁ M₂ A ≤ sTwoSqHybrid σ σ M₁ M₂ A := by
  have hσ : 0 ≤ σ := h0.trans h1
  have h' : σ' * ‖NTrace (M₁ * M₂)‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h
  have hd : 0 < ‖hybridDen σ M₁ M₂‖ := norm_one_sub_pos _ hσ h
  have hd' : 0 < ‖hybridDen σ' M₁ M₂‖ := norm_one_sub_pos _ h0 h'
  rw [sTwoSqHybrid_eq, sTwoSqHybrid_eq]
  have hnum : 0 ≤ sTwoNum M₁ M₂ A := norm_nonneg _
  have key := mul_norm_one_sub_le (NTrace (M₁ * M₂)) h0 h1 h.le
  have : σ' * sTwoNum M₁ M₂ A / ‖hybridDen σ' M₁ M₂‖ ≤
      σ * sTwoNum M₁ M₂ A / ‖hybridDen σ M₁ M₂‖ := by
    rw [div_le_div_iff₀ hd' hd]
    have : σ' * ‖hybridDen σ M₁ M₂‖ ≤ σ * ‖hybridDen σ' M₁ M₂‖ := key
    nlinarith
  linarith

/-- **Monotonicity of `s₂(σ)`** (time-dependent control). -/
theorem sTwoAt_mono {σ σ' : ℝ} (h0 : 0 ≤ σ') (h1 : σ' ≤ σ)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) (h : σ * ‖NTrace (M₁ * M₂)‖ < 1) :
    sTwoAt σ' M₁ M₂ A ≤ sTwoAt σ M₁ M₂ A :=
  Real.sqrt_le_sqrt (sTwoSqHybrid_mono h0 h1 M₁ M₂ A h)

/-- The time-dependent control is dominated by the CEH (5.27) control with target prefactor `s`. -/
theorem sTwoSqHybrid_le_prefactor {p q σ : ℝ} (hpq : p ≤ q)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) :
    sTwoSqHybrid p σ M₁ M₂ A ≤ sTwoSqHybrid q σ M₁ M₂ A := by
  rw [sTwoSqHybrid, sTwoSqHybrid]
  have := norm_nonneg (NTrace (M₁ * A * gammaMatrix M₂) *
    NTrace (gammaMatrix M₁ * Aᴴ * M₂) / hybridDen σ M₁ M₂)
  nlinarith

/-- **Quasi-monotonicity of CEH (5.27)** (CEH §7.1, "`s₂(s) ≲ s₂(t)` for `s ≤ t`"): with a
fixed prefactor `p ≥ 0`, for `0 ≤ σ' ≤ σ` and `σ |⟨M₁M₂⟩| < 1`,
`sTwoSqHybrid p σ' ≤ sTwoSqHybrid (2p) σ` (so `≤ 2 sTwoSqHybrid p σ` when the base is `≥ 0`). -/
theorem sTwoSqHybrid_le_two_mul {p σ σ' : ℝ} (hp : 0 ≤ p) (h0 : 0 ≤ σ') (h1 : σ' ≤ σ)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) (h : σ * ‖NTrace (M₁ * M₂)‖ < 1) :
    sTwoSqHybrid p σ' M₁ M₂ A ≤ sTwoSqHybrid (2 * p) σ M₁ M₂ A := by
  have hσ : 0 ≤ σ := h0.trans h1
  have h' : σ' * ‖NTrace (M₁ * M₂)‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h
  have hd : 0 < ‖hybridDen σ M₁ M₂‖ := norm_one_sub_pos _ hσ h
  have hd' : 0 < ‖hybridDen σ' M₁ M₂‖ := norm_one_sub_pos _ h0 h'
  rw [sTwoSqHybrid_eq, sTwoSqHybrid_eq]
  have hnum : 0 ≤ sTwoNum M₁ M₂ A := norm_nonneg _
  have key : ‖hybridDen σ M₁ M₂‖ ≤ 2 * ‖hybridDen σ' M₁ M₂‖ :=
    norm_one_sub_le_two_mul _ h0 h1 h.le
  have : p * sTwoNum M₁ M₂ A / ‖hybridDen σ' M₁ M₂‖ ≤
      2 * p * sTwoNum M₁ M₂ A / ‖hybridDen σ M₁ M₂‖ := by
    rw [div_le_div_iff₀ hd' hd]
    have hpn : 0 ≤ p * sTwoNum M₁ M₂ A := mul_nonneg hp hnum
    nlinarith
  linarith

end BlockBand.Native.CEH.ETH
