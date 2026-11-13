module

public import BlockBand.Native.CEH.ETH.ZigGlueAlg
public import BlockBand.Native.CEH.ETH.ZigHeightsGronwall

/-!
# CEH ETH: FTC for the deterministic approximations and drift bookkeeping

Setting: arbitrary matrices `M₁, A, M₂` and `T ≥ 0` with `1 - σ⟨M₁M₂⟩ ≠ 0` for all
`σ ∈ [0, T]` (`hden`); for MDE solutions at nonreal `zᵢ` in any adjoint constellation this
holds on `[0, s]` (`zgl_hybridDen_ne_zero_Icc`, from `hybridDen_ne_zero_mde`).
Notation: `μ_A(σ) = ⟨M^A_σ⟩ = ⟨twoResApprox σ M₁ A M₂⟩`, `a(σ) = μ_I(σ) = ⟨M^I_σ⟩`.

* `zgl_hasDerivAt_NTrace_twoResApprox`: `μ_A' = μ_A μ_I` at every `σ` with nonzero denominator
  (`B = 1` in `hasDerivAt_NTrace_twoResApprox_mul`, plus the symmetry of `μ_I`);
* `zgl_continuousOn_NTrace_twoResApprox`, `zgl_continuousOn_coeff`
  (`a = μ_I` is continuous on `[0, T]`; `a = ratCoeff ⟨M₁M₂⟩` there, `zgl_coeff_eq_ratCoeff`;
  its modulus bound in the `zigHeight` form of `norm_le_twoHeight_A/I`,
  `zgl_norm_coeff_le_twoHeight`),
  `zgl_continuousOn_deriv` (the derivative `μ_A μ_I` is continuous, so `μ_A` is `C¹`);
* `zgl_NTrace_twoResApprox_ftc`: `μ_A(t) = ⟨M₁AM₂⟩ + ∫₀ᵗ μ_A μ_I` for `t ∈ [0, T]`, and
  `zgl_NTrace_twoResApprox_one_ftc`: `μ_I(t) = ⟨M₁M₂⟩ + ∫₀ᵗ μ_I²`;
* drift bookkeeping (pointwise algebra, any matrices `R₁, R₂, A` and scalars):
  `zgl_drift_X_eq`: the drift with `B = 1` minus `μ_A μ_I` is
  `μ_I X + μ_A Y + X Y + W₁⟨R₁²AR₂⟩ + W₂⟨R₁AR₂²⟩` with `X = ⟨R₁AR₂⟩ - μ_A`,
  `Y = ⟨R₁R₂⟩ - μ_I`, `Wᵢ = ⟨Rᵢ⟩ - mᵢ`; `zgl_drift_Y_eq`: the `A = 1` drift minus `μ_I²` is
  `2μ_I Y + Y² + W₁⟨R₁²R₂⟩ + W₂⟨R₁R₂²⟩`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Internal.Contracts.Inputs (IsManuscriptMDE)

variable {N : ℕ}

/-!
## Value at `σ = 0` and the coefficient
-/

/-- `M^A_0 = M₁AM₂`. -/
theorem zgl_twoResApprox_zero (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    twoResApprox 0 M₁ A M₂ = M₁ * A * M₂ := by
  simp [twoResApprox]

/-- On the set where the denominator is nonzero, `a(σ) = ⟨M^I_σ⟩ = ratCoeff ⟨M₁M₂⟩ σ`. -/
theorem zgl_coeff_eq_ratCoeff {σ : ℝ} {M₁ M₂ : Matrix (Fin N) (Fin N) ℂ}
    (hden : hybridDen σ M₁ M₂ ≠ 0) :
    NTrace (twoResApprox σ M₁ 1 M₂) = ratCoeff (NTrace (M₁ * M₂)) σ := by
  rw [NTrace_twoResApprox_one σ M₁ M₂ hden, ratCoeff, hybridDen]

/-- For MDE solutions at nonreal `zᵢ`, in every constellation, the denominators do not vanish on
`[0, s]`. -/
theorem zgl_hybridDen_ne_zero_Icc {s : ℝ} {F₁ F₂ : BlockBand.External.CEH.SourceHermitian N}
    {z₁ z₂ : ℂ} {M₁ M₂ : BlockBand.External.CEH.SourceMatrix N}
    (h₁ : IsManuscriptMDE s F₁ z₁ M₁) (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0)
    (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s) (c₁ c₂ : AdjointChoice) :
    ∀ σ ∈ Icc (0 : ℝ) s, hybridDen σ (chooseAdjoint c₁ M₁) (chooseAdjoint c₂ M₂) ≠ 0 :=
  fun _ hσ => hybridDen_ne_zero_mde h₁ h₂ hz₁ hz₂ hs c₁ c₂ hσ.1 hσ.2

/-- **The Grönwall rate bound in `zigHeight` form** (the `hab` hypothesis of
`norm_le_twoHeight_A/I`): for MDE solutions at nonreal `zᵢ`, every constellation and
`u ∈ [0, s]`, `|a(u)| ≤ (c₁/η_{1,u} + c₂/η_{2,u})/2` with `cᵢ = |Im mᵢ|`,
`η_{i,u} = zigHeight |Im zᵢ| cᵢ s u` (`norm_NTrace_twoResApprox_one_le_mde`). -/
theorem zgl_norm_coeff_le_twoHeight {s : ℝ} {F₁ F₂ : BlockBand.External.CEH.SourceHermitian N}
    {z₁ z₂ : ℂ} {M₁ M₂ : BlockBand.External.CEH.SourceMatrix N}
    (h₁ : IsManuscriptMDE s F₁ z₁ M₁) (h₂ : IsManuscriptMDE s F₂ z₂ M₂) (hz₁ : z₁.im ≠ 0)
    (hz₂ : z₂.im ≠ 0) (hs : 0 ≤ s) (c₁ c₂ : AdjointChoice) :
    ∀ u ∈ Icc (0 : ℝ) s,
      ‖NTrace (twoResApprox u (chooseAdjoint c₁ M₁) 1 (chooseAdjoint c₂ M₂))‖ ≤
        (|(NTrace M₁).im| / BlockBand.Native.CEH.Zig.zigHeight |z₁.im| |(NTrace M₁).im| s u +
          |(NTrace M₂).im| / BlockBand.Native.CEH.Zig.zigHeight |z₂.im| |(NTrace M₂).im| s u) /
          2 := by
  intro u hu
  have h := norm_NTrace_twoResApprox_one_le_mde h₁ h₂ hz₁ hz₂ hs c₁ c₂ hu.1 hu.2
  simp only [BlockBand.Native.CEH.Zig.zigHeight, mul_comm |(NTrace M₁).im|,
    mul_comm |(NTrace M₂).im|]
  exact h

/-!
## Derivative, continuity, FTC
-/

section FTC

variable {M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ}

/-- `d/dσ ⟨M^A_σ⟩ = ⟨M^A_σ⟩ ⟨M^I_σ⟩` at every `σ` with nonzero denominator. -/
theorem zgl_hasDerivAt_NTrace_twoResApprox {σ : ℝ} (hden : hybridDen σ M₁ M₂ ≠ 0) :
    HasDerivAt (fun τ : ℝ => NTrace (twoResApprox τ M₁ A M₂))
      (NTrace (twoResApprox σ M₁ A M₂) * NTrace (twoResApprox σ M₁ 1 M₂)) σ := by
  have h := hasDerivAt_NTrace_twoResApprox_mul M₁ A M₂ 1 σ hden
  simp only [Matrix.mul_one] at h
  rwa [zgl_NTrace_twoResApprox_one_comm] at h

variable {T : ℝ} (hden : ∀ σ ∈ Icc (0 : ℝ) T, hybridDen σ M₁ M₂ ≠ 0)
include hden

/-- `σ ↦ ⟨M^A_σ⟩` is continuous on `[0, T]`. -/
theorem zgl_continuousOn_NTrace_twoResApprox (B : Matrix (Fin N) (Fin N) ℂ) :
    ContinuousOn (fun σ : ℝ => NTrace (twoResApprox σ M₁ B M₂)) (Icc 0 T) :=
  fun σ hσ => (zgl_hasDerivAt_NTrace_twoResApprox (A := B) (hden σ hσ)).continuousAt
    |>.continuousWithinAt

/-- **The Grönwall coefficient `a(σ) = ⟨M^I_σ⟩` is continuous on `[0, T]`.** -/
theorem zgl_continuousOn_coeff :
    ContinuousOn (fun σ : ℝ => NTrace (twoResApprox σ M₁ 1 M₂)) (Icc 0 T) :=
  zgl_continuousOn_NTrace_twoResApprox hden 1

/-- The derivative `⟨M^A_σ⟩⟨M^I_σ⟩` is continuous on `[0, T]` (`σ ↦ ⟨M^A_σ⟩` is `C¹`). -/
theorem zgl_continuousOn_deriv :
    ContinuousOn (fun σ : ℝ => NTrace (twoResApprox σ M₁ A M₂) *
      NTrace (twoResApprox σ M₁ 1 M₂)) (Icc 0 T) :=
  (zgl_continuousOn_NTrace_twoResApprox hden A).mul (zgl_continuousOn_coeff hden)

/-- **FTC for `⟨M^A_σ⟩`**: for `t ∈ [0, T]`,
`⟨M^A_t⟩ = ⟨M₁AM₂⟩ + ∫₀ᵗ ⟨M^A_u⟩⟨M^I_u⟩ du`. -/
theorem zgl_NTrace_twoResApprox_ftc : ∀ t ∈ Icc (0 : ℝ) T,
    NTrace (twoResApprox t M₁ A M₂) = NTrace (M₁ * A * M₂) +
      ∫ u in (0 : ℝ)..t, NTrace (twoResApprox u M₁ A M₂) * NTrace (twoResApprox u M₁ 1 M₂) := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := fun τ : ℝ => NTrace (twoResApprox τ M₁ A M₂))
    (fun x hx => zgl_hasDerivAt_NTrace_twoResApprox (hden x (hsub hx)))
    ((zgl_continuousOn_deriv hden).mono hsub).intervalIntegrable
  rw [hint, zgl_twoResApprox_zero]
  ring

/-- **FTC for `⟨M^I_σ⟩`**: for `t ∈ [0, T]`, `⟨M^I_t⟩ = ⟨M₁M₂⟩ + ∫₀ᵗ ⟨M^I_u⟩² du`. -/
theorem zgl_NTrace_twoResApprox_one_ftc : ∀ t ∈ Icc (0 : ℝ) T,
    NTrace (twoResApprox t M₁ 1 M₂) = NTrace (M₁ * M₂) +
      ∫ u in (0 : ℝ)..t, NTrace (twoResApprox u M₁ 1 M₂) * NTrace (twoResApprox u M₁ 1 M₂) := by
  intro t ht
  have h := zgl_NTrace_twoResApprox_ftc (A := 1) hden t ht
  rwa [Matrix.mul_one] at h

end FTC

/-!
## Drift bookkeeping (pointwise algebra)
-/

section Drift

open BlockBand.External.CEH (normalizedTrace)

/-- **The `X` drift minus `d⟨M^A⟩`.** For any matrices and scalars, the drift of
`⟨R₁AR₂·1⟩` (`isContinuousSemimartingale_avgRe2/avgIm2_flowResolvent` with `B = 1`) minus
`μ_A μ_I` equals `μ_I X + μ_A Y + XY + W₁⟨R₁²AR₂⟩ + W₂⟨R₁AR₂²⟩`, with `X = ⟨R₁AR₂⟩ - μ_A`,
`Y = ⟨R₁R₂⟩ - μ_I`, `Wᵢ = ⟨Rᵢ⟩ - mᵢ`. -/
theorem zgl_drift_X_eq (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ μA μI : ℂ) :
    (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * A * R₂ * 1) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * A * R₂ * R₂ * 1) +
        normalizedTrace (R₁ * A * R₂) * normalizedTrace (R₂ * 1 * R₁) - μA * μI =
      μI * (normalizedTrace (R₁ * A * R₂) - μA) + μA * (normalizedTrace (R₁ * R₂) - μI) +
        (normalizedTrace (R₁ * A * R₂) - μA) * (normalizedTrace (R₁ * R₂) - μI) +
        (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * A * R₂) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * A * R₂ * R₂) := by
  simp only [Matrix.mul_one]
  rw [Phase1.normalizedTrace_mul_comm R₂ R₁]
  ring

/-- **The `Y` drift minus `d⟨M^I⟩`.** The drift of `⟨R₁·1·R₂·1⟩` minus `μ_I²` equals
`2μ_I Y + Y² + W₁⟨R₁²R₂⟩ + W₂⟨R₁R₂²⟩`, `Y = ⟨R₁R₂⟩ - μ_I`, `Wᵢ = ⟨Rᵢ⟩ - mᵢ`. -/
theorem zgl_drift_Y_eq (R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ μI : ℂ) :
    (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * 1 * R₂ * 1) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * 1 * R₂ * R₂ * 1) +
        normalizedTrace (R₁ * 1 * R₂) * normalizedTrace (R₂ * 1 * R₁) - μI * μI =
      2 * μI * (normalizedTrace (R₁ * R₂) - μI) + (normalizedTrace (R₁ * R₂) - μI) ^ 2 +
        (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * R₂) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * R₂ * R₂) := by
  simp only [Matrix.mul_one]
  rw [Phase1.normalizedTrace_mul_comm R₂ R₁]
  ring

end Drift

end BlockBand.Native.CEH.ETH
