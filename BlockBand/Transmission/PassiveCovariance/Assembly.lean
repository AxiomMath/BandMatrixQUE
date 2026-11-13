module

public import BlockBand.Transmission.PassiveCovariance.Continuity
public import BlockBand.Transmission.PassiveCovariance.PassiveBoundsBridge
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# Assembly of `PassiveCovarianceContract` from the normalized near-domain bound

**Hypotheses:** `GaussianAbsorptionContract` and `GaussianLpGradient` (through
`passiveBounds_holds`), and the analytic input `PassiveCovarianceNormalized`, stated as a
hypothesis: the near-domain bound for strictly passive `X` and vectors with `‖v₁‖ ≤ ρ`,
`‖v₂‖, ‖v₃‖, ‖v₄‖ ≤ 1` (the normalization of `cov_level0`).

* `bilinearCovariance_smul`, `mainTensor_smul`: both sides are multiplied by `r₁r₂r₃r₄` when
  `v_j ↦ r_jv_j` (`r_j` real).
* `strict_of_normalized`: `PassiveCovarianceNormalized → PassiveCovarianceOnDomainStrict`
  (constant `C/ρ`; the bound is homogeneous of degree one in each `‖v_j‖`).
* **`passiveCovariance_holds_of_normalized hGA hLp hN : PassiveCovarianceContract`**, through
  `passiveCovarianceOnDomain_of_strict`, `passiveCovariance_of_domain` and
  `passiveFluctuationL2_of_passiveBounds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- **The normalized near-domain bound**: as `PassiveCovarianceOnDomainStrict`, for
vectors with `‖v₁‖ ≤ ρ` and `‖v₂‖, ‖v₃‖, ‖v₄‖ ≤ 1`, with an absolute constant. -/
def PassiveCovarianceNormalized : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (ρ d C : ℝ) (W₀ : ℕ), 0 < ρ ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, vecNorm v₁ ≤ ρ → vecNorm v₂ ≤ 1 → vecNorm v₃ ≤ 1 →
        vecNorm v₄ ≤ 1 →
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W))

section Smul
variable {n : Type*} [Fintype n]

theorem bilinear_smul_left (r : ℝ) (u : n → ℂ) (M : Matrix n n ℂ) (v : n → ℂ) :
    bilinear ((r : ℂ) • u) M v = (r : ℂ) * bilinear u M v := by
  simp [bilinear, star_smul, smul_dotProduct]

theorem bilinear_smul_right (r : ℝ) (u : n → ℂ) (M : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u M ((r : ℂ) • v) = (r : ℂ) * bilinear u M v := by
  simp [bilinear, mulVec_smul, dotProduct_smul]

theorem crossedTensor_smul (r₁ r₂ r₃ r₄ : ℝ) (v₁ v₂ v₃ v₄ : n → ℂ) (A B : Matrix n n ℂ) :
    crossedTensor ((r₁ : ℂ) • v₁) ((r₂ : ℂ) • v₂) ((r₃ : ℂ) • v₃) ((r₄ : ℂ) • v₄) A B =
      ((r₁ * r₂ * r₃ * r₄ : ℝ) : ℂ) * crossedTensor v₁ v₂ v₃ v₄ A B := by
  simp only [crossedTensor, bilinear_smul_left, bilinear_smul_right]
  push_cast; ring

theorem bilinearCovariance_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → Matrix n n ℂ) (r₁ r₂ r₃ r₄ : ℝ) (v₁ v₂ v₃ v₄ : n → ℂ) :
    bilinearCovariance μ U ((r₁ : ℂ) • v₁) ((r₂ : ℂ) • v₂) ((r₃ : ℂ) • v₃) ((r₄ : ℂ) • v₄) =
      ((r₁ * r₂ * r₃ * r₄ : ℝ) : ℂ) * bilinearCovariance μ U v₁ v₂ v₃ v₄ := by
  unfold bilinearCovariance
  simp only [bilinear_smul_left, bilinear_smul_right]
  rw [← integral_const_mul]
  congr 1; funext ω; push_cast; ring

end Smul

theorem mainTensor_smul {W : ℕ} (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (r₁ r₂ r₃ r₄ : ℝ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    mainTensor b E s X ((r₁ : ℂ) • v₁) ((r₂ : ℂ) • v₂) ((r₃ : ℂ) • v₃) ((r₄ : ℂ) • v₄) =
      ((r₁ * r₂ * r₃ * r₄ : ℝ) : ℂ) * mainTensor b E s X v₁ v₂ v₃ v₄ := by
  simp only [mainTensor, crossedTensor_smul]
  ring

theorem vecNorm_smul_real {n : Type*} [Fintype n] (r : ℝ) (v : n → ℂ) :
    vecNorm ((r : ℂ) • v) = |r| * vecNorm v := by
  simp only [vecNorm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs]

theorem eq_zero_of_vecNorm {n : Type*} [Fintype n] {v : n → ℂ} (hv : vecNorm v = 0) : v = 0 := by
  funext i
  have h2 : ∑ i, ‖v i‖ ^ 2 = 0 := by
    rw [vecNorm, Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hv; exact hv
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).mp h2 i (Finset.mem_univ _)
  simpa using this

theorem cov_sub_main_zero {W : ℕ} (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin W → ℂ)
    (h : vecNorm v₁ = 0 ∨ vecNorm v₂ = 0 ∨ vecNorm v₃ = 0 ∨ vecNorm v₄ = 0) :
    bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      mainTensor b E s X v₁ v₂ v₃ v₄ = 0 := by
  rcases h with h | h | h | h <;> obtain rfl := eq_zero_of_vecNorm h <;>
    simp [bilinearCovariance, mainTensor, crossedTensor, bilinear]

theorem smul_inv_smul_real {n : Type*} (r : ℝ) (hr : r ≠ 0) (v : n → ℂ) :
    v = (r : ℂ) • ((r⁻¹ : ℝ) : ℂ) • v := by
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one, one_smul]

/-- **Homogeneity**: the normalized bound implies the strict near-domain bound. -/
theorem strict_of_normalized (hN : PassiveCovarianceNormalized) :
    PassiveCovarianceOnDomainStrict := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨ρ, d, C, W₀, hρ, hd, hC⟩ := hN b hb0 hb E h1 h2 s hs
  refine ⟨d, max C 0 / ρ, W₀, hd, fun W hW X hX hδ v₁ v₂ v₃ v₄ => ?_⟩
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W
  have hδ0 : 0 ≤ δ := by
    have := passiveMass_nonneg b E hX.posSemidef
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  set B := (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ
  have hB : 0 ≤ B := by positivity
  have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
  have hC0 : 0 ≤ max C 0 / ρ := by positivity
  by_cases h0 : vecNorm v₁ = 0 ∨ vecNorm v₂ = 0 ∨ vecNorm v₃ = 0 ∨ vecNorm v₄ = 0
  · rw [cov_sub_main_zero b E s X v₁ v₂ v₃ v₄ h0, norm_zero]; positivity
  push Not at h0
  obtain ⟨n1, n2, n3, n4⟩ := h0
  have p1 := lt_of_le_of_ne (vecNorm_nonneg v₁) (Ne.symm n1)
  have p2 := lt_of_le_of_ne (vecNorm_nonneg v₂) (Ne.symm n2)
  have p3 := lt_of_le_of_ne (vecNorm_nonneg v₃) (Ne.symm n3)
  have p4 := lt_of_le_of_ne (vecNorm_nonneg v₄) (Ne.symm n4)
  set r₁ := vecNorm v₁ / ρ
  have q1 : 0 < r₁ := div_pos p1 hρ
  set w₁ := ((r₁⁻¹ : ℝ) : ℂ) • v₁
  set w₂ := (((vecNorm v₂)⁻¹ : ℝ) : ℂ) • v₂
  set w₃ := (((vecNorm v₃)⁻¹ : ℝ) : ℂ) • v₃
  set w₄ := (((vecNorm v₄)⁻¹ : ℝ) : ℂ) • v₄
  have m1 : vecNorm w₁ ≤ ρ := by
    rw [vecNorm_smul_real, abs_of_pos (inv_pos.mpr q1)]
    simp only [r₁]; field_simp; rfl
  have mj : ∀ v : Fin W → ℂ, 0 < vecNorm v → vecNorm ((((vecNorm v)⁻¹ : ℝ) : ℂ) • v) ≤ 1 :=
    fun v hv => by rw [vecNorm_smul_real, abs_of_pos (inv_pos.mpr hv), inv_mul_cancel₀ hv.ne']
  have hw := hC W hW X hX hδ w₁ w₂ w₃ w₄ m1 (mj v₂ p2) (mj v₃ p3) (mj v₄ p4)
  have e : bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      mainTensor b E s X v₁ v₂ v₃ v₄ = ((r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ : ℝ) : ℂ) *
      (bilinearCovariance (freshLaw W b) (freshU b E X) w₁ w₂ w₃ w₄ -
        mainTensor b E s X w₁ w₂ w₃ w₄) := by
    conv_lhs => rw [smul_inv_smul_real r₁ q1.ne' v₁, smul_inv_smul_real _ p2.ne' v₂,
      smul_inv_smul_real _ p3.ne' v₃, smul_inv_smul_real _ p4.ne' v₄]
    rw [bilinearCovariance_smul, mainTensor_smul, mul_sub]
  have hr : 0 ≤ r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ := by positivity
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  calc r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ * ‖bilinearCovariance (freshLaw W b) (freshU b E X)
        w₁ w₂ w₃ w₄ - mainTensor b E s X w₁ w₂ w₃ w₄‖
      ≤ r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ * (max C 0 * B) :=
        mul_le_mul_of_nonneg_left (hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)) hr
    _ = max C 0 / ρ * B * fourNorm v₁ v₂ v₃ v₄ := by
        simp only [r₁, fourNorm]; field_simp

/-- **The contract from the normalized near-domain bound.** -/
theorem passiveCovariance_holds_of_normalized (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hN : PassiveCovarianceNormalized) : PassiveCovarianceContract := by
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  exact passiveCovariance_of_domain (passiveCovarianceOnDomain_of_strict hA (strict_of_normalized hN))
    (passiveFluctuationL2_of_passiveBounds hA)

end BlockBand.Transmission.PassiveCovariance
