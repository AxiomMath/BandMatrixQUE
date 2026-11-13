module

public import BlockBand.Transmission.PassiveCovariance.StationaryJet
public import BlockBand.Transmission.PassiveCovariance.Fluctuation

/-!
# Off-domain reduction for `PassiveCovarianceContract`

`passiveCovariance_of_domain`: `PassiveCovarianceContract` follows from
* `PassiveCovarianceOnDomain`, the bound on `{δ₀ + δ₁ + q/W ≤ d}` for some fixed `d > 0`
  (the analytic core), and
* `PassiveFluctuationL2`, the `L²` fluctuation bound of the passive bounds lemma (defined with the
  fluctuation bounds; it follows from `PassiveBoundsStatement` by
  `passiveFluctuationL2_of_passiveBounds`).
Off the domain, the crude covariance bound and the bound on the leading tensor suffice.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- **The near-domain bound** (the analytic core of the passive covariance lemma):
for some fixed scalar radius `d > 0`, the covariance equals the leading tensor up to
`C[W⁻² + W⁻¹(δ₀ + δ₁ + q/W)]∏‖v_j‖` whenever `δ₀ + δ₁ + q/W ≤ d`. -/
def PassiveCovarianceOnDomain : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

theorem fourNorm_nonneg {n : Type*} [Fintype n] (v₁ v₂ v₃ v₄ : n → ℂ) :
    0 ≤ fourNorm v₁ v₂ v₃ v₄ := by
  have := vecNorm_nonneg v₁; have := vecNorm_nonneg v₂; have := vecNorm_nonneg v₃
  have := vecNorm_nonneg v₄; rw [fourNorm]; positivity

/-- **Off-domain reduction**: the near-domain bound and the `L²`
fluctuation bound imply the domain-free `PassiveCovarianceContract`.
-/
theorem passiveCovariance_of_domain (hdom : PassiveCovarianceOnDomain)
    (hfl : PassiveFluctuationL2) : PassiveCovarianceContract := by
  intro b hb0 hb E h1 h2
  refine ⟨stationaryJet_exists hb0 hb h1 h2, fun s hs => ?_⟩
  obtain ⟨d, C, W₀, hd, hC⟩ := hdom b hb0 hb E h1 h2 s hs
  obtain ⟨C₁, W₁, hC₁, hcr⟩ := crudeCovariance_of_fluctuation hfl b hb0 hb E h1 h2
  have hm0 : 0 ≤ mainConst b E s := by
    have := etaZ_pos b E (by linarith) h1 h2
    rw [mainConst]; positivity
  set K := C₁ + mainConst b E s with hKdef
  refine ⟨max C 0 + K / d, max (max W₀ W₁) 1, fun W hW X hX v₁ v₂ v₃ v₄ => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWpos : (0 : ℝ) < W := by
    have : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact_mod_cast this
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W with hδ
  have hδ0 : 0 ≤ δ := by
    have := passiveMass_nonneg b E hX
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
  set F := fourNorm v₁ v₂ v₃ v₄
  have hB : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ := by positivity
  have hK0 : 0 ≤ K / d := by positivity
  show ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤ (max C 0 + K / d) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) * F
  by_cases hin : δ ≤ d
  · refine (hC W hW0 X hX hin v₁ v₂ v₃ v₄).trans ?_
    have : C ≤ max C 0 + K / d := le_trans (le_max_left _ _) (le_add_of_nonneg_right hK0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hB) hF
  · have hout : d < δ := lt_of_not_ge hin
    have h1' := hcr W hW1 X hX v₁ v₂ v₃ v₄
    have h2' := norm_mainTensor_le hb0 hb h1 h2 s hX v₁ v₂ v₃ v₄
    have htri : ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
        mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤ K / W * F := by
      refine (norm_sub_le _ _).trans ?_
      have : K / W * F = C₁ / W * F + mainConst b E s / W * F := by rw [hKdef]; ring
      linarith
    refine htri.trans ?_
    have hKd : K / W ≤ K / d * ((W : ℝ)⁻¹ * δ) := by
      have hK : 0 ≤ K := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hd, div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_left hout.le (mul_nonneg hK (inv_nonneg.mpr hWpos.le))
      linarith
    have hstep : K / d * ((W : ℝ)⁻¹ * δ) ≤ (max C 0 + K / d) * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ) := by
      have h3 : 0 ≤ (W : ℝ)⁻¹ * δ := by positivity
      have h4 : 0 ≤ (W : ℝ)⁻¹ ^ 2 := by positivity
      have h5 : 0 ≤ max C 0 := le_max_right _ _
      nlinarith
    exact mul_le_mul_of_nonneg_right (hKd.trans hstep) hF

end BlockBand.Transmission.PassiveCovariance
