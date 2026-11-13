module

public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# One-layer bounds on `Δ` at every passive input, on and off the scalar domain

The scalar error has `L^p` size `C_p(ρ^j + W⁻¹)`, and Burkholder controls its centered
increments. The inputs are the one-port statements `deltaMean_holds` and `deltaFluctuation_holds`
and the crude moments `delta_moments`, `delta_integrable`. Off the scalar domain `δ₀(X) ≤ d₀` the
crude bounds are absorbed into `δ₀/d₀ ≥ 1`. For every passive `X`:
* `‖EΔ‖ ≤ C_m(δ₀(X) + W⁻¹)`;
* `‖u*(Δ - EΔ)v‖_{L^p} ≤ C_f(W^{-1/2} + δ₀(X))‖u‖‖v‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

/-- **The two one-layer bounds** at every passive input. -/
theorem delta_fresh_bounds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cm Cf : ℝ) (W₀ : ℕ), 0 ≤ Cm ∧ 0 ≤ Cf ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        (∀ x y, Integrable (fun ω => freshDelta b E X ω x y) (freshLaw W b)) ∧
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) ∧
        ∀ u v : Fin W → ℂ,
          eLpNorm (fun ω => bilinear u (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal p)
              (freshLaw W b) ≤
            ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u *
              vecNorm v) := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨dm, hdm, Cmean, W₁, hmean⟩ := deltaMean_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨Ci, W₂, hCi, hint⟩ := delta_integrable hGA b hb0 hb κ hκ
  obtain ⟨df, hdf, hfl⟩ := deltaFluctuation_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨Cfl, W₃, hfl'⟩ := hfl p hp
  obtain ⟨Cmo, W₄, hCmo, hmom⟩ := delta_moments hGA b hb0 hb κ hκ p hp
  refine ⟨max Cmean 0 + Ci / dm, max Cfl 0 + (Cmo + Ci) / df, max (max W₁ W₂) (max (max W₃ W₄) 1),
    by positivity, by positivity, fun W hW E hE X hY => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hW)
  have hW2 : W₂ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
  have hW3 : W₃ ≤ W :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW))
  have hW4 : W₄ ≤ W :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW))
  have hWone : 1 ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWone
  set δ := jetDistance0 b E X
  have hδ : 0 ≤ δ := norm_nonneg _
  obtain ⟨hI, hCiX⟩ := hint W hW2 E hE X hY
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  refine ⟨hI, ?_, fun u v => ?_⟩
  · have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    by_cases hd : δ ≤ dm
    · have h := hmean W hW1 E hE X hY hd
      have hsq : ((W : ℝ)⁻¹) ^ 2 ≤ (W : ℝ)⁻¹ := by
        rw [sq]; exact mul_le_of_le_one_left hWi (inv_le_one_of_one_le₀ hWr)
      calc ‖M‖ ≤ Cmean * (δ + ((W : ℝ)⁻¹) ^ 2) := h
        _ ≤ max Cmean 0 * (δ + (W : ℝ)⁻¹) :=
            mul_le_mul (le_max_left _ _) (by linarith) (by positivity) (le_max_right _ _)
        _ ≤ _ := by nlinarith [div_nonneg hCi hdm.le]
    · replace hd := not_le.mp hd
      have h1 : Ci ≤ Ci / dm * δ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hdm]; nlinarith
      calc ‖M‖ ≤ Ci := hCiX
        _ ≤ Ci / dm * δ := h1
        _ ≤ _ := by nlinarith [div_nonneg hCi hdm.le, le_max_right Cmean 0]
  · have hsW : 0 ≤ (Real.sqrt W)⁻¹ := by positivity
    have hu := vecNorm_nonneg u
    have hv := vecNorm_nonneg v
    by_cases hd : δ ≤ df
    · refine (hfl' W hW3 E hE X hY hd u v).trans (ENNReal.ofReal_le_ofReal ?_)
      have : Cfl / Real.sqrt W ≤ (max Cfl 0 + (Cmo + Ci) / df) * ((Real.sqrt W)⁻¹ + δ) := by
        rw [div_eq_mul_inv]
        have hc : 0 ≤ (Cmo + Ci) / df := by positivity
        nlinarith [le_max_left Cfl 0, le_max_right Cfl 0]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hu) hv
      linarith
    · replace hd := not_le.mp hd
      have hm : Measurable fun ω => freshDelta b E X ω :=
        measurable_freshDelta_comp b E (X := fun _ => X) measurable_const measurable_id
      have hbd : ∀ ω, ‖bilinear u (freshDelta b E X ω - M) v‖ ≤
          ‖(vecNorm u * vecNorm v) * (‖freshDelta b E X ω‖ + Ci)‖ := by
        intro ω
        refine (norm_bilinear_le u _ v).trans ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := norm_sub_le (freshDelta b E X ω) M
        nlinarith [mul_nonneg hu hv]
      have hg : MomBd (freshLaw W b) (fun ω => (vecNorm u * vecNorm v) *
          (‖freshDelta b E X ω‖ + Ci)) p ((vecNorm u * vecNorm v) * (Cmo + |Ci|)) :=
        ((hmom W hW4 E hE X hY).add hp (MomBd.const (μ := freshLaw W b) Ci p (by linarith))
          hCmo (abs_nonneg _)).const_mul (mul_nonneg hu hv)
      have hbm : AEStronglyMeasurable (fun ω => bilinear u (freshDelta b E X ω - M) v)
          (freshLaw W b) :=
        (measurable_bilinear_comp (hm.sub measurable_const) u v).aestronglyMeasurable
      refine (eLpNorm_mono hbm (fun ω => hbd ω)).trans (hg.2.trans (ENNReal.ofReal_le_ofReal ?_))
      rw [abs_of_nonneg hCi]
      have h1 : Cmo + Ci ≤ (Cmo + Ci) / df * δ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hdf]; nlinarith
      have h2 : (Cmo + Ci) / df * δ ≤ (max Cfl 0 + (Cmo + Ci) / df) * ((Real.sqrt W)⁻¹ + δ) := by
        have hc : 0 ≤ (Cmo + Ci) / df := by positivity
        nlinarith [le_max_right Cfl 0]
      have := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hu hv)
      nlinarith

end BlockBand.SourceProcess.RawTag
