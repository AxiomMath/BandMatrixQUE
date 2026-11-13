module

public import BlockBand.SourceProcess.FullSourceCovariance.TauCov

/-!
# `E[θΨ]` for a general centred test, with the crossed term as a hypothesis

`trace_test_bound` with the crossed term of
`delta_ibp` and the integrability hypotheses left to the caller (strictly passive `X`,
`E ∈ bulkInterval κ`, `δ₀ ≤ d₁`, `W ≥ W₀`; constants uniform). Notation: `Ψ = x*Δ⁰y`,
`F = x*K𝒢₁₁y`, `Ω̄ = (z+E) + Eτ`, `w = W⁻¹`.

**`test_bound hGA hLp`**: for every centred test `θ` with a layer derivative, the hypotheses of
`delta_ibp`, `‖θ‖₄ ≤ A_θ` and crossed term `≤ A_cr`,
`‖E[θΨ]‖ ≤ C₀·A_θ·(δ₀ + w)·‖x‖‖y‖ + A_cr`. Proof: `delta_ibp`, then `first_split_bound`
with `‖Ω̄‖ ≤ C(δ₀ + w²)`, `‖τ⁰‖₄ ≤ Cw`, `‖F⁰‖₄ ≤ C‖x‖‖y‖`, `‖EF‖ ≤ C‖x‖‖y‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The general centred-test bound.** -/
theorem test_bound (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₁ C₀ : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C₀ ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      jetDistance0 b E X ≤ d₁ →
      ∀ (θ : LayerSample W .oneBlockOnePort → ℂ)
        (Dθ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ),
        HasLayerDeriv θ Dθ → Measurable θ → ∀ x y : Fin W → ℂ,
        (∀ α γ, MemLp (fun ω => gRes b E X ω α γ * θ ω) 2 (freshLaw W b)) →
        (∀ α γ N, Integrable (fun ω => gRes b E X ω α γ * Dθ ω N) (freshLaw W b)) →
        (∀ α γ N, Integrable (fun ω => θ ω * (gRes b E X ω * N * gRes b E X ω) α γ)
          (freshLaw W b)) →
        (∀ α β γ, Integrable (fun ω => θ ω * (gRes b E X ω γ γ * gRes b E X ω α β))
          (freshLaw W b)) →
        Integrable (fun ω => (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) *
          θ ω) (freshLaw W b) →
        ∫ ω, θ ω ∂freshLaw W b = 0 → ∀ Aθ : ℝ, 0 ≤ Aθ →
        eLpNorm θ 4 (freshLaw W b) ≤ ENNReal.ofReal Aθ → ∀ Acr : ℝ,
        ‖∑ β, ∑ γ, physVec y β * siteVar W b β γ *
          ∫ ω, (star (physVec x) ᵥ* (kHat b E X * gRes b E X ω)) γ * Dθ ω (Matrix.single β γ 1)
            ∂freshLaw W b‖ ≤ Acr →
          ‖∫ ω, θ ω * bilinear x (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) y ∂freshLaw W b‖ ≤
            C₀ * Aθ * (jetDistance0 b E X + (W : ℝ)⁻¹) * (vecNorm x * vecNorm y) + Acr := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨d₁, CΩ, WΩ, hd₁, hCΩ, hΩ⟩ := omegaBar_close hA hb0 hb hκ
  obtain ⟨Cτ, Wτ, hCτ, hτ⟩ := selfTau_fluct_bulk hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨CF, WF, hCF, hF⟩ := rightForms_bulk hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨C1, W1, hC1, hp1⟩ := poly_eLpNorm_bulk hA hb0 hb hκ 1 le_rfl
  obtain ⟨CΨ, WΨ, hΨ⟩ := deltaFluctuation_all hGA hLp b hb0 hb κ hκ 2 one_le_two
  refine ⟨d₁, CΩ * CF + C1 * Cτ + Cτ * CF,
    max (max (max WΩ Wτ) (max WF W1)) (max WΨ 1), hd₁, by positivity,
    fun W hW E hE X hY hδ θ Dθ hD hθm x y hL2 hI1 hI2 hI3 hFi hθ0 Aθ hAθ hθ4 Acr hcr => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWΩ, hWτ⟩, hWF, hW1'⟩, hWΨ, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hWge : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hsq : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hWge
  set mτ := ∫ ω', selfTau b (gRes b E X ω') ∂freshLaw W b
  set τ0 := fun ω => selfTau b (gRes b E X ω) - mτ
  have hτ4 : eLpNorm τ0 4 (freshLaw W b) ≤ ENNReal.ofReal (Cτ / W) := by
    have := hτ W hWτ E hE X hY.posSemidef; rwa [ENNReal.ofReal_ofNat] at this
  have nx := PassiveCovariance.vecNorm_nonneg x
  have ny := PassiveCovariance.vecNorm_nonneg y
  set n := vecNorm x * vecNorm y
  have hn : 0 ≤ n := mul_nonneg nx ny
  set w := (W : ℝ)⁻¹
  have hw0 : 0 ≤ w := inv_nonneg.mpr hWr0.le
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hWge
  have hCτw : Cτ / W = Cτ * w := div_eq_mul_inv _ _
  -- `Ψ` and `x*Δy`
  set D₀ := matrixExpect (freshLaw W b) (freshDelta b E X)
  set Ψ := fun ω => bilinear x (freshDelta b E X ω - D₀) y
  have hΨ2 : eLpNorm Ψ 2 (freshLaw W b) ≤
      ENNReal.ofReal (CΨ / Real.sqrt W * vecNorm x * vecNorm y) := by
    have := hΨ W hWΨ E hE X hY.posSemidef x y; rwa [ENNReal.ofReal_ofNat] at this
  have hΨm : MemLp Ψ 2 (freshLaw W b) := lt_of_le_of_lt hΨ2 ENNReal.ofReal_lt_top
  set k := bilinear x D₀ y
  have hBm : MemLp (fun ω => bilinear x (freshDelta b E X ω) y) 2 (freshLaw W b) := by
    have h := hΨm.add (memLp_const k)
    have e : (Ψ + fun _ => k) = fun ω => bilinear x (freshDelta b E X ω) y := by
      funext ω; simp only [Pi.add_apply, Ψ, k, PassiveCovariance.bilinear_sub]; ring
    rwa [e] at h
  have hθ4m : MemLp θ 4 (freshLaw W b) := lt_of_le_of_lt hθ4 ENNReal.ofReal_lt_top
  have hθ2 : MemLp θ 2 (freshLaw W b) := hθ4m.mono_exponent (by norm_num)
  have e1 : ∫ ω, θ ω * Ψ ω ∂freshLaw W b =
      ∫ ω, bilinear x (freshDelta b E X ω) y * θ ω ∂freshLaw W b := by
    have e : ∀ ω, θ ω * Ψ ω = bilinear x (freshDelta b E X ω) y * θ ω - k * θ ω := fun ω => by
      simp only [Ψ, k, PassiveCovariance.bilinear_sub]; ring
    have i1 : Integrable (fun ω => bilinear x (freshDelta b E X ω) y * θ ω) (freshLaw W b) :=
      hBm.integrable_mul hθ2
    rw [integral_congr_ae (Eventually.of_forall e), integral_sub i1
      ((hθ2.integrable one_le_two).const_mul k), integral_const_mul, hθ0, mul_zero, sub_zero]
  -- the integration by parts
  have hibp := delta_ibp hb h1 h2 hY hD hθm x y hL2 hI1 hI2 hI3 hFi
  change ‖∫ ω, θ ω * Ψ ω ∂freshLaw W b‖ ≤ _
  rw [e1, hibp]
  -- the first term in split form
  set mF := ∫ ω, fForm b E X x y ω ∂freshLaw W b
  set F0 := fun ω => fForm b E X x y ω - mF
  set Ωb := (boundaryZ b E + E) + mτ
  have e2 : ∫ ω, ((boundaryZ b E + E) + selfTau b (gRes b E X ω)) *
      (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) * θ ω ∂freshLaw W b =
      ∫ ω, (Ωb + τ0 ω) * (mF + F0 ω) * θ ω ∂freshLaw W b := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Ωb, τ0, F0, fForm]; ring
  rw [e2]
  obtain ⟨hF4, -, -, -⟩ := hF W hWF E hE X hY.posSemidef x y
  rw [ENNReal.ofReal_ofNat] at hF4
  have hF4' : eLpNorm F0 4 (freshLaw W b) ≤ ENNReal.ofReal (CF * n) := by
    refine hF4.trans (ENNReal.ofReal_le_ofReal ?_)
    have : CF / Real.sqrt W ≤ CF := div_le_self hCF hsq
    calc CF / Real.sqrt W * vecNorm x * vecNorm y = CF / Real.sqrt W * n := by ring
      _ ≤ CF * n := by gcongr
  have hF0m : MemLp F0 4 (freshLaw W b) := lt_of_le_of_lt hF4' ENNReal.ofReal_lt_top
  have hτm : MemLp τ0 4 (freshLaw W b) := lt_of_le_of_lt hτ4 ENNReal.ofReal_lt_top
  have hT : ‖∫ ω, τ0 ω * θ ω ∂freshLaw W b‖ ≤ Cτ / W * Aθ :=
    norm_integral_mul_le_of hτm.aestronglyMeasurable.aemeasurable
      hθm.aemeasurable (by positivity) hAθ ((eLpNorm_two_le_four _).trans hτ4)
      ((eLpNorm_two_le_four _).trans hθ4)
  have hs := first_split_bound Ωb mF hτm hF0m hθ2 hθ0 (by positivity) (by positivity)
    hAθ hτ4 hF4' ((eLpNorm_two_le_four _).trans hθ4) hT
  -- the scalars
  have hΩb : ‖Ωb‖ ≤ CΩ * (jetDistance0 b E X + w ^ 2) := hΩ W hWΩ E hE X hY hδ
  have hmF : ‖mF‖ ≤ n * C1 :=
    norm_integral_le_of (measurable_fForm b E X x y).aemeasurable (by positivity)
      (hp1 W hW1' E hE X hY.posSemidef _ (measurable_fForm b E X x y).aestronglyMeasurable n hn
        (norm_fForm_le b E X x y))
  -- assembly
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  refine (norm_sub_le _ _).trans (add_le_add ?_ hcr)
  rw [hCτw] at hs
  have hw2 : w ^ 2 ≤ w := by nlinarith
  calc _ ≤ ‖Ωb‖ * (CF * n * Aθ) + ‖mF‖ * (Cτ * w * Aθ) + Cτ * w * (CF * n) * Aθ := hs
    _ ≤ CΩ * (jetDistance0 b E X + w ^ 2) * (CF * n * Aθ) + n * C1 * (Cτ * w * Aθ) +
        Cτ * w * (CF * n) * Aθ := by gcongr
    _ ≤ CΩ * (jetDistance0 b E X + w) * (CF * n * Aθ) + n * C1 * (Cτ * (jetDistance0 b E X + w)
          * Aθ) + Cτ * (jetDistance0 b E X + w) * (CF * n) * Aθ := by gcongr <;> linarith
    _ = (CΩ * CF + C1 * Cτ + Cτ * CF) * Aθ * (jetDistance0 b E X + w) * n := by ring

end BlockBand.SourceProcess.FullSourceCovariance
