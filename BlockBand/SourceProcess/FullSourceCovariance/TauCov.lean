module

public import BlockBand.SourceProcess.FullSourceCovariance.TauCrossed

/-!
# `E[τ⁰Ψ] = O(covErr)` by `delta_ibp` against a trace test

**`trace_test_bound hGA hLp`** (generic in the test): for every centred test `θ` with
`‖θ‖₄ ≤ C_τ/W`, a layer derivative with `Dθ(E_{βγ}) = -W⁻¹A(𝒢)_{γβ}`, `‖A(G)‖ ≤ ‖G‖²` and
polynomial bounds, `‖E[θΨ]‖ ≤ C(W⁻² + W⁻¹δ₀)‖x‖‖y‖`. Proof: `E[θΨ] = E[(x*Δy)θ]`, then
`delta_ibp` gives `E[Ω₀Fθ]` minus the crossed term; the latter is `O(W⁻²)`
(`crossed_trace_bound`), and `first_split_bound` with `Ω₀ = Ω̄ + τ⁰`, `F = EF + F⁰` gives
`‖Ω̄‖‖F⁰‖₄‖θ‖₄ + ‖EF‖‖τ⁰‖₄‖θ‖₄ + ‖τ⁰‖₄‖F⁰‖₄‖θ‖₄` with `‖Ω̄‖ ≤ C(δ₀+W⁻²)` (`omegaBar_close`),
`‖τ⁰‖₄ ≤ C/W` (`selfTau_fluct_bulk`), `‖F⁰‖₄ ≤ C` (`rightForms_bulk`), `‖EF‖ ≤ C`.

**`tauCov_bulk hGA hLp`**: the two cases `θ = τ⁰` (`A = 𝒢S̃𝒢`) and `θ = conj τ⁰`
(`A = (𝒢S̃𝒢)ᴴ`, `hasLayerDeriv_star`), giving `‖E[τ⁰Ψ]‖, ‖E[τ⁰Ψ̄]‖ ≤ C(W⁻² + W⁻¹δ₀)‖x‖‖y‖`,
for strictly passive `X` with `δ₀ ≤ d₁`, uniformly on `bulkInterval κ`.
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

/-- `‖x*K𝒢₁₁y‖ ≤ ‖x‖‖y‖(1 + B)`. -/
theorem norm_fForm_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖fForm b E X x y ω‖ ≤ (vecNorm x * vecNorm y) * (1 + btFun b E X ω) ^ 1 := by
  rw [pow_one, fForm]
  refine (norm_form_le _ _ _).trans ?_
  rw [vecNorm_physVec, vecNorm_physVec]
  exact mul_le_mul_of_nonneg_left (norm_kHat_gRes_le b E X ω)
    (mul_nonneg (PassiveCovariance.vecNorm_nonneg x) (PassiveCovariance.vecNorm_nonneg y))

theorem measurable_fForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    Measurable (fForm b E X x y) :=
  (continuous_const.dotProduct ((continuous_const.matrix_mul continuous_id).matrix_mulVec
    continuous_const)).measurable.comp (measurable_layerRes (W := W) E (boundaryZ b E) X)

/-- **Generic trace-test bound**: `‖E[θΨ]‖ ≤ C(W⁻² + W⁻¹δ₀)‖x‖‖y‖`. -/
theorem trace_test_bound (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₁ C Cτ : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ 0 ≤ Cτ ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      jetDistance0 b E X ≤ d₁ →
      eLpNorm (fun ω => selfTau b (gRes b E X ω) - ∫ ω', selfTau b (gRes b E X ω') ∂freshLaw W b)
          4 (freshLaw W b) ≤ ENNReal.ofReal (Cτ / W) ∧
      ∀ (θ : LayerSample W .oneBlockOnePort → ℂ)
        (Dθ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ)
        (A : LayerMat W → LayerMat W) (M : ℝ), 0 ≤ M →
        HasLayerDeriv θ Dθ → Measurable θ → (∀ N, Measurable fun ω => Dθ ω N) →
        (∀ ω, ‖θ ω‖ ≤ M * (1 + btFun b E X ω) ^ 1) →
        (∀ ω N, ‖Dθ ω N‖ ≤ (2 * ‖N‖) * (1 + btFun b E X ω) ^ 2) →
        Continuous A → (∀ G, ‖A G‖ ≤ ‖G‖ ^ 2) →
        (∀ ω β γ, Dθ ω (Matrix.single β γ 1) = -((W : ℂ)⁻¹ * A (gRes b E X ω) γ β)) →
        ∫ ω, θ ω ∂freshLaw W b = 0 → eLpNorm θ 4 (freshLaw W b) ≤ ENNReal.ofReal (Cτ / W) →
        ∀ x y : Fin W → ℂ,
          ‖∫ ω, θ ω * bilinear x (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) y ∂freshLaw W b‖ ≤
            C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) * (vecNorm x * vecNorm y) := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨d₁, CΩ, WΩ, hd₁, hCΩ, hΩ⟩ := omegaBar_close hA hb0 hb hκ
  obtain ⟨Cτ, Wτ, hCτ, hτ⟩ := selfTau_fluct_bulk hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨CF, WF, hCF, hF⟩ := rightForms_bulk hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨C1, W1, hC1, hp1⟩ := poly_eLpNorm_bulk hA hb0 hb hκ 1 le_rfl
  obtain ⟨Cr, Wr, hCr, hcr⟩ := crossed_trace_bound hA hb0 hb hκ
  obtain ⟨WI, hI⟩ := ibp_hyps_bulk hA hb0 hb hκ
  obtain ⟨CΨ, WΨ, hΨ⟩ := deltaFluctuation_all hGA hLp b hb0 hb κ hκ 2 one_le_two
  refine ⟨d₁, CΩ * CF * Cτ + C1 * Cτ ^ 2 + Cτ * CF * Cτ + Cr, Cτ,
    max (max (max WΩ Wτ) (max WF W1)) (max (max Wr WI) (max WΨ 1)), hd₁, by positivity, hCτ,
    fun W hW E hE X hY hδ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWΩ, hWτ⟩, hWF, hW1'⟩, ⟨hWr, hWI⟩, hWΨ, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hWge : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hsq : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hWge
  set μ := freshLaw W b
  set mτ := ∫ ω', selfTau b (gRes b E X ω') ∂μ
  set τ0 := fun ω => selfTau b (gRes b E X ω) - mτ
  have hτ4 : eLpNorm τ0 4 μ ≤ ENNReal.ofReal (Cτ / W) := by
    have := hτ W hWτ E hE X hY.posSemidef; rwa [ENNReal.ofReal_ofNat] at this
  refine ⟨hτ4, fun θ Dθ A M hM hD hθm hDm hθB hDB hAc hAn hDs hθ0 hθ4 x y => ?_⟩
  have nx := PassiveCovariance.vecNorm_nonneg x
  have ny := PassiveCovariance.vecNorm_nonneg y
  set n := vecNorm x * vecNorm y
  have hn : 0 ≤ n := mul_nonneg nx ny
  set w := (W : ℝ)⁻¹
  have hw0 : 0 ≤ w := inv_nonneg.mpr hWr0.le
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hWge
  have hCτw : Cτ / W = Cτ * w := div_eq_mul_inv _ _
  -- `Ψ` and `x*Δy`
  set D₀ := matrixExpect μ (freshDelta b E X)
  set Ψ := fun ω => bilinear x (freshDelta b E X ω - D₀) y
  have hΨ2 : eLpNorm Ψ 2 μ ≤ ENNReal.ofReal (CΨ / Real.sqrt W * vecNorm x * vecNorm y) := by
    have := hΨ W hWΨ E hE X hY.posSemidef x y; rwa [ENNReal.ofReal_ofNat] at this
  have hΨm : MemLp Ψ 2 μ := lt_of_le_of_lt hΨ2 ENNReal.ofReal_lt_top
  set k := bilinear x D₀ y
  have hBm : MemLp (fun ω => bilinear x (freshDelta b E X ω) y) 2 μ := by
    have h := hΨm.add (memLp_const k)
    have e : (Ψ + fun _ => k) = fun ω => bilinear x (freshDelta b E X ω) y := by
      funext ω; simp only [Pi.add_apply, Ψ, k, PassiveCovariance.bilinear_sub]; ring
    rwa [e] at h
  have hθ4m : MemLp θ 4 μ := lt_of_le_of_lt hθ4 ENNReal.ofReal_lt_top
  have hθ2 : MemLp θ 2 μ := hθ4m.mono_exponent (by norm_num)
  have e1 : ∫ ω, θ ω * Ψ ω ∂μ = ∫ ω, bilinear x (freshDelta b E X ω) y * θ ω ∂μ := by
    have e : ∀ ω, θ ω * Ψ ω = bilinear x (freshDelta b E X ω) y * θ ω - k * θ ω := fun ω => by
      simp only [Ψ, k, PassiveCovariance.bilinear_sub]; ring
    have i1 : Integrable (fun ω => bilinear x (freshDelta b E X ω) y * θ ω) μ :=
      hBm.integrable_mul hθ2
    rw [integral_congr_ae (Eventually.of_forall e), integral_sub i1
      ((hθ2.integrable one_le_two).const_mul k), integral_const_mul, hθ0, mul_zero, sub_zero]
  -- the integration by parts
  obtain ⟨hL2, hI1, hI2, hI3, hFi⟩ := hI W hWI E hE X hY (physVec x) (physVec y) M 2 hM
    (by norm_num) θ Dθ hθm hDm hθB hDB
  have hibp := delta_ibp hb h1 h2 hY hD hθm x y hL2 hI1 hI2 hI3 hFi
  change ‖∫ ω, θ ω * Ψ ω ∂μ‖ ≤ _
  rw [e1, hibp]
  simp only [hDs]
  -- the first term in split form
  set mF := ∫ ω, fForm b E X x y ω ∂μ
  set F0 := fun ω => fForm b E X x y ω - mF
  set Ωb := (boundaryZ b E + E) + mτ
  have e2 : ∫ ω, ((boundaryZ b E + E) + selfTau b (gRes b E X ω)) *
      (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) * θ ω ∂μ =
      ∫ ω, (Ωb + τ0 ω) * (mF + F0 ω) * θ ω ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Ωb, τ0, F0, fForm]; ring
  rw [e2]
  obtain ⟨hF4, -, -, -⟩ := hF W hWF E hE X hY.posSemidef x y
  rw [ENNReal.ofReal_ofNat] at hF4
  have hF4' : eLpNorm F0 4 μ ≤ ENNReal.ofReal (CF * n) := by
    refine hF4.trans (ENNReal.ofReal_le_ofReal ?_)
    have : CF / Real.sqrt W ≤ CF := div_le_self hCF hsq
    calc CF / Real.sqrt W * vecNorm x * vecNorm y = CF / Real.sqrt W * n := by ring
      _ ≤ CF * n := by gcongr
  have hF0m : MemLp F0 4 μ := lt_of_le_of_lt hF4' ENNReal.ofReal_lt_top
  have hτm : MemLp τ0 4 μ := lt_of_le_of_lt hτ4 ENNReal.ofReal_lt_top
  have hT : ‖∫ ω, τ0 ω * θ ω ∂μ‖ ≤ Cτ / W * (Cτ / W) :=
    norm_integral_mul_le_of hτm.aestronglyMeasurable.aemeasurable
      hθm.aemeasurable (by positivity) (by positivity) ((eLpNorm_two_le_four _).trans hτ4)
      ((eLpNorm_two_le_four _).trans hθ4)
  have hs := first_split_bound Ωb mF hτm hF0m hθ2 hθ0 (by positivity) (by positivity)
    (by positivity) hτ4 hF4' ((eLpNorm_two_le_four _).trans hθ4) hT
  -- the scalars
  have hΩb : ‖Ωb‖ ≤ CΩ * (jetDistance0 b E X + w ^ 2) := hΩ W hWΩ E hE X hY hδ
  have hmF : ‖mF‖ ≤ n * C1 :=
    norm_integral_le_of (measurable_fForm b E X x y).aemeasurable (by positivity)
      (hp1 W hW1' E hE X hY.posSemidef _ (measurable_fForm b E X x y).aestronglyMeasurable n hn
        (norm_fForm_le b E X x y))
  have hcr' := hcr W hWr E hE X hY.posSemidef A hAc hAn x y
  -- assembly
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  refine (norm_sub_le _ _).trans ?_
  rw [hCτw] at hs
  have hw3 : w ^ 3 ≤ w ^ 2 := pow_le_pow_of_le_one hw0 hw1 (by norm_num)
  calc _ ≤ ‖Ωb‖ * (CF * n * (Cτ * w)) + ‖mF‖ * (Cτ * w * (Cτ * w)) +
        Cτ * w * (CF * n) * (Cτ * w) + Cr * w ^ 2 * n := add_le_add hs hcr'
    _ ≤ CΩ * (jetDistance0 b E X + w ^ 2) * (CF * n * (Cτ * w)) +
        n * C1 * (Cτ * w * (Cτ * w)) + Cτ * w * (CF * n) * (Cτ * w) + Cr * w ^ 2 * n := by
        gcongr
    _ = CΩ * CF * Cτ * (w * jetDistance0 b E X + w ^ 3) * n +
        (C1 * Cτ ^ 2 + Cτ * CF * Cτ + Cr) * w ^ 2 * n := by ring
    _ ≤ CΩ * CF * Cτ * (w * jetDistance0 b E X + w ^ 2) * n +
        (C1 * Cτ ^ 2 + Cτ * CF * Cτ + Cr) * (w ^ 2 + w * jetDistance0 b E X) * n := by
        gcongr
        nlinarith [mul_nonneg hw0 hδ0, hw3]
    _ = (CΩ * CF * Cτ + C1 * Cτ ^ 2 + Cτ * CF * Cτ + Cr) * (w ^ 2 + w * jetDistance0 b E X) * n := by
        ring

end BlockBand.SourceProcess.FullSourceCovariance
