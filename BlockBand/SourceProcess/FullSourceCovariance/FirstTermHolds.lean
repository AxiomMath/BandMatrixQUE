module

public import BlockBand.SourceProcess.FullSourceCovariance.FirstTerm

/-!
# `FirstTermBound` holds

**`firstTermBound_holds hGA hLp : FirstTermBound`**. With `Ω₀ = Ω̄ + τ⁰`, `F = EF + F⁰` and
`Φ ∈ {Ψ, Ψ̄}` (`Ψ = x'*Δ⁰y'`), `first_split_bound` gives
`‖E[Ω₀FΦ]‖ ≤ ‖Ω̄‖‖F⁰‖₄‖Φ‖₂ + ‖EF‖‖E[τ⁰Φ]‖ + ‖τ⁰‖₄‖F⁰‖₄‖Φ‖₂`
`≤ C(δ₀+W⁻²)W⁻¹ + C(W⁻² + W⁻¹δ₀) + CW⁻²` times `‖x‖‖y‖‖x'‖‖y'‖` (`omegaBar_close`,
`rightForms_bulk`, `deltaFluctuation_all`, `tauCov_bulk`, `selfTau_fluct_bulk`,
`poly_eLpNorm_bulk`), which is `≤ C·covErr·∏‖v‖` since `δ₀ ≤ jetDist`. Radius `min(d₁, d₂)`.
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

/-- **The first-term node is proved** (bulk-uniform, strictly passive `X`). -/
theorem firstTermBound_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    FirstTermBound := by
  intro b hb0 hb κ hκ
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨d₁, CΩ, WΩ, hd₁, hCΩ, hΩ⟩ := omegaBar_close hA hb0 hb hκ
  obtain ⟨d₂, CT, WT, hd₂, hCT, hT⟩ := tauCov_bulk hGA hLp hb0 hb hκ
  obtain ⟨Cτ, Wτ, hCτ, hτ⟩ := selfTau_fluct_bulk hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨CF, WF, hCF, hF⟩ := rightForms_bulk hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨C1, W1, hC1, hp1⟩ := poly_eLpNorm_bulk hA hb0 hb hκ 1 le_rfl
  obtain ⟨CΨ, WΨ, hΨ⟩ := deltaFluctuation_all hGA hLp b hb0 hb κ hκ 2 one_le_two
  obtain ⟨CI, WI, -, hint⟩ := FullSource.delta_integrable hGA b hb0 hb κ hκ
  set CΨ' := max CΨ 0
  have hCΨ' : 0 ≤ CΨ' := le_max_right _ _
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, CΩ * CF * CΨ' + C1 * CT + Cτ * CF * CΨ',
    max (max (max WΩ WT) (max Wτ WF)) (max (max W1 WΨ) (max WI 1)),
    fun W hW E hE s hs X hY hd x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWΩ, hWT⟩, hWτ, hWF⟩, ⟨hW1', hWΨ⟩, hWI, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hs2 : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hWr0.le
  -- the jet distances
  have hg := conductance_nonneg b E hη.le hY.posSemidef
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδ1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hJ : jetDistance0 b E X ≤ jetDist b E s X := by
    unfold jetDist; have := div_nonneg hg hWr0.le; linarith
  have hd₁' : jetDistance0 b E X ≤ d₁ := hJ.trans (hd.trans (min_le_left _ _))
  have hd₂' : jetDistance0 b E X ≤ d₂ := hJ.trans (hd.trans (min_le_right _ _))
  set w := (W : ℝ)⁻¹
  have hw0 : 0 ≤ w := inv_nonneg.mpr hWr0.le
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
  have hcov : covErr b E s X = w ^ 2 + w * jetDist b E s X := rfl
  have hc1 : w ^ 2 + w * jetDistance0 b E X ≤ covErr b E s X := by
    rw [hcov]; nlinarith [mul_le_mul_of_nonneg_left hJ hw0]
  have hc2 : (jetDistance0 b E X + w ^ 2) * w ≤ covErr b E s X := by
    have : w ^ 3 ≤ w ^ 2 := pow_le_pow_of_le_one hw0 hw1 (by norm_num)
    nlinarith
  have hc3 : w ^ 2 ≤ covErr b E s X := by nlinarith [mul_nonneg hw0 hδ0]
  have nx := PassiveCovariance.vecNorm_nonneg x
  have ny := PassiveCovariance.vecNorm_nonneg y
  have nx' := PassiveCovariance.vecNorm_nonneg x'
  have ny' := PassiveCovariance.vecNorm_nonneg y'
  set n := vecNorm x * vecNorm y
  set n' := vecNorm x' * vecNorm y'
  have hn : 0 ≤ n := mul_nonneg nx ny
  have hn' : 0 ≤ n' := mul_nonneg nx' ny'
  have hN : fourNorm x y x' y' = n * n' := by simp only [fourNorm, n, n']; ring
  -- the factors
  set μ := freshLaw W b
  set mτ := ∫ ω', selfTau b (gRes b E X ω') ∂μ
  set τ0 := fun ω => selfTau b (gRes b E X ω) - mτ
  set mF := ∫ ω, fForm b E X x y ω ∂μ
  set F0 := fun ω => fForm b E X x y ω - mF
  set Ωb := (boundaryZ b E + E) + mτ
  set D₀ := matrixExpect μ (freshDelta b E X)
  set Ψ := fun ω => bilinear x' (freshDelta b E X ω - D₀) y'
  have hτ4 : eLpNorm τ0 4 μ ≤ ENNReal.ofReal (Cτ / W) := by
    have := hτ W hWτ E hE X hY.posSemidef; rwa [ENNReal.ofReal_ofNat] at this
  obtain ⟨hF4, -, -, -⟩ := hF W hWF E hE X hY.posSemidef x y
  rw [ENNReal.ofReal_ofNat] at hF4
  have hF4' : eLpNorm F0 4 μ ≤ ENNReal.ofReal (CF / Real.sqrt W * n) := by
    refine hF4.trans (le_of_eq ?_); congr 1; simp only [n]; ring
  have hΨ2 : eLpNorm Ψ 2 μ ≤ ENNReal.ofReal (CΨ' / Real.sqrt W * n') := by
    have := hΨ W hWΨ E hE X hY.posSemidef x' y'
    rw [ENNReal.ofReal_ofNat] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    calc CΨ / Real.sqrt W * vecNorm x' * vecNorm y' = CΨ / Real.sqrt W * n' := by ring
      _ ≤ CΨ' / Real.sqrt W * n' := by gcongr; exact le_max_left _ _
  have hτm : MemLp τ0 4 μ := lt_of_le_of_lt hτ4 ENNReal.ofReal_lt_top
  have hF0m : MemLp F0 4 μ := lt_of_le_of_lt hF4' ENNReal.ofReal_lt_top
  have hΨm : MemLp Ψ 2 μ := lt_of_le_of_lt hΨ2 ENNReal.ofReal_lt_top
  have hΨ0 : ∫ ω, Ψ ω ∂μ = 0 := by
    obtain ⟨hent, -⟩ := hint W hWI E hE X hY.posSemidef
    set k := bilinear x' D₀ y'
    have hBi : Integrable (fun ω => bilinear x' (freshDelta b E X ω) y') μ := by
      have e : (fun ω => bilinear x' (freshDelta b E X ω) y') = fun ω => Ψ ω + k := by
        funext ω; simp only [Ψ, k, PassiveCovariance.bilinear_sub]; ring
      rw [e]; exact (hΨm.integrable one_le_two).add (integrable_const _)
    have e : (fun ω => Ψ ω) = fun ω => bilinear x' (freshDelta b E X ω) y' -
        ∫ ω', bilinear x' (freshDelta b E X ω') y' ∂μ :=
      funext fun ω => PassiveLayer.bilinear_sub_matrixExpect _ hent x' y' ω
    rw [e, integral_sub hBi (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul, sub_self]
  -- the split, for `Φ ∈ {Ψ, Ψ̄}`
  have key : ∀ Φ : LayerSample W .oneBlockOnePort → ℂ, MemLp Φ 2 μ → ∫ ω, Φ ω ∂μ = 0 →
      eLpNorm Φ 2 μ ≤ ENNReal.ofReal (CΨ' / Real.sqrt W * n') →
      ‖∫ ω, τ0 ω * Φ ω ∂μ‖ ≤ CT * (w ^ 2 + w * jetDistance0 b E X) * n' →
      ‖∫ ω, omega0 b E X ω * fForm b E X x y ω * Φ ω ∂μ‖ ≤
        (CΩ * CF * CΨ' + C1 * CT + Cτ * CF * CΨ') * covErr b E s X * fourNorm x y x' y' := by
    intro Φ hΦm hΦ0 hΦ2 hΦT
    have e : ∫ ω, omega0 b E X ω * fForm b E X x y ω * Φ ω ∂μ =
        ∫ ω, (Ωb + τ0 ω) * (mF + F0 ω) * Φ ω ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [omega0, Ωb, τ0, F0]; ring
    rw [e]
    have hs := first_split_bound Ωb mF hτm hF0m hΦm hΦ0 (by positivity) (by positivity)
      (by positivity) hτ4 hF4' hΦ2 hΦT
    have hΩb : ‖Ωb‖ ≤ CΩ * (jetDistance0 b E X + w ^ 2) := hΩ W hWΩ E hE X hY hd₁'
    have hmF : ‖mF‖ ≤ n * C1 :=
      norm_integral_le_of (measurable_fForm b E X x y).aemeasurable (by positivity)
        (hp1 W hW1' E hE X hY.posSemidef _ (measurable_fForm b E X x y).aestronglyMeasurable n hn
          (norm_fForm_le b E X x y))
    have hAA : CF / Real.sqrt W * n * (CΨ' / Real.sqrt W * n') = CF * CΨ' * w * (n * n') := by
      have : CF / Real.sqrt W * n * (CΨ' / Real.sqrt W * n') =
          CF * CΨ' * (n * n') / (Real.sqrt W * Real.sqrt W) := by ring
      rw [this, hs2, div_eq_mul_inv]; ring
    have hτw : Cτ / W = Cτ * w := div_eq_mul_inv _ _
    rw [hAA, mul_assoc (Cτ / W), hAA, hτw] at hs
    rw [hN]
    calc _ ≤ ‖Ωb‖ * (CF * CΨ' * w * (n * n')) +
          ‖mF‖ * (CT * (w ^ 2 + w * jetDistance0 b E X) * n') +
          Cτ * w * (CF * CΨ' * w * (n * n')) := hs
      _ ≤ CΩ * (jetDistance0 b E X + w ^ 2) * (CF * CΨ' * w * (n * n')) +
          n * C1 * (CT * (w ^ 2 + w * jetDistance0 b E X) * n') +
          Cτ * w * (CF * CΨ' * w * (n * n')) := by gcongr
      _ = CΩ * CF * CΨ' * ((jetDistance0 b E X + w ^ 2) * w) * (n * n') +
          C1 * CT * (w ^ 2 + w * jetDistance0 b E X) * (n * n') +
          Cτ * CF * CΨ' * w ^ 2 * (n * n') := by ring
      _ ≤ CΩ * CF * CΨ' * covErr b E s X * (n * n') + C1 * CT * covErr b E s X * (n * n') +
          Cτ * CF * CΨ' * covErr b E s X * (n * n') := by gcongr
      _ = _ := by ring
  obtain ⟨hT1, hT2⟩ := hT W hWT E hE X hY hd₂' x' y'
  constructor
  · exact key Ψ hΨm hΨ0 hΨ2 hT1
  · have hs : eLpNorm (fun ω => star (Ψ ω)) 2 μ = eLpNorm Ψ 2 μ := eLpNorm_star (f := Ψ)
    have hσm : MemLp (fun ω => star (Ψ ω)) 2 μ := hΨm.star
    have hσ0 : ∫ ω, star (Ψ ω) ∂μ = 0 := by
      show ∫ ω, (starRingEnd ℂ) (Ψ ω) ∂μ = 0
      rw [integral_conj, hΨ0, map_zero]
    exact key (fun ω => star (Ψ ω)) hσm hσ0 (hs ▸ hΨ2) hT2

end BlockBand.SourceProcess.FullSourceCovariance
