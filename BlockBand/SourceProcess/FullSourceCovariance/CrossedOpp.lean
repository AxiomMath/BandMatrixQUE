module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiOpp
public import BlockBand.SourceProcess.FullSource.DeltaMeanStrict

/-!
# The opposite-sign crossed product from the mean of `Φ'`

* `PhiOppMean`: `|W·EΦ'(x,x') - σ₊·x*x'| ≤ C(δ₀+δ₁+g/W + W⁻¹)‖x‖‖x'‖` near the jet,
  `Y ≻ 0`, bulk-uniform. (`W·Φ' = a*K̂𝒢 S̃ (K̂𝒢)ᴴ a'`, `S̃ = diag(c, b)`; its leading value is the
  2×2 trace system with determinant `b`, as in `freshU_mean_bulk` with `P₂` replaced by `S̃`.)
* **`crossedOppBound_of_mean hGA hLp hP hM : CrossedOppBound`**. With `P = Φ'`, `H = y*𝒢₁₁Ky'`:
  `E[PH̄] - (σ₊/W)(x*x')(y'*y) = E[P⁰H̄⁰] + EP·(conj EH - y'*y) + (EP - σ₊/W·x*x')(y'*y)`, and
  - `|E[P⁰H̄⁰]| ≤ ‖P⁰‖₂‖H⁰‖₂ ≤ (C/W^{3/2})(C/W^{1/2})` (`phiOpp_l2_bulk`, `rightForms_bulk`);
  - `|EH - y*y'| = |(Rᴴy)*EΔy'| ≤ η⁻¹C(δ₀ + W⁻²)` (`rightForms_bulk`, `deltaMean_strict`);
  - `|EP| ≤ (σ₊ + C(d+1))/W` and the last term are `PhiOppMean`.
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

/-- **The mean of `Φ'`** (opposite-sign ladder, determinant `b`). -/
def PhiOppMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x x' : Fin W → ℂ,
        ‖(W : ℂ) * (∫ ω, phiOpp b E X x x' ω ∂freshLaw W b) -
            ((sigmaPlus b : ℝ) : ℂ) * bilinear x 1 x'‖ ≤
          C * (jetDist b E s X + (W : ℝ)⁻¹) * (vecNorm x * vecNorm x')

theorem measurable_hForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y y' : Fin W → ℂ) :
    Measurable (hForm b E X y y') :=
  (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).measurable.comp
    (measurable_layerRes (W := W) E (boundaryZ b E) X)

/-- `E[PH̄] = EP·conj EH + E[P⁰ conj H⁰]` for `P, H ∈ L²`. -/
theorem integral_mul_star_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P H : Ω → ℂ} (hP : MemLp P 2 μ) (hH : MemLp H 2 μ) :
    ∫ ω, P ω * star (H ω) ∂μ = (∫ ω, P ω ∂μ) * star (∫ ω, H ω ∂μ) +
      ∫ ω, (P ω - ∫ ω', P ω' ∂μ) * star (H ω - ∫ ω', H ω' ∂μ) ∂μ := by
  set mP := ∫ ω, P ω ∂μ
  set mH := ∫ ω, H ω ∂μ
  have hPi := hP.integrable one_le_two
  have hHi := hH.integrable one_le_two
  have hPH : Integrable (fun ω => P ω * star (H ω)) μ := hP.integrable_mul hH.star
  have e : (fun ω => (P ω - mP) * star (H ω - mH)) =
      fun ω => P ω * star (H ω) - star mH * P ω - mP * star (H ω) + mP * star mH := by
    funext ω; rw [star_sub]; ring
  have hsH : ∫ ω, star (H ω) ∂μ = star mH := integral_conj
  have hsHi := integrable_star_fun hHi
  have i1 : Integrable (fun ω => P ω * star (H ω) - star mH * P ω) μ := hPH.sub (hPi.const_mul _)
  have i2 : Integrable (fun ω => P ω * star (H ω) - star mH * P ω - mP * star (H ω)) μ :=
    i1.sub (hsHi.const_mul _)
  rw [e, integral_add i2 (integrable_const _), integral_sub i1 (hsHi.const_mul _),
    integral_sub hPH (hPi.const_mul _), integral_const_mul, integral_const_mul, hsH,
    integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- **The opposite-sign crossed product** from `PhiOppMean` and input hypotheses. -/
theorem crossedOppBound_of_mean (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hM : PhiOppMean) : CrossedOppBound := by
  intro b hb0 hb κ hκ
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨dM, hdM, CM, WM, hMb⟩ := hM b hb0 hb κ hκ
  obtain ⟨d₁, CΔ, WΔ, hd₁, hCΔ, hΔ⟩ := FullSource.deltaMean_strict hA hb0 hb hκ
  obtain ⟨Cv, Wv, hCv, hv⟩ := phiOpp_l2_bulk hP hA hb0 hb hκ
  obtain ⟨Ch, Wh, hCh, hh⟩ := rightForms_bulk hGA hLp hb0 hb hκ 2 one_le_two
  have hσ0 : 0 ≤ sigmaPlus b := by
    rw [sigmaPlus, kPlus]; exact div_nonneg (by nlinarith) hb0.le
  have hηL := PathScalar.etaLow_pos (b := b) (by linarith) hκ
  set CM' := max CM 0
  set ηi := (PathScalar.etaLow b κ)⁻¹
  set Cσ := sigmaPlus b + CM' * (dM + 1)
  refine ⟨min dM d₁, lt_min hdM hd₁, Cv * Ch + Cσ * ηi * CΔ + CM',
    max (max WM WΔ) (max (max Wv Wh) 1), fun W hW E hE s hs X hY hd x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWM, hWΔ⟩, ⟨hWv, hWh⟩, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hWi : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
  have hWi0 : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hWr.le
  -- the jet distance
  have hg := conductance_nonneg b E hη.le hY.posSemidef
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδ1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hJ : jetDistance0 b E X ≤ jetDist b E s X := by
    unfold jetDist; have := div_nonneg hg hWr.le; linarith
  have hJ0 : 0 ≤ jetDist b E s X := hδ0.trans hJ
  have hdM' : jetDist b E s X ≤ dM := hd.trans (min_le_left _ _)
  have hd₁' : jetDistance0 b E X ≤ d₁ := hJ.trans (hd.trans (min_le_right _ _))
  have hcov : covErr b E s X = (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDist b E s X := rfl
  set ε := covErr b E s X
  have hcA : (W : ℝ)⁻¹ ^ 2 ≤ ε := by rw [hcov]; nlinarith
  have hcB : (W : ℝ)⁻¹ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ≤ ε := by
    rw [hcov]; nlinarith [mul_le_mul_of_nonneg_left hJ hWi0]
  have hcC : (W : ℝ)⁻¹ * (jetDist b E s X + (W : ℝ)⁻¹) = ε := by rw [hcov]; ring
  -- the two factors
  set μ := freshLaw W b
  set Pf := phiOpp b E X x x'
  set H := hForm b E X y y'
  set mP := ∫ ω, Pf ω ∂μ
  set mH := ∫ ω, H ω ∂μ
  obtain ⟨hPm, hP0⟩ := hv W hWv E hE X hY x x'
  obtain ⟨-, hH0, -, hmH⟩ := hh W hWh E hE X hY.posSemidef y y'
  rw [ENNReal.ofReal_ofNat] at hH0
  have hlt : eLpNorm (fun ω => H ω - mH) 2 μ < ∞ := lt_of_le_of_lt hH0 ENNReal.ofReal_lt_top
  have hH0m : MemLp (fun ω => H ω - mH) 2 μ := hlt
  have hHm : MemLp H 2 μ := by
    have h := hH0m.add (memLp_const mH)
    have e : ((fun ω => H ω - mH) + fun _ => mH) = H := by funext ω; simp
    rw [e] at h; exact h
  rw [integral_mul_star_eq hPm hHm]
  set A := ∫ ω, (Pf ω - mP) * star (H ω - mH) ∂μ
  set bx := bilinear x 1 x'
  set byy := bilinear y' 1 y
  have hsplit : mP * star mH + A - ((sigmaPlus b : ℝ) : ℂ) / W * (bx * byy) =
      A + mP * (star mH - byy) + (mP - ((sigmaPlus b : ℝ) : ℂ) / W * bx) * byy := by ring
  rw [hsplit]
  -- norms of the vectors
  have nx0 := PassiveCovariance.vecNorm_nonneg x; have nx0' := PassiveCovariance.vecNorm_nonneg x'
  have ny0 := PassiveCovariance.vecNorm_nonneg y; have ny0' := PassiveCovariance.vecNorm_nonneg y'
  set nx := vecNorm x * vecNorm x'
  set ny := vecNorm y * vecNorm y'
  have hN : fourNorm x y x' y' = nx * ny := by simp only [fourNorm, nx, ny]; ring
  have hbx : ‖bx‖ ≤ nx := by
    refine (PassiveCovariance.norm_bilinear_le x 1 x').trans ?_
    have := norm_one_matrix_le (n := Fin W)
    calc vecNorm x * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm x' ≤ vecNorm x * 1 * vecNorm x' := by
          gcongr
      _ = nx := by ring
  have hby : ‖byy‖ ≤ ny := by
    refine (PassiveCovariance.norm_bilinear_le y' 1 y).trans ?_
    have := norm_one_matrix_le (n := Fin W)
    calc vecNorm y' * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm y ≤ vecNorm y' * 1 * vecNorm y := by
          gcongr
      _ = ny := by ring
  -- (1) the centred product
  have hA1 : ‖A‖ ≤ Cv * Ch * (W : ℝ)⁻¹ ^ 2 * (nx * ny) := by
    have hcs := enorm_integral_mul_le μ (fun ω => Pf ω - mP) (fun ω => star (H ω - mH))
      (hPm.sub (memLp_const _)).aestronglyMeasurable.aemeasurable
      (continuous_star.measurable.comp ((measurable_hForm b E X y y').sub
        measurable_const)).aemeasurable
    have hs : eLpNorm (fun ω => star (H ω - mH)) 2 μ = eLpNorm (fun ω => H ω - mH) 2 μ :=
      eLpNorm_star (f := fun ω => H ω - mH)
    rw [hs] at hcs
    have hb := hcs.trans (mul_le_mul' hP0 hH0)
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm] at hb
    refine ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb).trans (le_of_eq ?_)
    have hs2 : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hWr.le
    have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWr
    field_simp
    rw [Real.sq_sqrt hWr.le]
    simp only [nx, ny]; ring
  -- (2) the right letter mean
  have hH2 : ‖star mH - byy‖ ≤ ηi * (CΔ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * ny := by
    have e : star mH - byy =
        star (bilinear ((passiveResolvent b E X)ᴴ *ᵥ y) (matrixExpect μ (freshDelta b E X)) y') := by
      have hmH' : mH = bilinear y 1 y' + bilinear ((passiveResolvent b E X)ᴴ *ᵥ y)
          (matrixExpect μ (freshDelta b E X)) y' := hmH
      rw [hmH', star_add]
      have : star (bilinear y 1 y') = byy := by
        rw [← FullSource.bilinear_conjTranspose, conjTranspose_one]
      rw [this]; ring
    rw [e, norm_star]
    refine (PassiveCovariance.norm_bilinear_le _ _ _).trans ?_
    have hRy : vecNorm ((passiveResolvent b E X)ᴴ *ᵥ y) ≤ ηi * vecNorm y := by
      refine (vecNorm_mulVec_le' _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right ((norm_passiveResolvent_le hb0 hb h1 h2
        hY.posSemidef).trans (CovarianceBulk.inv_etaZ_le_bulk hb hκ hE)) ny0
    have hD := hΔ W hWΔ E hE X hY hd₁'
    calc vecNorm ((passiveResolvent b E X)ᴴ *ᵥ y) * ‖matrixExpect μ (freshDelta b E X)‖ *
          vecNorm y' ≤ (ηi * vecNorm y) * (CΔ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) *
            vecNorm y' := by gcongr
      _ = _ := by simp only [ny]; ring
  -- (3) the mean of `Φ'`
  have hM0 := hMb W hWM E hE s hs X hY hdM' x x'
  have hP3 : ‖mP - ((sigmaPlus b : ℝ) : ℂ) / W * bx‖ ≤
      (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * nx := by
    have e : mP - ((sigmaPlus b : ℝ) : ℂ) / W * bx =
        (W : ℂ)⁻¹ * ((W : ℂ) * mP - ((sigmaPlus b : ℝ) : ℂ) * bx) := by
      have : (W : ℂ) ≠ 0 := by exact_mod_cast hWr.ne'
      field_simp
    rw [e, norm_mul, norm_inv, Complex.norm_natCast]
    have : CM * (jetDist b E s X + (W : ℝ)⁻¹) * nx ≤ CM' * (jetDist b E s X + (W : ℝ)⁻¹) * nx := by
      gcongr; exact le_max_left _ _
    calc (W : ℝ)⁻¹ * ‖(W : ℂ) * mP - ((sigmaPlus b : ℝ) : ℂ) * bx‖ ≤
        (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹) * nx) := by gcongr; exact hM0.trans this
      _ = _ := by ring
  have hP4 : ‖mP‖ ≤ Cσ * (W : ℝ)⁻¹ * nx := by
    have e : mP = (mP - ((sigmaPlus b : ℝ) : ℂ) / W * bx) + ((sigmaPlus b : ℝ) : ℂ) / W * bx := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h5 : ‖((sigmaPlus b : ℝ) : ℂ) / W * bx‖ ≤ sigmaPlus b * (W : ℝ)⁻¹ * nx := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hσ0, Complex.norm_natCast,
        div_eq_mul_inv]
      gcongr
    have hCM' : 0 ≤ CM' := le_max_right _ _
    have h6 : (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * nx ≤
        CM' * (dM + 1) * (W : ℝ)⁻¹ * nx := by
      have : jetDist b E s X + (W : ℝ)⁻¹ ≤ dM + 1 := by linarith
      have : 0 ≤ nx := by positivity
      calc (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * nx =
          CM' * (jetDist b E s X + (W : ℝ)⁻¹) * (W : ℝ)⁻¹ * nx := by ring
        _ ≤ CM' * (dM + 1) * (W : ℝ)⁻¹ * nx := by gcongr
    calc _ ≤ (W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * nx +
          sigmaPlus b * (W : ℝ)⁻¹ * nx := add_le_add hP3 h5
      _ ≤ CM' * (dM + 1) * (W : ℝ)⁻¹ * nx + sigmaPlus b * (W : ℝ)⁻¹ * nx := by linarith
      _ = Cσ * (W : ℝ)⁻¹ * nx := by simp only [Cσ]; ring
  -- assembly
  have hnx : 0 ≤ nx := by positivity
  have hny : 0 ≤ ny := by positivity
  have hCσ : 0 ≤ Cσ := by have : 0 ≤ CM' := le_max_right _ _
                          positivity
  have hηi : 0 ≤ ηi := by positivity
  have hCM' : 0 ≤ CM' := le_max_right _ _
  rw [hN]
  calc ‖A + mP * (star mH - byy) + (mP - ((sigmaPlus b : ℝ) : ℂ) / W * bx) * byy‖
      ≤ ‖A‖ + ‖mP‖ * ‖star mH - byy‖ + ‖mP - ((sigmaPlus b : ℝ) : ℂ) / W * bx‖ * ‖byy‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [← norm_mul, ← norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ Cv * Ch * (W : ℝ)⁻¹ ^ 2 * (nx * ny) +
          (Cσ * (W : ℝ)⁻¹ * nx) * (ηi * (CΔ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * ny) +
          ((W : ℝ)⁻¹ * (CM' * (jetDist b E s X + (W : ℝ)⁻¹)) * nx) * ny := by
        gcongr
    _ = Cv * Ch * (W : ℝ)⁻¹ ^ 2 * (nx * ny) +
          Cσ * ηi * CΔ * ((W : ℝ)⁻¹ * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * (nx * ny) +
          CM' * ((W : ℝ)⁻¹ * (jetDist b E s X + (W : ℝ)⁻¹)) * (nx * ny) := by ring
    _ ≤ Cv * Ch * ε * (nx * ny) + Cσ * ηi * CΔ * ε * (nx * ny) + CM' * ε * (nx * ny) := by
        rw [hcC]
        gcongr
    _ = (Cv * Ch + Cσ * ηi * CΔ + CM') * ε * (nx * ny) := by ring

end BlockBand.SourceProcess.FullSourceCovariance
