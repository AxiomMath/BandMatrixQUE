module

public import BlockBand.SourceProcess.ContractingWords.SlotCov

/-!
# The covariance of two ordinary slots: main bound

`slot_cov`: the covariance of the centered slot bilinears `zc` of two ordinary separators is the
sum of the four full-source covariance tensors up to `C(1 + g)²(W^{-3/2} + e²)`, uniformly on the
bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem sq_norm_sub_le (a c : ℂ) : ‖a - c‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
  have h := norm_sub_le a c
  nlinarith [norm_nonneg a, norm_nonneg c, norm_nonneg (a - c), sq_nonneg (‖a‖ - ‖c‖)]

/-- The four-term bound once all moments are known. -/
theorem four_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y X' Y' : Ω → ℂ}
    (iX : Integrable (fun ω => ‖X ω‖ ^ 2) μ) (iY : Integrable (fun ω => ‖Y ω‖ ^ 2) μ)
    (iX' : Integrable (fun ω => ‖X' ω‖ ^ 2) μ) (iY' : Integrable (fun ω => ‖Y' ω‖ ^ 2) μ)
    {β γ r : ℝ} (hr : 0 < r) (bX : ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤ β ^ 2) (bY : ∫ ω, ‖Y ω‖ ^ 2 ∂μ ≤ γ ^ 2)
    (bX' : ∫ ω, ‖X' ω‖ ^ 2 ∂μ ≤ β ^ 2) (bY' : ∫ ω, ‖Y' ω‖ ^ 2 ∂μ ≤ γ ^ 2) :
    ‖∫ ω, X ω * Y' ω ∂μ‖ + ‖∫ ω, Y ω * X' ω ∂μ‖ + ‖∫ ω, Y ω * Y' ω ∂μ‖ ≤
      r⁻¹ * β ^ 2 + (r + 1) * γ ^ 2 := by
  have a1 := norm_integral_mul_le_amgm (f := X) (g := Y') iX iY' (inv_pos.mpr hr)
  have a2 := norm_integral_mul_le_amgm (f := Y) (g := X') iY iX' hr
  have a3 := norm_integral_mul_le_amgm (f := Y) (g := Y') iY iY' one_pos
  rw [inv_inv] at a1
  rw [inv_one] at a3
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  nlinarith [mul_le_mul_of_nonneg_left bX hr'.le, mul_le_mul_of_nonneg_left bY' hr.le,
    mul_le_mul_of_nonneg_left bY hr.le, mul_le_mul_of_nonneg_left bX' hr'.le]

/-- **The slot covariance.** -/
theorem slot_cov (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓ : ProjGammaFluct) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ σ' : Separator, σ.unconj + σ.conj = 0 → σ'.unconj + σ'.conj = 0 →
      ∀ u v u' v' : Fin 2 × Fin W → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 → vecNorm u' ≤ 1 →
        vecNorm v' ≤ 1 →
        ‖∫ y, zc b E XX σ u v y * zc b E XX σ' u' v' y ∂freshLaw W b -
            ∑ k, fscK b E s W k * crossedTensor u v u' v'
              (sepOf b E XX σ * fscG b E XX k * sepOf b E XX σ')
              (sepOf b E XX σ' * fscH b E XX k * sepOf b E XX σ)‖ ≤
          C * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) ^ 2 *
            ((W : ℝ)⁻¹ / Real.sqrt W + layerErr b E s XX ^ 2) := by
  obtain ⟨CF, WF, hF⟩ :=
    FullSourceCovariance.fullSourceCovarianceEnergyUniform_holds hGA hLp hP b hb0 hb κ hκ
  obtain ⟨C₂, W₂, hC₂, hf⟩ := sepFluctIdProj_holds hGA hLp b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨CΓ, WΓ, hCΓ, hΓ'⟩ := hΓ b hb0 hb κ hκ
  obtain ⟨μb, W₃, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  refine ⟨max CF 0 + 2 * C₂ ^ 2 + 4 * CΓ ^ 2, max (max WF W₂) (max WΓ (max W₃ 1)),
    by positivity, ?_⟩
  intro W hW E hE s hs XX hXX σ σ' hσ hσ' u v u' v' hu hv hu' hv'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWF, hW2⟩, hWΓ, hW3, hW1⟩ := hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨hδ0, hδe, -, hWe, he0, -⟩ := layerErr_parts b E s XX hg (W := W)
  set g := conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))
  set δ₀ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  set e := layerErr b E s XX
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr (by linarith)
  have hT : ∀ τ : Separator, ∀ i j, Integrable (fun y => transportedSep b E XX τ y i j)
      (freshLaw W b) := fun τ => (hfb W hW3 E hE XX hXX τ).1
  set β := C₂ * (1 / Real.sqrt W + e)
  have hβ : 0 ≤ β := by positivity
  have hZ : ∀ τ : Separator, τ.unconj + τ.conj = 0 → ∀ x z : Fin 2 × Fin W → ℂ, vecNorm x ≤ 1 →
      vecNorm z ≤ 1 → eLpNorm (zc b E XX τ x z) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal β := fun τ hτ x z hx hz => by
    refine (hf W hW2 E hE XX hXX τ hτ x z).trans (ENNReal.ofReal_le_ofReal ?_)
    have hm : min 1 δ₀ ≤ e := (min_le_right _ _).trans hδe
    have := vecNorm_nonneg x; have := vecNorm_nonneg z
    calc C₂ * (1 / Real.sqrt W + min 1 δ₀) * vecNorm x * vecNorm z ≤
          C₂ * (1 / Real.sqrt W + e) * 1 * 1 := by gcongr
      _ = β := by ring
  obtain ⟨hBs, hBn⟩ := sepOf_ord_herm (b := b) (E := E) (XX := XX) hσ
  obtain ⟨hBs', hBn'⟩ := sepOf_ord_herm (b := b) (E := E) (XX := XX) hσ'
  set B := sepOf b E XX σ
  set B' := sepOf b E XX σ'
  have hnB : ∀ x : Fin 2 × Fin W → ℂ, vecNorm x ≤ 1 → vecNorm (B *ᵥ x) ≤ 1 := fun x hx =>
    (vecNorm_mulVec_le B x).trans (by nlinarith [norm_nonneg B, vecNorm_nonneg x])
  have hnB' : ∀ x : Fin 2 × Fin W → ℂ, vecNorm x ≤ 1 → vecNorm (B' *ᵥ x) ≤ 1 := fun x hx =>
    (vecNorm_mulVec_le B' x).trans (by nlinarith [norm_nonneg B', vecNorm_nonneg x])
  obtain ⟨mX, -, -, iX, bX⟩ := zc_facts (hT .id) (B *ᵥ u) (B *ᵥ v) hβ
    (hZ .id rfl _ _ (hnB u hu) (hnB v hv))
  obtain ⟨mX', -, -, iX', bX'⟩ := zc_facts (hT .id) (B' *ᵥ u') (B' *ᵥ v') hβ
    (hZ .id rfl _ _ (hnB' u' hu') (hnB' v' hv'))
  obtain ⟨mZ, -, -, iZ, -⟩ := zc_facts (hT σ) u v hβ (hZ σ hσ u v hu hv)
  obtain ⟨mZ', -, -, iZ', -⟩ := zc_facts (hT σ') u' v' hβ (hZ σ' hσ' u' v' hu' hv')
  set γ := CΓ * (g / W + δ₀ * Real.sqrt (g / W))
  have hYb : ∀ τ : Separator, τ.unconj + τ.conj = 0 → ∀ x z : Fin 2 × Fin W → ℂ,
      vecNorm x ≤ 1 → vecNorm z ≤ 1 → ∫ y, ‖zr b E XX τ x z y‖ ^ 2 ∂freshLaw W b ≤ γ ^ 2 :=
    fun τ hτ x z hx hz => by
      rcases zr_cases (hT .id) (hT .proj) hτ x z with h | h
      · simp only [h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          integral_zero]
        positivity
      · simp only [h, norm_neg]
        refine (hΓ' W hWΓ E hE XX hXX x z).trans ?_
        have := vecNorm_nonneg x; have := vecNorm_nonneg z
        have h0 : 0 ≤ CΓ * (g / W + δ₀ * Real.sqrt (g / W)) := by positivity
        have h1 : CΓ * (g / W + δ₀ * Real.sqrt (g / W)) * vecNorm x * vecNorm z ≤ γ := by
          calc _ ≤ CΓ * (g / W + δ₀ * Real.sqrt (g / W)) * 1 * 1 := by gcongr
            _ = γ := by ring
        exact pow_le_pow_left₀ (by positivity) h1 2
  have hYi : ∀ {τ : Separator} {x z : Fin 2 × Fin W → ℂ},
      AEStronglyMeasurable (zc b E XX τ x z) (freshLaw W b) →
      Integrable (fun y => ‖zc b E XX τ x z y‖ ^ 2) (freshLaw W b) →
      AEStronglyMeasurable (zc b E XX .id (sepOf b E XX τ *ᵥ x) (sepOf b E XX τ *ᵥ z))
        (freshLaw W b) →
      Integrable (fun y => ‖zc b E XX .id (sepOf b E XX τ *ᵥ x) (sepOf b E XX τ *ᵥ z) y‖ ^ 2)
        (freshLaw W b) →
      AEStronglyMeasurable (zr b E XX τ x z) (freshLaw W b) ∧
        Integrable (fun y => ‖zr b E XX τ x z y‖ ^ 2) (freshLaw W b) :=
    fun h1 h2 h3 h4 => ⟨h1.sub h3, ((h2.const_mul 2).add (h4.const_mul 2)).mono'
      ((h1.sub h3).norm.pow 2) (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact sq_norm_sub_le _ _)⟩
  obtain ⟨mY, iY⟩ := hYi mZ iZ mX iX
  obtain ⟨mY', iY'⟩ := hYi mZ' iZ' mX' iX'
  have hsplit : ∀ y, zc b E XX σ u v y = zc b E XX .id (B *ᵥ u) (B *ᵥ v) y + zr b E XX σ u v y :=
    fun y => by simp only [zr, B]; ring
  have hsplit' : ∀ y, zc b E XX σ' u' v' y =
      zc b E XX .id (B' *ᵥ u') (B' *ᵥ v') y + zr b E XX σ' u' v' y :=
    fun y => by simp only [zr, B']; ring
  simp only [hsplit, hsplit']
  rw [int_four (integrable_mul_of_sq mX mX' iX iX') (integrable_mul_of_sq mX mY' iX iY')
    (integrable_mul_of_sq mY mX' iY iX') (integrable_mul_of_sq mY mY' iY iY'),
    zc_ward b E XX (hT .id)]
  have hFb := hF W hWF E hE s hs XX hXX (B *ᵥ u) (B *ᵥ v) (B' *ᵥ u') (B' *ᵥ v')
  simp only at hFb
  rw [fsc_eq] at hFb
  simp only [crossedTensor_sandwich u v u' v' B B' _ _ hBs hBs'] at hFb
  have h4 := FullSourceCovariance.fourNorm_le (hnB u hu) (hnB v hv) (hnB' u' hu') (hnB' v' hv')
  have hcov0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ₀ +
      jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W) := by
    have : 0 ≤ jetDistance1 b E s (nearSchur (boundaryZ b E) XX) := norm_nonneg _
    positivity
  have hFb' : ‖bilinearCovariance (freshLaw W b) (wardNoise b E XX) (B *ᵥ u) (B *ᵥ v)
      (B' *ᵥ u') (B' *ᵥ v') - ∑ k, fscK b E s W k * crossedTensor u v u' v'
        (B * fscG b E XX k * B') (B' * fscH b E XX k * B)‖ ≤
      max CF 0 * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ₀ +
        jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W)) := by
    refine hFb.trans ?_
    have := FullSourceCovariance.fourNorm_nonneg (B *ᵥ u) (B *ᵥ v) (B' *ᵥ u') (B' *ᵥ v')
    calc _ ≤ max CF 0 * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ₀ +
          jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W)) * (1 * 1 * 1 * 1) := by
          gcongr
          exact le_max_left _ _
      _ = _ := by ring
  have hfour := four_bound iX iY iX' iY' hsW bX (hYb σ hσ u v hu hv) bX' (hYb σ' hσ' u' v' hu' hv')
  have hsum : δ₀ + jetDistance1 b E s (nearSchur (boundaryZ b E) XX) + g / W ≤ e := by
    simp only [e, layerErr]; linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) W)]
  have harith := cov_arith (δ₁ := jetDistance1 b E s (nearSchur (boundaryZ b E) XX)) hWr hWe hδe
    hsum hδ0 (norm_nonneg _) hg (le_max_right CF 0) (C₂ := C₂) (CΓ := CΓ)
  calc _ = ‖(bilinearCovariance (freshLaw W b) (wardNoise b E XX) (B *ᵥ u) (B *ᵥ v)
        (B' *ᵥ u') (B' *ᵥ v') - ∑ k, fscK b E s W k * crossedTensor u v u' v'
          (B * fscG b E XX k * B') (B' * fscH b E XX k * B)) +
        (∫ y, zc b E XX .id (B *ᵥ u) (B *ᵥ v) y * zr b E XX σ' u' v' y ∂freshLaw W b +
          ∫ y, zr b E XX σ u v y * zc b E XX .id (B' *ᵥ u') (B' *ᵥ v') y ∂freshLaw W b +
          ∫ y, zr b E XX σ u v y * zr b E XX σ' u' v' y ∂freshLaw W b)‖ := by
        congr 1; ring
    _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add hFb' ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))).trans ?_
        refine le_trans ?_ harith
        simp only [β, γ] at hfour
        linarith

end BlockBand.SourceProcess.ContractingWords
