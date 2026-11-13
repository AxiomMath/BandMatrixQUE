module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKStep

/-!
# The `𝒦𝒦` part of `CovLayerHypK` and `ConjLayerHyp`

On the alive set, by `ae_condExp_kBracket`, the conditional brackets are fresh-layer integrals of
`(u_i*Δv_j)·op(u_k*Δv_l)` at `X_cl`, with frames bounded by `√R`. Then:

* **Conjugate (`conjLayerHyp_of_current`, from the contract hypotheses and `ClosedCurrentGram`)**:
  by `fresh_delta_opp_le` the integral is `σ₊/W (u_i*u_k)(v_l*v_j)` up to the same error; and
  `u_i*u_k = B_ik`, `v_l*v_j = (C₀)_lj` (`bilinear_uu_eq_B`, `bilinear_vv_eq_C0`) and
  `σ₊ = 2η²D₀` (`sigmaPlus_eq`) make it exactly `W⁻¹ kConjCov`.
* the arithmetic `layerErrX_facts`: `W⁻¹ ≤ e`, `(δ₀ + W⁻¹)² ≤ e²`, `covErr ≤ W^{-3/2} + e²` for
  passive `X_cl` (`e = b3CovErr`), so both errors have the `CovLayerHyp` shape with `N = 2`;
* the assembly `covLayerHypK_of_parts` (with the mixed pairs `CovLayerHypKG` as a
  hypothesis, the joint covariance of `u*Δv` with the Gram increments) and `covErrNonneg_b3CovErr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FullSourceCovariance (covErr)
open BlockBand.Transmission.Bridge
open scoped ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-!
## The hypotheses
-/

/-- The `𝒦𝒦` pairs of `CovLayerHyp`. -/
def CovLayerHypKK (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      CovLayerAt e Z b E τ m s h R (Vs W) j C N (Sum.inr ij) (Sum.inr kl)

/-- **The mixed `(𝒦, Gram)` pairs of `CovLayerHyp`** (the joint `(Δ, Gram-increment)` one-layer
covariance; `cCov = kGramCov`). -/
def CovLayerHypKG (e Z : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ 2 ≤ N ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ (ij : Fin np × Fin np) (g : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
        CovLayerAt e Z b E τ m s h R (Vs W) j C N (Sum.inr ij) (Sum.inl g) ∧
        CovLayerAt e Z b E τ m s h R (Vs W) j C N (Sum.inl g) (Sum.inr ij)

/-!
## The error scale at a passive input
-/

theorem layerErrX_facts {b E κ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {W : ℕ} (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    (W : ℝ)⁻¹ ≤ b3LayerErrX b E X ∧
      (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 ≤ b3LayerErrX b E X ^ 2 ∧
      covErr b E (b3Jet b E) X ≤ (W : ℝ)⁻¹ / Real.sqrt W + b3LayerErrX b E X ^ 2 := by
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := BlockBand.SourceProcess.FullSourceCovariance.conductance_nonneg b E hη.le hX
  have h0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have h1 : 0 ≤ jetDistance1 b E (b3Jet b E) X := norm_nonneg _
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hgW : 0 ≤ conductanceOf (passiveTransmission b E X) / W := div_nonneg hg hW0.le
  have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
  set e := b3LayerErrX b E X with he
  have hedef : e = jetDistance0 b E X + jetDistance1 b E (b3Jet b E) X +
      conductanceOf (passiveTransmission b E X) / W + (W : ℝ)⁻¹ := rfl
  have hWe : (W : ℝ)⁻¹ ≤ e := by rw [hedef]; linarith
  refine ⟨hWe, ?_, ?_⟩
  · have : jetDistance0 b E X + (W : ℝ)⁻¹ ≤ e := by rw [hedef]; linarith
    exact pow_le_pow_left₀ (by positivity) this 2
  · have hs1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr (by exact_mod_cast hW)
    have hsW : Real.sqrt W ≤ W := by
      have := Real.mul_self_sqrt hW0.le
      nlinarith
    have hsp : 0 < Real.sqrt W := by linarith
    have hinv : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := inv_anti₀ hsp hsW
    have hA : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by
      rw [div_eq_mul_inv, sq]; exact mul_le_mul_of_nonneg_left hinv hWi
    have hB : (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E (b3Jet b E) X +
        conductanceOf (passiveTransmission b E X) / W) ≤ e ^ 2 := by
      have hle : jetDistance0 b E X + jetDistance1 b E (b3Jet b E) X +
          conductanceOf (passiveTransmission b E X) / W ≤ e := by rw [hedef]; linarith
      rw [sq]
      exact mul_le_mul hWe hle (by positivity) (hWi.trans hWe)
    unfold covErr
    linarith

theorem norm_bilinear_one_le {W : ℕ} {u v : Fin W → ℂ} {r : ℝ} (hu : vecNorm u ≤ r)
    (hv : vecNorm v ≤ r) : ‖bilinear u 1 v‖ ≤ r * r := by
  rw [bilinear_one]
  refine (Transmission.PassiveCovariance.norm_star_dotProduct_le u v).trans ?_
  exact mul_le_mul hu hv (Transmission.PassiveCovariance.vecNorm_nonneg _)
    ((Transmission.PassiveCovariance.vecNorm_nonneg _).trans hu)

/-!
## `𝒦𝒦`
-/

/-- **The `𝒦𝒦` pairs of `CovLayerHyp b3CovErr b3CovZ`**, from the input hypotheses. -/
theorem covLayerHypKK_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    CovLayerHypKK b3CovErr b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  obtain ⟨CS, WS, hCS, hS⟩ := fresh_delta_same_le hGA hLp hb0 hb hκ
  obtain ⟨C₂, W₂, -, hL⟩ := lintegral_freshDelta_sq_le hGA hb0 hb hκ
  set r := Real.sqrt R
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  set σm := ‖sigmaMinus b E (b3Jet b E)‖
  set C' : ℝ := 2 * CS * r ^ 4 + σm * (r * r)
  refine ⟨C', 2, by positivity, le_rfl, ?_⟩
  filter_upwards [hFD.2.2.2.2.2, eventually_ge_atTop 1, eventually_ge_atTop WS,
    eventually_ge_atTop W₂, B3Cur.eventually_one_le_closeLen hFD.2.1]
    with W hVW hW1 hWS hW2 hs1 j hj ij kl
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hsj : closeLen s W ≤ j := hj'.1.1
  have hpas := ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 j
  have hint := integrable_freshDelta_sq (measurable_b3ClosedX b E s h τ m j)
    (hL W hW2 E hE np j (measurable_b3ClosedX b E s h τ m j)
      (fun y => b3ClosedX_b3Ext hsj le_rfl y) hpas)
  have hk := ae_condExp_kBracket hb0 hb hE1 hE2 s h hh τ m hW1 hVW.1 R (hs1.trans hsj) hj id
    continuous_id (fun _ => rfl) hint ij kl
  unfold CovLayerAt
  filter_upwards [hk, hpas, ae_closedNearV_eq_closedPS hb0 hb hE1 hE2 s h hh τ m hW1 j (Vs W),
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW1,
    ae_closedPhase_good (W := W) (np := np) b E s h j] with y hy hpy hv hP hQ hyA
  simp only [id_eq] at hy
  rw [hy hyA]
  have htr := hyA.2 j hsj le_rfl
  have hnu : ∀ k, vecNorm (closedNearU b E s h τ m W j k y) ≤ r := fun k =>
    norm_closedNearU_le b E s h τ m j (Vs W) k y htr
  have hnv : ∀ k, vecNorm (closedNearV b E s h τ m W j k y) ≤ r := fun k =>
    norm_closedNearV_le b E s h hh τ m j (Vs W) k y (hP.2.2.2 j) (isUnit_iff_ne_zero.2 hQ.1) htr
  have hfr := hS W hWS E hE (b3Jet b E) (b3Jet_spec hb0 hb hE1 hE2) _ hpy _ _ _ _ r
    (hnu ij.1) (hnv ij.2) (hnu kl.1) (hnv kl.2)
  have hcc : cCov b E (Sum.inr ij : CIdx K np) (Sum.inr kl)
      (b3ClosedGramAt b E s h τ m W j (Vs W) y) = 0 := rfl
  rw [hcc, mul_zero, sub_zero]
  obtain ⟨hWe, hδ, hcov⟩ := layerErrX_facts hb hκ hE hW1 hpy
  set e := b3CovErr b E np τ m s h K W (Vs W) j y
  have he : b3LayerErrX b E (b3ClosedX b E s h τ m W j y) = e := rfl
  rw [he] at hWe hδ hcov
  set Z := b3CovZ b E np τ m s h K W (Vs W) j y
  have hZ0 : 0 ≤ Z := b3CovZ_nonneg b E np τ m s h K W (Vs W) j y
  rw [norm_b3CovZ]
  have hQ0 := bilinear_uv_eq_contr b E s h τ m W j (Vs W) ij.1 kl.2 y (hv kl.2)
  have hQZ : ‖bilinear (closedNearU b E s h τ m W j ij.1 y) 1
      (closedNearV b E s h τ m W j kl.2 y)‖ ≤ Z := by
    rw [hQ0]
    exact norm_b3ContrCoord_le_b3CovZ b E np τ m s h K W (Vs W) j 0 (Sum.inr ij.1) (Sum.inr kl.2) y
  have hUV := norm_bilinear_one_le (hnu kl.1) (hnv ij.2)
  set L := sigmaMinus b E (b3Jet b E) / W *
    crossedTensor (closedNearU b E s h τ m W j ij.1 y) (closedNearV b E s h τ m W j ij.2 y)
      (closedNearU b E s h τ m W j kl.1 y) (closedNearV b E s h τ m W j kl.2 y) 1 1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hLn : ‖L‖ ≤ σm * (r * r) * (e * Z) := by
    simp only [L, crossedTensor, norm_mul, norm_div, Complex.norm_natCast]
    have hσ0 : 0 ≤ σm := norm_nonneg _
    calc σm / W * (‖bilinear (closedNearU b E s h τ m W j ij.1 y) 1
          (closedNearV b E s h τ m W j kl.2 y)‖ *
          ‖bilinear (closedNearU b E s h τ m W j kl.1 y) 1
            (closedNearV b E s h τ m W j ij.2 y)‖)
        ≤ σm * e * (Z * (r * r)) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hWe hσ0) (mul_le_mul hQZ hUV (norm_nonneg _)
            hZ0) (by positivity) (mul_nonneg hσ0 ((by positivity : (0:ℝ) ≤ (W:ℝ)⁻¹).trans hWe))
      _ = σm * (r * r) * (e * Z) := by ring
  have he0 : 0 ≤ e := (by positivity : (0:ℝ) ≤ (W:ℝ)⁻¹).trans hWe
  have hw : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  calc ‖∫ F, bilinear (closedNearU b E s h τ m W j ij.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W j y) F) (closedNearV b E s h τ m W j ij.2 y) *
        bilinear (closedNearU b E s h τ m W j kl.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W j y) F) (closedNearV b E s h τ m W j kl.2 y)
          ∂freshLaw W b‖
      ≤ ‖(∫ F, bilinear (closedNearU b E s h τ m W j ij.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W j y) F) (closedNearV b E s h τ m W j ij.2 y) *
        bilinear (closedNearU b E s h τ m W j kl.1 y)
          (freshDelta b E (b3ClosedX b E s h τ m W j y) F) (closedNearV b E s h τ m W j kl.2 y)
          ∂freshLaw W b) - L‖ + ‖L‖ := norm_le_norm_sub_add _ _
    _ ≤ CS * r ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ 2) + σm * (r * r) * (e * Z) := by
        refine add_le_add (hfr.trans ?_) hLn
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ C' * (e * Z) + C' * ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ 2) := by
        have h1 : 0 ≤ e * Z := mul_nonneg he0 hZ0
        have h2 : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ 2 := by positivity
        have h3 : 0 ≤ CS * r ^ 4 := by positivity
        have h4 : 0 ≤ σm * (r * r) := by positivity
        simp only [C']
        nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2, mul_nonneg h3 h2]

/-!
## The conjugate bracket
-/

/-- **`ConjLayerHyp b3CovErr b3CovZ`** from the input hypotheses and the closed current Gram
identity (c).
-/
theorem conjLayerHyp_of_current (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hc : ClosedCurrentGram) : ConjLayerHyp b3CovErr b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  obtain ⟨CO, WO, hCO, hO⟩ := fresh_delta_opp_le hGA hLp hP hb0 hb hκ
  obtain ⟨C₂, W₂, -, hL⟩ := lintegral_freshDelta_sq_le hGA hb0 hb hκ
  set r := Real.sqrt R
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  set C' : ℝ := 2 * CO * r ^ 4
  refine ⟨C', 2, by positivity, le_rfl, ?_⟩
  filter_upwards [hFD.2.2.2.2.2, eventually_ge_atTop 1, eventually_ge_atTop WO,
    eventually_ge_atTop W₂, B3Cur.eventually_one_le_closeLen hFD.2.1,
    hc b E np τ m T s h K Vs hFD R] with W hVW hW1 hWS hW2 hs1 hcW j hj ij kl
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hsj : closeLen s W ≤ j := hj'.1.1
  have hpas := ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 j
  have hint := integrable_freshDelta_sq (measurable_b3ClosedX b E s h τ m j)
    (hL W hW2 E hE np j (measurable_b3ClosedX b E s h τ m j)
      (fun y => b3ClosedX_b3Ext hsj le_rfl y) hpas)
  have hk := ae_condExp_kBracket hb0 hb hE1 hE2 s h hh τ m hW1 hVW.1 R (hs1.trans hsj) hj
    (starRingEnd ℂ) Complex.continuous_conj Complex.norm_conj hint ij kl
  filter_upwards [hk, hpas, ae_closedNearV_eq_closedPS hb0 hb hE1 hE2 s h hh τ m hW1 j (Vs W),
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW1,
    ae_closedPhase_good (W := W) (np := np) b E s h j, hcW j hj] with y hy hpy hv hPg hQ hcy hyA
  rw [hy hyA]
  simp only [starRingEnd_apply]
  have htr := hyA.2 j hsj le_rfl
  have hnu : ∀ k, vecNorm (closedNearU b E s h τ m W j k y) ≤ r := fun k =>
    norm_closedNearU_le b E s h τ m j (Vs W) k y htr
  have hnv : ∀ k, vecNorm (closedNearV b E s h τ m W j k y) ≤ r := fun k =>
    norm_closedNearV_le b E s h hh τ m j (Vs W) k y (hPg.2.2.2 j) (isUnit_iff_ne_zero.2 hQ.1) htr
  have hfr := hO W hWS E hE (b3Jet b E) (b3Jet_spec hb0 hb hE1 hE2) _ hpy _ _ _ _ r
    (hnu ij.1) (hnv ij.2) (hnu kl.1) (hnv kl.2)
  have hB := bilinear_uu_eq_B b E s h τ m W j (Vs W) ij.1 kl.1 y
  have hC := bilinear_vv_eq_C0 b E s h τ m W j (Vs W) kl.2 ij.2 y hv (hcy hyA)
  have hlead : ((sigmaPlus b : ℝ) : ℂ) / W *
      (bilinear (closedNearU b E s h τ m W j ij.1 y) 1 (closedNearU b E s h τ m W j kl.1 y) *
        bilinear (closedNearV b E s h τ m W j kl.2 y) 1 (closedNearV b E s h τ m W j ij.2 y)) =
      (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j (Vs W) y) := by
    rw [hB, hC, BlockBand.Transmission.PassiveCovariance.sigmaPlus_eq b E hb0 hE1 hE2]
    simp only [kConjCov]
    push_cast
    ring
  rw [← hlead]
  obtain ⟨hWe, hδ, hcov⟩ := layerErrX_facts hb hκ hE hW1 hpy
  set e := b3CovErr b E np τ m s h K W (Vs W) j y
  have he : b3LayerErrX b E (b3ClosedX b E s h τ m W j y) = e := rfl
  rw [he] at hWe hδ hcov
  have he0 : 0 ≤ e := (by positivity : (0:ℝ) ≤ (W:ℝ)⁻¹).trans hWe
  have hZ := norm_nonneg (b3CovZ b E np τ m s h K W (Vs W) j y)
  refine hfr.trans ?_
  have h2 : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ 2 := by positivity
  have h3 : 0 ≤ CO * r ^ 4 := by positivity
  have h5 : CO * r ^ 4 * (covErr b E (b3Jet b E) (b3ClosedX b E s h τ m W j y) +
      (jetDistance0 b E (b3ClosedX b E s h τ m W j y) + (W : ℝ)⁻¹) ^ 2) ≤
      CO * r ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) h3
  simp only [C']
  nlinarith [mul_nonneg h3 h2, mul_nonneg h3 (mul_nonneg he0 hZ)]

/-!
## Assembly of `CovLayerHypK`
-/

/-- `e ≥ 0` on the alive set for the closed layer error scale (passivity of `X_cl`). -/
theorem covErrNonneg_b3CovErr : CovErrNonneg b3CovErr := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  filter_upwards [eventually_ge_atTop 1] with W hW1 j hj
  filter_upwards [ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 j] with y hy _
  exact (by positivity : (0:ℝ) ≤ (W:ℝ)⁻¹).trans (layerErrX_facts hb hκ hE hW1 hy).1

/-- **`CovLayerHypK` from its `𝒦𝒦` and mixed parts.** -/
theorem covLayerHypK_of_parts {e Z : CovField} (hKK : CovLayerHypKK e Z) (hKG : CovLayerHypKG e Z)
    (hnn : CovErrNonneg e) : CovLayerHypK e Z := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C₁, N₁, hC₁, hN₁, hev₁⟩ := hKK b E np τ m T s h K Vs hFD R
  obtain ⟨C₂, N₂, hC₂, hN₂, hev₂⟩ := hKG b E np τ m T s h K Vs hFD R
  refine ⟨2 * (C₁ + C₂), max N₁ N₂, by positivity, le_max_of_le_left hN₁, ?_⟩
  filter_upwards [hev₁, hev₂, hnn b E np τ m T s h K Vs hFD R] with W hW₁ hW₂ hWn j hj c c' hc
  have hw : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have key : ∀ {C₀ : ℝ} {N₀ : ℕ}, 0 ≤ C₀ → C₀ ≤ C₁ + C₂ → 2 ≤ N₀ → N₀ ≤ max N₁ N₂ →
      CovLayerAt e Z b E τ m s h R (Vs W) j C₀ N₀ c c' →
      CovLayerAt e Z b E τ m s h R (Vs W) j (2 * (C₁ + C₂)) (max N₁ N₂) c c' := by
    intro C₀ N₀ h0 hle hN hNm hb
    filter_upwards [hb, hWn j hj] with y hy hy0 hyA
    exact cov_bound_weaken h0 hle (hy0 hyA) (norm_nonneg _) hw hN hNm (hy hyA)
  rcases c with g | ij
  · rcases hc with ⟨ij, hij⟩ | ⟨kl, hkl⟩
    · exact absurd hij (by simp)
    · subst hkl
      exact key hC₂ (by linarith) hN₂ (le_max_right _ _) (hW₂ j hj kl g).2
  · rcases c' with g | kl
    · exact key hC₂ (by linarith) hN₂ (le_max_right _ _) (hW₂ j hj ij g).1
    · exact key hC₁ (by linarith) hN₁ (le_max_left _ _) (hW₁ j hj ij kl)

/-- **`CovLayerHypK b3CovErr b3CovZ`** from the input hypotheses and the mixed pairs. -/
theorem covLayerHypK_of_mixed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hKG : CovLayerHypKG b3CovErr b3CovZ) : CovLayerHypK b3CovErr b3CovZ :=
  covLayerHypK_of_parts (covLayerHypKK_holds hGA hLp) hKG covErrNonneg_b3CovErr

end BlockBand.SourceProcess.PhysApprox.B3
