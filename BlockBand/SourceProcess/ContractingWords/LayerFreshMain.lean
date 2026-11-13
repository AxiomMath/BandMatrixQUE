module

public import BlockBand.SourceProcess.ContractingWords.LayerFreshHolds

/-!
# `LayerFreshBound` from `SepMeanAll`, `SepFluctAll` and the bulk moments of `N`

`layerFreshBound_of`: the separator mean and fluctuation bounds `SepMeanAll`, `SepFluctAll`,
together with the bulk moments of the fresh transport, give the one-layer bound `LayerFreshBound`
on the mean and centered parts of a product of new words.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator

/-- **The one-layer word step from the six separator inputs.** -/
theorem layerFreshBound_of (hGA : GaussianAbsorptionContract) (hM : SepMeanAll)
    (hF : SepFluctAll) : LayerFreshBound := by
  intro b hb0 hb κ hκ d r K c₀ hr hK hc₀
  obtain ⟨Ce, We, hCe, hMe⟩ := hM b hb0 hb κ hκ
  have hQ : (1 : ℝ) ≤ (d + 2) * r := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨Cf, Wf, hCf, hFl⟩ := hF b hb0 hb κ hκ ((d + 2) * r) hQ
  obtain ⟨μ, Wb, hμ, hbasic⟩ := fresh_basic hGA hb0 hb hκ
  set k : ℕ := 2 * (d + 1) ^ 2
  have hk : 1 ≤ k := by simp only [k]; nlinarith [Nat.zero_le d]
  obtain ⟨Cm, Wm, hCm⟩ := fullSourceMoments_field_holds hGA b hb0 hb κ hκ (k * r)
    (by nlinarith [(by exact_mod_cast hk : (1 : ℝ) ≤ k)])
  have hΓ : 0 ≤ max 1 K ^ d := by positivity
  have hKd : (0 : ℝ) ≤ 2 ^ d * (1 + μ) ^ d := by positivity
  have hGm : 0 ≤ (1 + 2 * max Cm 0) ^ k := by positivity
  have hCinj : (0 : ℝ) ≤ d * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) := by positivity
  obtain ⟨C1, hC1, hC1e⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C1 = max 1 K ^ d * (2 ^ d * (1 + μ) ^ d *
      ((d : ℝ) ^ 2 * (2 * Cf ^ 2)) * (1 + (2 * d * Cf) ^ d) + d * Ce * (3 + μ) ^ d) +
      d * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) * (1 + 2 * max Cm 0) ^ k :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C2, hC2, hC2e⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C2 = 2 * (max 1 K ^ d * (2 ^ d * (1 + μ) ^ d) *
      (d * Cf) * (1 + (2 * d * Cf) ^ d)) +
      2 * (d * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) * (1 + 2 * max Cm 0) ^ k) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨C1 + C2, max (max (max We Wf) (max Wb Wm)) 1, by positivity,
    fun W hW E hE s hs XX hXX nT nI A c hA hAK hc Zs hZ hd => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWe, hWf⟩, hWb, hWm⟩, hW1⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set X := nearSchur (boundaryZ b E) XX
  set δ0 := jetDistance0 b E X
  set δ1 := jetDistance1 b E s X
  set g := conductanceOf (passiveTransmission b E X)
  have hδ0 : 0 ≤ δ0 := by simp only [δ0, jetDistance0]; positivity
  have hδ1 : 0 ≤ δ1 := by simp only [δ1, jetDistance1]; positivity
  have hg : 0 ≤ g := BlockBand.SourceProcess.FullSourceCovariance.conductance_nonneg b E hη.le
    (nearSchur_passive hη hXX)
  set m := min 1 δ0
  have hm0 : 0 ≤ m := le_min zero_le_one hδ0
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmδ : m ≤ δ0 := min_le_right _ _
  set β : ℝ := Cf * (1 / Real.sqrt W + m)
  have hβ0 : 0 ≤ β := mul_nonneg hCf (add_nonneg (by positivity) hm0)
  set e : ℝ := min (Ce * (δ0 + δ1 + g / W + ((W : ℝ)⁻¹) ^ 2)) (μ + 1)
  have he0 : 0 ≤ e := le_min (by positivity) (by linarith)
  -- the layer data
  have hbas := fun σ => hbasic W hWb E hE XX hXX σ
  have hS := ae_sepOf_le hb0 hW1 hη hXX
  set Bt : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun σ => gapFactor b E s σ • sepOf b E XX σ
  have hBt : ∀ σ, ‖Bt σ‖ ≤ 1 := fun σ => by
    rw [norm_smul]
    have := norm_gapFactor_le hb0 hb hE1 hE2 hs σ
    have := norm_sepOf_le b E hXX hη σ
    nlinarith [norm_nonneg (gapFactor b E s σ), norm_nonneg (sepOf b E XX σ)]
  have hMB : ∀ σ, ‖matrixExpect (freshLaw W b) (fun y => freshTransport b E XX y *
      sepOf b E (freshTwoPortSchur E XX y) σ * (freshTransport b E XX y)ᴴ) - Bt σ‖ ≤ e :=
    fun σ => le_min (hMe W hWe E hE s hs XX hXX σ) ((norm_sub_le _ _).trans
      (add_le_add (hbas σ).2 (hBt σ)))
  have hB : ∀ σ u v, eLpNorm (fun y => bilinear u (freshTransport b E XX y *
      sepOf b E (freshTwoPortSchur E XX y) σ * (freshTransport b E XX y)ᴴ -
        matrixExpect (freshLaw W b) (fun y => freshTransport b E XX y *
          sepOf b E (freshTwoPortSchur E XX y) σ * (freshTransport b E XX y)ᴴ)) v)
      (ENNReal.ofReal ((d + 2) * r)) (freshLaw W b) ≤ ENNReal.ofReal (β * vecNorm u * vecNorm v) :=
    fun σ u v => hFl W hWf E hE XX hXX σ u v
  have hmom := hCm W hWm E hE XX hXX
  have hGmb : eLpNorm (fun y => (1 + ‖freshTransport b E XX y‖ + ‖freshD b E XX y‖) ^
      (2 * (d + 1) ^ 2)) (ENNReal.ofReal r) (freshLaw W b) ≤ ENNReal.ofReal ((1 + 2 * max Cm 0) ^ k) :=
    eLpNorm_G_pow_le (ν := freshLaw W b) (measurable_freshTransport_comp b E measurable_const
      measurable_id).norm.aestronglyMeasurable (measurable_freshD_comp b E measurable_const
      measurable_id).norm.aestronglyMeasurable (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      hk hr (le_max_right Cm 0) (hmom.1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      (hmom.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hZm : AEStronglyMeasurable (fun y => newProd A c (freshTransport b E XX y)
      (freshD b E XX y) (sepOf b E (freshTwoPortSchur E XX y)) Zs) (freshLaw W b) :=
    (measurable_layerZ (W := W) b E (A := fun _ : LayerSample W .oneBlockOnePort => A) c
      (XX := fun _ => XX) (ω := id) (fun _ => measurable_const) measurable_const measurable_id
      Zs).aestronglyMeasurable
  obtain ⟨hZi, hmean, hfl⟩ := layer_step hW1 A c hK hc₀ hA hAK hc
    (fun y => freshTransport b E XX y) (fun y => freshD b E XX y)
    (fun y => sepOf b E (freshTwoPortSchur E XX y)) hS (fun σ => (hbas σ).1)
    hμ hr hβ0 he0 hGm (fun σ => (hbas σ).2) hB Bt hBt hMB hGmb Zs hZ hd hZm
  have hcore : coreProd A Bt Zs = meanFactor b E s Zs * coreProd A (sepOf b E XX) Zs := by
    simp only [Bt]; rw [coreProd_smul, prod_gapFactor]
  refine ⟨hZi, ?_, ?_⟩
  · rw [← hcore]
    refine hmean.trans (le_trans ?_ (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hC2) (by positivity)))
    rw [hC1e]
    refine le_of_le_of_eq (arith_mean d hΓ hKd hCf hCe (by positivity) hW1' hδ0 hδ1 hg hm0 hm1 hmδ
      he0 (min_le_left _ _) (min_le_right _ _)) ?_
    ring
  · refine hfl.trans (ENNReal.ofReal_le_ofReal (le_trans ?_ (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hC1) (by positivity))))
    rw [hC2e]
    refine le_of_le_of_eq (arith_fluct d hΓ hKd hCf (by positivity) hW1' hδ0 hm0 hm1 hmδ) ?_
    ring

end BlockBand.SourceProcess.ContractingWords
