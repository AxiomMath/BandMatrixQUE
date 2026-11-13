module

public import BlockBand.SourceProcess.PhysApprox.B3DecayInBound
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormDefs
public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.ContractingWords.IncrementHolds
public import BlockBand.SourceProcess.ContractingWords.LayerMeas
public import BlockBand.Transmission.PathScalar.AbsorbedRecursion
public import BlockBand.SourceProcess.FullSource.Measurability

/-!
# The closed one-step estimates from the one-layer bound

The one-step mean (SM) `B3ClosedContrStepMean` and the one-step fluctuation (SF)
`B3ClosedContrStepFluct` of the closed contracting coordinates are proved from the one-layer
bound and two hypotheses:

* `B3ClosedContrLayerForm`: at every non-birth step, a closed contracting coordinate is, on the
  alive set, the polarized combination
  `Q_j = Σ_t wt_t coreProd(A, sepOf 𝕏, Zs_t)`, `Q_{j+1} = Σ_t wt_t newProd(A, c, N(𝕏, F_j), …)`
  of two admitted degree-`≤ 1` contracting products with equal conjugation counts, at a Hermitian
  two-port `𝕏` (the padded closed state) and Hermitian letters `Tr|A_ℓ| ≤ K_l`, all
  `b3Ext`-invariant Borel functions, with `nearSchur(𝕏) = b3ClosedX` on the alive set, and
  `1_{A_j}Q_{j+1}` integrable;
* `B3ClosedJetLp`: `‖1_{A_j}(δ₀ + δ₁ + |g|/W + W⁻¹)(X_cl)‖_p ≤ C_p/W` for `X_cl = b3ClosedX` at
  every non-birth step, every `p ≥ 1`. The `L⁴` jet bound `ClosedJetL4` is the `δ₀`, `p = 4` part
  only; it does not suffice for every `p`.

Main results: `b3ClosedContrStepMean_of_layer`, `b3ClosedContrStepFluct_of_layer`, their forms
from the input hypotheses (`b3ClosedContrStepMean_of_gaussianInputs`,
`b3ClosedContrStepFluct_of_gaussianInputs`), and `b3ClosedContrDecay_of_layer` (with
`b3ClosedContrBound_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3DecayIn

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.PhysApprox.B3
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops
open scoped NNReal ENNReal

variable {W np : ℕ}

/-!
## Objects
-/

/-- The one-layer new value of a product at the old two-port `𝕏` and the fresh layer `F`. -/
def b3LayerVal (b E : ℝ) {W nT nI : ℕ}
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (F : LayerSample W .oneBlockOnePort) (Zs : List (TraceWord nT nI)) : ℂ :=
  newProd A c (freshTransport b E XX F) (freshD b E XX F) (sepOf b E (freshTwoPortSchur E XX F)) Zs

/-- The one-layer error scale `δ₀ + δ₁ + |g|/W + W⁻¹` at a one-port input `X`. -/
def b3LayerErr (b E : ℝ) (sj : ℂ) (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  jetDistance0 b E X + jetDistance1 b E sj X +
    |conductanceOf (passiveTransmission b E X)| / W + (W : ℝ)⁻¹

theorem jetDistance0_le_b3LayerErr (b E : ℝ) (sj : ℂ) (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ) :
    jetDistance0 b E X ≤ b3LayerErr b E sj W X := by
  have h1 : 0 ≤ jetDistance1 b E sj X := by simp only [jetDistance1]; positivity
  have h2 : 0 ≤ |conductanceOf (passiveTransmission b E X)| / W := by positivity
  have h3 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  simp only [b3LayerErr]; linarith

theorem b3LayerErr_nonneg (b E : ℝ) (sj : ℂ) (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ) :
    0 ≤ b3LayerErr b E sj W X :=
  (show (0 : ℝ) ≤ jetDistance0 b E X by simp only [jetDistance0]; positivity).trans
    (jetDistance0_le_b3LayerErr b E sj W X)

/-- **The closed layer form at one step**: the polarized one-layer form of the closed contracting
coordinate `Q^σ_{kl}` at the step `j → j + 1`. -/
def ClosedContrLayerAt (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (σ : Fin 4)
    (k l : SrcCol K (Fin np)) (Kl c₀ : ℝ) {nT nI : ℕ}
    (XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : ProbedPath W np × ℝ → TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (Zs : Fin 2 → List (TraceWord nT nI)) (wt : Fin 2 → ℂ) : Prop :=
  Measurable XX ∧ (∀ ℓ, Measurable fun y => A y ℓ) ∧
    (∀ y, XX (b3Ext W j y) = XX y) ∧ (∀ y, A (b3Ext W j y) = A y) ∧
    (∀ y, (XX y).IsHermitian) ∧ (∀ y ℓ, (A y ℓ).IsHermitian) ∧
    (∀ y ℓ, nuclearNorm (A y ℓ) ≤ Kl) ∧ (∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2) ∧
    (∀ t, IsAdmittedProduct (Zs t)) ∧ (∀ t, productDegree (Zs t) ≤ 1) ∧
    1 ≤ unconjCount (Zs 0) + conjCount (Zs 0) ∧
    unconjCount (Zs 1) = unconjCount (Zs 0) ∧ conjCount (Zs 1) = conjCount (Zs 0) ∧
    (∀ t, ‖wt t‖ ≤ 1) ∧
    Integrable ((b3Alive b E s h τ m R W j Vs).indicator
      (b3ContrCoord b E s h τ m W (j + 1) Vs σ k l)) (closedLaw b W np) ∧
    ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      nearSchur (boundaryZ b E) (XX y) = b3ClosedX b E s h τ m W j y ∧
      b3ContrCoord b E s h τ m W (j + 1) Vs σ k l y =
        ∑ t, wt t * b3LayerVal b E (A y) c (XX y) (freshSample W j y.1.1) (Zs t) ∧
      b3ContrCoord b E s h τ m W j Vs σ k l y =
        ∑ t, wt t * coreProd (A y) (sepOf b E (XX y)) (Zs t)

/-- **The closed one-layer form** of the closed contracting coordinates at every non-birth step
(closing commutes with near-end growth; the padded closed two-port is Hermitian and its near Schur
complement is `b3ClosedX`). -/
def B3ClosedContrLayerForm : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ Kl c₀ : ℝ, 0 ≤ Kl ∧ 0 ≤ c₀ ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      ∃ (nT nI : ℕ) (XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (A : ProbedPath W np × ℝ → TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (c : TraceLetter nT nI → ℝ) (Zs : Fin 2 → List (TraceWord nT nI)) (wt : Fin 2 → ℂ),
        ClosedContrLayerAt b E s h τ m R W j (Vs W) σ k l Kl c₀ XX A c Zs wt

/-- **The closed jets in every `L^p` at scale `1/W`** from the closing length on, at the closed
input `b3ClosedX`. -/
def B3ClosedJetLp : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ Cj : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ sj : ℂ, IsStationaryJet b E sj →
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator fun y =>
          b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤ ENNReal.ofReal (Cj / W)

/-!
## `L^p` norms over the fresh layer
-/

/-- **Fubini for `L^p` norms over the fresh layer**: a fresh-layer `L^p` bound at every value of
the conditioning coordinates gives the `L^p(closedLaw)` bound. -/
theorem eLpNorm_fresh_le (b : ℝ) (j : ℕ) {p : ℝ} (hp : 1 ≤ p)
    {Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ}
    (hΦ : Measurable Φ) {H : ProbedPath W np × ℝ → ℝ} (hH0 : ∀ y, 0 ≤ H y)
    (hb : ∀ x, eLpNorm (fun F => Φ (x, F)) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (H (b3Rebuild W j x))) :
    eLpNorm (fun y => Φ (b3Past W j y, freshSample W j y.1.1)) (ENNReal.ofReal p)
      (closedLaw b W np) ≤
      eLpNorm (fun y => H (b3Ext W j y)) (ENNReal.ofReal p) (closedLaw b W np) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  by_cases hHm : AEStronglyMeasurable (fun y => H (b3Ext W j y)) (closedLaw b W np)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hHm]; exact le_top
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hf : Measurable fun z => ‖Φ z‖ₑ ^ p := hΦ.enorm.pow_const p
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (f := fun y => Φ (b3Past W j y, freshSample W j y.1.1)) hp0 hpt
      (hΦ.comp hT).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hHm, hpr]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hin : ∀ x, ∫⁻ F, ‖Φ (x, F)‖ₑ ^ p ∂freshLaw W b ≤ ‖H (b3Rebuild W j x)‖ₑ ^ p := by
    intro x
    have h1 := hb x
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun F => Φ (x, F)) hp0 hpt
      (hΦ.comp measurable_prodMk_left).aestronglyMeasurable, hpr] at h1
    have h2 := ENNReal.rpow_le_rpow h1 (by linarith : (0 : ℝ) ≤ p)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by linarith), ENNReal.rpow_one] at h2
    rwa [Real.enorm_eq_ofReal (hH0 _)]
  calc ∫⁻ y, ‖Φ (b3Past W j y, freshSample W j y.1.1)‖ₑ ^ p ∂closedLaw b W np
      = ∫⁻ z, ‖Φ z‖ₑ ^ p ∂(closedLaw b W np).map
          (fun y => (b3Past W j y, freshSample W j y.1.1)) := (lintegral_map hf hT).symm
    _ = ∫⁻ x, ∫⁻ F, ‖Φ (x, F)‖ₑ ^ p ∂freshLaw W b ∂((pastLaw W j b).prod (probePhaseLaw W np)) := by
        rw [closedLaw_map_past_fresh, lintegral_prod _ hf.aemeasurable]
    _ ≤ ∫⁻ x, ‖H (b3Rebuild W j x)‖ₑ ^ p ∂((pastLaw W j b).prod (probePhaseLaw W np)) :=
        lintegral_mono hin
    _ = ∫⁻ x, ‖H (b3Rebuild W j x)‖ₑ ^ p ∂(closedLaw b W np).map (b3Past W j) := by
        rw [closedLaw_map_b3Past]
    _ ≤ ∫⁻ y, ‖H (b3Ext W j y)‖ₑ ^ p ∂closedLaw b W np :=
        lintegral_map_le _ (measurable_b3Past W j).aemeasurable

/-!
## The closed step through the fresh layer
-/

section Step

variable {b E s h : ℝ} {K : ℕ} {τ m : Fin np → ℝ} {R : ℝ} {j : ℕ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {σ : Fin 4}
  {k l : SrcCol K (Fin np)} {Kl c₀ : ℝ} {nT nI : ℕ}
  {XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
  {A : ProbedPath W np × ℝ → TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
  {c : TraceLetter nT nI → ℝ} {Zs : Fin 2 → List (TraceWord nT nI)} {wt : Fin 2 → ℂ}

/-- The Borel alive weight `1_{A^M_j}`. -/
def aliveWt (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    ℂ :=
  (b3AliveM b E s h τ m R W j Vs).indicator (fun _ => (1 : ℂ)) y

theorem aliveWt_b3Ext (hjc : closeLen s W ≤ j)
    (hV : ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω) (y : ProbedPath W np × ℝ) :
    aliveWt b E s h τ m R W j Vs (b3Ext W j y) = aliveWt b E s h τ m R W j Vs y := by
  have hiff := mem_b3AliveM_b3Ext b E s h τ m R hjc le_rfl hV y
  by_cases hy : y ∈ b3AliveM b E s h τ m R W j Vs
  · simp only [aliveWt, Set.indicator_of_mem hy, Set.indicator_of_mem (hiff.2 hy)]
  · have hy' : b3Ext W j y ∉ b3AliveM b E s h τ m R W j Vs := fun h' => hy (hiff.1 h')
    simp only [aliveWt, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']

theorem measurable_aliveWt (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (j : ℕ)
    (hmV : Measurable Vs) : Measurable (aliveWt (np := np) b E s h τ m R W j Vs) :=
  measurable_const.indicator (measurableSet_b3AliveM b E s h τ m R W j hmV)

/-- The polarized layer value `S(y, F) = Σ_t wt_t newProd_t`. -/
def layerSum (b E : ℝ) {nT nI : ℕ}
    (XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : ProbedPath W np × ℝ → TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (Zs : Fin 2 → List (TraceWord nT nI)) (wt : Fin 2 → ℂ)
    (y : ProbedPath W np × ℝ) (F : LayerSample W .oneBlockOnePort) : ℂ :=
  ∑ t, wt t * b3LayerVal b E (A y) c (XX y) F (Zs t)

theorem measurable_layerSum_rebuild (b E : ℝ) (hXXm : Measurable XX)
    (hAm : ∀ ℓ, Measurable fun y => A y ℓ) :
    Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
        LayerSample W .oneBlockOnePort => layerSum b E XX A c Zs wt (b3Rebuild W j z.1) z.2 := by
  have hR : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => b3Rebuild W j z.1 :=
    (measurable_b3Rebuild (np := np) W j).comp measurable_fst
  refine Finset.measurable_sum _ fun t _ => measurable_const.mul ?_
  exact measurable_layerZ b E c (fun ℓ => (hAm ℓ).comp hR) (hXXm.comp hR) measurable_snd (Zs t)

theorem layerSum_b3Ext (b E : ℝ) (hXXi : ∀ y, XX (b3Ext W j y) = XX y)
    (hAi : ∀ y, A (b3Ext W j y) = A y) (y : ProbedPath W np × ℝ) :
    layerSum b E XX A c Zs wt (b3Ext W j y) = layerSum b E XX A c Zs wt y := by
  funext F; simp only [layerSum, hXXi, hAi]

/-- **The closed step through the fresh layer**: on the alive set, `Q_{j+1}` is the layer sum at
the fresh layer, and its conditional mean is the fresh mean of the layer sum. -/
theorem closedLayer_ae (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hjc : closeLen s W ≤ j)
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs)
    (hF : ClosedContrLayerAt b E s h τ m R W j Vs σ k l Kl c₀ XX A c Zs wt) :
    ((b3Alive b E s h τ m R W j Vs).indicator (b3ContrCoord b E s h τ m W (j + 1) Vs σ k l)
        =ᵐ[closedLaw b W np] fun y => aliveWt b E s h τ m R W j Vs y *
          layerSum b E XX A c Zs wt y (freshSample W j y.1.1)) ∧
      ((closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
          (b3ContrCoord b E s h τ m W (j + 1) Vs σ k l) | b3Sigma W j np]
        =ᵐ[closedLaw b W np] fun y => aliveWt b E s h τ m R W j Vs y *
          ∫ F, layerSum b E XX A c Zs wt y F ∂freshLaw W b) := by
  obtain ⟨hXXm, hAm, hXXi, hAi, -, -, -, -, -, -, -, -, -, -, hint, hform⟩ := hF
  have hmV : Measurable Vs :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs (extPast W j (pastCoords W j ω)) = Vs ω :=
    fun ω => growth_fun_extPast hjc hVs ω
  have hAlM := b3Alive_ae_eq (np := np) hb1 hE1 hE2 s h τ m R W j Vs
  have h1 : (b3Alive b E s h τ m R W j Vs).indicator (b3ContrCoord b E s h τ m W (j + 1) Vs σ k l)
      =ᵐ[closedLaw b W np] fun y => aliveWt b E s h τ m R W j Vs y *
        layerSum b E XX A c Zs wt y (freshSample W j y.1.1) := by
    filter_upwards [hAlM.mem_iff, hform] with y hy hf
    by_cases hya : y ∈ b3Alive b E s h τ m R W j Vs
    · rw [Set.indicator_of_mem hya, (hf hya).2.1, aliveWt, Set.indicator_of_mem (hy.1 hya),
        one_mul]
      rfl
    · have hyM : y ∉ b3AliveM b E s h τ m R W j Vs := fun h' => hya (hy.2 h')
      rw [Set.indicator_of_notMem hya, aliveWt, Set.indicator_of_notMem hyM, zero_mul]
  refine ⟨h1, ?_⟩
  set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => aliveWt b E s h τ m R W j Vs (b3Rebuild W j z.1) *
      layerSum b E XX A c Zs wt (b3Rebuild W j z.1) z.2 with hΨdef
  have hΨ : Measurable Ψ :=
    ((measurable_aliveWt b E s h τ m R j hmV).comp
      ((measurable_b3Rebuild (np := np) W j).comp measurable_fst)).mul
      (measurable_layerSum_rebuild b E hXXm hAm)
  have hcomp : (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) =
      fun y => aliveWt b E s h τ m R W j Vs y *
        layerSum b E XX A c Zs wt y (freshSample W j y.1.1) := by
    funext y
    simp only [hΨdef, b3Rebuild_b3Past, aliveWt_b3Ext hjc hVinv, layerSum_b3Ext b E hXXi hAi]
  have hint' : Integrable (fun y => Ψ (b3Past W j y, freshSample W j y.1.1))
      (closedLaw b W np) := by
    rw [hcomp]; exact hint.congr h1
  have h2 := condExp_closed_fresh b j hΨ hint'
  rw [hcomp] at h2
  refine (condExp_congr_ae h1).trans (h2.trans (Eventually.of_forall fun y => ?_))
  simp only [hΨdef, b3Rebuild_b3Past, aliveWt_b3Ext hjc hVinv, layerSum_b3Ext b E hXXi hAi,
    integral_const_mul]

end Step

/-!
## The bulk constants
-/

theorem bulk_of_lt {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (2 + E) (2 - E) / 2 ∧ E ∈ bulkInterval (min (2 + E) (2 - E) / 2) := by
  have h0 : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · linarith [min_le_left (2 + E) (2 - E)]
  · linarith [min_le_right (2 + E) (2 - E)]

/-!
## (SM)
-/

/-- **(SM) from the one-layer bound, the closed layer form and the closed jets.** -/
theorem b3ClosedContrStepMean_of_layer (hL : LayerFreshBound) (hI : B3ClosedContrLayerForm)
    (hJ : B3ClosedJetLp) : B3ClosedContrStepMean := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith
  obtain ⟨Kl, c₀, hKl, hc₀, hev⟩ := hI b E np τ m T s h K Vs hFD R
  obtain ⟨Cj, hevJ⟩ := hJ b E np τ m T s h K Vs hFD R p hp
  obtain ⟨hκ, hEb⟩ := bulk_of_lt hE1 hE2
  set κ := min (2 + E) (2 - E) / 2
  obtain ⟨sj, hsj⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  obtain ⟨hρ0, hρ1, -⟩ := thetaStar_bulk_bound hb0 hb hκ
  obtain ⟨CL, WL, hCL, hLb⟩ := hL b hb0 hb κ hκ 1 p Kl c₀ hp hKl hc₀
  refine ⟨2 * CL * max Cj 0, thetaBound b κ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hev, hevJ, hVs, eventually_ge_atTop WL, eventually_ge_atTop 1]
    with W hW hWJ hVW hWL hW1 j hj σ k l
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVσ : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVσ.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨nT, nI, XX, A, c, Zs, wt, hF⟩ := hW j hj σ k l
  obtain ⟨h1, h2⟩ := closedLayer_ae hb1 hE1 hE2 hjc hVσ hF
  obtain ⟨-, -, -, -, hXXh, hAh, hAn, hc, hZ, hd, hr, hu, hcc, hwt, -, hform⟩ := hF
  set lam := meanFactor b E sj (Zs 0)
  have hlam1 : meanFactor b E sj (Zs 1) = lam := by simp only [lam, meanFactor, hu, hcc]
  refine ⟨lam, norm_meanFactor_le hb0 hb hκ hEb hsj (Zs 0) hr, ?_⟩
  set μ := closedLaw b W np
  set Al := b3Alive b E s h τ m R W j (Vs W)
  have hAlM := b3Alive_ae_eq (np := np) hb1 hE1 hE2 s h τ m R W j (Vs W)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  set err : ProbedPath W np × ℝ → ℝ := Al.indicator fun y =>
    b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
  have herr0 : ∀ y, 0 ≤ err y := fun y => Set.indicator_nonneg
    (fun y _ => b3LayerErr_nonneg b E sj W _) y
  have hLHSm : AEStronglyMeasurable (Al.indicator fun y =>
      μ[Al.indicator (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y -
        lam * b3ContrCoord b E s h τ m W j (Vs W) σ k l y) μ :=
    genMem_aesm_indicator hb1 hE1 hE2 s h τ m R W j hmV
      ((stronglyMeasurable_condExp.mono (b3Sigma_le j)).measurable.sub
        ((measurable_b3ContrCoord b E s h τ m W j hmV σ k l).const_mul _))
  have hpt : ∀ᵐ y ∂μ, ‖Al.indicator (fun y =>
      μ[Al.indicator (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y -
        lam * b3ContrCoord b E s h τ m W j (Vs W) σ k l y) y‖ ≤ 2 * CL * err y := by
    filter_upwards [h2, hAlM.mem_iff, hform] with y hy2 hy hf
    by_cases hya : y ∈ Al
    · obtain ⟨hX, -, hQ⟩ := hf hya
      rw [Set.indicator_of_mem hya, hy2, aliveWt, Set.indicator_of_mem (hy.1 hya), one_mul, hQ]
      have hb' : ∀ t, Integrable (fun F => b3LayerVal b E (A y) c (XX y) F (Zs t))
          (freshLaw W b) ∧
          ‖∫ F, b3LayerVal b E (A y) c (XX y) F (Zs t) ∂freshLaw W b -
              meanFactor b E sj (Zs t) * coreProd (A y) (sepOf b E (XX y)) (Zs t)‖ ≤
            CL * b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y) := by
        intro t
        have hl := hLb W hWL E hEb sj hsj (XX y) (hXXh y) nT nI (A y) c (hAh y) (hAn y) hc
          (Zs t) (hZ t) (hd t)
        refine ⟨hl.1, hl.2.1.trans (mul_le_mul_of_nonneg_left ?_ hCL)⟩
        rw [← hX]
        have hg : conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) (XX y))) /
            W ≤ |conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) (XX y)))| /
              W := div_le_div_of_nonneg_right (le_abs_self _) hWpos.le
        simp only [b3LayerErr]; linarith
      obtain ⟨hi0, hm0⟩ := hb' 0
      obtain ⟨hi1, hm1⟩ := hb' 1
      rw [hlam1] at hm1
      have hsum : ∫ F, layerSum b E XX A c Zs wt y F ∂freshLaw W b =
          wt 0 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b +
            wt 1 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b := by
        simp only [layerSum, Fin.sum_univ_two]
        rw [integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul,
          integral_const_mul]
      rw [hsum, Fin.sum_univ_two, show err y = b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
        from Set.indicator_of_mem hya _]
      have e : wt 0 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b +
            wt 1 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b -
          lam * (wt 0 * coreProd (A y) (sepOf b E (XX y)) (Zs 0) +
            wt 1 * coreProd (A y) (sepOf b E (XX y)) (Zs 1)) =
          wt 0 * (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b -
              lam * coreProd (A y) (sepOf b E (XX y)) (Zs 0)) +
            wt 1 * (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b -
              lam * coreProd (A y) (sepOf b E (XX y)) (Zs 1)) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have hn0 := norm_nonneg (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b -
        lam * coreProd (A y) (sepOf b E (XX y)) (Zs 0))
      have hn1 := norm_nonneg (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b -
        lam * coreProd (A y) (sepOf b E (XX y)) (Zs 1))
      have hw0 := hwt 0
      have hw1 := hwt 1
      have := norm_nonneg (wt 0)
      have := norm_nonneg (wt 1)
      nlinarith
    · rw [Set.indicator_of_notMem hya, norm_zero]
      exact mul_nonneg (by positivity) (herr0 y)
  refine (eLpNorm_mono_ae_real hLHSm hpt).trans ?_
  have e : (fun y => 2 * CL * err y) = (2 * CL) • err := by funext y; simp [smul_eq_mul]
  have hC2 : 0 ≤ 2 * CL := by positivity
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hC2]
  calc ENNReal.ofReal (2 * CL) * eLpNorm err (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * CL) * ENNReal.ofReal (max Cj 0 / W) := by
        gcongr
        exact (hWJ j hj sj hsj).trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le))
    _ = ENNReal.ofReal (2 * CL * max Cj 0 / W) := by
        rw [← ENNReal.ofReal_mul hC2, mul_div_assoc]

/-!
## (SF)
-/

/-- **(SF) from the one-layer bound, the closed layer form and the closed jets.** -/
theorem b3ClosedContrStepFluct_of_layer (hL : LayerFreshBound) (hI : B3ClosedContrLayerForm)
    (hJ : B3ClosedJetLp) : B3ClosedContrStepFluct := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith
  obtain ⟨Kl, c₀, hKl, hc₀, hev⟩ := hI b E np τ m T s h K Vs hFD R
  obtain ⟨Cj, hevJ⟩ := hJ b E np τ m T s h K Vs hFD R p hp
  obtain ⟨hκ, hEb⟩ := bulk_of_lt hE1 hE2
  set κ := min (2 + E) (2 - E) / 2
  obtain ⟨sj, hsj⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  obtain ⟨CL, WL, hCL, hLb⟩ := hL b hb0 hb κ hκ 1 p Kl c₀ hp hKl hc₀
  refine ⟨2 * CL * (1 + max Cj 0), by positivity, ?_⟩
  filter_upwards [hev, hevJ, hVs, eventually_ge_atTop WL, eventually_ge_atTop 1]
    with W hW hWJ hVW hWL hW1 j hj σ k l
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVσ : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVσ.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hjc hVσ ω
  obtain ⟨nT, nI, XX, A, c, Zs, wt, hF⟩ := hW j hj σ k l
  obtain ⟨h1, h2⟩ := closedLayer_ae hb1 hE1 hE2 hjc hVσ hF
  obtain ⟨hXXm, hAm, hXXi, hAi, hXXh, hAh, hAn, hc, hZ, hd, -, -, -, hwt, -, hform⟩ := hF
  set μ := closedLaw b W np
  set Al := b3Alive b E s h τ m R W j (Vs W)
  set AM := b3AliveM b E s h τ m R W j (Vs W)
  have hAMm : MeasurableSet AM := measurableSet_b3AliveM b E s h τ m R W j hmV
  have hAlM := b3Alive_ae_eq (np := np) hb1 hE1 hE2 s h τ m R W j (Vs W)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  set wA := aliveWt b E s h τ m R W j (Vs W)
  set S := layerSum b E XX A c Zs wt
  have hwA : ∀ y, wA (b3Ext W j y) = wA y := aliveWt_b3Ext hjc hVinv
  have hSi : ∀ y, S (b3Ext W j y) = S y := layerSum_b3Ext b E hXXi hAi
  -- the centred function
  set Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => wA (b3Rebuild W j z.1) *
      (S (b3Rebuild W j z.1) z.2 - ∫ F, S (b3Rebuild W j z.1) F ∂freshLaw W b) with hΦdef
  have hSm := measurable_layerSum_rebuild (j := j) (Zs := Zs) (wt := wt) (c := c) b E hXXm hAm
  have hΦ : Measurable Φ :=
    ((measurable_aliveWt b E s h τ m R j hmV).comp
      ((measurable_b3Rebuild (np := np) W j).comp measurable_fst)).mul
      (hSm.sub ((hSm.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable.comp
        measurable_fst))
  have hgΦ : (Al.indicator fun y => b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l y -
      μ[Al.indicator (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y)
      =ᵐ[μ] fun y => Φ (b3Past W j y, freshSample W j y.1.1) := by
    filter_upwards [h1, h2, hAlM.mem_iff] with y hy1 hy2 hy
    simp only [hΦdef, b3Rebuild_b3Past, hwA, hSi]
    by_cases hya : y ∈ Al
    · have hyM := hy.1 hya
      have hw : wA y = 1 := Set.indicator_of_mem hyM _
      rw [Set.indicator_of_mem hya] at hy1 ⊢
      rw [hy2, hy1, hw, one_mul, one_mul, one_mul]
    · have hyM : y ∉ AM := fun h' => hya (hy.2 h')
      have hw : wA y = 0 := Set.indicator_of_notMem hyM _
      rw [Set.indicator_of_notMem hya, hw, zero_mul]
  -- the fresh bound
  set H : ProbedPath W np × ℝ → ℝ := AM.indicator fun y =>
    2 * CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) with hHdef
  have hH0 : ∀ y, 0 ≤ H y := fun y => Set.indicator_nonneg (fun y _ => by
    have : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)) := by
      simp only [jetDistance0]; positivity
    positivity) y
  have hb' : ∀ x, eLpNorm (fun F => Φ (x, F)) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (H (b3Rebuild W j x)) := by
    intro x
    set y := b3Rebuild W j x
    by_cases hyM : y ∈ AM
    · have hw : wA y = 1 := Set.indicator_of_mem hyM _
      have hl : ∀ t, Integrable (fun F => b3LayerVal b E (A y) c (XX y) F (Zs t))
          (freshLaw W b) ∧
          eLpNorm (fun F => b3LayerVal b E (A y) c (XX y) F (Zs t) -
              ∫ F', b3LayerVal b E (A y) c (XX y) F' (Zs t) ∂freshLaw W b)
            (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (CL * (1 / Real.sqrt W +
              jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)))) := fun t => by
        have hl := hLb W hWL E hEb sj hsj (XX y) (hXXh y) nT nI (A y) c (hAh y) (hAn y) hc
          (Zs t) (hZ t) (hd t)
        exact ⟨hl.1, hl.2.2⟩
      obtain ⟨hi0, hf0⟩ := hl 0
      obtain ⟨hi1, hf1⟩ := hl 1
      have hfun : (fun F => Φ (x, F)) =
          wt 0 • (fun F => b3LayerVal b E (A y) c (XX y) F (Zs 0) -
              ∫ F', b3LayerVal b E (A y) c (XX y) F' (Zs 0) ∂freshLaw W b) +
            wt 1 • (fun F => b3LayerVal b E (A y) c (XX y) F (Zs 1) -
              ∫ F', b3LayerVal b E (A y) c (XX y) F' (Zs 1) ∂freshLaw W b) := by
        funext F
        simp only [hΦdef, S, layerSum, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        rw [hw, integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul,
          integral_const_mul]
        ring
      rw [hfun]
      refine (eLpNorm_add_le hp1).trans ?_
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
      have hw0 : ‖wt 0‖ₑ ≤ 1 := by rw [← ofReal_norm, ← ENNReal.ofReal_one];
                                    exact ENNReal.ofReal_le_ofReal (hwt 0)
      have hw1 : ‖wt 1‖ₑ ≤ 1 := by rw [← ofReal_norm, ← ENNReal.ofReal_one];
                                    exact ENNReal.ofReal_le_ofReal (hwt 1)
      have hHy : H y = 2 * CL * (1 / Real.sqrt W +
          jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) := Set.indicator_of_mem hyM _
      have hj0 : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)) := by
        simp only [jetDistance0]; positivity
      have hD0 : 0 ≤ CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) :=
        by positivity
      rw [hHy, show 2 * CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)))
        = CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) +
          CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) by ring,
        ENNReal.ofReal_add hD0 hD0]
      gcongr
      · exact (mul_le_mul' hw0 hf0).trans (by rw [one_mul])
      · exact (mul_le_mul' hw1 hf1).trans (by rw [one_mul])
    · have hw : wA y = 0 := Set.indicator_of_notMem hyM _
      have hfun : (fun F => Φ (x, F)) = 0 := by
        funext F; simp only [hΦdef, Pi.zero_apply]; rw [hw, zero_mul]
      rw [hfun, eLpNorm_zero]
      exact zero_le
  have hfr := eLpNorm_fresh_le b j hp hΦ hH0 hb'
  have hHinv : (fun y => H (b3Ext W j y)) = H := by
    funext y
    have hiff := mem_b3AliveM_b3Ext b E s h τ m R hjc le_rfl hVinv y
    by_cases hyM : y ∈ AM
    · rw [hHdef, Set.indicator_of_mem hyM, Set.indicator_of_mem (show b3Ext W j y ∈ AM from
        hiff.2 hyM), hXXi]
    · have hyM' : b3Ext W j y ∉ AM := fun h' => hyM (hiff.1 h')
      rw [hHdef, Set.indicator_of_notMem hyM, Set.indicator_of_notMem hyM']
  rw [hHinv] at hfr
  rw [eLpNorm_congr_ae hgΦ]
  refine hfr.trans ?_
  -- `H ≤ 2CL/√W + 2CL·1_{A}err`
  set err : ProbedPath W np × ℝ → ℝ := Al.indicator fun y =>
    b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
  have herr0 : ∀ y, 0 ≤ err y := fun y => Set.indicator_nonneg
    (fun y _ => b3LayerErr_nonneg b E sj W _) y
  have hHm : AEStronglyMeasurable H μ :=
    (Measurable.indicator (measurable_const.mul (measurable_const.add
      ((BlockBand.Transmission.PathScalar.measurable_jetDistance0 b E).comp
        (FullSource.measurable_nearSchur_comp _ hXXm)))) hAMm).aestronglyMeasurable
  have hpt : ∀ᵐ y ∂μ, ‖H y‖ ≤ 2 * CL * (1 / Real.sqrt W) + 2 * CL * err y := by
    filter_upwards [hAlM.mem_iff, hform] with y hy hf
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 y)]
    by_cases hya : y ∈ Al
    · have hyM := hy.1 hya
      rw [hHdef, Set.indicator_of_mem hyM, show err y = b3LayerErr b E sj W
        (b3ClosedX b E s h τ m W j y) from Set.indicator_of_mem hya _, (hf hya).1]
      have := jetDistance0_le_b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
      nlinarith
    · have hyM : y ∉ AM := fun h' => hya (hy.2 h')
      rw [hHdef, Set.indicator_of_notMem hyM]
      have := herr0 y
      positivity
  refine (eLpNorm_mono_ae_real hHm hpt).trans ?_
  have hC2 : 0 ≤ 2 * CL := by positivity
  have hsplit : (fun y => 2 * CL * (1 / Real.sqrt W) + 2 * CL * err y) =
      (fun _ => 2 * CL * (1 / Real.sqrt W)) + (2 * CL) • err := by
    funext y; simp [smul_eq_mul]
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC2, eLpNorm_const _ (by positivity)
    (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one,
    Real.enorm_eq_ofReal (by positivity)]
  have hjet := hWJ j hj sj hsj
  have hWs : (1 : ℝ) / W ≤ 1 / Real.sqrt W := by
    have h1 : Real.sqrt W ≤ W := by
      have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have := Real.sqrt_le_sqrt (show (W : ℝ) ≤ W * W by nlinarith)
      rwa [Real.sqrt_mul_self hWpos.le] at this
    exact one_div_le_one_div_of_le hsq h1
  calc ENNReal.ofReal (2 * CL * (1 / Real.sqrt W)) +
        ENNReal.ofReal (2 * CL) * eLpNorm err (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * CL * (1 / Real.sqrt W)) +
          ENNReal.ofReal (2 * CL) * ENNReal.ofReal (max Cj 0 / W) := by
        gcongr
        exact hjet.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le))
    _ = ENNReal.ofReal (2 * CL * (1 / Real.sqrt W) + 2 * CL * (max Cj 0 / W)) := by
        rw [← ENNReal.ofReal_mul hC2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (2 * CL * (1 + max Cj 0) / Real.sqrt W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm0 : 0 ≤ max Cj 0 := le_max_right _ _
        have e1 : max Cj 0 / W = max Cj 0 * (1 / W) := by ring
        have e2 : 2 * CL * (1 + max Cj 0) / Real.sqrt W =
            2 * CL * (1 / Real.sqrt W) + 2 * CL * (max Cj 0 * (1 / Real.sqrt W)) := by ring
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_left hWs hm0
        nlinarith

/-!
## From the contract hypotheses
-/

/-- (SM) with `LayerFreshBound` from `GaussianAbsorptionContract` and `GaussianLpGradient`
(`layerFreshBound_holds`). -/
theorem b3ClosedContrStepMean_of_gaussianInputs (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hI : B3ClosedContrLayerForm) (hJ : B3ClosedJetLp) :
    B3ClosedContrStepMean :=
  b3ClosedContrStepMean_of_layer (layerFreshBound_holds hGA hLp) hI hJ

/-- (SF) with `LayerFreshBound` from `GaussianAbsorptionContract` and `GaussianLpGradient`
(`layerFreshBound_holds`). -/
theorem b3ClosedContrStepFluct_of_gaussianInputs (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hI : B3ClosedContrLayerForm) (hJ : B3ClosedJetLp) :
    B3ClosedContrStepFluct :=
  b3ClosedContrStepFluct_of_layer (layerFreshBound_holds hGA hLp) hI hJ

/-!
## The decay
-/

/-- **The closed contracting decay from the one-layer bound, the closed layer form and the closed
jets** (with the bound `b3ClosedContrBound_holds`). -/
theorem b3ClosedContrDecay_of_layer (hL : LayerFreshBound) (hI : B3ClosedContrLayerForm)
    (hJ : B3ClosedJetLp) : B3ClosedContrDecay :=
  b3ClosedContrDecay_of_steps (b3ClosedContrStepMean_of_layer hL hI hJ)
    (b3ClosedContrStepFluct_of_layer hL hI hJ) b3ClosedContrBound_holds

/-- **The closed contracting decay from the input hypotheses and the two open closed inputs.** -/
theorem b3ClosedContrDecay_of_gaussianInputs (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hI : B3ClosedContrLayerForm) (hJ : B3ClosedJetLp) :
    B3ClosedContrDecay :=
  b3ClosedContrDecay_of_layer (layerFreshBound_holds hGA hLp) hI hJ

end BlockBand.SourceProcess.PhysApprox.B3DecayIn

