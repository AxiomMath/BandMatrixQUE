module

public import BlockBand.SourceProcess.FullSource.WeightedStep
public import BlockBand.SourceProcess.FullSource.PathSetup

/-!
# The stopped weighted tag recursion along the path

Law `growthPathLaw W b`; a tag of birth index `k`, its mass `t_j = W⁻¹Re Tr Y_{j;k}` and the
path scalar `δ_j = δ₀(X_j)`. The stopping event `G_j = {δ_i ≤ d, k+1 ≤ i ≤ j}` is a past
event (`stopEv_eq`). With the weight `Z_j = (1 + Kδ_j)t_j^n`,
`stopped_tag_step`: `E[1_{G_{j+1}}Z_{j+1}] ≤ (1 + α/W) E[1_{G_j}Z_j]` for `j ≥ k+1`, from the
one-layer bounds bundled in `TagLayerBounds` (Fubini over `pastLaw ⊗ freshLaw`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- The tag mass `t_j = W⁻¹Re Tr Y_{j;k}`. -/
def tagMass (b E : ℝ) (W j k : ℕ) (ω : GrowthPath W) : ℝ :=
  (W : ℝ)⁻¹ * (tagResponse b E W j k ω).trace.re

/-- The path scalar `δ_j = δ₀(X_j)`. -/
def pathDelta (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ := jetDistance0 b E (pathX b E W j ω)

/-- The stopping event `G_j = {δ_i ≤ d for k+1 ≤ i ≤ j}`. -/
def stopEv (b E : ℝ) (W k : ℕ) (d : ℝ) (j : ℕ) : Set (GrowthPath W) :=
  {ω | ∀ i, k + 1 ≤ i → i ≤ j → pathDelta b E W i ω ≤ d}

/-- The stopping event as a set of past coordinates. -/
def stopPast (b E : ℝ) (W k : ℕ) (d : ℝ) (j : ℕ) : Set (PastSample W j) :=
  {p | ∀ i (h : i ≤ j), k + 1 ≤ i →
    jetDistance0 b E (pastX b E (fun _ => 0) W i (restrictPast h p)) ≤ d}

/-- The weight `Z_j = (1 + Kδ_j) t_j^n`. -/
def tagWeight (b E : ℝ) (W k n : ℕ) (K : ℝ) (j : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * pathDelta b E W j ω) * tagMass b E W j k ω ^ n)

theorem stopEv_eq (b E : ℝ) (k : ℕ) (d : ℝ) (j : ℕ) :
    stopEv b E W k d j = pastCoords W j ⁻¹' stopPast b E W k d j := by
  ext ω
  simp only [stopEv, stopPast, Set.mem_ofPred_eq, Set.mem_preimage, pathDelta, pathX,
    pathNearSchur_eq_past, ← pastCoords_restrict]
  exact ⟨fun h i hi hik => h i hik hi, fun h i hik hi => h i hi hik⟩

theorem measurableSet_stopPast (b E : ℝ) (k : ℕ) (d : ℝ) (j : ℕ) :
    MeasurableSet (stopPast b E W k d j) := by
  have : stopPast b E W k d j = ⋂ i, ⋂ (h : i ≤ j), ⋂ (_ : k + 1 ≤ i),
      {p | jetDistance0 b E (pastX b E (fun _ => 0) W i (restrictPast h p)) ≤ d} := by
    ext p; simp [stopPast]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ =>
    measurableSet_le ((measurable_jetDistance0 b E).comp
      ((measurable_pastX b E _ i).comp (measurable_restrictPast h))) measurable_const

theorem stopEv_succ_subset (b E : ℝ) (k : ℕ) (d : ℝ) (j : ℕ) :
    stopEv b E W k d (j + 1) ⊆ stopEv b E W k d j :=
  fun _ h i hi hij => h i hi (by omega)

theorem pastX_zero_eq (b E : ℝ) (j : ℕ) (p : PastSample W j) :
    pastX b E (fun _ => 0) W j p = nearSchur (boundaryZ b E) (pastXX E W j p) := by
  rw [pastX, pastXX, absorbedPathSchur, absorptionDiag_zero, add_zero, pathSchur]

/-- The one-layer inputs of the tag recursion at one width, bundled (they follow from
`FullSourceEstimates`, `PassiveMeanStep` and `PassiveFluctuationStep`). -/
structure TagLayerBounds (b E : ℝ) (W n : ℕ) (Ca C₂ Cn CN₂ CN Cf Cm ρ d₀ : ℝ) : Prop where
  mean : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤
      Ca * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2)
  fl₂ : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d₀ → ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (C₂ / Real.sqrt W * vecNorm u * vecNorm v)
  fln : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d₀ → ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal n) (freshLaw W b) ≤
        ENNReal.ofReal (Cn / Real.sqrt W * vecNorm u * vecNorm v)
  N₂ : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤ ENNReal.ofReal CN₂
  N : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
    eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * n) : ℕ) : ℝ))
      (freshLaw W b) ≤ ENNReal.ofReal CN
  xi : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
    eLpNorm (freshXi b E X) (ENNReal.ofReal 2) (freshLaw W b) ≤ ENNReal.ofReal (Cf / W)
  meanStep : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
    ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
      ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2

/-- The fresh integrand of the weighted step at past `p`. -/
def tagPhi (b E : ℝ) (W j k n : ℕ) (K ρ Cm : ℝ)
    (q : PastSample W j × LayerSample W .oneBlockOnePort) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) +
      Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2)) *
    tagPlus b E (pastXX E W j q.1) (pastS b E W j k q.1) q.2 ^ n)

theorem measurable_tagPhi (b E : ℝ) (j k n : ℕ) (K ρ Cm : ℝ) :
    Measurable (tagPhi b E W j k n K ρ Cm) := by
  have hXX : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      pastXX E W j q.1 := (measurable_pastXX E j).comp measurable_fst
  have hX := measurable_nearSchur_comp (boundaryZ b E) hXX
  have hδ := (measurable_jetDistance0 b E).comp hX
  have hF : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshPortTrace b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 :=
    measurable_freshPortTrace_comp b E hX measurable_snd
  have hI : Measurable fun p : PastSample W j =>
      ∫ f, freshPortTrace b E (nearSchur (boundaryZ b E) (pastXX E W j p)) f ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hξ : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshXi b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 :=
    (hF.sub (hI.comp measurable_fst)).norm
  have hN := measurable_freshTransport_comp b E hXX measurable_snd
  have hSN := measurable_matrix_mul' ((measurable_pastS b E j k).comp measurable_fst) hN
  have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hSN) hSN
  have ht : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      tagPlus b E (pastXX E W j q.1) (pastS b E W j k q.1) q.2 := by
    unfold tagPlus
    simp only [Matrix.trace, Matrix.diag]
    exact measurable_const.mul (Complex.measurable_re.comp
      (Finset.measurable_sum _ fun i _ => hT.eval_matrix))
  unfold tagPhi
  exact ((measurable_const.add (measurable_const.mul (((measurable_const.mul hδ).add
    measurable_const).add hξ))).mul (ht.pow_const n)).ennreal_ofReal

end BlockBand.SourceProcess.FullSource
