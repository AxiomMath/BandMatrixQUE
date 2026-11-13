module

public import BlockBand.SourceProcess.FullSource.SqWeighted
public import BlockBand.SourceProcess.FullSource.TagIter

/-!
# The stopped weighted tag-square recursion along the path

Law `growthPathLaw W b`; a tag of birth index `k`, its square `h_j = W⁻¹Re Tr Y_{j;k}²`
(`tagSq`), its mass `t_j` (`tagMass`), the stopping event `G_j` (`stopEv`, as for the tag mass)
and the weight `Z^h_j = (1 + Kδ_j)h_j` (`sqWeight`).
`stopped_sq_step`: `E[1_{G_{j+1}}Z^h_{j+1}] ≤ (1 + α/W)E[1_{G_j}Z^h_j] + D E t_j²` for
`j ≥ k+1` (Fubini over `pastLaw ⊗ freshLaw`, the one-layer `sq_weighted_layer_step`).
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

/-- The tag square `h_j = W⁻¹Re Tr Y_{j;k}²`. -/
def tagSq (b E : ℝ) (W j k : ℕ) (ω : GrowthPath W) : ℝ :=
  (W : ℝ)⁻¹ * (tagResponse b E W j k ω * tagResponse b E W j k ω).trace.re

theorem tagSq_eq_past (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) :
    tagSq b E W j k ω = sqOf W (pastS b E W j k (pastCoords W j ω)) := by
  rw [tagSq, tagResponse_eq_factor]; rfl

theorem tagSq_nonneg (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) : 0 ≤ tagSq b E W j k ω := by
  rw [tagSq_eq_past]; exact sqOf_nonneg _ _

theorem measurable_tagSq (b E : ℝ) (j k : ℕ) : Measurable (tagSq b E W j k) := by
  have e : tagSq b E W j k = fun ω => sqOf W (pastS b E W j k (pastCoords W j ω)) := by
    funext ω; exact tagSq_eq_past b E j k ω
  rw [e]
  exact measurable_sqOf_comp ((measurable_pastS b E j k).comp (measurable_pastCoords W j))

/-- The weight `Z^h_j = (1 + Kδ_j) h_j`. -/
def sqWeight (b E : ℝ) (W k : ℕ) (K : ℝ) (j : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * pathDelta b E W j ω) * tagSq b E W j k ω)

/-- The weight as a function of the past. -/
def sqPsi (b E : ℝ) (W j k : ℕ) (K : ℝ) (p : PastSample W j) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p))) *
    sqOf W (pastS b E W j k p))

theorem measurable_sqPsi (b E : ℝ) (j k : ℕ) (K : ℝ) : Measurable (sqPsi b E W j k K) := by
  have hX := measurable_nearSchur_comp (boundaryZ b E) (measurable_pastXX (W := W) E j)
  unfold sqPsi
  exact ((measurable_const.add (measurable_const.mul
    ((measurable_jetDistance0 b E).comp hX))).mul
      (measurable_sqOf_comp (measurable_pastS b E j k))).ennreal_ofReal

theorem sqWeight_eq (b E : ℝ) (k : ℕ) (K : ℝ) (j : ℕ) :
    sqWeight b E W k K j = sqPsi b E W j k K ∘ pastCoords W j := by
  funext ω; simp only [sqWeight, sqPsi, Function.comp, tagSq_eq_past, pathDelta_eq_past]

theorem measurable_sqWeight (b E : ℝ) (k : ℕ) (K : ℝ) (j : ℕ) :
    Measurable (sqWeight b E W k K j) := by
  rw [sqWeight_eq]; exact (measurable_sqPsi b E j k K).comp (measurable_pastCoords W j)

/-- The fresh integrand of the weighted square step at past `p`. -/
def sqPhi (b E : ℝ) (W j k : ℕ) (K ρ Cm : ℝ)
    (q : PastSample W j × LayerSample W .oneBlockOnePort) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) +
      Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2)) *
    sqPlus b E (pastXX E W j q.1) (pastS b E W j k q.1) q.2)

theorem measurable_sqPhi (b E : ℝ) (j k : ℕ) (K ρ Cm : ℝ) :
    Measurable (sqPhi b E W j k K ρ Cm) := by
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
  have ht : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      sqPlus b E (pastXX E W j q.1) (pastS b E W j k q.1) q.2 := measurable_sqOf_comp hSN
  unfold sqPhi
  exact ((measurable_const.add (measurable_const.mul (((measurable_const.mul hδ).add
    measurable_const).add hξ))).mul ht).ennreal_ofReal

end BlockBand.SourceProcess.FullSource
