module

public import BlockBand.Transmission.PathScalar.OneStep
public import BlockBand.Transmission.PathScalar.ProductLp
public import BlockBand.Transmission.PathScalar.Superexp

/-!
# One step of the absorbed near-end recursion: inputs, fresh errors and their moments

For the growth step `j → j+1` (`j ≥ 1`) with absorption profile `κ ≥ 0`:
* `stepInput κ j p = X_j(p) - iε'_j`, a function of the past coordinates (`X_j = pathNearSchur`,
  `pathNearSchur_eq_past`); it is passive whenever the past blocks are Hermitian
  (`passiveY_stepInput`), i.e. for `pastLaw`-a.e. `p` (`ae_pastLaw_hermitian`);
* `stepFluct κ j ω = |freshPortTrace(stepInput(past)) (fresh) - E_fresh freshPortTrace|`, the
  fresh error `ξ_{j+1}` of the step; `eLpNorm_stepFluct_le`: from `PassiveFluctuationStep`
  (Fubini over `pastLaw ⊗ freshLaw`, `growthPathLaw_map_past_fresh`), `‖ξ_{j+1}‖_p ≤ C_p/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix ComplexOrder

variable {W : ℕ}

/-- Past coordinates at length `j`. -/
abbrev PastSample (W j : ℕ) :=
  (Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)

/-- `X_j` as a function of the past coordinates. -/
def pastX (b E : ℝ) (κ : ℝ → ℝ) (W j : ℕ) (p : PastSample W j) : Matrix (Fin W) (Fin W) ℂ :=
  nearSchur (boundaryZ b E) (absorbedPathSchur E (layerAbsorption W κ j) (pathOfPast W j p))

theorem pathNearSchur_eq_past (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    pathNearSchur b E κ W j ω = pastX b E κ W j (pastCoords W j ω) := by
  rw [pathNearSchur, pathAt_eq_pathOfPast]; rfl

theorem measurable_pastX (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) : Measurable (pastX b E κ W j) :=
  (measurable_nearSchur_absorbed b E _).comp (measurable_pathOfPast j)

/-- The input of the fresh layer of step `j → j+1`: `X_j - iε'_j`. -/
def stepInput (b E : ℝ) (κ : ℝ → ℝ) (W j : ℕ) (p : PastSample W j) : Matrix (Fin W) (Fin W) ℂ :=
  pastX b E κ W j p - (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1

theorem measurable_stepInput (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (stepInput b E κ W j) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [stepInput, Matrix.sub_apply]
  exact (measurable_pastX b E κ j).eval_matrix.sub measurable_const

/-- A growth sample extending given past coordinates by zero blocks and bonds. -/
def extendPast {j : ℕ} (p : PastSample W j) : GrowthPath W :=
  (fun k => if h : k < j then p.1 ⟨k, h⟩ else 0, fun k => if h : k < j + 1 then p.2 ⟨k, h⟩ else 0)

theorem pastCoords_extendPast {j : ℕ} (p : PastSample W j) : pastCoords W j (extendPast p) = p := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · simp [pastCoords, extendPast]
  · have hk := k.isLt
    simp [pastCoords, extendPast]
    intro h; omega

/-- The set of past samples with Hermitian blocks. -/
def hermPast (W j : ℕ) : Set (PastSample W j) := {p | ∀ k, (p.1 k).IsHermitian}

theorem measurableSet_hermPast (W j : ℕ) : MeasurableSet (hermPast W j) := by
  have : hermPast W j = ⋂ k : Fin j, (fun p : PastSample W j => p.1 k) ⁻¹'
      {M : Matrix (Fin W) (Fin W) ℂ | M.IsHermitian} := by
    ext p; simp [hermPast]
  rw [this]
  exact MeasurableSet.iInter fun k => (measurableSet_isHermitian _).preimage
    ((measurable_pi_apply k).comp measurable_fst)

theorem ae_pastLaw_hermitian (W j : ℕ) (b : ℝ) : ∀ᵐ p ∂pastLaw W j b, p ∈ hermPast W j := by
  rw [← growthPathLaw_map_pastCoords]
  exact (ae_map_iff (p := fun q => q ∈ hermPast W j) (measurable_pastCoords W j).aemeasurable
    (measurableSet_hermPast W j)).2 ((ae_growth_isHermitian W b).mono fun ω h k => h k)

theorem passiveY_pastX {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {κ : ℝ → ℝ}
    (hκ : ∀ s, 0 ≤ κ s) {j : ℕ} {p : PastSample W j} (hp : p ∈ hermPast W j) :
    (passiveY (pastX b E κ W j p)).PosSemidef := by
  have hP : PassiveSample b E κ (extendPast p) := by
    refine ⟨fun k => ?_, hκ, boundaryZ_im_pos hb hE1 hE2⟩
    simp only [extendPast]
    split_ifs
    · exact hp _
    · exact Matrix.isHermitian_zero
  have := pathNearSchur_passive hP j
  rwa [pathNearSchur_eq_past, pastCoords_extendPast] at this

theorem passiveY_stepInput {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {κ : ℝ → ℝ}
    (hκ : ∀ s, 0 ≤ κ s) {j : ℕ} {p : PastSample W j} (hp : p ∈ hermPast W j) :
    (passiveY (stepInput b E κ W j p)).PosSemidef :=
  passiveY_absorb (passiveY_pastX hb hE1 hE2 hκ hp)
    (div_nonneg (hκ _) (sq_nonneg _))

/-!
## The fresh error and its moments
-/

theorem measurable_freshPortTrace_comp {α : Type*} [MeasurableSpace α] (b E : ℝ)
    {X : α → Matrix (Fin W) (Fin W) ℂ} {f : α → LayerSample W .oneBlockOnePort}
    (hX : Measurable X) (hf : Measurable f) :
    Measurable fun a => freshPortTrace b E (X a) (f a) := by
  have hlift : Measurable fun a => (Matrix.of fun (u v : Fin 1 × Fin W) => X a u.2 v.2 :
      Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) :=
    Measurable.of_eval_matrix _ fun u v => hX.eval_matrix
  have hS : Measurable fun a => freshSchur E (X a) (f a) :=
    Measurable.of_eval_matrix _ fun x y =>
      (measurable_layerSchur .oneBlockOnePort E hlift hf).eval_matrix
  have hR : Measurable fun a => passiveResolvent b E (freshSchur E (X a) (f a)) := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub hS.eval_matrix
  simp only [freshPortTrace, Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hR.eval_matrix)

/-- The centred fresh trace on `pastSample × freshSample`. -/
def stepPhi (b E : ℝ) (κ : ℝ → ℝ) (W j : ℕ) (q : PastSample W j × LayerSample W .oneBlockOnePort) :
    ℝ :=
  ‖freshPortTrace b E (stepInput b E κ W j q.1) q.2 -
    ∫ f, freshPortTrace b E (stepInput b E κ W j q.1) f ∂freshLaw W b‖

theorem measurable_stepPhi (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) : Measurable (stepPhi b E κ W j) := by
  have hF : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshPortTrace b E (stepInput b E κ W j q.1) q.2 :=
    measurable_freshPortTrace_comp b E ((measurable_stepInput b E κ j).comp measurable_fst)
      measurable_snd
  have hI : Measurable fun p : PastSample W j =>
      ∫ f, freshPortTrace b E (stepInput b E κ W j p) f ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  exact (hF.sub (hI.comp measurable_fst)).norm

/-- The fresh error `ξ_{j+1}` of the growth step `j → j+1`. -/
def stepFluct (b E : ℝ) (κ : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  stepPhi b E κ W j (pastCoords W j ω, freshSample W j ω)

theorem measurable_stepFluct (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (stepFluct b E κ W j) :=
  (measurable_stepPhi b E κ j).comp ((measurable_pastCoords W j).prodMk (measurable_freshSample W j))

theorem stepFluct_nonneg (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    0 ≤ stepFluct b E κ W j ω := norm_nonneg _

/-- **Moments of the fresh error** from `PassiveFluctuationStep`: `‖ξ_{j+1}‖_p ≤ C/W`, uniformly
in the step, the profile `κ ≥ 0` and `E ∈ bulkInterval κ'`. -/
theorem eLpNorm_stepFluct_le {b E p C : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hp : 0 < p) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (j : ℕ)
    (hfl : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖freshPortTrace b E X ω - ∫ ω', freshPortTrace b E X ω' ∂freshLaw W b‖)
        (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (C / W)) :
    eLpNorm (stepFluct b E κ W j) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal (C / W) := by
  have hg := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have : stepFluct b E κ W j = stepPhi b E κ W j ∘ fun ω => (pastCoords W j ω, freshSample W j ω) := by
    funext ω; simp only [stepFluct, Function.comp]
  rw [this, ← eLpNorm_map_measure (measurable_stepPhi b E κ j).aestronglyMeasurable hg.aemeasurable,
    growthPathLaw_map_past_fresh]
  refine eLpNorm_prod_le_of_section (pastLaw W j b) (freshLaw W b) (measurable_stepPhi b E κ j) hp ?_
  filter_upwards [ae_pastLaw_hermitian W j b] with q hq
  have h := hfl (stepInput b E κ W j q) (passiveY_stepInput hb hE1 hE2 hκ hq)
  unfold stepPhi
  exact h

end BlockBand.Transmission.PathScalar
