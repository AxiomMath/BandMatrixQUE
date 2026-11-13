module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalProjectedWegnerInstantiation
public import Mathlib.Probability.IdentDistribIndep

/-!
# Exterior-coordinate Schur instantiation for the Gaussian ring

For a fixed physical block, the exterior randomness is chosen canonically as
the complete vector of upper-triangular coordinates outside that block, with
its pushforward probability law.  The normalized diagonal block is independent
of this vector.  This module proves the measure-theoretic replacement lemma
which turns that independence into the product-space `IdentDistrib` required
by projected Wegner averaging.

The only remaining model-specific datum is deterministic: a measurable Schur
trace as a function of the exterior vector and an arbitrary normalized exposed
matrix, together with its pointwise identification with the physical trace.
No disintegration or conditional probability assertion remains.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Independent random variables have the same joint law as two independent
copies on the product of the first marginal law and the original space. -/
theorem identDistrib_independent_with_fresh_copy
    {Ω Ω' Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace Ξ] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Ξ) (Y : Ω → E) (Z : Ω' → E)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y μ) (hYZ : IdentDistrib Y Z μ ν) :
    IdentDistrib (fun ω => (X ω, Y ω))
      (fun p : Ξ × Ω' => (p.1, Z p.2)) μ ((μ.map X).prod ν) := by
  refine ⟨(hX.prodMk hY).aemeasurable,
    (measurable_fst.prodMk (hZ.comp measurable_snd)).aemeasurable, ?_⟩
  rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  change (μ.map X).prod (μ.map Y) =
    Measure.map (Prod.map id Z) ((μ.map X).prod ν)
  rw [← Measure.map_prod_map (μ.map X) ν measurable_id hZ]
  rw [Measure.map_id]
  exact congrArg ((μ.map X).prod ·) hYZ.map_eq

/-- Canonical exterior-coordinate probability law for physical block `j`. -/
def Law.exteriorCoordinateLaw
    {p : Params} (M : Law.{0} p) (j : ZMod p.n) :
    Measure (exteriorUpperPairs p j → ℂ) :=
  M.P.map (M.exteriorUpperCoordinates j)

instance Law.exteriorCoordinateLaw_isProbabilityMeasure
    {p : Params} (M : Law.{0} p) (j : ZMod p.n) :
    IsProbabilityMeasure (M.exteriorCoordinateLaw j) := by
  rw [Law.exteriorCoordinateLaw]
  infer_instance

/-- The exterior coordinate vector and normalized singleton GUE block are
independent. -/
theorem Law.indepFun_exterior_normalizedSingletonBlock
    {p : Params} (M : Law.{0} p) (j : ZMod p.n) :
    IndepFun (M.exteriorUpperCoordinates j)
      (M.normalizedSingletonBlock j) M.P := by
  have hsub : Measurable
      (fun A : Matrix (Fin p.W) (Fin p.W) ℂ =>
        A.submatrix (fun a : BlockGUE.Index (singletonBlockSize p.W) => a.2)
          (fun a : BlockGUE.Index (singletonBlockSize p.W) => a.2)) := by
    rw [Matrix.measurable_iff]
    intro a b
    exact (measurable_pi_apply b.2).comp (measurable_pi_apply a.2)
  have h := (M.indepFun_normalizedDiagonalBlock_exterior j).symm.comp
    measurable_id hsub
  have hfun :
      (fun ω => (M.normalizedDiagonalBlock j ω).submatrix
        (fun a : BlockGUE.Index (singletonBlockSize p.W) => a.2)
        (fun a : BlockGUE.Index (singletonBlockSize p.W) => a.2)) =
        M.normalizedSingletonBlock j := rfl
  simp only [Function.comp_def, id_eq] at h
  rw [hfun] at h
  exact h

/-- Joint law of the exterior vector and normalized singleton block as
an independent fresh product. -/
theorem Law.identDistrib_exterior_normalizedSingletonBlock
    {p : Params} (M : Law.{0} p) (j : ZMod p.n) :
    IdentDistrib
      (fun ω => (M.exteriorUpperCoordinates j ω,
        M.normalizedSingletonBlock j ω))
      (fun z : (exteriorUpperPairs p j → ℂ) ×
          (M.normalizedDiagonalBlockGUECoupling j).exposed.Ω =>
        (z.1, (M.normalizedDiagonalBlockGUECoupling j).exposed.G z.2))
      M.P ((M.exteriorCoordinateLaw j).prod
        (M.normalizedDiagonalBlockGUECoupling j).exposed.P) := by
  exact identDistrib_independent_with_fresh_copy M.P
    (M.normalizedDiagonalBlockGUECoupling j).exposed.P
    (M.exteriorUpperCoordinates j) (M.normalizedSingletonBlock j)
    (M.normalizedDiagonalBlockGUECoupling j).exposed.G
    (M.measurable_exteriorUpperCoordinates j)
    (M.measurable_normalizedSingletonBlock j)
    (by
      rw [Matrix.measurable_iff]
      exact (M.normalizedDiagonalBlockGUECoupling j).exposed.measurable_entry)
    (M.indepFun_exterior_normalizedSingletonBlock j)
    (M.normalizedDiagonalBlockGUECoupling j).identDistrib

/-- A Schur trace written directly as a function of the exterior coordinates
and an arbitrary normalized exposed matrix. -/
def schurMatrixTrace {p : Params} (j : ZMod p.n)
    (background : (exteriorUpperPairs p j → ℂ) →
      HermitianMatrix (BlockGUE.Index (singletonBlockSize p.W)))
    (absorber : (exteriorUpperPairs p j → ℂ) →
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (η : ℝ)
    (z : (exteriorUpperPairs p j → ℂ) ×
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ) : ℝ :=
  -(((((background z.1 : Matrix _ _ ℂ) + z.2) +
    Complex.I • (absorber z.1 + η • (1 : Matrix _ _ ℂ)))⁻¹).trace).im

/-- Evaluation on the canonical exposed law is exactly the conditioned
absorbed trace. -/
theorem schurMatrixTrace_exposed
    {p : Params} (M : Law.{0} p) (j : ZMod p.n)
    (background : (exteriorUpperPairs p j → ℂ) →
      HermitianMatrix (BlockGUE.Index (singletonBlockSize p.W)))
    (absorber : (exteriorUpperPairs p j → ℂ) →
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (η : ℝ) (z : (exteriorUpperPairs p j → ℂ) × M.Ω) :
    schurMatrixTrace j background absorber η
        (z.1, M.normalizedSingletonBlock j z.2) =
      conditionedAbsorbedTrace p.W_pos
        (M.normalizedDiagonalBlockGUECoupling j).exposed
        background absorber η z := by
  simp [schurMatrixTrace, conditionedAbsorbedTrace, BlockGUE.absorbedTrace,
    BlockGUE.deformed, Law.normalizedDiagonalBlockGUECoupling,
    GaussianRing.normalizedDiagonalBlockGUECoupling,
    Law.normalizedDiagonalBlockGUE, Law.normalizedSingletonBlock]

/-- Minimal deterministic Schur input.  The difficult physical block algebra is
now isolated as a pointwise factorization through the exterior coordinates and
normalized exposed matrix.  The probabilistic product replacement is proved,
not assumed. -/
structure PhysicalSchurMatrixData
    {p : Params} (M : Law.{0} p) (g : ZMod p.n → M.Ω → ℝ) (η : ℝ) where
  background : ∀ j, (exteriorUpperPairs p j → ℂ) →
    HermitianMatrix (BlockGUE.Index (singletonBlockSize p.W))
  absorber : ∀ j, (exteriorUpperPairs p j → ℂ) →
    Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ
  absorber_pos : ∀ j ξ, (absorber j ξ).PosSemidef
  measurable_schurMatrixTrace : ∀ j,
    Measurable (schurMatrixTrace j (background j) (absorber j) η)
  physical_trace_eq : ∀ j ω,
    g j ω = schurMatrixTrace j (background j) (absorber j) η
      (M.exteriorUpperCoordinates j ω, M.normalizedSingletonBlock j ω)

/-- The canonical exterior-coordinate construction discharges the full
projected-Wegner instantiation interface. -/
def PhysicalSchurMatrixData.toProjectedWegnerInstantiation
    {p : Params} (M : Law.{0} p) {g : ZMod p.n → M.Ω → ℝ} {η : ℝ}
    (h : PhysicalSchurMatrixData M g η) :
    PhysicalProjectedWegnerInstantiation M g η where
  Exterior j := exteriorUpperPairs p j → ℂ
  exteriorLaw j := M.exteriorCoordinateLaw j
  background := h.background
  absorber := h.absorber
  absorber_pos := h.absorber_pos
  joint_measurable j := by
    have heq :
        conditionedAbsorbedTrace p.W_pos
          (M.normalizedDiagonalBlockGUECoupling j).exposed
          (h.background j) (h.absorber j) η =
        fun z => schurMatrixTrace j (h.background j) (h.absorber j) η
          (z.1, (M.normalizedDiagonalBlockGUECoupling j).exposed.G z.2) := by
      funext z
      exact (schurMatrixTrace_exposed M j
        (h.background j) (h.absorber j) η z).symm
    rw [heq]
    exact (h.measurable_schurMatrixTrace j).comp
      (measurable_fst.prodMk
        ((M.measurable_normalizedSingletonBlock j).comp measurable_snd))
  trace_identDistrib j := by
    have hpair := M.identDistrib_exterior_normalizedSingletonBlock j
    have htrace := hpair.comp (h.measurable_schurMatrixTrace j)
    rw [show g j = schurMatrixTrace j (h.background j) (h.absorber j) η ∘
        (fun ω => (M.exteriorUpperCoordinates j ω,
          M.normalizedSingletonBlock j ω)) by
      funext ω
      exact h.physical_trace_eq j ω]
    have heq :
        conditionedAbsorbedTrace p.W_pos
          (M.normalizedDiagonalBlockGUECoupling j).exposed
          (h.background j) (h.absorber j) η =
        fun z => schurMatrixTrace j (h.background j) (h.absorber j) η
          (z.1, (M.normalizedDiagonalBlockGUECoupling j).exposed.G z.2) := by
      funext z
      exact (schurMatrixTrace_exposed M j
        (h.background j) (h.absorber j) η z).symm
    rw [heq]
    simpa only [Function.comp_def] using htrace

/-- Sharp projected-Wegner estimate from the minimal pointwise Schur
factorization. -/
theorem projectedWegner_gaussianRing_of_schurMatrixData
    (input : PSSSInput.{0})
    {p : Params} (M : Law.{0} p) {g : ZMod p.n → M.Ω → ℝ}
    {η : ℝ} (hη : 0 < η) (h : PhysicalSchurMatrixData M g η)
    (B : Finset (ZMod p.n)) (hproj : ProjectedTraceDecomposition g B) :
    ∫ ω, hproj.projectedTrace ω ∂M.P ≤
      Real.pi * input.C * (p.W : ℝ) * (B.card : ℝ) :=
  projectedWegner_gaussianRing_of_schurInstantiation input M hη
    h.toProjectedWegnerInstantiation B hproj

end GaussianRing
end CoareaNative.BlockBand
