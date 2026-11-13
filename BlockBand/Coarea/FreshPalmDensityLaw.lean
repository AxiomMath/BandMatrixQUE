module

public import BlockBand.Coarea.PoleExclusionLaw
public import BlockBand.Coarea.GUELaw
public import BlockBand.Model.Construction.GaussianCompatibility

/-!
# Scalar-part decomposition of `GUE_N(t)` on `Fin N`

*Measures.* `gueMeasure (Fin d) t` and `scalarShiftLaw (Fin d) t v`
(`BlockBand.Coarea.PoleExclusion`). *Domain.* every `d ≥ 1`, `t : ℝ≥0`, `v = t/d`. Exact
measure identity, no limit.

* `measure_eq_of_gueTestPairing`: two probability laws on `Matrix (Fin d) (Fin d) ℂ`, both
  supported on Hermitian matrices, with the same characteristic function against every
  `gueTestPairing Fin.val` coincide (coordinates `coordsOfMatrix`, Mathlib uniqueness of
  finite-dimensional characteristic functions).
* **`scalarShiftLaw_fin_eq_gueMeasure`**: `scalarShiftLaw (Fin d) t v = gueMeasure (Fin d) t`
  for `(v : ℝ) = t/d`, `d ≥ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FreshPalm

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
  BlockBand.Coarea.ContractClauses BlockBand.Coarea.PoleExclusion
open CoareaNative.BlockBand (StrictUpperIndex HermitianCoordinate hermitianMatrixOfCoordinates)
open scoped ENNReal NNReal

variable {d : ℕ}

/-- Diagonal test coefficients read off a coordinate test vector. -/
def coordD (q : HermitianCoordinate d → ℝ) : Fin d → ℝ := fun a => q (.inl a)

/-- Real strict-upper test coefficients. -/
def coordU (q : HermitianCoordinate d → ℝ) : Fin d → Fin d → ℝ := fun a b =>
  if h : a < b then q (.inr (.inl ⟨(a, b), h⟩)) else 0

/-- Imaginary strict-upper test coefficients. -/
def coordV (q : HermitianCoordinate d → ℝ) : Fin d → Fin d → ℝ := fun a b =>
  if h : a < b then q (.inr (.inr ⟨(a, b), h⟩)) else 0

theorem sum_strictUpper (g : Fin d × Fin d → ℝ) :
    ∑ ij : StrictUpperIndex d, g ij.1 = ∑ a, ∑ b, if a < b then g (a, b) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun ij : Fin d × Fin d => ij.1 < ij.2)
    (by intro x; simp) g, Finset.sum_filter, Fintype.sum_prod_type]

/-- Every linear test of the coordinates is a `gueTestPairing` with `κ = Fin.val`. -/
theorem sum_mul_coordsOfMatrix (q : HermitianCoordinate d → ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, q k * coordsOfMatrix A k =
      gueTestPairing (fun a : Fin d => a.val) (coordD q) (coordU q) (coordV q) A := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  unfold gueTestPairing
  have h1 : ∑ ij : StrictUpperIndex d, q (.inr (.inl ij)) * coordsOfMatrix A (.inr (.inl ij)) =
      ∑ ij : StrictUpperIndex d, (fun x : Fin d × Fin d =>
        coordU q x.1 x.2 * (A x.1 x.2).re) ij.1 := by
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [coordU, coordsOfMatrix, ij.2]
  have h2 : ∑ ij : StrictUpperIndex d, q (.inr (.inr ij)) * coordsOfMatrix A (.inr (.inr ij)) =
      ∑ ij : StrictUpperIndex d, (fun x : Fin d × Fin d =>
        coordV q x.1 x.2 * (A x.1 x.2).im) ij.1 := by
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [coordV, coordsOfMatrix, ij.2]
  rw [h1, h2, sum_strictUpper (fun x : Fin d × Fin d => coordU q x.1 x.2 * (A x.1 x.2).re),
    sum_strictUpper (fun x : Fin d × Fin d => coordV q x.1 x.2 * (A x.1 x.2).im),
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a < b
  · have h' : a.val < b.val := h
    simp [h, h']
  · have h' : ¬ a.val < b.val := h
    simp [h, h']

/-- Uniqueness from the `gueTestPairing` characteristic functions on Hermitian-supported laws. -/
theorem measure_eq_of_gueTestPairing (μ ν : Measure (Matrix (Fin d) (Fin d) ℂ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ A ∂μ, A.IsHermitian) (hν : ∀ᵐ A ∂ν, A.IsHermitian)
    (h : ∀ (D : Fin d → ℝ) (U V : Fin d → Fin d → ℝ),
      ∫ A, Complex.exp (Complex.I * (gueTestPairing (fun a : Fin d => a.val) D U V A : ℂ)) ∂μ =
        ∫ A, Complex.exp (Complex.I * (gueTestPairing (fun a : Fin d => a.val) D U V A : ℂ)) ∂ν) :
    μ = ν := by
  have hrec : ∀ ρ : Measure (Matrix (Fin d) (Fin d) ℂ), (∀ᵐ A ∂ρ, A.IsHermitian) →
      ρ = (ρ.map coordsOfMatrix).map hermitianMatrixOfCoordinates := by
    intro ρ hρ
    rw [Measure.map_map (measurable_hermitianMatrixOfCoordinates d) (measurable_coordsOfMatrix d)]
    have hae : (hermitianMatrixOfCoordinates ∘ coordsOfMatrix) =ᵐ[ρ] id := by
      filter_upwards [hρ] with A hA
      exact hermitianMatrixOfCoordinates_coordsOfMatrix hA
    rw [Measure.map_congr hae, Measure.map_id]
  have hc : μ.map coordsOfMatrix = ν.map coordsOfMatrix := by
    have : IsProbabilityMeasure (μ.map coordsOfMatrix) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_coordsOfMatrix d).aemeasurable).2 inferInstance
    have : IsProbabilityMeasure (ν.map coordsOfMatrix) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_coordsOfMatrix d).aemeasurable).2 inferInstance
    apply BlockBand.Parameters.finiteReal_measure_eq_of_characteristic
    intro q
    have hm : Measurable fun z : HermitianCoordinate d → ℝ =>
        Complex.exp (Complex.I * ((∑ i, q i * z i : ℝ) : ℂ)) := by fun_prop
    rw [integral_map (measurable_coordsOfMatrix d).aemeasurable hm.aestronglyMeasurable,
      integral_map (measurable_coordsOfMatrix d).aemeasurable hm.aestronglyMeasurable]
    simp_rw [sum_mul_coordsOfMatrix]
    exact h _ _ _
  rw [hrec μ hμ, hrec ν hν, hc]

/-- **Scalar-part decomposition on `Fin d`**: `G⁰ + ζ I` with `G⁰ ~ GUE_d(t).map tracelessPart`
and an independent `ζ ~ N(0, t/d)` has law `GUE_d(t)`. -/
theorem scalarShiftLaw_fin_eq_gueMeasure (hd : 0 < d) (t v : ℝ≥0)
    (hv : (v : ℝ) = (t : ℝ) / d) :
    scalarShiftLaw (Fin d) t v = gueMeasure (Fin d) t := by
  have hκ : Function.Injective (fun a : Fin d => a.val) := Fin.val_injective
  have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]; exact_mod_cast hd.ne'
  have hv' : (v : ℝ) = (t : ℝ) / Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hv
  apply measure_eq_of_gueTestPairing
  · exact ae_isHermitian_scalarShiftLaw t v
  · exact ae_isHermitian_gueMeasure t
  · intro D U V
    rw [integral_exp_gueTestPairing_scalarShiftLaw _ hκ t v hcard hv' D U V,
      integral_exp_gueTestPairing _ hκ]

end BlockBand.Coarea.FreshPalm
