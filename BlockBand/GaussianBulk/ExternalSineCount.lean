module

public import Mathlib
public import BlockBand.Wegner.ProjectedWegnerGUECount
public import BlockBand.Internal.Contracts.Inputs

/-!
# PSSS factorial counts for the deformed GUE

The counting bound for the deformed GUE, which gives uniform exponential moments of local
eigenvalue counts in the external-source sine-kernel theorem.

Law: `deformedGUELaw N t F hF`, the image of the Johansson coordinate product
`coordinateMeasure N (t/N)` under `z ↦ F + G(z)` (diagonal real variance `t/N`, strict-upper
real and imaginary variances `t/(2N)`), i.e. `F + √t G_N` with `G_N` the normalized GUE.
Domain: `N > 0`, `t > 0`, every Hermitian `F` (no norm bound), every closed `[a,b]`, `a ≤ b`,
every order `r ≥ 1`. Observable: the multiplicity count of eigenvalues in `[a,b]`.
Uniformity: one constant `C > 0` (the PSSS constant) is chosen before everything else.
Bound: `E (n)_r ≤ (C/√t · N · (b-a))^r`. Only `PSSS.SourceContract` is used, through the
one-block law `Wegner.ProjectedGUE.gueLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Counting BlockBand.Wegner BlockBand.Wegner.ProjectedGUE
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- The deformed Gaussian sample `F + G(z)` on Johansson coordinates. -/
def deformedSample {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    (z : Johansson.UpperPair N → ℝ × ℝ) : Johansson.HermitianMatrix N :=
  ⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩

/-- The deformed Gaussian sample is Borel measurable in the Johansson coordinates. -/
theorem measurable_deformedSample {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    Measurable (deformedSample F hF) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro i j
  have h := measurable_subtype_coe.comp (Johansson.measurable_gaussianMatrix (N := N))
  exact measurable_const.add ((Matrix.measurable_iff.mp h) i j)

/-- `deformedGUELaw` is the image of the Johansson coordinate product at `S = t/N`. -/
theorem deformedGUELaw_eq_map (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) :
    deformedGUELaw N t F hF =
      (Johansson.coordinateMeasure N (Johansson.sourceTime N t)).map (deformedSample F hF) :=
  rfl

/-- `deformedGUELaw` is a probability measure (every `N`, `t`, Hermitian `F`). -/
theorem isProbabilityMeasure_deformedGUELaw (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) : IsProbabilityMeasure (deformedGUELaw N t F hF) := by
  have := Johansson.coordinateMeasure_probability N (Johansson.sourceTime N t)
  rw [deformedGUELaw_eq_map]
  constructor
  rw [Measure.map_apply (measurable_deformedSample F hF) MeasurableSet.univ]
  simp

/-- The source time `t/N` is the coordinate variance `coordVar N t` of `gueLaw`. -/
theorem sourceTime_eq_coordVar (N : ℕ) (t : ℝ≥0) :
    Johansson.sourceTime N t = coordVar N (t : ℝ) := by
  ext
  rw [Johansson.sourceTime_coe, coordVar, Real.coe_toNNReal _ (by positivity)]

/-- PSSS factorial moments for `F + √t G_N`. One absolute `C > 0` first; then `N > 0`, `t > 0`, every
Hermitian `F` without a norm bound, every `a ≤ b` and `r ≥ 1`. Law `deformedGUELaw N t F hF`.
Conclusion: the `r`-th factorial moment of the eigenvalue count in `[a,b]` is at most
`(C/√t · N · (b-a))^r`. Only `PSSS.SourceContract` is used. -/
theorem deformedGUELaw_factorialCount_le (source : PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (t : ℝ≥0), 0 < t →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (a b : ℝ), a ≤ b →
      ∀ r : ℕ, 1 ≤ r →
        (∫ A, ((PSSS.eigenCount A (Icc a b)).descFactorial r : ℝ) ∂deformedGUELaw N t F hF) ≤
          (C / Real.sqrt t * (N : ℝ) * (b - a)) ^ r := by
  refine ⟨source.C, source.C_pos, ?_⟩
  intro N hN t ht F hF a b hab r hr
  have hc : (0 : ℝ) < t := ht
  set s : ℝ := (Real.sqrt t)⁻¹ with hs_def
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  let M := gueLaw hN (t : ℝ) hc
  let D : PSSS.HermitianMatrix (Index (oneBlock N)) := hermitianReindex (toFin N).symm ⟨F, hF⟩
  let A₀ := hermitianScale s D
  let I : Set ℝ := Icc (s * a) (s * b)
  have hcount : ∀ z : Johansson.UpperPair N → ℝ × ℝ,
      eigenCount (deformedSample F hF z) (Icc a b) = intervalCount M A₀ I z := by
    intro z
    have h1 : intervalCount M A₀ I z = sumCount (Icc a b)
        (D, hermitianReindex (toFin N).symm (Johansson.gaussianMatrix z)) :=
      sumCount_scale s hs a b (D, hermitianReindex (toFin N).symm (Johansson.gaussianMatrix z))
    have h2 := nativeEigenCount_hermitianReindex (toFin N).symm
      (deformedSample F hF z : PSSS.HermitianMatrix (Fin N)) (Icc a b)
    calc eigenCount (deformedSample F hF z) (Icc a b)
        = eigenCount (hermitianReindex (toFin N).symm (deformedSample F hF z)) (Icc a b) :=
          h2.symm
      _ = sumCount (Icc a b)
          (D, hermitianReindex (toFin N).symm (Johansson.gaussianMatrix z)) := rfl
      _ = intervalCount M A₀ I z := h1.symm
  have hb := source.factorialBound (oneBlock_pos hN) M A₀ (s * a) (s * b)
    (mul_le_mul_of_nonneg_left hab hs.le) r hr
  unfold FactorialMomentBound at hb
  have hmeas : Measurable (fun A : Johansson.HermitianMatrix N =>
      ((PSSS.eigenCount A (Icc a b)).descFactorial r : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n.descFactorial r : ℝ))).comp
      (measurable_nativeEigenCount (Icc a b) measurableSet_Icc)
  rw [deformedGUELaw_eq_map, integral_map (measurable_deformedSample F hF).aemeasurable
    hmeas.aestronglyMeasurable, sourceTime_eq_coordVar]
  have hlhs : (∫ z, ((PSSS.eigenCount (deformedSample F hF z) (Icc a b)).descFactorial r : ℝ)
        ∂(Johansson.coordinateMeasure N (coordVar N (t : ℝ)))) =
      ∫ z, factorialCount (intervalCount M A₀ I) r z ∂M.P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      simp only [factorialCount]
      rw [hcount z]
  rw [hlhs]
  refine hb.trans (le_of_eq ?_)
  rw [card_index, hs_def]
  ring

end BlockBand.GaussianBulk
