module

public import BlockBand.Coarea.FixedOmegaDecode

/-!
# Fixed-`ω` coarea: measurability and the complementary-block Gaussian integral

Support lemmas for the fixed-`ω` coarea formula `CoareaContract.formula_fixed`.

*Measures.* Lebesgue measure on the coordinates `HermitianCoordinateSpace m` and
`gueMeasure (Fin m) t` (`GUE_m(t)`, `t > 0`).

## Main results

* `measurable_negativeCount`: the contract's `N_-` is Borel measurable on all matrices.
* `measurable_fiberIntegrand`: joint measurability of the contract `G'`-integrand for a
  measurable frame map `U`, measurable scalar `K` and measurable `g`.
* `lintegral_translated_gueDensity` (translation `B = F_v + G'`): for Hermitian `A`,
  `∫ Z_m(t)⁻¹ e^{-‖B - A‖²/(2t)} Θ(B - A) dB = ∫ Θ dGUE_m(t)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open scoped ENNReal NNReal ComplexConjugate

/-!
## Measurability of `N_-`
-/

theorem measurable_matrix_add {α : Type*} [MeasurableSpace α] {m n : Type*}
    {f g : α → Matrix m n ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x + g x) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.add_apply]
  exact (Matrix.measurable_iff.mp hf i j).add (Matrix.measurable_iff.mp hg i j)

theorem measurable_matrix_sub {α : Type*} [MeasurableSpace α] {m n : Type*}
    {f g : α → Matrix m n ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x - g x) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.sub_apply]
  exact (Matrix.measurable_iff.mp hf i j).sub (Matrix.measurable_iff.mp hg i j)

theorem measurable_matrix_smul {α : Type*} [MeasurableSpace α] {m n : Type*}
    {f : α → Matrix m n ℂ} (hf : Measurable f) (c : ℂ) :
    Measurable (fun x => c • f x) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.smul_apply]
  exact (Matrix.measurable_iff.mp hf i j).const_smul c

theorem measurableSet_isHermitian (ι : Type*) [Fintype ι] :
    MeasurableSet {M : Matrix ι ι ℂ | M.IsHermitian} := by
  have : {M : Matrix ι ι ℂ | M.IsHermitian} = ⋂ i, ⋂ j, {M | star (M j i) = M i j} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian, ← Matrix.ext_iff,
      Matrix.conjTranspose_apply]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  exact measurableSet_eq_fun (Complex.continuous_conj.measurable.comp
    (Matrix.measurable_apply (i := j) (j := i))) (Matrix.measurable_apply (i := i) (j := j))

theorem measurable_negativeCount (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measurable (negativeCount : Matrix ι ι ℂ → ℕ) := by
  classical
  have hrw : (negativeCount : Matrix ι ι ℂ → ℕ) = fun M =>
      if hM : M ∈ {M : Matrix ι ι ℂ | M.IsHermitian} then
        inertia (⟨M, hM⟩ : HermitianMatrix ι) else (fun _ => 0) (⟨M, hM⟩ : {M : Matrix ι ι ℂ //
          M ∈ {M : Matrix ι ι ℂ | M.IsHermitian}ᶜ}) := by
    funext M
    by_cases hM : M.IsHermitian
    · have h1 : M ∈ {M : Matrix ι ι ℂ | M.IsHermitian} := hM
      simp only [h1, ↓reduceDIte]
      rw [inertia_eq_negativeEigenvalueCount, negativeEigenvalueCount_eq_negativeCount]
    · have h1 : M ∉ {M : Matrix ι ι ℂ | M.IsHermitian} := hM
      simp only [h1, ↓reduceDIte]
      unfold negativeCount
      simp [hM]
  rw [hrw]
  refine Measurable.dite ?_ measurable_const (measurableSet_isHermitian ι)
  exact (measurable_inertia (ι := ι)).comp (measurable_subtype_coe.subtype_mk)

theorem measurable_indicator_negativeCount {α : Type*} [MeasurableSpace α] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {M : α → Matrix ι ι ℂ} (hM : Measurable M) (n k : ℕ) :
    Measurable (fun x => if negativeCount (M x) + n = k then (1 : ℝ≥0∞) else 0) := by
  have h := (measurable_negativeCount ι).comp hM
  exact Measurable.ite (measurableSet_eq_fun (h.add_const n) measurable_const) measurable_const
    measurable_const

/-!
## Measurability of the fiber integrand
-/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem measurable_fiberIntegrand {U : (ι → ℂ) → Matrix ι κ ℂ} (hU : Measurable U)
    (F : Matrix ι ι ℂ) (E : ℝ) (nR α : ℕ) {K : (ι → ℂ) → ℝ} (hK : Measurable K)
    {g : Matrix ι ι ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun p : (ι → ℂ) × Matrix κ κ ℂ =>
      fiberIntegrand (U p.1) F E p.1 nR α (K p.1) g p.2) := by
  have hU1 : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ => U p.1 := hU.comp measurable_fst
  have hUh : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ => (U p.1)ᴴ :=
    Measurable.matrix_conjTranspose hU1
  have hA : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ => (U p.1)ᴴ * F * U p.1 :=
    measurable_matrix_mul_rect (measurable_matrix_mul_rect hUh measurable_const) hU1
  have hM : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ =>
      (U p.1)ᴴ * F * U p.1 + p.2 - (E : ℂ) • 1 :=
    measurable_matrix_sub (measurable_matrix_add hA measurable_snd) measurable_const
  have hdet : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ =>
      Complex.normSq ((U p.1)ᴴ * F * U p.1 + p.2 - (E : ℂ) • 1).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hv : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ =>
      vecMulVec p.1 (star p.1) := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [vecMulVec_apply, Pi.star_apply]
    have h1 : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ => p.1 a :=
      (measurable_pi_apply a).comp measurable_fst
    have h2 : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ => p.1 b :=
      (measurable_pi_apply b).comp measurable_fst
    exact h1.mul (Complex.continuous_conj.measurable.comp h2)
  have hrec : Measurable fun p : (ι → ℂ) × Matrix κ κ ℂ =>
      (E : ℂ) • vecMulVec p.1 (star p.1) + U p.1 * ((U p.1)ᴴ * F * U p.1 + p.2) * (U p.1)ᴴ - F :=
    measurable_matrix_sub (measurable_matrix_add (measurable_matrix_smul hv _)
      (measurable_matrix_mul_rect
        (measurable_matrix_mul_rect hU1 (measurable_matrix_add hA measurable_snd)) hUh))
      measurable_const
  unfold fiberIntegrand
  refine Measurable.mul (Measurable.mul ?_ (measurable_indicator_negativeCount hM nR α))
    (hg.comp hrec)
  exact ENNReal.measurable_ofReal.comp ((hK.comp measurable_fst).mul hdet)

/-!
## The complementary-block Gaussian integral
-/

theorem hermitianOfFinCoordinates_sub (m : ℕ) (x y : HermitianCoordinateSpace m) :
    (hermitianOfFinCoordinates m (x - y)).1 =
      (hermitianOfFinCoordinates m x).1 - (hermitianOfFinCoordinates m y).1 := by
  have h := (hermitianFinCoordinatesLinearEquiv m).map_sub x y
  exact congrArg Subtype.val h

/-- **Translation `B = A + G'`**: for Hermitian `A`, `t > 0` and measurable `Θ`,
`∫ Z_m(t)⁻¹ e^{-‖B - A‖²_HS/(2t)} Θ(B - A) dB = ∫ Θ dGUE_m(t)` (Lebesgue on the real
coordinates of `B`). -/
theorem lintegral_translated_gueDensity (m : ℕ) {t : ℝ≥0} (ht : 0 < t)
    {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    {Θ : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞} (hΘ : Measurable Θ) :
    ∫⁻ b : HermitianCoordinateSpace m,
        ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
            ((hermitianOfFinCoordinates m b).1 - A) / (2 * t)) / gueNormalizer m t) *
          Θ ((hermitianOfFinCoordinates m b).1 - A) =
      ∫⁻ G', Θ G' ∂gueMeasure (Fin m) t := by
  rw [lintegral_gueMeasure m ht hΘ]
  set a : HermitianCoordinateSpace m := (hermitianFinCoordinatesLinearEquiv m).symm ⟨A, hA⟩
  have ha : (hermitianOfFinCoordinates m a).1 = A :=
    congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv m).apply_symm_apply ⟨A, hA⟩)
  have hfun : ∀ b : HermitianCoordinateSpace m,
      ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
            ((hermitianOfFinCoordinates m b).1 - A) / (2 * t)) / gueNormalizer m t) *
          Θ ((hermitianOfFinCoordinates m b).1 - A) =
        (fun b' : HermitianCoordinateSpace m => hermitianGUEDensity m t (hermitianGUEBlock m b') *
          Θ (hermitianOfFinCoordinates m b').1) (b - a) := by
    intro b
    simp only [hermitianGUEDensity, hermitianGUEBlock, hermitianOfFinCoordinates_sub, ha]
  simp_rw [hfun]
  exact lintegral_sub_right_eq_self (μ := (volume : Measure (HermitianCoordinateSpace m)))
    (fun b' : HermitianCoordinateSpace m => hermitianGUEDensity m t (hermitianGUEBlock m b') *
      Θ (hermitianOfFinCoordinates m b').1) a

end BlockBand.Coarea.FixedOmega
