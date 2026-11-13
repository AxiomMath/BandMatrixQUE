module

public import Mathlib
public import BlockBand.Wegner.CanonicalBlockGUE
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Counting.NativeCountTransport

/-!
# The PSSS bound conditional on an independent deformation

Proves `ConditionalBlockGUECount` from `PSSS.SourceContract`: if `G/√t` has the canonical
block-GUE law and `D` is a random Hermitian matrix independent of `G`, the factorial moments of the
eigenvalue count of `D + G` on `[a, b]` are at most `(C t^{-1/2} N (b - a))^r`. The deterministic
bound is applied conditionally on `D`, after rescaling by `t^{-1/2}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Counting

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The set of Hermitian matrices is measurable (it is closed). -/
theorem measurableSet_isHermitian :
    MeasurableSet {A : Matrix ι ι ℂ | A.IsHermitian} :=
  (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id).measurableSet

/-- A real positive multiple of a Hermitian matrix. -/
def hermitianScale (s : ℝ) (A : PSSS.HermitianMatrix ι) : PSSS.HermitianMatrix ι :=
  ⟨(s : ℂ) • A.1, A.2.smul (by simp [IsSelfAdjoint])⟩

theorem measurable_hermitianScale (s : ℝ) :
    Measurable (hermitianScale (ι := ι) s) := by
  apply Measurable.subtype_mk
  exact (measurable_subtype_coe :
    Measurable (Subtype.val : PSSS.HermitianMatrix ι → Matrix ι ι ℂ)).const_smul (s : ℂ)

/-- The count of the sum of two Hermitian matrices on `I`. -/
def sumCount (I : Set ℝ) (z : PSSS.HermitianMatrix ι × PSSS.HermitianMatrix ι) : ℕ :=
  eigenCount ⟨z.1.1 + z.2.1, z.1.2.add z.2.2⟩ I

theorem measurable_sumCount (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (sumCount (ι := ι) I) := by
  apply (measurable_nativeEigenCount I hI).comp
  apply Measurable.subtype_mk
  have h1 : Measurable (fun z : PSSS.HermitianMatrix ι × PSSS.HermitianMatrix ι => z.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have h2 : Measurable (fun z : PSSS.HermitianMatrix ι × PSSS.HermitianMatrix ι => z.2.1) :=
    measurable_subtype_coe.comp measurable_snd
  exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
    (measurable_pi_iff.mp (measurable_pi_iff.mp h1 x) y).add
      (measurable_pi_iff.mp (measurable_pi_iff.mp h2 x) y)

theorem sumCount_le (I : Set ℝ) (z : PSSS.HermitianMatrix ι × PSSS.HermitianMatrix ι) :
    sumCount I z ≤ Fintype.card ι :=
  eigenCount_le_dimension _ _

/-- Scaling both summands by `s > 0` scales the interval. -/
theorem sumCount_scale (s : ℝ) (hs : 0 < s) (a b : ℝ)
    (z : PSSS.HermitianMatrix ι × PSSS.HermitianMatrix ι) :
    sumCount (Icc (s * a) (s * b)) (hermitianScale s z.1, hermitianScale s z.2) =
      sumCount (Icc a b) z := by
  unfold sumCount
  rw [nativeEigenCount_eq_orderedEigenvalueCount, nativeEigenCount_eq_orderedEigenvalueCount]
  have hM : (z.1.1 + z.2.1).IsHermitian := z.1.2.add z.2.2
  have hS : ((s : ℂ) • (z.1.1 + z.2.1)).IsHermitian := hM.smul (by simp [IsSelfAdjoint])
  have he : (hermitianScale s z.1).1 + (hermitianScale s z.2).1 = (s : ℂ) • (z.1.1 + z.2.1) := by
    simp [hermitianScale, smul_add]
  have h := orderedEigenvalueCount_positiveScale_Icc hM s hs hS a b
  unfold orderedEigenvalueCount at h ⊢
  rw [← h]
  apply eigenvalueCount_congr
  intro i
  have hv : BlockBand.Foundations.Spectral.increasingEigenvalue
      ((hermitianScale s z.1).2.add (hermitianScale s z.2).2) i =
      BlockBand.Foundations.Spectral.increasingEigenvalue hS i := by
    congr 1
  rw [hv]

/-- The canonical matrix law is the law of the canonical `Law`'s noise. -/
theorem integral_canonicalMatrixMeasure {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)
    (f : PSSS.HermitianMatrix (Index d) → ℝ) (hf : Measurable f) :
    (∫ g, f g ∂canonicalMatrixMeasure d hd) =
      ∫ z, f (matrixOfUpperCoordinates d z) ∂(canonicalLaw d hd).P := by
  rw [canonicalMatrixMeasure, integral_map (measurable_matrixOfUpperCoordinates d).aemeasurable
    hf.aestronglyMeasurable]
  rfl

/-- Pushforward through the Hermitian inclusion determines the law. -/
theorem map_eq_of_map_val_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → PSSS.HermitianMatrix ι) (hX : Measurable X) (μ : Measure (PSSS.HermitianMatrix ι))
    (h : P.map (fun ω => (X ω).1) = μ.map Subtype.val) : P.map X = μ := by
  have he : MeasurableEmbedding (Subtype.val : PSSS.HermitianMatrix ι → Matrix ι ι ℂ) :=
    MeasurableEmbedding.subtype_coe measurableSet_isHermitian
  have h1 : (P.map X).map Subtype.val = μ.map Subtype.val := by
    rw [Measure.map_map measurable_subtype_coe hX]
    exact h
  rw [← he.comap_map (P.map X), h1, he.comap_map]

/-- `ConditionalBlockGUECount` from the PSSS source contract. -/
theorem conditionalBlockGUECount_holds (source : PSSS.SourceContract.{0}) :
    Internal.Contracts.Inputs.ConditionalBlockGUECount := by
  refine ⟨source.C, source.C_pos, ?_⟩
  intro Ω _ P _ k d hd t ht G D hG hD hlaw hind a b hab r hr
  have hcan : IsProbabilityMeasure (canonicalMatrixMeasure d hd) :=
    canonicalMatrixMeasure_probability d hd
  set s : ℝ := (Real.sqrt t)⁻¹ with hs_def
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  let I : Set ℝ := Icc (s * a) (s * b)
  let pair : Ω → PSSS.HermitianMatrix (Index d) × PSSS.HermitianMatrix (Index d) :=
    fun ω => (hermitianScale s (D ω), hermitianScale s (G ω))
  have hpair : Measurable pair :=
    ((measurable_hermitianScale s).comp hD).prodMk ((measurable_hermitianScale s).comp hG)
  have hcount : (fun ω => eigenCount ⟨(D ω).1 + (G ω).1, (D ω).2.add (G ω).2⟩ (Icc a b)) =
      fun ω => sumCount I (pair ω) := by
    funext ω
    exact (sumCount_scale s hs a b (D ω, G ω)).symm
  rw [hcount]
  have hmeas : Measurable (fun ω => sumCount I (pair ω)) :=
    (measurable_sumCount I measurableSet_Icc).comp hpair
  refine ⟨integrable_factorialCount P hmeas (fun ω => sumCount_le I (pair ω)) r, ?_⟩
  -- the law of the scaled pair is the product of the deformation law and the canonical law
  have hGlaw : P.map (fun ω => hermitianScale s (G ω)) = canonicalMatrixMeasure d hd := by
    apply map_eq_of_map_val_eq P _ ((measurable_hermitianScale s).comp hG)
    simpa [hermitianScale, hs_def] using hlaw.map_eq
  have hind' : IndepFun (fun ω => hermitianScale s (D ω)) (fun ω => hermitianScale s (G ω)) P :=
    hind.comp (measurable_hermitianScale s) (measurable_hermitianScale s)
  have hprod : P.map pair =
      (P.map (fun ω => hermitianScale s (D ω))).prod (canonicalMatrixMeasure d hd) := by
    rw [← hGlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map
      ((measurable_hermitianScale s).comp hD).aemeasurable
      ((measurable_hermitianScale s).comp hG).aemeasurable).mp hind'
  have hint : Integrable (factorialCount (sumCount (ι := Index d) I) r)
      ((P.map (fun ω => hermitianScale s (D ω))).prod (canonicalMatrixMeasure d hd)) := by
    exact integrable_factorialCount _ (measurable_sumCount I measurableSet_Icc)
      (fun z => sumCount_le I z) r
  have hfm : Measurable (factorialCount (sumCount (ι := Index d) I) r) :=
    measurable_factorialCount (measurable_sumCount I measurableSet_Icc) r
  have hrw : (∫ ω, factorialCount (fun ω => sumCount I (pair ω)) r ω ∂P) =
      ∫ z, factorialCount (sumCount I) r z ∂(P.map pair) := by
    rw [integral_map hpair.aemeasurable hfm.aestronglyMeasurable]
    rfl
  rw [hrw, hprod, integral_prod _ hint]
  -- inner bound from PSSS at the canonical law, deformation `s • D`
  have hlen : (s * b - s * a) = s * (b - a) := by ring
  have hbound : ∀ A : PSSS.HermitianMatrix (Index d),
      (∫ g, factorialCount (sumCount I) r (A, g) ∂canonicalMatrixMeasure d hd) ≤
        (source.C * (Fintype.card (Index d) : ℝ) * (s * b - s * a)) ^ r := by
    intro A
    rw [integral_canonicalMatrixMeasure d hd (fun g => factorialCount (sumCount I) r (A, g))
      (hfm.comp (measurable_const.prodMk measurable_id))]
    exact source.factorialBound hd (canonicalLaw d hd) A (s * a) (s * b)
      (mul_le_mul_of_nonneg_left hab hs.le) r hr
  have : IsProbabilityMeasure (P.map (fun ω => hermitianScale s (D ω))) := by
    constructor
    rw [Measure.map_apply (f := fun ω => hermitianScale s (D ω))
      ((measurable_hermitianScale s).comp hD) MeasurableSet.univ]
    simp
  have hle := integral_mono hint.integral_prod_left
    (integrable_const ((source.C * (Fintype.card (Index d) : ℝ) * (s * b - s * a)) ^ r)) hbound
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hle
  refine hle.trans (le_of_eq ?_)
  rw [hlen, blockGUE_dimension]
  congr 1
  rw [hs_def]
  ring

end BlockBand.Wegner
