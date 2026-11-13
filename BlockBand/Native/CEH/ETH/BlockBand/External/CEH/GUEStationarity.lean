module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OUFlow
public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.PhysicalHermitianGaussianSplit
public import Mathlib.Probability.Independence.Integration

/-!
# Concrete GUE stationarity for the CEH Ornstein–Uhlenbeck flow

This module constructs the probability law used at the stationarity boundary,
rather than packaging invariance as a field of an abstract certificate.  A
sample contains, at every finite Hermitian coordinate, an independent pair of
centered Gaussians of the variance of the paper.  Coordinatewise mixing by
`a x + b y`, with `a²+b²=1`, is proved to map this finite product exactly back
to the concrete GUE coordinate measure.

Diagonal coordinates have variance `t`; the real and imaginary parts of each
strict-upper entry have variance `t/2`.  The CEH adapter specializes
`t = s/N`, and the OU adapter specializes `a=e^{-u/2}` and
`b=sqrt(1-e^{-u})`.  All statements are finite-dimensional and exact.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped NNReal

/-- Paired real coordinates for two independent concrete GUE samples. -/
abbrev GUEPairSample (d : ℕ) :=
  Fin (Fintype.card (HermitianCoordinate d)) → (ℝ × ℝ)

/-- At coordinate `k`, two independent copies of the exact GUE coordinate
Gaussian. -/
def guePairCoordinateMeasure (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) : Measure (ℝ × ℝ) :=
  let γ := gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht k)
  γ.prod γ

instance guePairCoordinateMeasure.instIsProbabilityMeasure
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    IsProbabilityMeasure (guePairCoordinateMeasure d t ht k) := by
  unfold guePairCoordinateMeasure
  infer_instance

/-- Concrete finite product carrying two independent copies at every
Hermitian coordinate. -/
def guePairMeasure (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure (GUEPairSample d) :=
  Measure.pi (guePairCoordinateMeasure d t ht)

instance guePairMeasure.instIsProbabilityMeasure
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IsProbabilityMeasure (guePairMeasure d t ht) := by
  unfold guePairMeasure
  infer_instance

/-- The first GUE coordinate field. -/
def guePairFirst {d : ℕ} (x : GUEPairSample d) : HermitianCoordinateSpace d :=
  fun k => (x k).1

/-- The second GUE coordinate field. -/
def guePairSecond {d : ℕ} (x : GUEPairSample d) : HermitianCoordinateSpace d :=
  fun k => (x k).2

/-- Coordinatewise orthogonal mixture. -/
def gueMix {d : ℕ} (a b : ℝ) (x : GUEPairSample d) :
    HermitianCoordinateSpace d :=
  fun k => a * (x k).1 + b * (x k).2

/-- The paired source and both projections are measurable. -/
theorem measurable_guePairFirst {d : ℕ} : Measurable (@guePairFirst d) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_fst.comp (measurable_pi_apply k)

/-- The second projection is measurable. -/
theorem measurable_guePairSecond {d : ℕ} : Measurable (@guePairSecond d) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_snd.comp (measurable_pi_apply k)

/-- Every coordinatewise mixture is measurable. -/
theorem measurable_gueMix {d : ℕ} (a b : ℝ) :
    Measurable (@gueMix d a b) := by
  rw [measurable_pi_iff]
  intro k
  exact ((measurable_fst.comp (measurable_pi_apply k)).const_mul a).add
    ((measurable_snd.comp (measurable_pi_apply k)).const_mul b)

/-- Under a product of two centered scalar Gaussians, the coordinate
projections are independent. -/
theorem indepFun_guePairCoordinate (v : NNReal) :
    IndepFun (fun x : ℝ × ℝ => x.1) (fun x : ℝ × ℝ => x.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  exact indepFun_prod measurable_id measurable_id

/-- Scalar Gaussian rotation for arbitrary coefficients on the unit circle.
This is proved from Mathlib's scaling and convolution laws, not assumed. -/
theorem gaussianReal_pair_mix {v : NNReal} {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) :
    Measure.map (fun x : ℝ × ℝ => a * x.1 + b * x.2)
        ((gaussianReal 0 v).prod (gaussianReal 0 v)) =
      gaussianReal 0 v := by
  let P := (gaussianReal 0 v).prod (gaussianReal 0 v)
  have hX : HasLaw (fun x : ℝ × ℝ => x.1) (gaussianReal 0 v) P := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simp [P]
  have hY : HasLaw (fun x : ℝ × ℝ => x.2) (gaussianReal 0 v) P := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    simp [P]
  have hI : IndepFun (fun x : ℝ × ℝ => a * x.1)
      (fun x : ℝ × ℝ => b * x.2) P := by
    exact (indepFun_guePairCoordinate v).comp
      (measurable_const_mul a) (measurable_const_mul b)
  have hXa := gaussianReal_const_mul hX a
  have hYb := gaussianReal_const_mul hY b
  have hadd := gaussianReal_add_gaussianReal_of_indepFun hI hXa hYb
  have hv : NNReal.mk (a ^ 2) (sq_nonneg a) * v +
      NNReal.mk (b ^ 2) (sq_nonneg b) * v = v := by
    ext
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk]
    nlinarith [show 0 ≤ (v : ℝ) from v.coe_nonneg]
  have hfun :
      (fun x : ℝ × ℝ => a * x.1) + (fun x : ℝ × ℝ => b * x.2) =
        (fun x : ℝ × ℝ => a * x.1 + b * x.2) := by
    funext x
    rfl
  rw [hfun] at hadd
  simpa [P, hv] using hadd

/-- Each pair at coordinate `k` has the declared concrete product law. -/
theorem guePairCoordinate_hasLaw (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    HasLaw (fun x : GUEPairSample d => x k)
      (guePairCoordinateMeasure d t ht k) (guePairMeasure d t ht) := by
  refine ⟨(measurable_pi_apply k).aemeasurable, ?_⟩
  exact (measurePreserving_eval (guePairCoordinateMeasure d t ht) k).map_eq

/-- At every Hermitian coordinate, the two scalar copies are independent
under the full finite-product source measure (not merely under the isolated
coordinate marginal). -/
theorem indepFun_guePairCoordinate_under_pairMeasure
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    IndepFun (fun x : GUEPairSample d => (x k).1)
      (fun x : GUEPairSample d => (x k).2) (guePairMeasure d t ht) := by
  have hpair := guePairCoordinate_hasLaw d t ht k
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (f := fun x : GUEPairSample d => (x k).1)
    (g := fun x : GUEPairSample d => (x k).2)
    ((measurable_fst.comp (measurable_pi_apply k)).aemeasurable)
    ((measurable_snd.comp (measurable_pi_apply k)).aemeasurable)]
  change Measure.map (fun x : GUEPairSample d => x k) (guePairMeasure d t ht) =
    (Measure.map (fun x : GUEPairSample d => (x k).1) (guePairMeasure d t ht)).prod
      (Measure.map (fun x : GUEPairSample d => (x k).2) (guePairMeasure d t ht))
  rw [hpair.map_eq]
  have hfst :
      Measure.map (fun x : GUEPairSample d => (x k).1) (guePairMeasure d t ht) =
        Measure.map Prod.fst (guePairCoordinateMeasure d t ht k) := by
    rw [← hpair.map_eq, Measure.map_map]
    · rfl
    · exact measurable_fst
    · exact measurable_pi_apply k
  have hsnd :
      Measure.map (fun x : GUEPairSample d => (x k).2) (guePairMeasure d t ht) =
        Measure.map Prod.snd (guePairCoordinateMeasure d t ht k) := by
    rw [← hpair.map_eq, Measure.map_map]
    · rfl
    · exact measurable_snd
    · exact measurable_pi_apply k
  rw [hfst, hsnd]
  unfold guePairCoordinateMeasure
  simp

/-- The coordinate pairs in the concrete source are mutually independent. -/
theorem iIndepFun_guePairCoordinates (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iIndepFun (fun k (x : GUEPairSample d) => x k) (guePairMeasure d t ht) := by
  unfold guePairMeasure
  apply iIndepFun_pi (X := fun _ => id)
  intro k
  exact measurable_id.aemeasurable

/-- **Concrete finite-product GUE stationarity.**  The pushforward of the
explicit paired product law by `a G₁ + b G₂` is exactly the existing concrete
GUE coordinate measure whenever `a²+b²=1`. -/
theorem gueMix_map_eq_gue (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    Measure.map (gueMix a b) (guePairMeasure d t ht) =
      hermitianGUECoordinateMeasure d t ht := by
  unfold guePairMeasure hermitianGUECoordinateMeasure gueMix
  calc
    Measure.map (fun x k => a * (x k).1 + b * (x k).2)
        (Measure.pi (guePairCoordinateMeasure d t ht)) =
        Measure.pi (fun k => Measure.map
          (fun p : ℝ × ℝ => a * p.1 + b * p.2)
          (guePairCoordinateMeasure d t ht k)) := by
      exact Measure.pi_map_pi
        (μ := guePairCoordinateMeasure d t ht)
        (f := fun (_ : Fin (Fintype.card (HermitianCoordinate d)))
          (p : ℝ × ℝ) => a * p.1 + b * p.2)
        (fun k => by fun_prop)
    _ = Measure.pi (fun k =>
        gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht k)) := by
      congrm Measure.pi fun k => ?_
      unfold guePairCoordinateMeasure
      exact gaussianReal_pair_mix hab

/-- The unmixed first field has exactly the concrete GUE law. -/
theorem guePairFirst_map_eq_gue (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map guePairFirst (guePairMeasure d t ht) =
      hermitianGUECoordinateMeasure d t ht := by
  have hfun : @gueMix d 1 0 = @guePairFirst d := by
    funext x k
    change 1 * (x k).1 + 0 * (x k).2 = (x k).1
    ring
  rw [← hfun]
  exact gueMix_map_eq_gue d t ht (a := 1) (b := 0) (by norm_num)

/-- The unmixed second field has exactly the concrete GUE law. -/
theorem guePairSecond_map_eq_gue (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map guePairSecond (guePairMeasure d t ht) =
      hermitianGUECoordinateMeasure d t ht := by
  have hfun : @gueMix d 0 1 = @guePairSecond d := by
    funext x k
    change 0 * (x k).1 + 1 * (x k).2 = (x k).2
    ring
  rw [← hfun]
  exact gueMix_map_eq_gue d t ht (a := 0) (b := 1) (by norm_num)

/-- The first field is a measurable random variable with the concrete
normalized GUE product law. -/
theorem guePairFirst_hasLaw (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasLaw (@guePairFirst d) (hermitianGUECoordinateMeasure d t ht)
      (guePairMeasure d t ht) :=
  ⟨measurable_guePairFirst.aemeasurable, guePairFirst_map_eq_gue d t ht⟩

/-- The second field is a measurable random variable with the same concrete
normalized GUE product law. -/
theorem guePairSecond_hasLaw (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasLaw (@guePairSecond d) (hermitianGUECoordinateMeasure d t ht)
      (guePairMeasure d t ht) :=
  ⟨measurable_guePairSecond.aemeasurable, guePairSecond_map_eq_gue d t ht⟩

/-- The normalized OU coefficients lie on the unit circle at forward time. -/
theorem ou_coefficients_unit {u : ℝ} (hu : 0 ≤ u) :
    ouDecay u ^ 2 + ouNoise u ^ 2 = 1 :=
  ouDecay_sq_add_ouNoise_sq hu

/-- Concrete GUE stationarity for the normalized OU coefficients
`e^{-u/2}` and `sqrt(1-e^{-u})`. -/
theorem gueOU_map_eq_gue (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {u : ℝ} (hu : 0 ≤ u) :
    Measure.map (gueMix (ouDecay u) (ouNoise u)) (guePairMeasure d t ht) =
      hermitianGUECoordinateMeasure d t ht :=
  gueMix_map_eq_gue d t ht (ou_coefficients_unit hu)

/-- The OU stationarity identity with both scalar coefficients written out as in the CEH
interpolation. -/
theorem gueOU_exp_sqrt_map_eq_gue (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {u : ℝ} (hu : 0 ≤ u) :
    Measure.map
        (gueMix (Real.exp (-u / 2)) (Real.sqrt (1 - Real.exp (-u))))
        (guePairMeasure d t ht) =
      hermitianGUECoordinateMeasure d t ht := by
  simpa only [ouDecay, ouNoise] using gueOU_map_eq_gue d t ht hu

/-- Exact CEH normalized variance `s/N`. -/
def cehGUEVariance (s : ℝ) (N : ℕ) : ℝ := s / N

/-- Nonnegativity of the CEH variance adapter. -/
theorem cehGUEVariance_nonneg {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    0 ≤ cehGUEVariance s N := by
  unfold cehGUEVariance
  positivity

/-- Exact `s/N` concrete GUE stationarity adapter. -/
theorem gueOU_map_eq_gue_s_div_N (d N : ℕ) {s u : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) :
    Measure.map (gueMix (ouDecay u) (ouNoise u))
        (guePairMeasure d (s / N) (cehGUEVariance_nonneg hs N)) =
      hermitianGUECoordinateMeasure d (s / N)
        (cehGUEVariance_nonneg hs N) :=
  gueOU_map_eq_gue d (s / N) (cehGUEVariance_nonneg hs N) hu

/-- Reconstruct the mixed coordinate field as a Hermitian matrix. -/
def gueMixBlock (d : ℕ) (a b : ℝ) (x : GUEPairSample d) :
    HermitianMatrix (Fin d) :=
  hermitianGUEBlock d (gueMix a b x)

/-- Reconstruction of a mixed GUE coordinate field is measurable. -/
theorem measurable_gueMixBlock (d : ℕ) (a b : ℝ) :
    Measurable (gueMixBlock d a b) :=
  (measurable_hermitianGUEBlock d).comp (measurable_gueMix a b)

/-- Deterministic Hermitian translation of a mixed GUE block. -/
def translatedGueMixBlock {d : ℕ} (F : HermitianMatrix (Fin d))
    (a b : ℝ) (x : GUEPairSample d) : Matrix (Fin d) (Fin d) ℂ :=
  F.1 + (gueMixBlock d a b x).1

/-- Deterministic translation preserves Hermitian symmetry pointwise. -/
theorem translatedGueMixBlock_isHermitian {d : ℕ}
    (F : HermitianMatrix (Fin d)) (a b : ℝ) (x : GUEPairSample d) :
    (translatedGueMixBlock F a b x).IsHermitian := by
  exact F.2.add (gueMixBlock d a b x).2

/-- A deterministic translation of the reconstructed random block is
measurable. -/
theorem measurable_translatedGueMixBlock {d : ℕ}
    (F : HermitianMatrix (Fin d)) (a b : ℝ) :
    Measurable (translatedGueMixBlock F a b) := by
  unfold translatedGueMixBlock
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_const.add
    ((measurable_subtype_coe.comp
      (measurable_gueMixBlock d a b)).eval_matrix)

/-- The translated matrix has the exact deterministic-plus-random form. -/
theorem translated_ou_eq {d : ℕ} (F : HermitianMatrix (Fin d))
    (u : ℝ) (x : GUEPairSample d) :
    translatedGueMixBlock F (ouDecay u) (ouNoise u) x =
      F.1 + (hermitianGUEBlock d
        (gueMix (ouDecay u) (ouNoise u) x)).1 := rfl

/-- Damped deterministic deformation plus the stationary OU GUE mixture. -/
def dampedTranslatedGueMixBlock {d : ℕ} (F : HermitianMatrix (Fin d))
    (u : ℝ) (x : GUEPairSample d) : Matrix (Fin d) (Fin d) ℂ :=
  (ouDecay u : ℂ) • F.1 +
    (gueMixBlock d (ouDecay u) (ouNoise u) x).1

/-- The damped deterministic translation remains Hermitian. -/
theorem dampedTranslatedGueMixBlock_isHermitian {d : ℕ}
    (F : HermitianMatrix (Fin d)) (u : ℝ) (x : GUEPairSample d) :
    (dampedTranslatedGueMixBlock F u x).IsHermitian := by
  exact F.2.smul (RCLike.conj_ofReal _)
    |>.add (gueMixBlock d (ouDecay u) (ouNoise u) x).2

/-- The exact damped deformation with the exponential and square-root coefficients written
out. -/
theorem dampedTranslatedGueMixBlock_eq_exp_sqrt {d : ℕ}
    (F : HermitianMatrix (Fin d)) (u : ℝ) (x : GUEPairSample d) :
    dampedTranslatedGueMixBlock F u x =
      (Real.exp (-u / 2) : ℂ) • F.1 +
        (gueMixBlock d (Real.exp (-u / 2))
          (Real.sqrt (1 - Real.exp (-u))) x).1 := by
  rfl

end CEHNative.BlockBand.CEH
