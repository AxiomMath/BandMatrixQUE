module

public import BlockBand.SourceProcess.WienerRecovery.ScalarWienerMeasureAllPathExistence
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.Process.Adapted
public import BlockBand.SourceProcess.FreshSeparatorNoise

/-!
# The finite common-noise Wiener product

A finite family of independent Wiener processes on continuous paths, independent of an old state;
the real coordinates are Brownian motions with independent increments for the enlarged
old-state/all-past filtration, and the circular complex matrix driver built from them has
continuous paths and Gaussian increments independent of the past.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ComplexConjugate
open WienerRecovery.CEH.ScalarWienerRealizationClosure
open WienerRecovery.ScalarWienerMeasureAllPathExistence

abbrev CanonicalWienerPath := C(ℝ≥0, ℝ)

def canonicalWienerLaw : Measure CanonicalWienerPath := standardScalarWienerMeasure

instance canonicalWienerLaw_probability : IsProbabilityMeasure canonicalWienerLaw :=
  isProbabilityMeasure_of_isScalarWienerMeasure isScalarWienerMeasure_standardScalarWienerMeasure

/-- A scalar Brownian motion on the continuous-path law. -/
theorem canonicalWiener_isBrownian :
    IsBrownianReal (fun t (ω : CanonicalWienerPath) => ω t) canonicalWienerLaw :=
  isBrownianReal_coordinateProcess isScalarWienerMeasure_standardScalarWienerMeasure

/-- Finite product of constructed continuous Wiener laws. -/
def commonWienerLaw (κ : Type*) [Fintype κ] : Measure (κ → CanonicalWienerPath) :=
  Measure.pi fun _ => canonicalWienerLaw

instance commonWienerLaw_probability (κ : Type*) [Fintype κ] :
    IsProbabilityMeasure (commonWienerLaw κ) := by unfold commonWienerLaw; infer_instance

/-- Real common-noise coordinates on the independent old-state/Wiener product. -/
def commonRealBrownian {S κ : Type*} (t : ℝ≥0)
    (x : S × (κ → CanonicalWienerPath)) (a : κ) : ℝ := x.2 a t

/-- Every coordinate is a Brownian motion. -/
theorem commonRealBrownian_isBrownian {S κ : Type*} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] (a : κ) :
    IsBrownianReal (fun t x => commonRealBrownian t x a) (μ.prod (commonWienerLaw κ)) := by
  have mp := (measurePreserving_eval (fun _ : κ => canonicalWienerLaw) a).comp
    (measurePreserving_snd (μ := μ) (ν := commonWienerLaw κ))
  refine ⟨?_, Filter.Eventually.of_forall fun x => (x.2 a).continuous⟩
  refine IsPreBrownianReal.mk' fun I => ?_
  simpa only [commonRealBrownian, Function.comp_def] using
    (canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw I).comp mp.hasLaw

/-- The whole scalar paths are independent across coordinates. -/
theorem commonWiener_paths_independent {κ : Type*} [Fintype κ] :
    iIndepFun (fun a (ω : κ → CanonicalWienerPath) => ω a) (commonWienerLaw κ) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- All common-noise paths are independent of arbitrary old state. -/
theorem commonWiener_oldState_independent {S κ : Type*} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    IndepFun (Prod.fst : S × (κ → CanonicalWienerPath) → S) Prod.snd
      (μ.prod (commonWienerLaw κ)) := indepFun_prod measurable_id measurable_id

/-- Every real coordinate has independent increments on the product law. -/
theorem commonRealBrownian_hasIndepIncrements {S κ : Type*} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] (a : κ) :
    HasIndepIncrements (fun t x => commonRealBrownian t x a) (μ.prod (commonWienerLaw κ)) :=
  (commonRealBrownian_isBrownian μ a).toIsPreBrownianReal.hasIndepIncrements

private theorem measurable_commonRealVector {κ : Type*} (t : ℝ≥0) :
    Measurable (fun ω : κ → CanonicalWienerPath => fun a => ω a t) :=
  Measurable.of_eval fun a => (ContinuousMap.measurable_eval t).comp (measurable_pi_apply a)

/-- Joint Gaussian product law of all real increments. -/
theorem hasLaw_commonRealBrownian_increment {S κ : Type*} [MeasurableSpace S] [Fintype κ]
    (μ : Measure S) [IsProbabilityMeasure μ] (s t : ℝ≥0) :
    HasLaw (fun x : S × (κ → CanonicalWienerPath) =>
      fun a => commonRealBrownian t x a - commonRealBrownian s x a)
      (Measure.pi fun _ : κ => gaussianReal 0 (nndist t s)) (μ.prod (commonWienerLaw κ)) := by
  have hmap : HasLaw (fun ω : κ → CanonicalWienerPath => fun a => ω a t - ω a s)
      (Measure.pi fun _ : κ => gaussianReal 0 (nndist t s)) (commonWienerLaw κ) := by
    refine ⟨((measurable_commonRealVector t).sub (measurable_commonRealVector s)).aemeasurable, ?_⟩
    rw [commonWienerLaw, Measure.pi_map_pi
      (f := fun (_ : κ) (ω : CanonicalWienerPath) => ω t - ω s)]
    · congr 1
      funext a
      exact (canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw_sub t s).map_eq
    · exact fun _ => ((ContinuousMap.measurable_eval t).sub
        (ContinuousMap.measurable_eval s)).aemeasurable
  exact hmap.comp (measurePreserving_snd (μ := μ) (ν := commonWienerLaw κ)).hasLaw

/-- Circular complex conversion: each real direction has coefficient 1/sqrt(2). -/
def circularBrownianCoordinates {ι : Type*} (r : ((ι × ι) × Fin 2) → ℝ)
    (u : ι × ι) : ℂ := ((r (u, 0) : ℂ) + (r (u, 1) : ℂ) * Complex.I) / Real.sqrt 2

/-- Common circular complex matrix driver in canonical flat coordinates. -/
def commonComplexBrownian {S ι : Type*} (t : ℝ≥0)
    (x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath)) : (ι × ι) → ℂ :=
  circularBrownianCoordinates (commonRealBrownian t x)

/-- Increment law from a finite independent centered Gaussian product. -/
def commonCircularIncrementLaw (ι : Type*) [Fintype ι] (δ : ℝ≥0) : Measure ((ι × ι) → ℂ) :=
  (Measure.pi fun _ : ((ι × ι) × Fin 2) => gaussianReal 0 δ).map circularBrownianCoordinates

/-- The whole flat complex increment has the constructed finite product Gaussian law. -/
theorem hasLaw_commonComplexBrownian_increment {S ι : Type*} [MeasurableSpace S] [Fintype ι]
    (μ : Measure S) [IsProbabilityMeasure μ] (s t : ℝ≥0) :
    HasLaw (fun x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath) =>
      commonComplexBrownian t x - commonComplexBrownian s x)
      (commonCircularIncrementLaw ι (nndist t s))
      (μ.prod (commonWienerLaw ((ι × ι) × Fin 2))) := by
  have hm : Measurable (circularBrownianCoordinates (ι := ι)) := by
    apply Measurable.of_eval
    intro u
    unfold circularBrownianCoordinates
    fun_prop
  have h := (hasLaw_map hm.aemeasurable).comp (hasLaw_commonRealBrownian_increment μ s t)
  apply h.congr
  apply Filter.Eventually.of_forall
  intro x
  funext u
  simp only [Function.comp_def, commonComplexBrownian, circularBrownianCoordinates,
    commonRealBrownian, Pi.sub_apply, Complex.ofReal_sub]
  ring

/-- The entire matrix driver has continuous paths for every sample. -/
theorem commonComplexBrownian_continuous {S ι : Type*}
    (x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath)) :
    Continuous (fun t => commonComplexBrownian t x) := by
  apply continuous_pi
  intro u
  exact (((Complex.continuous_ofReal.comp (x.2 (u, 0)).continuous).add
    ((Complex.continuous_ofReal.comp (x.2 (u, 1)).continuous).mul continuous_const)).div_const _)

/-- Full coordinate prefix through the current time. -/
def commonWienerPast {κ : Type*} (t : ℝ≥0) (ω : κ → CanonicalWienerPath) : κ → Set.Iic t → ℝ :=
  fun a v => ω a v.1

/-- Full shifted future of all coordinates. -/
def commonWienerFuture {κ : Type*} (t : ℝ≥0) (ω : κ → CanonicalWienerPath) : κ → ℝ≥0 → ℝ :=
  fun a v => ω a (t + v) - ω a t

theorem measurable_commonWienerPast {κ : Type*} (t : ℝ≥0) :
    Measurable (commonWienerPast (κ := κ) t) :=
  Measurable.of_eval fun a => Measurable.of_eval fun v =>
    (ContinuousMap.measurable_eval v.1).comp (measurable_pi_apply a)

theorem measurable_commonWienerFuture {κ : Type*} (t : ℝ≥0) :
    Measurable (commonWienerFuture (κ := κ) t) :=
  Measurable.of_eval fun a => Measurable.of_eval fun v =>
    ((ContinuousMap.measurable_eval (t + v)).sub
      (ContinuousMap.measurable_eval t)).comp (measurable_pi_apply a)

/-- The enlarged filtration records old state and all common-noise coordinate past. -/
def commonWienerFiltration (S κ : Type*) [MeasurableSpace S] :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (S × (κ → CanonicalWienerPath))) where
  seq t := MeasurableSpace.comap (fun x : S × (κ → CanonicalWienerPath) =>
    (x.1, commonWienerPast t x.2)) inferInstance
  mono' := by
    intro s t hst
    let restrict : S × (κ → Set.Iic t → ℝ) → S × (κ → Set.Iic s → ℝ) :=
      fun z => (z.1, fun a v => z.2 a ⟨v.1, v.2.trans hst⟩)
    have hr : Measurable restrict := measurable_fst.prodMk
      (Measurable.of_eval fun a => Measurable.of_eval fun v =>
        (measurable_pi_apply (⟨v.1, v.2.trans hst⟩ : Set.Iic t)).comp
          ((measurable_pi_apply a).comp measurable_snd))
    exact (hr.comp (comap_measurable (fun x : S × (κ → CanonicalWienerPath) =>
      (x.1, commonWienerPast t x.2)))).comap_le
  le' t := (measurable_fst.prodMk ((measurable_commonWienerPast (κ := κ) t).comp measurable_snd)).comap_le

/-- Common real vector is adapted to the enlarged old-state/all-past filtration. -/
theorem commonRealBrownian_adapted {S κ : Type*} [MeasurableSpace S] :
    Adapted (commonWienerFiltration S κ) (commonRealBrownian (S := S) (κ := κ)) := by
  intro t
  change @Measurable _ _ (MeasurableSpace.comap
    (fun x : S × (κ → CanonicalWienerPath) => (x.1, commonWienerPast t x.2)) _) _ _
  have hev : Measurable (fun z : S × (κ → Set.Iic t → ℝ) =>
      fun a => z.2 a ⟨t, le_rfl⟩) :=
    Measurable.of_eval fun a => (measurable_pi_apply (⟨t, le_rfl⟩ : Set.Iic t)).comp
      ((measurable_pi_apply a).comp measurable_snd)
  exact hev.comp (comap_measurable _)

private theorem independent_pair_pi {κ Ω A B : Type*} [Fintype κ]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (F : Ω → A) (H : Ω → B)
    (hF : Measurable F) (hH : Measurable H) (h : IndepFun F H ν) :
    IndepFun (fun ω : κ → Ω => fun a => F (ω a))
      (fun ω : κ → Ω => fun a => H (ω a)) (Measure.pi fun _ : κ => ν) := by
  have hp : Measurable (fun ω : κ → Ω => fun a => (F (ω a), H (ω a))) :=
    Measurable.of_eval fun a => (hF.prodMk hH).comp (measurable_pi_apply a)
  have hmap : (Measure.pi fun _ : κ => ν).map
      (fun ω => (fun a => F (ω a), fun a => H (ω a))) =
      (Measure.pi fun _ : κ => ν.map F).prod (Measure.pi fun _ : κ => ν.map H) := by
    change (Measure.pi fun _ : κ => ν).map
      ((MeasurableEquiv.arrowProdEquivProdArrow A B κ) ∘
        (fun ω : κ → Ω => fun a => (F (ω a), H (ω a)))) = _
    rw [← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow A B κ).measurable hp,
      Measure.pi_map_pi (fun _ => (hF.prodMk hH).aemeasurable)]
    simp_rw [h.map_prod_eq_prod_map_map hF.aemeasurable hH.aemeasurable]
    exact (measurePreserving_arrowProdEquivProdArrow A B κ
      (fun _ => ν.map F) (fun _ => ν.map H)).map_eq
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (Measurable.of_eval fun a => hF.comp (measurable_pi_apply a)).aemeasurable
    (Measurable.of_eval fun a => hH.comp (measurable_pi_apply a)).aemeasurable).2
  simp only [Function.comp_def]
  rw [hmap, Measure.pi_map_pi (fun _ => hF.aemeasurable),
    Measure.pi_map_pi (fun _ => hH.aemeasurable)]

/-- The whole shifted future matrix-coordinate family is independent of its whole past. -/
theorem commonWienerFuture_independent_past {κ : Type*} [Fintype κ] (t : ℝ≥0) :
    IndepFun (commonWienerFuture (κ := κ) t) (commonWienerPast t) (commonWienerLaw κ) := by
  exact independent_pair_pi canonicalWienerLaw
    (fun ω : CanonicalWienerPath => fun v => ω (t + v) - ω t)
    (fun ω : CanonicalWienerPath => fun v : Set.Iic t => ω v.1)
    (Measurable.of_eval fun v => (ContinuousMap.measurable_eval (t + v)).sub
      (ContinuousMap.measurable_eval t))
    (Measurable.of_eval fun v => ContinuousMap.measurable_eval v.1)
    (canonicalWiener_isBrownian.toIsPreBrownianReal.indepFun_shift t)

private theorem independent_old_past {S Ω A B : Type*} [MeasurableSpace S]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (F : Ω → A) (H : Ω → B) (hF : Measurable F) (hH : Measurable H)
    (hindep : IndepFun F H ν) :
    IndepFun (fun x : S × Ω => F x.2) (fun x => (x.1, H x.2)) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro U V hU hV
  have hu : MeasurableSet ((fun x : S × Ω => F x.2) ⁻¹' U) :=
    (hF.comp measurable_snd) hU
  have hv : MeasurableSet ((fun x : S × Ω => (x.1, H x.2)) ⁻¹' V) :=
    (measurable_fst.prodMk (hH.comp measurable_snd)) hV
  rw [Measure.prod_apply (hu.inter hv), Measure.prod_apply hu, Measure.prod_apply hv]
  change (∫⁻ a, ν (F ⁻¹' U ∩ H ⁻¹' (Prod.mk a ⁻¹' V)) ∂μ) =
    (∫⁻ _ : S, ν (F ⁻¹' U) ∂μ) * (∫⁻ a, ν (H ⁻¹' (Prod.mk a ⁻¹' V)) ∂μ)
  simp only [lintegral_const, measure_univ, mul_one]
  calc
    _ = ∫⁻ a, ν (F ⁻¹' U) * ν (H ⁻¹' (Prod.mk a ⁻¹' V)) ∂μ := by
      apply lintegral_congr
      intro a
      exact hindep.measure_inter_preimage_eq_mul U (Prod.mk a ⁻¹' V) hU
        (measurable_prodMk_left hV)
    _ = _ := lintegral_const_mul' _ _ (measure_ne_top _ _)

/-- Future increments are independent of the enlarged old-state/all-coordinate past. -/
theorem commonWienerFuture_independent_old_past {S κ : Type*}
    [MeasurableSpace S] [Fintype κ] (μ : Measure S) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    IndepFun (fun x : S × (κ → CanonicalWienerPath) => commonWienerFuture t x.2)
      (fun x => (x.1, commonWienerPast t x.2)) (μ.prod (commonWienerLaw κ)) :=
  independent_old_past μ (commonWienerLaw κ) (commonWienerFuture t) (commonWienerPast t)
    (measurable_commonWienerFuture t) (measurable_commonWienerPast t)
    (commonWienerFuture_independent_past t)

def commonMatrixReshape {ι : Type*} : ((ι × ι) → ℂ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun g := fun i j => g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def commonSeparatorRealLinear {ι : Type*} [Fintype ι]
    (c : ℂ) (P Pprime : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun G := c • (P * G * Pprime + Pprime * Gᴴ * P)
  map_add' G H := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_add, smul_add]
    abel
  map_smul' r G := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_smul, star_trivial, smul_add]
    exact congrArg₂ (· + ·) (smul_comm c r (P * G * Pprime))
      (smul_comm c r (Pprime * Gᴴ * P))

def commonMatrixFlatten {ι : Type*} : Matrix ι ι ℂ →ₗ[ℝ] ((ι × ι) → ℂ) where
  toFun G := fun u => G u.1 u.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Real-linear coefficient for the circular driver with complex variance dt.
The coefficient is sqrt(D0/2), not sqrt(D0)/2; the latter belongs to Z=sqrt(2)W. -/
def separatorBrownianCoefficient {ι : Type*} [Fintype ι]
    (D0 : ℝ) (P Pprime : Matrix ι ι ℂ) : ((ι × ι) → ℂ) →L[ℝ] ((ι × ι) → ℂ) :=
  ((commonMatrixFlatten (ι := ι)).comp
    ((commonSeparatorRealLinear (Real.sqrt (D0 / 2)) P Pprime).comp
      (commonMatrixReshape (ι := ι)))).toContinuousLinearMap

/-- Entrywise coefficient formula, with both projection orders retained. -/
theorem separatorBrownianCoefficient_apply {ι : Type*} [Fintype ι]
    (D0 : ℝ) (P Pprime : Matrix ι ι ℂ) (g : (ι × ι) → ℂ) (u : ι × ι) :
    separatorBrownianCoefficient D0 P Pprime g u =
      ((Real.sqrt (D0 / 2) : ℂ) •
        (P * (commonMatrixReshape g) * Pprime +
          Pprime * (commonMatrixReshape g)ᴴ * P)) u.1 u.2 := rfl

/-- The image of the common driver under a fixed old-state coefficient (a fixed-coefficient process,
not a stochastic integral). -/
def frozenSeparatorBrownian {S ι : Type*} [Fintype ι] (D0 : ℝ)
    (P Pprime : S → Matrix ι ι ℂ) (t : ℝ≥0)
    (x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath)) : (ι × ι) → ℂ :=
  separatorBrownianCoefficient D0 (P x.1) (Pprime x.1) (commonComplexBrownian t x)

/-- Every sample path of `frozenSeparatorBrownian` is continuous. -/
theorem frozenSeparatorBrownian_continuous {S ι : Type*} [Fintype ι]
    (D0 : ℝ) (P Pprime : S → Matrix ι ι ℂ)
    (x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath)) :
    Continuous (fun t => frozenSeparatorBrownian D0 P Pprime t x) :=
  (separatorBrownianCoefficient D0 (P x.1) (Pprime x.1)).continuous.comp
    (commonComplexBrownian_continuous x)

/-- The whole shifted future of the complex matrix driver is independent of the old state and every
real coordinate prefix. -/
theorem commonComplexBrownian_future_independent_old_past {S ι : Type*}
    [MeasurableSpace S] [Fintype ι] (μ : Measure S) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    IndepFun (fun x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath) =>
      fun v => commonComplexBrownian (t + v) x - commonComplexBrownian t x)
      (fun x => (x.1, commonWienerPast t x.2))
      (μ.prod (commonWienerLaw ((ι × ι) × Fin 2))) := by
  let F : (((ι × ι) × Fin 2) → ℝ≥0 → ℝ) → ℝ≥0 → (ι × ι) → ℂ :=
    fun f v => circularBrownianCoordinates (fun a => f a v)
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro v
    apply Measurable.of_eval
    intro u
    unfold F circularBrownianCoordinates
    fun_prop
  have h := (commonWienerFuture_independent_old_past μ t).comp hF measurable_id
  apply h.congr _ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro x
  funext v u
  simp only [Function.comp_def, F, commonWienerFuture, commonComplexBrownian,
    circularBrownianCoordinates, commonRealBrownian, Pi.sub_apply, Complex.ofReal_sub]
  ring

/-- Whole continuous matrix path, built pointwise from the continuous scalar paths. -/
def commonComplexBrownianPath {S ι : Type*} (x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath)) :
    C(ℝ≥0, (ι × ι) → ℂ) where
  toFun t := commonComplexBrownian t x
  continuous_toFun := commonComplexBrownian_continuous x

/-- The whole path is measurable in the compact-open Borel path space. -/
theorem measurable_commonComplexBrownianPath {S ι : Type*} [MeasurableSpace S] [Fintype ι] :
    Measurable (commonComplexBrownianPath (S := S) (ι := ι)) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  apply Measurable.of_eval
  intro u
  change Measurable (fun x => commonComplexBrownian t x u)
  unfold commonComplexBrownian circularBrownianCoordinates commonRealBrownian
  have hcoord (a : (ι × ι) × Fin 2) :
      Measurable (fun x : S × (((ι × ι) × Fin 2) → CanonicalWienerPath) => x.2 a t) :=
    (ContinuousMap.measurable_eval t).comp ((measurable_pi_apply a).comp measurable_snd)
  have h0 := Complex.continuous_ofReal.measurable.comp (hcoord (u, 0))
  have h1 := Complex.continuous_ofReal.measurable.comp (hcoord (u, 1))
  exact (h0.add (h1.mul_const Complex.I)).div_const _

/-- Every Hermitian coefficient pair gives a Hermitian separator, samplewise. -/
theorem separatorBrownianCoefficient_isHermitian {ι : Type*} [Fintype ι]
    (D0 : ℝ) (P Pprime : Matrix ι ι ℂ) (hP : Pᴴ = P) (hPprime : Pprimeᴴ = Pprime)
    (g : (ι × ι) → ℂ) :
    (commonMatrixReshape (separatorBrownianCoefficient D0 P Pprime g)).IsHermitian := by
  change ((Real.sqrt (D0 / 2) : ℂ) •
      (P * commonMatrixReshape g * Pprime + Pprime * (commonMatrixReshape g)ᴴ * P))ᴴ =
    (Real.sqrt (D0 / 2) : ℂ) •
      (P * commonMatrixReshape g * Pprime + Pprime * (commonMatrixReshape g)ᴴ * P)
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hP, hPprime]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [add_comm]
  simp only [Matrix.mul_assoc]

end BlockBand.SourceProcess
