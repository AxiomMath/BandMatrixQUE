module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorPolarFactorization

/-!
# Polar decomposition of the standard Gaussian

A finite-dimensional real standard Gaussian is Lebesgue measure with the normalized radial density
`(2π)^{-d/2} e^{-r²/2}`. On the nonzero locus, the polar map sends it to the product of the uniform
measure on the unit sphere and a radial law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory

/-- Tonelli for a finite product of one-variable functions over σ-finite real
measures. -/
theorem lintegral_pi_fin_prod_eq_prod_psss :
    ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
      (f : Fin n → ℝ → ENNReal), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, μ, _, f, _ => by simp
  | n + 1, μ, _, f, hf => by
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [Fin.prod_univ_succ]
      have hcomp : ∀ p : ℝ × (Fin n → ℝ),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p 0 = p.1 ∧
          ∀ j : Fin n,
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p j.succ =
              p.2 j := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.cons_succ]
      simp_rw [fun p => (hcomp p).1, fun p j => (hcomp p).2 j]
      simp only [Fin.succAbove_zero]
      have hg : Measurable (fun y : Fin n → ℝ => ∏ j, f j.succ (y j)) :=
        Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ j, f j.succ (y j))
          (hf 0).aemeasurable hg.aemeasurable,
        lintegral_pi_fin_prod_eq_prod_psss n (fun j => μ j.succ) (fun j => f j.succ)
          (fun j => hf j.succ)]

/-- Finite products of real density measures have the product density. -/
theorem pi_fin_withDensity_eq_psss {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → ℝ → ENNReal) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_fin_prod_eq_prod_psss n _ f hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

/-- The normalized radial density of a standard Gaussian in real dimension `d`. -/
def stdGaussianRadialDensity (d : ℕ) (r : ℝ) : ENNReal :=
  ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-(r ^ 2) / 2))

/-- The coordinatewise standard Gaussian density is the radial density. -/
theorem prod_gaussianPDF_zero_one_eq_radial (d : ℕ) (x : Fin d → ℝ) :
    ∏ i, gaussianPDF 0 1 (x i) =
      stdGaussianRadialDensity d (Real.sqrt (∑ i, (x i) ^ 2)) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _]
  unfold stdGaussianRadialDensity
  congr 1
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  apply congrArg₂ (· * ·) rfl
  apply congrArg Real.exp
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_neg_distrib]

/-- The product of `d` independent standard real Gaussians is Lebesgue
measure with the normalized radial density. -/
theorem pi_gaussianReal_zero_one_eq_radial_withDensity (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      volume.withDensity (fun x : Fin d → ℝ =>
        stdGaussianRadialDensity d (Real.sqrt (∑ i, (x i) ^ 2))) := by
  have hfun : (fun _ : Fin d => gaussianReal 0 1) =
      fun _ => volume.withDensity (gaussianPDF 0 1) := by
    funext i
    exact gaussianReal_of_var_ne_zero 0 (by norm_num)
  have : ∀ i : Fin d, SigmaFinite
      ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := fun i => by
    rw [← gaussianReal_of_var_ne_zero 0 (by norm_num)]
    infer_instance
  have hpi := @pi_fin_withDensity_eq_psss d
    (fun _ => (volume : Measure ℝ)) (by infer_instance)
    (fun _ => gaussianPDF 0 1) (fun _ => measurable_gaussianPDF 0 1) this
  rw [hfun, hpi, ← volume_pi]
  congr 1
  funext x
  exact prod_gaussianPDF_zero_one_eq_radial d x

/-- In standard real Euclidean coordinates, the abstract standard Gaussian is
exactly the normalized radial reweighting of Lebesgue volume. -/
theorem stdGaussian_euclidean_eq_radial_withDensity (d : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) =
      volume.withDensity (fun x : EuclideanSpace ℝ (Fin d) =>
        stdGaussianRadialDensity d ‖x‖) := by
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  let w : EuclideanSpace ℝ (Fin d) → ENNReal := fun x =>
    stdGaussianRadialDensity d ‖x‖
  have hw : Measurable w := by
    unfold w stdGaussianRadialDensity
    fun_prop
  have hdensity : (fun x : Fin d → ℝ =>
      stdGaussianRadialDensity d (Real.sqrt (∑ i, (x i) ^ 2))) = w ∘ e := by
    funext x
    unfold w e
    congr 2
    rw [EuclideanSpace.norm_eq]
    simp
  rw [← map_pi_eq_stdGaussian]
  rw [pi_gaussianReal_zero_one_eq_radial_withDensity]
  rw [hdensity]
  exact map_withDensity_comp_of_measurePreserving e volume volume
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
    w hw

/-- Every finite-dimensional real standard Gaussian is Lebesgue volume with
its normalized radial density.  Both the normalizing constant and real
ambient dimension are explicit. -/
theorem stdGaussian_eq_radial_withDensity
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    stdGaussian E = volume.withDensity (fun x : E =>
      stdGaussianRadialDensity (Module.finrank ℝ E) ‖x‖) := by
  let d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] E :=
    (EuclideanSpace.basisFun (Fin d) ℝ).equiv b (Equiv.refl (Fin d))
  let w : E → ENNReal := fun x => stdGaussianRadialDensity d ‖x‖
  have hw : Measurable w := by
    unfold w stdGaussianRadialDensity
    fun_prop
  have hdensity : (fun x : EuclideanSpace ℝ (Fin d) =>
      stdGaussianRadialDensity d ‖x‖) = w ∘ U := by
    funext x
    unfold w
    rw [Function.comp_apply, U.norm_map]
  rw [← stdGaussian_map U]
  rw [stdGaussian_euclidean_eq_radial_withDensity]
  rw [hdensity]
  exact map_withDensity_comp_of_measurePreserving U.toMeasurableEquiv volume volume
    U.measurePreserving w hw

/-- Pulling a density back to a measurable subtype agrees with taking the
density after pulling back the underlying measure. -/
theorem subtype_comap_withDensity
    {E : Type*} [MeasurableSpace E] (U : Set E) (hU : MeasurableSet U)
    (μ : Measure E) (f : E → ENNReal) :
    (μ.comap (fun x : U => (x : E))).withDensity (f ∘ fun x : U => (x : E)) =
      (μ.withDensity f).comap (fun x : U => (x : E)) := by
  ext s hs
  let emb : U → E := fun x => (x : E)
  have hemb : MeasurableEmbedding emb := MeasurableEmbedding.subtype_coe hU
  have himg : MeasurableSet (emb '' s) := hemb.measurableSet_image' hs
  rw [withDensity_apply _ hs, hemb.comap_apply]
  rw [withDensity_apply f himg]
  rw [← lintegral_indicator hs]
  rw [← lintegral_indicator himg]
  have hsupport : Function.support ((emb '' s).indicator f) ⊆ U := by
    intro x hx
    by_contra hxU
    have hnot : x ∉ emb '' s := by
      rintro ⟨y, hy, rfl⟩
      exact hxU y.property
    simp [Function.mem_support, hnot] at hx
  rw [← setLIntegral_eq_of_support_subset hsupport]
  rw [← lintegral_subtype_comap hU ((emb '' s).indicator f)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · have him : emb x ∈ emb '' s := ⟨x, hx, rfl⟩
    simp [hx, him, emb]
  · have him : emb x ∉ emb '' s := by
      intro h
      rcases h with ⟨y, hy, hxy⟩
      exact hx (hemb.injective hxy.symm ▸ hy)
    simp [hx, him, emb]

/-- On the nonzero locus, the standard Gaussian pullback is exactly the radial
measure used by the polar product theorem. -/
theorem stdGaussian_comap_nonzero_eq_polarRadial
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    (stdGaussian E).comap (fun x : ({0}ᶜ : Set E) => (x : E)) =
      (volume.comap (fun x : ({0}ᶜ : Set E) => (x : E))).withDensity
        ((fun r : Set.Ioi (0 : ℝ) =>
          stdGaussianRadialDensity (Module.finrank ℝ E) r) ∘
            fun x => ((homeomorphUnitSphereProd E) x).2) := by
  rw [stdGaussian_eq_radial_withDensity E]
  rw [← subtype_comap_withDensity ({0}ᶜ : Set E) (measurableSet_singleton (0 : E)).compl
    volume (fun x : E => stdGaussianRadialDensity (Module.finrank ℝ E) ‖x‖)]
  congr 1
  funext x
  rw [Function.comp_apply, Function.comp_apply]
  congr 1
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- Direction-radius product law for a finite-dimensional standard Gaussian on its nonzero locus:
an exact product-measure identity. -/
theorem map_polar_stdGaussian_comap_nonzero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    Measure.map (homeomorphUnitSphereProd E)
        ((stdGaussian E).comap (fun x : ({0}ᶜ : Set E) => (x : E))) =
      volume.toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (fun r : Set.Ioi (0 : ℝ) =>
            stdGaussianRadialDensity (Module.finrank ℝ E) r)) := by
  rw [stdGaussian_comap_nonzero_eq_polarRadial E]
  apply map_polar_withDensity_radial
  unfold stdGaussianRadialDensity
  fun_prop

/-- Rectangle form of the exact standard-Gaussian polar product law. -/
theorem stdGaussian_comap_nonzero_polar_rectangle
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (s : Set (Metric.sphere (0 : E) 1))
    (t : Set (Set.Ioi (0 : ℝ)))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((stdGaussian E).comap (fun x : ({0}ᶜ : Set E) => (x : E)))
        (Set.preimage (homeomorphUnitSphereProd E) (s ×ˢ t)) =
      volume.toSphere s *
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (fun r : Set.Ioi (0 : ℝ) =>
            stdGaussianRadialDensity (Module.finrank ℝ E) r) t := by
  let μ := (stdGaussian E).comap (fun x : ({0}ᶜ : Set E) => (x : E))
  have hmap := map_polar_stdGaussian_comap_nonzero E
  calc
    μ (Set.preimage (homeomorphUnitSphereProd E) (s ×ˢ t)) =
        (Measure.map (homeomorphUnitSphereProd E).toMeasurableEquiv μ) (s ×ˢ t) := by
      symm
      exact Measure.map_apply (homeomorphUnitSphereProd E).measurable (hs.prod ht)
    _ = (volume.toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (fun r : Set.Ioi (0 : ℝ) =>
            stdGaussianRadialDensity (Module.finrank ℝ E) r))) (s ×ˢ t) := by
      change (Measure.map (homeomorphUnitSphereProd E) μ) (s ×ˢ t) = _
      rw [hmap]
    _ = _ := Measure.prod_prod s t

end PSSSNative.BlockBand.PSSS
