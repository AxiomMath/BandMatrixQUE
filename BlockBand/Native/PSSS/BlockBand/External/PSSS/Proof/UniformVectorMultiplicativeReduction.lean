module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorGaussianPolar
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorGaussianRadius
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorSpectralTrace

/-!
# Multiplicative radius reduction for uniform vectors

For a complex standard Gaussian, the normalized direction is independent of the radius. Hence a
small-image event `‖Q φ‖ ≤ a` for a uniform unit vector `φ` is controlled, up to a factor two, by
the Gaussian small-image event `‖Q g‖ ≤ 2a√N`. The Gaussian event is then rewritten in the
spectral coordinates of the real Gram operator of `Q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- In positive complex dimension, inclusion of the nonzero locus transports the
pulled-back standard Gaussian back to the full standard Gaussian.  The only
omitted point is the origin, whose Gaussian mass is zero. -/
theorem measurePreserving_nonzero_inclusion_stdGaussian {N : ℕ} (hN : 0 < N) :
    MeasurePreserving
      (fun x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin N))) =>
        (x : EuclideanSpace ℂ (Fin N)))
      ((stdGaussian (EuclideanSpace ℂ (Fin N))).comap
        (fun x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin N))) =>
          (x : EuclideanSpace ℂ (Fin N))))
      (stdGaussian (EuclideanSpace ℂ (Fin N))) := by
  let E := EuclideanSpace ℂ (Fin N)
  let ι : ({0}ᶜ : Set E) → E := fun x => (x : E)
  have hemb : MeasurableEmbedding ι :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  refine ⟨hemb.measurable, ?_⟩
  rw [hemb.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  have hrange : {a : E | a ∉ Set.range ι} = {0} := by
    ext a
    simp [ι]
  rw [hrange]
  simpa [E] using stdGaussian_complex_singleton_zero hN

set_option maxHeartbeats 800000 in
/-- For the complex standard Gaussian, a matrix small-image event of the
normalized direction is exactly independent of a radius truncation.  This is
the multiplicative replacement for the additive radius-tail reduction. -/
theorem uniformSphere_mul_gaussian_radius_eq_direction_inter {N : ℕ} (hN : 0 < N)
    (Q : Matrix (Fin N) (Fin N) ℂ) (a R : ℝ) :
    uniformSphere N (mulVecNormLeEvent Q a) *
        stdGaussian (EuclideanSpace ℂ (Fin N)) {g | ‖g‖ ≤ R} =
      stdGaussian (EuclideanSpace ℂ (Fin N))
        ((complexGaussianDirection ⁻¹' mulVecNormLeEvent Q a) ∩ {g | ‖g‖ ≤ R}) := by
  let E := EuclideanSpace ℂ (Fin N)
  let μ := stdGaussian E
  let ι : ({0}ᶜ : Set E) → E := fun x => (x : E)
  let μ₀ := μ.comap ι
  let polar := homeomorphUnitSphereProd E
  let s : Set (Metric.sphere (0 : E) 1) :=
    {u | (u : E) ∈ mulVecNormLeEvent Q a}
  let t : Set (Set.Ioi (0 : ℝ)) := {r | (r : ℝ) ≤ R}
  have hs : MeasurableSet s := by
    exact (measurableSet_mulVecNormLeEvent Q a).preimage measurable_subtype_coe
  have ht : MeasurableSet t := by
    exact measurableSet_le measurable_subtype_coe measurable_const
  have hι := measurePreserving_nonzero_inclusion_stdGaussian hN
  have hpolar := stdGaussian_comap_nonzero_polar_rectangle E s t hs ht
  have hrect :
      ι ⁻¹' ((complexGaussianDirection ⁻¹' mulVecNormLeEvent Q a) ∩
        {g : E | ‖g‖ ≤ R}) =
        polar ⁻¹' (s ×ˢ t) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_prod, s, t, ι, polar]
    rw [complexGaussianDirection_eq_polar_fst x, norm_eq_polar_snd x]
  have hinter :
      μ ((complexGaussianDirection ⁻¹' mulVecNormLeEvent Q a) ∩
        {g : E | ‖g‖ ≤ R}) =
        volume.toSphere s *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
            (fun r : Set.Ioi (0 : ℝ) =>
              stdGaussianRadialDensity (Module.finrank ℝ E) r) t := by
    rw [← hι.measure_preimage
      ((measurable_complexGaussianDirection
        (N := N) (measurableSet_mulVecNormLeEvent Q a)).inter
          (measurableSet_le measurable_norm measurable_const)).nullMeasurableSet]
    change μ₀ (ι ⁻¹' _) = _
    rw [hrect]
    exact hpolar
  have htotal :
      volume.toSphere (Set.univ : Set (Metric.sphere (0 : E) 1)) *
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (fun r : Set.Ioi (0 : ℝ) =>
            stdGaussianRadialDensity (Module.finrank ℝ E) r) Set.univ = 1 := by
    have hmap := map_polar_stdGaussian_comap_nonzero E
    have hsource : μ₀ Set.univ = 1 := by
      have hmap_univ := congrArg (fun ν : Measure E => ν Set.univ) hι.map_eq
      rw [Measure.map_apply hι.measurable MeasurableSet.univ, Set.preimage_univ] at hmap_univ
      simpa [μ] using hmap_univ
    rw [← Measure.prod_prod (μ := volume.toSphere)
      (ν := (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
        (fun r : Set.Ioi (0 : ℝ) =>
          stdGaussianRadialDensity (Module.finrank ℝ E) r)) Set.univ Set.univ]
    have huniv :
        (Set.univ : Set (Metric.sphere (0 : E) 1)) ×ˢ
            (Set.univ : Set (Set.Ioi (0 : ℝ))) = Set.univ := by
      ext x
      simp
    rw [huniv, ← hmap, Measure.map_apply polar.measurable MeasurableSet.univ,
      Set.preimage_univ, hsource]
  have hdirection :
      uniformSphere N (mulVecNormLeEvent Q a) =
        volume.toSphere s *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
            (fun r : Set.Ioi (0 : ℝ) =>
              stdGaussianRadialDensity (Module.finrank ℝ E) r) Set.univ := by
    rw [uniformSphere_apply_measurableSet (measurableSet_mulVecNormLeEvent Q a)]
    have hfull := stdGaussian_comap_nonzero_polar_rectangle E s Set.univ hs
      MeasurableSet.univ
    have hpre :
        ι ⁻¹' (complexGaussianDirection ⁻¹' mulVecNormLeEvent Q a) =
          polar ⁻¹' (s ×ˢ Set.univ) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, s, ι, polar]
      rw [complexGaussianDirection_eq_polar_fst x]
      rfl
    rw [← hι.measure_preimage
      (measurable_complexGaussianDirection
        (N := N) (measurableSet_mulVecNormLeEvent Q a)).nullMeasurableSet]
    change μ₀ (ι ⁻¹' _) = _
    rw [hpre, hfull]
  have hradius :
      μ {g : E | ‖g‖ ≤ R} =
        volume.toSphere (Set.univ : Set (Metric.sphere (0 : E) 1)) *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (fun r : Set.Ioi (0 : ℝ) =>
            stdGaussianRadialDensity (Module.finrank ℝ E) r) t := by
    have hfull := stdGaussian_comap_nonzero_polar_rectangle E Set.univ t
      MeasurableSet.univ ht
    have hpre :
        ι ⁻¹' {g : E | ‖g‖ ≤ R} = polar ⁻¹' (Set.univ ×ˢ t) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ,
        true_and, t, ι, polar]
      rw [norm_eq_polar_snd x]
    rw [← hι.measure_preimage
      (measurableSet_le measurable_norm measurable_const).nullMeasurableSet]
    change μ₀ (ι ⁻¹' _) = _
    rw [hpre, hfull]
  rw [hdirection, hradius, hinter]
  calc
    (volume.toSphere s *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
            (fun r : Set.Ioi (0 : ℝ) =>
              stdGaussianRadialDensity (Module.finrank ℝ E) r) Set.univ) *
        (volume.toSphere Set.univ *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
            (fun r : Set.Ioi (0 : ℝ) =>
              stdGaussianRadialDensity (Module.finrank ℝ E) r) t) =
      (volume.toSphere s *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
            (fun r : Set.Ioi (0 : ℝ) =>
              stdGaussianRadialDensity (Module.finrank ℝ E) r) t) *
        (volume.toSphere Set.univ *
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
            (fun r : Set.Ioi (0 : ℝ) =>
              stdGaussianRadialDensity (Module.finrank ℝ E) r) Set.univ) := by
        ring
    _ = _ := by rw [htotal, mul_one]

/-- Multiplicative radius reduction: after exact direction–radius factorization,
the truncated directional event is bounded by the corresponding unnormalized
Gaussian small-image event. -/
theorem uniformSphere_mul_gaussian_radius_le_gaussian_smallBall {N : ℕ} (hN : 0 < N)
    (Q : Matrix (Fin N) (Fin N) ℂ) {a R : ℝ} (ha : 0 ≤ a) :
    uniformSphere N (mulVecNormLeEvent Q a) *
        stdGaussian (EuclideanSpace ℂ (Fin N)) {g | ‖g‖ ≤ R} ≤
      stdGaussian (EuclideanSpace ℂ (Fin N)) (mulVecNormLeEvent Q (a * R)) := by
  rw [uniformSphere_mul_gaussian_radius_eq_direction_inter hN Q a R]
  exact measure_mono (direction_smallBall_inter_radius_subset Q ha)

/-- At the radius `2√N`, the good-radius event for the complex standard Gaussian has
probability at least one half. -/
theorem half_le_stdGaussian_complex_norm_le {N : ℕ} (hN : 0 < N) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      stdGaussian (EuclideanSpace ℂ (Fin N)) {g | ‖g‖ ≤ 2 * Real.sqrt N} := by
  let μ := stdGaussian (EuclideanSpace ℂ (Fin N))
  let bad : Set (EuclideanSpace ℂ (Fin N)) := {g | 2 * Real.sqrt N < ‖g‖}
  have hbad : μ bad ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
    stdGaussian_complex_norm_tail_le_half hN
  have hgood :
      μ badᶜ = 1 - μ bad :=
    prob_compl_eq_one_sub (measurableSet_lt measurable_const measurable_norm)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = 1 - ENNReal.ofReal (1 / 2 : ℝ) := by
    have hof : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hof, ENNReal.one_sub_inv_two]
  have hset : badᶜ = {g : EuclideanSpace ℂ (Fin N) | ‖g‖ ≤ 2 * Real.sqrt N} := by
    ext g
    simp [bad]
  rw [← hset, hgood, hhalf]
  exact tsub_le_tsub_left hbad 1

/-- Event-level form used by the APSSS spherical small-ball estimate: one half of the
spherical small-image probability is bounded by the Gaussian small-image probability with
threshold scaled by `2√N`, with no additive radius-tail loss. -/
theorem half_mul_uniformSphere_mulVec_le_gaussian_smallBall {N : ℕ} (hN : 0 < N)
    (Q : Matrix (Fin N) (Fin N) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal (1 / 2 : ℝ) *
        uniformSphere N (mulVecNormLeEvent Q a) ≤
      stdGaussian (EuclideanSpace ℂ (Fin N))
        (mulVecNormLeEvent Q (a * (2 * Real.sqrt N))) := by
  calc
    ENNReal.ofReal (1 / 2 : ℝ) *
        uniformSphere N (mulVecNormLeEvent Q a) ≤
      uniformSphere N (mulVecNormLeEvent Q a) *
        stdGaussian (EuclideanSpace ℂ (Fin N))
          {g | ‖g‖ ≤ 2 * Real.sqrt N} := by
            rw [mul_comm (ENNReal.ofReal (1 / 2 : ℝ))]
            gcongr
            exact half_le_stdGaussian_complex_norm_le hN
    _ ≤ _ := uniformSphere_mul_gaussian_radius_le_gaussian_smallBall hN Q ha

/-- Exact event-level transport of a complex Gaussian matrix image into the
orthogonal spectral coordinates of its positive real Gram operator.  The weights
are nonnegative by `eigenvalues_complexGramRealification_nonneg`, and their sum is
twice the squared complex Frobenius norm by
`sum_eigenvalues_complexGramRealification`. -/
theorem stdGaussian_mulVecNormLeEvent_eq_pi_spectral {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) {a : ℝ} (ha : 0 ≤ a) :
    let T := Matrix.toEuclideanLin (complexGramRealification Q)
    let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
    let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
        Fintype.card (Fin N × Fin 2) := by simp
    stdGaussian (EuclideanSpace ℂ (Fin N)) (mulVecNormLeEvent Q a) =
      Measure.pi
        (fun _ : Fin (Fintype.card (Fin N × Fin 2)) => gaussianReal 0 1)
        {x | (∑ k, hT.eigenvalues hdim k * (x k) ^ 2) ≤ a ^ 2} := by
  dsimp only
  let T := Matrix.toEuclideanLin (complexGramRealification Q)
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
      Fintype.card (Fin N × Fin 2) := by simp
  let F : EuclideanSpace ℂ (Fin N) →
      (Fin (Fintype.card (Fin N × Fin 2)) → ℝ) :=
    fun z => WithLp.ofLp ((hT.eigenvectorBasis hdim).repr
      (complexEuclideanRealification N z))
  let A : Set (Fin (Fintype.card (Fin N × Fin 2)) → ℝ) :=
    {x | (∑ k, hT.eigenvalues hdim k * (x k) ^ 2) ≤ a ^ 2}
  have hA : MeasurableSet A := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hmap := map_complexGramSpectralCoordinates_stdGaussian Q
  have hpre : F ⁻¹' A = mulVecNormLeEvent Q a := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, A, F]
    have hspectral := complexGramRealification_spectralQuadraticForm Q (WithLp.ofLp z)
    dsimp only at hspectral
    change
      (∑ k, hT.eigenvalues hdim k *
          (WithLp.ofLp ((hT.eigenvectorBasis hdim).repr
            (complexEuclideanRealification N z)) k) ^ 2) ≤ a ^ 2 ↔
        z ∈ mulVecNormLeEvent Q a
    rw [complexEuclideanRealification_apply]
    have hnormsq :
        ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp z) :
          EuclideanSpace ℂ (Fin N))‖ ^ 2 =
          ∑ i : Fin N, ‖(Q *ᵥ WithLp.ofLp z) i‖ ^ 2 := by
      exact EuclideanSpace.norm_sq_eq _
    rw [hspectral, ← hnormsq]
    unfold mulVecNormLeEvent
    change
      ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp z) :
        EuclideanSpace ℂ (Fin N))‖ ^ 2 ≤ a ^ 2 ↔
      ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp z) :
        EuclideanSpace ℂ (Fin N))‖ ≤ a
    constructor <;> intro h <;>
      nlinarith [norm_nonneg
        (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp z) :
          EuclideanSpace ℂ (Fin N))]
  change stdGaussian (EuclideanSpace ℂ (Fin N)) (mulVecNormLeEvent Q a) =
    Measure.pi
      (fun _ : Fin (Fintype.card (Fin N × Fin 2)) => gaussianReal 0 1) A
  rw [← hmap]
  rw [Measure.map_apply (by fun_prop : Measurable F) hA, hpre]

end PSSSNative.BlockBand.PSSS
