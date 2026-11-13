module

public import Mathlib
public import BlockBand.Adapters.ErdosRiabov.RingNativeLawGaussian
public import BlockBand.Adapters.ErdosRiabov.ShortRingLocalLawProfile
public import BlockBand.Model.Construction.GaussianCompatibility

/-!
# The physical Gaussian ring as an Erdős–Riabov law

Law identification: the matrix `√S ∘ h`, reindexed to the physical sites by the
row-major `siteFinEquiv p` (`x ↦ siteIndex x`), has a law satisfying
`IsPhysicalGaussianRingLaw` (Hermitian everywhere; joint characteristic function computed
from `ringOmega_characteristic`), hence by `physicalGaussianRingLaw_unique` it is the law of
every `p.GaussianRingModel`. No contract is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open MeasureTheory ProbabilityTheory BlockBand.External BlockBand.Counting
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal

/-!
### The profile on `Fin p.N`
-/

/-- The short-ring profile of the physical parameters, indexed by `Fin p.N`. -/
def ringProfile (p : Parameters) : Matrix (Fin p.N) (Fin p.N) ℝ :=
  shortRingProfile p.b p.n p.W

theorem ringProfile_symm (p : Parameters) (i j : Fin p.N) :
    ringProfile p i j = ringProfile p j i :=
  shortRingProfile_symm p.b p.n p.W i j

theorem ringProfile_nonneg (p : Parameters) (i j : Fin p.N) : 0 ≤ ringProfile p i j :=
  shortRingProfile_nonneg p.b_pos p.b_lt_half p.n p.W i j

theorem ringProfile_siteFinEquiv (p : Parameters) (x y : p.Site) :
    ringProfile p (siteFinEquiv p x) (siteFinEquiv p y) = p.entryVariance x y :=
  shortRingProfile_siteFinEquiv p x y

/-- [ER, Definition 2.1] profile clauses for the physical ring (bandwidth assumed). -/
theorem ringProfile_nativeProfile (q : ErdosRiabov.ModelParameters) (hCW : 1 ≤ q.CW)
    (p : Parameters) (hband : (p.N : ℝ) ^ (1 + q.zeta0) ≤ (p.W : ℝ) ^ 2) :
    ErdosRiabov.NativeProfile q p.N p.W (ringProfile p) :=
  shortRingProfile_nativeProfile q hCW p.b_pos p.b_lt_half
    (le_trans (by norm_num) p.n_ge_four) p.W_pos hband

/-!
### The three one-site value functions
-/

/-- The common one-site properties of a standardized entry value. -/
def IsSiteValue (F : ℝ × ℝ → ℂ) : Prop :=
  Continuous F ∧ (∀ r : ℝ≥0, MemLp F r standardCircularGaussian) ∧
    (∫ w, F w ∂standardCircularGaussian) = 0 ∧
    (∫ w, ‖F w‖ ^ 2 ∂standardCircularGaussian) = 1 ∧
    ∀ r : ℕ, (∫ w, ‖F w‖ ^ r ∂standardCircularGaussian) ≤ ringMomentBound r

/-- The off-diagonal one-site properties. -/
def IsOffSiteValue (F : ℝ × ℝ → ℂ) : Prop :=
  Integrable (fun w => F w ^ 2) standardCircularGaussian ∧
    (∫ w, F w ^ 2 ∂standardCircularGaussian) = 0

theorem isSiteValue_diag : IsSiteValue diagValue :=
  ⟨continuous_diagValue, memLp_diagValue, integral_diagValue, integral_norm_sq_diagValue,
    fun _ => le_max_left _ _⟩

theorem isSiteValue_circular : IsSiteValue circularGaussianCoordinate :=
  ⟨continuous_circular, memLp_circular, integral_circular, integral_norm_sq_circular,
    fun _ => le_max_right _ _⟩

theorem isOffSiteValue_circular : IsOffSiteValue circularGaussianCoordinate :=
  ⟨integrable_circular_sq, integral_circular_sq⟩

theorem continuous_conj_circular :
    Continuous (fun w : ℝ × ℝ => conj (circularGaussianCoordinate w)) :=
  Complex.continuous_conj.comp continuous_circular

theorem isSiteValue_conj_circular :
    IsSiteValue (fun w => conj (circularGaussianCoordinate w)) := by
  refine ⟨continuous_conj_circular, fun r => ?_, ?_, ?_, fun r => ?_⟩
  · exact (memLp_circular r).of_le continuous_conj_circular.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by simp)
  · rw [integral_conj, integral_circular, map_zero]
  · simp_rw [Complex.norm_conj]
    exact integral_norm_sq_circular
  · simp_rw [Complex.norm_conj]
    exact le_max_right _ _

theorem isOffSiteValue_conj_circular :
    IsOffSiteValue (fun w => conj (circularGaussianCoordinate w)) := by
  refine ⟨?_, ?_⟩
  · exact integrable_circular_sq.mono
      ((continuous_conj_circular.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => by simp [norm_pow])
  · simp_rw [← map_pow]
    rw [integral_conj, integral_circular_sq, map_zero]

/-- Every standardized entry is a site value of one coordinate pair, off-diagonal ones with
the off-diagonal properties. -/
theorem stdEntry_siteValue {N : ℕ} (i j : Fin N) : ∃ (q : ErdosRiabov.UpperPair N)
    (F : ℝ × ℝ → ℂ), (∀ ω : RingOmega N, stdEntry ω i j = F (ω q)) ∧ IsSiteValue F ∧
      (i ≠ j → IsOffSiteValue F) := by
  obtain ⟨q, F, hF, hc⟩ := stdEntry_cases (N := N) i j
  refine ⟨q, F, hF, ?_, ?_⟩
  · rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact isSiteValue_diag
    · exact isSiteValue_circular
    · exact isSiteValue_conj_circular
  · intro hij
    rcases hc with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact absurd h hij
    · exact isOffSiteValue_circular
    · exact isOffSiteValue_conj_circular

theorem stdEntry_fun_eq {N : ℕ} {i j : Fin N} {q : ErdosRiabov.UpperPair N}
    {F : ℝ × ℝ → ℂ} (hF : ∀ ω : RingOmega N, stdEntry ω i j = F (ω q)) (g : ℂ → ℂ) :
    (fun ω : RingOmega N => g (stdEntry ω i j)) = fun ω => g (F (ω q)) := by
  funext ω
  rw [hF]

/-!
### The law
-/

/-- The standardized entry matrix. -/
def stdMatrix {N : ℕ} (ω : RingOmega N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => stdEntry ω i j

theorem stdMatrix_isHermitian {N : ℕ} (ω : RingOmega N) : (stdMatrix ω).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, stdMatrix]
  exact stdEntry_conj ω i j

/-- `ShortRing → ER native law` ([ER, Definition 2.1]) for the physical ring `p`. -/
def ringNativeLaw (q : ErdosRiabov.ModelParameters) (p : Parameters)
    (hprof : ErdosRiabov.NativeProfile q p.N p.W (ringProfile p))
    (hmb : ∀ r, ringMomentBound r ≤ q.momentBound r) : ErdosRiabov.NativeLaw.{0} q p.N p.W where
  Ω := RingOmega p.N
  mΩ := inferInstance
  P := ringOmegaMeasure p.N
  probability := inferInstance
  symmetry := .complexHermitian
  S := ringProfile p
  profile := hprof
  h := stdMatrix
  hermitian := stdMatrix_isHermitian
  measurable_entry := fun i j => measurable_stdEntry i j
  upper_independent := by
    have h := iIndepFun_pi (μ := fun _ : ErdosRiabov.UpperPair p.N => standardCircularGaussian)
      (X := fun q => upperValue q) (fun q => (measurable_upperValue q).aemeasurable)
    have he : (fun (q : ErdosRiabov.UpperPair p.N) (ω : RingOmega p.N) =>
        stdMatrix ω q.1.1 q.1.2) = fun q ω => upperValue q (ω q) := by
      funext q ω
      exact stdEntry_upper ω q
    rw [he]
    exact h
  entry_integrable := fun i j => by
    obtain ⟨q, F, hF, hv, -⟩ := stdEntry_siteValue (N := p.N) i j
    have := integrable_ringOmega_eval q hv.1 (memLp_one_iff_integrable.mp (hv.2.1 1))
    simpa only [stdMatrix, ← hF] using this
  mean_zero := fun i j => by
    obtain ⟨q, F, hF, hv, -⟩ := stdEntry_siteValue (N := p.N) i j
    simp only [stdMatrix, hF]
    rw [integral_ringOmega_eval q hv.1, hv.2.2.1]
  moment_integrable := fun r i j => by
    obtain ⟨q, F, hF, hv, -⟩ := stdEntry_siteValue (N := p.N) i j
    have := integrable_ringOmega_eval q (g := fun w => ‖F w‖ ^ r) (hv.1.norm.pow r)
      (integrable_norm_pow_of_memLp hv.2.1 r)
    simpa only [stdMatrix, ← hF] using this
  variance_one := fun i j => by
    obtain ⟨q, F, hF, hv, -⟩ := stdEntry_siteValue (N := p.N) i j
    simp only [stdMatrix, hF]
    rw [integral_ringOmega_eval_real q (g := fun w => ‖F w‖ ^ 2) (hv.1.norm.pow 2),
      hv.2.2.2.1]
  moment_bound := fun r i j => by
    obtain ⟨q, F, hF, hv, -⟩ := stdEntry_siteValue (N := p.N) i j
    simp only [stdMatrix, hF]
    rw [integral_ringOmega_eval_real q (g := fun w => ‖F w‖ ^ r) (hv.1.norm.pow r)]
    exact (hv.2.2.2.2 r).trans (hmb r)
  real_entries := fun h => by cases h
  offdiag_square_integrable := fun _ i j hij => by
    obtain ⟨q, F, hF, hv, hoff⟩ := stdEntry_siteValue (N := p.N) i j
    have := integrable_ringOmega_eval q (g := fun w => F w ^ 2) (hv.1.pow 2) (hoff hij).1
    simpa only [stdMatrix, ← hF] using this
  offdiag_square_zero := fun _ i j hij => by
    obtain ⟨q, F, hF, hv, hoff⟩ := stdEntry_siteValue (N := p.N) i j
    simp only [stdMatrix, hF]
    rw [integral_ringOmega_eval q (g := fun w => F w ^ 2) (hv.1.pow 2), (hoff hij).2]

/-!
### The physical matrix and its law
-/

/-- The matrix `√S ∘ h` read at the physical sites. -/
def ringPhysMatrix (p : Parameters) (ω : RingOmega p.N) : p.SiteMatrix :=
  fun x y => (Real.sqrt (ringProfile p (siteFinEquiv p x) (siteFinEquiv p y)) : ℂ) *
    stdEntry ω (siteFinEquiv p x) (siteFinEquiv p y)

theorem ringPhysMatrix_eq_submatrix (q : ErdosRiabov.ModelParameters) (p : Parameters)
    (hprof : ErdosRiabov.NativeProfile q p.N p.W (ringProfile p))
    (hmb : ∀ r, ringMomentBound r ≤ q.momentBound r) (ω : RingOmega p.N) :
    ringPhysMatrix p ω =
      ((ringNativeLaw q p hprof hmb).matrix ω).submatrix (siteFinEquiv p) (siteFinEquiv p) :=
  rfl

theorem measurable_ringPhysMatrix (p : Parameters) : Measurable (ringPhysMatrix p) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact measurable_const.mul (measurable_stdEntry _ _)

theorem ringPhysMatrix_isHermitian (p : Parameters) (ω : RingOmega p.N) :
    (ringPhysMatrix p ω).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, ringPhysMatrix, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  rw [stdEntry_conj, ringProfile_symm]

/-- Sum over upper pairs: diagonal plus strict upper part. -/
theorem upperPair_sum {N : ℕ} (f : ErdosRiabov.UpperPair N → ℝ) :
    (∑ q, f q) = (∑ i : Fin N, f ⟨(i, i), le_rfl⟩) +
      ∑ i : Fin N, ∑ j : Fin N, if h : i < j then f ⟨(i, j), h.le⟩ else 0 := by
  classical
  set f' : Fin N × Fin N → ℝ := fun x => if h : x.1 ≤ x.2 then f ⟨x, h⟩ else 0 with hf'
  have h1 : (∑ q, f q) = ∑ q : ErdosRiabov.UpperPair N, f' q.1 := by
    apply Finset.sum_congr rfl
    intro q _
    rw [hf']
    dsimp only
    split_ifs with h
    · rfl
    · exact absurd q.2 h
  have h2 : (∑ q : ErdosRiabov.UpperPair N, f' q.1) = ∑ x : Fin N × Fin N, f' x := by
    have hs := Finset.sum_subtype (F := ringUpperPairFintype N)
      (p := fun x : Fin N × Fin N => x.1 ≤ x.2)
      (Finset.univ.filter fun x : Fin N × Fin N => x.1 ≤ x.2) (by simp) f'
    change (∑ q : {x : Fin N × Fin N // x.1 ≤ x.2}, f' q.1) = _
    rw [← hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · rfl
    · simp [hf', h]
  rw [h1, h2, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hpt : ∀ j : Fin N, f' (i, j) =
      (if h : i = j then f ⟨(i, j), h.le⟩ else 0) +
        (if h : i < j then f ⟨(i, j), h.le⟩ else 0) := by
    intro j
    rw [hf']
    dsimp only
    by_cases h : i = j
    · subst h
      simp
    · by_cases hlt : i < j
      · simp [h, hlt, hlt.le]
      · have : ¬ i ≤ j := fun hle => hlt (lt_of_le_of_ne hle h)
        simp [h, hlt, this]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_dite_eq]
  simp

theorem stdEntry_self {N : ℕ} (ω : RingOmega N) (i : Fin N) :
    stdEntry ω i i = diagValue (ω ⟨(i, i), le_rfl⟩) := by
  simp [stdEntry]

theorem stdEntry_of_lt {N : ℕ} (ω : RingOmega N) {i j : Fin N} (h : i < j) :
    stdEntry ω i j = circularGaussianCoordinate (ω ⟨(i, j), h.le⟩) := by
  simp [stdEntry, h.ne, h]

theorem circular_re (w : ℝ × ℝ) : (circularGaussianCoordinate w).re = w.1 := by
  simp [circularGaussianCoordinate]

theorem circular_im (w : ℝ × ℝ) : (circularGaussianCoordinate w).im = w.2 := by
  simp [circularGaussianCoordinate]

/-- The coefficient of the real component in the physical pairing. -/
def pairCoeffRe (p : Parameters) (d : p.Site → ℝ) (u : p.Site → p.Site → ℝ)
    (q : ErdosRiabov.UpperPair p.N) : ℝ :=
  if q.1.1 = q.1.2 then
    d ((siteFinEquiv p).symm q.1.1) * Real.sqrt (ringProfile p q.1.1 q.1.1) * Real.sqrt 2
  else u ((siteFinEquiv p).symm q.1.1) ((siteFinEquiv p).symm q.1.2) *
      Real.sqrt (ringProfile p q.1.1 q.1.2)

/-- The coefficient of the imaginary component in the physical pairing. -/
def pairCoeffIm (p : Parameters) (v : p.Site → p.Site → ℝ)
    (q : ErdosRiabov.UpperPair p.N) : ℝ :=
  if q.1.1 = q.1.2 then 0
  else v ((siteFinEquiv p).symm q.1.1) ((siteFinEquiv p).symm q.1.2) *
      Real.sqrt (ringProfile p q.1.1 q.1.2)

theorem pairCoeffRe_self (p : Parameters) (d : p.Site → ℝ) (u : p.Site → p.Site → ℝ)
    (x : p.Site) :
    pairCoeffRe p d u ⟨(siteFinEquiv p x, siteFinEquiv p x), le_rfl⟩ =
      d x * Real.sqrt (ringProfile p (siteFinEquiv p x) (siteFinEquiv p x)) * Real.sqrt 2 := by
  simp [pairCoeffRe]

theorem pairCoeffIm_self (p : Parameters) (v : p.Site → p.Site → ℝ) (x : p.Site) :
    pairCoeffIm p v ⟨(siteFinEquiv p x, siteFinEquiv p x), le_rfl⟩ = 0 := by
  simp [pairCoeffIm]

theorem pairCoeffRe_of_lt (p : Parameters) (d : p.Site → ℝ) (u : p.Site → p.Site → ℝ)
    {x y : p.Site} (h : siteFinEquiv p x < siteFinEquiv p y) :
    pairCoeffRe p d u ⟨(siteFinEquiv p x, siteFinEquiv p y), h.le⟩ =
      u x y * Real.sqrt (ringProfile p (siteFinEquiv p x) (siteFinEquiv p y)) := by
  simp [pairCoeffRe, h.ne]

theorem pairCoeffIm_of_lt (p : Parameters) (v : p.Site → p.Site → ℝ)
    {x y : p.Site} (h : siteFinEquiv p x < siteFinEquiv p y) :
    pairCoeffIm p v ⟨(siteFinEquiv p x, siteFinEquiv p y), h.le⟩ =
      v x y * Real.sqrt (ringProfile p (siteFinEquiv p x) (siteFinEquiv p y)) := by
  simp [pairCoeffIm, h.ne]

theorem siteFinEquiv_lt_iff (p : Parameters) (x y : p.Site) :
    siteFinEquiv p x < siteFinEquiv p y ↔ p.siteIndex x < p.siteIndex y := by
  rw [Fin.lt_def, siteFinEquiv_val, siteFinEquiv_val]

/-- The physical coordinate pairing of the matrix is a real-linear form in the
independent coordinates. -/
theorem coordinatePairing_ringPhysMatrix (p : Parameters) (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) (ω : RingOmega p.N) :
    p.coordinatePairing d u v (ringPhysMatrix p ω) =
      ∑ q, (pairCoeffRe p d u q * (ω q).1 + pairCoeffIm p v q * (ω q).2) := by
  classical
  rw [upperPair_sum]
  unfold Parameters.coordinatePairing
  congr 1
  · rw [← (siteFinEquiv p).sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [pairCoeffRe_self, pairCoeffIm_self]
    unfold ringPhysMatrix
    rw [stdEntry_self, Complex.re_ofReal_mul]
    simp only [diagValue, Complex.ofReal_re]
    ring
  · rw [← (siteFinEquiv p).sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [← (siteFinEquiv p).sum_comp, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : siteFinEquiv p x < siteFinEquiv p y
    · have hidx : p.siteIndex x < p.siteIndex y := (siteFinEquiv_lt_iff p x y).mp h
      simp only [hidx, h, ↓reduceIte, ↓reduceDIte]
      rw [pairCoeffRe_of_lt p d u h, pairCoeffIm_of_lt p v h]
      unfold ringPhysMatrix
      rw [stdEntry_of_lt ω h, Complex.re_ofReal_mul, Complex.im_ofReal_mul, circular_re,
        circular_im]
      ring
    · have hidx : ¬ p.siteIndex x < p.siteIndex y := fun h' =>
        h ((siteFinEquiv_lt_iff p x y).mpr h')
      simp only [hidx, h, ↓reduceIte, ↓reduceDIte]

/-- The variance of the real-linear form is the physical quadratic form. -/
theorem coordinateVariance_ringPhys (p : Parameters) (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) :
    (∑ q, (1 : ℝ) / 2 * (pairCoeffRe p d u q ^ 2 + pairCoeffIm p v q ^ 2)) =
      p.coordinateVariance d u v := by
  classical
  have hS : ∀ x y : p.Site,
      Real.sqrt (ringProfile p (siteFinEquiv p x) (siteFinEquiv p y)) ^ 2 =
        p.entryVariance x y := by
    intro x y
    rw [Real.sq_sqrt (ringProfile_nonneg p _ _), ringProfile_siteFinEquiv]
  rw [upperPair_sum]
  unfold Parameters.coordinateVariance
  congr 1
  · rw [← (siteFinEquiv p).sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [pairCoeffRe_self, pairCoeffIm_self, mul_pow, mul_pow, hS,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · rw [← (siteFinEquiv p).sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [← (siteFinEquiv p).sum_comp, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : siteFinEquiv p x < siteFinEquiv p y
    · have hidx : p.siteIndex x < p.siteIndex y := (siteFinEquiv_lt_iff p x y).mp h
      simp only [hidx, h, ↓reduceIte, ↓reduceDIte]
      rw [pairCoeffRe_of_lt p d u h, pairCoeffIm_of_lt p v h, mul_pow, mul_pow, hS]
      ring
    · have hidx : ¬ p.siteIndex x < p.siteIndex y := fun h' =>
        h ((siteFinEquiv_lt_iff p x y).mpr h')
      simp only [hidx, h, ↓reduceIte, ↓reduceDIte]

/-- The coordinate product law as a probability measure. -/
def ringOmegaProb (N : ℕ) : ProbabilityMeasure (RingOmega N) :=
  ⟨ringOmegaMeasure N, inferInstance⟩

/-- The law of the ring matrix at the physical sites is the physical law
of the model: Hermitian support and the joint characteristic function. -/
theorem ringPhys_isPhysical (p : Parameters) :
    p.IsPhysicalGaussianRingLaw ((ringOmegaProb p.N).map (ringPhysMatrix p)) := by
  have hmeas := measurable_ringPhysMatrix p
  refine ⟨?_, ?_⟩
  · change ∀ᵐ H ∂Measure.map (ringPhysMatrix p) (ringOmegaMeasure p.N), H.IsHermitian
    rw [ae_map_iff hmeas.aemeasurable]
    · filter_upwards with ω
      exact ringPhysMatrix_isHermitian p ω
    · exact (isClosed_eq (by fun_prop : Continuous (fun H : p.SiteMatrix => H.conjTranspose))
        continuous_id).measurableSet
  · intro d u v
    change (∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
      ∂Measure.map (ringPhysMatrix p) (ringOmegaMeasure p.N)) = _
    rw [integral_map hmeas.aemeasurable
      (show Continuous (fun H : p.SiteMatrix =>
          Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))) by
        unfold Parameters.coordinatePairing
        fun_prop).aestronglyMeasurable]
    simp_rw [coordinatePairing_ringPhysMatrix]
    rw [ringOmega_characteristic, coordinateVariance_ringPhys]

/-- The ring construction as a physical model. -/
def ringPhysicalModel (p : Parameters) : p.GaussianRingModel :=
  ⟨(ringOmegaProb p.N).map (ringPhysMatrix p), ringPhys_isPhysical p⟩

/-- Every physical model has the law of the ring matrix at the physical sites. -/
theorem model_law_eq_ringPhys (p : Parameters) (model : p.GaussianRingModel) :
    (model.law : Measure p.SiteMatrix) =
      Measure.map (ringPhysMatrix p) (ringOmegaMeasure p.N) := by
  rw [Parameters.physicalGaussianRingLaw_unique model (ringPhysicalModel p)]
  exact ProbabilityMeasure.toMeasure_map _

end BlockBand.Adapters.ErdosRiabov
