module

public import BlockBand.DeterminantScore.Sector.Inertia
public import BlockBand.DeterminantScore.Sector.LineCalculus
public import BlockBand.DeterminantScore.Sector.CoordinateFubini
public import BlockBand.DeterminantScore.PointwiseJacobi

/-!
# Sector cut-offs of polynomials vanishing on the determinant locus

The analytic core of the sector integration-by-parts lemma. For Hermitian `K`, a sector `ℓ` and
a complex polynomial `Q` in the Hermitian coordinates that vanishes wherever
`P = det(K + G(x))` vanishes (`Q = P²` and `Q = P · C_ab` below), put `cut Q = 1{N_-=ℓ} Q` and
`cutDeriv Q c = 1{N_-=ℓ} ∂_c Q`. We prove:

* `cut Q` is continuous (no jump across `{P = 0}`, since `Q = 0` there; elsewhere the sector
  is locally constant);
* on every coordinate line, `cut Q` is differentiable with derivative `cutDeriv Q c` off a
  countable set: off the finitely many real roots of the line polynomial `det(A + sE_c)` when it
  is nonzero, and everywhere when it vanishes identically (then `Q ≡ 0` on the line);
* hence `cutDeriv Q c` is the weak coordinate derivative (`Inputs.HasWeakCoordPartial`,
  Lebesgue, via Fubini along `c`);
* integrability under every product Gaussian, and the first Gaussian integration by parts
  `E[x_c cut Q] = v_c E[cutDeriv Q c]` (one-dimensional weak Gaussian IBP on almost every
  line, then Fubini).

The cutoff `χ(P/ε)` of the paper's proof is replaced by the one-dimensional fundamental theorem
of calculus with countably many exceptional points; both arguments prove the same identity (no
boundary term). No separate null-fibre step is needed: on a line where `det` vanishes
identically both sides vanish pointwise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory Filter Set MvPolynomial
open scoped Topology NNReal ContDiff
open BlockBand.Internal.Contracts

variable {m : ℕ}

/-- `1{N_-(K+G(x))=ℓ} Q(x)`. -/
def cut (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (Q : MvPolynomial (HermCoord m) ℂ)
    (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then realEval Q x else 0

/-- `1{N_-(K+G(x))=ℓ} ∂_c Q(x)`. -/
def cutDeriv (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (Q : MvPolynomial (HermCoord m) ℂ)
    (c : HermCoord m) (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then realEval (pderiv c Q) x else 0

/-- `Q` vanishes on the determinant locus `{det(K + G(x)) = 0}`. -/
def VanishesOnDet (K : Matrix (Fin m) (Fin m) ℂ) (Q : MvPolynomial (HermCoord m) ℂ) : Prop :=
  ∀ x, (K + hermOfCoord x).det = 0 → realEval Q x = 0

variable {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
  (Q : MvPolynomial (HermCoord m) ℂ)
include hK

theorem measurable_cut : Measurable (cut K ℓ Q) :=
  Measurable.ite (measurableSet_inSector hK ℓ) (continuous_realEval Q).measurable
    measurable_const

theorem measurable_cutDeriv (c : HermCoord m) : Measurable (cutDeriv K ℓ Q c) :=
  Measurable.ite (measurableSet_inSector hK ℓ) (continuous_realEval _).measurable
    measurable_const

theorem eventually_cut_eq {x : HermCoord m → ℝ} (hdet : (K + hermOfCoord x).det ≠ 0) :
    cut K ℓ Q =ᶠ[𝓝 x] (if InSector K ℓ x then realEval Q else fun _ => 0) := by
  filter_upwards [eventually_inSector_iff hK ℓ hdet] with y hy
  by_cases hx : InSector K ℓ x
  · simp [cut, hx, hy.mpr hx]
  · simp [cut, hx, mt hy.mp hx]

theorem continuous_cut (hQ : VanishesOnDet K Q) : Continuous (cut K ℓ Q) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hdet : (K + hermOfCoord x).det = 0
  · exact continuousAt_ite_zero_of_continuousAt_of_eq_zero _ _
      (continuous_realEval Q).continuousAt (hQ x hdet)
  · refine ContinuousAt.congr ?_ (eventually_cut_eq hK ℓ Q hdet).symm
    by_cases hx : InSector K ℓ x
    · simpa [hx] using (continuous_realEval Q).continuousAt
    · simpa [hx] using continuousAt_const

/-- Off `{P = 0}` the coordinate line of `cut Q` has the derivative `cutDeriv Q c`. -/
theorem hasDerivAt_cut_line (x : HermCoord m → ℝ) (c : HermCoord m) (s : ℝ)
    (hdet : (K + hermOfCoord (Function.update x c s)).det ≠ 0) :
    HasDerivAt (fun r => cut K ℓ Q (Function.update x c r))
      (cutDeriv K ℓ Q c (Function.update x c s)) s := by
  have hev := ((isClosedEmbedding_update x c).continuous.tendsto s).eventually
    (eventually_cut_eq hK ℓ Q hdet)
  by_cases hz : InSector K ℓ (Function.update x c s)
  · simp only [hz, ↓reduceIte] at hev
    simp only [cutDeriv, hz, ↓reduceIte]
    exact (hasDerivAt_realEval_update Q x c s).congr_of_eventuallyEq hev
  · simp only [hz, ↓reduceIte] at hev
    simp only [cutDeriv, hz, ↓reduceIte]
    exact (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq hev

/-- On every coordinate line, `cut Q` has derivative `cutDeriv Q c` off a countable set. -/
theorem exists_countable_line (hQ : VanishesOnDet K Q) (x : HermCoord m → ℝ)
    (c : HermCoord m) :
    ∃ T : Set ℝ, T.Countable ∧ ∀ s ∉ T,
      HasDerivAt (fun r => cut K ℓ Q (Function.update x c r))
        (cutDeriv K ℓ Q c (Function.update x c s)) s := by
  set A0 := K + hermOfCoord (Function.update x c 0)
  set E := hermOfCoord (m := m) (Pi.single c 1)
  have hline : ∀ r : ℝ, (K + hermOfCoord (Function.update x c r)).det =
      (detLinePoly A0 E).eval (r : ℂ) := by
    intro r
    rw [eval_detLinePoly_complex, hermOfCoord_update, ← add_assoc]
  by_cases hp : detLinePoly A0 E = 0
  · have hz : ∀ r : ℝ, realEval Q (Function.update x c r) = 0 := fun r =>
      hQ _ (by rw [hline, hp, Polynomial.eval_zero])
    have hcut : (fun r => cut K ℓ Q (Function.update x c r)) = fun _ => 0 :=
      funext fun r => by simp [cut, hz]
    refine ⟨∅, countable_empty, fun s _ => ?_⟩
    have hd0 : realEval (pderiv c Q) (Function.update x c s) = 0 := by
      have h1 := hasDerivAt_realEval_update Q x c s
      have h2 : (fun r : ℝ => realEval Q (Function.update x c r)) = fun _ => 0 := funext hz
      rw [h2] at h1
      exact h1.unique (hasDerivAt_const s 0)
    rw [hcut]
    have hv : cutDeriv K ℓ Q c (Function.update x c s) = 0 := by
      simp [cutDeriv, hd0]
    rw [hv]
    exact hasDerivAt_const s 0
  · refine ⟨{r : ℝ | (detLinePoly A0 E).eval (r : ℂ) = 0}, ?_, fun s hs =>
      hasDerivAt_cut_line hK ℓ Q x c s (by rw [hline]; exact hs)⟩
    have hfin : {z : ℂ | (detLinePoly A0 E).IsRoot z}.Finite :=
      Polynomial.finite_setOfPred_isRoot hp
    exact (hfin.preimage Complex.ofReal_injective.injOn).countable

theorem locallyIntegrable_cutDeriv (c : HermCoord m) :
    LocallyIntegrable (cutDeriv K ℓ Q c) volume :=
  (continuous_realEval (pderiv c Q)).locallyIntegrable.mono
    (measurable_cutDeriv hK ℓ Q c).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simp only [cutDeriv]
      split_ifs <;> simp)

/-- The weak derivative on every coordinate line. -/
theorem hasRealWeakDerivative_line (hQ : VanishesOnDet K Q) (x : HermCoord m → ℝ)
    (c : HermCoord m) :
    BlockBand.Model.Construction.HasRealWeakDerivative
      (fun r => cut K ℓ Q (Function.update x c r))
      (fun r => cutDeriv K ℓ Q c (Function.update x c r)) := by
  obtain ⟨T, hT, hd⟩ := exists_countable_line hK ℓ Q hQ x c
  have hcu : Continuous (Function.update x c) := (isClosedEmbedding_update x c).continuous
  refine hasRealWeakDerivative_of_hasDerivAt_off_countable
    ((continuous_cut hK ℓ Q hQ).comp hcu) ?_ hT hd
  exact ((continuous_realEval (pderiv c Q)).comp hcu).locallyIntegrable.mono
    ((measurable_cutDeriv hK ℓ Q c).comp hcu.measurable).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simp only [Function.comp_apply, cutDeriv]
      split_ifs <;> simp)

/-- **Weak coordinate derivative** (Lebesgue, distributional). -/
theorem hasWeakCoordPartial_cut (hQ : VanishesOnDet K Q) (c : HermCoord m) :
    Inputs.HasWeakCoordPartial c (cut K ℓ Q) (cutDeriv K ℓ Q c) := by
  refine ⟨(continuous_cut hK ℓ Q hQ).locallyIntegrable, locallyIntegrable_cutDeriv hK ℓ Q c,
    fun φ hφ hφs => ?_⟩
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hline (x0 : HermCoord m → ℝ) (s : ℝ) :
      HasDerivAt (fun r => φ (Function.update x0 c r))
        (fderiv ℝ φ (Function.update x0 c s) (Pi.single c 1)) s :=
    (hφd _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_update x0 c s)
  have hcp : Inputs.coordPartial φ c = fun x => fderiv ℝ φ x (Pi.single c 1) := by
    funext x
    unfold Inputs.coordPartial
    have h := (hline x (x c)).deriv
    rw [Function.update_eq_self] at h
    exact h
  rw [hcp]
  have hcont : Continuous fun x => fderiv ℝ φ x (Pi.single c 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ φ x (Pi.single c 1) :=
    hφs.fderiv_apply (𝕜 := ℝ) _
  have hI1 : Integrable (fun x => fderiv ℝ φ x (Pi.single c 1) • cut K ℓ Q x) :=
    (continuous_cut hK ℓ Q hQ).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      hcont hsupp
  have hI2 : Integrable (fun x => φ x • cutDeriv K ℓ Q c x) :=
    (locallyIntegrable_cutDeriv hK ℓ Q c).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφs
  rw [volume_pi] at hI1 hI2 ⊢
  rw [integral_eq_iterated _ c _ hI1, integral_eq_iterated _ c _ hI2, ← integral_neg]
  congr 1
  funext y
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = insertCoord c 0 y := ⟨_, rfl⟩
  have hins : ∀ s, insertCoord c s y = Function.update x0 c s :=
    fun s => hx0 ▸ insertCoord_eq_update c s y
  simp only [hins]
  have hw := (hasRealWeakDerivative_line hK ℓ Q hQ x0 c).2.2
    (fun r => φ (Function.update x0 c r)) (hφ.comp (contDiff_update ∞ x0 c))
    (hφs.comp_isClosedEmbedding (isClosedEmbedding_update x0 c))
  simp only [(hline x0 _).deriv] at hw
  exact hw

/-!
## Gaussian integrability and integration by parts
-/

variable (v : HermCoord m → ℝ≥0)

theorem integrable_cut :
    Integrable (cut K ℓ Q) (Measure.pi fun i => gaussianReal 0 (v i)) :=
  (integrable_realEval v Q).mono (measurable_cut hK ℓ Q).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simp only [cut]
      split_ifs <;> simp)

theorem integrable_cutDeriv (c : HermCoord m) :
    Integrable (cutDeriv K ℓ Q c) (Measure.pi fun i => gaussianReal 0 (v i)) :=
  (integrable_realEval v (pderiv c Q)).mono (measurable_cutDeriv hK ℓ Q c).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simp only [cutDeriv]
      split_ifs <;> simp)

theorem integrable_coord_smul_cut (c : HermCoord m) :
    Integrable (fun x => x c • cut K ℓ Q x) (Measure.pi fun i => gaussianReal 0 (v i)) :=
  (integrable_realEval v (X c * Q)).mono
    ((measurable_pi_apply c).smul (measurable_cut hK ℓ Q)).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simp only [cut, realEval_mul, realEval_X]
      split_ifs
      · simp
      · simp only [smul_zero, norm_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        positivity)

/-- **First Gaussian integration by parts** for a sector cut-off:
`E[x_c 1{N_-=ℓ} Q] = v_c E[1{N_-=ℓ} ∂_c Q]`. -/
theorem gaussian_ibp_cut (hQ : VanishesOnDet K Q) (c : HermCoord m) :
    (∫ x, x c • cut K ℓ Q x ∂Measure.pi fun i => gaussianReal 0 (v i)) =
      (v c : ℝ) • ∫ x, cutDeriv K ℓ Q c x ∂Measure.pi fun i => gaussianReal 0 (v i) := by
  set ν : HermCoord m → Measure ℝ := fun i => gaussianReal 0 (v i)
  have hI0 := integrable_cut hK ℓ Q v
  have hI1 := integrable_coord_smul_cut hK ℓ Q v c
  have hI2 := integrable_cutDeriv hK ℓ Q v c
  rw [integral_eq_iterated ν c _ hI1, integral_eq_iterated ν c _ hI2, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_integrable_line ν c _ hI0, ae_integrable_line ν c _ hI1,
    ae_integrable_line ν c _ hI2] with y h0 h1 h2
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 = insertCoord c 0 y := ⟨_, rfl⟩
  have hins : ∀ s, insertCoord c s y = Function.update x0 c s :=
    fun s => hx0 ▸ insertCoord_eq_update c s y
  simp only [insertCoord_self] at h1 ⊢
  simp only [hins] at h0 h1 h2 ⊢
  have h := BlockBand.Model.Construction.gaussian_weak_integration_by_parts 0 (v c)
    (hasRealWeakDerivative_line hK ℓ Q hQ x0 c) h0 h2
    (by simpa only [sub_zero] using h1)
  simpa only [sub_zero] using h

end BlockBand.DeterminantScore.Sector
