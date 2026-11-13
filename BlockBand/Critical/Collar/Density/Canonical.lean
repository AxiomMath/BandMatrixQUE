module

public import BlockBand.Critical.Collar.Density.SpectralSum
public import BlockBand.Critical.Collar.Density.CommonShift
public import BlockBand.Critical.Collar.Density.RowBound
public import BlockBand.Critical.WeightedDensity.Global

/-!
# The canonical continuous collar density `Ψ_X` (`PLAN.md` §2.1)

*Law.* `collarLaw W b`, `W ≥ 1`, `0 < b < 1/2` (only `b < 1/2` is used here), deterministic
Hermitian `X` (no norm bound). By `collarLaw_commonShift`, `collarLaw = (μ' ⊗ N(0,s)).map shift`,
`s = commonShiftVar W b = c/(3W²)`, and `ℋ_X(shift θ ω') = ℋ_X(ω') + θ I`.

*Definition.* `collarDensity W b e X x = E_{μ'}[φ_s(x - ℋ_X)]₁₁` (entrywise; `φ_s` the
`N(0,s)` density, Mathlib `cfc`).

*Results.*
* `continuous_collarDensity`: `Ψ` is continuous (dominated convergence).
* `isCollarTopDensity_collarDensity`: `∫_{[a₁,a₂]} Ψ = E_collar[1_{[a₁,a₂]}(ℋ_X)]₁₁` entrywise
  (Fubini; spectral sums need no simple spectrum).
* `eq_collarDensity_of_isCollarTopDensity`: every continuous top density equals `Ψ`.
* `collarDensity_isHermitian`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Foundations.Spectral
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {W : ℕ}

/-!
## The base law and the shift weight
-/

/-- The base law `μ'` of the common scalar shift (`collarLaw_commonShift`). -/
def collarBase (W : ℕ) (b : ℝ) : Measure (CollarSample W) :=
  if hW : 0 < W then Classical.choose (collarLaw_commonShift hW b) else collarLaw W b

theorem collarBase_spec (hW : 0 < W) (b : ℝ) :
    IsProbabilityMeasure (collarBase W b) ∧
      collarLaw W b = ((collarBase W b).prod (gaussianReal 0 (commonShiftVar W b))).map
        (fun p => shiftSample p.2 p.1) := by
  unfold collarBase
  split_ifs
  exact Classical.choose_spec (collarLaw_commonShift hW b)

instance isProbabilityMeasure_collarBase (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (collarBase W b) := by
  by_cases hW : 0 < W
  · exact (collarBase_spec hW b).1
  · unfold collarBase
    split_ifs
    infer_instance

theorem commonShiftVar_ne_zero (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) : commonShiftVar W b ≠ 0 := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  unfold commonShiftVar blockScalarVar
  refine div_ne_zero (div_ne_zero ?_ (by exact_mod_cast hW.ne')) (by norm_num)
  exact (Real.toNNReal_pos.2 (div_pos (by linarith) hWr)).ne'

/-- The `N(0, s)` density `φ_s`, `s = commonShiftVar W b`. -/
def shiftWeight (W : ℕ) (b : ℝ) (u : ℝ) : ℝ := gaussianPDFReal 0 (commonShiftVar W b) u

theorem shiftWeight_nonneg (W : ℕ) (b u : ℝ) : 0 ≤ shiftWeight W b u :=
  gaussianPDFReal_nonneg _ _ _

theorem shiftWeight_le (W : ℕ) (b u : ℝ) :
    shiftWeight W b u ≤ (Real.sqrt (2 * Real.pi * commonShiftVar W b))⁻¹ := by
  unfold shiftWeight gaussianPDFReal
  have he : Real.exp (-(u - 0) ^ 2 / (2 * commonShiftVar W b)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (mul_one _)

theorem continuous_shiftWeight (W : ℕ) (b : ℝ) : Continuous (shiftWeight W b) := by
  unfold shiftWeight gaussianPDFReal
  fun_prop

theorem measurable_shiftWeight (W : ℕ) (b : ℝ) : Measurable (shiftWeight W b) :=
  (continuous_shiftWeight W b).measurable

/-- The collar matrix is Hermitian, and so are the end and middle blocks, `μ'`-almost surely. -/
theorem ae_collarBase_isHermitian (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    ∀ᵐ ω ∂collarBase W b, (collarMatrix e X ω).IsHermitian ∧
      (∀ k, (ω.1.1 k).IsHermitian) ∧ ω.2.IsHermitian := by
  have h := ae_collarMatrix_isHermitian (W := W) b e hX
  rw [(collarBase_spec hW b).2] at h
  have h2 := Measure.ae_ae_of_ae_prod (ae_of_ae_map measurable_shiftSample.aemeasurable h)
  filter_upwards [h2] with ω hω
  obtain ⟨θ, hθ, hA, hG⟩ := hω.exists
  have hθI : ((θ : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)).IsHermitian :=
    isHermitian_one.smul (Complex.conj_ofReal θ)
  refine ⟨?_, fun k => ?_, ?_⟩
  · have := hθ.sub hθI
    rwa [collarMatrix_shiftSample, add_sub_cancel_right] at this
  · have := (hA k).sub (isHermitian_one.smul (Complex.conj_ofReal θ))
    simpa only [shiftSample, add_sub_cancel_right] using this
  · have := hG.sub (isHermitian_one.smul (Complex.conj_ofReal θ))
    simpa only [shiftSample, add_sub_cancel_right] using this

/-!
## The canonical density
-/

/-- `Ψ_X(x) = E_{μ'}[φ_s(x - ℋ_X)]₁₁`. -/
def collarDensity (W : ℕ) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.of fun i j => ∫ ω, cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)
    (Sum.inl i) (Sum.inl j) ∂collarBase W b

theorem norm_cfc_shiftWeight_apply_le {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (b : ℝ) (x : ℝ) (i j : ι) :
    ‖cfc (fun l => shiftWeight W b (x - l)) M i j‖ ≤
      Fintype.card ι * (Real.sqrt (2 * Real.pi * commonShiftVar W b))⁻¹ := by
  rw [cfc_eq_specSum hM]
  refine norm_specSum_apply_le hM (fun l => ?_) i j
  rw [Complex.norm_real, Real.norm_of_nonneg (shiftWeight_nonneg _ _ _)]
  exact shiftWeight_le _ _ _

theorem aestronglyMeasurable_cfc_collar (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {f : ℝ → ℝ}
    (hf : Measurable f) (i j : LayerSite W .common) :
    AEStronglyMeasurable (fun ω => cfc f (collarMatrix e X ω) i j) (collarBase W b) :=
  aestronglyMeasurable_cfc_apply (measurable_collarMatrix e X)
    ((ae_collarBase_isHermitian hW b e hX).mono fun _ h => h.1) hf i j

theorem integrable_cfc_shiftWeight (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (x : ℝ)
    (i j : LayerSite W .common) :
    Integrable (fun ω => cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω) i j)
      (collarBase W b) := by
  refine (integrable_const (Fintype.card (LayerSite W .common) *
    (Real.sqrt (2 * Real.pi * commonShiftVar W b))⁻¹)).mono'
    (aestronglyMeasurable_cfc_collar hW b e hX
      ((measurable_shiftWeight W b).comp (measurable_const.sub measurable_id)) i j) ?_
  filter_upwards [ae_collarBase_isHermitian hW b e hX] with ω hω
  exact norm_cfc_shiftWeight_apply_le hω.1 b x i j

/-- **Continuity** of the canonical density. -/
theorem continuous_collarDensity_apply (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (i j : Fin 2 × Fin W) :
    Continuous fun x => collarDensity W b e X x i j := by
  simp only [collarDensity, Matrix.of_apply]
  refine continuous_of_dominated (bound := fun _ => (Fintype.card (LayerSite W .common) *
    (Real.sqrt (2 * Real.pi * commonShiftVar W b))⁻¹ : ℝ))
    (fun x => aestronglyMeasurable_cfc_collar hW b e hX
      ((measurable_shiftWeight W b).comp (measurable_const.sub measurable_id)) _ _)
    (fun x => ?_) (integrable_const _) ?_
  · filter_upwards [ae_collarBase_isHermitian hW b e hX] with ω hω
    exact norm_cfc_shiftWeight_apply_le hω.1 b x _ _
  · filter_upwards [ae_collarBase_isHermitian hW b e hX] with ω hω
    simp_rw [cfc_eq_specSum hω.1, specSum_apply]
    refine continuous_finsetSum _ fun r _ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_shiftWeight W b).comp
      (continuous_id.sub continuous_const))).mul continuous_const

theorem continuous_collarDensity (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    Continuous (collarDensity W b e X) :=
  continuous_pi fun i => continuous_pi fun j => continuous_collarDensity_apply hW b e hX i j

/-!
## The defining identity
-/

/-- `∫ 1_B(λ + θ) dN(0,s)(θ) = ∫_B φ_s(x - λ) dx`. -/
theorem integral_indicator_add_gaussian {s : ℝ≥0} (hs : s ≠ 0) {B : Set ℝ} (hB : MeasurableSet B)
    (lam : ℝ) :
    ∫ θ, B.indicator (1 : ℝ → ℝ) (lam + θ) ∂gaussianReal 0 s =
      ∫ x in B, gaussianPDFReal 0 s (x - lam) := by
  have hm : (gaussianReal 0 s).map (fun θ => lam + θ) = gaussianReal (0 + lam) s :=
    gaussianReal_map_const_add lam
  rw [← integral_map (f := B.indicator (1 : ℝ → ℝ)) (measurable_const_add lam).aemeasurable
      ((measurable_one.indicator hB).aestronglyMeasurable), hm, integral_indicator_one hB,
    measureReal_def, gaussianReal_apply_eq_integral _ hs,
    ENNReal.toReal_ofReal (setIntegral_nonneg hB fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  refine setIntegral_congr_fun hB fun x _ => ?_
  rw [gaussianPDFReal_sub]

theorem norm_indicator_one_le (B : Set ℝ) (x : ℝ) : ‖B.indicator (1 : ℝ → ℝ) x‖ ≤ 1 := by
  by_cases hx : x ∈ B
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- Fixed-matrix form of the defining identity: averaging the common shift turns the spectral
projector into the Gaussian-smoothed calculus. -/
theorem integral_cfc_indicator_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) {s : ℝ≥0} (hs : s ≠ 0) {B : Set ℝ} (hB : MeasurableSet B) (i j : ι) :
    ∫ θ, cfc (B.indicator (1 : ℝ → ℝ)) (M + (θ : ℂ) • 1) i j ∂gaussianReal 0 s =
      ∫ x in B, cfc (fun l => gaussianPDFReal 0 s (x - l)) M i j := by
  simp_rw [cfc_add_smul_one hM, cfc_eq_specSum hM, specSum_apply]
  have hint1 : ∀ r : Fin (Fintype.card ι), Integrable (fun θ : ℝ =>
      ((B.indicator (1 : ℝ → ℝ) (increasingEigenvalue hM r + θ) : ℝ) : ℂ) *
        (increasingEigenvector hM r i * star (increasingEigenvector hM r j))) (gaussianReal 0 s) := by
    intro r
    refine Integrable.mul_const ?_ _
    refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun θ => ?_)
    · exact (Complex.continuous_ofReal.measurable.comp ((measurable_one.indicator hB).comp
        (measurable_const_add _))).aestronglyMeasurable
    · rw [Complex.norm_real]; exact norm_indicator_one_le B _
  have hint2 : ∀ r : Fin (Fintype.card ι), Integrable (fun x : ℝ =>
      ((gaussianPDFReal 0 s (x - increasingEigenvalue hM r) : ℝ) : ℂ) *
        (increasingEigenvector hM r i * star (increasingEigenvector hM r j))) (volume.restrict B) := by
    intro r
    refine Integrable.mul_const ?_ _
    refine Integrable.ofReal ?_
    exact ((integrable_gaussianPDFReal 0 s).comp_sub_right _).restrict
  rw [integral_finsetSum _ fun r _ => hint1 r, integral_finsetSum _ fun r _ => hint2 r]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_mul_const, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_indicator_add_gaussian hs hB]

/-- **Defining identity** for bounded intervals: `∫_{[a₁,a₂]} Ψ_ij = E_collar[1_{[a₁,a₂]}(ℋ_X)]_ij`. -/
theorem setIntegral_collarDensity_apply (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (a₁ a₂ : ℝ)
    (i j : Fin 2 × Fin W) :
    ∫ x in Set.Icc a₁ a₂, collarDensity W b e X x i j =
      collarTopProjector W b e X (Set.Icc a₁ a₂) i j := by
  set I := Set.Icc a₁ a₂
  have hI : MeasurableSet I := measurableSet_Icc
  set μ' := collarBase W b
  set N := gaussianReal 0 (commonShiftVar W b)
  have hs := commonShiftVar_ne_zero hW hb
  set Cb : ℝ := Fintype.card (LayerSite W .common) * (Real.sqrt (2 * Real.pi * commonShiftVar W b))⁻¹
  have hHerm := ae_collarBase_isHermitian hW b e hX
  -- joint measurable version of the integrand
  set k : ℝ × CollarSample W → ℂ := fun p => rawCfc (fun l => shiftWeight W b (p.1 - l))
    (collarMatrix e X p.2) (Sum.inl i) (Sum.inl j) with hkdef
  have hk : Measurable k := measurable_rawCfc (measurable_collarMatrix e X)
    (g := fun x l => shiftWeight W b (x - l))
    ((measurable_shiftWeight W b).comp (measurable_fst.sub measurable_snd)) _ _
  have hk_eq : ∀ᵐ p ∂(volume.restrict I).prod μ', k p =
      cfc (fun l => shiftWeight W b (p.1 - l)) (collarMatrix e X p.2) (Sum.inl i) (Sum.inl j) := by
    have := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict I) (ν := μ')).ae hHerm
    filter_upwards [this] with p hp
    exact congrFun (congrFun (rawCfc_eq_cfc hp.1 _) _) _
  have hIfin : (volume.restrict I) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (volume.restrict I) := ⟨hIfin⟩
  have hkint : Integrable k ((volume.restrict I).prod μ') := by
    refine (integrable_const Cb).mono' hk.aestronglyMeasurable ?_
    filter_upwards [hk_eq, (Measure.quasiMeasurePreserving_snd (μ := volume.restrict I)
      (ν := μ')).ae hHerm] with p hp hp2
    rw [hp]
    exact norm_cfc_shiftWeight_apply_le hp2.1 b p.1 _ _
  -- left side: Fubini
  have hL : ∫ x in I, collarDensity W b e X x i j = ∫ ω, (∫ x in I,
      cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω) (Sum.inl i) (Sum.inl j)) ∂μ' := by
    simp only [collarDensity, Matrix.of_apply]
    have h1 : ∀ x, ∫ ω, cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)
        (Sum.inl i) (Sum.inl j) ∂μ' = ∫ ω, k (x, ω) ∂μ' := fun x => by
      refine integral_congr_ae ?_
      filter_upwards [hHerm] with ω hω
      exact (congrFun (congrFun (rawCfc_eq_cfc hω.1 _) _) _).symm
    have h2 : ∀ ω, (collarMatrix e X ω).IsHermitian → ∫ x in I, k (x, ω) =
        ∫ x in I, cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)
          (Sum.inl i) (Sum.inl j) := fun ω hω =>
      integral_congr_ae (Eventually.of_forall fun x =>
        congrFun (congrFun (rawCfc_eq_cfc hω _) _) _)
    refine (setIntegral_congr_fun hI fun x _ => h1 x).trans ?_
    rw [integral_integral_swap (f := fun x ω => k (x, ω)) hkint]
    refine integral_congr_ae ?_
    filter_upwards [hHerm] with ω hω
    exact h2 ω hω.1
  -- right side: the common shift
  set g : CollarSample W → ℂ := fun ω => rawCfc (I.indicator (1 : ℝ → ℝ)) (collarMatrix e X ω)
    (Sum.inl i) (Sum.inl j)
  have hg : Measurable g := measurable_rawCfc_apply (measurable_collarMatrix e X)
    (measurable_one.indicator hI) _ _
  have hR : collarTopProjector W b e X I i j = ∫ ω, g ω ∂collarLaw W b := by
    simp only [collarTopProjector, matrixExpect, Matrix.of_apply, Matrix.toBlocks₁₁]
    refine integral_congr_ae ?_
    filter_upwards [ae_collarMatrix_isHermitian (W := W) b e hX] with ω hω
    exact (congrFun (congrFun (rawCfc_eq_cfc hω.1 _) _) _).symm
  have hlaw := (collarBase_spec hW b).2
  have hgs : ∀ᵐ p ∂μ'.prod N, g (shiftSample p.2 p.1) =
      cfc (I.indicator (1 : ℝ → ℝ)) (collarMatrix e X p.1 + (p.2 : ℂ) • 1) (Sum.inl i) (Sum.inl j) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ') (ν := N)).ae hHerm] with p hp
    have hH : (collarMatrix e X p.1 + (p.2 : ℂ) • (1 : Matrix (LayerSite W .common)
        (LayerSite W .common) ℂ)).IsHermitian := hp.1.add (isHermitian_one.smul (Complex.conj_ofReal _))
    simp only [g]
    rw [collarMatrix_shiftSample]
    exact congrFun (congrFun (rawCfc_eq_cfc hH _) _) _
  have hgint : Integrable (fun p : CollarSample W × ℝ => g (shiftSample p.2 p.1)) (μ'.prod N) := by
    refine (integrable_const (Fintype.card (LayerSite W .common) * (1 : ℝ))).mono'
      (hg.comp measurable_shiftSample).aestronglyMeasurable ?_
    filter_upwards [hgs, (Measure.quasiMeasurePreserving_fst (μ := μ') (ν := N)).ae hHerm] with p hp hp2
    rw [hp]
    have hH : (collarMatrix e X p.1 + (p.2 : ℂ) • (1 : Matrix (LayerSite W .common)
        (LayerSite W .common) ℂ)).IsHermitian := hp2.1.add (isHermitian_one.smul (Complex.conj_ofReal _))
    rw [cfc_eq_specSum hH]
    exact norm_specSum_apply_le hH (fun l => by rw [Complex.norm_real]; exact norm_indicator_one_le I l) _ _
  rw [hL, hR, hlaw, integral_map measurable_shiftSample.aemeasurable hg.aestronglyMeasurable,
    integral_prod _ hgint]
  refine integral_congr_ae ?_
  filter_upwards [hHerm] with ω hω
  have h3 : ∫ θ, g (shiftSample θ ω) ∂N = ∫ θ, cfc (I.indicator (1 : ℝ → ℝ))
      (collarMatrix e X ω + (θ : ℂ) • 1) (Sum.inl i) (Sum.inl j) ∂N := by
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    have hH : (collarMatrix e X ω + (θ : ℂ) • (1 : Matrix (LayerSite W .common)
        (LayerSite W .common) ℂ)).IsHermitian := hω.1.add (isHermitian_one.smul (Complex.conj_ofReal _))
    simp only [g]
    rw [collarMatrix_shiftSample]
    exact congrFun (congrFun (rawCfc_eq_cfc hH _) _) _
  rw [h3, integral_cfc_indicator_shift hω.1 hs hI]
  rfl

/-- The canonical version is an expected top-top density (`IsCollarTopDensity`). -/
theorem isCollarTopDensity_collarDensity (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    IsCollarTopDensity W b e X (collarDensity W b e X) :=
  fun a₁ a₂ _ i j => setIntegral_collarDensity_apply hW hb e hX a₁ a₂ i j

/-- **Uniqueness**: every continuous expected top-top density equals `Ψ`. -/
theorem eq_collarDensity_of_isCollarTopDensity (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : Continuous S)
    (h : IsCollarTopDensity W b e X S) : S = collarDensity W b e X := by
  funext x
  ext i j
  have hSij : Continuous fun x => S x i j := (continuous_apply j).comp ((continuous_apply i).comp hS)
  have hPij := continuous_collarDensity_apply hW b e hX i j
  have hfc : Continuous fun x => S x i j - collarDensity W b e X x i j := hSij.sub hPij
  refine sub_eq_zero.1 (BlockBand.Critical.WeightedDensity.eq_zero_of_setIntegral_Icc_eq_zero
    hfc (fun a₁ a₂ ha => ?_) x)
  rw [integral_sub (f := fun x => S x i j) (g := fun x => collarDensity W b e X x i j)
    hSij.integrableOn_Icc hPij.integrableOn_Icc, h a₁ a₂ ha i j,
    isCollarTopDensity_collarDensity hW hb e hX a₁ a₂ ha i j, sub_self]

/-- `Ψ_X(x)` is Hermitian. -/
theorem collarDensity_isHermitian (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (x : ℝ) :
    (collarDensity W b e X x).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, collarDensity, Matrix.of_apply]
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [ae_collarBase_isHermitian hW b e hX] with ω hω
  have hc : (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)).IsHermitian :=
    (cfc_predicate _ _ : IsSelfAdjoint _)
  exact congrFun (congrFun hc (Sum.inl i)) (Sum.inl j)

end BlockBand.Critical.Collar.Density
