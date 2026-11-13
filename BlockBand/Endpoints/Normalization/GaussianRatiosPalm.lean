module

public import BlockBand.Endpoints.Normalization.GaussianRatiosGaussian
public import BlockBand.Endpoints.Clock.UniformTags
public import BlockBand.Coarea.ClockRank
public import BlockBand.Coarea.FreshPalmDensity

/-!
# The normalized unranked Palm law as a measure, and relative Palm moments

**Measure.** `Â = palmMeasure F c₀ E`, the measure on `ℂ^N` with
`∫ φ dÂ = Z⁻¹ Σ_ℓ E[w_{ℓ,E} φ(u_ℓ)]` (`palmExpect`), `Z = palmMass F c₀ E`, the expectation over
the traceless part `A⁰` of `GUE_N(c₀/N)` (`freshTracelessLaw`). For `Z > 0` it is a probability
measure (`isProbabilityMeasure_palmMeasure`), and `palmExpect φ = ∫ φ dÂ` for every measurable
`φ` bounded on the unit ball (`palmExpect_eq_integral`; the selected eigenvectors have
`‖u_ℓ‖ ≤ 1` for every matrix).

**Relative moments** (`palm_quadForm_moment`), from `CoareaPalm.FreshPalmContract` (the
fresh-Palm theorem) only. Fixed first the constants `A, c₀, r₀, s₀, v₀` (`FreshConstants`) and the
order `r ≥ 1`; then `κ > 0` and `C_r`; then every `K > 0` has `C_{r,K}`; uniformly in `N ≥ 1`,
every `F` in `FreshClass`, every deterministic `Y ⪰ 0` (no norm or condition restriction) and every
`M` with `MM* = Γ`, if `Z > 0`:
`|Â[(N v*Yv)^r] - E_g(g*M*YMg)^r| ≤ C_r (N^{-κ} + N C_{r,K} N^{-K}/Z) E_g(g*M*YMg)^r / r!`.
Proof: `(N v*Yv)^r = (r!)⁻¹ E_h (N|(Lh)*v|²)^r` with `LL* = Y` (`integral_normSq_dotProduct_pow`);
Fubini in `(h, A⁰)`; the fresh-Palm theorem at `q = Lh` for each rank; summing the ranks;
`E_h(quadForm Γ (Lh))^r = E_g(quadForm Y (Mg))^r` (`integral_quadForm_pow_swap`).

`palm_quadForm_moment_uniform`: adding the lower bound `Z ≥ cN` (the hypothesis
`hZ : NormalizerLowerBound`, the statement of the deterministic-normalizer corollary) gives, for
every `r` and `η > 0`, `N₀` with `|Â[(N v*Yv)^r] - E_g(g*M*YMg)^r| ≤ η (Tr ΓY)^r` for `N ≥ N₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Model.Construction BlockBand.Foundations.Spectral BlockBand.Coarea.ClockRank
open scoped ENNReal NNReal ComplexOrder Matrix ComplexConjugate

variable {N : ℕ}

/-!
## The selected eigenvectors
-/

/-- The selected eigenvectors have total squared norm at most one (a local copy of
`sum_norm_sq_freshEigenvector_le`). -/
theorem sum_norm_sq_freshEigenvector_le' (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    ∑ x, ‖freshEigenvector K ℓ x‖ ^ 2 ≤ 1 := by
  unfold freshEigenvector rawOrderedColumnSelection rawHermitianExtension
  split_ifs with hK
  · by_cases hs : RankSimple (⟨K, hK⟩ : HermitianMatrix (Fin N)) (Fin.cast (Fintype.card_fin N).symm ℓ)
    · obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase_of_rankSimple _ _ hs
      beta_reduce
      rw [hsel]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hz, one_mul]
      rw [sum_norm_sq_increasingEigenvector]
    · beta_reduce
      rw [orderedColumnSelection_eq_zero_of_not_rankSimple _ _ hs]
      simp
  · simp

theorem sqNorm_freshEigenvector_le (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    sqNorm (freshEigenvector K ℓ) ≤ 1 := by
  have h := sum_norm_sq_freshEigenvector_le' K ℓ
  unfold sqNorm
  simpa [Complex.normSq_eq_norm_sq] using h

theorem measurable_freshEigenvector_add (F : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => freshEigenvector (F + A0) ℓ := by
  have hadd : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => F + A0 := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.add_apply]
    exact measurable_const.add ((measurable_pi_apply j).comp (measurable_pi_apply i))
  refine measurable_pi_iff.mpr fun x => ?_
  exact (measurable_rawOrderedColumnSelection _ x).comp hadd

theorem palmWeight_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmWeight F c₀ E ℓ A0 :=
  BlockBand.Palm.scalarWeight_nonneg _ _ _ _

/-- The prefactor bound of the scalar Palm weight. -/
def weightBound (c₀ : ℝ) (N : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹

theorem palmWeight_le (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : palmWeight F c₀ E ℓ A0 ≤ weightBound c₀ N :=
  BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _

theorem gr_palmMass_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) : 0 ≤ palmMass F c₀ E :=
  Finset.sum_nonneg fun ℓ _ => integral_nonneg fun A0 => palmWeight_nonneg F c₀ E ℓ A0

/-- A bounded measurable observable of the selected eigenvector, weighted, is integrable. -/
theorem gr_integrable_palmWeight_mul (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ v, sqNorm v ≤ 1 → |φ v| ≤ B) :
    Integrable (fun A0 => palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ))
      (freshTracelessLaw N c₀) := by
  refine Integrable.mono' (integrable_const (weightBound c₀ N * B)) ?_
    (Filter.Eventually.of_forall fun A0 => ?_)
  · exact ((BlockBand.Coarea.FreshPalm.measurable_palmWeight F c₀ E ℓ).mul
      (hφ.comp (measurable_freshEigenvector_add F ℓ))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (palmWeight_nonneg F c₀ E ℓ A0)]
    exact mul_le_mul (palmWeight_le F c₀ E ℓ A0) (hB _ (sqNorm_freshEigenvector_le _ ℓ))
      (abs_nonneg _) ((palmWeight_nonneg F c₀ E ℓ A0).trans (palmWeight_le F c₀ E ℓ A0))

/-!
## The Palm measure
-/

/-- The weighted rank-`ℓ` eigenvector law `E[w_ℓ 1{u_ℓ ∈ ·}]`. -/
def rankPalmMeasure (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Measure (Fin N → ℂ) :=
  ((freshTracelessLaw N c₀).withDensity fun A0 =>
      ((Real.toNNReal (palmWeight F c₀ E ℓ A0) : ℝ≥0) : ℝ≥0∞)).map
    fun A0 => freshEigenvector (F + A0) ℓ

/-- The normalized unranked Palm law `Â = Z⁻¹ Σ_ℓ E[w_ℓ δ_{u_ℓ}]`. -/
def palmMeasure (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) : Measure (Fin N → ℂ) :=
  ENNReal.ofReal (palmMass F c₀ E)⁻¹ • ∑ ℓ : Fin N, rankPalmMeasure F c₀ E ℓ

theorem measurable_toNNReal_palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Measurable fun A0 => Real.toNNReal (palmWeight F c₀ E ℓ A0) :=
  measurable_real_toNNReal.comp (BlockBand.Coarea.FreshPalm.measurable_palmWeight F c₀ E ℓ)

theorem integral_rankPalmMeasure (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Measurable φ) :
    ∫ v, φ v ∂rankPalmMeasure F c₀ E ℓ =
      ∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c₀ := by
  unfold rankPalmMeasure
  rw [integral_map (measurable_freshEigenvector_add F ℓ).aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_toNNReal_palmWeight F c₀ E ℓ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A0 => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (palmWeight_nonneg F c₀ E ℓ A0)]

theorem integrable_rankPalmMeasure (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ v, sqNorm v ≤ 1 → |φ v| ≤ B) :
    Integrable φ (rankPalmMeasure F c₀ E ℓ) := by
  unfold rankPalmMeasure
  rw [integrable_map_measure hφ.aestronglyMeasurable
      (measurable_freshEigenvector_add F ℓ).aemeasurable,
    integrable_withDensity_iff_integrable_smul (measurable_toNNReal_palmWeight F c₀ E ℓ)]
  refine (gr_integrable_palmWeight_mul F c₀ E ℓ hφ hB).congr
    (Filter.Eventually.of_forall fun A0 => ?_)
  simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (palmWeight_nonneg F c₀ E ℓ A0)]

/-- `palmExpect φ = ∫ φ dÂ` for measurable `φ` bounded on the unit ball. -/
theorem palmExpect_eq_integral (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ v, sqNorm v ≤ 1 → |φ v| ≤ B) :
    palmExpect F c₀ E φ = ∫ v, φ v ∂palmMeasure F c₀ E := by
  unfold palmMeasure palmExpect
  rw [integral_smul_measure, integral_finsetSum_measure fun ℓ _ =>
    integrable_rankPalmMeasure F c₀ E ℓ hφ hB]
  simp_rw [integral_rankPalmMeasure F c₀ E _ hφ]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (gr_palmMass_nonneg F c₀ E)), smul_eq_mul,
    div_eq_inv_mul]

theorem integrable_palmMeasure (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    {φ : (Fin N → ℂ) → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ v, sqNorm v ≤ 1 → |φ v| ≤ B) :
    Integrable φ (palmMeasure F c₀ E) := by
  unfold palmMeasure
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  exact integrable_finsetSum_measure.mpr fun ℓ _ => integrable_rankPalmMeasure F c₀ E ℓ hφ hB

theorem rankPalmMeasure_univ (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    rankPalmMeasure F c₀ E ℓ Set.univ =
      ENNReal.ofReal (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) := by
  unfold rankPalmMeasure
  rw [Measure.map_apply (measurable_freshEigenvector_add F ℓ) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal (BlockBand.Endpoints.Clock.integrable_palmWeight F c₀ E ℓ)
      (Filter.Eventually.of_forall fun A0 => palmWeight_nonneg F c₀ E ℓ A0)]
  rfl

theorem isProbabilityMeasure_palmMeasure (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    (hZ : 0 < palmMass F c₀ E) : IsProbabilityMeasure (palmMeasure F c₀ E) := by
  constructor
  unfold palmMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  simp_rw [rankPalmMeasure_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ℓ _ => integral_nonneg fun A0 =>
      palmWeight_nonneg F c₀ E ℓ A0, ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le)]
  have : (palmMass F c₀ E)⁻¹ * ∑ ℓ : Fin N, ∫ A0, palmWeight F c₀ E ℓ A0
      ∂freshTracelessLaw N c₀ = 1 := inv_mul_cancel₀ hZ.ne'
  rw [this, ENNReal.ofReal_one]

/-!
## Relative Palm moments
-/

/-- `normSq (q*u) = normSq ((Lᴴu)* h)` for `q = Lh`. -/
theorem normSq_mulVec_dotProduct (L : Matrix (Fin N) (Fin N) ℂ) (h u : Fin N → ℂ) :
    Complex.normSq (star (L *ᵥ h) ⬝ᵥ u) = Complex.normSq (star (Lᴴ *ᵥ u) ⬝ᵥ h) := by
  rw [normSq_dotProduct_comm]
  congr 1
  rw [dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

theorem palmOverlap_eq (F : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) :
    palmOverlap F q ℓ A0 = N * Complex.normSq (star q ⬝ᵥ freshEigenvector (F + A0) ℓ) := by
  unfold palmOverlap; rw [Complex.normSq_eq_norm_sq]

/-- Averaging the overlap over `q = Lh`: `E_h (palmOverlap (Lh))^r = r!(N quadForm (LL*) u)^r`. -/
theorem integral_palmOverlap_pow (F : Matrix (Fin N) (Fin N) ℂ) (L : Matrix (Fin N) (Fin N) ℂ)
    (ℓ : Fin N) (A0 : Matrix (Fin N) (Fin N) ℂ) (r : ℕ) :
    ∫ h, palmOverlap F (L *ᵥ h) ℓ A0 ^ r ∂circularVectorLaw (Fin N) =
      r.factorial * ((N : ℝ) * quadForm (L * Lᴴ) (freshEigenvector (F + A0) ℓ)) ^ r := by
  simp_rw [palmOverlap_eq, normSq_mulVec_dotProduct L _ (freshEigenvector (F + A0) ℓ), mul_pow]
  rw [integral_const_mul, integral_normSq_dotProduct_pow]
  have := quadForm_conjTranspose_mul_self Lᴴ (freshEigenvector (F + A0) ℓ)
  rw [conjTranspose_conjTranspose] at this
  rw [this]; ring

theorem palmOverlap_le (F : Matrix (Fin N) (Fin N) ℂ) (L : Matrix (Fin N) (Fin N) ℂ)
    (ℓ : Fin N) (A0 : Matrix (Fin N) (Fin N) ℂ) (h : Fin N → ℂ) :
    palmOverlap F (L *ᵥ h) ℓ A0 ≤ N * quadForm (Lᴴ * L) h := by
  rw [palmOverlap_eq, quadForm_conjTranspose_mul_self]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  refine (normSq_dotProduct_le _ _).trans ?_
  calc sqNorm (L *ᵥ h) * sqNorm (freshEigenvector (F + A0) ℓ) ≤ sqNorm (L *ᵥ h) * 1 :=
        mul_le_mul_of_nonneg_left (sqNorm_freshEigenvector_le _ ℓ) (sqNorm_nonneg _)
    _ = _ := mul_one _

theorem palmOverlap_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmOverlap F q ℓ A0 := by
  unfold palmOverlap; positivity

theorem measurable_palmOverlap_uncurry (F : Matrix (Fin N) (Fin N) ℂ)
    (L : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable fun z : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      palmOverlap F (L *ᵥ z.2) ℓ z.1 := by
  simp_rw [palmOverlap_eq]
  refine measurable_const.mul (Complex.continuous_normSq.measurable.comp ?_)
  simp only [dotProduct]
  refine Finset.measurable_sum _ fun x _ => ?_
  refine Measurable.mul ?_ ?_
  · exact (continuous_star.measurable.comp
      ((measurable_pi_apply x).comp ((measurable_mulVec L).comp measurable_snd)))
  · exact (measurable_pi_apply x).comp ((measurable_freshEigenvector_add F ℓ).comp measurable_fst)

/-- The rank-`ℓ` integrand `w_ℓ(A⁰) (palmOverlap (Lh))^r` is integrable on `law ⊗ CN(0,I)`. -/
theorem integrable_weight_overlap_prod (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    (L : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) (r : ℕ) :
    Integrable (fun z : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
        palmWeight F c₀ E ℓ z.1 * palmOverlap F (L *ᵥ z.2) ℓ z.1 ^ r)
      ((freshTracelessLaw N c₀).prod (circularVectorLaw (Fin N))) := by
  have hb : Integrable (fun z : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      weightBound c₀ N * (((N : ℝ) * quadForm (Lᴴ * L) z.2) ^ r))
      ((freshTracelessLaw N c₀).prod (circularVectorLaw (Fin N))) := by
    have hg : Integrable (fun h : Fin N → ℂ => ((N : ℝ) * quadForm (Lᴴ * L) h) ^ r)
        (circularVectorLaw (Fin N)) := by
      simp_rw [mul_pow]
      exact (integrable_quadForm_pow (posSemidef_conjTranspose_mul_self L) r).const_mul _
    exact (integrable_const (weightBound c₀ N)).mul_prod hg
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (((BlockBand.Coarea.FreshPalm.measurable_palmWeight F c₀ E ℓ).comp measurable_fst).mul
      ((measurable_palmOverlap_uncurry F L ℓ).pow_const r)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (palmWeight_nonneg F c₀ E ℓ z.1),
      abs_of_nonneg (pow_nonneg (palmOverlap_nonneg _ _ _ _) _)]
    exact mul_le_mul (palmWeight_le F c₀ E ℓ z.1)
      (pow_le_pow_left₀ (palmOverlap_nonneg _ _ _ _) (palmOverlap_le F L ℓ z.1 z.2) r)
      (pow_nonneg (palmOverlap_nonneg _ _ _ _) _)
      ((palmWeight_nonneg F c₀ E ℓ z.1).trans (palmWeight_le F c₀ E ℓ z.1))

/-- Fubini: `E[w_ℓ (N quadForm (LL*) u_ℓ)^r] = (r!)⁻¹ E_h E[w_ℓ (palmOverlap (Lh))^r]`. -/
theorem rank_moment_eq_average (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    (L : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) (r : ℕ) :
    (r.factorial : ℝ) * ∫ A0, palmWeight F c₀ E ℓ A0 *
        ((N : ℝ) * quadForm (L * Lᴴ) (freshEigenvector (F + A0) ℓ)) ^ r ∂freshTracelessLaw N c₀ =
      ∫ h, (∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F (L *ᵥ h) ℓ A0 ^ r
        ∂freshTracelessLaw N c₀) ∂circularVectorLaw (Fin N) := by
  have hint := integrable_weight_overlap_prod F c₀ E L ℓ r
  have hswap := integral_integral_swap (f := fun A0 h =>
    palmWeight F c₀ E ℓ A0 * palmOverlap F (L *ᵥ h) ℓ A0 ^ r) hint
  rw [← hswap, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A0 => ?_)
  simp only
  rw [integral_const_mul, integral_palmOverlap_pow]
  ring

/-- `E_h (quadForm Γ (Lh))^r = E_g (quadForm (LL*) (Mg))^r` when `MM* = Γ`. -/
theorem gamma_average_eq (L M Γ : Matrix (Fin N) (Fin N) ℂ) (hM : M * Mᴴ = Γ) (r : ℕ) :
    ∫ h, quadForm Γ (L *ᵥ h) ^ r ∂circularVectorLaw (Fin N) =
      ∫ g, quadForm (L * Lᴴ) (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N) := by
  rw [← hM]; exact integral_quadForm_pow_swap L M r

theorem exists_sqrt_factor {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef) :
    ∃ L : Matrix (Fin N) (Fin N) ℂ, L * Lᴴ = Y := by
  open scoped MatrixOrder in
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hY.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hY.nonneg)
  have hXs : Xᴴ = X := hX
  exact ⟨X, by rw [hXs]; exact hXX⟩

/-- **Relative Palm moments** (first display of the proof of the Gaussian-ratios theorem),
from `FreshPalmContract` only. -/
theorem palm_quadForm_moment (hP : FreshPalmContract) {A c₀ r₀ s₀ v₀ : ℝ}
    (hc : FreshConstants c₀ r₀ s₀ v₀) (r : ℕ) (hr : 1 ≤ r) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ Cr : ℝ, ∀ K : ℝ, 0 < K → ∃ CrK : ℝ,
      ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ Y : Matrix (Fin N) (Fin N) ℂ, Y.PosSemidef →
      ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
      0 < palmMass F c₀ E →
        |palmExpect F c₀ E (fun v => ((N : ℝ) * quadForm Y v) ^ r) -
            ∫ g, quadForm Y (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N)| ≤
          Cr * ((N : ℝ) ^ (-κ) + N * CrK * (N : ℝ) ^ (-K) / palmMass F c₀ E) *
            (∫ g, quadForm Y (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N)) / r.factorial := by
  obtain ⟨κ, hκ, Cr, hK⟩ := hP A c₀ r₀ s₀ v₀ hc r hr
  refine ⟨κ, hκ, Cr, fun K hK0 => ?_⟩
  obtain ⟨CrK, hCrK⟩ := hK K hK0
  refine ⟨CrK, fun N hN F E hF Y hY M hM hZ => ?_⟩
  obtain ⟨L, hL⟩ := exists_sqrt_factor hY
  subst hL
  set μ := freshTracelessLaw N c₀
  set ν := circularVectorLaw (Fin N)
  set Γ := freshGamma F c₀ E with hΓ
  set Z := palmMass F c₀ E with hZdef
  set G := ∫ g, quadForm (L * Lᴴ) (M *ᵥ g) ^ r ∂ν with hGdef
  set Zℓ : Fin N → ℝ := fun ℓ => ∫ A0, palmWeight F c₀ E ℓ A0 ∂μ
  set I : Fin N → (Fin N → ℂ) → ℝ := fun ℓ h =>
    ∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F (L *ᵥ h) ℓ A0 ^ r ∂μ with hIdef
  set γ : (Fin N → ℂ) → ℝ := fun h => quadForm Γ (L *ᵥ h) with hγ
  have hΓpsd : Γ.PosSemidef := BlockBand.Endpoints.Clock.freshGamma_posSemidef F hc.1.le E
  have hγ0 : ∀ h, 0 ≤ γ h := fun h => quadForm_nonneg_of_posSemidef hΓpsd _
  -- the contract at `q = Lh`, rank by rank
  have hrank : ∀ ℓ h, |I ℓ h - (r.factorial : ℝ) * γ h ^ r * Zℓ ℓ| ≤
      Cr * ((N : ℝ) ^ (-κ) * Zℓ ℓ + CrK * (N : ℝ) ^ (-K)) * γ h ^ r := fun ℓ h =>
    hCrK N hN F E hF (L *ᵥ h) ℓ
  -- integrability in `h`
  have hIint : ∀ ℓ, Integrable (I ℓ) ν := fun ℓ =>
    (integrable_weight_overlap_prod F c₀ E L ℓ r).integral_prod_right
  have hγint : Integrable (fun h => γ h ^ r) ν := by
    simp only [hγ]
    simp_rw [← quadForm_conjTranspose_mul_mul]
    exact integrable_quadForm_pow (hΓpsd.conjTranspose_mul_mul_same L) r
  -- the Palm numerator through Fubini
  have hnum : (r.factorial : ℝ) * (∑ ℓ : Fin N, ∫ A0, palmWeight F c₀ E ℓ A0 *
      ((N : ℝ) * quadForm (L * Lᴴ) (freshEigenvector (F + A0) ℓ)) ^ r ∂μ) =
      ∫ h, ∑ ℓ, I ℓ h ∂ν := by
    rw [Finset.mul_sum, integral_finsetSum _ fun ℓ _ => hIint ℓ]
    exact Finset.sum_congr rfl fun ℓ _ => rank_moment_eq_average F c₀ E L ℓ r
  have hmain : ∫ h, γ h ^ r ∂ν = G := gamma_average_eq L M Γ hM r
  have hsumZ : ∑ ℓ, Zℓ ℓ = Z := rfl
  -- pointwise bound after summing the ranks
  have hpt : ∀ h, |∑ ℓ, I ℓ h - (r.factorial : ℝ) * Z * γ h ^ r| ≤
      Cr * ((N : ℝ) ^ (-κ) * Z + N * CrK * (N : ℝ) ^ (-K)) * γ h ^ r := by
    intro h
    have e1 : ∑ ℓ, I ℓ h - (r.factorial : ℝ) * Z * γ h ^ r =
        ∑ ℓ, (I ℓ h - (r.factorial : ℝ) * γ h ^ r * Zℓ ℓ) := by
      rw [Finset.sum_sub_distrib, ← hsumZ, Finset.mul_sum, Finset.sum_mul]
      congr 1; exact Finset.sum_congr rfl fun ℓ _ => by ring
    have e2 : Cr * ((N : ℝ) ^ (-κ) * Z + N * CrK * (N : ℝ) ^ (-K)) * γ h ^ r =
        ∑ ℓ : Fin N, Cr * ((N : ℝ) ^ (-κ) * Zℓ ℓ + CrK * (N : ℝ) ^ (-K)) * γ h ^ r := by
      rw [← hsumZ, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [e1, e2]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ => hrank ℓ h)
  -- integrate the pointwise bound
  have hSint : Integrable (fun h => ∑ ℓ, I ℓ h) ν := integrable_finsetSum _ fun ℓ _ => hIint ℓ
  have hint_bound : |∫ h, ∑ ℓ, I ℓ h ∂ν - (r.factorial : ℝ) * Z * G| ≤
      Cr * ((N : ℝ) ^ (-κ) * Z + N * CrK * (N : ℝ) ^ (-K)) * G := by
    rw [← hmain, ← integral_const_mul, ← integral_sub hSint (hγint.const_mul _),
      ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono (hSint.sub (hγint.const_mul _)).abs (hγint.const_mul _) hpt
  -- the Palm expectation
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hpe : palmExpect F c₀ E (fun v => ((N : ℝ) * quadForm (L * Lᴴ) v) ^ r) =
      (∫ h, ∑ ℓ, I ℓ h ∂ν) / (r.factorial * Z) := by
    unfold palmExpect
    rw [← hnum, mul_comm (r.factorial : ℝ) Z, ← div_div, mul_div_assoc, mul_div_cancel_left₀ _
      hfac.ne']
  rw [hpe]
  have hden : 0 < (r.factorial : ℝ) * Z := mul_pos hfac hZ
  have : (∫ h, ∑ ℓ, I ℓ h ∂ν) / (r.factorial * Z) - G =
      ((∫ h, ∑ ℓ, I ℓ h ∂ν) - (r.factorial : ℝ) * Z * G) / (r.factorial * Z) := by
    field_simp
  rw [this, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |∫ h, ∑ ℓ, I ℓ h ∂ν - (r.factorial : ℝ) * Z * G| ≤
        Cr * ((N : ℝ) ^ (-κ) * Z + N * CrK * (N : ℝ) ^ (-K)) * G := hint_bound
    _ = Cr * ((N : ℝ) ^ (-κ) + N * CrK * (N : ℝ) ^ (-K) / Z) * G / r.factorial *
          (r.factorial * Z) := by
        field_simp

/-- `Re Tr(M*YM) = Tr(ΓY)` when `MM* = Γ`. -/
theorem trace_conj_eq_traceAgainst (Y M Γ : Matrix (Fin N) (Fin N) ℂ) (hM : M * Mᴴ = Γ) :
    (Mᴴ * Y * M).trace.re = traceAgainst Γ Y := by
  unfold traceAgainst
  rw [Matrix.trace_mul_cycle, ← hM, Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- `E_g (g*M*YMg)^r ≤ r! Tr(ΓY)^r`. -/
theorem integral_quadForm_mulVec_pow_le {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef)
    (M Γ : Matrix (Fin N) (Fin N) ℂ) (hM : M * Mᴴ = Γ) (r : ℕ) :
    ∫ g, quadForm Y (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N) ≤
      r.factorial * traceAgainst Γ Y ^ r := by
  simp_rw [← quadForm_conjTranspose_mul_mul]
  rw [← trace_conj_eq_traceAgainst Y M Γ hM]
  exact integral_quadForm_pow_le (hY.conjTranspose_mul_mul_same M) r

theorem integrable_quadForm_mulVec_pow {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef)
    (M : Matrix (Fin N) (Fin N) ℂ) (r : ℕ) :
    Integrable (fun g => quadForm Y (M *ᵥ g) ^ r) (circularVectorLaw (Fin N)) := by
  simp_rw [← quadForm_conjTranspose_mul_mul]
  exact integrable_quadForm_pow (hY.conjTranspose_mul_mul_same M) r

theorem palmExpect_one (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (hZ : 0 < palmMass F c₀ E) :
    palmExpect F c₀ E (fun _ => (1 : ℝ)) = 1 := by
  unfold palmExpect palmMass
  simp only [mul_one]
  exact div_self hZ.ne'

/-- **The deterministic-normalizer lower bound**: `Z ≥ cN` for all sufficiently large `N` in the
fresh class (the statement of the deterministic-normalizer corollary). -/
def NormalizerLowerBound : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ → c * N ≤ palmMass F c₀ E

/-- **Uniform relative moments**: `|Â(Nv*Yv)^r - E_g(g*M*YMg)^r| ≤ η Tr(ΓY)^r` for `N ≥ N₀`,
uniformly in the class, `Y ⪰ 0` and `M` (dividing by `Z ≥ cN`), from
`FreshPalmContract` and the normalizer lower bound `hZ`. -/
theorem palm_quadForm_moment_uniform (hP : FreshPalmContract) (hZ : NormalizerLowerBound)
    {A c₀ r₀ s₀ v₀ : ℝ} (hc : FreshConstants c₀ r₀ s₀ v₀) (r : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ Y : Matrix (Fin N) (Fin N) ℂ, Y.PosSemidef →
      ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
        0 < palmMass F c₀ E ∧
        |palmExpect F c₀ E (fun v => ((N : ℝ) * quadForm Y v) ^ r) -
            ∫ g, quadForm Y (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N)| ≤
          η * traceAgainst (freshGamma F c₀ E) Y ^ r := by
  obtain ⟨c, hc0, NZ, hNZ⟩ := hZ A c₀ r₀ s₀ v₀ hc
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    refine ⟨max NZ 1, fun N hN F E hF Y hY M hM => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hZpos : 0 < palmMass F c₀ E :=
      lt_of_lt_of_le (mul_pos hc0 (by exact_mod_cast hN1)) (hNZ N (le_of_max_le_left hN) F E hF)
    refine ⟨hZpos, ?_⟩
    simp only [pow_zero]
    rw [palmExpect_one F c₀ E hZpos, integral_const, smul_eq_mul, mul_one, probReal_univ,
      sub_self, abs_zero, mul_one]
    exact hη.le
  obtain ⟨κ, hκ, Cr, hK⟩ := palm_quadForm_moment hP (A := A) hc r hrpos
  obtain ⟨CrK, hCrK⟩ := hK 1 one_pos
  -- `|Cr| (N^{-κ} + |CrK|/(cN)) ≤ η` for large `N`
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      |Cr| * ((N : ℝ) ^ (-κ) + |CrK| / (c * N)) ≤ η := by
    have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-κ)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun N : ℕ => |CrK| / (c * N)) Filter.atTop (nhds 0) := by
      have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (|CrK| / c)
      rw [mul_zero] at h
      refine h.congr fun N => ?_
      simp only [div_eq_mul_inv, mul_inv]; ring
    have h3 : Filter.Tendsto (fun N : ℕ => |Cr| * ((N : ℝ) ^ (-κ) + |CrK| / (c * N)))
        Filter.atTop (nhds 0) := by
      simpa using (h1.add h2).const_mul (|Cr|)
    exact (h3.eventually (gt_mem_nhds hη)).mono fun N hN => hN.le
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max NZ N₁) 1, fun N hN F E hF Y hY M hM => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNZ' : NZ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN₁' : N₁ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hZlow := hNZ N hNZ' F E hF
  have hZpos : 0 < palmMass F c₀ E := lt_of_lt_of_le (mul_pos hc0 hNpos) hZlow
  refine ⟨hZpos, ?_⟩
  set G := ∫ g, quadForm Y (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N)
  set T := traceAgainst (freshGamma F c₀ E) Y
  have hG0 : 0 ≤ G := integral_nonneg fun g =>
    pow_nonneg (quadForm_nonneg_of_posSemidef hY _) _
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hGle : G / r.factorial ≤ T ^ r := by
    rw [div_le_iff₀ hfac, mul_comm]
    exact integral_quadForm_mulVec_pow_le hY M _ hM r
  have hb := hCrK N (by omega) F E hF Y hY M hM hZpos
  set Z := palmMass F c₀ E
  have hNK : (N : ℝ) * CrK * (N : ℝ) ^ (-(1 : ℝ)) = CrK := by
    rw [Real.rpow_neg_one]; field_simp
  rw [hNK] at hb
  have hX : 0 ≤ (N : ℝ) ^ (-κ) := Real.rpow_nonneg hNpos.le _
  have hle1 : Cr * ((N : ℝ) ^ (-κ) + CrK / Z) * G / r.factorial ≤
      |Cr| * ((N : ℝ) ^ (-κ) + |CrK| / (c * N)) * (G / r.factorial) := by
    rw [mul_div_assoc]
    have hGf : 0 ≤ G / r.factorial := div_nonneg hG0 hfac.le
    refine mul_le_mul_of_nonneg_right ?_ hGf
    calc Cr * ((N : ℝ) ^ (-κ) + CrK / Z) ≤ |Cr * ((N : ℝ) ^ (-κ) + CrK / Z)| := le_abs_self _
      _ = |Cr| * |(N : ℝ) ^ (-κ) + CrK / Z| := abs_mul _ _
      _ ≤ |Cr| * ((N : ℝ) ^ (-κ) + |CrK| / (c * N)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg hX, abs_div, abs_of_pos hZpos]
          gcongr
  have hT0 : 0 ≤ T := BlockBand.Endpoints.Clock.traceAgainst_nonneg
    (BlockBand.Endpoints.Clock.freshGamma_posSemidef F hc.1.le E) hY
  calc _ ≤ Cr * ((N : ℝ) ^ (-κ) + CrK / Z) * G / r.factorial := hb
    _ ≤ |Cr| * ((N : ℝ) ^ (-κ) + |CrK| / (c * N)) * (G / r.factorial) := hle1
    _ ≤ η * T ^ r := mul_le_mul (hN₁ N hN₁') hGle (div_nonneg hG0 hfac.le) hη.le

end BlockBand.Endpoints.Normalization
