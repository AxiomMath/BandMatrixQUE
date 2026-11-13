module

public import BlockBand.Model.Construction.GaussianCompatibility
public import BlockBand.Endpoints.Sine.CrossingSine

/-!
# The exact Gaussian likelihood of the scalar pair shift

The likelihood is written on the independent real Gaussian coordinates
`z ∈ ℝ^{GaussianCoordinate}` (law `gaussianCoordinatesLaw`, `H = gaussianReconstruction z`):
`R_a(z) = ∏_k exp((m_k z_k - m_k²/2)/v_k)` (`fa_density`), `m = fa_shiftVec a` (`a` on the
diagonal labels of `S`, `0` elsewhere), `v_k` the coordinate variances (`c/W` on the diagonal).
* `fa_lintegral_shift` (`E_a[G] = E[R_a G]`): for every measurable `G ≥ 0`,
  `∫ G(H + a P_S) dP = ∫ R_a(z) G(H(z)) dz`;
* `fa_density_sq` (`R_a² = K_a R_{2a}`), with `K_a = exp(2W · a²/(c/W))` (`fa_densitySqConst_eq`);
  for `a = t/(𝒩ρ)`, `𝒩 = 2W`, this is the pair-shift likelihood constant `exp(t²/(2cρ²))`;
* `fa_lintegral_density_sq`: `∫ R_a(z)² G(H(z)) dz = K_a ∫ G(H + 2a P_S) dP`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

/-!
## One real coordinate
-/

/-- The one-coordinate likelihood ratio `dN(μ,v)/dN(0,v)(y) = exp((μy - μ²/2)/v)`. -/
def fa_ratio (μ : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((μ * y - μ ^ 2 / 2) / v))

theorem fa_measurable_ratio (μ : ℝ) (v : ℝ≥0) : Measurable (fa_ratio μ v) := by
  unfold fa_ratio
  fun_prop

theorem fa_withDensity_ratio (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).withDensity (fa_ratio μ v) = gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero μ hv,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (fa_measurable_ratio μ v)]
  congr 1
  funext y
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.mp h.symm))
  simp only [Pi.mul_apply, gaussianPDF, fa_ratio]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v y)]
  congr 1
  simp only [gaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem fa_ratio_zero (v : ℝ≥0) : fa_ratio 0 v = 1 := by
  funext y
  simp [fa_ratio]

theorem fa_ratio_sq (μ : ℝ) (v : ℝ≥0) (y : ℝ) :
    fa_ratio μ v y ^ 2 =
      ENNReal.ofReal (Real.exp (μ ^ 2 / v)) * fa_ratio (2 * μ) v y := by
  unfold fa_ratio
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_nat_mul]
  congr 2
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-!
## The physical coordinates
-/

section Physical

variable (p : Parameters) (i : ZMod p.n)

/-- The coordinate shift `m = a·1_{diagonal labels of S}`: `H(z + m) = H(z) + a P_S`. -/
def fa_shiftVec (a : ℝ) : p.GaussianCoordinate → ℝ
  | .inl x => if x.1 = i ∨ x.1 = i + 1 then a else 0
  | .inr _ => 0

theorem fa_shiftVec_two_mul (a : ℝ) (k : p.GaussianCoordinate) :
    fa_shiftVec p i (2 * a) k = 2 * fa_shiftVec p i a k := by
  cases k with
  | inl x => simp only [fa_shiftVec]; split_ifs <;> simp
  | inr _ => simp [fa_shiftVec]

/-- `H(z + m) = H(z) + a P_S`: the shift moves only the real diagonal entries of `S`. -/
theorem fa_reconstruction_add_shiftVec (a : ℝ) (z : p.GaussianCoordinate → ℝ) :
    p.gaussianReconstruction (z + fa_shiftVec p i a) =
      p.gaussianReconstruction z + (a : ℂ) • pairProjector p i := by
  ext x y
  simp only [Parameters.gaussianReconstruction, pairProjector, Matrix.add_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, Pi.add_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true, fa_shiftVec]
    split_ifs <;> push_cast <;> ring
  · simp only [hxy, ite_false, mul_zero, add_zero]
    split_ifs <;> simp [fa_shiftVec]

/-- The coordinate variance of a diagonal label is `c/W > 0`. -/
theorem fa_variance_inl_ne_zero (x : p.Site) :
    p.gaussianCoordinateVariance (.inl x) ≠ 0 := by
  intro h
  have h1 := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
  simp only [Parameters.gaussianCoordinateVariance, NNReal.coe_zero,
    Parameters.entryVariance, ite_true] at h1
  exact (div_pos p.c_pos (Nat.cast_pos.mpr p.W_pos)).ne' h1

theorem fa_variance_inl (x : p.Site) :
    ((p.gaussianCoordinateVariance (.inl x) : ℝ≥0) : ℝ) = p.c / p.W := by
  show p.entryVariance x x = p.c / p.W
  simp [Parameters.entryVariance]

theorem fa_withDensity_coord (a : ℝ) (k : p.GaussianCoordinate) :
    (gaussianReal 0 (p.gaussianCoordinateVariance k)).withDensity
        (fa_ratio (fa_shiftVec p i a k) (p.gaussianCoordinateVariance k)) =
      gaussianReal (fa_shiftVec p i a k) (p.gaussianCoordinateVariance k) := by
  cases k with
  | inl x => exact fa_withDensity_ratio _ (fa_variance_inl_ne_zero p x)
  | inr _ => simp only [fa_shiftVec, fa_ratio_zero, withDensity_one]

/-- The likelihood `R_a(z) = ∏_k exp((m_k z_k - m_k²/2)/v_k)` of the shifted coordinates. -/
def fa_density (a : ℝ) (z : p.GaussianCoordinate → ℝ) : ℝ≥0∞ :=
  ∏ k, fa_ratio (fa_shiftVec p i a k) (p.gaussianCoordinateVariance k) (z k)

theorem fa_measurable_density (a : ℝ) : Measurable (fa_density p i a) := by
  unfold fa_density
  exact Finset.measurable_prod _ fun k _ =>
    (fa_measurable_ratio _ _).comp (measurable_pi_apply k)

/-- The coordinate law. -/
abbrev fa_coordLaw : Measure (p.GaussianCoordinate → ℝ) :=
  (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))

theorem fa_coordLaw_eq :
    fa_coordLaw p = Measure.pi (fun k => gaussianReal 0 (p.gaussianCoordinateVariance k)) := rfl

/-- `Law(z + m) = R_a · Law(z)` (finite product of one-coordinate Gaussian shifts). -/
theorem fa_map_shift (a : ℝ) :
    (fa_coordLaw p).map (fun z => z + fa_shiftVec p i a) =
      (fa_coordLaw p).withDensity (fa_density p i a) := by
  classical
  rw [fa_coordLaw_eq]
  have hmap : (fun z : p.GaussianCoordinate → ℝ => z + fa_shiftVec p i a) =
      fun z k => (fun y : ℝ => y + fa_shiftVec p i a k) (z k) := by
    funext z k; rfl
  have : ∀ k, SigmaFinite ((gaussianReal 0 (p.gaussianCoordinateVariance k)).map
      (fun y : ℝ => y + fa_shiftVec p i a k)) := fun k => by
    rw [gaussianReal_map_add_const]; infer_instance
  rw [hmap, Measure.pi_map_pi (fun k => (measurable_add_const _).aemeasurable)]
  simp_rw [gaussianReal_map_add_const, zero_add]
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fa_density p i a) = fun z =>
      ∏ k, (s k).indicator
        (fa_ratio (fa_shiftVec p i a k) (p.gaussianCoordinateVariance k)) (z k) := by
    funext z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      unfold fa_density
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Set.indicator_of_mem (hz k (Set.mem_univ k))]
    · rw [Set.indicator_of_notMem hz]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hz
      obtain ⟨k, hk⟩ := hz
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)).symm
  rw [hind]
  dsimp only
  have hmeas : ∀ k, Measurable ((s k).indicator
      (fa_ratio (fa_shiftVec p i a k) (p.gaussianCoordinateVariance k))) :=
    fun k => (fa_measurable_ratio _ _).indicator (hs k)
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun k (z : p.GaussianCoordinate → ℝ) => (s k).indicator
      (fa_ratio (fa_shiftVec p i a k) (p.gaussianCoordinateVariance k)) (z k))
    (iIndepFun_pi fun k => (hmeas k).aemeasurable)
    (fun k => (hmeas k).comp (measurable_pi_apply k))).trans ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [(measurePreserving_eval
      (fun k => gaussianReal 0 (p.gaussianCoordinateVariance k)) k).lintegral_comp (hmeas k),
    lintegral_indicator (hs k), ← withDensity_apply _ (hs k), fa_withDensity_coord]

/-- The physical law as the coordinate pushforward. -/
theorem fa_law_eq (model : p.GaussianRingModel) :
    (model.law : Measure p.SiteMatrix) = (fa_coordLaw p).map p.gaussianReconstruction := by
  rw [model.law_eq_gaussianMatrixLaw]
  rfl

/-- `E_a[G] = E[R_a G]`. For every measurable `G ≥ 0`, every model and real `a`:
`∫ G(H + a P_S) d model.law = ∫ R_a(z) G(H(z)) dz`. -/
theorem fa_lintegral_shift (model : p.GaussianRingModel) (a : ℝ)
    {G : p.SiteMatrix → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ H, G (H + (a : ℂ) • pairProjector p i) ∂(model.law : Measure p.SiteMatrix) =
      ∫⁻ z, fa_density p i a z * G (p.gaussianReconstruction z) ∂fa_coordLaw p := by
  have hGs : Measurable fun H : p.SiteMatrix => G (H + (a : ℂ) • pairProjector p i) :=
    hG.comp (measurable_id.add_const _)
  rw [fa_law_eq p model, lintegral_map hGs p.measurable_gaussianReconstruction]
  simp_rw [← fa_reconstruction_add_shiftVec]
  have h := lintegral_map (μ := fa_coordLaw p) (hG.comp p.measurable_gaussianReconstruction)
    (measurable_add_const (fa_shiftVec p i a))
  rw [fa_map_shift] at h
  simp only [Function.comp] at h
  rw [← h]
  exact lintegral_withDensity_eq_lintegral_mul _ (fa_measurable_density p i a)
    (hG.comp p.measurable_gaussianReconstruction)

/-- The constant `K_a = ∏_k exp(m_k²/v_k)` of `R_a² = K_a R_{2a}`. -/
def fa_densitySqConst (a : ℝ) : ℝ≥0∞ :=
  ∏ k, ENNReal.ofReal (Real.exp (fa_shiftVec p i a k ^ 2 / p.gaussianCoordinateVariance k))

/-- `R_a² = K_a R_{2a}`. -/
theorem fa_density_sq (a : ℝ) (z : p.GaussianCoordinate → ℝ) :
    fa_density p i a z ^ 2 = fa_densitySqConst p i a * fa_density p i (2 * a) z := by
  unfold fa_density fa_densitySqConst
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [fa_ratio_sq, fa_shiftVec_two_mul]

/-- `K_a = exp(2W · a²/(c/W))`; for `a = t/(2Wρ)` this is `exp(t²/(2cρ²))`. -/
theorem fa_densitySqConst_eq (a : ℝ) :
    fa_densitySqConst p i a =
      ENNReal.ofReal (Real.exp ((2 * p.W : ℝ) * (a ^ 2 / (p.c / p.W)))) := by
  classical
  unfold fa_densitySqConst
  rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [Fintype.sum_sum_type]
  simp only [fa_shiftVec]
  have h0 : ∑ x : p.Site × p.Site × Bool,
      ((0 : ℝ) ^ 2 / (p.gaussianCoordinateVariance (Sum.inr x) : ℝ)) = 0 := by simp
  rw [h0, add_zero]
  have h1 : ∀ x : p.Site, ((if x.1 = i ∨ x.1 = i + 1 then a else 0) ^ 2 /
      (p.gaussianCoordinateVariance (Sum.inl x) : ℝ)) =
      if x.1 = i ∨ x.1 = i + 1 then a ^ 2 / (p.c / p.W) else 0 := by
    intro x
    rw [fa_variance_inl]
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hc : (Finset.univ.filter fun x : p.Site => x.1 = i ∨ x.1 = i + 1).card = 2 * p.W := by
    rw [← card_pairSite p i, Fintype.card_subtype]
  rw [hc]
  push_cast
  ring

/-- `∫ R_a² G(H) = K_a E_{2a}[G]`. -/
theorem fa_lintegral_density_sq (model : p.GaussianRingModel) (a : ℝ)
    {G : p.SiteMatrix → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, fa_density p i a z ^ 2 * G (p.gaussianReconstruction z) ∂fa_coordLaw p =
      fa_densitySqConst p i a *
        ∫⁻ H, G (H + ((2 * a : ℝ) : ℂ) • pairProjector p i)
          ∂(model.law : Measure p.SiteMatrix) := by
  simp_rw [fa_density_sq, mul_assoc]
  have hm0 := (fa_measurable_density p i (2 * a)).mul
    (hG.comp p.measurable_gaussianReconstruction)
  have hm : Measurable fun z => fa_density p i (2 * a) z * G (p.gaussianReconstruction z) := hm0
  rw [lintegral_const_mul (fa_densitySqConst p i a) hm, fa_lintegral_shift p i model (2 * a) hG]

/-- The coordinate law integrates `G ∘ H` as the physical law integrates `G`. -/
theorem fa_lintegral_reconstruction (model : p.GaussianRingModel)
    {G : p.SiteMatrix → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G (p.gaussianReconstruction z) ∂fa_coordLaw p =
      ∫⁻ H, G H ∂(model.law : Measure p.SiteMatrix) := by
  rw [fa_law_eq p model, lintegral_map hG p.measurable_gaussianReconstruction]

end Physical

end BlockBand.Endpoints
