module

public import BlockBand.Critical.GlobalSource.GapC
public import BlockBand.Critical.GlobalSource.ReplacementGaussian
public import BlockBand.Critical.GlobalSource.ReplacementTaylor

/-!
# Global Gaussian source, source replacement: slots, matched moments and the hybrid model

Every one of the `J·M` slots carries a block index `o` (law `discreteBlockLaw`)
and a full circular vector `h` on the path (`slotLaw`). A sampled tag of mass `m` is
`diag(tagWeight m o) h` (the block `o` of `h`, times `√(m/W)`); a Gaussian probe of covariance
`r/W²` is `diag(gaussWeight r) h`. Hybrids differ only in the weights (`slotWeight`), so all of
them live on one product law and the Lindeberg swaps are swaps of one weight.

* `sum_discreteBlockLaw_tagWeight_sq`: **exact covariance** `E(ξξ^*) = r/W²`;
* `slot_moments`, `slot_moments_match`: equal mean, mean square of every real linear functional
  and mean of every quadratic form for the tag and the Gaussian slot;
* `inner_matrixCoord_eq`, `sum_coef_pairMatrix_add`, `re_lin_eq`, `inner_hybrid_update`: after
  resampling one slot the characteristic phase is `θ₀ + tα + t²β`
  (from `K(t) = K(0) + tA + t²C`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

/-!
## One slot: a block index and a full circular vector
-/

/-- A slot sample: a block index `o : Fin (L + 1)` (`o = L`: no tag) and a circular vector on the
whole path. A tag uses the block `o` of the vector; a Gaussian probe uses all of it. -/
abbrev SlotSample (W L : ℕ) := Fin (L + 1) × (Fin L × Fin W → ℂ)

/-- Law of one slot: the discrete block law times a circular vector. -/
def slotLaw (W L : ℕ) (r : Fin L → ℝ) : Measure (SlotSample W L) :=
  (discreteBlockLaw W L r).prod (circularVectorLaw (Fin L × Fin W))

theorem isProbabilityMeasure_slotLaw {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) :
    IsProbabilityMeasure (slotLaw W L r) := by
  have := isProbabilityMeasure_discreteBlockLaw (W := W) hr
  unfold slotLaw; infer_instance

/-- Diagonal weight of a tag of mass `m` on block `o`: `√(m/W)` on the block, `0` elsewhere. -/
def tagWeight (W L : ℕ) (m : ℝ) (o : Fin (L + 1)) (x : Fin L × Fin W) : ℝ :=
  if x.1.val = o.val then Real.sqrt (m / W) else 0

/-- Diagonal weight `W⁻¹ √r` of a Gaussian probe of covariance `r/W²`. -/
def gaussWeight (W L : ℕ) (r : Fin L → ℝ) (x : Fin L × Fin W) : ℝ :=
  (W : ℝ)⁻¹ * Real.sqrt (r x.1)

/-- The vector `diag(w) h`. -/
def weightVec {σ : Type*} (w : σ → ℝ) (h : σ → ℂ) : σ → ℂ := fun x => (w x : ℂ) * h x

theorem tagWeight_last (W L : ℕ) (m : ℝ) (x : Fin L × Fin W) :
    tagWeight W L m (Fin.last L) x = 0 := by
  unfold tagWeight
  have : x.1.val ≠ (Fin.last L).val := by simp only [Fin.val_last]; exact x.1.isLt.ne
  simp only [this, ↓reduceIte]

theorem discreteBlockLaw_real_eq_of_not_pos {W L : ℕ} {r : Fin L → ℝ}
    (hpm : ¬ 0 < profileMass W L r) (o : Fin (L + 1)) :
    (discreteBlockLaw W L r).real {o} = if o = Fin.last L then 1 else 0 := by
  simp only [discreteBlockLaw, hpm, ↓reduceIte, Measure.real]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
  by_cases h : o = Fin.last L
  · subst h; simp
  · rw [Set.indicator_of_notMem (by simpa [eq_comm] using h)]; simp [h]

theorem profile_eq_zero_of_not_pos {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (hW : 0 < W)
    (hpm : ¬ 0 < profileMass W L r) (k : Fin L) : r k = 0 := by
  have h0 : profileMass W L r = 0 := by
    have : 0 ≤ profileMass W L r := by
      unfold profileMass; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hr k)
    linarith [not_lt.1 hpm]
  unfold profileMass at h0
  have hW' : (W : ℝ)⁻¹ ≠ 0 := by positivity
  have hs : ∑ k, r k = 0 := (mul_eq_zero.1 h0).resolve_left hW'
  exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hr k).1 hs k (Finset.mem_univ k)

/-- **Exact covariance of a sampled tag** (`E(ξξ^*|G) = Q/W²`): the block mixture of the
squared tag weights is the squared Gaussian weight. -/
theorem sum_discreteBlockLaw_tagWeight_sq {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k)
    (x : Fin L × Fin W) :
    ∑ o, (discreteBlockLaw W L r).real {o} * tagWeight W L (profileMass W L r) o x ^ 2 =
      gaussWeight W L r x ^ 2 := by
  by_cases hpm : 0 < profileMass W L r
  · have hW : 0 < W := by
      by_contra h
      simp [profileMass, Nat.le_zero.1 (not_lt.1 h)] at hpm
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    rw [Fin.sum_univ_castSucc, discreteBlockLaw_real_last hpm, zero_mul, add_zero]
    simp_rw [discreteBlockLaw_real_castSucc hr hpm]
    rw [Finset.sum_eq_single x.1]
    · unfold tagWeight gaussWeight
      simp only [Fin.val_castSucc, ↓reduceIte]
      rw [Real.sq_sqrt (by positivity), mul_pow, inv_pow, Real.sq_sqrt (hr _)]
      field_simp
    · intro k _ hk
      unfold tagWeight
      have : x.1.val ≠ (Fin.castSucc k).val := by
        simp only [Fin.val_castSucc]; exact fun h => hk (Fin.ext h).symm
      simp only [this, ↓reduceIte]; ring
    · simp
  · simp_rw [discreteBlockLaw_real_eq_of_not_pos hpm, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (Fin.last L)]
    simp only [Finset.mem_univ, ↓reduceIte, tagWeight_last]
    unfold gaussWeight
    rcases Nat.eq_zero_or_pos W with hW | hW
    · subst hW; simp
    · rw [profile_eq_zero_of_not_pos hr hW hpm]; simp

theorem sum_discreteBlockLaw_real {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) :
    ∑ o, (discreteBlockLaw W L r).real {o} = 1 := by
  have := isProbabilityMeasure_discreteBlockLaw (W := W) hr
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

theorem discreteBlockLaw_real_nonneg {W L : ℕ} {r : Fin L → ℝ} (o : Fin (L + 1)) :
    0 ≤ (discreteBlockLaw W L r).real {o} := measureReal_nonneg

/-- Integrability on a slot from integrability for each block index. -/
theorem integrable_slotLaw_of {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k)
    {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F] [MeasurableSpace F]
    [BorelSpace F] {f : SlotSample W L → F} (hm : Measurable f)
    (hf : ∀ o, Integrable (fun h => f (o, h)) (circularVectorLaw (Fin L × Fin W))) :
    Integrable f (slotLaw W L r) := by
  have := isProbabilityMeasure_discreteBlockLaw (W := W) hr
  unfold slotLaw
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  exact ⟨ae_of_all _ hf, Integrable.of_finite⟩

/-- Integrals on a slot are block mixtures of circular integrals. -/
theorem integral_slotLaw {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k)
    {f : SlotSample W L → ℝ} (hm : Measurable f)
    (hf : ∀ o, Integrable (fun h => f (o, h)) (circularVectorLaw (Fin L × Fin W))) :
    ∫ y, f y ∂slotLaw W L r =
      ∑ o, (discreteBlockLaw W L r).real {o} * ∫ h, f (o, h) ∂circularVectorLaw _ := by
  have := isProbabilityMeasure_discreteBlockLaw (W := W) hr
  have hint := integrable_slotLaw_of hr hm hf
  unfold slotLaw at hint ⊢
  rw [integral_prod _ hint, integral_fintype Integrable.of_finite]
  simp [smul_eq_mul]

/-- Lower integrals on a slot are block mixtures of circular lower integrals. -/
theorem lintegral_slotLaw {W L : ℕ} {r : Fin L → ℝ}
    {f : SlotSample W L → ℝ≥0∞} (hm : Measurable f) :
    ∫⁻ y, f y ∂slotLaw W L r =
      ∑ o, (discreteBlockLaw W L r) {o} * ∫⁻ h, f (o, h) ∂circularVectorLaw _ := by
  unfold slotLaw
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp [mul_comm]

/-!
## First two moments of a slot vector
-/

section SlotMoments
variable {σ : Type*} [Fintype σ]

theorem dotc_weightVec (w : σ → ℂ) (lam : σ → ℝ) (h : σ → ℂ) :
    star w ⬝ᵥ weightVec lam h = star (weightVec lam w) ⬝ᵥ h := by
  unfold dotProduct weightVec
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal]
  ring

/-- `diag(λ) G diag(λ)`. -/
def weightMat (lam : σ → ℝ) (G : Matrix σ σ ℂ) : Matrix σ σ ℂ :=
  Matrix.of fun x y => (lam x : ℂ) * G x y * (lam y : ℂ)

theorem quad_weightVec (G : Matrix σ σ ℂ) (lam : σ → ℝ) (h : σ → ℂ) :
    star (weightVec lam h) ⬝ᵥ (G *ᵥ weightVec lam h) = star h ⬝ᵥ (weightMat lam G *ᵥ h) := by
  unfold dotProduct weightVec weightMat Matrix.mulVec dotProduct
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, Matrix.of_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem trace_weightMat (lam : σ → ℝ) (G : Matrix σ σ ℂ) :
    Matrix.trace (weightMat lam G) = ∑ x, ((lam x : ℂ) ^ 2 * G x x) := by
  unfold Matrix.trace weightMat
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.diag, Matrix.of_apply]
  ring

theorem re_sq_eq (z : ℂ) : z.re ^ 2 = (‖z‖ ^ 2 + (z ^ 2).re) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, pow_two z, Complex.mul_re]; ring

/-- `∫ Re f = Re ∫ f` with `Complex.re` (syntactic form). -/
theorem integral_complex_re {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : ∫ x, (f x).re ∂μ = (∫ x, f x ∂μ).re := integral_re hf

theorem integrable_complex_re {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => (f x).re) μ := hf.re

variable [DecidableEq σ]

omit [DecidableEq σ] in
theorem integral_re_dotc_weightVec (w : σ → ℂ) (lam : σ → ℝ) :
    ∫ h, (star w ⬝ᵥ weightVec lam h).re ∂circularVectorLaw σ = 0 := by
  simp_rw [dotc_weightVec]
  rw [integral_complex_re (integrable_dotc_circular _), integral_dotc_circular, Complex.zero_re]

omit [DecidableEq σ] in
theorem integrable_re_dotc_weightVec (w : σ → ℂ) (lam : σ → ℝ) :
    Integrable (fun h => (star w ⬝ᵥ weightVec lam h).re) (circularVectorLaw σ) := by
  simp_rw [dotc_weightVec]; exact integrable_complex_re (integrable_dotc_circular _)

theorem integrable_re_dotc_weightVec_sq (w : σ → ℂ) (lam : σ → ℝ) :
    Integrable (fun h => (star w ⬝ᵥ weightVec lam h).re ^ 2) (circularVectorLaw σ) := by
  simp_rw [dotc_weightVec, re_sq_eq]
  exact ((integrable_norm_sq_dotc _).add (integrable_complex_re (integrable_dotc_sq _))).div_const 2

theorem integral_re_dotc_weightVec_sq (w : σ → ℂ) (lam : σ → ℝ) :
    ∫ h, (star w ⬝ᵥ weightVec lam h).re ^ 2 ∂circularVectorLaw σ =
      (∑ x, ‖w x‖ ^ 2 * lam x ^ 2) / 2 := by
  simp_rw [dotc_weightVec, re_sq_eq]
  rw [integral_div, integral_add (integrable_norm_sq_dotc _) (integrable_complex_re (integrable_dotc_sq _)),
    integral_complex_re (integrable_dotc_sq _), integral_dotc_sq, Complex.zero_re, add_zero,
    integral_norm_sq_dotc]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold weightVec
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]

theorem integrable_re_quad_weightVec (G : Matrix σ σ ℂ) (lam : σ → ℝ) (c : ℂ) :
    Integrable (fun h => (c * (star (weightVec lam h) ⬝ᵥ (G *ᵥ weightVec lam h))).re)
      (circularVectorLaw σ) := by
  simp_rw [quad_weightVec]; exact integrable_complex_re ((integrable_quadratic _).const_mul c)

theorem integral_re_quad_weightVec (G : Matrix σ σ ℂ) (lam : σ → ℝ) (c : ℂ) :
    ∫ h, (c * (star (weightVec lam h) ⬝ᵥ (G *ᵥ weightVec lam h))).re ∂circularVectorLaw σ =
      (c * ∑ x, ((lam x : ℂ) ^ 2 * G x x)).re := by
  simp_rw [quad_weightVec]
  rw [integral_complex_re ((integrable_quadratic _).const_mul c), integral_const_mul, integral_quadratic,
    trace_weightMat]

end SlotMoments

section SlotMatch
variable {W L : ℕ}

theorem measurable_slot_of {f : SlotSample W L → ℝ}
    (hf : ∀ o, Measurable fun h => f (o, h)) : Measurable f :=
  measurable_from_prod_countable_right hf

theorem continuous_re_dotc_weightVec (w : Fin L × Fin W → ℂ) (lam : Fin L × Fin W → ℝ) :
    Continuous fun h : Fin L × Fin W → ℂ => (star w ⬝ᵥ weightVec lam h).re := by
  unfold dotProduct weightVec; fun_prop

theorem continuous_re_quad_weightVec (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (lam : Fin L × Fin W → ℝ) (c : ℂ) :
    Continuous fun h : Fin L × Fin W → ℂ =>
      (c * (star (weightVec lam h) ⬝ᵥ (G *ᵥ weightVec lam h))).re := by
  unfold dotProduct weightVec Matrix.mulVec dotProduct; fun_prop

variable {r : Fin L → ℝ}

/-- The three slot moments, for any block-dependent weight `λ`. -/
theorem slot_moments (hr : ∀ k, 0 ≤ r k) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (w : Fin L × Fin W → ℂ) (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : ℂ) :
    Integrable (fun y : SlotSample W L => (star w ⬝ᵥ weightVec (lam y.1) y.2).re) (slotLaw W L r) ∧
    Integrable (fun y : SlotSample W L => (star w ⬝ᵥ weightVec (lam y.1) y.2).re ^ 2)
      (slotLaw W L r) ∧
    Integrable (fun y : SlotSample W L =>
      (c * (star (weightVec (lam y.1) y.2) ⬝ᵥ (G *ᵥ weightVec (lam y.1) y.2))).re)
      (slotLaw W L r) ∧
    ∫ y, (star w ⬝ᵥ weightVec (lam y.1) y.2).re ∂slotLaw W L r = 0 ∧
    ∫ y, (star w ⬝ᵥ weightVec (lam y.1) y.2).re ^ 2 ∂slotLaw W L r =
      ∑ o, (discreteBlockLaw W L r).real {o} * ((∑ x, ‖w x‖ ^ 2 * lam o x ^ 2) / 2) ∧
    ∫ y, (c * (star (weightVec (lam y.1) y.2) ⬝ᵥ (G *ᵥ weightVec (lam y.1) y.2))).re
        ∂slotLaw W L r =
      ∑ o, (discreteBlockLaw W L r).real {o} * (c * ∑ x, ((lam o x : ℂ) ^ 2 * G x x)).re := by
  have m1 : Measurable fun y : SlotSample W L => (star w ⬝ᵥ weightVec (lam y.1) y.2).re :=
    measurable_slot_of fun o => (continuous_re_dotc_weightVec w (lam o)).measurable
  have m2 : Measurable fun y : SlotSample W L => (star w ⬝ᵥ weightVec (lam y.1) y.2).re ^ 2 :=
    m1.pow_const 2
  have m3 : Measurable fun y : SlotSample W L =>
      (c * (star (weightVec (lam y.1) y.2) ⬝ᵥ (G *ᵥ weightVec (lam y.1) y.2))).re :=
    measurable_slot_of fun o => (continuous_re_quad_weightVec G (lam o) c).measurable
  refine ⟨integrable_slotLaw_of hr m1 fun o => integrable_re_dotc_weightVec w (lam o),
    integrable_slotLaw_of hr m2 fun o => integrable_re_dotc_weightVec_sq w (lam o),
    integrable_slotLaw_of hr m3 fun o => integrable_re_quad_weightVec G (lam o) c, ?_, ?_, ?_⟩
  · rw [integral_slotLaw hr m1 fun o => integrable_re_dotc_weightVec w (lam o)]
    simp [integral_re_dotc_weightVec]
  · rw [integral_slotLaw hr m2 fun o => integrable_re_dotc_weightVec_sq w (lam o)]
    simp_rw [integral_re_dotc_weightVec_sq]
  · rw [integral_slotLaw hr m3 fun o => integrable_re_quad_weightVec G (lam o) c]
    simp_rw [integral_re_quad_weightVec]

/-- **Matching of the second moments**: the block-sampled tag and the Gaussian
probe have the same covariance, hence the same mean square of every real linear functional and the
same mean of every quadratic form. -/
theorem slot_moments_match (hr : ∀ k, 0 ≤ r k) (w : Fin L × Fin W → ℂ)
    (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (c : ℂ) :
    ∑ o, (discreteBlockLaw W L r).real {o} *
        ((∑ x, ‖w x‖ ^ 2 * tagWeight W L (profileMass W L r) o x ^ 2) / 2) =
      ∑ o, (discreteBlockLaw W L r).real {o} * ((∑ x, ‖w x‖ ^ 2 * gaussWeight W L r x ^ 2) / 2) ∧
    ∑ o, (discreteBlockLaw W L r).real {o} *
        (c * ∑ x, ((tagWeight W L (profileMass W L r) o x : ℂ) ^ 2 * G x x)).re =
      ∑ o, (discreteBlockLaw W L r).real {o} *
        (c * ∑ x, ((gaussWeight W L r x : ℂ) ^ 2 * G x x)).re := by
  constructor
  · rw [← Finset.sum_mul, sum_discreteBlockLaw_real hr, one_mul]
    have h : ∀ o, (discreteBlockLaw W L r).real {o} *
        ((∑ x, ‖w x‖ ^ 2 * tagWeight W L (profileMass W L r) o x ^ 2) / 2) =
        ∑ x, ‖w x‖ ^ 2 * ((discreteBlockLaw W L r).real {o} *
          tagWeight W L (profileMass W L r) o x ^ 2) / 2 := by
      intro o
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    simp_rw [h]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_div, ← Finset.mul_sum, sum_discreteBlockLaw_tagWeight_sq hr x]
  · rw [← Finset.sum_mul, sum_discreteBlockLaw_real hr, one_mul]
    have h : ∀ o, (discreteBlockLaw W L r).real {o} *
        (c * ∑ x, ((tagWeight W L (profileMass W L r) o x : ℂ) ^ 2 * G x x)).re =
        (c * ∑ x, (((discreteBlockLaw W L r).real {o} *
          tagWeight W L (profileMass W L r) o x ^ 2 : ℝ) : ℂ) * G x x).re := by
      intro o
      rw [← Complex.re_ofReal_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast; ring
    simp_rw [h, ← Complex.re_sum, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_discreteBlockLaw_tagWeight_sq hr]
    push_cast
    rfl

end SlotMatch

/-!
## Characteristic tests in coordinates
-/

section Coord
variable {J : ℕ}

/-- `⟪matrixCoord K, u⟫ = Re Σ_{a,c} (u_{ac0} - i u_{ac1}) K_{ac}`. -/
def coefU (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (a c : Fin J) : ℂ :=
  (u (a, c, 0) : ℂ) - (u (a, c, 1) : ℂ) * I

theorem inner_matrixCoord_eq (K : Matrix (Fin J) (Fin J) ℂ)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    ⟪matrixCoord J K, u⟫ = (∑ a, ∑ c, coefU u a c * K a c).re := by
  rw [PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fin.sum_univ_two]
  simp only [matrixCoord_apply, coefU, RCLike.inner_apply]
  simp [Complex.mul_re]

theorem norm_coefU_le (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (a c : Fin J) :
    ‖coefU u a c‖ ≤ 2 * ‖u‖ := by
  unfold coefU
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
  have h0 := PiLp.norm_apply_le u (a, c, 0)
  have h1 := PiLp.norm_apply_le u (a, c, 1)
  linarith

end Coord

/-!
## Expanding a bilinear form after adding one vector to one group
-/

section Expand
variable {σ : Type*} [Fintype σ] {J : ℕ}

/-- The matrix `(η_a^* G η_c)_{a,c}`. -/
def pairMatrix (G : Matrix σ σ ℂ) (η : Fin J → σ → ℂ) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c => star (η a) ⬝ᵥ (G *ᵥ η c)

theorem sum_coef_pairMatrix_add (coef : Fin J → Fin J → ℂ) (G : Matrix σ σ ℂ)
    (η : Fin J → σ → ℂ) (a : Fin J) (X : σ → ℂ) :
    ∑ b, ∑ c, coef b c * pairMatrix G (fun b => η b + if b = a then X else 0) b c =
      ∑ b, ∑ c, coef b c * pairMatrix G η b c +
        (∑ b, coef b a * (star (η b) ⬝ᵥ (G *ᵥ X)) + ∑ c, coef a c * (star X ⬝ᵥ (G *ᵥ η c))) +
        coef a a * (star X ⬝ᵥ (G *ᵥ X)) := by
  have hentry : ∀ b c, pairMatrix G (fun b => η b + if b = a then X else 0) b c =
      pairMatrix G η b c + (if c = a then star (η b) ⬝ᵥ (G *ᵥ X) else 0) +
        (if b = a then star X ⬝ᵥ (G *ᵥ η c) else 0) +
        (if b = a then (if c = a then star X ⬝ᵥ (G *ᵥ X) else 0) else 0) := by
    intro b c
    unfold pairMatrix
    by_cases hb : b = a <;> by_cases hc : c = a
    all_goals simp [hb, hc, star_add, add_dotProduct, dotProduct_add, Matrix.mulVec_add]
    all_goals ring
  simp only [hentry, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

/-- Real-linear part as an inner product: `Re ℓ(X) = Re (w^* X)`. -/
def linVec (coef : Fin J → Fin J → ℂ) (G : Matrix σ σ ℂ) (η : Fin J → σ → ℂ) (a : Fin J) :
    σ → ℂ :=
  ∑ b, star (coef b a) • (Gᴴ *ᵥ η b) + ∑ c, coef a c • (G *ᵥ η c)

theorem re_lin_eq (coef : Fin J → Fin J → ℂ) (G : Matrix σ σ ℂ) (η : Fin J → σ → ℂ) (a : Fin J)
    (X : σ → ℂ) :
    (∑ b, coef b a * (star (η b) ⬝ᵥ (G *ᵥ X)) + ∑ c, coef a c * (star X ⬝ᵥ (G *ᵥ η c))).re =
      (star (linVec coef G η a) ⬝ᵥ X).re := by
  have h1 : ∀ b, coef b a * (star (η b) ⬝ᵥ (G *ᵥ X)) =
      star (star (coef b a) • (Gᴴ *ᵥ η b)) ⬝ᵥ X := by
    intro b
    rw [star_smul, star_star, smul_dotProduct, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec, smul_eq_mul]
  have h2 : ∀ c, (coef a c * (star X ⬝ᵥ (G *ᵥ η c))).re =
      (star (coef a c • (G *ᵥ η c)) ⬝ᵥ X).re := by
    intro c
    rw [star_smul, smul_dotProduct, smul_eq_mul, ← Complex.conj_re]
    congr 1
    unfold dotProduct
    rw [map_mul, map_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [map_mul, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
    ring
  rw [Complex.add_re, Complex.re_sum, Complex.re_sum]
  simp_rw [h1, h2]
  unfold linVec
  rw [star_add, add_dotProduct, Complex.add_re, star_sum, star_sum, sum_dotProduct, sum_dotProduct,
    Complex.re_sum, Complex.re_sum]

end Expand

/-!
## The hybrid model
-/

section Hybrid
variable {W L J M : ℕ}

/-- Weight of slot `s` when the slots in `S` are sampled tags and the others Gaussian probes. -/
def slotWeight (W L : ℕ) {J M : ℕ} (r : Fin J → Fin L → ℝ) (S : Finset (Fin (J * M)))
    (s : Fin (J * M)) (o : Fin (L + 1)) : Fin L × Fin W → ℝ :=
  if s ∈ S then tagWeight W L (profileMass W L (r (tagGroup s))) o
  else gaussWeight W L (r (tagGroup s))

/-- Group vectors `η_a = M^{-1/2} Σ_{tagGroup s = a} diag(Λ_s(o_s)) h_s`. -/
def slotSum (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (y : Fin (J * M) → SlotSample W L) (a : Fin J) : Fin L × Fin W → ℂ :=
  fun x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
    ∑ s, if tagGroup s = a then (Λ s (y s).1 x : ℂ) * (y s).2 x else 0

/-- The weights with slot `j` removed. -/
def zeroAt (j : Fin (J * M)) (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) :
    Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ :=
  fun s => if s = j then 0 else Λ s

theorem zeroAt_update (j : Fin (J * M)) (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (v : Fin (L + 1) → Fin L × Fin W → ℝ) : zeroAt j (Function.update Λ j v) = zeroAt j Λ := by
  funext s
  unfold zeroAt
  by_cases h : s = j
  · simp [h]
  · simp [h]

/-- Resampling slot `j` adds one weighted vector to its group. -/
theorem slotSum_update (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (y : Fin (J * M) → SlotSample W L) (j : Fin (J * M)) (y' : SlotSample W L) :
    slotSum Λ (Function.update y j y') = fun b => slotSum (zeroAt j Λ) y b +
      if b = tagGroup j then (((Real.sqrt M)⁻¹ : ℝ) : ℂ) • weightVec (Λ j y'.1) y'.2 else 0 := by
  funext b x
  unfold slotSum
  have hterm : ∀ s, (if tagGroup s = b then (Λ s (Function.update y j y' s).1 x : ℂ) *
      (Function.update y j y' s).2 x else 0) =
      (if tagGroup s = b then (zeroAt j Λ s (y s).1 x : ℂ) * (y s).2 x else 0) +
        if s = j then (if tagGroup j = b then (Λ j y'.1 x : ℂ) * y'.2 x else 0) else 0 := by
    intro s
    by_cases hs : s = j
    · subst hs; simp [zeroAt]
    · simp [zeroAt, hs]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hb : b = tagGroup j
  · subst hb; simp [weightVec, mul_add]
  · have hb' : tagGroup j ≠ b := fun h => hb h.symm
    simp [hb, hb']

/-- The characteristic integrand of the hybrid with weights `Λ`. -/
def hybridF {Ω : Type*} (G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (z : Ω × (Fin (J * M) → SlotSample W L)) : ℂ :=
  exp ((⟪matrixCoord J (pairMatrix (G z.1) (slotSum Λ z.2)), u⟫ : ℂ) * I)

theorem norm_hybridF {Ω : Type*} (G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (z : Ω × (Fin (J * M) → SlotSample W L)) :
    ‖hybridF G Λ u z‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_pairMatrix {σ : Type*} [Fintype σ] :
    Continuous fun p : Matrix σ σ ℂ × (Fin J → σ → ℂ) => pairMatrix p.1 p.2 := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  unfold pairMatrix dotProduct Matrix.mulVec dotProduct
  fun_prop

theorem measurable_slotSum (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) :
    Measurable fun y : Fin (J * M) → SlotSample W L => slotSum Λ y := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun x => ?_
  unfold slotSum
  refine measurable_const.mul (Finset.measurable_sum _ fun s _ => ?_)
  split_ifs
  · refine Measurable.mul ?_ ?_
    · have h : Measurable fun o : Fin (L + 1) => (Λ s o x : ℂ) := measurable_of_countable _
      exact h.comp (measurable_fst.comp (measurable_pi_apply s))
    · exact (measurable_pi_apply x).comp (measurable_snd.comp (measurable_pi_apply s))
  · exact measurable_const

theorem measurable_hybridF {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hG : Measurable G)
    (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) : Measurable (hybridF G Λ u) := by
  have h1 : Measurable fun z : Ω × (Fin (J * M) → SlotSample W L) =>
      pairMatrix (G z.1) (slotSum Λ z.2) :=
    continuous_pairMatrix.measurable.comp ((hG.comp measurable_fst).prodMk
      ((measurable_slotSum Λ).comp measurable_snd))
  have h2 : Continuous fun K : Matrix (Fin J) (Fin J) ℂ =>
      exp ((⟪matrixCoord J K, u⟫ : ℂ) * I) := by
    have := (matrixCoord J).continuous; fun_prop
  exact h2.measurable.comp h1

/-- **One swap in coordinates**: after resampling slot `j`, the phase is
`θ₀ + t α + t² β` with `α = Re(w^*X)` real-linear and `β = Re(c X^*GX)`, `t = M^{-1/2}`. -/
theorem inner_hybrid_update (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (y : Fin (J * M) → SlotSample W L) (j : Fin (J * M)) (y' : SlotSample W L) :
    ⟪matrixCoord J (pairMatrix G (slotSum Λ (Function.update y j y'))), u⟫ =
      ⟪matrixCoord J (pairMatrix G (slotSum (zeroAt j Λ) y)), u⟫ +
        (Real.sqrt M)⁻¹ * (star (linVec (coefU u) G (slotSum (zeroAt j Λ) y) (tagGroup j)) ⬝ᵥ
          weightVec (Λ j y'.1) y'.2).re +
        (Real.sqrt M)⁻¹ ^ 2 * (coefU u (tagGroup j) (tagGroup j) *
          (star (weightVec (Λ j y'.1) y'.2) ⬝ᵥ (G *ᵥ weightVec (Λ j y'.1) y'.2))).re := by
  set t : ℝ := (Real.sqrt M)⁻¹
  set η := slotSum (zeroAt j Λ) y
  set X0 := weightVec (Λ j y'.1) y'.2
  set a := tagGroup j
  rw [inner_matrixCoord_eq, inner_matrixCoord_eq, slotSum_update, sum_coef_pairMatrix_add]
  have hstar : star ((t : ℂ) • X0) = (t : ℂ) • star X0 := by
    rw [star_smul, show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
  have hlin : ∑ b, coefU u b a * (star (η b) ⬝ᵥ (G *ᵥ ((t : ℂ) • X0))) +
      ∑ c, coefU u a c * (star ((t : ℂ) • X0) ⬝ᵥ (G *ᵥ η c)) =
      (t : ℂ) * (∑ b, coefU u b a * (star (η b) ⬝ᵥ (G *ᵥ X0)) +
        ∑ c, coefU u a c * (star X0 ⬝ᵥ (G *ᵥ η c))) := by
    rw [hstar, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; ring
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_dotProduct, smul_eq_mul]; ring
  have hquad : coefU u a a * (star ((t : ℂ) • X0) ⬝ᵥ (G *ᵥ ((t : ℂ) • X0))) =
      ((t ^ 2 : ℝ) : ℂ) * (coefU u a a * (star X0 ⬝ᵥ (G *ᵥ X0))) := by
    rw [hstar, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    push_cast; ring
  rw [hlin, hquad, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    re_lin_eq]

end Hybrid

end BlockBand.Critical.GlobalSource
