module

public import BlockBand.Palm.CoarseRelativeGaussMoment

/-!
# Good spectral event: operator norm of Gaussian matrices

* `opB M = ‖toEuclideanCLM M‖`, the Euclidean operator norm, with its `l2Norm` form and
  seminorm facts.
* `exists_net`: a `1/4`-net of the unit sphere of `ℂ^N` with at most `9^{2N}` points
  (maximal `1/4`-separated set; volumetric packing bound with an additive Haar measure).
* `clm_norm_le_of_net`: `‖T‖ ≤ 2 max_{x,y ∈ net} |⟪y, T x⟫|`.
* `bilin_tail`: for fixed `u, w`, `g ↦ u* G(g) w` is a centred linear Gaussian form with
  gradient norm `√(t ‖u‖²‖w‖²)`; `GaussianLpGradient` and Markov give
  `P(λ ≤ |u* G w|) ≤ (C √p √(t‖u‖²‖w‖²)/λ)^p`.
* `opB_tail`, `opB_tail_gue`: at `p = N`, union over net pairs,
  `P(r < ‖GUE_N(σ/N)‖) ≤ (K √σ / r)^N` for every `N ≥ 1`, `σ ≥ 0`, `r > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.CoarseRelative
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

variable {N : ℕ}

/-- Euclidean operator norm of a square complex matrix. -/
def opB (M : Matrix (Fin N) (Fin N) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

theorem l2Norm_eq_norm (x : Fin N → ℂ) : l2Norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin N))‖ := by
  rw [l2Norm_eq_sqrt_nsq, nsq_eq_euclidean, Real.sqrt_sq (norm_nonneg _)]

theorem opB_nonneg (M : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ opB M := norm_nonneg _

theorem l2Norm_mulVec_le (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    l2Norm (M *ᵥ x) ≤ opB M * l2Norm x := by
  rw [l2Norm_eq_norm, l2Norm_eq_norm, ← Matrix.toEuclideanCLM_toLp]
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) M).le_opNorm _

theorem opB_le_of (M : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, l2Norm (M *ᵥ x) ≤ C * l2Norm x) : opB M ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have := h (WithLp.ofLp x)
  rwa [l2Norm_eq_norm, l2Norm_eq_norm, ← Matrix.toEuclideanCLM_toLp, WithLp.toLp_ofLp] at this

theorem opB_add_le (M M' : Matrix (Fin N) (Fin N) ℂ) : opB (M + M') ≤ opB M + opB M' := by
  unfold opB; rw [map_add]; exact norm_add_le _ _

theorem opB_neg (M : Matrix (Fin N) (Fin N) ℂ) : opB (-M) = opB M := by
  unfold opB; rw [map_neg, norm_neg]

theorem opB_sub_le (M M' M'' : Matrix (Fin N) (Fin N) ℂ) :
    opB (M - M'') ≤ opB (M - M') + opB (M' - M'') := by
  have : M - M'' = (M - M') + (M' - M'') := by abel
  rw [this]; exact opB_add_le _ _

theorem opB_smul (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) : opB (c • M) = ‖c‖ * opB M := by
  unfold opB; rw [map_smul, norm_smul]

theorem continuous_opB : Continuous (opB (N := N)) := by
  unfold opB
  have : Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M) :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun M => Matrix.toEuclideanCLM (𝕜 := ℂ) M
         map_add' := fun A B => map_add _ A B
         map_smul' := fun c A => map_smul _ c A } :
        Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)))
  exact continuous_norm.comp this

/-!
## The `1/4`-net
-/

/-- A `1/4`-separated finite set of unit vectors. -/
def IsSeparated (S : Finset (EuclideanSpace ℂ (Fin N))) : Prop :=
  (∀ y ∈ S, ‖y‖ = 1) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 / 4 ≤ ‖x - y‖

theorem finrank_euclidean_complex :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

/-- Volumetric packing bound. -/
theorem card_le_of_isSeparated {S : Finset (EuclideanSpace ℂ (Fin N))} (hS : IsSeparated S) :
    S.card ≤ 9 ^ (2 * N) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    rcases S.eq_empty_or_nonempty with he | ⟨y, hy⟩
    · simp [he]
    · exfalso
      have h1 := hS.1 y hy
      have : y = 0 := Subsingleton.elim _ _
      rw [this, norm_zero] at h1
      exact zero_ne_one h1
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set μ : Measure (EuclideanSpace ℂ (Fin N)) := Measure.addHaar
  set d := Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) with hd
  have hdisj : (S : Set (EuclideanSpace ℂ (Fin N))).PairwiseDisjoint
      (fun y => Metric.ball y (1 / 8)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have := hS.2 x hx y hy hxy
    linarith
  have hsub : (⋃ y ∈ S, Metric.ball y (1 / 8 : ℝ)) ⊆ Metric.ball 0 (9 / 8) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [sub_zero]
    have h1 := hS.1 y hy
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ < 9 / 8 := by linarith
  have hmeas := measure_biUnion_finset (μ := μ) hdisj (fun y _ => Metric.isOpen_ball.measurableSet)
  have hle := measure_mono (μ := μ) hsub
  rw [hmeas] at hle
  simp_rw [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 1 / 8)] at hle
  rw [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 9 / 8), Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc] at hle
  have hB0 : μ (Metric.ball 0 1) ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : μ (Metric.ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hB0 hBt).1 hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  have h4 : (S.card : ℝ) ≤ 9 ^ d := by
    have hp : (0 : ℝ) < (1 / 8) ^ d := by positivity
    have : (9 / 8 : ℝ) ^ d = 9 ^ d * (1 / 8) ^ d := by rw [← mul_pow]; norm_num
    rw [this] at h3
    exact le_of_mul_le_mul_right h3 hp
  rw [hd, finrank_euclidean_complex] at h4
  exact_mod_cast h4

/-- A `1/4`-net of the unit sphere of `ℂ^N` with at most `9^{2N}` points. -/
theorem exists_net (N : ℕ) : ∃ S : Finset (EuclideanSpace ℂ (Fin N)),
    (∀ y ∈ S, ‖y‖ = 1) ∧ S.card ≤ 9 ^ (2 * N) ∧
      ∀ x : EuclideanSpace ℂ (Fin N), ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ < 1 / 4 := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset (EuclideanSpace ℂ (Fin N)), IsSeparated S ∧ S.card = n
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  have hspec := Nat.findGreatest_spec (P := P) (Nat.zero_le (9 ^ (2 * N))) hP0
  obtain ⟨S, hS, hcard⟩ := hspec
  refine ⟨S, hS.1, card_le_of_isSeparated hS, ?_⟩
  intro x hx
  by_contra hne
  simp only [not_exists, not_and, not_lt] at hne
  have hxS : x ∉ S := fun hxS => by
    have := hne x hxS
    rw [sub_self, norm_zero] at this
    norm_num at this
  have hsep : IsSeparated (insert x S) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx
      · exact hS.1 y hy
    · intro u hu v hv huv
      rcases Finset.mem_insert.1 hu with hu' | hu' <;>
        rcases Finset.mem_insert.1 hv with hv' | hv'
      · exact absurd (hu'.trans hv'.symm) huv
      · rw [hu']; exact hne v hv'
      · rw [hv', norm_sub_rev]; exact hne u hu'
      · exact hS.2 u hu' v hv' huv
  have hle := Nat.le_findGreatest (P := P) (card_le_of_isSeparated hsep) ⟨_, hsep, rfl⟩
  rw [Finset.card_insert_of_notMem hxS, ← hcard] at hle
  omega

/-!
## Operator norm from the net
-/

theorem clm_norm_le_of_net (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (S : Finset (EuclideanSpace ℂ (Fin N))) (hS1 : ∀ y ∈ S, ‖y‖ = 1)
    (hnet : ∀ x : EuclideanSpace ℂ (Fin N), ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ < 1 / 4)
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ x ∈ S, ∀ y ∈ S, ‖inner ℂ y (T x)‖ ≤ r) : ‖T‖ ≤ 2 * r := by
  have hunit : ∀ x : EuclideanSpace ℂ (Fin N), ‖x‖ = 1 → ‖T x‖ ≤ r + ‖T‖ / 2 := by
    intro x hx
    by_cases hTx : T x = 0
    · rw [hTx, norm_zero]; positivity
    have hpos : 0 < ‖T x‖ := norm_pos_iff.2 hTx
    set y : EuclideanSpace ℂ (Fin N) := ((‖T x‖ : ℂ)⁻¹) • T x with hy
    have hy1 : ‖y‖ = 1 := by
      rw [hy, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
        inv_mul_cancel₀ hpos.ne']
    have hyx : inner ℂ y (T x) = (‖T x‖ : ℂ) := by
      rw [hy, inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp only [map_inv₀, Complex.conj_ofReal]
      have hne : (‖T x‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
      rfl
    obtain ⟨x', hx'S, hxx'⟩ := hnet x hx
    obtain ⟨y', hy'S, hyy'⟩ := hnet y hy1
    have hdec : inner ℂ y (T x) =
        inner ℂ y' (T x') + inner ℂ (y - y') (T x) + inner ℂ y' (T (x - x')) := by
      rw [map_sub, inner_sub_left, inner_sub_right]; ring
    have h1 : ‖inner ℂ (y - y') (T x)‖ ≤ ‖T‖ / 4 := by
      calc ‖inner ℂ (y - y') (T x)‖ ≤ ‖y - y'‖ * ‖T x‖ := norm_inner_le_norm _ _
        _ ≤ (1 / 4) * ‖T‖ := by
          apply mul_le_mul hyy'.le _ (norm_nonneg _) (by norm_num)
          simpa [hx] using T.le_opNorm x
        _ = ‖T‖ / 4 := by ring
    have h2 : ‖inner ℂ y' (T (x - x'))‖ ≤ ‖T‖ / 4 := by
      calc ‖inner ℂ y' (T (x - x'))‖ ≤ ‖y'‖ * ‖T (x - x')‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖T‖ * (1 / 4)) := by
          rw [hS1 y' hy'S]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxx'.le (norm_nonneg _))
        _ = ‖T‖ / 4 := by ring
    have h0 := h x' hx'S y' hy'S
    have : ‖T x‖ = ‖inner ℂ y (T x)‖ := by rw [hyx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
    rw [this, hdec]
    calc _ ≤ ‖inner ℂ y' (T x') + inner ℂ (y - y') (T x)‖ + ‖inner ℂ y' (T (x - x'))‖ :=
          norm_add_le _ _
      _ ≤ ‖inner ℂ y' (T x')‖ + ‖inner ℂ (y - y') (T x)‖ + ‖inner ℂ y' (T (x - x'))‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ r + ‖T‖ / 4 + ‖T‖ / 4 := by gcongr
      _ = r + ‖T‖ / 2 := by ring
  have hall : ∀ x, ‖T x‖ ≤ (r + ‖T‖ / 2) * ‖x‖ := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hu := hunit (((‖x‖ : ℂ)⁻¹) • x) (by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp,
        inv_mul_cancel₀ hxp.ne'])
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxp] at hu
    rw [inv_mul_le_iff₀ hxp] at hu
    linarith
  have := T.opNorm_le_bound (by positivity) hall
  linarith

/-!
## Gaussian bilinear forms
-/

/-- The real-linear functional `g ↦ u* G(g) w`. -/
def bilinLin (t : ℝ≥0) (u w : Fin N → ℂ) : (((Fin N × Fin N) × Fin 2) → ℝ) →ₗ[ℝ] ℂ :=
  ({ toFun := fun A => star u ⬝ᵥ (A *ᵥ w)
     map_add' := fun A B => by simp [add_mulVec, dotProduct_add]
     map_smul' := fun r A => by simp [smul_mulVec, dotProduct_smul] } :
      Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℂ).comp (gueCoordLin t)

theorem bilin_eq_clm (t : ℝ≥0) (u w : Fin N → ℂ) :
    (fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w)) =
      ⇑(LinearMap.toContinuousLinearMap (bilinLin t u w)) := by
  funext g; rfl

theorem bilin_contDiff (t : ℝ≥0) (u w : Fin N → ℂ) :
    ContDiff ℝ 1 (fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w)) := by
  rw [bilin_eq_clm]; exact ContinuousLinearMap.contDiff _

theorem bilin_fderiv (t : ℝ≥0) (u w : Fin N → ℂ) (g v) :
    fderiv ℝ (fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w)) g v = star u ⬝ᵥ (gueCoord t v *ᵥ w) := by
  rw [bilin_eq_clm, ContinuousLinearMap.fderiv]; rfl

theorem bilin_grad (t : ℝ≥0) (u w : Fin N → ℂ) (g) :
    weightedGradientNorm (fun _ => (1 : ℝ≥0)) (fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w)) g =
      Real.sqrt ((t : ℝ) * (nsq u * nsq w)) := by
  unfold weightedGradientNorm
  congr 1
  simp only [NNReal.coe_one, one_mul, bilin_fderiv]
  exact sum_dot_gueCoord_sq t u w

theorem bilin_eq_sum (t : ℝ≥0) (u w : Fin N → ℂ) (g) :
    star u ⬝ᵥ (gueCoord t g *ᵥ w) =
      ∑ j, (g j : ℂ) * (star u ⬝ᵥ (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ w)) := by
  rw [gueCoord_eq_sum t g, Matrix.sum_mulVec, dotProduct_sum]
  simp [smul_mulVec, dotProduct_smul]

theorem bilin_memLp (t : ℝ≥0) (u w : Fin N → ℂ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w)) p (coordLaw N) := by
  have h : (fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w)) =
      ∑ j, fun g : ((Fin N × Fin N) × Fin 2) → ℝ =>
        ((g j : ℝ) : ℂ) * (star u ⬝ᵥ (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ w)) := by
    funext g
    rw [bilin_eq_sum, Finset.sum_apply]
  rw [h]
  exact memLp_finsetSum' _ (fun j _ => ((coord_memLp j p hp).ofReal (K := ℂ)).mul_const _)

theorem bilin_integral_zero (t : ℝ≥0) (u w : Fin N → ℂ) :
    ∫ g, star u ⬝ᵥ (gueCoord t g *ᵥ w) ∂coordLaw N = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (bilin_eq_sum t u w)),
    show coordLaw N = gaussianProduct (fun _ => (1 : ℝ≥0)) from rfl]
  have hi : ∀ j : (Fin N × Fin N) × Fin 2, Integrable (fun g : ((Fin N × Fin N) × Fin 2) → ℝ =>
      ((g j : ℝ) : ℂ) * (star u ⬝ᵥ (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ w)))
      (gaussianProduct (fun _ => (1 : ℝ≥0))) := fun j =>
    ((coord_integrable j).ofReal (𝕜 := ℂ)).mul_const _
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_mul_const, integral_complex_ofReal, coord_integral_zero]
  simp

/-- Fixed-moment tail of a bilinear Gaussian form, from `GaussianLpGradient`. -/
theorem bilin_tail (hLp : GaussianLpGradient) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ) (t : ℝ≥0) (u w : Fin N → ℂ) (lam : ℝ), 0 < lam →
      coordLaw N {g | lam ≤ ‖star u ⬝ᵥ (gueCoord t g *ᵥ w)‖} ≤
        ENNReal.ofReal ((C * Real.sqrt p * Real.sqrt ((t : ℝ) * (nsq u * nsq w)) / lam) ^ p) := by
  obtain ⟨C, hC, hLp'⟩ := hLp
  refine ⟨C, hC, ?_⟩
  intro p hp N t u w lam hlam
  set f := fun g => star u ⬝ᵥ (gueCoord t g *ᵥ w) with hfdef
  set μ := coordLaw N
  set B := Real.sqrt ((t : ℝ) * (nsq u * nsq w)) with hB
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hfl := hLp' p hp ((Fin N × Fin N) × Fin 2) (fun _ => 1) f (bilin_contDiff t u w)
    (bilin_memLp t u w _ ENNReal.ofReal_ne_top)
  have hint : ∫ g, f g ∂gaussianProduct (fun _ => (1 : ℝ≥0)) = 0 := bilin_integral_zero t u w
  simp only [hint, sub_zero] at hfl
  have hgrad : eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B := by
    have he : weightedGradientNorm (fun _ => (1 : ℝ≥0)) f = fun _ => B := funext (bilin_grad t u w)
    have h := eLpNorm_le_of_ae_bound (μ := μ) (p := ENNReal.ofReal p) (C := B)
      (f := weightedGradientNorm (fun _ => (1 : ℝ≥0)) f)
      (by rw [he]; exact aestronglyMeasurable_const)
      (Filter.Eventually.of_forall (fun g => by
        rw [he, Real.norm_eq_abs, abs_of_nonneg hB0]))
    rwa [measure_univ, ENNReal.one_rpow, one_mul] at h
  have hL : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C * Real.sqrt p * B) := by
    refine hfl.trans ?_
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * Real.sqrt p)]
    exact by gcongr
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hptr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hset : {g | lam ≤ ‖f g‖} = {g | ENNReal.ofReal lam ≤ ‖f g‖ₑ} := by
    ext g
    simp only [Set.mem_ofPred_eq, ← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
  change μ {g | lam ≤ ‖f g‖} ≤ _
  rw [hset]
  have hM := meas_ge_le_mul_pow_eLpNorm_enorm μ hp0 hptop
    (f := f) (ε := ENNReal.ofReal lam)
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hlam) (fun h => absurd h ENNReal.ofReal_ne_top)
  refine hM.trans ?_
  rw [hptr]
  have hpow : eLpNorm f (ENNReal.ofReal p) μ ^ p ≤ ENNReal.ofReal (C * Real.sqrt p * B) ^ p :=
    ENNReal.rpow_le_rpow hL (by linarith)
  calc (ENNReal.ofReal lam)⁻¹ ^ p * eLpNorm f (ENNReal.ofReal p) μ ^ p
      ≤ (ENNReal.ofReal lam)⁻¹ ^ p * ENNReal.ofReal (C * Real.sqrt p * B) ^ p := by gcongr
    _ = ENNReal.ofReal ((C * Real.sqrt p * B / lam) ^ p) := by
      rw [← ENNReal.ofReal_inv_of_pos hlam,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
      congr 2
      ring

/-!
## Operator-norm tail
-/

theorem inner_toEuclideanCLM_eq (M : Matrix (Fin N) (Fin N) ℂ) (x y : EuclideanSpace ℂ (Fin N)) :
    inner ℂ y (Matrix.toEuclideanCLM (𝕜 := ℂ) M x) =
      star (WithLp.ofLp y) ⬝ᵥ (M *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]

theorem nsq_ofLp_of_norm_one {y : EuclideanSpace ℂ (Fin N)} (hy : ‖y‖ = 1) :
    nsq (WithLp.ofLp y) = 1 := by
  rw [nsq_eq_euclidean, WithLp.toLp_ofLp, hy, one_pow]

/-- `P(r < ‖GUE_N(σ/N)‖) ≤ (K√σ/r)^N` in the real Gaussian coordinates. -/
theorem opB_tail (hLp : GaussianLpGradient) : ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 0 < N →
    ∀ σ : ℝ, 0 ≤ σ → ∀ r : ℝ, 0 < r →
      coordLaw N {g | r < opB (gueCoord (Real.toNNReal (σ / N)) g)} ≤
        ENNReal.ofReal ((K * Real.sqrt σ / r) ^ N) := by
  obtain ⟨C, hC, hT⟩ := bilin_tail hLp
  refine ⟨6561 * (2 * C), by positivity, ?_⟩
  intro N hN σ hσ r hr
  obtain ⟨S, hS1, hScard, hnet⟩ := exists_net N
  set t := Real.toNNReal (σ / N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (t : ℝ) = σ / N := Real.coe_toNNReal _ (by positivity)
  have hsub : {g | r < opB (gueCoord t g)} ⊆ ⋃ x ∈ S, ⋃ y ∈ S,
      {g | r / 2 ≤ ‖star (WithLp.ofLp y) ⬝ᵥ (gueCoord t g *ᵥ WithLp.ofLp x)‖} := by
    intro g hg
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hno
    have hle := clm_norm_le_of_net (Matrix.toEuclideanCLM (𝕜 := ℂ) (gueCoord t g)) S hS1 hnet
      (r := r / 2) (by positivity) (fun x hx y hy => by
        rw [inner_toEuclideanCLM_eq]; exact (hno x hx y hy).le)
    have : opB (gueCoord t g) ≤ r := by unfold opB; linarith
    exact absurd hg (not_lt.2 this)
  have hpair : ∀ x ∈ S, ∀ y ∈ S,
      coordLaw N {g | r / 2 ≤ ‖star (WithLp.ofLp y) ⬝ᵥ (gueCoord t g *ᵥ WithLp.ofLp x)‖} ≤
        ENNReal.ofReal ((2 * C * Real.sqrt σ / r) ^ N) := by
    intro x hx y hy
    refine (hT N (by exact_mod_cast hN) N t _ _ (r / 2) (by positivity)).trans
      (le_of_eq ?_)
    rw [nsq_ofLp_of_norm_one (hS1 y hy), nsq_ofLp_of_norm_one (hS1 x hx), mul_one, mul_one, ht,
      Real.rpow_natCast]
    congr 2
    have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
    rw [Real.sqrt_div' _ hNr.le]
    field_simp
  calc coordLaw N {g | r < opB (gueCoord t g)}
      ≤ coordLaw N (⋃ x ∈ S, ⋃ y ∈ S,
          {g | r / 2 ≤ ‖star (WithLp.ofLp y) ⬝ᵥ (gueCoord t g *ᵥ WithLp.ofLp x)‖}) :=
        measure_mono hsub
    _ ≤ ∑ x ∈ S, ∑ y ∈ S, coordLaw N
          {g | r / 2 ≤ ‖star (WithLp.ofLp y) ⬝ᵥ (gueCoord t g *ᵥ WithLp.ofLp x)‖} := by
        refine (measure_biUnion_finset_le S _).trans ?_
        exact Finset.sum_le_sum fun x _ => measure_biUnion_finset_le S _
    _ ≤ ∑ _x ∈ S, ∑ _y ∈ S, ENNReal.ofReal ((2 * C * Real.sqrt σ / r) ^ N) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpair x hx y hy
    _ = ENNReal.ofReal ((S.card : ℝ) * (S.card : ℝ) * (2 * C * Real.sqrt σ / r) ^ N) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((6561 * (2 * C) * Real.sqrt σ / r) ^ N) := by
        apply ENNReal.ofReal_le_ofReal
        have hc : (S.card : ℝ) ≤ 9 ^ (2 * N) := by exact_mod_cast hScard
        have hc2 : (S.card : ℝ) * S.card ≤ (6561 : ℝ) ^ N := by
          have : (6561 : ℝ) ^ N = 9 ^ (2 * N) * 9 ^ (2 * N) := by
            rw [← mul_pow, pow_mul]; norm_num
          rw [this]
          exact mul_le_mul hc hc (by positivity) (by positivity)
        calc (S.card : ℝ) * S.card * (2 * C * Real.sqrt σ / r) ^ N
            ≤ (6561 : ℝ) ^ N * (2 * C * Real.sqrt σ / r) ^ N :=
              mul_le_mul_of_nonneg_right hc2 (by positivity)
          _ = (6561 * (2 * C) * Real.sqrt σ / r) ^ N := by
              rw [← mul_pow]; congr 1; ring

theorem measurable_gueCoord_net (t : ℝ≥0) : Measurable (gueCoord (ι := Fin N) t) := by
  have hc : Measurable (BlockBand.SourceProcess.circularBrownianCoordinates (ι := Fin N)) := by
    apply Measurable.of_eval
    intro u
    unfold BlockBand.SourceProcess.circularBrownianCoordinates
    fun_prop
  have hg : Continuous (gueSample (ι := Fin N) t) := by
    unfold gueSample
    fun_prop
  exact hg.measurable.comp hc

/-- GUE form: `P(r < ‖GUE_N(σ/N)‖) ≤ (K√σ/r)^N`. -/
theorem opB_tail_gue (hLp : GaussianLpGradient) : ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 0 < N →
    ∀ σ : ℝ, 0 ≤ σ → ∀ r : ℝ, 0 < r →
      gueMeasure (Fin N) (Real.toNNReal (σ / N)) {M | r < opB M} ≤
        ENNReal.ofReal ((K * Real.sqrt σ / r) ^ N) := by
  obtain ⟨K, hK, h⟩ := opB_tail hLp
  refine ⟨K, hK, ?_⟩
  intro N hN σ hσ r hr
  have hS : MeasurableSet {M : Matrix (Fin N) (Fin N) ℂ | r < opB M} :=
    (isOpen_lt continuous_const continuous_opB).measurableSet
  rw [gueMeasure_eq_map_gaussianProduct, Measure.map_apply (measurable_gueCoord_net _) hS]
  exact h N hN σ hσ r hr

end BlockBand.Palm.GoodEvent
