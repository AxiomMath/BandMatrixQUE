module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularAugment

/-!
# Bounds for the augmented Dyson state up to a gap stop

On a non-collision sample and for `n > 0`: the overlaps stay in the box `[0, N‖q‖²]^N`
(`overlap_mem_box`, `xOf_dysonState`); strictly before `σ_n` all gaps exceed `1/n`
(`gap_of_lt_gapStop`), so `|𝒜 f| ≤ K_a` there (`exists_angGen_bound`); hence
`|∫_0^{r∧σ_n} 𝒜 f| ≤ K_a r` and `|f(X) - ∫𝒜f|` is bounded on `[0, T]` up to `σ_n` (`g2_stop_bound`).
The clock coordinate is `t` and `|Phi| ≤ e^{c_θ T}` on `[0, T]` (`Phi_bound`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_le)

variable {N : ℕ} {Ω : Type}

/-!
### Coordinates of the augmented state
-/

theorem Vint_two (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : Vint θ f Y u ω 2 = u := by
  simp [Vint, vdOf]

theorem prV2_Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : prV N 2 (Yplus θ f Y u ω) = u := by
  simp [Yplus, cV, Vint_two]

theorem prV1_Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : prV N 1 (Yplus θ f Y u ω) =
      ∫ r in Ioc (0 : ℝ) u, angularGenerator N (lamOf (Y r.toNNReal ω)) f
        (xOf (Y r.toNNReal ω)) := by
  simp [Yplus, cV, Vint, vdOf]

theorem prX_Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : prX N (Yplus θ f Y u ω) = xOf (Y u ω) := by
  rw [prX_eq_xOf, prY_Yplus]

theorem xOf_dysonState (q : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) :
    xOf (dysonState N q H) = fun i => dysonOverlap N q H i := by
  funext i; rw [xOf_eq]; simp only
  rw [← finSumFinEquiv_apply_right, dysonState_inr]

theorem lamOf_dysonState (q : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) :
    lamOf (dysonState N q H) = dysonEigenvalue N H := by
  funext i; rw [lamOf_eq]; simp only
  rw [← finSumFinEquiv_apply_left, dysonState_inl]

/-!
### The overlap box and the generator bound
-/

/-- The box `[0, N‖q‖²]^N` containing the overlaps. -/
def box (N : ℕ) (q : Fin N → ℂ) : Set (Fin N → ℝ) := Icc 0 fun _ => (N : ℝ) * qNormSq q

theorem isCompact_box (q : Fin N → ℂ) : IsCompact (box N q) := isCompact_Icc

theorem overlap_mem_box {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (q : Fin N → ℂ) : (fun i => dysonOverlap N q H i) ∈ box N q :=
  ⟨fun i => overlap_nonneg hH hs q i, fun i => overlap_le hH hs q i⟩

theorem exists_f_bound {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (q : Fin N → ℂ) :
    ∃ K, 0 ≤ K ∧ ∀ X ∈ box N q, |f X| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_box q).exists_bound_of_continuousOn hf.continuous.continuousOn
  exact ⟨max K 0, le_max_right _ _, fun X hX => (hK X hX).trans (le_max_left _ _)⟩

theorem exists_angGen_bound {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (q : Fin N → ℂ)
    {n : ℕ} (hn : 0 < n) : ∃ K, 0 ≤ K ∧ ∀ lam X, X ∈ box N q →
      (∀ i j, i ≠ j → 1 / (n : ℝ) < |lam i - lam j|) → |angularGenerator N lam f X| ≤ K := by
  have hc : Continuous fun X => ∑ i, ∑ j, |angTerm f i j X| :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_angTerm hf i j).abs
  obtain ⟨K, hK⟩ := (isCompact_box q).exists_bound_of_continuousOn hc.continuousOn
  have hδ : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  refine ⟨1 / (N * (1 / (n : ℝ)) ^ 2) * max K 0, by positivity, fun lam X hX hgap => ?_⟩
  rw [angularGenerator_eq_sum]
  have hsum : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), |angTerm f i j X| ≤ max K 0 := by
    have h1 : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), |angTerm f i j X| ≤
        ∑ i, ∑ j, |angTerm f i j X| := Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _
    have h2 := hK X hX
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg
      fun j _ => abs_nonneg _)] at h2
    exact h1.trans (h2.trans (le_max_left _ _))
  calc |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), dysonCoupling N lam i j * angTerm f i j X|
      ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          1 / (N * (1 / (n : ℝ)) ^ 2) * |angTerm f i j X| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
        rw [abs_mul, abs_of_nonneg (coupling_nonneg lam i j)]
        exact mul_le_mul_of_nonneg_right (coupling_le hδ (hgap i j hij).le) (abs_nonneg _)
    _ = 1 / (N * (1 / (n : ℝ)) ^ 2) *
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), |angTerm f i j X| := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-!
### Gaps before the gap stop
-/

theorem gap_of_lt_gapStop {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0} {n : ℕ} {ω : Ω}
    {x : ℝ≥0} (hx : (x : WithTop ℝ≥0) < gapStop N H s n ω) (i j : Fin N) (hij : i ≠ j) :
    1 / (n : ℝ) < |dysonEigenvalue N (H (s + x) ω) i - dysonEigenvalue N (H (s + x) ω) j| := by
  by_contra h
  push Not at h
  have : gapStop N H s n ω ≤ x := iInf₂_le x ⟨i, j, hij, h⟩
  exact absurd (hx.trans_le this) (lt_irrefl _)

/-!
### Bounds along the augmented process
-/

variable [MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

theorem V1_bound (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian) {s : ℝ≥0}
    (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) (θ : Fin N → ℝ)
    {f : (Fin N → ℝ) → ℝ} {n : ℕ} {K : ℝ} (hK : ∀ lam X, X ∈ box N q →
      (∀ i j, i ≠ j → 1 / (n : ℝ) < |lam i - lam j|) → |angularGenerator N lam f X| ≤ K)
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) ≤ gapStop N (fun t ω => F ω + G t ω) s n ω) :
    |prV N 1 (Yplus θ f (Yst N q G F s) r ω)| ≤ K * r := by
  rw [prV1_Yplus, integral_Ioc_eq_integral_Ioo, ← Real.norm_eq_abs]
  have hb : ∀ x ∈ Ioo (0 : ℝ) r, ‖angularGenerator N (lamOf (Yst N q G F s x.toNNReal ω)) f
      (xOf (Yst N q G F s x.toNNReal ω))‖ ≤ K := by
    intro x hx
    have hxr : (x.toNNReal : WithTop ℝ≥0) < gapStop N (fun t ω => F ω + G t ω) s n ω := by
      refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hr
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx.1.le]; exact hx.2
    have hsimp := hω _ (add_pos_of_pos_of_nonneg hs (zero_le : (0 : ℝ≥0) ≤ x.toNNReal))
    rw [Real.norm_eq_abs, Yst, lamOf_dysonState, xOf_dysonState]
    exact hK _ _ (overlap_mem_box (herm_add hG hFh _ ω) hsimp q)
      (fun i j hij => gap_of_lt_gapStop hxr i j hij)
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp) hb
  rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by simp), sub_zero] at this
  linarith [this]

theorem g2_stop_bound (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ)
    (θ : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ} {n : ℕ} {Kf Ka : ℝ}
    (hKf : ∀ X ∈ box N q, |f X| ≤ Kf) (hKa0 : 0 ≤ Ka) (hKa : ∀ lam X, X ∈ box N q →
      (∀ i j, i ≠ j → 1 / (n : ℝ) < |lam i - lam j|) → |angularGenerator N lam f X| ≤ Ka)
    {T r : ℝ≥0} (hr : r ≤ T) :
    |g2 f (Yplus θ f (Yst N q G F s)
      (stopTime (gapStop N (fun t ω => F ω + G t ω) s n ω) r) ω)| ≤ Kf + Ka * T := by
  set r' := stopTime (gapStop N (fun t ω => F ω + G t ω) s n ω) r
  have hr' : (r' : WithTop ℝ≥0) ≤ gapStop N (fun t ω => F ω + G t ω) s n ω :=
    BlockBand.SourceProcess.Stochastic.Semimartingale.stopTime_le_self _ r
  have hr'T : r' ≤ T := (stopTime_le _ r).trans hr
  unfold g2
  rw [prX_Yplus, Yst, xOf_dysonState]
  have h1 := hKf _ (overlap_mem_box (herm_add hG hFh (s + r') ω)
    (hω _ (add_pos_of_pos_of_nonneg hs (zero_le : (0 : ℝ≥0) ≤ r'))) q)
  have h2 := V1_bound hG hFh hs hω q θ hKa hr'
  have h3 : Ka * (r' : ℝ) ≤ Ka * T := mul_le_mul_of_nonneg_left (by exact_mod_cast hr'T) hKa0
  calc _ ≤ |f fun i => dysonOverlap N q (F ω + G (s + r') ω) i| +
        |prV N 1 (Yplus θ f (Yst N q G F s) r' ω)| := abs_sub _ _
    _ ≤ Kf + Ka * T := by linarith

omit [MeasurableSpace Ω] in
theorem Phi_bound {h : ℝ → ℝ} (hb : ∀ x, |h x| ≤ 1) (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ)
    (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) {T r : ℝ≥0} (hr : r ≤ T) (ω : Ω) :
    |Phi h θ (Yplus θ f Y r ω)| ≤ Real.exp (cθ θ * T) := by
  have hc : 0 ≤ cθ θ := by unfold cθ; positivity
  unfold Phi Efun
  rw [prV2_Yplus, abs_mul, Real.abs_exp]
  calc Real.exp (cθ θ * r) * |h (ell θ (Yplus θ f Y r ω))| ≤ Real.exp (cθ θ * r) * 1 :=
        mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
    _ ≤ Real.exp (cθ θ * T) := by
        rw [mul_one]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hr) hc)

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
