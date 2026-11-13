module

public import BlockBand.Critical.Entire.RandomEntire

/-!
# The entire law: Montel's theorem on `ℂ^m` and a tightness criterion

* `norm_fderiv_le_of_forall_closedBall_norm_le`: Cauchy estimate `‖Df(z)‖ ≤ C/R` (one-variable
  Cauchy estimate on each complex line), any complex normed space;
* `differentiable_of_tendstoLocallyUniformly`, `isClosed_setOf_differentiable`: locally uniform
  limits of entire functions are entire (the estimate makes the derivatives locally uniformly
  Cauchy; Mathlib's `hasFDerivAt_of_tendstoUniformlyOn`), proper complex normed spaces;
* `isCompact_boundedEntireSet`: **Montel** — entire functions bounded by `M r` on every closed
  ball of radius `r` form a compact set (Arzelà–Ascoli, `isCompact_closure_of_isClosedEmbedding`,
  equicontinuity from the Cauchy estimate and the mean value inequality);
* `isTightMeasureSet_of_forall_exists_bound`: a family of measures on `EntireFunction m` is tight
  if the sup of `‖F‖` on each closed ball is bounded in probability uniformly in the family.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open Filter Topology Metric Set MeasureTheory
open BlockBand.Critical.Entire
open scoped ENNReal NNReal Uniformity

section Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Cauchy estimate for the Fréchet derivative** of an entire function on a complex normed
space: if `‖f‖ ≤ C` on the closed ball of radius `R > 0` about `z`, then `‖Df(z)‖ ≤ C / R`
(one-variable Cauchy estimate on each complex line `t ↦ z + t v`). -/
theorem norm_fderiv_le_of_forall_closedBall_norm_le {f : E → ℂ} (hf : Differentiable ℂ f)
    {z : E} {R C : ℝ} (hR : 0 < R) (hC : ∀ w ∈ closedBall z R, ‖f w‖ ≤ C) :
    ‖fderiv ℂ f z‖ ≤ C / R := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z (mem_closedBall_self hR.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC0 hR.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set g : ℂ → ℂ := fun t => f (z + t • v)
  have hline : ∀ t : ℂ, HasDerivAt (fun t : ℂ => z + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hg : Differentiable ℂ g := fun t => (hf _).comp t (hline t).differentiableAt
  have hderiv : deriv g 0 = fderiv ℂ f z v := by
    have h := (hf (z + (0 : ℂ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hline 0)
    simp only [zero_smul, add_zero] at h
    exact h.deriv
  set ρ : ℝ := R / ‖v‖
  have hρ : 0 < ρ := div_pos hR hv'
  have hbd : ∀ t ∈ sphere (0 : ℂ) ρ, ‖g t‖ ≤ C := by
    intro t ht
    rw [mem_sphere_zero_iff_norm] at ht
    refine hC _ ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, ht]
    simp only [ρ]
    rw [div_mul_cancel₀ _ hv'.ne']
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hg.diffContOnCl hbd
  rw [hderiv] at h
  calc ‖fderiv ℂ f z v‖ ≤ C / ρ := h
    _ = C / R * ‖v‖ := by simp only [ρ]; field_simp

/-- **Locally uniform limits of entire functions are entire** (complex normed space, proper):
the Cauchy estimate makes the derivatives locally uniformly Cauchy, and Mathlib's
`hasFDerivAt_of_tendstoUniformlyOn` identifies the derivative of the limit. -/
theorem differentiable_of_tendstoLocallyUniformly [ProperSpace E] {ι : Type*} {l : Filter ι}
    [l.NeBot] {F : ι → E → ℂ} {f : E → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (h : TendstoLocallyUniformly F f l) : Differentiable ℂ f := by
  intro x
  set s : Set E := ball x 1
  have hK : TendstoUniformlyOn F f l (closedBall x 2) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp h) _ (isCompact_closedBall x 2)
  have hKc := hK.uniformCauchySeqOn
  have hcauchy : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) l s := by
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
    have h2 : {p : ℂ × ℂ | dist p.1 p.2 < ε / 2} ∈ 𝓤 ℂ :=
      Metric.dist_mem_uniformity (half_pos hε)
    filter_upwards [hKc _ h2] with n hn y hy
    apply hεu
    have hball : ∀ w ∈ closedBall y 1, ‖(F n.1 - F n.2) w‖ ≤ ε / 2 := by
      intro w hw
      have hwK : w ∈ closedBall x 2 := by
        rw [mem_closedBall] at hw ⊢
        have : dist y x < 1 := hy
        linarith [dist_triangle w y x]
      have := hn w hwK
      rw [Pi.sub_apply, ← dist_eq_norm]
      exact this.le
    have hest := norm_fderiv_le_of_forall_closedBall_norm_le ((hF n.1).sub (hF n.2))
      one_pos hball
    rw [fderiv_sub (hF n.1 y) (hF n.2 y), div_one] at hest
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hest (half_lt_self hε)
  have hlim : ∀ y ∈ s, ∃ L, Tendsto (fun n => fderiv ℂ (F n) y) l (𝓝 L) := fun y hy =>
    CompleteSpace.complete (hcauchy.cauchy_map hy)
  set g' : E → E →L[ℂ] ℂ := fun y => limUnder l (fun n => fderiv ℂ (F n) y)
  have hg' : TendstoUniformlyOn (fun n => fderiv ℂ (F n)) g' l s :=
    hcauchy.tendstoUniformlyOn_of_tendsto fun y hy => tendsto_nhds_limUnder (hlim y hy)
  exact (hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hg'
    (fun n y _ => (hF n y).hasFDerivAt) (fun y _ => (h.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ y))
    (mem_ball_self one_pos)).differentiableAt

/-- Entire functions form a closed subset of `C(E, ℂ)` (compact-open topology). -/
theorem isClosed_setOf_differentiable [ProperSpace E] :
    IsClosed {f : C(E, ℂ) | Differentiable ℂ ⇑f} := by
  refine isClosed_of_closure_subset fun f hf => ?_
  set D := {f : C(E, ℂ) | Differentiable ℂ ⇑f}
  have : (comap ((↑) : D → C(E, ℂ)) (𝓝 f)).NeBot := mem_closure_iff_comap_neBot.mp hf
  have ht : Tendsto ((↑) : D → C(E, ℂ)) (comap ((↑) : D → C(E, ℂ)) (𝓝 f)) (𝓝 f) :=
    tendsto_comap
  exact differentiable_of_tendstoLocallyUniformly (F := fun n : D => ⇑(n : C(E, ℂ)))
    (fun n => n.2) (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht)

end Cauchy

section Montel

variable {m : ℕ}

/-- Entire functions bounded by `M r` on the closed ball of radius `r`, for every `r : ℕ`
(sup norm on `ℂ^m`). -/
def boundedEntireSet (m : ℕ) (M : ℕ → ℝ) : Set (EntireFunction m) :=
  {F | ∀ r : ℕ, ∀ z ∈ closedBall (0 : Fin m → ℂ) r, ‖F z‖ ≤ M r}

/-- The same set inside `C(ℂ^m, ℂ)`. -/
def boundedEntireCM (m : ℕ) (M : ℕ → ℝ) : Set C(Fin m → ℂ, ℂ) :=
  {f | Differentiable ℂ ⇑f ∧ ∀ r : ℕ, ∀ z ∈ closedBall (0 : Fin m → ℂ) r, ‖f z‖ ≤ M r}

theorem isClosed_boundedEntireCM (M : ℕ → ℝ) : IsClosed (boundedEntireCM m M) := by
  have h : {f : C(Fin m → ℂ, ℂ) | ∀ r : ℕ, ∀ z ∈ closedBall (0 : Fin m → ℂ) r, ‖f z‖ ≤ M r} =
      ⋂ r : ℕ, ⋂ z ∈ closedBall (0 : Fin m → ℂ) r, {f : C(Fin m → ℂ, ℂ) | ‖f z‖ ≤ M r} := by
    ext f; simp
  have hB : IsClosed {f : C(Fin m → ℂ, ℂ) |
      ∀ r : ℕ, ∀ z ∈ closedBall (0 : Fin m → ℂ) r, ‖f z‖ ≤ M r} := by
    rw [h]
    exact isClosed_iInter fun r => isClosed_biInter fun z _ =>
      isClosed_le (continuous_eval_const z).norm continuous_const
  exact isClosed_setOf_differentiable.inter hB

/-- Uniform local bounds give equicontinuity (Cauchy estimate and the mean value inequality). -/
theorem equicontinuous_boundedEntireCM (M : ℕ → ℝ) :
    Equicontinuous (fun f : boundedEntireCM m M => ⇑(f : C(Fin m → ℂ, ℂ))) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  set r : ℕ := ⌈‖x‖⌉₊ + 2
  set C : ℝ := max (M r) 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨min 1 (ε / (C + 1)), by positivity, fun y hy f => ?_⟩
  have hbound : ∀ w ∈ ball x 1, ‖fderiv ℂ (⇑(f : C(Fin m → ℂ, ℂ))) w‖ ≤ C := by
    intro w hw
    have h := norm_fderiv_le_of_forall_closedBall_norm_le f.2.1 one_pos (z := w) (C := C)
      (fun u hu => ?_)
    · simpa using h
    have hu0 : u ∈ closedBall (0 : Fin m → ℂ) r := by
      rw [mem_closedBall]
      have h1 : dist u w ≤ 1 := hu
      have h2 : dist w x < 1 := hw
      have h3 : dist x 0 ≤ ⌈‖x‖⌉₊ := by rw [dist_zero_right]; exact Nat.le_ceil _
      have h4 := dist_triangle u w 0
      have h5 := dist_triangle w x 0
      simp only [r]; push_cast; linarith
    exact (f.2.2 r u hu0).trans (le_max_left _ _)
  have hy1 : y ∈ ball x 1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (fun w _ => f.2.1 w) hbound
    (convex_ball x 1) (mem_ball_self one_pos) hy1
  rw [dist_eq_norm, norm_sub_rev]
  have hyx : ‖y - x‖ < ε / (C + 1) := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_right _ _)
  calc _ ≤ C * ‖y - x‖ := hmv
    _ ≤ C * (ε / (C + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- **Montel (Arzelà–Ascoli form)**: the locally bounded entire functions form a compact subset
of `C(ℂ^m, ℂ)`. -/
theorem isCompact_boundedEntireCM (M : ℕ → ℝ) : IsCompact (boundedEntireCM m M) := by
  have hemb : IsClosedEmbedding (UniformOnFun.ofFun {K : Set (Fin m → ℂ) | IsCompact K} ∘
      (DFunLike.coe : C(Fin m → ℂ, ℂ) → (Fin m → ℂ) → ℂ)) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    have : range (UniformOnFun.ofFun {K : Set (Fin m → ℂ) | IsCompact K} ∘
        (DFunLike.coe : C(Fin m → ℂ, ℂ) → (Fin m → ℂ) → ℂ)) =
        {f | Continuous (UniformOnFun.toFun _ f)} :=
      ContinuousMap.range_toUniformOnFunIsCompact
    rw [this]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  have hcl := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hemb
    (s := boundedEntireCM m M)
    (fun K _ => (equicontinuous_boundedEntireCM M).equicontinuousOn K)
    (fun K _ x _ => ⟨closedBall 0 (M ⌈‖x‖⌉₊), isCompact_closedBall _ _, fun f hf => by
      rw [mem_closedBall, dist_zero_right]
      exact hf.2 _ x (by rw [mem_closedBall, dist_zero_right]; exact Nat.le_ceil _)⟩)
  rwa [(isClosed_boundedEntireCM M).closure_eq] at hcl

/-- **Montel's theorem on `ℂ^m`**: a set of entire functions bounded by `M r` on each closed
ball of radius `r` is compact in `EntireFunction m` (compact-open topology). -/
theorem isCompact_boundedEntireSet (M : ℕ → ℝ) : IsCompact (boundedEntireSet m M) := by
  rw [EntireFunction.isEmbedding_toContinuousMap.isInducing.isCompact_iff]
  convert isCompact_boundedEntireCM (m := m) M using 1
  ext f
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F.2, hF⟩
  · rintro ⟨hd, hb⟩
    exact ⟨⟨f, hd⟩, hb, rfl⟩

/-- **Tightness criterion in `EntireFunction m`** (Montel + countable subadditivity): a family
of measures is tight as soon as, for every radius `r` and every `ε > 0`, the sup of `‖F‖` on the
closed ball of radius `r` exceeds some level `M` with mass at most `ε`, uniformly in the family. -/
theorem isTightMeasureSet_of_forall_exists_bound {S : Set (Measure (EntireFunction m))}
    (h : ∀ (r : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ M : ℝ, ∀ μ ∈ S,
      μ {F | ∃ z ∈ closedBall (0 : Fin m → ℂ) r, M < ‖F z‖} ≤ ε) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose M hM using fun r => h r (δ r) (ENNReal.coe_pos.mpr (hδ r))
  refine ⟨boundedEntireSet m M, isCompact_boundedEntireSet M, fun μ hμ => ?_⟩
  have hsub : (boundedEntireSet m M)ᶜ ⊆
      ⋃ r : ℕ, {F : EntireFunction m | ∃ z ∈ closedBall (0 : Fin m → ℂ) r, M r < ‖F z‖} := by
    intro F hF
    simp only [boundedEntireSet, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hF
    obtain ⟨r, z, hz, hlt⟩ := hF
    exact mem_iUnion.mpr ⟨r, z, hz, hlt⟩
  calc μ (boundedEntireSet m M)ᶜ ≤ μ (⋃ r : ℕ, {F : EntireFunction m |
        ∃ z ∈ closedBall (0 : Fin m → ℂ) r, M r < ‖F z‖}) := measure_mono hsub
    _ ≤ ∑' r : ℕ, μ {F : EntireFunction m | ∃ z ∈ closedBall (0 : Fin m → ℂ) r, M r < ‖F z‖} :=
      measure_iUnion_le _
    _ ≤ ∑' r : ℕ, (δ r : ℝ≥0∞) := ENNReal.tsum_le_tsum fun r => hM r μ hμ
    _ ≤ ε := hsum.le

end Montel

end BlockBand.Critical.EntireLaw
