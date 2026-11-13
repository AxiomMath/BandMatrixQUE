module
public import BlockBand.Diffusion.Duality.Main
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Support
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Backward time mollification

Lebesgue measure on `ℝ` (the time shift `r`). `E` is a proper real normed space (the space
variable, later `Fin d → ℝ`), `F` a real Banach space (the values: `ℝ`, or the spaces of first
and second spatial derivatives).

* `tconv ψ g (s, x) = ∫ ψ(r) • g(s + r, x) dr`: time convolution with a kernel `ψ` supported in
  `[-ε, 0]`, so only the times `[s - ε, s]` enter.
* `continuousOn_tconv`: if `g` is continuous on `(a, b] × O` (`O` open), `tconv ψ g` is
  continuous on `(a + ε, b] × O`; `continuousOn_tconv_Ioo`: the same with `(a, b)`.
* `hasFDerivAt_tconv`: if `ψ ∈ C¹` and `g` has a spatial derivative `g'` (`HasFDerivAt` in `x`)
  with `g, g'` continuous on `(a, b) × O`, then on `(a + ε, b) × O` the map `tconv ψ g` is
  (jointly) differentiable with derivative `tconvD ψ g g' = fst ⊗ tconv(-ψ') g + tconv ψ g' ∘ snd`
  (the time derivative falls on the kernel, the space derivative on `g`).
* `contDiffOn_one_tconv`, `contDiffOn_two_tconv`: `C¹` (resp. `C²`, for `ψ ∈ C²` and a second
  spatial derivative `g''`) on `(a + ε, b) × O`. No time regularity of `g` is used.
* `tconv_timeDeriv` (integration by parts in time): if `σ ↦ g(σ, x)` has a continuous
  derivative `gt` on `(a, b) × O`, then `tconv ψ gt = tconv (-ψ') g` on `(a + ε, b) × O`.
* `IsBwdMollifier φ ε`: `φ ∈ C²`, `φ ≥ 0`, `∫ φ = 1`, `support φ ⊆ [-ε, 0]`;
  `isBwdMollifier_bwdMollifier`: Mathlib's normed bump `bwdMollifier ε` is one, for `ε > 0`.
* `IsBwdMollifier.abs_tconv_sub_le`, `abs_tconv_le_of_bound`: mollified values are averages
  (`|u_ε - c| ≤ η` if `|u - c| ≤ η` on the time window; `|u_ε| ≤ sup |u|` on `(a + ε, b] × O`).
* `tendstoLocallyUniformlyOn_tconv`: if `φ ε` is a backward mollifier for every `ε > 0` and `u`
  is continuous on `(a, b] × O`, then `tconv (φ ε) u → u` locally uniformly on `(a, b] × O` as
  `ε → 0⁺`.
-/

namespace BlockBand.Diffusion
open MeasureTheory Filter Topology Set Function
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Time convolution: `tconv ψ g (s, x) = ∫ ψ(r) • g(s + r, x) dr`. -/
def tconv (ψ : ℝ → ℝ) (g : ℝ × E → F) (p : ℝ × E) : F :=
  ∫ r, ψ r • g (p.1 + r, p.2)

/-!
### Kernels supported in `[-ε, 0]`
-/

section Kernel

variable {ψ : ℝ → ℝ} {ε : ℝ}

theorem eq_zero_of_support_subset (hs : support ψ ⊆ Icc (-ε) 0) {r : ℝ} (hr : r ∉ Icc (-ε) 0) :
    ψ r = 0 :=
  notMem_support.1 fun h => hr (hs h)

theorem tsupport_subset_of_support_subset (hs : support ψ ⊆ Icc (-ε) 0) :
    tsupport ψ ⊆ Icc (-ε) 0 :=
  closure_minimal hs isClosed_Icc

theorem support_deriv_subset_Icc (hs : support ψ ⊆ Icc (-ε) 0) :
    support (deriv ψ) ⊆ Icc (-ε) 0 :=
  support_deriv_subset.trans (tsupport_subset_of_support_subset hs)

theorem support_neg_deriv_subset_Icc (hs : support ψ ⊆ Icc (-ε) 0) :
    support (fun r => -deriv ψ r) ⊆ Icc (-ε) 0 := by
  rw [show (fun r => -deriv ψ r) = -deriv ψ from rfl, support_neg]
  exact support_deriv_subset_Icc hs

theorem hasCompactSupport_of_support_subset (hs : support ψ ⊆ Icc (-ε) 0) :
    HasCompactSupport ψ :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) (tsupport_subset_of_support_subset hs)

theorem exists_bound_kernel (hψ : Continuous ψ) (hs : support ψ ⊆ Icc (-ε) 0) :
    ∃ B, 0 ≤ B ∧ ∀ r, ‖ψ r‖ ≤ B := by
  obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support (hasCompactSupport_of_support_subset hs)
  exact ⟨max B 0, le_max_right _ _, fun r => (hB r).trans (le_max_left _ _)⟩

/-- A kernel times a function continuous on its support window is integrable. -/
theorem integrable_kernel_smul (hψ : Continuous ψ) (hs : support ψ ⊆ Icc (-ε) 0) {h : ℝ → F}
    (hh : ContinuousOn h (Icc (-ε) 0)) : Integrable (fun r => ψ r • h r) := by
  have hI : IntegrableOn (fun r => ψ r • h r) (Icc (-ε) 0) :=
    (hψ.continuousOn.smul hh).integrableOn_compact isCompact_Icc
  exact hI.integrable_of_forall_notMem_eq_zero fun r hr => by
    rw [eq_zero_of_support_subset hs hr, zero_smul]

end Kernel

/-!
### Windows
-/

theorem mem_Ioc_prod_of_shift {a b ε : ℝ} {O : Set E} {q : ℝ × E}
    (hq : q ∈ Ioc (a + ε) b ×ˢ O) {r : ℝ} (hr : r ∈ Icc (-ε) 0) :
    (q.1 + r, q.2) ∈ Ioc a b ×ˢ O :=
  ⟨⟨by linarith [hq.1.1, hr.1], by linarith [hq.1.2, hr.2]⟩, hq.2⟩

theorem mem_Ioo_prod_of_shift {a b ε : ℝ} {O : Set E} {q : ℝ × E}
    (hq : q ∈ Ioo (a + ε) b ×ˢ O) {r : ℝ} (hr : r ∈ Icc (-ε) 0) :
    (q.1 + r, q.2) ∈ Ioo a b ×ˢ O :=
  ⟨⟨by linarith [hq.1.1, hr.1], by linarith [hq.1.2, hr.2]⟩, hq.2⟩

/-- `tconv` in the variable `σ = s + r`. -/
theorem tconv_eq_integral_sub (ψ : ℝ → ℝ) (g : ℝ × E → F) (p : ℝ × E) :
    tconv ψ g p = ∫ σ, ψ (σ - p.1) • g (σ, p.2) := by
  rw [tconv, ← integral_sub_right_eq_self (fun r => ψ r • g (p.1 + r, p.2)) p.1]
  simp only [add_sub_cancel]

/-- `tconv` as an integral over a time window `[α, β] ⊇ [s - ε, s]`. -/
theorem tconv_eq_setIntegral {ψ : ℝ → ℝ} {ε : ℝ} (hs : support ψ ⊆ Icc (-ε) 0) (g : ℝ × E → F)
    {p : ℝ × E} {α β : ℝ} (hα : α ≤ p.1 - ε) (hβ : p.1 ≤ β) :
    tconv ψ g p = ∫ σ in Icc α β, ψ (σ - p.1) • g (σ, p.2) := by
  rw [tconv_eq_integral_sub, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro σ hσ
  rw [eq_zero_of_support_subset hs, zero_smul]
  intro h
  exact hσ ⟨by linarith [h.1], by linarith [h.2]⟩

/-!
### Continuity
-/

section Continuity

variable [NormedAddCommGroup E] [ProperSpace E] {ψ : ℝ → ℝ} {ε : ℝ}

/-- **Continuity of the time convolution** on `(a + ε, b] × O`. -/
theorem continuousOn_tconv (hψ : Continuous ψ) (hs : support ψ ⊆ Icc (-ε) 0) {a b : ℝ}
    {O : Set E} (hO : IsOpen O) {g : ℝ × E → F} (hg : ContinuousOn g (Ioc a b ×ˢ O)) :
    ContinuousOn (tconv ψ g) (Ioc (a + ε) b ×ˢ O) := by
  intro p hp
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hO p.2 hp.2
  set δ : ℝ := min (δ₀ / 2) ((p.1 - ε - a) / 2) with hδ
  have hpa : 0 < p.1 - ε - a := by linarith [hp.1.1]
  have hδ0 : 0 < δ := lt_min (half_pos hδ₀) (half_pos hpa)
  set K : Set (ℝ × E) := Icc (p.1 - ε - δ) b ×ˢ Metric.closedBall p.2 δ with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKS : K ⊆ Ioc a b ×ˢ O := by
    rintro q ⟨hq1, hq2⟩
    refine ⟨⟨?_, hq1.2⟩, hball ?_⟩
    · have : δ ≤ (p.1 - ε - a) / 2 := min_le_right _ _
      linarith [hq1.1]
    · have : δ ≤ δ₀ / 2 := min_le_left _ _
      exact lt_of_le_of_lt (Metric.mem_closedBall.1 hq2) (by linarith)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hg.mono hKS)
  have hint : ∀ q ∈ Ioc (a + ε) b ×ˢ O, Integrable (fun r => ψ r • g (q.1 + r, q.2)) := by
    intro q hq
    refine integrable_kernel_smul hψ hs (hg.comp (by fun_prop) fun r hr => ?_)
    exact mem_Ioc_prod_of_shift hq hr
  have hbd : Integrable (fun r => ‖ψ r‖ * M) :=
    (hψ.norm.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset hs).norm).mul_const M
  refine continuousWithinAt_of_dominated (bound := fun r => ‖ψ r‖ * M) ?_ ?_ hbd ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq using (hint q hq).aestronglyMeasurable
  · have hnb : Metric.ball p δ ∈ 𝓝 p := Metric.ball_mem_nhds p hδ0
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnb] with q hq hqb
    refine Eventually.of_forall fun r => ?_
    by_cases hr : r ∈ Icc (-ε) 0
    · rw [norm_smul]
      refine mul_le_mul_of_nonneg_left (hM _ ?_) (norm_nonneg _)
      have hqb' : dist q p < δ := hqb
      rw [Prod.dist_eq] at hqb'
      have h1 : dist q.1 p.1 < δ := lt_of_le_of_lt (le_max_left _ _) hqb'
      have h2 : dist q.2 p.2 < δ := lt_of_le_of_lt (le_max_right _ _) hqb'
      rw [Real.dist_eq, abs_lt] at h1
      refine ⟨⟨by linarith [hr.1], by linarith [hr.2, hq.1.2]⟩, ?_⟩
      exact Metric.mem_closedBall.2 h2.le
    · rw [eq_zero_of_support_subset hs hr, zero_smul, norm_zero, norm_zero, zero_mul]
  · refine Eventually.of_forall fun r => ?_
    by_cases hr : r ∈ Icc (-ε) 0
    · refine ContinuousWithinAt.const_smul ?_ (ψ r)
      have hc : Continuous fun q : ℝ × E => (q.1 + r, q.2) := by fun_prop
      exact ContinuousWithinAt.comp (f := fun q : ℝ × E => (q.1 + r, q.2)) (x := p)
        (hg _ (mem_Ioc_prod_of_shift hp hr)) hc.continuousWithinAt
        fun q hq => mem_Ioc_prod_of_shift hq hr
    · simp only [eq_zero_of_support_subset hs hr, zero_smul]
      exact continuousWithinAt_const

/-- **Continuity of the time convolution** on `(a + ε, b) × O`. -/
theorem continuousOn_tconv_Ioo (hψ : Continuous ψ) (hs : support ψ ⊆ Icc (-ε) 0) {a b : ℝ}
    {O : Set E} (hO : IsOpen O) {g : ℝ × E → F} (hg : ContinuousOn g (Ioo a b ×ˢ O)) :
    ContinuousOn (tconv ψ g) (Ioo (a + ε) b ×ˢ O) := by
  intro p hp
  obtain ⟨b', hb'1, hb'2⟩ := exists_between hp.1.2
  have hsub : Ioc a b' ×ˢ O ⊆ Ioo a b ×ˢ O :=
    prod_mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hb'2⟩) le_rfl
  have h := continuousOn_tconv hψ hs hO (hg.mono hsub) p ⟨⟨hp.1.1, hb'1.le⟩, hp.2⟩
  have hn : Ioc (a + ε) b' ×ˢ O ∈ 𝓝 p := by
    refine prod_mem_nhds ?_ (hO.mem_nhds hp.2)
    exact Ioc_mem_nhds hp.1.1 hb'1
  exact (h.continuousAt hn).continuousWithinAt

end Continuity

/-!
### Differentiation under the integral
-/

section Deriv

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : ℝ → ℝ} {ε : ℝ}

/-- The derivative of `tconv ψ g` (`g'` the spatial derivative of `g`):
`(τ, v) ↦ τ • tconv (-ψ') g + tconv ψ g' v`. -/
def tconvD (ψ : ℝ → ℝ) (g : ℝ × E → F) (g' : ℝ × E → E →L[ℝ] F) (p : ℝ × E) :
    ℝ × E →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ E).smulRight (tconv (fun r => -deriv ψ r) g p) +
    (tconv ψ g' p).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem tconvD_apply (ψ : ℝ → ℝ) (g : ℝ × E → F) (g' : ℝ × E → E →L[ℝ] F)
    (p v : ℝ × E) :
    tconvD ψ g g' p v = v.1 • tconv (fun r => -deriv ψ r) g p + tconv ψ g' p v.2 := by
  simp [tconvD]

/-- `tconvD` as a sum of two continuous linear images. -/
theorem tconvD_eq (ψ : ℝ → ℝ) (g : ℝ × E → F) (g' : ℝ × E → E →L[ℝ] F) :
    tconvD ψ g g' = fun p =>
      ContinuousLinearMap.smulRightL ℝ (ℝ × E) F (ContinuousLinearMap.fst ℝ ℝ E)
          (tconv (fun r => -deriv ψ r) g p) +
        (tconv ψ g' p).comp (ContinuousLinearMap.snd ℝ ℝ E) := by
  funext p; ext v <;> simp [tconvD]

variable [ProperSpace E]

/-- **Differentiation of the time convolution.** -/
theorem hasFDerivAt_tconv (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0) {a b : ℝ}
    {O : Set E} (hO : IsOpen O) {g : ℝ × E → F} {g' : ℝ × E → E →L[ℝ] F}
    (hg : ContinuousOn g (Ioo a b ×ˢ O)) (hg'c : ContinuousOn g' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2) {p : ℝ × E}
    (hp : p ∈ Ioo (a + ε) b ×ˢ O) : HasFDerivAt (tconv ψ g) (tconvD ψ g g' p) p := by
  have hψc : Continuous ψ := hψ.continuous
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.differentiable (by norm_num)) x).hasDerivAt
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hO p.2 hp.2
  have hpa : 0 < p.1 - ε - a := by linarith [hp.1.1]
  have hpb : 0 < b - p.1 := by linarith [hp.1.2]
  set δ : ℝ := min (δ₀ / 2) (min ((p.1 - ε - a) / 2) ((b - p.1) / 2)) with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hδ₀) (lt_min (half_pos hpa) (half_pos hpb))
  have hδ1 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ2 : δ ≤ (p.1 - ε - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (b - p.1) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set α : ℝ := p.1 - ε - δ with hα
  set β : ℝ := p.1 + δ with hβ
  set K : Set (ℝ × E) := Icc α β ×ˢ Metric.closedBall p.2 δ with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKS : K ⊆ Ioo a b ×ˢ O := by
    rintro q ⟨hq1, hq2⟩
    refine ⟨⟨by linarith [hq1.1], by linarith [hq1.2]⟩, hball ?_⟩
    exact lt_of_le_of_lt (Metric.mem_closedBall.1 hq2) (by linarith)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hg.mono hKS)
  obtain ⟨M', hM'⟩ := hKc.exists_bound_of_continuousOn (hg'c.mono hKS)
  obtain ⟨B, hB0, hB⟩ := exists_bound_kernel hψc hs
  obtain ⟨B', hB'0, hB'⟩ := exists_bound_kernel hψ'c (support_deriv_subset_Icc hs)
  set N : Set (ℝ × E) := Metric.ball p δ with hN
  have hNm : ∀ q ∈ N, |q.1 - p.1| < δ ∧ dist q.2 p.2 < δ := fun q hq => by
    have hq' : dist q p < δ := hq
    rw [Prod.dist_eq] at hq'
    exact ⟨by rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) hq',
      lt_of_le_of_lt (le_max_right _ _) hq'⟩
  have hNK : ∀ q ∈ N, ∀ σ ∈ Icc α β, (σ, q.2) ∈ K := fun q hq σ hσ =>
    ⟨hσ, Metric.mem_closedBall.2 (hNm q hq).2.le⟩
  have hpN : p ∈ N := Metric.mem_ball_self hδ0
  -- the local representation
  have hloc : ∀ q ∈ N, tconv ψ g q = ∫ σ in Icc α β, ψ (σ - q.1) • g (σ, q.2) := by
    intro q hq
    have h1 := (hNm q hq).1
    rw [abs_lt] at h1
    exact tconv_eq_setIntegral hs g (by linarith) (by linarith)
  set F' : ℝ × E → ℝ → ℝ × E →L[ℝ] F := fun q σ =>
    ψ (σ - q.1) • (g' (σ, q.2)).comp (ContinuousLinearMap.snd ℝ ℝ E) +
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight (-deriv ψ (σ - q.1) • g (σ, q.2)) with hF'
  have hcg : ∀ q ∈ N, ContinuousOn (fun σ => g (σ, q.2)) (Icc α β) := fun q hq =>
    hg.comp (by fun_prop) fun σ hσ => hKS (hNK q hq σ hσ)
  have hcg' : ∀ q ∈ N, ContinuousOn (fun σ => g' (σ, q.2)) (Icc α β) := fun q hq =>
    hg'c.comp (by fun_prop) fun σ hσ => hKS (hNK q hq σ hσ)
  have hFc : ∀ q ∈ N, ContinuousOn (fun σ => ψ (σ - q.1) • g (σ, q.2)) (Icc α β) :=
    fun q hq => ((hψc.comp (by fun_prop)).continuousOn).smul (hcg q hq)
  have hF'c : ContinuousOn (F' p) (Icc α β) := by
    refine ContinuousOn.add ?_ ?_
    · exact ((hψc.comp (by fun_prop)).continuousOn).smul
        ((hcg' p hpN).clm_comp continuousOn_const)
    · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
        (ContinuousLinearMap.fst ℝ ℝ E)).continuous.comp_continuousOn
        (((hψ'c.comp (by fun_prop)).neg.continuousOn).smul (hcg p hpN))
  have hdiff : ∀ σ ∈ Icc α β, ∀ q ∈ N,
      HasFDerivAt (fun q : ℝ × E => ψ (σ - q.1) • g (σ, q.2)) (F' q σ) q := by
    intro σ hσ q hq
    have hc : HasFDerivAt (fun q : ℝ × E => ψ (σ - q.1))
        (deriv ψ (σ - q.1) • -ContinuousLinearMap.fst ℝ ℝ E) q :=
      (hψd (σ - q.1)).comp_hasFDerivAt q ((hasFDerivAt_fst).const_sub σ)
    have h0 : HasFDerivAt (fun y => g (σ, y)) (g' (σ, q.2)) q.2 :=
      hg' (σ, q.2) (hKS (hNK q hq σ hσ))
    have hf : HasFDerivAt (fun q : ℝ × E => g (σ, q.2))
        ((g' (σ, q.2)).comp (ContinuousLinearMap.snd ℝ ℝ E)) q :=
      h0.comp q hasFDerivAt_snd
    refine (hc.fun_smul hf).congr_fderiv ?_
    ext v <;> simp [hF', smul_smul, mul_comm]
  have hbound : ∀ σ ∈ Icc α β, ∀ q ∈ N, ‖F' q σ‖ ≤ B * M' + M * B' := by
    intro σ hσ q hq
    have hKq := hNK q hq σ hσ
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]
      refine mul_le_mul (hB _) ?_ (norm_nonneg _) hB0
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      calc ‖g' (σ, q.2)‖ * ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ M' * 1 :=
            mul_le_mul (hM' _ hKq) (ContinuousLinearMap.norm_snd_le ℝ ℝ E) (norm_nonneg _)
              ((norm_nonneg _).trans (hM' _ hKq))
        _ = M' := mul_one _
    · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_neg]
      calc ‖ContinuousLinearMap.fst ℝ ℝ E‖ * (‖deriv ψ (σ - q.1)‖ * ‖g (σ, q.2)‖)
          ≤ 1 * (B' * M) := by
            refine mul_le_mul (ContinuousLinearMap.norm_fst_le ℝ ℝ E) ?_ (by positivity) zero_le_one
            exact mul_le_mul (hB' _) (hM _ hKq) (norm_nonneg _) hB'0
        _ = M * B' := by ring
  have hmain : HasFDerivAt (fun q => ∫ σ in Icc α β, ψ (σ - q.1) • g (σ, q.2))
      (∫ σ in Icc α β, F' p σ) p := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := N)
      (bound := fun _ => B * M' + M * B') (Metric.ball_mem_nhds p hδ0) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds p hδ0] with q hq
      exact (hFc q hq).aestronglyMeasurable measurableSet_Icc
    · exact (hFc p hpN).integrableOn_compact isCompact_Icc
    · exact hF'c.aestronglyMeasurable measurableSet_Icc
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hbound)
    · exact integrable_const _
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hdiff)
  -- identify the derivative
  have hF'i : Integrable (F' p) (volume.restrict (Icc α β)) :=
    hF'c.integrableOn_compact isCompact_Icc
  have heq : ∫ σ in Icc α β, F' p σ = tconvD ψ g g' p := by
    have h1 : α ≤ p.1 - ε := by linarith
    have h2 : p.1 ≤ β := by linarith
    have hi1 : IntegrableOn (fun σ => (-deriv ψ (σ - p.1)) • g (σ, p.2)) (Icc α β) :=
      (((hψ'c.comp (by fun_prop)).neg.continuousOn).smul (hcg p hpN)).integrableOn_compact
        isCompact_Icc
    have hi2 : IntegrableOn (fun σ => ψ (σ - p.1) • g' (σ, p.2)) (Icc α β) :=
      (((hψc.comp (by fun_prop)).continuousOn).smul (hcg' p hpN)).integrableOn_compact
        isCompact_Icc
    have hi3 : ∀ v : E, IntegrableOn (fun σ => ψ (σ - p.1) • g' (σ, p.2) v) (Icc α β) :=
      fun v => (((hψc.comp (by fun_prop)).continuousOn).smul
        ((hcg' p hpN).clm_apply continuousOn_const)).integrableOn_compact isCompact_Icc
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.integral_apply hF'i, tconvD_apply,
      tconv_eq_setIntegral (support_neg_deriv_subset_Icc hs) g h1 h2,
      tconv_eq_setIntegral hs g' h1 h2, ContinuousLinearMap.integral_apply hi2, ← integral_smul]
    have hA : IntegrableOn (fun σ => v.1 • -deriv ψ (σ - p.1) • g (σ, p.2)) (Icc α β) :=
      hi1.smul v.1
    have hB : IntegrableOn (fun σ => (ψ (σ - p.1) • g' (σ, p.2)) v.2) (Icc α β) := by
      simpa only [_root_.smul_apply] using hi3 v.2
    rw [← integral_add hA hB]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [hF', _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rw [add_comm]
  rw [← heq]
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds p hδ0] with q hq using hloc q hq

end Deriv

section Deriv2

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {ψ : ℝ → ℝ} {ε : ℝ}
  {a b : ℝ} {O : Set E} {g : ℝ × E → F} {g' : ℝ × E → E →L[ℝ] F}

theorem differentiableOn_tconv (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2) :
    DifferentiableOn ℝ (tconv ψ g) (Ioo (a + ε) b ×ˢ O) := fun _ hp =>
  (hasFDerivAt_tconv hψ hs hO hg hg'c hg' hp).differentiableAt.differentiableWithinAt

theorem fderiv_tconv_eqOn (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2) :
    EqOn (fderiv ℝ (tconv ψ g)) (tconvD ψ g g') (Ioo (a + ε) b ×ˢ O) := fun _ hp =>
  (hasFDerivAt_tconv hψ hs hO hg hg'c hg' hp).fderiv

theorem continuousOn_tconvD (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O)) :
    ContinuousOn (tconvD ψ g g') (Ioo (a + ε) b ×ˢ O) := by
  rw [tconvD_eq]
  refine ContinuousOn.add ?_ ?_
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
      (ContinuousLinearMap.fst ℝ ℝ E)).continuous.comp_continuousOn
      (continuousOn_tconv_Ioo (hψ.continuous_deriv (by norm_num)).neg
        (support_neg_deriv_subset_Icc hs) hO hg)
  · exact (continuousOn_tconv_Ioo hψ.continuous hs hO hg'c).clm_comp continuousOn_const

/-- **`C¹` regularity of the time convolution** (no time regularity of `g`). -/
theorem contDiffOn_one_tconv (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2) :
    ContDiffOn ℝ 1 (tconv ψ g) (Ioo (a + ε) b ×ˢ O) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioo.prod hO)]
  refine ⟨differentiableOn_tconv hψ hs hO hg hg'c hg', by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (continuousOn_tconvD hψ hs hO hg hg'c).congr (fderiv_tconv_eqOn hψ hs hO hg hg'c hg')

theorem contDiff_one_neg_deriv (hψ : ContDiff ℝ 2 ψ) : ContDiff ℝ 1 fun r => -deriv ψ r :=
  (hψ.iterate_deriv' 1 1).neg

/-- **`C²` regularity of the time convolution**: `ψ ∈ C²`, and `g` has continuous first and
second spatial derivatives `g'`, `g''` on `(a, b) × O`. -/
theorem contDiffOn_two_tconv (hψ : ContDiff ℝ 2 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) {g'' : ℝ × E → E →L[ℝ] E →L[ℝ] F} (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O)) (hg''c : ContinuousOn g'' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2)
    (hg'' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g' (p.1, y)) (g'' p) p.2) :
    ContDiffOn ℝ 2 (tconv ψ g) (Ioo (a + ε) b ×ˢ O) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioo.prod hO)]
  refine ⟨differentiableOn_tconv hψ1 hs hO hg hg'c hg', by simp, ?_⟩
  refine ContDiffOn.congr ?_ (fderiv_tconv_eqOn hψ1 hs hO hg hg'c hg')
  rw [tconvD_eq]
  refine ContDiffOn.add ?_ ?_
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
      (ContinuousLinearMap.fst ℝ ℝ E)).contDiff.comp_contDiffOn
      (contDiffOn_one_tconv (contDiff_one_neg_deriv hψ) (support_neg_deriv_subset_Icc hs) hO hg
        hg'c hg')
  · exact (contDiffOn_one_tconv hψ1 hs hO hg'c hg''c hg'').clm_comp contDiffOn_const

theorem fderiv_tconv_apply (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2) {p : ℝ × E}
    (hp : p ∈ Ioo (a + ε) b ×ˢ O) (v : ℝ × E) :
    fderiv ℝ (tconv ψ g) p v = v.1 • tconv (fun r => -deriv ψ r) g p + tconv ψ g' p v.2 := by
  rw [fderiv_tconv_eqOn hψ hs hO hg hg'c hg' hp, tconvD_apply]

/-- The pure spatial second derivative of the time convolution. -/
theorem fderiv_fderiv_tconv_apply (hψ : ContDiff ℝ 2 ψ) (hs : support ψ ⊆ Icc (-ε) 0)
    (hO : IsOpen O) {g'' : ℝ × E → E →L[ℝ] E →L[ℝ] F} (hg : ContinuousOn g (Ioo a b ×ˢ O))
    (hg'c : ContinuousOn g' (Ioo a b ×ˢ O)) (hg''c : ContinuousOn g'' (Ioo a b ×ˢ O))
    (hg' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g (p.1, y)) (g' p) p.2)
    (hg'' : ∀ p ∈ Ioo a b ×ˢ O, HasFDerivAt (fun y => g' (p.1, y)) (g'' p) p.2) {p : ℝ × E}
    (hp : p ∈ Ioo (a + ε) b ×ˢ O) (v w : E) :
    fderiv ℝ (fderiv ℝ (tconv ψ g)) p (0, v) (0, w) = tconv ψ g'' p v w := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hW : IsOpen (Ioo (a + ε) b ×ˢ O) := isOpen_Ioo.prod hO
  have hev : fderiv ℝ (tconv ψ g) =ᶠ[𝓝 p] tconvD ψ g g' :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hp) (fderiv_tconv_eqOn hψ1 hs hO hg hg'c hg')
  have h1 := hasFDerivAt_tconv (contDiff_one_neg_deriv hψ) (support_neg_deriv_subset_Icc hs) hO
    hg hg'c hg' hp
  have h2 := hasFDerivAt_tconv hψ1 hs hO hg'c hg''c hg'' hp
  have hD : HasFDerivAt (tconvD ψ g g')
      ((ContinuousLinearMap.smulRightL ℝ (ℝ × E) F (ContinuousLinearMap.fst ℝ ℝ E)).comp
          (tconvD (fun r => -deriv ψ r) g g' p) +
        ((ContinuousLinearMap.compL ℝ (ℝ × E) E F).flip (ContinuousLinearMap.snd ℝ ℝ E)).comp
          (tconvD ψ g' g'' p)) p := by
    rw [tconvD_eq]
    exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × E) F
      (ContinuousLinearMap.fst ℝ ℝ E)).hasFDerivAt.comp p h1).add
      (((ContinuousLinearMap.compL ℝ (ℝ × E) E F).flip
        (ContinuousLinearMap.snd ℝ ℝ E)).hasFDerivAt.comp p h2)
  rw [hev.fderiv_eq, hD.fderiv]
  simp

end Deriv2

/-!
### Moving the time derivative onto the kernel
-/

section TimeDeriv

variable [TopologicalSpace E] [CompleteSpace F] {ψ : ℝ → ℝ} {ε a b : ℝ} {O : Set E}
  {g gt : ℝ × E → F}

/-- **Integration by parts in time.** If `σ ↦ g(σ, x)` has derivative `gt` (continuous) on
`(a, b) × O`, then `tconv ψ gt = tconv (-ψ') g` on `(a + ε, b) × O`. -/
theorem tconv_timeDeriv (hψ : ContDiff ℝ 1 ψ) (hs : support ψ ⊆ Icc (-ε) 0) (hε : 0 ≤ ε)
    (hgt : ∀ p ∈ Ioo a b ×ˢ O, HasDerivAt (fun σ => g (σ, p.2)) (gt p) p.1)
    (hgtc : ContinuousOn gt (Ioo a b ×ˢ O)) {p : ℝ × E} (hp : p ∈ Ioo (a + ε) b ×ˢ O) :
    tconv ψ gt p = tconv (fun r => -deriv ψ r) g p := by
  have hψc : Continuous ψ := hψ.continuous
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.differentiable (by norm_num)) x).hasDerivAt
  have hψ'c : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  have hpa : 0 < p.1 - ε - a := by linarith [hp.1.1]
  have hpb : 0 < b - p.1 := by linarith [hp.1.2]
  set δ : ℝ := min ((p.1 - ε - a) / 2) ((b - p.1) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hpa) (half_pos hpb)
  have hδ1 : δ ≤ (p.1 - ε - a) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (b - p.1) / 2 := min_le_right _ _
  have hmem : ∀ r ∈ Icc (-ε - δ) δ, (p.1 + r, p.2) ∈ Ioo a b ×ˢ O := fun r hr =>
    ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, hp.2⟩
  have h0 : ∀ r ∈ Icc (-ε - δ) δ, HasDerivAt (fun r => g (p.1 + r, p.2)) (gt (p.1 + r, p.2)) r :=
    fun r hr => by
      have h := hgt (p.1 + r, p.2) (hmem r hr)
      exact HasDerivAt.comp_const_add (f := fun σ => g (σ, p.2)) p.1 r h
  have hgc : ContinuousOn (fun r => g (p.1 + r, p.2)) (Icc (-ε - δ) δ) := fun r hr =>
    (h0 r hr).continuousAt.continuousWithinAt
  have hgtc' : ContinuousOn (fun r => gt (p.1 + r, p.2)) (Icc (-ε - δ) δ) :=
    hgtc.comp (by fun_prop) hmem
  have hsub : Icc (-ε) 0 ⊆ Icc (-ε - δ) δ := Icc_subset_Icc (by linarith) hδ0.le
  set f' : ℝ → F := fun r => ψ r • gt (p.1 + r, p.2) + deriv ψ r • g (p.1 + r, p.2) with hf'
  have hderiv : ∀ r ∈ uIcc (-ε - δ) δ,
      HasDerivAt (fun r => ψ r • g (p.1 + r, p.2)) (f' r) r := by
    intro r hr
    rw [uIcc_of_le (by linarith)] at hr
    exact (hψd r).smul (h0 r hr)
  have hf'c : ContinuousOn f' (Icc (-ε - δ) δ) :=
    (hψc.continuousOn.smul hgtc').add (hψ'c.continuousOn.smul hgc)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hf'c.intervalIntegrable_of_Icc (by linarith))
  have hzA : ψ (-ε - δ) = 0 := eq_zero_of_support_subset hs fun h => by linarith [h.1]
  have hzB : ψ δ = 0 := eq_zero_of_support_subset hs fun h => by linarith [h.2]
  rw [hzA, hzB, zero_smul, zero_smul, sub_zero,
    intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_integral_of_forall_compl_eq_zero] at hftc
  swap
  · intro r hr
    have hr' : r ∉ Icc (-ε) 0 := fun h => hr ⟨by linarith [h.1], by linarith [h.2]⟩
    have h1 : ψ r = 0 := eq_zero_of_support_subset hs hr'
    have h2 : deriv ψ r = 0 := eq_zero_of_support_subset (support_deriv_subset_Icc hs) hr'
    simp [hf', h1, h2]
  have hi1 : Integrable (fun r => ψ r • gt (p.1 + r, p.2)) :=
    integrable_kernel_smul hψc hs (hgtc'.mono hsub)
  have hi2 : Integrable (fun r => deriv ψ r • g (p.1 + r, p.2)) :=
    integrable_kernel_smul hψ'c (support_deriv_subset_Icc hs) (hgc.mono hsub)
  rw [hf', integral_add hi1 hi2] at hftc
  simp only [tconv, neg_smul, integral_neg]
  exact eq_neg_of_add_eq_zero_left hftc

end TimeDeriv

theorem tconv_clm_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (ψ : ℝ → ℝ)
    (g : ℝ × E → G →L[ℝ] F) (p : ℝ × E) (v : G)
    (hint : Integrable (fun r => ψ r • g (p.1 + r, p.2))) :
    tconv ψ g p v = tconv ψ (fun q => g q v) p := by
  rw [tconv, ContinuousLinearMap.integral_apply hint]
  simp [tconv]

/-!
### Backward mollifiers
-/

section Mollifier

variable [TopologicalSpace E]

/-- A backward mollifier at scale `ε`: `C²`, nonnegative, unit mass, supported in `[-ε, 0]`. -/
structure IsBwdMollifier (φ : ℝ → ℝ) (ε : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  nonneg : ∀ r, 0 ≤ φ r
  integral_eq_one : ∫ r, φ r = 1
  support_subset : support φ ⊆ Icc (-ε) 0

/-- Mathlib's smooth bump centred at `-ε/2`, with outer radius `ε/2`. -/
def bwdBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (-ε / 2 : ℝ) where
  rIn := ε / 4
  rOut := ε / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The normalized backward bump (zero for `ε ≤ 0`). -/
def bwdMollifier (ε : ℝ) : ℝ → ℝ :=
  if h : 0 < ε then (bwdBump ε h).normed volume else 0

theorem isBwdMollifier_bwdMollifier {ε : ℝ} (hε : 0 < ε) :
    IsBwdMollifier (bwdMollifier ε) ε := by
  simp only [bwdMollifier, hε, ↓reduceDIte]
  refine ⟨(bwdBump ε hε).contDiff_normed, (bwdBump ε hε).nonneg_normed,
    (bwdBump ε hε).integral_normed, ?_⟩
  rw [(bwdBump ε hε).support_normed_eq]
  intro r hr
  rw [Metric.mem_ball, Real.dist_eq, abs_lt, show (bwdBump ε hε).rOut = ε / 2 from rfl] at hr
  constructor <;> linarith [hr.1, hr.2]

namespace IsBwdMollifier

variable {φ : ℝ → ℝ} {ε : ℝ}

theorem continuous (h : IsBwdMollifier φ ε) : Continuous φ := h.contDiff.continuous

theorem integrable (h : IsBwdMollifier φ ε) : Integrable φ :=
  h.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset h.support_subset)

omit [TopologicalSpace E] in
/-- **Mollified values are averages.** -/
theorem abs_tconv_sub_le (h : IsBwdMollifier φ ε) {u : ℝ × E → ℝ} {p : ℝ × E}
    (hu : ContinuousOn (fun r => u (p.1 + r, p.2)) (Icc (-ε) 0)) {c η : ℝ}
    (hη : ∀ r ∈ Icc (-ε) 0, |u (p.1 + r, p.2) - c| ≤ η) : |tconv φ u p - c| ≤ η := by
  have hi : Integrable (fun r => φ r • u (p.1 + r, p.2)) :=
    integrable_kernel_smul h.continuous h.support_subset hu
  have hc : Integrable (fun r => φ r * c) := h.integrable.mul_const c
  have e : tconv φ u p - c = ∫ r, φ r * (u (p.1 + r, p.2) - c) := by
    have : ∫ r, φ r * (u (p.1 + r, p.2) - c) = tconv φ u p - ∫ r, φ r * c := by
      rw [tconv, ← integral_sub hi hc]
      congr 1; funext r; simp only [smul_eq_mul]; ring
    rw [this, integral_mul_const, h.integral_eq_one, one_mul]
  have hg : Integrable (fun r => φ r * η) := h.integrable.mul_const η
  have hb := norm_integral_le_of_norm_le (f := fun r => φ r * (u (p.1 + r, p.2) - c)) hg
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg r)]
      by_cases hr : r ∈ Icc (-ε) 0
      · exact mul_le_mul_of_nonneg_left (hη r hr) (h.nonneg r)
      · rw [eq_zero_of_support_subset h.support_subset hr, zero_mul, zero_mul])
  rw [integral_mul_const, h.integral_eq_one, one_mul, Real.norm_eq_abs] at hb
  rw [e]; exact hb

omit [TopologicalSpace E] in
theorem abs_tconv_le (h : IsBwdMollifier φ ε) {u : ℝ × E → ℝ} {p : ℝ × E}
    (hu : ContinuousOn (fun r => u (p.1 + r, p.2)) (Icc (-ε) 0)) {C : ℝ}
    (hC : ∀ r ∈ Icc (-ε) 0, |u (p.1 + r, p.2)| ≤ C) : |tconv φ u p| ≤ C := by
  simpa using h.abs_tconv_sub_le hu (c := 0) (by simpa using hC)

end IsBwdMollifier

/-- Mollified values are bounded by `sup |u|` on `(a, b] × O`. -/
theorem abs_tconv_le_of_bound {φ : ℝ → ℝ} {ε a b : ℝ} (hφ : IsBwdMollifier φ ε) {O : Set E}
    {u : ℝ × E → ℝ} (hu : ContinuousOn u (Ioc a b ×ˢ O)) {C : ℝ}
    (hC : ∀ p ∈ Ioc a b ×ˢ O, |u p| ≤ C) {p : ℝ × E} (hp : p ∈ Ioc (a + ε) b ×ˢ O) :
    |tconv φ u p| ≤ C :=
  hφ.abs_tconv_le (hu.comp (by fun_prop) fun r hr => mem_Ioc_prod_of_shift hp hr)
    fun r hr => hC _ (mem_Ioc_prod_of_shift hp hr)

end Mollifier

section Uniform

variable [PseudoMetricSpace E]

/-- **Locally uniform convergence** `u_ε → u` on `(a, b] × O` as `ε → 0⁺`. -/
theorem tendstoLocallyUniformlyOn_tconv {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ ε, 0 < ε → IsBwdMollifier (φ ε) ε) {a b : ℝ} {O : Set E} {u : ℝ × E → ℝ}
    (hu : ContinuousOn u (Ioc a b ×ˢ O)) :
    TendstoLocallyUniformlyOn (fun ε => tconv (φ ε) u) u (𝓝[>] 0) (Ioc a b ×ˢ O) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro η hη x hx
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hu x hx) (η / 4) (by positivity)
  have hxa : 0 < x.1 - a := by linarith [hx.1.1]
  set δ' : ℝ := min (δ / 2) ((x.1 - a) / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min (half_pos hδ) (half_pos hxa)
  have hδ'1 : δ' ≤ δ / 2 := min_le_left _ _
  have hδ'2 : δ' ≤ (x.1 - a) / 2 := min_le_right _ _
  refine ⟨Ioc a b ×ˢ O ∩ Metric.ball x δ',
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ'0)), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ'0] with ε hε y hy
  have hyx : dist y x < δ' := hy.2
  rw [Prod.dist_eq] at hyx
  have h1 : |y.1 - x.1| < δ' := by
    rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) hyx
  have h2 : dist y.2 x.2 < δ' := lt_of_le_of_lt (le_max_right _ _) hyx
  rw [abs_lt] at h1
  have hyS : y ∈ Ioc (a + ε) b ×ˢ O :=
    ⟨⟨by linarith [hε.2], hy.1.1.2⟩, hy.1.2⟩
  have hux : dist (u y) (u x) < η / 4 := hcont hy.1 (lt_of_lt_of_le hy.2 (by linarith))
  have hb := (hφ ε hε.1).abs_tconv_sub_le (c := u y) (η := η / 2)
    (hu.comp (by fun_prop) fun r hr => mem_Ioc_prod_of_shift hyS hr) fun r hr => by
      have hq := mem_Ioc_prod_of_shift hyS hr
      have hqx : dist (y.1 + r, y.2) x < δ := by
        rw [Prod.dist_eq, Real.dist_eq]
        refine max_lt ?_ (by linarith)
        rw [abs_lt]; constructor <;> linarith [hr.1, hr.2, hε.2]
      have := hcont hq hqx
      rw [Real.dist_eq] at this hux
      rw [abs_lt] at this hux
      rw [abs_le]
      constructor <;> linarith [this.1, this.2, hux.1, hux.2]
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end Uniform

end BlockBand.Diffusion
