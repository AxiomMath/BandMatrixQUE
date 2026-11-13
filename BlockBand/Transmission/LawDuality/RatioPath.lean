module

public import BlockBand.Transmission.LawDuality.RatioWeakGen
public import BlockBand.Transmission.Dual.Path

/-!
# `RatioDualityPrinciple`: `F` along a deletion path, and monotonicity

* `continuous_pathSum`: along a deletion path, `t ↦ Σ_{i < n_t} g(x_t(i), y_t(i))` is continuous
  for every `g` continuous on `{x > −1, y < 1}` with `g(0,0) = 0` (the deleted pair tends to the
  corner `(0,0)`). This generalizes `Dual.continuous_total` (`g(a,b) = a + b`).
* **`continuous_ratioPath`**: for every finite measure `ν`, the **full-level** process
  `t ↦ F_{Z_t}(ν)` (`F = 1` at level `0`) is continuous along every deletion path, across
  deletions. This is the corner continuity used to cross deletions in step (a3).
* **`transmissionRatio_le_pair`**: `F_{x,y}(ν) ≤ F_{a,b}(ν)` (one pair) when some pair has
  `x_{i₀} ≥ a ≥ 0`, `y_{i₀} ≥ b ≥ 0`. With the entrance of a single pair this gives the endpoint
  `r ↑ t` of step (e) on `{ζ > t}` without any uniformity of the entrance in `z`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- The open parameter set `{x > −1, y < 1}` of the kernels. -/
def kernelDom : Set (ℝ × ℝ) := {w | -1 < w.1 ∧ w.2 < 1}

theorem isOpen_kernelDom : IsOpen kernelDom :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_snd continuous_const)

section Path

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem mem_kernelDom_of_path (hP : IsDeletionPath n x y) (t : ℝ≥0) {i : ℕ} (hi : i < n t) :
    (x t i, y t i) ∈ kernelDom := by
  have h := hP.chamber t
  have h1 : 0 < x t i := h.2.2.1 ⟨i, hi⟩
  exact ⟨show -1 < x t i by linarith, (h.2.2.2 ⟨i, hi⟩).2⟩

/-- **Path sums of a corner-null `g` are continuous along deletion paths.** -/
theorem continuous_pathSum (hP : IsDeletionPath n x y) {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g kernelDom) (hg0 : g (0, 0) = 0) :
    Continuous fun t => ∑ i ∈ Finset.range (n t), g (x t i, y t i) := by
  have hgt : ∀ {t : ℝ≥0} {i : ℕ}, i < n t → ContinuousAt g (x t i, y t i) := fun {t i} hi =>
    hg.continuousAt (isOpen_kernelDom.mem_nhds (mem_kernelDom_of_path hP t hi))
  have hg0' : ContinuousAt g (0, 0) :=
    hg.continuousAt (isOpen_kernelDom.mem_nhds ⟨by norm_num, by norm_num⟩)
  refine continuous_iff_continuousAt.2 fun t => ?_
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | htpos
    · subst h0
      have : Iio (0 : ℝ≥0) = ∅ := Set.eq_empty_iff_forall_notMem.2 fun u hu =>
        absurd hu (not_lt.2 (zero_le : (0 : ℝ≥0) ≤ u))
      rw [this, ContinuousWithinAt, nhdsWithin_empty]
      exact tendsto_bot
    obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone htpos
    have hev : ∀ᶠ u in 𝓝[<] t, n u = k :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT hu₀) fun u hu => hk u ⟨hu.1.le, hu.2⟩
    by_cases hkt : k = n t
    · subst hkt
      have hsum : Tendsto (fun u => ∑ i ∈ Finset.range (n t), g (x u i, y u i)) (𝓝[<] t)
          (𝓝 (∑ i ∈ Finset.range (n t), g (x t i, y t i))) := by
        refine tendsto_finsetSum _ fun i hi => ?_
        obtain ⟨h1, h2⟩ := tendsto_coord_left_same hP hu₀ hk (Finset.mem_range.1 hi)
        exact (hgt (Finset.mem_range.1 hi)).tendsto.comp (h1.prodMk_nhds h2)
      refine hsum.congr' ?_
      filter_upwards [hev] with u hu
      rw [hu]
    · obtain ⟨hk1, hx0, hy0, hrest⟩ := left_jump hP hu₀ hk hkt
      have hsum : Tendsto (fun u => g (x u 0, y u 0) +
          ∑ i ∈ Finset.range (n t), g (x u (i + 1), y u (i + 1))) (𝓝[<] t)
          (𝓝 (g (0, 0) + ∑ i ∈ Finset.range (n t), g (x t i, y t i))) := by
        refine (hg0'.tendsto.comp (hx0.prodMk_nhds hy0)).add (tendsto_finsetSum _ fun i hi => ?_)
        obtain ⟨h1, h2⟩ := hrest i (Finset.mem_range.1 hi)
        exact (hgt (Finset.mem_range.1 hi)).tendsto.comp (h1.prodMk_nhds h2)
      rw [hg0, zero_add] at hsum
      refine hsum.congr' ?_
      filter_upwards [hev] with u hu
      rw [hu, hk1, Finset.sum_range_succ']
      ring
  · have hsum : Tendsto (fun u => ∑ i ∈ Finset.range (n t), g (x u i, y u i)) (𝓝[≥] t)
        (𝓝 (∑ i ∈ Finset.range (n t), g (x t i, y t i))) := by
      refine tendsto_finsetSum _ fun i hi => ?_
      obtain ⟨h1, h2⟩ := tendsto_coord_right hP t (Finset.mem_range.1 hi)
      exact (hgt (Finset.mem_range.1 hi)).tendsto.comp (h1.prodMk_nhds h2)
    obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
    have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t :=
      Filter.mem_of_superset (Ico_mem_nhdsGE hb) fun u hu => hlev u hu
    have : Tendsto (fun u => ∑ i ∈ Finset.range (n u), g (x u i, y u i)) (𝓝[≥] t)
        (𝓝 (∑ i ∈ Finset.range (n t), g (x t i, y t i))) := by
      refine hsum.congr' ?_
      filter_upwards [hev] with u hu
      rw [hu]
    exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- The kernel pair `g(a, b) = A_ν(a) − A_ν(−b)`. -/
def kernelPair (ν : FiniteMeasure unitInterval) (w : ℝ × ℝ) : ℝ :=
  lkerInt ν w.1 - lkerInt ν (-w.2)

theorem lkerInt_zero (ν : FiniteMeasure unitInterval) : lkerInt ν 0 = 0 := by
  unfold lkerInt lker; simp

theorem continuousOn_kernelPair (ν : FiniteMeasure unitInterval) :
    ContinuousOn (kernelPair ν) kernelDom := by
  have hA : ContinuousOn (lkerInt ν) (Ioi (-1)) := fun a ha =>
    (hasDerivAt_lkerInt ν ha).continuousAt.continuousWithinAt
  refine ContinuousOn.sub (hA.comp continuous_fst.continuousOn fun w hw => hw.1)
    (hA.comp continuous_snd.neg.continuousOn fun w hw => ?_)
  show -1 < -w.2
  linarith [hw.2]

theorem ratioOn_dualCoordOf_eq (ν : FiniteMeasure unitInterval) {k : ℕ} {a b : ℕ → ℝ}
    (h : ∀ i, i < k → (a i, b i) ∈ kernelDom) :
    ratioOn ν (dualCoordOf k a b) =
      Real.exp (∑ i ∈ Finset.range k, kernelPair ν (a i, b i)) := by
  rw [ratioOn_eq_exp ν (fun i => ⟨(h i i.2).1, (h i i.2).2⟩)]
  congr 1
  unfold ratioExp kernelPair dualCoordOf
  exact Fin.sum_univ_eq_sum_range (fun i => lkerInt ν (a i) - lkerInt ν (-b i)) k

/-- **The full-level ratio `t ↦ F_{Z_t}(ν)` is continuous along every deletion path.** -/
theorem continuous_ratioPath (hP : IsDeletionPath n x y) (ν : FiniteMeasure unitInterval) :
    Continuous fun t => ratioOn ν (dualCoordOf (n t) (x t) (y t)) := by
  have e : (fun t => ratioOn ν (dualCoordOf (n t) (x t) (y t))) =
      fun t => Real.exp (∑ i ∈ Finset.range (n t), kernelPair ν (x t i, y t i)) :=
    funext fun t => ratioOn_dualCoordOf_eq ν fun i hi => mem_kernelDom_of_path hP t hi
  rw [e]
  exact Real.continuous_exp.comp (continuous_pathSum hP (continuousOn_kernelPair ν)
    (by simp [kernelPair, lkerInt_zero]))

end Path

/-!
## Monotonicity in the parameters
-/

theorem lker_anti {a x t : ℝ} (hax : a ≤ x) (ht0 : 0 ≤ t) (ha : 0 < 1 + a * t) :
    lker x t ≤ lker a t := by
  unfold lker
  split_ifs with ht
  · linarith
  · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    rw [div_le_div_iff_of_pos_right htp, neg_le_neg_iff]
    exact Real.log_le_log ha (by nlinarith)

/-- **`F_{x,y}(ν) ≤ F_{a,b}(ν)` (one pair)** when `x_{i₀} ≥ a ≥ 0` and `y_{i₀} ≥ b ≥ 0`. -/
theorem transmissionRatio_le_pair {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) (i0 : Fin p)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hax : a ≤ x i0) (hby : b ≤ y i0)
    (ν : FiniteMeasure unitInterval) :
    transmissionRatio x y ν ≤ transmissionRatio ![a] ![b] ν := by
  have hb1 : b < 1 := lt_of_le_of_lt hby (h.2 i0).2
  have hab : IsRatioRange ![a] ![b] := ⟨fun _ => by simpa using ha, fun _ => by simp [hb, hb1]⟩
  have h1 : transmissionRatio x y ν ≤ transmissionRatio ![x i0] ![y i0] ν := by
    rw [transmissionRatio_eq_prod h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    have hle : ∏ j ∈ Finset.univ.erase i0, transmissionRatio ![x j] ![y j] ν ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => (transmissionRatio_mem_vec
        ⟨fun _ => by simpa using h.1 j, fun _ => by simp [(h.2 j).1, (h.2 j).2]⟩ ν).1.le)
        fun j _ => (transmissionRatio_mem_vec
        ⟨fun _ => by simpa using h.1 j, fun _ => by simp [(h.2 j).1, (h.2 j).2]⟩ ν).2
    have hpos := (transmissionRatio_mem_vec
      (⟨fun _ => by simpa using h.1 i0, fun _ => by simp [(h.2 i0).1, (h.2 i0).2]⟩ :
        IsRatioRange ![x i0] ![y i0]) ν).1
    exact mul_le_of_le_one_right hpos.le hle
  refine h1.trans ?_
  unfold transmissionRatio
  refine Real.exp_le_exp.2 (integral_mono (integrable_ratioIntegrand
    ⟨fun _ => by simpa using h.1 i0, fun _ => by simp [(h.2 i0).1, (h.2 i0).2]⟩ ν)
    (integrable_ratioIntegrand hab ν) fun t => ?_)
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  simp only [ratioIntegrand_eq_sum_lker, Finset.univ_unique, Fin.default_eq_zero,
    Matrix.cons_val_fin_one, Finset.sum_singleton]
  have e1 := lker_anti hax ht0 (by nlinarith)
  have e2 := lker_anti (show -y i0 ≤ -b by linarith) ht0 (by nlinarith [(h.2 i0).2])
  linarith

end BlockBand.Transmission.LawDuality
