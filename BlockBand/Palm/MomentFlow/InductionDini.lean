module

public import BlockBand.Palm.MomentFlow.MaxPrinciple
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The damped maximum principle with a lower semicontinuous integrated error (Dini fence)

* `fence_dini_finset`: the first-touching comparison of `fence_finset` with the barrier
  derivative replaced by a **lower right Dini bound** (`∀ r < B'(u)`, eventually
  `r(v - u) ≤ B(v) - B(u)` for `v ↓ u`).
* `lowerDini_primitive`: for `g` integrable on `[a,b]` and lower semicontinuous at an interior `u`,
  the primitive `v ↦ ∫_a^v g` has lower right Dini derivative `≥ g(u)` at `u`.
* **`dampedMaxPrinciple_lsc`**: at every maximizer with value `≥ 1`,
  `D ≤ -κ(f - 1) + e + g(u)` with `g ≥ 0` interval-integrable on `[a,b]` and lower
  semicontinuous on `(a,b)` ⇒ `f(u) ≤ 1 + A e^{-κ(u-a)} + e/κ + ∫_a^u g`.
* `dampedMinPrinciple_lsc`: the symmetric statement for the minimum.

Every continuous `g ≥ 0` is admissible; so is every countable sum of nonnegative continuous
functions with integrable sum (lower semicontinuous), e.g. tail functions of propagators.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Filter Topology MeasureTheory intervalIntegral

variable {X : Type*}

/-- **Fence with a lower Dini barrier.** -/
theorem fence_dini_finset (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ} {B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ u ∈ Ioo a b, ∀ r < B' u, ∀ᶠ v in 𝓝[>] u, r * (v - u) ≤ B v - B u)
    (ha : ∀ x ∈ S, f a x < B a)
    (hbound : ∀ u ∈ Ioo a b, ∀ x ∈ S, f u x = B u → (∀ y ∈ S, f u y ≤ B u) → D u x < B' u) :
    ∀ u ∈ Icc a b, ∀ x ∈ S, f u x ≤ B u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀, x₀, hx₀, hlt₀⟩ := hcon
  set T : Set ℝ := {u | u ∈ Icc a b ∧ ∃ x ∈ S, B u < f u x} with hTdef
  have hTne : T.Nonempty := ⟨u₀, hu₀, x₀, hx₀, hlt₀⟩
  have hTbdd : BddBelow T := ⟨a, fun v hv => hv.1.1⟩
  set t := sInf T with htdef
  have hat : a ≤ t := le_csInf hTne fun v hv => hv.1.1
  have htu : t ≤ u₀ := csInf_le hTbdd ⟨hu₀, x₀, hx₀, hlt₀⟩
  have htb : t ≤ b := htu.trans hu₀.2
  -- (i) below `t` everything is below the barrier
  have hbelow : ∀ v ∈ Ico a t, ∀ x ∈ S, f v x ≤ B v := by
    intro v hv x hx
    by_contra h
    push Not at h
    have : t ≤ v := csInf_le hTbdd ⟨⟨hv.1, hv.2.le.trans htb⟩, x, hx, h⟩
    exact absurd hv.2 (not_lt.2 this)
  -- (ii) at `t` everything is below the barrier
  have hat_le : ∀ x ∈ S, f t x ≤ B t := by
    intro x hx
    rcases eq_or_lt_of_le hat with h | h
    · rw [← h]; exact (ha x hx).le
    · have hcl : t ∈ closure (Ico a t) := by
        rw [closure_Ico h.ne]; exact ⟨h.le, le_rfl⟩
      have hsub : Ico a t ⊆ Icc a b := fun v hv => ⟨hv.1, hv.2.le.trans htb⟩
      have hft : ContinuousWithinAt (fun u => f u x) (Ico a t) t :=
        ((hf x hx) t ⟨hat, htb⟩).mono hsub
      have hBt : ContinuousWithinAt B (Ico a t) t := (hB t ⟨hat, htb⟩).mono hsub
      exact ContinuousWithinAt.closure_le hcl hft hBt fun v hv => hbelow v hv x hx
  have htT : t ∉ T := fun h => by
    obtain ⟨_, x, hx, hlt⟩ := h
    exact absurd (hat_le x hx) (not_le.2 hlt)
  have htb' : t < b := by
    rcases eq_or_lt_of_le htb with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hTne
      have hvt : t ≤ v := csInf_le hTbdd hv
      have : v = t := le_antisymm (h ▸ hv.1.2) hvt
      exact htT (this ▸ hv)
    · exact h
  -- (iii) some configuration does not stay below the barrier just after `t`
  have hnot : ∃ x ∈ S, ¬ ∀ᶠ v in 𝓝[>] t, f v x ≤ B v := by
    by_contra h
    push Not at h
    have hall : ∀ᶠ v in 𝓝[>] t, ∀ x ∈ S, f v x ≤ B v :=
      (Filter.eventually_all_finset S).2 h
    obtain ⟨ε, hε, hεsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hall
    have hlow : t < ε → ε ≤ t := by
      intro htε
      apply le_csInf hTne
      intro v hv
      by_contra hvlt
      push Not at hvlt
      have hvt : t ≤ v := csInf_le hTbdd hv
      rcases eq_or_lt_of_le hvt with hve | hve
      · exact htT (hve ▸ hv)
      · obtain ⟨_, x, hx, hlt⟩ := hv
        exact absurd (hεsub ⟨hve, hvlt⟩ x hx) (not_le.2 hlt)
    exact absurd (hlow hε) (not_le.2 hε)
  obtain ⟨x, hx, hxnot⟩ := hnot
  apply hxnot
  have hsub : Ioo t b ⊆ Icc a b := fun v hv => ⟨hat.trans hv.1.le, hv.2.le⟩
  have hnhds : 𝓝[Ioo t b] t = 𝓝[>] t := nhdsWithin_Ioo_eq_nhdsGT htb'
  rcases lt_or_eq_of_le (hat_le x hx) with hlt | heq
  · -- strictly below at `t`: right continuity
    have hft : ContinuousWithinAt (fun u => f u x - B u) (Ioo t b) t :=
      (((hf x hx) t ⟨hat, htb⟩).sub (hB t ⟨hat, htb⟩)).mono hsub
    rw [ContinuousWithinAt, hnhds] at hft
    have hev : ∀ᶠ v in 𝓝[>] t, f v x - B v < 0 :=
      hft.eventually (gt_mem_nhds (sub_neg.2 hlt))
    exact hev.mono fun v hv => (sub_neg.1 hv).le
  · -- touching at `t`: then `t > a` and the derivative condition applies
    have hta : a < t := by
      rcases eq_or_lt_of_le hat with h | h
      · exfalso; rw [← h] at heq; exact absurd heq (ha x hx).ne
      · exact h
    have hD := hbound t ⟨hta, htb'⟩ x hx heq hat_le
    set r := (D t x + B' t) / 2
    have hr1 : D t x < r := by simp only [r]; linarith
    have hr2 : r < B' t := by simp only [r]; linarith
    have hslope := ((hf' x hx t ⟨hta, htb'⟩).limsup_slope_le' (lt_irrefl t) hr1)
    filter_upwards [hslope, hB' t ⟨hta, htb'⟩ r hr2, self_mem_nhdsWithin] with v hv hBv hvt
    have hvt' : 0 < v - t := sub_pos.2 hvt
    rw [slope_def_field] at hv
    have hnum : f v x - f t x < r * (v - t) := by
      have := (div_lt_iff₀ hvt').1 hv
      linarith
    linarith

private theorem le_of_forall_pos_le_add_mul'' {y z w : ℝ} (hw : 0 ≤ w)
    (h : ∀ δ : ℝ, 0 < δ → y ≤ z + δ * w) : y ≤ z := by
  by_contra hyz
  push Not at hyz
  have hpos : 0 < y - z := sub_pos.2 hyz
  have hδ : 0 < (y - z) / (2 * (w + 1)) := by positivity
  have h1 := h _ hδ
  have h2 : (y - z) / (2 * (w + 1)) * w < y - z := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Differentiable functions have the expected lower right Dini bound. -/
theorem lowerDini_of_hasDerivAt {φ : ℝ → ℝ} {φ' u : ℝ} (h : HasDerivAt φ φ' u) :
    ∀ r < φ', ∀ᶠ v in 𝓝[>] u, r * (v - u) ≤ φ v - φ u := by
  intro r hr
  have h1 : ∀ᶠ v in 𝓝[>] u, r < slope φ u v := by
    have ht := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl u)).1
      (h.hasDerivWithinAt (s := Ioi u))
    exact ht (IsOpen.mem_nhds isOpen_Ioi hr)
  filter_upwards [h1, self_mem_nhdsWithin] with v hv hvu
  have hvu' : 0 < v - u := sub_pos.2 hvu
  rw [slope_def_field, lt_div_iff₀ hvu'] at hv
  linarith

/-- The primitive of an integrable, lower semicontinuous `g` has lower right Dini derivative
`≥ g(u)`. -/
theorem lowerDini_primitive {g : ℝ → ℝ} {a b u : ℝ} (hg : IntervalIntegrable g volume a b)
    (hab : a ≤ b) (hu : u ∈ Ioo a b) (hlsc : LowerSemicontinuousAt g u) :
    ∀ r < g u, ∀ᶠ v in 𝓝[>] u, r * (v - u) ≤ (∫ t in a..v, g t) - ∫ t in a..u, g t := by
  intro r hr
  have hev : ∀ᶠ t in 𝓝 u, r < g t := hlsc r hr
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : Ioo u (min (u + δ) b) ∈ 𝓝[>] u := Ioo_mem_nhdsGT (lt_min (by linarith) hu.2)
  filter_upwards [hmem] with v hv
  have hvb : v ≤ b := hv.2.le.trans (min_le_right _ _)
  have huv : u ≤ v := hv.1.le
  have hsub : uIcc a v ⊆ uIcc a b := by
    rw [uIcc_of_le (hu.1.le.trans huv), uIcc_of_le hab]
    exact Icc_subset_Icc_right hvb
  have hsub' : uIcc a u ⊆ uIcc a b := by
    rw [uIcc_of_le hu.1.le, uIcc_of_le hab]; exact Icc_subset_Icc_right hu.2.le
  have hsub'' : uIcc u v ⊆ uIcc a b := by
    rw [uIcc_of_le huv, uIcc_of_le hab]; exact Icc_subset_Icc hu.1.le hvb
  rw [intervalIntegral.integral_interval_sub_left (hg.mono_set hsub) (hg.mono_set hsub')]
  have hconst : ∫ t in u..v, r = r * (v - u) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← hconst]
  refine intervalIntegral.integral_mono_on huv intervalIntegrable_const (hg.mono_set hsub'')
    fun t ht => ?_
  have : dist t u < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
    have := hv.2; have := min_le_left (u + δ) b; linarith [ht.2]
  exact (hball this).le

/-- **Damped maximum principle with a lower semicontinuous integrated error.** -/
theorem dampedMaxPrinciple_lsc (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ}
    {g : ℝ → ℝ} {a b κ e A : ℝ} (hab : a ≤ b) (hκ : 0 < κ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hg : IntervalIntegrable g volume a b) (hlsc : ∀ u ∈ Ioo a b, LowerSemicontinuousAt g u)
    (hg0 : ∀ u ∈ Icc a b, 0 ≤ g u)
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hgen : ∀ u ∈ Ioo a b, ∀ x ∈ S, (∀ y ∈ S, f u y ≤ f u x) → 1 ≤ f u x →
      D u x ≤ -κ * (f u x - 1) + e + g u)
    (ha : ∀ x ∈ S, f a x ≤ 1 + A) :
    ∀ u ∈ Icc a b, ∀ x ∈ S,
      f u x ≤ 1 + A * Real.exp (-κ * (u - a)) + e / κ + ∫ v in a..u, g v := by
  intro u hu x hx
  have hw : 0 ≤ Real.exp (-κ * (u - a)) + 1 / κ := by positivity
  refine le_of_forall_pos_le_add_mul'' hw fun δ hδ => ?_
  set G : ℝ → ℝ := fun v => ∫ t in a..v, g t
  have hGc : ContinuousOn G (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := a) hg
      left_mem_uIcc
    rwa [uIcc_of_le hab] at this
  have hG0 : ∀ v ∈ Icc a b, 0 ≤ G v := fun v hv =>
    intervalIntegral.integral_nonneg hv.1 fun t ht => hg0 t ⟨ht.1, ht.2.trans hv.2⟩
  set φ : ℝ → ℝ := fun v => 1 + (A + δ) * Real.exp (-κ * (v - a)) + (e + δ) / κ
  set φ' : ℝ → ℝ := fun v => (A + δ) * (Real.exp (-κ * (v - a)) * (-κ))
  have hE : ∀ v, HasDerivAt φ (φ' v) v := by
    intro v
    have h1 : HasDerivAt (fun v => -κ * (v - a)) (-κ) v := by
      simpa using ((hasDerivAt_id v).sub_const a).const_mul (-κ)
    have h2 := (h1.exp.const_mul (A + δ)).const_add 1 |>.add_const ((e + δ) / κ)
    simpa [φ, φ'] using h2
  let B : ℝ → ℝ := fun v => φ v + G v
  let B' : ℝ → ℝ := fun v => φ' v + g v
  have hBd : ∀ v ∈ Ioo a b, ∀ r < B' v, ∀ᶠ w in 𝓝[>] v, r * (w - v) ≤ B w - B v := by
    intro v hv r hr
    set ε := (B' v - r) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    have h1 := lowerDini_of_hasDerivAt (hE v) (φ' v - ε) (by linarith)
    have h2 := lowerDini_primitive hg hab hv (hlsc v hv) (g v - ε) (by linarith)
    filter_upwards [h1, h2, self_mem_nhdsWithin] with w hw1 hw2 hwv
    have : r = (φ' v - ε) + (g v - ε) := by simp only [ε, B']; ring
    simp only [B, G] at hw2 ⊢
    rw [this]; nlinarith
  have hfen := fence_dini_finset S (B := B) (B' := B') hf hf'
    (fun v hv => ((hE v).continuousAt.continuousWithinAt).add (hGc v hv)) hBd
    (fun y hy => by
      have := ha y hy
      simp only [B, φ, G, sub_self, mul_zero, Real.exp_zero, mul_one,
        intervalIntegral.integral_same, add_zero]
      have : 0 < (e + δ) / κ := by positivity
      linarith)
    (fun v hv y hy heq hall => by
      have hmax : ∀ z ∈ S, f v z ≤ f v y := fun z hz => heq ▸ hall z hz
      have hexp : 0 < Real.exp (-κ * (v - a)) := Real.exp_pos _
      have hGv := hG0 v ⟨hv.1.le, hv.2.le⟩
      have h1 : 1 ≤ f v y := by
        rw [heq]; simp only [B, φ]
        have : 0 ≤ (A + δ) * Real.exp (-κ * (v - a)) := by positivity
        have : 0 ≤ (e + δ) / κ := by positivity
        linarith
      have hgv := hgen v hv y hy hmax h1
      rw [heq] at hgv
      simp only [B, B', φ, φ'] at hgv ⊢
      have hk : κ * ((e + δ) / κ) = e + δ := by field_simp
      nlinarith [mul_nonneg hκ.le hGv])
  have := hfen u hu x hx
  simp only [B, φ, G] at this
  have hsplit : 1 + (A + δ) * Real.exp (-κ * (u - a)) + (e + δ) / κ + ∫ t in a..u, g t =
      1 + A * Real.exp (-κ * (u - a)) + e / κ + (∫ t in a..u, g t) +
        δ * (Real.exp (-κ * (u - a)) + 1 / κ) := by
    field_simp; ring
  linarith

/-- **Damped minimum principle with a lower semicontinuous integrated error.** -/
theorem dampedMinPrinciple_lsc (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ}
    {g : ℝ → ℝ} {a b κ e A : ℝ} (hab : a ≤ b) (hκ : 0 < κ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hg : IntervalIntegrable g volume a b) (hlsc : ∀ u ∈ Ioo a b, LowerSemicontinuousAt g u)
    (hg0 : ∀ u ∈ Icc a b, 0 ≤ g u)
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hgen : ∀ u ∈ Ioo a b, ∀ x ∈ S, (∀ y ∈ S, f u x ≤ f u y) → f u x ≤ 1 →
      κ * (1 - f u x) - e - g u ≤ D u x)
    (ha : ∀ x ∈ S, 1 - A ≤ f a x) :
    ∀ u ∈ Icc a b, ∀ x ∈ S,
      1 - A * Real.exp (-κ * (u - a)) - e / κ - ∫ v in a..u, g v ≤ f u x := by
  have h := dampedMaxPrinciple_lsc S (f := fun u x => 2 - f u x) (D := fun u x => -D u x)
    hab hκ he hA hg hlsc hg0 (fun x hx => continuousOn_const.sub (hf x hx))
    (fun x hx u hu => by simpa using (hf' x hx u hu).const_sub 2)
    (fun u hu x hx hmax h1 => by
      have := hgen u hu x hx (fun y hy => by have := hmax y hy; linarith) (by linarith)
      linarith)
    (fun x hx => by have := ha x hx; linarith)
  intro u hu x hx
  have := h u hu x hx
  linarith

end BlockBand.Palm.MomentFlow
