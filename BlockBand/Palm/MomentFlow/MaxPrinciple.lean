module

public import BlockBand.Palm.MomentFlow.Generator
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.OrderClosed

/-!
# Maximum principle for the conditional moment flow

* `fence_finset`: strict comparison with a barrier `B` (first touching time argument).
* `maxPrinciple_finset`, `minPrinciple_finset`: if the time derivative is `≤ 0` at every
  maximizer (resp. `≥ 0` at every minimizer), the maximum cannot increase (resp. the minimum
  cannot decrease).
* `dampedMaxPrinciple_finset`: if at every maximizer with value `≥ 1` the derivative is at most
  `-κ (f - 1) + e`, then `max f(u) ≤ 1 + A e^{-κ(u-a)} + e/κ` (relaxation with a constant
  error).
* For solutions of `∂_u F = 𝓑_u F` on a sector (`IsMomentFlowSolution`) with nonnegative
  off-diagonal rates: positivity, upper/lower bounds by the initial extremes, `L^∞`
  contraction, and uniqueness of solutions with given initial data.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Filter Topology

variable {X : Type*}

/-- **Fence (first touching time).** Strict initial inequality, and at every interior time and
configuration where `f` touches the barrier `B` from below while staying below it on all of
`S`, the derivative of `f` is strictly smaller than that of `B`. Then `f ≤ B` on `[a,b]`. -/
theorem fence_finset (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ} {B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ u ∈ Ioo a b, HasDerivWithinAt B (B' u) (Ioi u) u)
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
    have hder : HasDerivWithinAt (fun u => f u x - B u) (D t x - B' t) (Ioi t) t :=
      (hf' x hx t ⟨hta, htb'⟩).sub (hB' t ⟨hta, htb'⟩)
    have hslope := hder.limsup_slope_le' (lt_irrefl t) (sub_neg.2 hD)
    filter_upwards [hslope, self_mem_nhdsWithin] with v hv hvt
    have hvt' : 0 < v - t := sub_pos.2 hvt
    rw [slope_def_field] at hv
    have hnum : (f v x - B v) - (f t x - B t) < 0 := by
      have := (div_lt_iff₀ hvt').1 hv
      linarith
    rw [heq, sub_self, sub_zero] at hnum
    linarith

/-- Large-`δ` limit used to remove the relaxation parameter. -/
private theorem le_of_forall_pos_le_add_mul {y z w : ℝ} (hw : 0 ≤ w)
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

/-- **Maximum principle.** If at every interior time the derivative at a maximizer over `S`
is nonpositive, then the maximum does not increase. -/
theorem maxPrinciple_finset (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ} {a b M : ℝ}
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hgen : ∀ u ∈ Ioo a b, ∀ x ∈ S, (∀ y ∈ S, f u y ≤ f u x) → D u x ≤ 0)
    (ha : ∀ x ∈ S, f a x ≤ M) :
    ∀ u ∈ Icc a b, ∀ x ∈ S, f u x ≤ M := by
  intro u hu x hx
  have hw : 0 ≤ 1 + (u - a) := by linarith [hu.1]
  refine le_of_forall_pos_le_add_mul hw fun δ hδ => ?_
  have hfen := fence_finset S (B := fun v => M + δ * (1 + (v - a))) (B' := fun _ => δ) hf hf'
    (by fun_prop)
    (fun v _ => by
      have := ((hasDerivAt_id v).sub_const a).const_add 1 |>.const_mul δ |>.const_add M
      simpa using this.hasDerivWithinAt)
    (fun y hy => by have := ha y hy; simp only [sub_self, add_zero, mul_one]; linarith)
    (fun v hv y hy heq hall => by
      have hmax : ∀ z ∈ S, f v z ≤ f v y := fun z hz => heq ▸ hall z hz
      linarith [hgen v hv y hy hmax])
  exact hfen u hu x hx

/-- **Maximum principle with a source.** If at every maximizer the derivative is at most `e`,
then `f(u) ≤ M + e (u - a)`. -/
theorem sourceMaxPrinciple_finset (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ} {a b M e : ℝ}
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hgen : ∀ u ∈ Ioo a b, ∀ x ∈ S, (∀ y ∈ S, f u y ≤ f u x) → D u x ≤ e)
    (ha : ∀ x ∈ S, f a x ≤ M) :
    ∀ u ∈ Icc a b, ∀ x ∈ S, f u x ≤ M + e * (u - a) := by
  intro u hu x hx
  have hw : 0 ≤ 1 + (u - a) := by linarith [hu.1]
  refine le_of_forall_pos_le_add_mul hw fun δ hδ => ?_
  have hfen := fence_finset S (B := fun v => M + e * (v - a) + δ * (1 + (v - a)))
    (B' := fun _ => e + δ) hf hf' (by fun_prop)
    (fun v _ => by
      have h1 : HasDerivAt (fun v => v - a) 1 v := HasDerivAt.sub_const a (hasDerivAt_id v)
      have h2 := HasDerivAt.fun_add (HasDerivAt.const_add M (HasDerivAt.const_mul e h1))
        (HasDerivAt.const_mul δ (HasDerivAt.const_add 1 h1))
      exact (h2.congr_deriv (by ring)).hasDerivWithinAt)
    (fun y hy => by have := ha y hy; simp only [sub_self, mul_zero, add_zero, mul_one]; linarith)
    (fun v hv y hy heq hall => by
      have hmax : ∀ z ∈ S, f v z ≤ f v y := fun z hz => heq ▸ hall z hz
      linarith [hgen v hv y hy hmax])
  have := hfen u hu x hx
  linarith

/-- **Minimum principle.** -/
theorem minPrinciple_finset (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ} {a b m : ℝ}
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hgen : ∀ u ∈ Ioo a b, ∀ x ∈ S, (∀ y ∈ S, f u x ≤ f u y) → 0 ≤ D u x)
    (ha : ∀ x ∈ S, m ≤ f a x) :
    ∀ u ∈ Icc a b, ∀ x ∈ S, m ≤ f u x := by
  have h := maxPrinciple_finset S (f := fun u x => -f u x) (D := fun u x => -D u x) (M := -m)
    (fun x hx => (hf x hx).neg) (fun x hx u hu => (hf' x hx u hu).neg)
    (fun u hu x hx hmax => by
      have := hgen u hu x hx fun y hy => neg_le_neg_iff.1 (hmax y hy)
      linarith)
    (fun x hx => neg_le_neg (ha x hx))
  intro u hu x hx
  have := h u hu x hx
  linarith

/-- **Damped maximum principle** (with a constant error `e`). If at every maximizer with value at
least `1` the derivative is at most `-κ (f - 1) + e`, then `f(u) ≤ 1 + A e^{-κ(u-a)} + e/κ` whenever
`f(a) ≤ 1 + A`, `A ≥ 0`. -/
theorem dampedMaxPrinciple_finset (S : Finset X) {f : ℝ → X → ℝ} {D : ℝ → X → ℝ}
    {a b κ e A : ℝ} (hκ : 0 < κ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hf : ∀ x ∈ S, ContinuousOn (fun u => f u x) (Icc a b))
    (hf' : ∀ x ∈ S, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => f u x) (D u x) (Ioi u) u)
    (hgen : ∀ u ∈ Ioo a b, ∀ x ∈ S, (∀ y ∈ S, f u y ≤ f u x) → 1 ≤ f u x →
      D u x ≤ -κ * (f u x - 1) + e)
    (ha : ∀ x ∈ S, f a x ≤ 1 + A) :
    ∀ u ∈ Icc a b, ∀ x ∈ S, f u x ≤ 1 + A * Real.exp (-κ * (u - a)) + e / κ := by
  intro u hu x hx
  have hw : 0 ≤ Real.exp (-κ * (u - a)) + 1 / κ := by positivity
  refine le_of_forall_pos_le_add_mul hw fun δ hδ => ?_
  let B : ℝ → ℝ := fun v => 1 + (A + δ) * Real.exp (-κ * (v - a)) + (e + δ) / κ
  let B' : ℝ → ℝ := fun v => (A + δ) * (Real.exp (-κ * (v - a)) * (-κ))
  have hBd : ∀ v, HasDerivAt B (B' v) v := by
    intro v
    have h1 : HasDerivAt (fun v => -κ * (v - a)) (-κ) v := by
      simpa using ((hasDerivAt_id v).sub_const a).const_mul (-κ)
    have h2 := (h1.exp.const_mul (A + δ)).const_add 1 |>.add_const ((e + δ) / κ)
    simpa [B, B'] using h2
  have hfen := fence_finset S (B := B) (B' := B') hf hf'
    (fun v _ => (hBd v).continuousAt.continuousWithinAt)
    (fun v _ => (hBd v).hasDerivWithinAt)
    (fun y hy => by
      have := ha y hy
      simp only [B, sub_self, mul_zero, Real.exp_zero, mul_one]
      have : 0 < (e + δ) / κ := by positivity
      linarith)
    (fun v hv y hy heq hall => by
      have hmax : ∀ z ∈ S, f v z ≤ f v y := fun z hz => heq ▸ hall z hz
      have hexp : 0 < Real.exp (-κ * (v - a)) := Real.exp_pos _
      have h1 : 1 ≤ f v y := by
        rw [heq]; simp only [B]
        have : 0 ≤ (A + δ) * Real.exp (-κ * (v - a)) := by positivity
        have : 0 ≤ (e + δ) / κ := by positivity
        linarith
      have hg := hgen v hv y hy hmax h1
      rw [heq] at hg
      simp only [B, B'] at hg ⊢
      have hk : κ * ((e + δ) / κ) = e + δ := by field_simp
      nlinarith)
  have := hfen u hu x hx
  simp only [B] at this
  have hsplit : 1 + (A + δ) * Real.exp (-κ * (u - a)) + (e + δ) / κ =
      1 + A * Real.exp (-κ * (u - a)) + e / κ + δ * (Real.exp (-κ * (u - a)) + 1 / κ) := by
    field_simp; ring
  linarith

/-!
## Solutions of the moment flow on a sector
-/

variable {N : ℕ}

/-- `F` solves `∂_u F(u,ξ) = (𝓑_{c(u)} F(u))(ξ)` on `[a,b]` for every `ξ` of the `r`-particle
sector (forward form, continuous on `[a,b]`, differentiable on `(a,b)`). -/
def IsMomentFlowSolution (c : ℝ → Fin N → Fin N → ℝ) (r : ℕ) (a b : ℝ)
    (F : ℝ → Occ N → ℝ) : Prop :=
  ∀ ξ ∈ sector N r, ContinuousOn (fun u => F u ξ) (Icc a b) ∧
    ∀ u ∈ Ioo a b, HasDerivAt (fun u => F u ξ) (momentGenerator (c u) (F u) ξ) u

/-- Constants solve the moment flow (conservation). -/
theorem isMomentFlowSolution_const (c : ℝ → Fin N → Fin N → ℝ) (r : ℕ) (a b k : ℝ) :
    IsMomentFlowSolution c r a b (fun _ _ => k) := by
  intro ξ _
  refine ⟨continuousOn_const, fun u _ => ?_⟩
  simpa using hasDerivAt_const u k

/-- Differences of solutions are solutions (linearity). -/
theorem IsMomentFlowSolution.sub {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b : ℝ}
    {F G : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (hG : IsMomentFlowSolution c r a b G) :
    IsMomentFlowSolution c r a b (fun u ξ => F u ξ - G u ξ) := by
  intro ξ hξ
  refine ⟨(hF ξ hξ).1.sub (hG ξ hξ).1, fun u hu => ?_⟩
  have h := ((hF ξ hξ).2 u hu).sub ((hG ξ hξ).2 u hu)
  have : momentGenerator (c u) (fun ζ => F u ζ - G u ζ) ξ =
      momentGenerator (c u) (F u) ξ - momentGenerator (c u) (G u) ξ :=
    momentGenerator_sub (c u) (F u) (G u) ξ
  rw [this]; exact h

/-- The maximum over the sector does not increase along the moment flow (nonnegative
off-diagonal rates, no size bound on the rates). -/
theorem IsMomentFlowSolution.le_of_initial_le {c : ℝ → Fin N → Fin N → ℝ}
    {r : ℕ} {a b M : ℝ}
    (hc : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    {F : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (h0 : ∀ ξ ∈ sector N r, F a ξ ≤ M) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r, F u ξ ≤ M :=
  maxPrinciple_finset (sector N r) (D := fun u ξ => momentGenerator (c u) (F u) ξ)
    (fun ξ hξ => (hF ξ hξ).1) (fun ξ hξ u hu => ((hF ξ hξ).2 u hu).hasDerivWithinAt)
    (fun u hu _ξ hξ hmax => momentGenerator_nonpos_of_isMax (hc u hu) hξ hmax) h0

/-- The minimum over the sector does not decrease; in particular **positivity**. -/
theorem IsMomentFlowSolution.ge_of_initial_ge {c : ℝ → Fin N → Fin N → ℝ}
    {r : ℕ} {a b m : ℝ}
    (hc : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    {F : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (h0 : ∀ ξ ∈ sector N r, m ≤ F a ξ) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r, m ≤ F u ξ :=
  minPrinciple_finset (sector N r) (D := fun u ξ => momentGenerator (c u) (F u) ξ)
    (fun ξ hξ => (hF ξ hξ).1) (fun ξ hξ u hu => ((hF ξ hξ).2 u hu).hasDerivWithinAt)
    (fun u hu _ξ hξ hmin => momentGenerator_nonneg_of_isMin (hc u hu) hξ hmin) h0

/-- **`L^∞` contraction** of the moment flow on the sector. -/
theorem IsMomentFlowSolution.abs_le {c : ℝ → Fin N → Fin N → ℝ}
    {r : ℕ} {a b M : ℝ}
    (hc : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    {F : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (h0 : ∀ ξ ∈ sector N r, |F a ξ| ≤ M) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r, |F u ξ| ≤ M := by
  intro u hu ξ hξ
  rw [_root_.abs_le]
  exact ⟨hF.ge_of_initial_ge hc (fun ζ hζ => (_root_.abs_le.1 (h0 ζ hζ)).1) u hu ξ hξ,
    hF.le_of_initial_le hc (fun ζ hζ => (_root_.abs_le.1 (h0 ζ hζ)).2) u hu ξ hξ⟩

/-- **Uniqueness**: two solutions with the same initial data on the sector agree on the sector
for all times (no bound on the rates). -/
theorem IsMomentFlowSolution.eq_of_initial_eq {c : ℝ → Fin N → Fin N → ℝ}
    {r : ℕ} {a b : ℝ}
    (hc : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    {F G : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (hG : IsMomentFlowSolution c r a b G) (h0 : ∀ ξ ∈ sector N r, F a ξ = G a ξ) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r, F u ξ = G u ξ := by
  intro u hu ξ hξ
  have h := (hF.sub hG).abs_le hc (M := 0) (fun ζ hζ => by simp [h0 ζ hζ]) u hu ξ hξ
  have := abs_nonpos_iff.1 h
  linarith

/-- **Damped maximum principle for the moment flow** (with a constant error): if at every
maximizer with value `≥ 1` the generator is at most `-κ (F - 1) + e`, the excess over `1` relaxes
at rate `κ`. -/
theorem IsMomentFlowSolution.damped_le {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ}
    {a b κ e A : ℝ} (hκ : 0 < κ) (he : 0 ≤ e) (hA : 0 ≤ A)
    {F : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (hgen : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, (∀ ζ ∈ sector N r, F u ζ ≤ F u ξ) → 1 ≤ F u ξ →
      momentGenerator (c u) (F u) ξ ≤ -κ * (F u ξ - 1) + e)
    (h0 : ∀ ξ ∈ sector N r, F a ξ ≤ 1 + A) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r, F u ξ ≤ 1 + A * Real.exp (-κ * (u - a)) + e / κ :=
  dampedMaxPrinciple_finset (sector N r) hκ he hA (fun ξ hξ => (hF ξ hξ).1)
    (fun ξ hξ u hu => ((hF ξ hξ).2 u hu).hasDerivWithinAt) hgen h0

/-- **Duhamel comparison with a bounded source** (the deterministic core of the long-versus-short
moment comparison, without localization): if `Φ` solves `∂_u Φ = 𝓑_u Φ + g_u` with
`|g| ≤ e` on the sector and `Ψ` solves `∂_u Ψ = 𝓑_u Ψ` with the same initial data, then
`|Φ(u) - Ψ(u)| ≤ e (u - a)` on the sector. No bound on the rates is used. -/
theorem momentFlow_source_comparison {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b e : ℝ}
    (hc : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    {Φ Ψ : ℝ → Occ N → ℝ} {g : ℝ → Occ N → ℝ}
    (hΦc : ∀ ξ ∈ sector N r, ContinuousOn (fun u => Φ u ξ) (Icc a b))
    (hΦd : ∀ ξ ∈ sector N r, ∀ u ∈ Ioo a b,
      HasDerivAt (fun u => Φ u ξ) (momentGenerator (c u) (Φ u) ξ + g u ξ) u)
    (hg : ∀ u ∈ Ioo a b, ∀ ξ ∈ sector N r, |g u ξ| ≤ e)
    (hΨ : IsMomentFlowSolution c r a b Ψ) (h0 : ∀ ξ ∈ sector N r, Φ a ξ = Ψ a ξ) :
    ∀ u ∈ Icc a b, ∀ ξ ∈ sector N r, |Φ u ξ - Ψ u ξ| ≤ e * (u - a) := by
  have hDiff : ∀ ξ ∈ sector N r, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => Φ u ξ - Ψ u ξ)
      (momentGenerator (c u) (fun ζ => Φ u ζ - Ψ u ζ) ξ + g u ξ) (Ioi u) u := by
    intro ξ hξ u hu
    have h := HasDerivAt.fun_sub (hΦd ξ hξ u hu) ((hΨ ξ hξ).2 u hu)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    have hs : momentGenerator (c u) (fun ζ => Φ u ζ - Ψ u ζ) ξ =
        momentGenerator (c u) (Φ u) ξ - momentGenerator (c u) (Ψ u) ξ :=
      momentGenerator_sub (c u) (Φ u) (Ψ u) ξ
    rw [hs]; ring
  have hNeg : ∀ ξ ∈ sector N r, ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => -(Φ u ξ - Ψ u ξ))
      (-(momentGenerator (c u) (fun ζ => Φ u ζ - Ψ u ζ) ξ + g u ξ)) (Ioi u) u :=
    fun ξ hξ u hu => (hDiff ξ hξ u hu).neg
  have hcont : ∀ ξ ∈ sector N r, ContinuousOn (fun u => Φ u ξ - Ψ u ξ) (Icc a b) :=
    fun ξ hξ => (hΦc ξ hξ).sub (hΨ ξ hξ).1
  have hup := sourceMaxPrinciple_finset (sector N r) (M := 0) hcont hDiff
    (fun u hu ξ hξ hmax => by
      have h1 := momentGenerator_nonpos_of_isMax (hc u hu) (f := fun ζ => Φ u ζ - Ψ u ζ) hξ hmax
      linarith [(abs_le.1 (hg u hu ξ hξ)).2])
    (fun ξ hξ => by simp [h0 ξ hξ])
  have hlow := sourceMaxPrinciple_finset (sector N r) (M := 0)
    (fun ξ hξ => (hcont ξ hξ).neg) hNeg
    (fun u hu ξ hξ hmax => by
      have hmin : ∀ ζ ∈ sector N r, Φ u ξ - Ψ u ξ ≤ Φ u ζ - Ψ u ζ :=
        fun ζ hζ => neg_le_neg_iff.1 (hmax ζ hζ)
      have h1 := momentGenerator_nonneg_of_isMin (hc u hu) (f := fun ζ => Φ u ζ - Ψ u ζ) hξ hmin
      linarith [(abs_le.1 (hg u hu ξ hξ)).1])
    (fun ξ hξ => by simp [h0 ξ hξ])
  intro u hu ξ hξ
  rw [abs_le]
  constructor
  · have h1 : -(Φ u ξ - Ψ u ξ) ≤ 0 + e * (u - a) := hlow u hu ξ hξ
    linarith
  · have h1 : Φ u ξ - Ψ u ξ ≤ 0 + e * (u - a) := hup u hu ξ hξ
    linarith

end BlockBand.Palm.MomentFlow
