module

public import BlockBand.SourceProcess.ComplexUnique.CMP
public import BlockBand.SourceProcess.ComplexUnique.Restart

/-!
# Localized complex martingale problems with deterministic jumps, and their restarts

A process with deterministic jumps is written as `X + c`: `X : ℝ≥0 → Ω → κ → ℂ` is the
continuous part (complex coordinates) and `c : ℝ≥0 → κ → ℂ` the deterministic jump part.
`IsCLocSol Q 𝓖 β Γ Γ' c X σ`: `X` adapted, a.s. continuous; for every level `L` the compensated
coordinates `lComp` (drift `β(X + c)`), products `lBr` (bracket `Γ(X + c)`) and sesquilinear
products `lBr'` (bracket `Γ'(X + c)`), stopped at `σ L`, have martingale modifications; the hits
of `{‖x‖ ≥ k}` by `X` lie below some `σ L`.

`rsY X c a h`: the restarted real process `u ↦ (u ∧ h, X(a + u ∧ h) + c(a))`.
`cC_rsY`, `cB_rsY`, `cB'_rsY`: before the horizon `h` (with `c` constant on `[a, a + h)`), its
complex compensated coordinates and products are the restarted increments of `lComp`, `lBr`,
`lBr'`, with the cross terms `lComp(a) ΔlComp`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {κ : Type*} [Fintype κ] {Ω : Type*} [MeasurableSpace Ω]

/-- Compensated coordinate `X_p(t) - X_p(0) - ∫_0^t β_p(X + c)`. -/
def lComp (β : (κ → ℂ) → κ → ℂ) (c : ℝ≥0 → κ → ℂ) (X : ℝ≥0 → Ω → κ → ℂ) (p : κ) (t : ℝ≥0)
    (ω : Ω) : ℂ :=
  X t ω p - X 0 ω p - ∫ s in Ioc (0 : ℝ) t, β (X s.toNNReal ω + c s.toNNReal) p

/-- Compensated product. -/
def lBr (β : (κ → ℂ) → κ → ℂ) (Γ : (κ → ℂ) → κ → κ → ℂ) (c : ℝ≥0 → κ → ℂ)
    (X : ℝ≥0 → Ω → κ → ℂ) (p q : κ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  lComp β c X p t ω * lComp β c X q t ω - ∫ s in Ioc (0 : ℝ) t, Γ (X s.toNNReal ω + c s.toNNReal) p q

/-- Compensated sesquilinear product. -/
def lBr' (β : (κ → ℂ) → κ → ℂ) (Γ' : (κ → ℂ) → κ → κ → ℂ) (c : ℝ≥0 → κ → ℂ)
    (X : ℝ≥0 → Ω → κ → ℂ) (p q : κ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  lComp β c X p t ω * star (lComp β c X q t ω) -
    ∫ s in Ioc (0 : ℝ) t, Γ' (X s.toNNReal ω + c s.toNNReal) p q

/-- **A localized complex martingale problem with deterministic jumps.** -/
structure IsCLocSol (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (β : (κ → ℂ) → κ → ℂ) (Γ Γ' : (κ → ℂ) → κ → κ → ℂ) (c : ℝ≥0 → κ → ℂ)
    (X : ℝ≥0 → Ω → κ → ℂ) (σ : ℝ → Ω → WithTop ℝ≥0) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (X t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => X t ω
  loc : ∀ k : ℕ, ∃ L : ℝ, ∀ᵐ ω ∂Q, rawHit {x : κ → ℂ | (k : ℝ) ≤ ‖x‖} X ω ≤ σ L ω
  drift : ∀ (L : ℝ) (p : κ), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧
    ∀ t, N t =ᵐ[Q] stoppedProcess (lComp β c X p) (σ L) t
  bracket : ∀ (L : ℝ) (p q : κ), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧
    ∀ t, N t =ᵐ[Q] stoppedProcess (lBr β Γ c X p q) (σ L) t
  cbracket : ∀ (L : ℝ) (p q : κ), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧
    ∀ t, N t =ᵐ[Q] stoppedProcess (lBr' β Γ' c X p q) (σ L) t

/-- The restarted real process `u ↦ (u ∧ h, X(a + u ∧ h) + c(a))`. -/
def rsY (X : ℝ≥0 → Ω → κ → ℂ) (c : ℝ≥0 → κ → ℂ) (a h : ℝ≥0) :
    ℝ≥0 → Ω → Fin (rDim κ) → ℝ :=
  fun u ω => toR ((min u h : ℝ≥0) : ℝ) (X (a + min u h) ω + c a)

omit [MeasurableSpace Ω] in
theorem zOf_rsY (X : ℝ≥0 → Ω → κ → ℂ) (c : ℝ≥0 → κ → ℂ) (a h u : ℝ≥0) (ω : Ω) :
    zOf (rsY X c a h u ω) = X (a + min u h) ω + c a := zOf_toR _ _

omit [MeasurableSpace Ω] in
theorem tOf_rsY (X : ℝ≥0 → Ω → κ → ℂ) (c : ℝ≥0 → κ → ℂ) (a h u : ℝ≥0) (ω : Ω) :
    tOf (rsY X c a h u ω) = ((min u h : ℝ≥0) : ℝ) := tOf_toR _ _

/-- `∫_{(0,v]} f(a+s) = ∫_{(0,a+v]} f - ∫_{(0,a]} f`. -/
theorem setIntegral_shift {f : ℝ≥0 → ℂ}
    (hf : ∀ A B : ℝ, IntervalIntegrable (fun s : ℝ => f s.toNNReal) volume A B) (a v : ℝ≥0) :
    ∫ s in Ioc (0 : ℝ) v, f (a + s.toNNReal) =
      (∫ s in Ioc (0 : ℝ) (a + v : ℝ≥0), f s.toNNReal) - ∫ s in Ioc (0 : ℝ) a, f s.toNNReal := by
  rw [← intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  have e : ∫ s in (0 : ℝ)..v, f (a + s.toNNReal) = ∫ s in (0 : ℝ)..v, f ((a : ℝ) + s).toNNReal := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIcc_of_le (NNReal.coe_nonneg v)] at hs; exact hs.1
    rw [Real.toNNReal_add a.coe_nonneg hs0, Real.toNNReal_coe]
  rw [e, intervalIntegral.integral_comp_add_left (fun r => f r.toNNReal) (a : ℝ), add_zero,
    NNReal.coe_add]
  exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _))

omit [Fintype κ] in
theorem intervalIntegrable_comp_add [Fintype κ] {g : (κ → ℂ) → ℂ} (hg : Continuous g)
    {x : ℝ≥0 → κ → ℂ} (hx : Continuous x) {c : ℝ≥0 → κ → ℂ} (hc : Measurable c) {C : ℝ}
    (hC : ∀ t, ‖c t‖ ≤ C) (A B : ℝ) :
    IntervalIntegrable (fun s : ℝ => g (x s.toNNReal + c s.toNNReal)) volume A B := by
  rw [intervalIntegrable_iff]
  set T : ℝ≥0 := (max A B).toNNReal
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    hx.continuousOn
  obtain ⟨Bg, hBg⟩ := (isCompact_closedBall (0 : κ → ℂ) (R + C)).exists_bound_of_continuousOn
    hg.continuousOn
  refine Measure.integrableOn_of_bounded (M := Bg) (by simp [Real.volume_uIoc])
    ((hg.measurable.comp ((hx.measurable.comp measurable_real_toNNReal).add
      (hc.comp measurable_real_toNNReal))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun s hs => hBg _ ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsT : s.toNNReal ∈ Icc (0 : ℝ≥0) T := by
    refine ⟨zero_le, Real.toNNReal_le_toNNReal ?_⟩
    rcases hs with ⟨-, h2⟩
    exact h2.trans (max_le (le_max_left _ _) (le_max_right _ _))
  exact (norm_add_le _ _).trans (add_le_add (hR _ hsT) (hC _))

variable {X : ℝ≥0 → Ω → κ → ℂ} {c : ℝ≥0 → κ → ℂ} {ω : Ω}

omit [MeasurableSpace Ω] in
/-- Integrals along the restarted path are restarted integrals. -/
theorem integral_rsY {g : (κ → ℂ) → ℂ} (hg : Continuous g) (hx : Continuous fun t => X t ω)
    (hc : Measurable c) {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) {a h : ℝ≥0}
    (hseg : ∀ t, a ≤ t → t < a + h → c t = c a) {v : ℝ≥0} (hv : v ≤ h) :
    ∫ s in Ioc (0 : ℝ) v, g (zOf (rsY X c a h s.toNNReal ω)) =
      (∫ s in Ioc (0 : ℝ) (a + v : ℝ≥0), g (X s.toNNReal ω + c s.toNNReal)) -
        ∫ s in Ioc (0 : ℝ) a, g (X s.toNNReal ω + c s.toNNReal) := by
  rw [← setIntegral_shift (f := fun t => g (X t ω + c t))
    (intervalIntegrable_comp_add hg hx hc hC)]
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (h : ℝ) := by
    rw [ae_iff]; simp
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [hne] with s hs hsI
  have hsv : s.toNNReal ≤ v := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hsI.2
  have hsh : s.toNNReal < h := by
    rcases (hsv.trans hv).lt_or_eq with h1 | h1
    · exact h1
    · exfalso; apply hs
      rw [← h1, Real.coe_toNNReal _ hsI.1.le]
  rw [zOf_rsY, min_eq_left (hsv.trans hv), hseg _ le_self_add (add_lt_add_of_le_of_lt le_rfl hsh)]

omit [MeasurableSpace Ω] in
theorem cC_rsY {β : (κ → ℂ) → κ → ℂ} (hβ : Continuous β) (hx : Continuous fun t => X t ω)
    (hc : Measurable c) {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) {a h : ℝ≥0}
    (hseg : ∀ t, a ≤ t → t < a + h → c t = c a) {v : ℝ≥0} (hv : v ≤ h) (p : κ) :
    cC β (rsY X c a h) p v ω = lComp β c X p (a + v) ω - lComp β c X p a ω := by
  unfold cC lComp
  rw [integral_rsY (g := fun z => β z p) ((continuous_apply p).comp hβ) hx hc hC hseg hv,
    zOf_rsY, zOf_rsY, min_eq_left hv, min_eq_left (zero_le : (0 : ℝ≥0) ≤ h), add_zero]
  simp only [Pi.add_apply]
  ring

omit [MeasurableSpace Ω] in
theorem cB_rsY {β : (κ → ℂ) → κ → ℂ} (hβ : Continuous β) {Γ : (κ → ℂ) → κ → κ → ℂ}
    (hΓ : Continuous Γ) (hx : Continuous fun t => X t ω) (hc : Measurable c) {C : ℝ}
    (hC : ∀ t, ‖c t‖ ≤ C) {a h : ℝ≥0} (hseg : ∀ t, a ≤ t → t < a + h → c t = c a) {v : ℝ≥0}
    (hv : v ≤ h) (p q : κ) :
    cB β Γ (rsY X c a h) p q v ω = (lBr β Γ c X p q (a + v) ω - lBr β Γ c X p q a ω) -
      lComp β c X p a ω * (lComp β c X q (a + v) ω - lComp β c X q a ω) -
      lComp β c X q a ω * (lComp β c X p (a + v) ω - lComp β c X p a ω) := by
  unfold cB lBr
  rw [cC_rsY hβ hx hc hC hseg hv, cC_rsY hβ hx hc hC hseg hv,
    integral_rsY (g := fun z => Γ z p q) ((continuous_apply q).comp ((continuous_apply p).comp hΓ))
      hx hc hC hseg hv]
  ring

omit [MeasurableSpace Ω] in
theorem cB'_rsY {β : (κ → ℂ) → κ → ℂ} (hβ : Continuous β) {Γ' : (κ → ℂ) → κ → κ → ℂ}
    (hΓ' : Continuous Γ') (hx : Continuous fun t => X t ω) (hc : Measurable c) {C : ℝ}
    (hC : ∀ t, ‖c t‖ ≤ C) {a h : ℝ≥0} (hseg : ∀ t, a ≤ t → t < a + h → c t = c a) {v : ℝ≥0}
    (hv : v ≤ h) (p q : κ) :
    cB' β Γ' (rsY X c a h) p q v ω = (lBr' β Γ' c X p q (a + v) ω - lBr' β Γ' c X p q a ω) -
      lComp β c X p a ω * star (lComp β c X q (a + v) ω - lComp β c X q a ω) -
      star (lComp β c X q a ω) * (lComp β c X p (a + v) ω - lComp β c X p a ω) := by
  unfold cB' lBr'
  rw [cC_rsY hβ hx hc hC hseg hv, cC_rsY hβ hx hc hC hseg hv,
    integral_rsY (g := fun z => Γ' z p q)
      ((continuous_apply q).comp ((continuous_apply p).comp hΓ')) hx hc hC hseg hv, star_sub]
  ring

end BlockBand.SourceProcess.ComplexUnique
