module

public import BlockBand.Transmission.PathScalar.Exit

/-!
# The stopped scalar recursion (abstract form)

Setting: a probability space, nonnegative measurable `δ_j, ξ_j` (`j = 1,…,n`), and
`0 ≤ ρ < 1`, `c ≥ 0`, a domain radius `d > 0` with `c ≤ (1-ρ)d/2`. Hypotheses:
* (step) for `1 ≤ j < n`, almost surely `δ_j ≤ d → δ_{j+1} ≤ ρ δ_j + c + ξ_{j+1}`;
* (bound) almost surely `δ_j ≤ M` (the deterministic port bound);
* `‖δ_1‖_p ≤ s₁` and `‖ξ_j‖_p ≤ s_ξ` (`2 ≤ j ≤ n`).

With the good event `G_r = {δ_1 ≤ d/2} ∩ ⋂_{2 ≤ j ≤ r} {ξ_j ≤ t}`, `t = (1-ρ)d/2`:
* `stopped_le_d`: on `G_r` the recursion never leaves the domain (`δ_r ≤ d`);
* `eLpNorm_stopped_le`: `‖1_{G_r} δ_r‖_p ≤ s₁ + (c + s_ξ)/(1-ρ)` (no independence used:
  Minkowski and the invariant bound);
* `eLpNorm_delta_le`: `‖δ_r‖_p ≤ s₁ + (c + s_ξ)/(1-ρ) + M μ(G_rᶜ)^{1/p}`;
* `measure_bad_le`: `μ(G_rᶜ) ≤ μ(δ_1 > d/2) + Σ_{2 ≤ j ≤ r} μ(ξ_j > t)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory
open scoped ENNReal

section Abstract

variable {Ω : Type*} (δ ξ : ℕ → Ω → ℝ) (d t : ℝ)

/-- The good event `G_r`: `δ_1 ≤ d/2` and `ξ_j ≤ t` for `2 ≤ j ≤ r`. -/
def goodEvent (r : ℕ) : Set Ω :=
  {ω | δ 1 ω ≤ d / 2 ∧ ∀ j, 2 ≤ j → j ≤ r → ξ j ω ≤ t}

theorem goodEvent_mono {r s : ℕ} (h : r ≤ s) : goodEvent δ ξ d t s ⊆ goodEvent δ ξ d t r :=
  fun _ hω => ⟨hω.1, fun j hj hjr => hω.2 j hj (hjr.trans h)⟩

theorem measurableSet_goodEvent [MeasurableSpace Ω] (hδ : Measurable (δ 1)) (hξ : ∀ j, Measurable (ξ j)) (r : ℕ) :
    MeasurableSet (goodEvent δ ξ d t r) := by
  have : goodEvent δ ξ d t r =
      {ω | δ 1 ω ≤ d / 2} ∩ ⋂ j ∈ Finset.Icc 2 r, {ω | ξ j ω ≤ t} := by
    ext ω
    simp only [goodEvent, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_Icc]
    exact ⟨fun h => ⟨h.1, fun j hj => h.2 j hj.1 hj.2⟩, fun h => ⟨h.1, fun j h1 h2 => h.2 j ⟨h1, h2⟩⟩⟩
  rw [this]
  exact (measurableSet_le hδ measurable_const).inter
    (Finset.measurableSet_biInter _ fun j _ => measurableSet_le (hξ j) measurable_const)

/-- The stopped scalar `1_{G_r} δ_r`. -/
def stopped (r : ℕ) : Ω → ℝ := (goodEvent δ ξ d t r).indicator (δ r)

theorem stopped_nonneg (hδ0 : ∀ j ω, 0 ≤ δ j ω) (r : ℕ) (ω : Ω) :
    0 ≤ stopped δ ξ d t r ω := by
  unfold stopped; by_cases h : ω ∈ goodEvent δ ξ d t r
  · rw [Set.indicator_of_mem h]; exact hδ0 r ω
  · rw [Set.indicator_of_notMem h]

variable {δ ξ d t}
variable {ρ c : ℝ} {n : ℕ}

/-- On the good event the recursion stays in the domain. -/
theorem stopped_le_d (hρ0 : 0 ≤ ρ) (hd : 0 < d) (hct : c + t ≤ (1 - ρ) * d) {ω : Ω}
    (hstep : ∀ j, 1 ≤ j → j < n → δ j ω ≤ d → δ (j + 1) ω ≤ ρ * δ j ω + c + ξ (j + 1) ω) :
    ∀ r, 1 ≤ r → r ≤ n → ω ∈ goodEvent δ ξ d t r → δ r ω ≤ d := by
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    intro hrn hω
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact hω.1.trans (by linarith)
    · have h1 := ih hr0 (by omega) (goodEvent_mono δ ξ d t (Nat.le_succ r) hω)
      have h2 := hstep r hr0 (by omega) h1
      have h3 := hω.2 (r + 1) (by omega) le_rfl
      nlinarith

theorem stopped_succ_le (hρ0 : 0 ≤ ρ) (hd : 0 < d) (hc : 0 ≤ c) (hct : c + t ≤ (1 - ρ) * d)
    (hδ0 : ∀ j ω, 0 ≤ δ j ω) (hξ0 : ∀ j ω, 0 ≤ ξ j ω) {ω : Ω}
    (hstep : ∀ j, 1 ≤ j → j < n → δ j ω ≤ d → δ (j + 1) ω ≤ ρ * δ j ω + c + ξ (j + 1) ω)
    {r : ℕ} (hr : 1 ≤ r) (hrn : r < n) :
    stopped δ ξ d t (r + 1) ω ≤ ρ * stopped δ ξ d t r ω + c + ξ (r + 1) ω := by
  have hR : 0 ≤ ρ * stopped δ ξ d t r ω + c + ξ (r + 1) ω := by
    have := stopped_nonneg δ ξ d t hδ0 r ω; have := hξ0 (r + 1) ω; positivity
  unfold stopped
  by_cases h : ω ∈ goodEvent δ ξ d t (r + 1)
  · have h' := goodEvent_mono δ ξ d t (Nat.le_succ r) h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    exact hstep r hr hrn (stopped_le_d hρ0 hd hct hstep r hr hrn.le h')
  · rw [Set.indicator_of_notMem h]
    simpa [stopped] using hR

/-- **The invariant `L^p` bound for the stopped scalar**: `‖1_{G_r}δ_r‖_p ≤ s₁ + (c+s_ξ)/(1-ρ)`. -/
theorem eLpNorm_stopped_le [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p s₁ sξ : ℝ} (hp : 1 ≤ p)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd : 0 < d) (hc : 0 ≤ c) (hct : c + t ≤ (1 - ρ) * d)
    (hs₁ : 0 ≤ s₁) (hsξ : 0 ≤ sξ) (hδ0 : ∀ j ω, 0 ≤ δ j ω) (hξ0 : ∀ j ω, 0 ≤ ξ j ω)
    (hδm : ∀ j, Measurable (δ j)) (hξm : ∀ j, Measurable (ξ j))
    (hstep : ∀ᵐ ω ∂μ, ∀ j, 1 ≤ j → j < n → δ j ω ≤ d →
      δ (j + 1) ω ≤ ρ * δ j ω + c + ξ (j + 1) ω)
    (h1 : eLpNorm (δ 1) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal s₁)
    (hξ : ∀ j, 2 ≤ j → j ≤ n → eLpNorm (ξ j) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal sξ) :
    ∀ r, 1 ≤ r → r ≤ n → eLpNorm (stopped δ ξ d t r) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (s₁ + (c + sξ) / (1 - ρ)) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  set B := s₁ + (c + sξ) / (1 - ρ) with hB
  have hB0 : (c + sξ) / (1 - ρ) ≥ 0 := div_nonneg (by linarith) h1ρ.le
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hSm : ∀ r, Measurable (stopped δ ξ d t r) := fun r =>
    (hδm r).indicator (measurableSet_goodEvent δ ξ d t (hδm 1) hξm r)
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    intro hrn
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · refine le_trans ?_ (h1.trans (ENNReal.ofReal_le_ofReal (by linarith)))
      refine eLpNorm_mono_real (hSm 1).aestronglyMeasurable fun ω => ?_
      rw [Real.norm_of_nonneg (stopped_nonneg δ ξ d t hδ0 1 ω)]
      unfold stopped; by_cases h : ω ∈ goodEvent δ ξ d t 1
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; exact hδ0 1 ω
    · have hIH := ih hr0 (by omega)
      have hmono : eLpNorm (stopped δ ξ d t (r + 1)) (ENNReal.ofReal p) μ ≤
          eLpNorm ((ρ • stopped δ ξ d t r + fun _ => c) + ξ (r + 1)) (ENNReal.ofReal p) μ := by
        refine eLpNorm_mono_ae_real (hSm _).aestronglyMeasurable (hstep.mono fun ω hω => ?_)
        rw [Real.norm_of_nonneg (stopped_nonneg δ ξ d t hδ0 _ ω)]
        simpa [smul_eq_mul] using stopped_succ_le hρ0 hd hc hct hδ0 hξ0 hω hr0 (by omega)
      refine hmono.trans ((eLpNorm_add_le hp1).trans ?_)
      refine (add_le_add (eLpNorm_add_le hp1) (hξ (r + 1) (by omega) hrn)).trans ?_
      rw [eLpNorm_const_smul, eLpNorm_const _ (by simpa using (by linarith : (0 : ℝ) < p))
        (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal hρ0, Real.enorm_eq_ofReal hc]
      calc ENNReal.ofReal ρ * eLpNorm (stopped δ ξ d t r) (ENNReal.ofReal p) μ +
            ENNReal.ofReal c + ENNReal.ofReal sξ
          ≤ ENNReal.ofReal ρ * ENNReal.ofReal B + ENNReal.ofReal c + ENNReal.ofReal sξ := by
            gcongr
        _ = ENNReal.ofReal (ρ * B + c + sξ) := by
            rw [← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add (by positivity) hc,
              ← ENNReal.ofReal_add (by positivity) hsξ]
        _ ≤ ENNReal.ofReal B := by
            refine ENNReal.ofReal_le_ofReal ?_
            have : c + sξ = (1 - ρ) * ((c + sξ) / (1 - ρ)) := by field_simp
            nlinarith

/-- `‖δ_r‖_p ≤ s₁ + (c+s_ξ)/(1-ρ) + μ(G_rᶜ)^{1/p} M`. -/
theorem eLpNorm_delta_le [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p s₁ sξ M : ℝ} (hp : 1 ≤ p)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd : 0 < d) (hc : 0 ≤ c) (hct : c + t ≤ (1 - ρ) * d)
    (hs₁ : 0 ≤ s₁) (hsξ : 0 ≤ sξ) (hδ0 : ∀ j ω, 0 ≤ δ j ω) (hξ0 : ∀ j ω, 0 ≤ ξ j ω)
    (hδm : ∀ j, Measurable (δ j)) (hξm : ∀ j, Measurable (ξ j))
    (hstep : ∀ᵐ ω ∂μ, ∀ j, 1 ≤ j → j < n → δ j ω ≤ d →
      δ (j + 1) ω ≤ ρ * δ j ω + c + ξ (j + 1) ω)
    (h1 : eLpNorm (δ 1) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal s₁)
    (hξ : ∀ j, 2 ≤ j → j ≤ n → eLpNorm (ξ j) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal sξ)
    {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) (hM : ∀ᵐ ω ∂μ, δ r ω ≤ M) :
    eLpNorm (δ r) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (s₁ + (c + sξ) / (1 - ρ)) +
      μ (goodEvent δ ξ d t r)ᶜ ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal M := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hG := measurableSet_goodEvent δ ξ d t (hδm 1) hξm r
  have hsplit : δ r = stopped δ ξ d t r + (goodEvent δ ξ d t r)ᶜ.indicator (δ r) := by
    funext ω; simp only [stopped, Pi.add_apply]
    by_cases h : ω ∈ goodEvent δ ξ d t r
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h), add_zero]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (by simpa using h), zero_add]
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans (add_le_add
    (eLpNorm_stopped_le μ hp hρ0 hρ1 hd hc hct hs₁ hsξ hδ0 hξ0 hδm hξm hstep h1 hξ r hr hrn) ?_)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hG.compl.nullMeasurableSet]
  have := eLpNorm_le_of_ae_bound (μ := μ.restrict (goodEvent δ ξ d t r)ᶜ) (p := ENNReal.ofReal p)
    (hδm r).aestronglyMeasurable (ae_restrict_of_ae (hM.mono fun ω h => by
      rw [Real.norm_of_nonneg (hδ0 r ω)]; exact h))
  rwa [Measure.restrict_apply_univ] at this

/-- The bad event: `μ(G_rᶜ) ≤ μ(δ_1 > d/2) + Σ_{2 ≤ j ≤ r} μ(ξ_j > t)`. -/
theorem measure_bad_le [MeasurableSpace Ω] (μ : Measure Ω) (r : ℕ) :
    μ (goodEvent δ ξ d t r)ᶜ ≤
      μ {ω | d / 2 < δ 1 ω} + ∑ j ∈ Finset.Icc 2 r, μ {ω | t < ξ j ω} := by
  have hsub : (goodEvent δ ξ d t r)ᶜ ⊆
      {ω | d / 2 < δ 1 ω} ∪ ⋃ j ∈ Finset.Icc 2 r, {ω | t < ξ j ω} := by
    intro ω hω
    simp only [goodEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le,
      not_forall] at hω
    rcases hω with h | ⟨j, hj1, hj2, h⟩
    · exact Or.inl h
    · exact Or.inr (Set.mem_biUnion (Finset.mem_Icc.2 ⟨hj1, hj2⟩) h)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le _ _)))

end Abstract

end BlockBand.Transmission.PathScalar
