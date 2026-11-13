module

public import BlockBand.Transmission.Dual.Hitting
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Martingale.Basic

/-!
# Right-continuous processes and the time shift of a martingale

* **`isStronglyProgressive_of_rightCont`**: a strongly adapted real process with right-continuous
  paths is strongly progressive (approximants `u(⌈2^l s⌉/2^l ∧ i)` on `[0, i]`). Mathlib only has
  the continuous case. With `measurable_stoppedValue` this gives `𝓖_τ`-measurability of `u_τ`.
* `shiftTime θ t = t − θ` (truncated subtraction, i.e. `(t − θ)⁺`) is a stopping time for a
  `𝓖₀`-measurable `θ` (`isStoppingTime_shiftTime`); `shiftFilt` is the filtration
  `t ↦ 𝓖_{(t−θ)⁺}`.
* **`martingale_shift`**: for a right-continuous martingale `M`, bounded on bounded time sets,
  `t ↦ M_{(t−θ)⁺}` is a `shiftFilt`-martingale. Identity: `θ` is approximated from below by
  dyadics `θ_k = ⌊2^k θ⌋/2^k`; on `{θ_k = r}` the martingale property at the deterministic
  times `(s−r)⁺ ≤ (t−r)⁺` applies (the set is in `𝓖_{(s−r)⁺}` because `θ_k ≤ θ`); then
  `(t − θ_k)⁺ ↓ (t − θ)⁺`, right-continuity and dominated convergence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}

/-- **A right-continuous adapted real process is progressive.** -/
theorem isStronglyProgressive_of_rightCont {u : ℝ≥0 → Ω → ℝ} (h : StronglyAdapted 𝓖 u)
    (hrc : ∀ ω t, Tendsto (fun s => u s ω) (𝓝[≥] t) (𝓝 (u t ω))) :
    IsStronglyProgressive 𝓖 u := by
  intro i
  let _ : MeasurableSpace Ω := 𝓖 i
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun (l : ℕ) (p : Set.Iic i × Ω) => u (min (ceilDyad l p.1) i) p.2) (fun l => ?_)
    (tendsto_pi_nhds.2 fun p => ?_)
  · have hk : ∀ k : ℕ, Measurable fun ω => u (min ((k : ℝ≥0) / 2 ^ l) i) ω := fun k =>
      ((h _).mono (𝓖.mono (min_le_right _ _))).measurable
    have hF : Measurable fun q : Ω × ℕ => u (min ((q.2 : ℝ≥0) / 2 ^ l) i) q.1 :=
      measurable_from_prod_countable_left hk
    have hg : Measurable fun p : Set.Iic i × Ω => (p.2, ⌈(p.1 : ℝ≥0) * 2 ^ l⌉₊) :=
      measurable_snd.prodMk (Nat.measurable_ceil.comp
        ((measurable_subtype_coe.comp measurable_fst).mul_const _))
    exact (hF.comp hg).stronglyMeasurable
  · obtain ⟨⟨s, hs⟩, ω⟩ := p
    have h1 : Tendsto (fun l => min (ceilDyad l s) i) atTop (𝓝[≥] s) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun l =>
        le_min (le_ceilDyad l s) hs⟩
      have := ((tendsto_ceilDyad s).mono_right nhdsWithin_le_nhds).min
        (tendsto_const_nhds (x := i))
      rwa [min_eq_left (show s ≤ i from hs)] at this
    exact (hrc ω s).comp h1

/-!
## The time shift
-/

/-- The shifted time `(t − θ)⁺`. -/
def shiftTime (θ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 := ((t - θ ω : ℝ≥0) : WithTop ℝ≥0)

variable {θ : Ω → ℝ≥0}

theorem isStoppingTime_shiftTime (hθ : Measurable[𝓖 0] θ) (t : ℝ≥0) :
    IsStoppingTime 𝓖 (shiftTime θ t) := by
  intro u
  have e : {ω | shiftTime θ t ω ≤ u} = θ ⁻¹' {x | t ≤ u + x} := by
    ext ω; simp only [shiftTime, mem_ofPred_eq, mem_preimage, WithTop.coe_le_coe,
      tsub_le_iff_right]
  rw [e]
  exact 𝓖.mono zero_le _ (hθ (measurableSet_le measurable_const
    (measurable_const.add measurable_id)))

/-- The filtration `t ↦ 𝓖_{(t−θ)⁺}`. -/
def shiftFilt (hθ : Measurable[𝓖 0] θ) : Filtration ℝ≥0 m where
  seq t := (isStoppingTime_shiftTime hθ t).measurableSpace
  mono' _ _ hst := IsStoppingTime.measurableSpace_mono _ _ fun _ =>
    WithTop.coe_le_coe.2 (tsub_le_tsub_right hst _)
  le' t := (isStoppingTime_shiftTime hθ t).measurableSpace_le

/-- The dyadic approximation from below `⌊2^k x⌋/2^k`. -/
def floorDyad (k : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌊x * 2 ^ k⌋₊ : ℝ≥0) / 2 ^ k

theorem floorDyad_le (k : ℕ) (x : ℝ≥0) : floorDyad k x ≤ x := by
  rw [floorDyad, div_le_iff₀ (by positivity)]; exact Nat.floor_le zero_le

theorem le_floorDyad_add (k : ℕ) (x : ℝ≥0) : x ≤ floorDyad k x + (1 / 2) ^ k := by
  have h := Nat.lt_floor_add_one (x * 2 ^ k)
  have h2 : (0 : ℝ≥0) < 2 ^ k := by positivity
  rw [floorDyad, one_div, inv_pow, ← mul_le_mul_iff_left₀ h2, add_mul, div_mul_cancel₀ _ h2.ne',
    inv_mul_cancel₀ h2.ne']
  exact h.le

theorem tendsto_floorDyad (x : ℝ≥0) : Tendsto (fun k => floorDyad k x) atTop (𝓝 x) := by
  have h0 : Tendsto (fun k : ℕ => x - (1 / 2 : ℝ≥0) ^ k) atTop (𝓝 (x - 0)) :=
    tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [tsub_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds
    (fun k => tsub_le_iff_right.2 (le_floorDyad_add k x)) (fun k => floorDyad_le k x)

variable {P : Measure Ω} [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}

theorem measurable_comp_nat (hM : StronglyAdapted 𝓖 M) {g : Ω → ℕ} (hg : Measurable g)
    (c : ℕ → ℝ≥0) : Measurable fun ω => M (c (g ω)) ω := by
  have hF : Measurable fun q : Ω × ℕ => M (c q.2) q.1 :=
    measurable_from_prod_countable_left fun k => ((hM (c k)).mono (𝓖.le _)).measurable
  exact hF.comp (measurable_id.prodMk hg)

theorem integrable_of_abs_le' {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    Integrable f P :=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun ω => hC ω)

/-- **The martingale identity for the shift at a dyadic `θ_k`.** -/
theorem setIntegral_shift_floorDyad (hM : Martingale M 𝓖 P) (hθ : Measurable[𝓖 0] θ)
    (hb : ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, ∀ ω, |M t ω| ≤ C) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[shiftFilt hθ s] A) (k : ℕ) :
    ∫ ω in A, M (t - floorDyad k (θ ω)) ω ∂P = ∫ ω in A, M (s - floorDyad k (θ ω)) ω ∂P := by
  have hθm : Measurable θ := hθ.mono (𝓖.le 0) le_rfl
  have hgm : Measurable fun ω => ⌊θ ω * 2 ^ k⌋₊ := Nat.measurable_floor.comp (hθm.mul_const _)
  set r : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) / 2 ^ k
  set B : ℕ → Set Ω := fun j => A ∩ {ω | ⌊θ ω * 2 ^ k⌋₊ = j}
  have hB0 : ∀ j, MeasurableSet[𝓖 0] {ω | ⌊θ ω * 2 ^ k⌋₊ = j} := fun j =>
    (Nat.measurable_floor.comp (hθ.mul_const _)) (measurableSet_singleton j)
  have hBs : ∀ j, MeasurableSet[𝓖 (s - r j)] (B j) := by
    intro j
    have h1 := hA.2 (s - r j)
    have e : B j = (A ∩ {ω | shiftTime θ s ω ≤ ↑(s - r j)}) ∩ {ω | ⌊θ ω * 2 ^ k⌋₊ = j} := by
      ext ω
      simp only [B, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hω, hj⟩
        refine ⟨⟨hω, WithTop.coe_le_coe.2 (tsub_le_tsub_left ?_ s)⟩, hj⟩
        have := floorDyad_le k (θ ω)
        rwa [floorDyad, hj] at this
      · rintro ⟨⟨hω, -⟩, hj⟩; exact ⟨hω, hj⟩
    rw [e]; exact h1.inter (𝓖.mono zero_le _ (hB0 j))
  have hBm : ∀ j, MeasurableSet (B j) := fun j => 𝓖.le _ _ (hBs j)
  have hA' : A = ⋃ j, B j := by
    ext ω; simp only [B, mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_eq_right']
  have hdisj : Pairwise (Function.onFun Disjoint B) := fun i j hij => by
    refine Set.disjoint_left.2 fun ω h1 h2 => hij ?_
    exact h1.2.symm.trans h2.2
  have hfd : ∀ ω, floorDyad k (θ ω) = r (⌊θ ω * 2 ^ k⌋₊) := fun ω => rfl
  have hint : ∀ u, IntegrableOn (fun ω => M (u - floorDyad k (θ ω)) ω) (⋃ j, B j) P := by
    intro u
    obtain ⟨C, hC⟩ := hb u
    exact (integrable_of_abs_le' (measurable_comp_nat hM.1 hgm fun j => u - r j)
      fun ω => hC _ tsub_le_self ω).integrableOn
  have hpiece : ∀ u j, ∫ ω in B j, M (u - floorDyad k (θ ω)) ω ∂P = ∫ ω in B j, M (u - r j) ω ∂P :=
    fun u j => setIntegral_congr_fun (hBm j) fun ω hω => by
      show M (u - floorDyad k (θ ω)) ω = M (u - r j) ω
      rw [hfd ω, show ⌊θ ω * 2 ^ k⌋₊ = j from hω.2]
  rw [hA', integral_iUnion hBm hdisj (hint t), integral_iUnion hBm hdisj (hint s)]
  refine tsum_congr fun j => ?_
  rw [hpiece, hpiece]
  exact (hM.setIntegral_eq (tsub_le_tsub_right hst _) (hBs j)).symm

theorem shift_eq_stoppedValue (θ : Ω → ℝ≥0) (t : ℝ≥0) :
    (fun ω => M (t - θ ω) ω) = stoppedValue M (shiftTime θ t) := rfl

/-- **The time shift of a right-continuous bounded martingale is a martingale** for
`t ↦ 𝓖_{(t−θ)⁺}`, `θ` `𝓖₀`-measurable. -/
theorem martingale_shift (hM : Martingale M 𝓖 P) (hθ : Measurable[𝓖 0] θ)
    (hrc : ∀ ω t, Tendsto (fun s => M s ω) (𝓝[≥] t) (𝓝 (M t ω)))
    (hb : ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, ∀ ω, |M t ω| ≤ C) :
    Martingale (fun t ω => M (t - θ ω) ω) (shiftFilt hθ) P := by
  have hprog := isStronglyProgressive_of_rightCont hM.1 hrc
  have hadapt : ∀ t, StronglyMeasurable[shiftFilt hθ t] fun ω => M (t - θ ω) ω := fun t => by
    rw [shift_eq_stoppedValue]
    exact (measurable_stoppedValue hprog (isStoppingTime_shiftTime hθ t)).stronglyMeasurable
  have hmeas : ∀ t, Measurable fun ω => M (t - θ ω) ω := fun t =>
    ((hadapt t).mono ((shiftFilt hθ).le t)).measurable
  have hint : ∀ t, Integrable (fun ω => M (t - θ ω) ω) P := fun t => by
    obtain ⟨C, hC⟩ := hb t
    exact integrable_of_abs_le' (hmeas t) fun ω => hC _ tsub_le_self ω
  have hθm : Measurable θ := hθ.mono (𝓖.le 0) le_rfl
  have hlim : ∀ (u : ℝ≥0) (A : Set Ω), Tendsto (fun k => ∫ ω in A, M (u - floorDyad k (θ ω)) ω ∂P)
      atTop (𝓝 (∫ ω in A, M (u - θ ω) ω ∂P)) := by
    intro u A
    obtain ⟨C, hC⟩ := hb u
    have hgm : ∀ k, Measurable fun ω => ⌊θ ω * 2 ^ k⌋₊ := fun k =>
      Nat.measurable_floor.comp (hθm.mul_const _)
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun k => (measurable_comp_nat hM.1 (hgm k)
        fun j => u - (j : ℝ≥0) / 2 ^ k).aestronglyMeasurable)
      (integrable_const C) (fun k => ae_of_all _ fun ω => hC _ tsub_le_self ω)
      (ae_of_all _ fun ω => (hrc ω (u - θ ω)).comp ?_)
    refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_const_nhds (x := u)).sub (tendsto_floorDyad _),
      Eventually.of_forall fun k => tsub_le_tsub_left (floorDyad_le k (θ ω)) u⟩
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((shiftFilt hθ).le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  exact tendsto_nhds_unique ((hlim s A).congr fun k =>
    (setIntegral_shift_floorDyad hM hθ hb hst hA k).symm) (hlim t A)

end BlockBand.Transmission.Dual.G
