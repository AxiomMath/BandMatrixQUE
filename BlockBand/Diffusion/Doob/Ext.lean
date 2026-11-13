module

public import BlockBand.Diffusion.Doob.Test

/-!
# Measures determined by the duality tests

**Headline (`dk_measure_ext`).** Two measures `μ, ν` on `α × ℝ²`, `μ` finite, both concentrated
on `α × (0, ∞) × (0, 1)` (`exOpenStrip`), which agree on all the test functionals
`∫ 1_A(a) (x + y) g(x) k(y)` (`A` measurable, `(g, k)` a test pair, `IsDkTestPair`), are equal.

Proof. With the continuous ramps `dkRamp a b m ↑ 1_{(a,b)}` (test pairs), monotone convergence
gives agreement of the truncated weighted measures `μ_n = (x + y) 1_{x < n} μ` on all boxes
`A × (a, b) × (c, d)`; these are finite, so they are equal (`Measure.ext_prod₃` and twice
`dk_ext_of_Ioo` on `ℝ`); letting `n → ∞` and dividing by `x + y > 0` on the open strip gives
`μ = ν`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### Finite measures on `ℝ` agreeing on open intervals
-/

theorem dk_ext_of_Ioo (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a b : ℝ, a < b → μ (Ioo a b) = ν (Ioo a b)) : μ = ν := by
  refine Measure.ext_of_Ioc μ ν fun a b hab => ?_
  have hI : Ioc a b = ⋂ n : ℕ, Ioo a (b + 1 / ((n : ℝ) + 1)) := by
    ext r
    simp only [mem_Ioc, mem_iInter, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩ n
      exact ⟨h1, lt_of_le_of_lt h2 (lt_add_of_pos_right _ (by positivity))⟩
    · intro hr
      refine ⟨(hr 0).1, le_of_forall_pos_lt_add fun ε hε => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      exact lt_of_lt_of_le (hr n).2 (by linarith)
  have hdir : Antitone fun n : ℕ => Ioo a (b + 1 / ((n : ℝ) + 1)) := by
    refine fun m n hmn => Ioo_subset_Ioo_right ?_
    have : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have := one_div_le_one_div_of_le (by positivity) this
    linarith
  have h1 := tendsto_measure_iInter_atTop (μ := μ)
    (fun _ => measurableSet_Ioo.nullMeasurableSet) hdir ⟨0, measure_ne_top _ _⟩
  have h2 := tendsto_measure_iInter_atTop (μ := ν)
    (fun _ => measurableSet_Ioo.nullMeasurableSet) hdir ⟨0, measure_ne_top _ _⟩
  rw [hI]
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  simp only [Function.comp]
  exact (h _ _ (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                   linarith)).symm

/-!
### Ramps
-/

/-- The continuous ramp `min 1 (max 0 (m · min (x - a) (b - x)))`, increasing in `m` to
`1_{(a, b)}`. -/
def dkRamp (a b : ℝ) (m : ℕ) (x : ℝ) : ℝ := min 1 (max 0 ((m : ℝ) * min (x - a) (b - x)))

theorem dkRamp_nonneg (a b : ℝ) (m : ℕ) (x : ℝ) : 0 ≤ dkRamp a b m x :=
  le_min zero_le_one (le_max_left _ _)

theorem dkRamp_le_one (a b : ℝ) (m : ℕ) (x : ℝ) : dkRamp a b m x ≤ 1 := min_le_left _ _

theorem continuous_dkRamp (a b : ℝ) (m : ℕ) : Continuous (dkRamp a b m) := by
  unfold dkRamp; fun_prop

theorem dkRamp_eq_zero {a b : ℝ} (m : ℕ) {x : ℝ} (hx : x ∉ Ioo a b) : dkRamp a b m x = 0 := by
  have : min (x - a) (b - x) ≤ 0 := by
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  unfold dkRamp
  rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) this)]
  simp

theorem dkRamp_mono (a b : ℝ) (x : ℝ) : Monotone fun m => dkRamp a b m x := by
  intro m n hmn
  simp only [dkRamp]
  rcases le_total 0 (min (x - a) (b - x)) with h | h
  · exact min_le_min_left _ (max_le_max_left _
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) h))
  · have h1 : (m : ℝ) * min (x - a) (b - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) h
    have h2 : (n : ℝ) * min (x - a) (b - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h
    rw [max_eq_left h1, max_eq_left h2]

theorem tendsto_dkRamp (a b x : ℝ) :
    Tendsto (fun m : ℕ => dkRamp a b m x) atTop (𝓝 ((Ioo a b).indicator 1 x)) := by
  by_cases hx : x ∈ Ioo a b
  · rw [indicator_of_mem hx, Pi.one_apply]
    have hpos : 0 < min (x - a) (b - x) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt (1 / min (x - a) (b - x))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨m₀, fun m hm => ?_⟩)
    have : 1 ≤ (m : ℝ) * min (x - a) (b - x) := by
      have h1 : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
      rw [div_lt_iff₀ hpos] at hm₀
      nlinarith
    show (1 : ℝ) = min 1 (max 0 ((m : ℝ) * min (x - a) (b - x)))
    rw [max_eq_right (by linarith), min_eq_left this]
  · rw [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr fun m => (dkRamp_eq_zero m hx).symm

theorem isDkTestPair_dkRamp (a b c d : ℝ) (m : ℕ) :
    IsDkTestPair (dkRamp a b m) (dkRamp c d m) where
  contg := continuous_dkRamp a b m
  contk := continuous_dkRamp c d m
  g_nonneg := dkRamp_nonneg a b m
  g_le := dkRamp_le_one a b m
  k_nonneg := dkRamp_nonneg c d m
  k_le := dkRamp_le_one c d m
  supp := ⟨b, fun x hx => dkRamp_eq_zero m fun h => by linarith [h.2]⟩

/-!
### The extension lemma
-/

section Ext

variable {α : Type*} [MeasurableSpace α]

/-- The test functional `1_A(a) (x + y) g(x) k(y)`. -/
def dkTestFun (A : Set α) (g k : ℝ → ℝ) (p : α × (ℝ × ℝ)) : ℝ≥0∞ :=
  A.indicator 1 p.1 * ENNReal.ofReal ((p.2.1 + p.2.2) * g p.2.1 * k p.2.2)

theorem measurable_dkTestFun {A : Set α} (hA : MeasurableSet A) {g k : ℝ → ℝ}
    (hg : Measurable g) (hk : Measurable k) : Measurable (dkTestFun A g k) := by
  unfold dkTestFun
  refine ((measurable_const.indicator hA).comp measurable_fst).mul ?_
  refine ENNReal.measurable_ofReal.comp ?_
  exact (((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd)).mul
    (hg.comp (measurable_fst.comp measurable_snd))).mul (hk.comp (measurable_snd.comp
      measurable_snd))

/-- The truncated weight `(x + y) 1_{x < n}`. -/
def dkWeight (n : ℕ) (p : α × (ℝ × ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (p.2.1 + p.2.2) * (Iio (n : ℝ)).indicator 1 p.2.1

theorem measurable_dkWeight (n : ℕ) : Measurable (dkWeight (α := α) n) := by
  unfold dkWeight
  exact (ENNReal.measurable_ofReal.comp ((measurable_fst.comp measurable_snd).add
    (measurable_snd.comp measurable_snd))).mul ((measurable_const.indicator measurableSet_Iio).comp
      (measurable_fst.comp measurable_snd))

variable {μ ν : Measure (α × (ℝ × ℝ))}

/-- Boxes of the weighted measures from the tests (monotone convergence of ramps). -/
theorem dk_box_eq (hμO : ∀ᵐ p ∂μ, p.2 ∈ exOpenStrip) (hνO : ∀ᵐ p ∂ν, p.2 ∈ exOpenStrip)
    (htest : ∀ A : Set α, MeasurableSet A → ∀ g k : ℝ → ℝ, IsDkTestPair g k →
      ∫⁻ p, dkTestFun A g k p ∂μ = ∫⁻ p, dkTestFun A g k p ∂ν)
    (n : ℕ) {s : Set α} (hs : MeasurableSet s) (a b c d : ℝ) :
    μ.withDensity (dkWeight n) (s ×ˢ Ioo a b ×ˢ Ioo c d) =
      ν.withDensity (dkWeight n) (s ×ˢ Ioo a b ×ˢ Ioo c d) := by
  set a' := max a 0
  set b' := min b n
  set c' := max c 0
  set d' := min d 1
  have hbox : MeasurableSet (s ×ˢ Ioo a b ×ˢ Ioo c d) :=
    hs.prod (measurableSet_Ioo.prod measurableSet_Ioo)
  -- the limit integrand
  set F : α × (ℝ × ℝ) → ℝ≥0∞ := fun p => s.indicator 1 p.1 *
    ENNReal.ofReal ((p.2.1 + p.2.2) * (Ioo a' b').indicator 1 p.2.1 *
      (Ioo c' d').indicator 1 p.2.2) with hF
  have hbF : ∀ p : α × (ℝ × ℝ), p.2 ∈ exOpenStrip →
      (s ×ˢ Ioo a b ×ˢ Ioo c d).indicator (dkWeight n) p = F p := by
    rintro ⟨q, x, y⟩ ⟨hx, hy0, hy1⟩
    simp only at hx hy0 hy1
    have e1 : (a' < x ∧ x < b') ↔ ((a < x ∧ x < b) ∧ x < n) := by
      simp only [a', b', max_lt_iff, lt_min_iff]; constructor
      · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, hx⟩, h2, h3⟩
    have e2 : (c' < y ∧ y < d') ↔ (c < y ∧ y < d) := by
      simp only [c', d', max_lt_iff, lt_min_iff]; constructor
      · rintro ⟨⟨h1, -⟩, h2, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hy0⟩, h2, hy1⟩
    simp only [hF, indicator_apply]
    by_cases h1 : a < x ∧ x < b <;> by_cases h2 : x < (n : ℝ) <;>
      by_cases h3 : c < y ∧ y < d <;> by_cases hq : q ∈ s <;>
      simp [h1, h2, h3, hq, dkWeight, e1, e2]
  -- the ramps
  set f : ℕ → α × (ℝ × ℝ) → ℝ≥0∞ := fun m => dkTestFun s (dkRamp a' b' m) (dkRamp c' d' m)
    with hf
  have hfm : ∀ m, Measurable (f m) := fun m =>
    measurable_dkTestFun hs (continuous_dkRamp _ _ m).measurable
      (continuous_dkRamp _ _ m).measurable
  have hmono : ∀ p : α × (ℝ × ℝ), p.2 ∈ exOpenStrip → Monotone fun m => f m p := by
    rintro ⟨q, x, y⟩ ⟨hx, hy0, -⟩ m m' hmm'
    have hx' : 0 < x := hx
    have hy0' : 0 < y := hy0
    simp only [hf, dkTestFun]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    have hxy : 0 ≤ x + y := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left (dkRamp_mono _ _ _ hmm') hxy)
      (dkRamp_mono _ _ _ hmm') (dkRamp_nonneg _ _ _ _)
      (mul_nonneg hxy (dkRamp_nonneg _ _ _ _))
  have hlim : ∀ p : α × (ℝ × ℝ), Tendsto (fun m => f m p) atTop (𝓝 (F p)) := by
    rintro ⟨q, x, y⟩
    simp only [hf, hF, dkTestFun]
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ((tendsto_const_nhds.mul
      (tendsto_dkRamp a' b' x)).mul (tendsto_dkRamp c' d' y)))
      (Or.inr (by by_cases hq : q ∈ s <;> simp [hq]))
  have hTμ := lintegral_tendsto_of_tendsto_of_monotone (μ := μ) (fun m => (hfm m).aemeasurable)
    (hμO.mono fun p hp => hmono p hp) (ae_of_all _ hlim)
  have hTν := lintegral_tendsto_of_tendsto_of_monotone (μ := ν) (fun m => (hfm m).aemeasurable)
    (hνO.mono fun p hp => hmono p hp) (ae_of_all _ hlim)
  have heq : ∀ m, ∫⁻ p, f m p ∂μ = ∫⁻ p, f m p ∂ν := fun m =>
    htest s hs _ _ (isDkTestPair_dkRamp a' b' c' d' m)
  have hlimeq : ∫⁻ p, F p ∂μ = ∫⁻ p, F p ∂ν :=
    tendsto_nhds_unique hTμ (hTν.congr fun m => (heq m).symm)
  rw [withDensity_apply _ hbox, withDensity_apply _ hbox, ← lintegral_indicator hbox,
    ← lintegral_indicator hbox, lintegral_congr_ae (hμO.mono fun p hp => hbF p hp),
    lintegral_congr_ae (hνO.mono fun p hp => hbF p hp), hlimeq]

/-- **Measures determined by the duality tests.** -/
theorem dk_measure_ext [IsFiniteMeasure μ] (hμO : ∀ᵐ p ∂μ, p.2 ∈ exOpenStrip)
    (hνO : ∀ᵐ p ∂ν, p.2 ∈ exOpenStrip)
    (htest : ∀ A : Set α, MeasurableSet A → ∀ g k : ℝ → ℝ, IsDkTestPair g k →
      ∫⁻ p, dkTestFun A g k p ∂μ = ∫⁻ p, dkTestFun A g k p ∂ν) : μ = ν := by
  -- the weighted measures agree
  have hW : ∀ n : ℕ, μ.withDensity (dkWeight n) = ν.withDensity (dkWeight n) := by
    intro n
    set μn := μ.withDensity (dkWeight n) with hμn
    set νn := ν.withDensity (dkWeight n) with hνn
    have hbox := fun {s : Set α} (hs : MeasurableSet s) a b c d =>
      dk_box_eq hμO hνO htest n hs a b c d
    -- finiteness
    have hμf : IsFiniteMeasure μn := by
      refine ⟨?_⟩
      rw [hμn, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      have hb : ∫⁻ p, dkWeight n p ∂μ ≤ ∫⁻ _, ENNReal.ofReal ((n : ℝ) + 1) ∂μ := by
        refine lintegral_mono_ae (hμO.mono fun p hp => ?_)
        simp only [dkWeight]
        by_cases hx : p.2.1 < n
        · rw [indicator_of_mem (show p.2.1 ∈ Iio (n : ℝ) from hx), Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal (by linarith [hp.2.2])
        · rw [indicator_of_notMem (show p.2.1 ∉ Iio (n : ℝ) from hx), mul_zero]
          exact bot_le
      refine lt_of_le_of_lt hb ?_
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    have hconc : ∀ ρ : Measure (α × (ℝ × ℝ)), (∀ᵐ p ∂ρ, p.2 ∈ exOpenStrip) →
        ρ.withDensity (dkWeight n) (univ ×ˢ Ioo (-1) (n : ℝ) ×ˢ Ioo (-1) 2)ᶜ = 0 := by
      intro ρ hρ
      have hm : MeasurableSet (univ ×ˢ Ioo (-1) (n : ℝ) ×ˢ Ioo (-1) 2 : Set (α × (ℝ × ℝ))) :=
        MeasurableSet.univ.prod (measurableSet_Ioo.prod measurableSet_Ioo)
      rw [withDensity_apply _ hm.compl]
      refine le_antisymm ?_ bot_le
      calc ∫⁻ p in (univ ×ˢ Ioo (-1) (n : ℝ) ×ˢ Ioo (-1) 2)ᶜ, dkWeight n p ∂ρ
          ≤ ∫⁻ _ in (univ ×ˢ Ioo (-1) (n : ℝ) ×ˢ Ioo (-1) 2)ᶜ, 0 ∂ρ := by
            refine lintegral_mono_ae ((ae_restrict_iff' hm.compl).2 (hρ.mono fun p hp hpc => ?_))
            have hx : ¬ p.2.1 < n := by
              intro hx
              apply hpc
              have h1 : (0 : ℝ) < p.2.1 := hp.1
              have h2 : (0 : ℝ) < p.2.2 := hp.2.1
              have h3 : p.2.2 < 1 := hp.2.2
              exact ⟨mem_univ _, ⟨by linarith, hx⟩, ⟨by linarith, by linarith⟩⟩
            simp only [dkWeight, indicator_of_notMem (show p.2.1 ∉ Iio (n : ℝ) from hx),
              mul_zero, le_refl]
        _ = 0 := by simp
    have hPm : MeasurableSet (univ ×ˢ Ioo (-1) (n : ℝ) ×ˢ Ioo (-1) 2 : Set (α × (ℝ × ℝ))) :=
      MeasurableSet.univ.prod (measurableSet_Ioo.prod measurableSet_Ioo)
    have hνf : IsFiniteMeasure νn := by
      refine ⟨?_⟩
      rw [← measure_add_measure_compl hPm, hconc ν hνO, add_zero, ← hbox MeasurableSet.univ]
      exact measure_lt_top _ _
    -- boxes with measurable sides
    have hstage1 : ∀ {s : Set α}, MeasurableSet s → ∀ {t : Set ℝ}, MeasurableSet t →
        ∀ c d : ℝ, μn (s ×ˢ t ×ˢ Ioo c d) = νn (s ×ˢ t ×ˢ Ioo c d) := by
      intro s hs t ht c d
      have hR : MeasurableSet (s ×ˢ (univ : Set ℝ) ×ˢ Ioo c d) :=
        hs.prod (MeasurableSet.univ.prod measurableSet_Ioo)
      have hmap : ∀ (ρ : Measure (α × (ℝ × ℝ))) (I : Set ℝ), MeasurableSet I →
          ((ρ.restrict (s ×ˢ (univ : Set ℝ) ×ˢ Ioo c d)).map fun p => p.2.1) I =
            ρ (s ×ˢ I ×ˢ Ioo c d) := by
        intro ρ I hI
        have hmf : Measurable fun p : α × (ℝ × ℝ) => p.2.1 := by fun_prop
        rw [Measure.map_apply hmf hI, Measure.restrict_apply (hmf hI)]
        congr 1
        ext p
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and]
        tauto
      have hE : ((μn.restrict (s ×ˢ (univ : Set ℝ) ×ˢ Ioo c d)).map fun p => p.2.1) =
          ((νn.restrict (s ×ˢ (univ : Set ℝ) ×ˢ Ioo c d)).map fun p => p.2.1) := by
        refine dk_ext_of_Ioo _ _ fun a b _ => ?_
        rw [hmap μn _ measurableSet_Ioo, hmap νn _ measurableSet_Ioo]
        exact hbox hs a b c d
      rw [← hmap μn t ht, ← hmap νn t ht, hE]
    have hstage2 : ∀ {s : Set α}, MeasurableSet s → ∀ {t : Set ℝ}, MeasurableSet t →
        ∀ {u : Set ℝ}, MeasurableSet u → μn (s ×ˢ t ×ˢ u) = νn (s ×ˢ t ×ˢ u) := by
      intro s hs t ht u hu
      have hmap : ∀ (ρ : Measure (α × (ℝ × ℝ))) (J : Set ℝ), MeasurableSet J →
          ((ρ.restrict (s ×ˢ t ×ˢ (univ : Set ℝ))).map fun p => p.2.2) J =
            ρ (s ×ˢ t ×ˢ J) := by
        intro ρ J hJ
        have hmf : Measurable fun p : α × (ℝ × ℝ) => p.2.2 := by fun_prop
        rw [Measure.map_apply hmf hJ, Measure.restrict_apply (hmf hJ)]
        congr 1
        ext p
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
        tauto
      have hE : ((μn.restrict (s ×ˢ t ×ˢ (univ : Set ℝ))).map fun p => p.2.2) =
          ((νn.restrict (s ×ˢ t ×ˢ (univ : Set ℝ))).map fun p => p.2.2) := by
        refine dk_ext_of_Ioo _ _ fun c d _ => ?_
        rw [hmap μn _ measurableSet_Ioo, hmap νn _ measurableSet_Ioo]
        exact hstage1 hs ht c d
      rw [← hmap μn u hu, ← hmap νn u hu, hE]
    exact Measure.ext_prod₃ fun hs ht hu => hstage2 hs ht hu
  -- remove the weight
  set O' : Set (α × (ℝ × ℝ)) := {p | p.2 ∈ exOpenStrip} with hO'
  have hO'm : MeasurableSet O' :=
    measurable_snd (measurableSet_Ioi.prod measurableSet_Ioo)
  have hμc : μ O'ᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hμO.mono fun p hp h => h hp)
  have hνc : ν O'ᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hνO.mono fun p hp h => h hp)
  ext S hS
  have hSO := hS.inter hO'm
  have key : μ (S ∩ O') = ν (S ∩ O') := by
    set f : ℕ → α × (ℝ × ℝ) → ℝ≥0∞ := fun n p =>
      dkWeight n p * (S ∩ O').indicator (fun p => (ENNReal.ofReal (p.2.1 + p.2.2))⁻¹) p
      with hfdef
    have hg : Measurable ((S ∩ O').indicator fun p : α × (ℝ × ℝ) =>
        (ENNReal.ofReal (p.2.1 + p.2.2))⁻¹) :=
      (ENNReal.measurable_ofReal.comp ((measurable_fst.comp measurable_snd).add
        (measurable_snd.comp measurable_snd))).inv.indicator hSO
    have hfm : ∀ n, Measurable (f n) := fun n => (measurable_dkWeight n).mul hg
    have hmono : ∀ p, Monotone fun n => f n p := fun p m n hmn => by
      simp only [hfdef, dkWeight]
      refine mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
      by_cases hx : p.2.1 < m
      · have hx' : p.2.1 < n := lt_of_lt_of_le hx (by exact_mod_cast hmn)
        simp [indicator_of_mem (show p.2.1 ∈ Iio (m : ℝ) from hx),
          indicator_of_mem (show p.2.1 ∈ Iio (n : ℝ) from hx')]
      · simp [indicator_of_notMem (show p.2.1 ∉ Iio (m : ℝ) from hx)]
    have hlim : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 ((S ∩ O').indicator 1 p)) := by
      intro p
      by_cases hp : p ∈ S ∩ O'
      · have hpos : 0 < p.2.1 + p.2.2 := by
          have h1 : (0 : ℝ) < p.2.1 := hp.2.1
          have h2 : (0 : ℝ) < p.2.2 := hp.2.2.1
          linarith
        obtain ⟨n₀, hn₀⟩ := exists_nat_gt p.2.1
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
        have hx : p.2.1 < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
        simp only [hfdef, dkWeight, indicator_of_mem hp,
          indicator_of_mem (show p.2.1 ∈ Iio (n : ℝ) from hx), Pi.one_apply, mul_one]
        exact (ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hpos).ne'
          ENNReal.ofReal_ne_top).symm
      · simp only [hfdef, indicator_of_notMem hp, mul_zero]
        exact tendsto_const_nhds
    have hT : ∀ ρ : Measure (α × (ℝ × ℝ)), Tendsto (fun n => ∫⁻ p, f n p ∂ρ) atTop
        (𝓝 (ρ (S ∩ O'))) := fun ρ => by
      have := lintegral_tendsto_of_tendsto_of_monotone (μ := ρ) (fun n => (hfm n).aemeasurable)
        (ae_of_all _ hmono) (ae_of_all _ hlim)
      rwa [lintegral_indicator_one hSO] at this
    have heq : ∀ n, ∫⁻ p, f n p ∂μ = ∫⁻ p, f n p ∂ν := fun n => by
      have e : ∀ ρ : Measure (α × (ℝ × ℝ)), ∫⁻ p, f n p ∂ρ =
          ∫⁻ p, (S ∩ O').indicator (fun p => (ENNReal.ofReal (p.2.1 + p.2.2))⁻¹) p
            ∂(ρ.withDensity (dkWeight n)) := fun ρ =>
        (lintegral_withDensity_eq_lintegral_mul ρ (measurable_dkWeight n) hg).symm
      rw [e μ, e ν, hW n]
    exact tendsto_nhds_unique (hT μ) ((hT ν).congr fun n => (heq n).symm)
  have hsplit : ∀ ρ : Measure (α × (ℝ × ℝ)), ρ O'ᶜ = 0 → ρ S = ρ (S ∩ O') := fun ρ h0 => by
    rw [← measure_inter_add_sdiff S hO'm,
      measure_mono_null (fun p (hp : p ∈ S \ O') => hp.2) h0, add_zero]
  rw [hsplit μ hμc, hsplit ν hνc, key]

end Ext

end BlockBand.Diffusion
