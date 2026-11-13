module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The ε-pairing of branch starts and crossings (deterministic, abstract)

Abstract setting: finitely many continuous branches `u_α` with nonnegative velocities `v_α`
(`u_α(t) - u_α(s) = ∫_s^t v_α`), a finite set `Z` of crossing parameters (the zeros of the
branches), and the velocity-error bound `∫_{-T}^T χ(u_α)|v_α - 1| ≤ ε` for each branch, with
`χ = 1` on `[-K, K]`. Then every branch starting in `[-R-1, R+1]` crosses zero exactly once in
`Z`, within `ε` of `-u_α(0)`, and branches starting outside contribute nothing to tests supported
in `[-R, R]`; so the two configurations `{u_α(0)}` and `{-t_j}` are `ε`-paired and the linear
statistics differ by at most `M` times the count in `[-R-1, R+1]` (`M` a modulus of `f` at `ε`).
Deterministic; no measure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set

/-- One segment of the flow on which `χ(u) = 1`: `|u(t) - u(s) - (t - s)| ≤ ε`. -/
theorem sep_segment_bound {u v χ : ℝ → ℝ} {T ε s t : ℝ}
    (hint : IntervalIntegrable v volume s t) (hftc : u t - u s = ∫ r in s..t, v r)
    (hA : ∫⁻ r in Icc (-T) T, ENNReal.ofReal (χ (u r) * |v r - 1|) ≤ ENNReal.ofReal ε)
    (hε : 0 ≤ ε) (hst : s ≤ t) (hs : -T ≤ s) (ht : t ≤ T)
    (hχ : ∀ r ∈ Icc s t, χ (u r) = 1) :
    |u t - u s - (t - s)| ≤ ε := by
  have h1 : u t - u s - (t - s) = ∫ r in s..t, (v r - 1) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hftc]
    simp
  rw [h1]
  refine (intervalIntegral.abs_integral_le_integral_abs hst).trans ?_
  rw [intervalIntegral.integral_of_le hst]
  have hi : IntegrableOn (fun r => |v r - 1|) (Ioc s t) :=
    ((hint.sub intervalIntegrable_const).abs).1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun r => abs_nonneg _)
    hi.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal hε
  calc ∫⁻ r in Ioc s t, ENNReal.ofReal |v r - 1|
      = ∫⁻ r in Ioc s t, ENNReal.ofReal (χ (u r) * |v r - 1|) := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro r hr
        simp only
        rw [hχ r (Ioc_subset_Icc_self hr), one_mul]
    _ ≤ ∫⁻ r in Icc (-T) T, ENNReal.ofReal (χ (u r) * |v r - 1|) :=
        lintegral_mono_set fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
    _ ≤ _ := hA

/-- A flow with nonnegative integrated velocity is monotone. -/
theorem sep_monotone {u v : ℝ → ℝ}
    (hftc : ∀ s t, s ≤ t → IntervalIntegrable v volume s t ∧ u t - u s = ∫ r in s..t, v r)
    (hv : ∀ r, 0 ≤ v r) : Monotone u := by
  intro s t hst
  have h := (hftc s t hst).2
  have : 0 ≤ ∫ r in s..t, v r := intervalIntegral.integral_nonneg hst fun r _ => hv r
  linarith

/-- **Key step**: from a base point `s₀` with `|u(s₀)| ≤ R + 1`, the branch
stays in `[-K, K]` and `|u(t) - u(s₀) - (t - s₀)| ≤ ε` for every `t ∈ [-T, T]`. -/
theorem sep_key {u v χ : ℝ → ℝ} {R T K ε s₀ t : ℝ}
    (hu : Continuous u)
    (hftc : ∀ s t, s ≤ t → IntervalIntegrable v volume s t ∧ u t - u s = ∫ r in s..t, v r)
    (hv : ∀ r, 0 ≤ v r)
    (hχ1 : ∀ x ∈ Icc (-K) K, χ x = 1)
    (hA : ∫⁻ r in Icc (-T) T, ENNReal.ofReal (χ (u r) * |v r - 1|) ≤ ENNReal.ofReal ε)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : R + 2 * T + 3 ≤ K)
    (hs₀ : s₀ ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) (hu₀ : |u s₀| ≤ R + 1) :
    |u t - u s₀ - (t - s₀)| ≤ ε := by
  have hmono := sep_monotone hftc hv
  obtain ⟨hu₀l, hu₀u⟩ := abs_le.mp hu₀
  have hT0 : 0 ≤ T := by linarith [hs₀.1, hs₀.2]
  have hR1 : 0 ≤ R + 1 := (abs_nonneg _).trans hu₀
  rcases le_total s₀ t with hst | hts
  · -- forward in time: the upper barrier `K`
    have hbar : ∀ r ∈ Icc s₀ t, u r ≤ K := by
      intro r hr
      by_contra hcon
      replace hcon := lt_of_not_ge hcon
      have hivt := intermediate_value_Icc hr.1 hu.continuousOn
      obtain ⟨t', ht', hut'⟩ := hivt ⟨by linarith, hcon.le⟩
      have hb := sep_segment_bound (hftc s₀ t' ht'.1).1 (hftc s₀ t' ht'.1).2 hA hε ht'.1 hs₀.1
        (by linarith [ht'.2, hr.2, ht.2]) (fun r' hr' => hχ1 _
          ⟨by linarith [hmono hr'.1], by linarith [hmono hr'.2]⟩)
      rw [hut'] at hb
      have := (abs_le.mp hb).2
      linarith [ht'.2, hr.2, ht.2, hs₀.1]
    exact sep_segment_bound (hftc s₀ t hst).1 (hftc s₀ t hst).2 hA hε hst hs₀.1 ht.2
      (fun r hr => hχ1 _ ⟨by linarith [hmono hr.1], hbar r hr⟩)
  · -- backward in time: the lower barrier `-K`
    have hbar : ∀ r ∈ Icc t s₀, -K ≤ u r := by
      intro r hr
      by_contra hcon
      replace hcon := lt_of_not_ge hcon
      have hivt := intermediate_value_Icc hr.2 hu.continuousOn
      obtain ⟨t', ht', hut'⟩ := hivt ⟨hcon.le, by linarith⟩
      have hb := sep_segment_bound (hftc t' s₀ ht'.2).1 (hftc t' s₀ ht'.2).2 hA hε ht'.2
        (by linarith [ht'.1, hr.1, ht.1]) hs₀.2 (fun r' hr' => hχ1 _
          ⟨by linarith [hmono hr'.1], by linarith [hmono hr'.2]⟩)
      rw [hut'] at hb
      have := (abs_le.mp hb).2
      linarith [ht'.1, hr.1, ht.1, hs₀.2]
    have hb := sep_segment_bound (hftc t s₀ hts).1 (hftc t s₀ hts).2 hA hε hts ht.1 hs₀.2
      (fun r hr => hχ1 _ ⟨hbar r hr, by linarith [hmono hr.2]⟩)
    rw [show u t - u s₀ - (t - s₀) = -(u s₀ - u t - (s₀ - t)) by ring, abs_neg]
    exact hb

/-- **Pairing on the event `A ≤ ε`**. -/
theorem se_pairing {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ) (Z : Finset ℝ) (f χ : ℝ → ℝ)
    {R T K ε M : ℝ}
    (hu : ∀ α, Continuous (u α))
    (hftc : ∀ α s t, s ≤ t →
      IntervalIntegrable (v α) volume s t ∧ u α t - u α s = ∫ r in s..t, v α r)
    (hv : ∀ α r, 0 ≤ v α r)
    (hZ : ∀ t, t ∈ Z ↔ ∃ α, u α t = 0)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x ∈ Icc (-K) K, χ x = 1)
    (hA : ∀ α, ∫⁻ r in Icc (-T) T, ENNReal.ofReal (χ (u α r) * |v α r - 1|) ≤ ENNReal.ofReal ε)
    (hf : ∀ x, f x ≠ 0 → |x| ≤ R) (hM : ∀ x y, |x - y| ≤ ε → |f x - f y| ≤ M)
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hT : R + 2 ≤ T) (hK : R + 2 * T + 3 ≤ K) :
    |∑ α, f (u α 0) - ∑ α, ∑ t ∈ Z.filter (fun t => u α t = 0), f (-t)| ≤
      M * ((Finset.univ.filter fun α => |u α 0| ≤ R + 1).card : ℝ) := by
  -- `χ ≥ 0` is not needed for this deterministic step (only `χ = 1` on `[-K, K]`)
  have _ := hχ0
  classical
  have hT0 : 0 ≤ T := by linarith
  have hmono : ∀ α, Monotone (u α) := fun α => sep_monotone (hftc α) (hv α)
  have h0T : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT0⟩
  have key : ∀ α s₀ t, s₀ ∈ Icc (-T) T → t ∈ Icc (-T) T → |u α s₀| ≤ R + 1 →
      |u α t - u α s₀ - (t - s₀)| ≤ ε := fun α s₀ t hs ht h =>
    sep_key (hu α) (hftc α) (hv α) hχ1 (hA α) hε hε1 hK hs ht h
  -- each branch has at most one zero in `Z` (monotone branch, finite `Z`)
  have hlt : ∀ α t₁ t₂, u α t₁ = 0 → u α t₂ = 0 → t₁ < t₂ → False := by
    intro α t₁ t₂ h₁ h₂ h12
    have hsub : Icc t₁ t₂ ⊆ (Z : Set ℝ) := by
      intro x hx
      have hx0 : u α x = 0 :=
        le_antisymm (h₂ ▸ hmono α hx.2) (h₁ ▸ hmono α hx.1)
      exact Finset.mem_coe.mpr ((hZ x).2 ⟨α, hx0⟩)
    exact Set.Icc_infinite h12 (Z.finite_toSet.subset hsub)
  have huniq : ∀ α, ∀ t₁ ∈ Z.filter (fun t => u α t = 0),
      ∀ t₂ ∈ Z.filter (fun t => u α t = 0), t₁ = t₂ := by
    intro α t₁ h₁ t₂ h₂
    rw [Finset.mem_filter] at h₁ h₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt α t₁ t₂ h₁.2 h₂.2 h
    · exact hlt α t₂ t₁ h₂.2 h₁.2 h
  -- a branch starting in `[-R-1, R+1]` crosses within `ε` of `-u_α(0)`
  have hex : ∀ α, |u α 0| ≤ R + 1 →
      ∃ t ∈ Z.filter (fun t => u α t = 0), |u α 0 - -t| ≤ ε := by
    intro α hα
    obtain ⟨hl, hr⟩ := abs_le.mp hα
    have ha : -u α 0 - ε ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
    have hb : -u α 0 + ε ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
    have hka := (abs_le.mp (key α 0 _ h0T ha hα)).2
    have hkb := (abs_le.mp (key α 0 _ h0T hb hα)).1
    have hua : u α (-u α 0 - ε) ≤ 0 := by linarith
    have hub : 0 ≤ u α (-u α 0 + ε) := by linarith
    obtain ⟨t, ht, hut⟩ := intermediate_value_Icc (by linarith : -u α 0 - ε ≤ -u α 0 + ε)
      (hu α).continuousOn ⟨hua, hub⟩
    refine ⟨t, Finset.mem_filter.mpr ⟨(hZ t).2 ⟨α, hut⟩, hut⟩, ?_⟩
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  -- branches starting outside `[-R-1, R+1]` contribute nothing
  have hout : ∀ α, ¬ |u α 0| ≤ R + 1 →
      f (u α 0) = 0 ∧ ∀ t ∈ Z.filter (fun t => u α t = 0), f (-t) = 0 := by
    intro α hα
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hα ((hf _ h).trans (by linarith))
    · intro t ht
      rw [Finset.mem_filter] at ht
      by_contra h
      have h1 := hf _ h
      rw [abs_neg] at h1
      obtain ⟨h1l, h1r⟩ := abs_le.mp h1
      have htT : t ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
      have hk := key α t 0 htT h0T (by rw [ht.2, abs_zero]; linarith)
      rw [ht.2] at hk
      obtain ⟨hkl, hkr⟩ := abs_le.mp hk
      apply hα
      rw [abs_le]
      constructor <;> linarith
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ α, |f (u α 0) - ∑ t ∈ Z.filter (fun t => u α t = 0), f (-t)|
      ≤ ∑ α, (if |u α 0| ≤ R + 1 then M else 0) := by
        refine Finset.sum_le_sum fun α _ => ?_
        split_ifs with hα
        · obtain ⟨t, ht, hdist⟩ := hex α hα
          have hsing : Z.filter (fun t => u α t = 0) = {t} :=
            Finset.eq_singleton_iff_unique_mem.mpr ⟨ht, fun x hx => huniq α x hx t ht⟩
          rw [hsing, Finset.sum_singleton]
          exact hM _ _ hdist
        · obtain ⟨h1, h2⟩ := hout α hα
          rw [h1, Finset.sum_eq_zero h2, sub_zero, abs_zero]
    _ = M * ((Finset.univ.filter fun α => |u α 0| ≤ R + 1).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end BlockBand.Endpoints
