module

public import BlockBand.Diffusion.Doob.Defs

/-!
# Pathwise structure of the one-pair boundary dual

For a level path `n` with `n 0 = 1` and the pathwise structure
`IsDkBoundaryDeletionPath n x y` (a copy of `IsBoundaryDeletionPath`), with lifetime
`σ = dkDualExtinction` (a copy of `dualExtinction`):
* `dk_level_le_one`, `dk_level_eq_one_iff`: `n_t ≤ 1`, and `n_t = 1 ↔ t < σ` (right continuity
  of the level); `dk_level_eq_zero`: `n_t = 0` for `t ≥ σ`; `dk_extinction_pos`: `σ > 0`;
* `dk_mem_openStrip`: for `0 < t < σ` the point `(x_t 0, y_t 0)` lies in the open strip
  `exOpenStrip = (0, ∞) × (0, 1)` (the `chamber` field at level `1`);
* `dk_continuous_pt`: the killed point `dkPt` (equal to `(x_t 0, y_t 0)` while the level is `1`
  and to the corner `(0, 0)` after) is **continuous** on `[0, ∞)` (the `cont` field before
  `σ`, the `deletion` field at `σ`: the left limit is the corner).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

variable {Ω : Type*}

/-- The killed point of a one-pair dual: `(X_t 0, Y_t 0)` while `N_0 = N_t = 1`, the corner
`(0, 0)` otherwise. -/
def dkPt (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ × ℝ :=
  if N 0 ω = 1 ∧ N t ω = 1 then (X t ω 0, Y t ω 0) else (0, 0)

section Deterministic

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

/-- The lifetime of a level path (`dkDualExtinction` of a deterministic path). -/
theorem dk_extinction_eq (N : ℝ≥0 → Ω → ℕ) (ω : Ω) :
    dkDualExtinction N ω = ⨅ (t : ℝ≥0) (_ : N t ω = 0), (t : ℝ≥0∞) := rfl

variable (h : IsDkBoundaryDeletionPath n x y) (h0 : n 0 = 1)
include h h0

theorem dk_level_le_one (t : ℝ≥0) : n t ≤ 1 := h0 ▸ h.antitone zero_le

/-- The level is `1` exactly before the lifetime. -/
theorem dk_level_eq_one_iff (t : ℝ≥0) :
    n t = 1 ↔ (t : ℝ≥0∞) < ⨅ (u : ℝ≥0) (_ : n u = 0), (u : ℝ≥0∞) := by
  constructor
  · intro ht
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h.rightCont t)
    refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hu') (le_iInf₂ fun v hv => ?_)
    by_contra hlt
    have hlt' : v < u' := ENNReal.coe_lt_coe.1 (not_le.1 hlt)
    rcases le_or_gt v t with hvt | hvt
    · have := h.antitone hvt
      rw [ht, hv] at this
      exact absurd this (by norm_num)
    · have : n v = n t := hsub ⟨hvt, hlt'⟩
      rw [hv, ht] at this
      exact absurd this (by norm_num)
  · intro ht
    by_contra hne
    have h1 : n t = 0 := by
      have := dk_level_le_one h h0 t
      omega
    exact absurd (iInf₂_le t h1) (not_le.2 ht)

theorem dk_level_eq_zero {t : ℝ≥0} (ht : ⨅ (u : ℝ≥0) (_ : n u = 0), (u : ℝ≥0∞) ≤ t) :
    n t = 0 := by
  have h1 : ¬ n t = 1 := fun h1 => not_lt.2 ht ((dk_level_eq_one_iff h h0 t).1 h1)
  have := dk_level_le_one h h0 t
  omega

theorem dk_extinction_pos : 0 < ⨅ (u : ℝ≥0) (_ : n u = 0), (u : ℝ≥0∞) := by
  have := (dk_level_eq_one_iff h h0 0).1 h0
  simpa using this

/-- Before the lifetime and at positive times the point lies in the open strip. -/
theorem dk_mem_openStrip {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < ⨅ (u : ℝ≥0) (_ : n u = 0), (u : ℝ≥0∞)) :
    (x t 0, y t 0) ∈ exOpenStrip := by
  have h1 : n t = 1 := (dk_level_eq_one_iff h h0 t).2 ht
  have hc := h.chamber t ht0
  rw [h1] at hc
  obtain ⟨-, -, hx, hy⟩ := hc
  exact ⟨hx 0, (hy 0).1, (hy 0).2⟩

end Deterministic

section Process

variable {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
  (h : IsDkBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (h0 : N 0 ω = 1)
include h h0

theorem dkPt_eq_of_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < dkDualExtinction N ω) :
    dkPt N X Y t ω = (X t ω 0, Y t ω 0) := by
  have h1 : N t ω = 1 := (dk_level_eq_one_iff h h0 t).2 ht
  simp [dkPt, h0, h1]

theorem dkPt_eq_of_le {t : ℝ≥0} (ht : dkDualExtinction N ω ≤ t) : dkPt N X Y t ω = (0, 0) := by
  have h1 : N t ω = 0 := dk_level_eq_zero h h0 ht
  simp [dkPt, h1]

/-- **The killed point is continuous.** -/
theorem dk_continuous_pt : Continuous fun t => dkPt N X Y t ω := by
  set σ := dkDualExtinction N ω with hσ
  have hP : ∀ t₁ : ℝ≥0, (t₁ : ℝ≥0∞) < σ →
      ContinuousOn (fun t => (X t ω 0, Y t ω 0)) (Icc 0 t₁) := fun t₁ ht₁ => by
    have h1 : N t₁ ω = 1 := (dk_level_eq_one_iff h h0 t₁).2 ht₁
    have hc := h.cont 0 t₁ zero_le (by simp only [h1, h0]) 0 (by simp [h0])
    exact hc.1.prodMk hc.2
  rw [continuous_iff_continuousAt]
  intro t₀
  rcases lt_trichotomy (t₀ : ℝ≥0∞) σ with hlt | heq | hgt
  · obtain ⟨t₁, ht₀₁, ht₁σ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have ht₀₁' : t₀ < t₁ := ENNReal.coe_lt_coe.1 ht₀₁
    have hmem : Icc (0 : ℝ≥0) t₁ ∈ 𝓝 t₀ := by
      have : Icc (0 : ℝ≥0) t₁ = Iic t₁ := by
        ext v; simp
      rw [this]; exact Iic_mem_nhds ht₀₁'
    have hcongr : EqOn (fun t => dkPt N X Y t ω) (fun t => (X t ω 0, Y t ω 0)) (Icc 0 t₁) :=
      fun t ht => dkPt_eq_of_lt h h0 (lt_of_le_of_lt (by exact_mod_cast ht.2) ht₁σ)
    exact ((hP t₁ ht₁σ).congr hcongr).continuousAt hmem
  · -- at the lifetime
    have hσtop : σ ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have hpos : 0 < t₀ := by
      have := dk_extinction_pos h h0
      rw [← dk_extinction_eq, ← hσ, ← heq] at this
      exact_mod_cast this
    have hval : dkPt N X Y t₀ ω = (0, 0) := dkPt_eq_of_le h h0 heq.symm.le
    refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · rw [← continuousWithinAt_Iio_iff_Iic]
      have hev : ∀ᶠ u in 𝓝[<] t₀, N u ω = 0 + 1 := eventually_nhdsWithin_of_forall
        fun u hu => (dk_level_eq_one_iff h h0 u).2 (by
          rw [← dk_extinction_eq, ← hσ, ← heq]; exact_mod_cast hu)
      have hne : N t₀ ω ≠ 0 + 1 := by
        rw [dk_level_eq_zero h h0 heq.symm.le]; norm_num
      obtain ⟨-, hx, hy, -⟩ := h.deletion t₀ hpos 0 hev hne
      have hlim : Tendsto (fun t => (X t ω 0, Y t ω 0)) (𝓝[<] t₀) (𝓝 (0, 0)) :=
        hx.prodMk_nhds hy
      rw [ContinuousWithinAt, hval]
      refine hlim.congr' (eventually_nhdsWithin_of_forall fun u hu => ?_)
      exact (dkPt_eq_of_lt h h0 (by rw [← hσ, ← heq]; exact_mod_cast hu)).symm
    · refine (continuousWithinAt_const (b := ((0 : ℝ), (0 : ℝ)))).congr (fun u hu => ?_) hval
      exact dkPt_eq_of_le h h0 (by rw [← hσ, ← heq]; exact_mod_cast hu)
  · -- after the lifetime
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, σ = τ :=
      ⟨σ.toNNReal, (ENNReal.coe_toNNReal (ne_top_of_lt hgt)).symm⟩
    have hτt : τ < t₀ := by rw [hτ] at hgt; exact_mod_cast hgt
    have hev : (fun t => dkPt N X Y t ω) =ᶠ[𝓝 t₀] fun _ => ((0 : ℝ), (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hτt] with u hu
      exact dkPt_eq_of_le h h0 (by rw [← hσ, hτ]; exact_mod_cast hu.le)
    exact (continuousAt_const).congr hev.symm

end Process

end BlockBand.Diffusion
