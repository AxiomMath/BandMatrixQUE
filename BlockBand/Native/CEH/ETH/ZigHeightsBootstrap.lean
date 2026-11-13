module

public import BlockBand.Native.CEH.Zig.Bootstrap

/-!
# CEH ETH, two-resolvent zig: the multi-component bootstrap

This file proves a continuity (bootstrap) argument for finitely many processes at once.

Setting. Variance time `t ∈ [0, s]`, a finite index set `ι`, real functions `g_k` (e.g.
`g_k = ‖X_k‖` for complex paths, or `Z` itself for the imaginary chain) and thresholds `θ_k`,
continuous on `[0, s]`, with `g_k 0 < θ_k 0`, and improved bounds `b_k < θ_k` on `[0, s]`
(no regularity of `b_k`).

* `multi_bootstrap_of_strict`: if, for every `T ∈ [0, s]` such that all strict thresholds hold
  on `[0, T)` and all non-strict thresholds hold on `[0, T]`, the improved bounds `g_k ≤ b_k`
  hold on `[0, T]`, then `g_k ≤ b_k` and `g_k < θ_k` on all of `[0, s]`.
* `multi_bootstrap_norm_of_strict`: the same for complex paths `X_k` vanishing at `0`, with
  `g_k = ‖X_k‖` and `θ_k > 0`.
* `multi_bootstrap`: the simple form. If `‖X_k‖ ≤ θ_k` for all `k` on `[0, T]` implies
  `‖X_k‖ ≤ b_k` for all `k` on `[0, T]`, then `‖X_k‖ ≤ b_k` on `[0, s]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set

section Bootstrap

variable {ι : Type*} {s : ℝ} {g θ b : ι → ℝ → ℝ}

private theorem continuousOn_gap (hg : ∀ k, ContinuousOn (g k) (Icc 0 s))
    (hθ : ∀ k, ContinuousOn (θ k) (Icc 0 s)) :
    ContinuousOn (fun t k => g k t - θ k t) (Icc 0 s) :=
  continuousOn_pi.2 fun k => (hg k).sub (hθ k)

private theorem isClosed_thresholds (hg : ∀ k, ContinuousOn (g k) (Icc 0 s))
    (hθ : ∀ k, ContinuousOn (θ k) (Icc 0 s)) :
    IsClosed (Icc 0 s ∩ {t | ∀ k, g k t ≤ θ k t}) := by
  have hC : IsClosed {p : ι → ℝ | ∀ k, p k ≤ 0} := by
    have e : {p : ι → ℝ | ∀ k, p k ≤ 0} = ⋂ k, {p : ι → ℝ | p k ≤ 0} := by
      ext p
      simp
    rw [e]
    exact isClosed_iInter fun k => isClosed_le (continuous_apply k) continuous_const
  have h := (continuousOn_gap hg hθ).preimage_isClosed_of_isClosed isClosed_Icc hC
  convert h using 1
  ext t
  simp

private theorem isClosed_not_strict [Finite ι] (hg : ∀ k, ContinuousOn (g k) (Icc 0 s))
    (hθ : ∀ k, ContinuousOn (θ k) (Icc 0 s)) :
    IsClosed (Icc 0 s ∩ {t | ¬ ∀ k, g k t < θ k t}) := by
  have hO : IsOpen {p : ι → ℝ | ∀ k, p k < 0} := by
    have e : {p : ι → ℝ | ∀ k, p k < 0} = ⋂ k, {p : ι → ℝ | p k < 0} := by
      ext p
      simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_lt (continuous_apply k) continuous_const
  have h := (continuousOn_gap hg hθ).preimage_isClosed_of_isClosed isClosed_Icc
    hO.isClosed_compl
  convert h using 1
  ext t
  simp [sub_neg]

/-- **Multi-component bootstrap, general form.** Let `ι` be finite, `g_k, θ_k` continuous on
`[0, s]`, `g_k 0 < θ_k 0`, and `b_k t < θ_k t` on `[0, s]`. Suppose that for every
`T ∈ [0, s]`, if `g_k < θ_k` on `[0, T)` and `g_k ≤ θ_k` on `[0, T]` for all `k`, then
`g_k ≤ b_k` on `[0, T]` for all `k`. Then `g_k ≤ b_k` and `g_k < θ_k` on all of `[0, s]`. -/
theorem multi_bootstrap_of_strict [Finite ι] (hg : ∀ k, ContinuousOn (g k) (Icc 0 s))
    (hθ : ∀ k, ContinuousOn (θ k) (Icc 0 s)) (h0 : ∀ k, g k 0 < θ k 0)
    (hbθ : ∀ k, ∀ t ∈ Icc 0 s, b k t < θ k t)
    (hstep : ∀ T ∈ Icc 0 s, (∀ k, ∀ r ∈ Ico 0 T, g k r < θ k r) →
      (∀ k, ∀ r ∈ Icc 0 T, g k r ≤ θ k r) → ∀ k, ∀ t ∈ Icc 0 T, g k t ≤ b k t) :
    ∀ k, ∀ t ∈ Icc 0 s, g k t ≤ b k t ∧ g k t < θ k t := by
  intro k₀ t₀ ht₀
  have hs : 0 ≤ s := ht₀.1.trans ht₀.2
  have hall : ∀ t ∈ Icc (0 : ℝ) s, ∀ k, g k t < θ k t := by
    by_contra hne
    push Not at hne
    obtain ⟨t₁, ht₁, k₁, hk₁⟩ := hne
    set Fs := Icc (0 : ℝ) s ∩ {t | ¬ ∀ k, g k t < θ k t} with hFs
    have hFcl : IsClosed Fs := isClosed_not_strict hg hθ
    have hFne : Fs.Nonempty := ⟨t₁, ht₁, fun h => (h k₁).not_ge hk₁⟩
    have hFbdd : BddBelow Fs := ⟨0, fun x hx => hx.1.1⟩
    have hτ : sInf Fs ∈ Fs := hFcl.csInf_mem hFne hFbdd
    set τ := sInf Fs with hτdef
    have hbelow : ∀ k, ∀ r ∈ Ico 0 τ, g k r < θ k r := by
      intro k r hr
      by_contra hnr
      have hmem : r ∈ Fs := ⟨⟨hr.1, hr.2.le.trans hτ.1.2⟩, fun h => hnr (h k)⟩
      have := csInf_le hFbdd hmem
      linarith [hr.2]
    have hτpos : 0 < τ := by
      rcases eq_or_lt_of_le hτ.1.1 with h | h
      · exact absurd (h ▸ h0) hτ.2
      · exact h
    have hthrτ : ∀ k, ∀ r ∈ Icc 0 τ, g k r ≤ θ k r := by
      have hsub : Ico 0 τ ⊆ Icc (0 : ℝ) s ∩ {t | ∀ k, g k t ≤ θ k t} :=
        fun r hr => ⟨⟨hr.1, hr.2.le.trans hτ.1.2⟩, fun k => (hbelow k r hr).le⟩
      have hcl := ((isClosed_thresholds hg hθ).closure_subset_iff).2 hsub
      rw [closure_Ico hτpos.ne] at hcl
      exact fun k r hr => (hcl hr).2 k
    have hb := hstep τ hτ.1 hbelow hthrτ
    exact hτ.2 fun k => (hb k τ ⟨hτpos.le, le_rfl⟩).trans_lt (hbθ k τ hτ.1)
  exact ⟨hstep s ⟨hs, le_rfl⟩ (fun k r hr => hall r ⟨hr.1, hr.2.le⟩ k)
    (fun k r hr => (hall r hr k).le) k₀ t₀ ht₀, hall t₀ ht₀ k₀⟩

end Bootstrap

section Norm

variable {ι : Type*} {s : ℝ} {X : ι → ℝ → ℂ} {θ b : ι → ℝ → ℝ}

/-- **Multi-component bootstrap for complex paths, with strict information.** Let `ι` be
finite, `X_k` complex, continuous on `[0, s]`, `X_k 0 = 0`, thresholds `θ_k` continuous and
positive on `[0, s]`, and `b_k < θ_k` on `[0, s]`. Suppose that for every `T ∈ [0, s]`, if
`‖X_k‖ < θ_k` on `[0, T)` and `‖X_k‖ ≤ θ_k` on `[0, T]` for all `k`, then `‖X_k‖ ≤ b_k` on
`[0, T]` for all `k`. Then `‖X_k‖ ≤ b_k` and `‖X_k‖ < θ_k` on all of `[0, s]`. -/
theorem multi_bootstrap_norm_of_strict [Finite ι] (hX : ∀ k, ContinuousOn (X k) (Icc 0 s))
    (hX0 : ∀ k, X k 0 = 0) (hθ : ∀ k, ContinuousOn (θ k) (Icc 0 s))
    (hθpos : ∀ k, ∀ t ∈ Icc 0 s, 0 < θ k t) (hbθ : ∀ k, ∀ t ∈ Icc 0 s, b k t < θ k t)
    (hstep : ∀ T ∈ Icc 0 s, (∀ k, ∀ r ∈ Ico 0 T, ‖X k r‖ < θ k r) →
      (∀ k, ∀ r ∈ Icc 0 T, ‖X k r‖ ≤ θ k r) → ∀ k, ∀ t ∈ Icc 0 T, ‖X k t‖ ≤ b k t) :
    ∀ k, ∀ t ∈ Icc 0 s, ‖X k t‖ ≤ b k t ∧ ‖X k t‖ < θ k t := by
  intro k t ht
  have hs : 0 ≤ s := ht.1.trans ht.2
  exact multi_bootstrap_of_strict (g := fun k t => ‖X k t‖) (fun k => (hX k).norm) hθ
    (fun k => by simpa [hX0 k] using hθpos k 0 ⟨le_rfl, hs⟩) hbθ hstep k t ht

/-- **Multi-component bootstrap, simple form** (the bootstrap behind CEH (7.3)). Let `ι` be
finite, `X_k` complex, continuous on `[0, s]`, `X_k 0 = 0`, thresholds `θ_k` continuous and
positive on `[0, s]`, and `b_k < θ_k` on `[0, s]`. If, for every `T ∈ [0, s]`, `‖X_k‖ ≤ θ_k` on
`[0, T]` for all `k` implies `‖X_k‖ ≤ b_k` on `[0, T]` for all `k`, then `‖X_k‖ ≤ b_k` on all of
`[0, s]`. -/
theorem multi_bootstrap [Finite ι] (hX : ∀ k, ContinuousOn (X k) (Icc 0 s))
    (hX0 : ∀ k, X k 0 = 0) (hθ : ∀ k, ContinuousOn (θ k) (Icc 0 s))
    (hθpos : ∀ k, ∀ t ∈ Icc 0 s, 0 < θ k t) (hbθ : ∀ k, ∀ t ∈ Icc 0 s, b k t < θ k t)
    (hstep : ∀ T ∈ Icc 0 s, (∀ k, ∀ t ∈ Icc 0 T, ‖X k t‖ ≤ θ k t) →
      ∀ k, ∀ t ∈ Icc 0 T, ‖X k t‖ ≤ b k t) :
    ∀ k, ∀ t ∈ Icc 0 s, ‖X k t‖ ≤ b k t := fun k t ht =>
  (multi_bootstrap_norm_of_strict hX hX0 hθ hθpos hbθ (fun T hT _ h => hstep T hT h) k t ht).1

end Norm

end BlockBand.Native.CEH.ETH
