module

public import BlockBand.Palm.RelativeLocalizationSpectral
public import BlockBand.Palm.RelativeLocalizationLabels
public import BlockBand.Palm.RelativeLocalizationStop

/-!
# Relative localization: the closed failure set and the window geometry

* `failSet N ℓ E r₀ c₁ C₁ ⊆ ℝ^N` : the eigenvalue vectors violating the **relaxed** long-gap
  clauses (`c₁/2` instead of `c₁`, `2C₁` instead of `C₁`). It is closed (`isClosed_failSet`), so
  its hitting time by a continuous adapted process is a stopping time of the raw filtration
  (`isStoppingTime_hitTime`).
* `relaxed_of_not_mem_failSet` : outside the failure set the relaxed clauses hold, which is
  what `rlPhi_drift_le` needs (it accepts arbitrary constants).
* `not_mem_failSet_of_clauses` : the clauses of `SpectralGoodEventContract` (with
  `ℓ ≥ 1`) put the vector outside the failure set, so on the good event the stopping time
  is not reached on `[a, c]`.
* `far_of_not_window_flow` : the window geometry for two Hermitian matrices (times `a`, `s`):
  time-`a` upper count and an operator-norm displacement `‖(H_s - H_a)x‖ ≤ D₀‖x‖` give, for
  every label outside the window, `|λ_j(H_s) - E| ≥ (w+1)/(CN) - h - D₀` (Weyl).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set Matrix BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Failure set of the relaxed long-gap clauses: some long pair has
`|λ_i - λ_j| ≤ (c₁/2) d(i,j)/N`, or some short pair near `E` has `|λ_i - λ_j| ≥ 2C₁ℓ/N`. -/
def failSet (N ℓ : ℕ) (E r₀ c₁ C₁ : ℝ) : Set (Fin N → ℝ) :=
  {lam | (∃ i j : Fin N, ℓ ≤ labelDist i j ∧
      |lam i - lam j| ≤ c₁ / 2 * labelDist i j / N) ∨
    (∃ i j : Fin N, labelDist i j < ℓ ∧ min |lam i - E| |lam j - E| ≤ r₀ / 8 ∧
      2 * C₁ * ℓ / N ≤ |lam i - lam j|)}

theorem isClosed_failSet (N ℓ : ℕ) (E r₀ c₁ C₁ : ℝ) : IsClosed (failSet N ℓ E r₀ c₁ C₁) := by
  have hc : ∀ i : Fin N, Continuous fun lam : Fin N → ℝ => lam i := fun i => continuous_apply i
  have h1 : IsClosed {lam : Fin N → ℝ | ∃ i j : Fin N, ℓ ≤ labelDist i j ∧
      |lam i - lam j| ≤ c₁ / 2 * labelDist i j / N} := by
    have : {lam : Fin N → ℝ | ∃ i j : Fin N, ℓ ≤ labelDist i j ∧
        |lam i - lam j| ≤ c₁ / 2 * labelDist i j / N} =
        ⋃ i : Fin N, ⋃ j : Fin N, {lam : Fin N → ℝ | ℓ ≤ labelDist i j ∧
          |lam i - lam j| ≤ c₁ / 2 * labelDist i j / N} := by
      ext lam; simp
    rw [this]
    refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j => ?_
    by_cases hij : ℓ ≤ labelDist i j
    · simp only [hij, true_and]
      exact isClosed_le (((hc i).sub (hc j)).abs) continuous_const
    · simp [hij]
  have h2 : IsClosed {lam : Fin N → ℝ | ∃ i j : Fin N, labelDist i j < ℓ ∧
      min |lam i - E| |lam j - E| ≤ r₀ / 8 ∧ 2 * C₁ * ℓ / N ≤ |lam i - lam j|} := by
    have : {lam : Fin N → ℝ | ∃ i j : Fin N, labelDist i j < ℓ ∧
        min |lam i - E| |lam j - E| ≤ r₀ / 8 ∧ 2 * C₁ * ℓ / N ≤ |lam i - lam j|} =
        ⋃ i : Fin N, ⋃ j : Fin N, {lam : Fin N → ℝ | labelDist i j < ℓ ∧
          min |lam i - E| |lam j - E| ≤ r₀ / 8 ∧ 2 * C₁ * ℓ / N ≤ |lam i - lam j|} := by
      ext lam; simp
    rw [this]
    refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j => ?_
    by_cases hij : labelDist i j < ℓ
    · simp only [hij, true_and]
      exact (isClosed_le ((((hc i).sub continuous_const).abs).min
        (((hc j).sub continuous_const).abs)) continuous_const).inter
        (isClosed_le continuous_const (((hc i).sub (hc j)).abs))
    · simp [hij]
  exact h1.union h2

/-- Outside the failure set the relaxed clauses hold. -/
theorem relaxed_of_not_mem_failSet {ℓ : ℕ} {E r₀ c₁ C₁ : ℝ} {lam : Fin N → ℝ}
    (h : lam ∉ failSet N ℓ E r₀ c₁ C₁) :
    (∀ i j : Fin N, ℓ ≤ labelDist i j → c₁ / 2 * labelDist i j / N ≤ |lam i - lam j|) ∧
    (∀ i j : Fin N, labelDist i j < ℓ → min |lam i - E| |lam j - E| ≤ r₀ / 8 →
      |lam i - lam j| ≤ 2 * C₁ * ℓ / N) := by
  simp only [failSet, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_le] at h
  exact ⟨fun i j hij => (h.1 i j hij).le, fun i j hij hm => (h.2 i j hij hm).le⟩

/-- The two long-gap clauses of `SpectralGoodEventContract` (with `ℓ ≥ 1`, `c₁, C₁ > 0`)
put the eigenvalue vector outside the failure set. -/
theorem not_mem_failSet_of_clauses {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {E r₀ c₁ C₁ : ℝ} (hc₁ : 0 < c₁)
    (hC₁ : 0 < C₁) (hN : 0 < N) {lam : Fin N → ℝ}
    (h1 : ∀ i j : Fin N, ℓ ≤ labelDist i j → c₁ * labelDist i j / N ≤ |lam i - lam j|)
    (h2 : ∀ i j : Fin N, labelDist i j < ℓ → min |lam i - E| |lam j - E| ≤ r₀ / 8 →
      |lam i - lam j| ≤ C₁ * ℓ / N) :
    lam ∉ failSet N ℓ E r₀ c₁ C₁ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  simp only [failSet, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_le]
  refine ⟨fun i j hij => ?_, fun i j hij hm => ?_⟩
  · have hd : (1 : ℝ) ≤ labelDist i j := le_trans hℓr (by exact_mod_cast hij)
    have := h1 i j hij
    have : c₁ / 2 * labelDist i j / N < c₁ * labelDist i j / N := by
      apply div_lt_div_of_pos_right _ hNr
      nlinarith
    linarith [h1 i j hij]
  · have := h2 i j hij hm
    have : C₁ * ℓ / N < 2 * C₁ * ℓ / N := by
      apply div_lt_div_of_pos_right _ hNr
      nlinarith
    linarith

/-- **Window geometry at the matrix level** (deterministic): upper count at time `a`
plus an operator-norm displacement bound give the distance of every label outside the window
`|j - k₀| ≤ w` from `E` at time `s` (`k₀ = #{l : λ_l(a) ≤ E}`). -/
theorem far_of_not_window_flow {Ha Hs : Matrix (Fin N) (Fin N) ℂ} (hHa : Ha.IsHermitian)
    (hHs : Hs.IsHermitian) (E : ℝ) (w : ℕ) {C h D₀ : ℝ} (hC : 0 < C)
    (hcount : ∀ x y : ℝ, x ≤ y →
      ((Finset.univ.filter fun i : Fin N => freshEigenvalue Ha i ∈ Set.Icc x y).card : ℝ) ≤
        C * N * ((y - x) + h))
    (hdisp : ∀ x : Fin N → ℂ, l2Norm ((Hs - Ha) *ᵥ x) ≤ D₀ * l2Norm x) (j : Fin N)
    (hj : w < Int.natAbs ((j : ℤ) -
      ((Finset.univ.filter fun l : Fin N => freshEigenvalue Ha l ≤ E).card : ℤ))) :
    ((w : ℝ) + 1) / (C * N) - h - D₀ ≤ |freshEigenvalue Hs j - E| :=
  far_of_not_window (freshEigenvalue Ha) (freshEigenvalue Hs) (freshEigenvalue_monotone hHa)
    E w hC hcount (fun j => abs_freshEigenvalue_sub_le hHs hHa hdisp j) j hj

end BlockBand.Palm.RelativeLocalization
