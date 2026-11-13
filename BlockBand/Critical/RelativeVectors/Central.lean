module

public import BlockBand.Critical.RelativeVectors.DiagonalFrame
public import BlockBand.Palm.RelativeLocalizationLabels

/-!
# The central window and the `(t+ρ) → (t+w/N)` conversion

* `rank_lt_iff`: for monotone eigenvalues, `l < k₀ ↔ λ_l ≤ E`, `k₀ = #{l : λ_l ≤ E}`;
* `central_close`: the bulk lower count (clause 3) at one time gives, for `|j - k₀| ≤ w`,
  `|λ_j - E| ≤ d := 2 max((w+1)/(c₁N), ℓ/N)` provided `d ≤ r₀/8`;
* `centralRho`, `centralRho_le`: `ρ = d + C√t ≤ (4/c₁ + C)(w/N) + 2ℓ/N` once `√t ≤ w/N` and
  `w ≥ 1` (both hold for `w = ⌈N√t N^{2ε}⌉`: `rmv_sqrt_le_w`, `rmv_w_pos`), hence
  `(N/ℓ)(ρ + t) ≤ (4/c₁ + C + 1)(N/ℓ)(t + w/N) + 2` (`centralRho_variation_le`);
* `centralRho_small`: `ρ ≤ r₀/8` for all large `N` at the critical scales;
* `diagonal_central_le`: the diagonal relative error bound
  `C[N M/ℓ² + (N/ℓ)(t + w/N) + log N]` for every central label `j`, on the clause-3 (time `a`),
  clause-1 and clause-5 (time `s`) events and the interval and distant-label events.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset Set Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.CoarseRelative

variable {N r : ℕ}

/-- `k₀ = #{l : λ_l ≤ E}` is the rank of the first eigenvalue above `E`: `l < k₀ ↔ λ_l ≤ E`. -/
theorem rank_lt_iff {lam : Fin N → ℝ} (hlam : Monotone lam) (E : ℝ) (l : Fin N) :
    l.val < (univ.filter fun i : Fin N => lam i ≤ E).card ↔ lam l ≤ E := by
  constructor
  · intro hl
    by_contra hc
    rw [not_le] at hc
    have hsub : (univ.filter fun i : Fin N => lam i ≤ E) ⊆ Finset.Iio l := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_Iio]
      by_contra hil
      have := hlam (not_lt.mp hil)
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hl
    have hsub : Finset.Iic l ⊆ (univ.filter fun i : Fin N => lam i ≤ E) := by
      intro i hi
      rw [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hlam hi).trans hl
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

/-- Labels with values in `[x, y]`, `x > E`, `y < λ_j`, have ranks in `[k₀, j)`. -/
theorem card_window_right {lam : Fin N → ℝ} (hlam : Monotone lam) (E : ℝ) (j : Fin N)
    {x y : ℝ} (hx : E < x) (hy : y < lam j) :
    (univ.filter fun i : Fin N => lam i ∈ Icc x y).card ≤
      j.val - (univ.filter fun i : Fin N => lam i ≤ E).card := by
  set k₀ := (univ.filter fun i : Fin N => lam i ≤ E).card
  have hsub : ((univ.filter fun i : Fin N => lam i ∈ Icc x y).image Fin.val) ⊆
      Finset.Ico k₀ j.val := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
      at hn
    obtain ⟨i, ⟨hix, hiy⟩, rfl⟩ := hn
    rw [Finset.mem_Ico]
    constructor
    · by_contra hc
      have := (rank_lt_iff hlam E i).mp (not_le.mp hc)
      linarith
    · by_contra hc
      have := hlam (show j ≤ i from not_lt.mp hc)
      linarith
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at this
  exact this

/-- Labels with values in `[x, y]`, `x > λ_j`, `y ≤ E`, have ranks in `(j, k₀)`. -/
theorem card_window_left {lam : Fin N → ℝ} (hlam : Monotone lam) (E : ℝ) (j : Fin N)
    {x y : ℝ} (hx : lam j < x) (hy : y ≤ E) :
    (univ.filter fun i : Fin N => lam i ∈ Icc x y).card ≤
      (univ.filter fun i : Fin N => lam i ≤ E).card - j.val := by
  set k₀ := (univ.filter fun i : Fin N => lam i ≤ E).card
  have hsub : ((univ.filter fun i : Fin N => lam i ∈ Icc x y).image Fin.val) ⊆
      Finset.Ico j.val k₀ := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
      at hn
    obtain ⟨i, ⟨hix, hiy⟩, rfl⟩ := hn
    rw [Finset.mem_Ico]
    constructor
    · by_contra hc
      have := hlam (show i ≤ j from (not_le.mp hc).le)
      linarith
    · exact (rank_lt_iff hlam E i).mpr (by linarith)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at this
  exact this

/-- Half-width `d = 2 max((w+1)/(c₁N), ℓ/N)` of the central window in energy. -/
def centralWidth (N w ℓ : ℕ) (c₁ : ℝ) : ℝ :=
  2 * max (((w : ℝ) + 1) / (c₁ * N)) ((ℓ : ℝ) / N)

/-- **Central labels are close to `E`** (one time). The bulk lower count (clause 3 of
`SpectralGoodEventContract`) gives `|λ_j - E| ≤ d` for every `j` with `|j - k₀| ≤ w`, provided
`d ≤ r₀/8`. -/
theorem central_close {lam : Fin N → ℝ} (hlam : Monotone lam) {E r₀ c₁ : ℝ} {ℓ w : ℕ}
    (hN : 0 < N) (hc₁ : 0 < c₁)
    (hlow : ∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      c₁ * N * (y - x) ≤ ((univ.filter fun i : Fin N => lam i ∈ Icc x y).card : ℝ))
    (hd : centralWidth N w ℓ c₁ ≤ r₀ / 8) (j : Fin N)
    (hj : Int.natAbs ((j : ℤ) - ((univ.filter fun l : Fin N => lam l ≤ E).card : ℤ)) ≤ w) :
    |lam j - E| ≤ centralWidth N w ℓ c₁ := by
  set k₀ := (univ.filter fun i : Fin N => lam i ≤ E).card with hk₀
  set d := centralWidth N w ℓ c₁ with hddef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set m := max (((w : ℝ) + 1) / (c₁ * N)) ((ℓ : ℝ) / N) with hm
  have hm1 : ((w : ℝ) + 1) / (c₁ * N) ≤ m := le_max_left _ _
  have hm2 : (ℓ : ℝ) / N ≤ m := le_max_right _ _
  have hdm : d = 2 * m := rfl
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm1
  -- `c₁ N m ≥ w + 1`
  have hcm : (w : ℝ) + 1 ≤ c₁ * N * m := by
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ c₁ * N)
    rwa [mul_div_cancel₀ _ (by positivity : (c₁ * N : ℝ) ≠ 0)] at this
  rw [abs_le]
  by_cases hjE : lam j ≤ E
  · refine ⟨?_, by linarith⟩
    by_contra hc
    rw [not_le] at hc
    have hjk : j.val < k₀ := (rank_lt_iff hlam E j).mpr hjE
    have hw : k₀ - j.val ≤ w := by omega
    have hcount := hlow (E - d) (E - d / 2) (by linarith) (by linarith)
      (by rw [hdm]; linarith)
    have hcard := card_window_left hlam E j (x := E - d) (y := E - d / 2) (by linarith)
      (by linarith)
    have hcard' : ((univ.filter fun i : Fin N => lam i ∈ Icc (E - d) (E - d / 2)).card : ℝ) ≤
        w := by
      have : (univ.filter fun i : Fin N => lam i ∈ Icc (E - d) (E - d / 2)).card ≤ w :=
        hcard.trans hw
      exact_mod_cast this
    have : c₁ * N * (E - d / 2 - (E - d)) = c₁ * N * m := by rw [hdm]; ring
    linarith
  · rw [not_le] at hjE
    refine ⟨by linarith, ?_⟩
    by_contra hc
    rw [not_le] at hc
    have hjk : k₀ ≤ j.val := by
      by_contra h'
      exact absurd ((rank_lt_iff hlam E j).mp (not_le.mp h')) (not_le.mpr hjE)
    have hw : j.val - k₀ ≤ w := by omega
    have hcount := hlow (E + d / 2) (E + d) (by linarith) (by linarith)
      (by rw [hdm]; linarith)
    have hcard := card_window_right hlam E j (x := E + d / 2) (y := E + d) (by linarith)
      (by linarith)
    have hcard' : ((univ.filter fun i : Fin N => lam i ∈ Icc (E + d / 2) (E + d)).card : ℝ) ≤
        w := by
      have : (univ.filter fun i : Fin N => lam i ∈ Icc (E + d / 2) (E + d)).card ≤ w :=
        hcard.trans hw
      exact_mod_cast this
    have : c₁ * N * (E + d - (E + d / 2)) = c₁ * N * m := by rw [hdm]; ring
    linarith

/-- **Central labels along the flow.** Lower count at time `a` (matrix `Ha`) and the operator
displacement `‖(Hs - Ha)x‖ ≤ D₀‖x‖` (clause 5) give `|λ_j(Hs) - E| ≤ d + D₀` for every central
label `j` (`|j - k₀| ≤ w`, `k₀` counted at time `a`). -/
theorem central_close_flow {Ha Hs : Matrix (Fin N) (Fin N) ℂ} (hHa : Ha.IsHermitian)
    (hHs : Hs.IsHermitian) {E r₀ c₁ D₀ : ℝ} {ℓ w : ℕ} (hN : 0 < N) (hc₁ : 0 < c₁)
    (hlow : ∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      c₁ * N * (y - x) ≤
        ((univ.filter fun i : Fin N => freshEigenvalue Ha i ∈ Icc x y).card : ℝ))
    (hdisp : ∀ x : Fin N → ℂ, l2Norm ((Hs - Ha) *ᵥ x) ≤ D₀ * l2Norm x)
    (hd : centralWidth N w ℓ c₁ ≤ r₀ / 8) (j : Fin N)
    (hj : Int.natAbs ((j : ℤ) -
      ((univ.filter fun l : Fin N => freshEigenvalue Ha l ≤ E).card : ℤ)) ≤ w) :
    |freshEigenvalue Hs j - E| ≤ centralWidth N w ℓ c₁ + D₀ := by
  have h1 := central_close (BlockBand.Palm.RelativeLocalization.freshEigenvalue_monotone hHa)
    hN hc₁ hlow hd j hj
  have h2 := BlockBand.Palm.RelativeLocalization.abs_freshEigenvalue_sub_le hHs hHa hdisp j
  calc |freshEigenvalue Hs j - E|
      = |(freshEigenvalue Hs j - freshEigenvalue Ha j) + (freshEigenvalue Ha j - E)| := by
        ring_nf
    _ ≤ |freshEigenvalue Hs j - freshEigenvalue Ha j| + |freshEigenvalue Ha j - E| :=
        abs_add_le _ _
    _ ≤ D₀ + centralWidth N w ℓ c₁ := add_le_add h2 h1
    _ = centralWidth N w ℓ c₁ + D₀ := add_comm _ _

/-!
## The scale conversion
-/

/-- `ρ = 2 max((w+1)/(c₁N), ℓ/N) + C√t`, the radius of the central labels at every time. -/
def centralRho (N w ℓ : ℕ) (c₁ C t : ℝ) : ℝ := centralWidth N w ℓ c₁ + C * Real.sqrt t

/-- `ρ ≤ (4/c₁ + C)(w/N) + 2ℓ/N`, once `1 ≤ w` and `√t ≤ w/N`. -/
theorem centralRho_le {w ℓ : ℕ} {c₁ C t : ℝ} (hN : 0 < N) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    (hw : 1 ≤ w) (hsq : Real.sqrt t ≤ (w : ℝ) / N) :
    centralRho N w ℓ c₁ C t ≤ (4 / c₁ + C) * ((w : ℝ) / N) + 2 * ((ℓ : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  unfold centralRho centralWidth
  have hmax : max (((w : ℝ) + 1) / (c₁ * N)) ((ℓ : ℝ) / N) ≤
      ((w : ℝ) + 1) / (c₁ * N) + (ℓ : ℝ) / N :=
    max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
  have h1 : ((w : ℝ) + 1) / (c₁ * N) ≤ 2 / c₁ * ((w : ℝ) / N) := by
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have h2 : C * Real.sqrt t ≤ C * ((w : ℝ) / N) := mul_le_mul_of_nonneg_left hsq hC
  have e : (4 / c₁ + C) * ((w : ℝ) / N) = 2 * (2 / c₁ * ((w : ℝ) / N)) + C * ((w : ℝ) / N) := by
    ring
  rw [e]
  linarith

/-- `(N/ℓ)(ρ + t) ≤ (4/c₁ + C + 1)(N/ℓ)(t + w/N) + 2`: the `(t+ρ)` form of `diagonal_frame_le`
gives `(N/ℓ)(t + w/N)`, up to a constant and an additive `2` (absorbed in `log N`). -/
theorem centralRho_variation_le {w ℓ : ℕ} {c₁ C t : ℝ} (hN : 0 < N) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ) (ht : 0 ≤ t) (hw : 1 ≤ w) (hsq : Real.sqrt t ≤ (w : ℝ) / N) :
    (N : ℝ) * (centralRho N w ℓ c₁ C t + t) / ℓ ≤
      (4 / c₁ + C + 1) * ((N : ℝ) / ℓ * (t + (w : ℝ) / N)) + 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h := centralRho_le (ℓ := ℓ) hN hc₁ hC hw hsq
  have hK : 0 ≤ 4 / c₁ + C := by positivity
  have hwN : 0 ≤ (w : ℝ) / N := by positivity
  have hNℓ : 0 ≤ (N : ℝ) / ℓ := by positivity
  have e1 : (N : ℝ) * (centralRho N w ℓ c₁ C t + t) / ℓ =
      (N : ℝ) / ℓ * (centralRho N w ℓ c₁ C t + t) := by ring
  have e2 : (N : ℝ) / ℓ * (2 * ((ℓ : ℝ) / N)) = 2 := by field_simp
  rw [e1]
  calc (N : ℝ) / ℓ * (centralRho N w ℓ c₁ C t + t)
      ≤ (N : ℝ) / ℓ * ((4 / c₁ + C) * ((w : ℝ) / N) + 2 * ((ℓ : ℝ) / N) + t) :=
        mul_le_mul_of_nonneg_left (by linarith) hNℓ
    _ = (N : ℝ) / ℓ * ((4 / c₁ + C) * ((w : ℝ) / N) + t) + 2 := by
        have : (N : ℝ) / ℓ * ((4 / c₁ + C) * ((w : ℝ) / N) + 2 * ((ℓ : ℝ) / N) + t) =
            (N : ℝ) / ℓ * ((4 / c₁ + C) * ((w : ℝ) / N) + t) +
              (N : ℝ) / ℓ * (2 * ((ℓ : ℝ) / N)) := by ring
        rw [this, e2]
    _ ≤ (N : ℝ) / ℓ * ((4 / c₁ + C + 1) * (t + (w : ℝ) / N)) + 2 := by
        gcongr
        nlinarith
    _ = (4 / c₁ + C + 1) * ((N : ℝ) / ℓ * (t + (w : ℝ) / N)) + 2 := by ring

/-!
## The critical scales
-/

/-- `w = ⌈N√t N^{2ε}⌉ ≥ 1` for `N ≥ 1`. -/
theorem rmv_w_pos {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
      (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 < (N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ)) := by
    have := Real.rpow_pos_of_pos hN0 (-(1 / 500 : ℝ))
    positivity
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr this).ne'

/-- `√t ≤ w/N` for `w = ⌈N√t N^{2ε}⌉`, `N ≥ 1`. -/
theorem rmv_sqrt_le_w {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) ≤
      (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
        (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [le_div_iff₀ hN0]
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ (2 * (1 / 10000 : ℝ)) := Real.one_le_rpow hN1 (by norm_num)
  have hs : 0 ≤ Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) := Real.sqrt_nonneg _
  calc Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * N
      ≤ (N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hp
          (by positivity : (0 : ℝ) ≤ (N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))))
        linarith
    _ ≤ _ := Nat.le_ceil _

/-- `w/N → 0` at the critical scales: `w/N ≤ N^{-1/1000 + 2/10000} + 1/N`. -/
theorem rmv_w_div_le {N : ℕ} (hN : 1 ≤ N) :
    (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
        (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) / N ≤
      (N : ℝ) ^ (-(8 / 10000 : ℝ)) + 1 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) = (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    norm_num
  have e : (N : ℝ) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ)) =
      (N : ℝ) ^ (-(8 / 10000 : ℝ)) * N := by
    rw [mul_comm ((N : ℝ) ^ (-(8 / 10000 : ℝ))), mul_assoc, ← Real.rpow_add hN0]
    norm_num
  rw [hsq, e, div_le_iff₀ hN0]
  have hc := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (N : ℝ) ^ (-(8 / 10000 : ℝ)) * N by
    positivity)).le
  have e2 : ((N : ℝ) ^ (-(8 / 10000 : ℝ)) + 1 / N) * N = (N : ℝ) ^ (-(8 / 10000 : ℝ)) * N + 1 := by
    field_simp
  rw [e2]
  exact hc

/-- **`ρ ≤ r₀/8` for large `N`** at the critical scales (`t = N^{-1/500}`, `ℓ = ⌊N^{1-13/5000}⌋`,
`w = ⌈N√t N^{2ε}⌉`), for fixed `c₁ > 0`, `C ≥ 0`, `r₀ > 0`. -/
theorem centralRho_small {c₁ C r₀ : ℝ} (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hr₀ : 0 < r₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      centralRho N (⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
          (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊) ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ c₁ C
        ((N : ℝ) ^ (-(1 / 500 : ℝ))) ≤ r₀ / 8 := by
  open Filter Topology in
  have hlim : Tendsto (fun N : ℕ => (4 / c₁ + C) * ((N : ℝ) ^ (-(8 / 10000 : ℝ)) + 1 / N) +
      2 * (N : ℝ) ^ (-(13 / 5000 : ℝ))) atTop (𝓝 ((4 / c₁ + C) * (0 + 0) + 2 * 0)) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(8 / 10000 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h3 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(13 / 5000 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact ((h1.add h2).const_mul _).add (h3.const_mul _)
  simp only [add_zero, mul_zero] at hlim
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < r₀ / 8 by positivity)))
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hρ := centralRho_le (N := N) (ℓ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊) hN0 hc₁ hC
    (rmv_w_pos hN1) (rmv_sqrt_le_w hN1)
  have hw := rmv_w_div_le hN1
  have hl : (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) / N ≤ (N : ℝ) ^ (-(13 / 5000 : ℝ)) := by
    rw [div_le_iff₀ hNr]
    refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
    rw [show (N : ℝ) ^ (-(13 / 5000 : ℝ)) * N = (N : ℝ) ^ (-(13 / 5000 : ℝ)) * (N : ℝ) ^ (1 : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hNr]
    norm_num
  have hK : 0 ≤ 4 / c₁ + C := by positivity
  have := hN₁ N (le_trans (le_max_left _ _) hN)
  nlinarith [mul_le_mul_of_nonneg_left hw hK]

/-!
## The diagonal relative error for the central labels
-/

/-- **The diagonal relative error bound for central labels** (`|j - k₀| ≤ w`).

Deterministic, at one time `s ∈ [c - t, c]` (`c - s₀ ≤ s`), for the flow matrices `Ha = H_a`,
`H = H_s` (Hermitian, `H_s` with strictly increasing eigenvalues), `k₀ = #{l : λ_l(a) ≤ E}`.
Hypotheses: the bulk lower count at time `a` (clause 3), the displacement `‖H_s - H_a‖ ≤ C√t`
(clause 5), the long gaps at time `s` (clause 1), the middle line of the interval bound with
bound `M‖p‖²` and the distant-label bound with `C_d‖p‖²` at time `s`, and `ρ = centralRho ≤ r₀/8`
(true for large `N`: `centralRho_small`); `1 ≤ w`, `√t ≤ w/N` (`rmv_w_pos`, `rmv_sqrt_le_w`).
Conclusion, for every `j` with `|j - k₀| ≤ w`:
`|p^*Δ_jp| ≤ [2NM/(c₁²ℓ²) + C_γ(2(1+log N)/c₁ + (4/c₁²)((4/c₁+C+1)(N/ℓ)(t+w/N) + 2))
  + C_d + 64/r₀²] ‖p‖²`,
i.e. `C_r[N^{2-α+ε}/ℓ² + (N/ℓ)(t + w/N) + log N]` for `M = C_r N^{1-α+ε}`. -/
theorem diagonal_central_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {s t : ℝ}
    (hs : s ∈ Icc (c - s₀) c) (hst : c - t ≤ s) (ht : 0 ≤ t)
    {Ha H : Matrix (Fin N) (Fin N) ℂ} (hHa : Ha.IsHermitian) (hH : H.IsHermitian)
    (hlam : StrictMono (freshEigenvalue H)) {c₁ Cdisp M Cd : ℝ} (hc₁ : 0 < c₁)
    (hCdisp : 0 ≤ Cdisp) {ℓ w : ℕ} (hℓ : 1 ≤ ℓ) (hw : 1 ≤ w)
    (hsq : Real.sqrt t ≤ (w : ℝ) / N) (hρ8 : centralRho N w ℓ c₁ Cdisp t ≤ r₀ / 8)
    (hlow : ∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      c₁ * N * (y - x) ≤
        ((univ.filter fun i : Fin N => freshEigenvalue Ha i ∈ Icc x y).card : ℝ))
    (hdisp : ∀ x : Fin N → ℂ, l2Norm ((H - Ha) *ᵥ x) ≤ Cdisp * Real.sqrt t * l2Norm x)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * labelDist i j / N ≤ |freshEigenvalue H i - freshEigenvalue H j|)
    (p : Fin r → ℂ)
    (hS1 : ∀ x y, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 →
      |∑ i ∈ univ.filter (fun i => freshEigenvalue H i ∈ Icc x y),
          (‖star p ⬝ᵥ frameArray V H i‖ ^ 2 -
            quadForm (freshGamma F s (freshEigenvalue H i)) (V *ᵥ p))| ≤ M * nsq p)
    (j : Fin N)
    (hj : Int.natAbs ((j : ℤ) -
      ((univ.filter fun l : Fin N => freshEigenvalue Ha l ≤ E).card : ℤ)) ≤ w)
    (hS2 : ∑ i ∈ univ.filter (fun i => r₀ / 4 < |freshEigenvalue H i - E|),
      ‖star p ⬝ᵥ frameArray V H i‖ ^ 2 /
        ((N : ℝ) * (freshEigenvalue H i - freshEigenvalue H j) ^ 2) ≤ Cd * ∑ b, ‖p b‖ ^ 2) :
    |∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist i j),
        (‖star p ⬝ᵥ frameArray V H i‖ ^ 2 - nsq p) /
          (N * (freshEigenvalue H i - freshEigenvalue H j) ^ 2)| ≤
      (2 * (M * (N / (c₁ ^ 2 * ℓ ^ 2))) +
        gammaShiftConst c r₀ s₀ v₀ * (2 * (1 + Real.log N) / c₁ +
          4 / c₁ ^ 2 * ((4 / c₁ + Cdisp + 1) * ((N : ℝ) / ℓ * (t + (w : ℝ) / N)) + 2)) +
        Cd + 64 / r₀ ^ 2) * nsq p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hd : centralWidth N w ℓ c₁ ≤ r₀ / 8 := by
    have : 0 ≤ Cdisp * Real.sqrt t := by positivity
    unfold centralRho at hρ8; linarith
  have hρj : |freshEigenvalue H j - E| ≤ centralRho N w ℓ c₁ Cdisp t := by
    have := central_close_flow hHa hH hN hc₁ hlow (D₀ := Cdisp * Real.sqrt t) hdisp hd j hj
    exact this
  have h := diagonal_frame_le hN hK hC hV hs hst ht hlam hc₁ j hℓ hρj hρ8
    (fun i hi => hgap i j hi) p hS1 hS2
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg p))
  have hCγ : 0 ≤ gammaShiftConst c r₀ s₀ v₀ := by
    have hκ'0 : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
    have hv0 := hK.2.2.2.2.2
    have hc0 := hK.1
    have hs0 := hK.2.2.2.1
    have hr₀ := hK.2.2.1
    unfold gammaShiftConst
    positivity
  have hv := centralRho_variation_le (ℓ := ℓ) hN hc₁ hCdisp hℓ ht hw hsq
  have e : 4 * (N : ℝ) * (centralRho N w ℓ c₁ Cdisp t + t) / (c₁ ^ 2 * ℓ) =
      4 / c₁ ^ 2 * ((N : ℝ) * (centralRho N w ℓ c₁ Cdisp t + t) / ℓ) := by
    field_simp
  rw [e]
  have : 4 / c₁ ^ 2 * ((N : ℝ) * (centralRho N w ℓ c₁ Cdisp t + t) / ℓ) ≤
      4 / c₁ ^ 2 * ((4 / c₁ + Cdisp + 1) * ((N : ℝ) / ℓ * (t + (w : ℝ) / N)) + 2) :=
    mul_le_mul_of_nonneg_left hv (by positivity)
  nlinarith

end BlockBand.Critical.RelativeVectors
