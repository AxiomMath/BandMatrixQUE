module

public import BlockBand.Palm.MomentFlow.RemUnif

/-!
# The short generator at an extremal configuration (deterministic)

Notation. `c` is a short rate matrix (`c_ij ≥ 0`, `c_ij = 0` for `labelDist i j ≥ ℓ`), `K` a
nonnegative kernel with `K_ij ≤ η c_ij` on short pairs (for the flow:
`K_ij = N⁻¹η/((λ_i-λ_j)²+η²) ≤ η/(N(λ_i-λ_j)²)`, i.e. `remKernel`), `f ≥ 0` on the `r`-sector,
and `remSum K f ξ i = Σ_j K_ij remCoef(ξ,i,j) f(remTarget(ξ,i,j))` the restored resolvent sum of
the removal identity.

* **`maxStep`**: at a maximizer `ξ` of `f` on the sector, with `M = f ξ`,
  `η 𝓢f(ξ) ≤ Σ_i ξ_i (remSum K f ξ i - M Σ_j K_ij) + (r+1) M Σ_i ξ_i Σ_{|j-i|≥ℓ} K_ij`.
  (Occupied destinations are discarded since every jump lowers `f`; `c_ij` is replaced by the
  smaller kernel `K_ij/η`; the short sum is extended to all destinations.)
* **`minStep`**: at a minimizer, with `m = f ξ ≥ 0`, `f ≤ G` on the sector and `K ≤ Kmax`,
  `η 𝓢f(ξ) ≥ Σ_i ξ_i (remSum - m Σ_j K_ij) - Σ_i ξ_i (m r Kmax + (r+1) G Σ_{long} K_ij)`.
* **`maxStep_damped`**, **`minStep_damped`**: inserting the averaged identity
  `|remSum - V_i(aΨ_i + 1 - a)| ≤ e₁`, the averaged law `|Σ_j K_ij - V_i| ≤ e₂`, the long kernel
  bound `Σ_{long} K_ij ≤ e₃` and the induction hypothesis `|Ψ_i - 1| ≤ e₄` with `v ≤ V_i ≤ V̄`:
  `η 𝓢f(ξ) ≤ -r v (M - 1) + r (e₁ + V̄ e₄ + G e₂ + (r+1) G e₃)` if `1 ≤ M ≤ G`, and
  `η 𝓢f(ξ) ≥ r v (1 - m) - r (e₁ + V̄ e₄ + e₂ + r Kmax + (r+1) G e₃)` if `0 ≤ m ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- The restored resolvent sum `Σ_j K_ij remCoef(ξ,i,j) f(remTarget(ξ,i,j))`. -/
def remSum (K : Fin N → Fin N → ℝ) (f : Occ N → ℝ) (ξ : Occ N) (i : Fin N) : ℝ :=
  ∑ j, K i j * remCoef ξ i j * f (remTarget ξ i j)

/-- The long part of the kernel row: `Σ_{labelDist i j ≥ ℓ} K_ij`. -/
def longKer (K : Fin N → Fin N → ℝ) (ℓ : ℕ) (i : Fin N) : ℝ :=
  ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j), K i j

theorem longKer_nonneg {K : Fin N → Fin N → ℝ} (hK : ∀ i j, 0 ≤ K i j) (ℓ : ℕ) (i : Fin N) :
    0 ≤ longKer K ℓ i :=
  Finset.sum_nonneg fun j _ => hK i j

/-- Split of the restored sum at an occupied label: `remSum = K_ii ξ_i f ξ + Σ_{j≠i} …`. -/
theorem remSum_split (K : Fin N → Fin N → ℝ) (f : Occ N → ℝ) (ξ : Occ N) (i : Fin N) :
    remSum K f ξ i = K i i * (ξ i : ℝ) * f ξ +
      ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * f (move ξ i j) := by
  unfold remSum
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  congr 1
  · simp [remCoef, remTarget]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := (mem_erase.1 hj).1
    simp [remCoef, remTarget, hji]

theorem sum_erase_add_diag (K : Fin N → Fin N → ℝ) (i : Fin N) :
    ∑ j, K i j = K i i + ∑ j ∈ univ.erase i, K i j :=
  (Finset.add_sum_erase _ _ (mem_univ i)).symm

/-- Long row sum restricted to `j ≠ i`, with the weights `1 + ξ_j ≤ 1 + r`. -/
theorem long_weighted_le {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {K : Fin N → Fin N → ℝ}
    (hK : ∀ i j, 0 ≤ K i j) (ℓ : ℕ) (i : Fin N) :
    ∑ j ∈ univ.erase i, (if ℓ ≤ labelDist i j then K i j * ((ξ j : ℝ) + 1) else 0) ≤
      ((r : ℝ) + 1) * longKer K ℓ i := by
  have hξj : ∀ j, (ξ j : ℝ) ≤ r := by
    intro j
    rw [mem_sector] at hξ
    have : ξ j ≤ r := hξ ▸ Finset.single_le_sum (fun k _ => Nat.zero_le (ξ k)) (mem_univ j)
    exact_mod_cast this
  calc ∑ j ∈ univ.erase i, (if ℓ ≤ labelDist i j then K i j * ((ξ j : ℝ) + 1) else 0)
      ≤ ∑ j, (if ℓ ≤ labelDist i j then K i j * ((r : ℝ) + 1) else 0) := by
        refine (Finset.sum_le_sum fun j _ => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (erase_subset i univ) fun j _ _ => ?_)
        · split_ifs
          · exact mul_le_mul_of_nonneg_left (by linarith [hξj j]) (hK i j)
          · exact le_rfl
        · split_ifs
          · exact mul_nonneg (hK i j) (by positivity)
          · exact le_rfl
    _ = ((r : ℝ) + 1) * longKer K ℓ i := by
        unfold longKer
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring

/-- `Σ_i ξ_i x_i ≤ r y` if `x_i ≤ y` at every occupied label. -/
theorem sum_occ_le {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {x : Fin N → ℝ} {y : ℝ}
    (h : ∀ i, 0 < ξ i → x i ≤ y) : ∑ i, (ξ i : ℝ) * x i ≤ (r : ℝ) * y := by
  have hr : (r : ℝ) = ∑ i, (ξ i : ℝ) := by rw [mem_sector] at hξ; exact_mod_cast hξ.symm
  rw [hr, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases Nat.eq_zero_or_pos (ξ i) with h0 | hpos
  · simp [h0]
  · exact mul_le_mul_of_nonneg_left (h i hpos) (by positivity)

theorem le_sum_occ {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {x : Fin N → ℝ} {y : ℝ}
    (h : ∀ i, 0 < ξ i → y ≤ x i) : (r : ℝ) * y ≤ ∑ i, (ξ i : ℝ) * x i := by
  have := sum_occ_le hξ (x := fun i => -x i) (y := -y) (fun i hi => by linarith [h i hi])
  simp only [mul_neg, Finset.sum_neg_distrib] at this
  linarith

/-- **Maximum.** The short generator at a maximizer of a nonnegative function. -/
theorem maxStep {r ℓ : ℕ} {c K : Fin N → Fin N → ℝ} {η : ℝ} {f : Occ N → ℝ} {ξ : Occ N}
    (hξ : ξ ∈ sector N r) (hK : ∀ i j, 0 ≤ K i j)
    (hcK : ∀ i j, i ≠ j → labelDist i j < ℓ → K i j ≤ η * c i j)
    (hcl : ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c i j = 0)
    (hf0 : ∀ ζ ∈ sector N r, 0 ≤ f ζ) (hmax : ∀ ζ ∈ sector N r, f ζ ≤ f ξ) :
    η * momentGenerator c f ξ ≤
      ∑ i, (ξ i : ℝ) * (remSum K f ξ i - f ξ * ∑ j, K i j) +
        ((r : ℝ) + 1) * f ξ * ∑ i, (ξ i : ℝ) * longKer K ℓ i := by
  classical
  unfold momentGenerator
  set M := f ξ
  have hM0 : 0 ≤ M := hf0 ξ hξ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  rcases Nat.eq_zero_or_pos (ξ i) with h0 | hi
  · have : ∀ j, jumpCoeff ξ i j = 0 := fun j => jumpCoeff_eq_zero_of_eq_zero ξ j h0
    simp [this, h0]
  -- per-pair bound
  have hpair : ∀ j ∈ univ.erase i, η * (c i j * jumpCoeff ξ i j * (f (move ξ i j) - M)) ≤
      (ξ i : ℝ) * (K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - M)) +
        (ξ i : ℝ) * M * (if ℓ ≤ labelDist i j then K i j * ((ξ j : ℝ) + 1) else 0) := by
    intro j hj
    have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
    have hmv := hmax _ (move_mem_sector hξ hij hi)
    have hfm0 := hf0 _ (move_mem_sector hξ hij hi)
    have hxi : (0 : ℝ) ≤ ξ i := by positivity
    have hxj : (0 : ℝ) ≤ (ξ j : ℝ) + 1 := by positivity
    unfold jumpCoeff
    by_cases hl : ℓ ≤ labelDist i j
    · rw [hcl i j hij hl]; simp only [hl, ite_true]
      have : 0 ≤ (ξ i : ℝ) * (K i j * ((ξ j : ℝ) + 1) * f (move ξ i j)) :=
        mul_nonneg hxi (mul_nonneg (mul_nonneg (hK i j) hxj) hfm0)
      nlinarith
    · simp only [hl, ite_false]
      have hs := hcK i j hij (not_le.1 hl)
      have hneg : f (move ξ i j) - M ≤ 0 := by linarith
      have : η * c i j * ((ξ i : ℝ) * ((ξ j : ℝ) + 1)) * (f (move ξ i j) - M) ≤
          K i j * ((ξ i : ℝ) * ((ξ j : ℝ) + 1)) * (f (move ξ i j) - M) :=
        mul_le_mul_of_nonpos_right
          (mul_le_mul_of_nonneg_right hs (mul_nonneg hxi hxj)) hneg
      nlinarith
  refine (Finset.sum_le_sum hpair).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hlw := long_weighted_le hξ hK ℓ i
  have hS : ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - M) ≤
      remSum K f ξ i - M * ∑ j, K i j := by
    rw [remSum_split, sum_erase_add_diag]
    have e1 : ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - M) =
        ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * f (move ξ i j) -
          M * ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j ∈ univ.erase i, K i j ≤ ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) :=
      Finset.sum_le_sum fun j _ => by nlinarith [hK i j, (Nat.cast_nonneg (ξ j) : (0 : ℝ) ≤ ξ j)]
    have hxi1 : (1 : ℝ) ≤ ξ i := by exact_mod_cast hi
    have e3 : K i i * M ≤ K i i * (ξ i : ℝ) * M := by
      have := mul_nonneg (hK i i) hM0; nlinarith
    rw [e1]
    nlinarith
  have hxi : (0 : ℝ) ≤ ξ i := by positivity
  calc (ξ i : ℝ) * ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - M) +
        (ξ i : ℝ) * M * ∑ j ∈ univ.erase i,
          (if ℓ ≤ labelDist i j then K i j * ((ξ j : ℝ) + 1) else 0)
      ≤ (ξ i : ℝ) * (remSum K f ξ i - M * ∑ j, K i j) +
        (ξ i : ℝ) * M * (((r : ℝ) + 1) * longKer K ℓ i) := by
        gcongr
    _ = (ξ i : ℝ) * (remSum K f ξ i - M * ∑ j, K i j) +
        ((r : ℝ) + 1) * M * ((ξ i : ℝ) * longKer K ℓ i) := by ring

/-- **Minimum.** The short generator at a minimizer. -/
theorem minStep {r ℓ : ℕ} {c K : Fin N → Fin N → ℝ} {η G Kmax : ℝ} {f : Occ N → ℝ} {ξ : Occ N}
    (hξ : ξ ∈ sector N r) (hK : ∀ i j, 0 ≤ K i j) (hKm : ∀ i j, K i j ≤ Kmax)
    (hcK : ∀ i j, i ≠ j → labelDist i j < ℓ → K i j ≤ η * c i j)
    (hcl : ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c i j = 0)
    (hfG : ∀ ζ ∈ sector N r, f ζ ≤ G) (hm0 : 0 ≤ f ξ)
    (hmin : ∀ ζ ∈ sector N r, f ξ ≤ f ζ) :
    ∑ i, (ξ i : ℝ) * (remSum K f ξ i - f ξ * ∑ j, K i j) -
        ∑ i, (ξ i : ℝ) * (f ξ * r * Kmax + ((r : ℝ) + 1) * G * longKer K ℓ i) ≤
      η * momentGenerator c f ξ := by
  classical
  unfold momentGenerator
  set m := f ξ
  have hξj : ∀ j, (ξ j : ℝ) ≤ r := by
    intro j
    have h := hξ
    rw [mem_sector] at h
    have : ξ j ≤ r := h ▸ Finset.single_le_sum (fun k _ => Nat.zero_le (ξ k)) (mem_univ j)
    exact_mod_cast this
  have hr : (r : ℝ) = ∑ j, (ξ j : ℝ) := by
    have h := hξ; rw [mem_sector] at h; exact_mod_cast h.symm
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum (s := univ.erase i)]
  rcases Nat.eq_zero_or_pos (ξ i) with h0 | hi
  · have : ∀ j, jumpCoeff ξ i j = 0 := fun j => jumpCoeff_eq_zero_of_eq_zero ξ j h0
    simp [this, h0]
  have hxi : (0 : ℝ) ≤ ξ i := by positivity
  have hpair : ∀ j ∈ univ.erase i,
      (ξ i : ℝ) * (K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - m)) -
        (ξ i : ℝ) * G * (if ℓ ≤ labelDist i j then K i j * ((ξ j : ℝ) + 1) else 0) ≤
      η * (c i j * jumpCoeff ξ i j * (f (move ξ i j) - m)) := by
    intro j hj
    have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
    have hmv := hmin _ (move_mem_sector hξ hij hi)
    have hfG' := hfG _ (move_mem_sector hξ hij hi)
    have hxj : (0 : ℝ) ≤ (ξ j : ℝ) + 1 := by positivity
    unfold jumpCoeff
    by_cases hl : ℓ ≤ labelDist i j
    · rw [hcl i j hij hl]; simp only [hl, ite_true]
      have : (ξ i : ℝ) * (K i j * ((ξ j : ℝ) + 1)) * (f (move ξ i j) - m) ≤
          (ξ i : ℝ) * (K i j * ((ξ j : ℝ) + 1)) * G :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hxi (mul_nonneg (hK i j) hxj))
      nlinarith
    · simp only [hl, ite_false]
      have hs := hcK i j hij (not_le.1 hl)
      have hpos : 0 ≤ f (move ξ i j) - m := by linarith
      have : K i j * ((ξ i : ℝ) * ((ξ j : ℝ) + 1)) * (f (move ξ i j) - m) ≤
          η * c i j * ((ξ i : ℝ) * ((ξ j : ℝ) + 1)) * (f (move ξ i j) - m) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hs (mul_nonneg hxi hxj)) hpos
      nlinarith
  refine le_trans ?_ (Finset.sum_le_sum hpair)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hlw := long_weighted_le hξ hK ℓ i
  have hS : remSum K f ξ i - m * ∑ j, K i j - m * r * Kmax ≤
      ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - m) := by
    rw [remSum_split, sum_erase_add_diag]
    have e1 : ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - m) =
        ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * f (move ξ i j) -
          (∑ j ∈ univ.erase i, K i j + ∑ j ∈ univ.erase i, K i j * (ξ j : ℝ)) * m := by
      rw [← Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : K i i * (ξ i : ℝ) + ∑ j ∈ univ.erase i, K i j * (ξ j : ℝ) ≤ Kmax * r := by
      rw [hr, Finset.mul_sum, ← Finset.add_sum_erase _ _ (mem_univ i)]
      gcongr with j hj
      · exact hKm i i
      · exact hKm i j
    rw [e1]
    have hm0' : 0 ≤ m := hm0
    nlinarith [hK i i]
  calc (ξ i : ℝ) * (remSum K f ξ i - m * ∑ j, K i j) -
        (ξ i : ℝ) * (m * r * Kmax + ((r : ℝ) + 1) * G * longKer K ℓ i)
      ≤ (ξ i : ℝ) * ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - m) -
        (ξ i : ℝ) * G * (((r : ℝ) + 1) * longKer K ℓ i) := by
        have hG0 : 0 ≤ G := le_trans hm0 (hfG ξ hξ)
        have h1 := mul_le_mul_of_nonneg_left hS hxi
        nlinarith
    _ ≤ (ξ i : ℝ) * ∑ j ∈ univ.erase i, K i j * ((ξ j : ℝ) + 1) * (f (move ξ i j) - m) -
        (ξ i : ℝ) * G * ∑ j ∈ univ.erase i,
          (if ℓ ≤ labelDist i j then K i j * ((ξ j : ℝ) + 1) else 0) := by
        have hG0 : 0 ≤ G := le_trans hm0 (hfG ξ hξ)
        have := mul_le_mul_of_nonneg_left hlw (mul_nonneg hxi hG0)
        linarith

/-- **Damped form at a maximizer.** -/
theorem maxStep_damped {r ℓ : ℕ} {c K : Fin N → Fin N → ℝ} {η : ℝ} {f : Occ N → ℝ} {ξ : Occ N}
    (hξ : ξ ∈ sector N r) (hK : ∀ i j, 0 ≤ K i j)
    (hcK : ∀ i j, i ≠ j → labelDist i j < ℓ → K i j ≤ η * c i j)
    (hcl : ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c i j = 0)
    (hf0 : ∀ ζ ∈ sector N r, 0 ≤ f ζ) (hmax : ∀ ζ ∈ sector N r, f ζ ≤ f ξ)
    {V Ψ : Fin N → ℝ} {aξ v Vb G e₁ e₂ e₃ e₄ : ℝ} (hv0 : 0 ≤ v) (ha0 : 0 ≤ aξ) (ha1 : aξ ≤ 1)
    (hM1 : 1 ≤ f ξ) (hMG : f ξ ≤ G)
    (hR3 : ∀ i, 0 < ξ i → |remSum K f ξ i - V i * (aξ * Ψ i + (1 - aξ))| ≤ e₁)
    (hAv : ∀ i, 0 < ξ i → |∑ j, K i j - V i| ≤ e₂)
    (hL : ∀ i, 0 < ξ i → longKer K ℓ i ≤ e₃)
    (hIH : ∀ i, 0 < ξ i → |Ψ i - 1| ≤ e₄)
    (hV : ∀ i, 0 < ξ i → v ≤ V i ∧ V i ≤ Vb) :
    η * momentGenerator c f ξ ≤
      -((r : ℝ) * v) * (f ξ - 1) + (r : ℝ) * (e₁ + Vb * e₄ + G * e₂ + ((r : ℝ) + 1) * G * e₃) := by
  have h := maxStep hξ hK hcK hcl hf0 hmax
  set M := f ξ
  have h1 : ∑ i, (ξ i : ℝ) * (remSum K f ξ i - M * ∑ j, K i j) ≤
      (r : ℝ) * (-v * (M - 1) + (e₁ + Vb * e₄ + G * e₂)) := by
    refine sum_occ_le hξ fun i hi => ?_
    have a1 := abs_le.1 (hR3 i hi)
    have a2 := abs_le.1 (hAv i hi)
    have a4 := abs_le.1 (hIH i hi)
    obtain ⟨hv1, hv2⟩ := hV i hi
    have hV0 : 0 ≤ V i := hv0.trans hv1
    have hM0 : 0 ≤ M := by linarith
    -- remSum - M ΣK ≤ V(aΨ+1-a) + e₁ - M(V - e₂)
    have k1 : V i * (aξ * (Ψ i - 1)) ≤ Vb * e₄ := by
      have : |aξ * (Ψ i - 1)| ≤ e₄ := by
        rw [abs_mul, abs_of_nonneg ha0]
        calc aξ * |Ψ i - 1| ≤ 1 * |Ψ i - 1| := by gcongr
          _ ≤ e₄ := by linarith [hIH i hi]
      have hb := (abs_le.1 this).2
      have he4 : 0 ≤ e₄ := (abs_nonneg _).trans (hIH i hi)
      calc V i * (aξ * (Ψ i - 1)) ≤ V i * e₄ := mul_le_mul_of_nonneg_left hb hV0
        _ ≤ Vb * e₄ := mul_le_mul_of_nonneg_right hv2 he4
    have k2 : M * (∑ j, K i j) ≥ M * (V i - e₂) := mul_le_mul_of_nonneg_left (by linarith) hM0
    have k3 : M * e₂ ≤ G * e₂ := mul_le_mul_of_nonneg_right hMG ((abs_nonneg _).trans (hAv i hi))
    have k4 : -(V i) * (M - 1) ≤ -v * (M - 1) := by nlinarith
    nlinarith
  have hlk : ∑ i, (ξ i : ℝ) * longKer K ℓ i ≤ (r : ℝ) * e₃ := sum_occ_le hξ hL
  have hM0 : 0 ≤ M := by linarith
  have h2 : ((r : ℝ) + 1) * M * ∑ i, (ξ i : ℝ) * longKer K ℓ i ≤
      ((r : ℝ) + 1) * G * ((r : ℝ) * e₃) := by
    have hl0 : 0 ≤ ∑ i, (ξ i : ℝ) * longKer K ℓ i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (longKer_nonneg hK ℓ i)
    calc ((r : ℝ) + 1) * M * ∑ i, (ξ i : ℝ) * longKer K ℓ i
        ≤ ((r : ℝ) + 1) * G * ∑ i, (ξ i : ℝ) * longKer K ℓ i := by gcongr
      _ ≤ ((r : ℝ) + 1) * G * ((r : ℝ) * e₃) := by
        have : 0 ≤ ((r : ℝ) + 1) * G := mul_nonneg (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_left hlk this
  have : (r : ℝ) * (-v * (M - 1) + (e₁ + Vb * e₄ + G * e₂)) + ((r : ℝ) + 1) * G * ((r : ℝ) * e₃) =
      -((r : ℝ) * v) * (M - 1) + (r : ℝ) * (e₁ + Vb * e₄ + G * e₂ + ((r : ℝ) + 1) * G * e₃) := by
    ring
  linarith

/-- **Damped form at a minimizer.** -/
theorem minStep_damped {r ℓ : ℕ} {c K : Fin N → Fin N → ℝ} {η Kmax : ℝ} {f : Occ N → ℝ}
    {ξ : Occ N} (hξ : ξ ∈ sector N r) (hK : ∀ i j, 0 ≤ K i j) (hKm : ∀ i j, K i j ≤ Kmax)
    (hKm0 : 0 ≤ Kmax) (hcK : ∀ i j, i ≠ j → labelDist i j < ℓ → K i j ≤ η * c i j)
    (hcl : ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c i j = 0)
    {V Ψ : Fin N → ℝ} {aξ v Vb G e₁ e₂ e₃ e₄ : ℝ} (hv0 : 0 ≤ v) (ha0 : 0 ≤ aξ) (ha1 : aξ ≤ 1)
    (hfG : ∀ ζ ∈ sector N r, f ζ ≤ G) (hm0 : 0 ≤ f ξ) (hm1 : f ξ ≤ 1)
    (hmin : ∀ ζ ∈ sector N r, f ξ ≤ f ζ)
    (hR3 : ∀ i, 0 < ξ i → |remSum K f ξ i - V i * (aξ * Ψ i + (1 - aξ))| ≤ e₁)
    (hAv : ∀ i, 0 < ξ i → |∑ j, K i j - V i| ≤ e₂)
    (hL : ∀ i, 0 < ξ i → longKer K ℓ i ≤ e₃)
    (hIH : ∀ i, 0 < ξ i → |Ψ i - 1| ≤ e₄)
    (hV : ∀ i, 0 < ξ i → v ≤ V i ∧ V i ≤ Vb) :
    (r : ℝ) * v * (1 - f ξ) -
        (r : ℝ) * (e₁ + Vb * e₄ + e₂ + r * Kmax + ((r : ℝ) + 1) * G * e₃) ≤
      η * momentGenerator c f ξ := by
  have h := minStep hξ hK hKm hcK hcl hfG hm0 hmin
  set m := f ξ
  have hG0 : 0 ≤ G := hm0.trans (hfG ξ hξ)
  have h1 : (r : ℝ) * (v * (1 - m) - (e₁ + Vb * e₄ + e₂)) ≤
      ∑ i, (ξ i : ℝ) * (remSum K f ξ i - m * ∑ j, K i j) := by
    refine le_sum_occ hξ fun i hi => ?_
    have a1 := abs_le.1 (hR3 i hi)
    have a2 := abs_le.1 (hAv i hi)
    obtain ⟨hv1, hv2⟩ := hV i hi
    have he4 : 0 ≤ e₄ := (abs_nonneg _).trans (hIH i hi)
    have he2 : 0 ≤ e₂ := (abs_nonneg _).trans (hAv i hi)
    have hV0 : 0 ≤ V i := hv0.trans hv1
    have k1 : -(Vb * e₄) ≤ V i * (aξ * (Ψ i - 1)) := by
      have : |aξ * (Ψ i - 1)| ≤ e₄ := by
        rw [abs_mul, abs_of_nonneg ha0]
        calc aξ * |Ψ i - 1| ≤ 1 * |Ψ i - 1| := by gcongr
          _ ≤ e₄ := by linarith [hIH i hi]
      have hb := (abs_le.1 this).1
      calc -(Vb * e₄) ≤ -(V i * e₄) := by nlinarith
        _ = V i * (-e₄) := by ring
        _ ≤ V i * (aξ * (Ψ i - 1)) := mul_le_mul_of_nonneg_left hb hV0
    have k2 : m * (∑ j, K i j) ≤ m * (V i + e₂) := mul_le_mul_of_nonneg_left (by linarith) hm0
    have k3 : m * e₂ ≤ e₂ := by nlinarith
    have k4 : v * (1 - m) ≤ V i * (1 - m) := mul_le_mul_of_nonneg_right hv1 (by linarith)
    nlinarith
  have h2 : ∑ i, (ξ i : ℝ) * (m * r * Kmax + ((r : ℝ) + 1) * G * longKer K ℓ i) ≤
      (r : ℝ) * (r * Kmax + ((r : ℝ) + 1) * G * e₃) := by
    refine sum_occ_le hξ fun i hi => ?_
    have : m * r * Kmax ≤ r * Kmax := by
      have : 0 ≤ (r : ℝ) * Kmax := mul_nonneg (by positivity) hKm0
      nlinarith
    have : ((r : ℝ) + 1) * G * longKer K ℓ i ≤ ((r : ℝ) + 1) * G * e₃ :=
      mul_le_mul_of_nonneg_left (hL i hi) (mul_nonneg (by positivity) hG0)
    linarith
  have : (r : ℝ) * (v * (1 - m) - (e₁ + Vb * e₄ + e₂)) -
      (r : ℝ) * (r * Kmax + ((r : ℝ) + 1) * G * e₃) =
      (r : ℝ) * v * (1 - m) - (r : ℝ) * (e₁ + Vb * e₄ + e₂ + r * Kmax + ((r : ℝ) + 1) * G * e₃) := by
    ring
  linarith

end BlockBand.Palm.MomentFlow
