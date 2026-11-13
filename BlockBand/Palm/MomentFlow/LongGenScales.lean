module

public import BlockBand.Palm.MomentFlow.PropLong
public import BlockBand.Palm.MomentFlow.IndProps

/-!
# Long-jump generator bounds and the scales of `LongShortPropagation`

* **`longGen_local_bound`**: `|𝓑F - 𝓢F|(η) ≤ r d + (r+1) b (r L)` for `F ≥ 0` on the sector, the
  long-jump row bound `Σ_{|i-j| ≥ ℓ} c_ij (η_j + 1) F(η^{ij}) ≤ d` at every occupied `i`, `F(η) ≤ b`
  (`M_loc`) and `longCoupling ≤ L` (`longGen_local_le`).
* **`longGen_global_bound`**: `|𝓑F - 𝓢F| ≤ 2B(r+1)rL` from `|F| ≤ B` (`longGen_global_le`).
* **`eloc_le`**: the local error `r d + (r+1) b r L` with the values of the long-jump bound and
  `M_loc` is `≤ N^{(4r+1)ε} N/ℓ` once the (ε-dependent) constants are `≤ N^ε` and the `N^{-D}`
  remainders are `≤ 1`.
* Scale lemmas: `eventually_window_le` (`K_w w + rN^{1/1000}ℓ ≤ N^{1-1/1200}`),
  `eventually_center_le` (`M w/N ≤ r₀/64`), `eventually_const_le_rpow`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset Filter
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem flowRate_self (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (i : Fin N) : flowRate F a ω σ i i = 0 := by
  simp [flowRate]

/-- **Local long-jump bound** from the long-jump row bound and `M_loc`. -/
theorem longGen_local_bound {F : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} {ω : FlowSample N} {ℓ : ℕ}
    {σ : ℝ} {r : ℕ} {η : Occ N} (hη : η ∈ sector N r) {f : Occ N → ℝ}
    (hf : ∀ ζ ∈ sector N r, 0 ≤ f ζ) {d b L : ℝ}
    (hd : ∀ i, 0 < η i → ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      flowRate F a ω σ i j * ((η j : ℝ) + 1) * f (move η i j) ≤ d)
    (hb : f η ≤ b) (hL : ∀ i, longCoupling F a ω ℓ σ i ≤ L) :
    |momentGenerator (flowRate F a ω σ) f η - momentGenerator (shortFlowRate F a ω ℓ σ) f η| ≤
      r * d + (r + 1) * b * (r * L) := by
  classical
  rw [full_sub_short_eq_long]
  have h := longGen_local_le (P := fun i j => ¬ labelDist i j < ℓ) (c := flowRate F a ω σ)
    (flowRate_nonneg F a ω σ) hη hf
  have hsum : ∑ i, (η i : ℝ) = r := by exact_mod_cast mem_sector.1 hη
  have hterm : ∀ i, 0 < η i → ∀ j, 0 ≤ flowRate F a ω σ i j * (1 + (η j : ℝ)) * f (move η i j) := by
    intro i hi j
    by_cases hij : i = j
    · subst hij; rw [flowRate_self]; simp
    · exact mul_nonneg (mul_nonneg (flowRate_nonneg F a ω σ i j) (by positivity))
        (hf _ (move_mem_sector hη hij hi))
  have h1 : ∑ i, (η i : ℝ) * ∑ j ∈ (univ.erase i).filter (fun j => ¬ labelDist i j < ℓ),
      flowRate F a ω σ i j * (1 + η j) * f (move η i j) ≤ ∑ i, (η i : ℝ) * d := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases Nat.eq_zero_or_pos (η i) with h0 | hpos
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left (le_trans ?_ (hd i hpos)) (Nat.cast_nonneg _)
      calc ∑ j ∈ (univ.erase i).filter (fun j => ¬ labelDist i j < ℓ),
            flowRate F a ω σ i j * (1 + η j) * f (move η i j)
          ≤ ∑ j ∈ univ.filter (fun j => ¬ labelDist i j < ℓ),
            flowRate F a ω σ i j * (1 + η j) * f (move η i j) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
              fun j _ _ => hterm i hpos j
        _ = ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
            flowRate F a ω σ i j * ((η j : ℝ) + 1) * f (move η i j) := by
            refine Finset.sum_congr (Finset.filter_congr fun j _ => not_lt) fun j _ => ?_
            ring
  have h2 : ∑ i, (η i : ℝ) * ∑ j ∈ univ.filter (fun j => ¬ labelDist i j < ℓ),
      flowRate F a ω σ i j ≤ ∑ i, (η i : ℝ) * L := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [← longCoupling_eq_filter]; exact hL i
  have h2' : 0 ≤ ∑ i, (η i : ℝ) * ∑ j ∈ univ.filter (fun j => ¬ labelDist i j < ℓ),
      flowRate F a ω σ i j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun j _ => flowRate_nonneg F a ω σ i j)
  rw [← Finset.sum_mul, hsum] at h1 h2
  have hfη := hf η hη
  have hb0 : 0 ≤ b := hfη.trans hb
  refine h.trans (add_le_add h1 ?_)
  have hr1 : (0 : ℝ) ≤ r + 1 := by positivity
  calc (r + 1 : ℝ) * f η * ∑ i, (η i : ℝ) * ∑ j ∈ univ.filter (fun j => ¬ labelDist i j < ℓ),
        flowRate F a ω σ i j
      ≤ (r + 1) * b * (r * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb hr1) h2 h2' (mul_nonneg hr1 hb0)

/-- **Global long-jump bound.** -/
theorem longGen_global_bound {F : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} {ω : FlowSample N} {ℓ : ℕ}
    {σ : ℝ} {r : ℕ} {ζ : Occ N} (hζ : ζ ∈ sector N r) {f : Occ N → ℝ} {B L : ℝ}
    (hB : ∀ η ∈ sector N r, |f η| ≤ B) (hL : ∀ i, longCoupling F a ω ℓ σ i ≤ L) :
    |momentGenerator (flowRate F a ω σ) f ζ - momentGenerator (shortFlowRate F a ω ℓ σ) f ζ| ≤
      2 * B * (r + 1) * r * L := by
  classical
  rw [full_sub_short_eq_long]
  exact longGen_global_le (P := fun i j => ¬ labelDist i j < ℓ) (flowRate_nonneg F a ω σ) hζ hB
    fun i => by rw [← longCoupling_eq_filter]; exact hL i

/-- **The local error** `r d + (r+1) b r L` with the values of the long-jump row bound and
`M_loc`. -/
theorem eloc_le {x ℓ ε : ℝ} {r : ℕ} {Cov Cst Cst' c₁ C j₁ j₂ : ℝ} (hx : 1 ≤ x) (hℓ : 0 < ℓ)
    (hℓx : ℓ ≤ x) (hε : 0 ≤ ε) (hCov : 0 ≤ Cov) (hCst : 0 ≤ Cst) (hCst' : 0 ≤ Cst')
    (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hj₁ : j₁ ≤ 1) (hj₂ : j₂ ≤ 1)
    (hK : r * max 1 Cov ^ r * (2 * Cst / c₁) + r + (r + 1) * r * C * (max 1 Cst' ^ r + 1) ≤
      x ^ ε) :
    r * ((Cov * x ^ (4 * ε)) ^ (r - 1) * (2 / (c₁ * ℓ / x) * Cst) + j₁) +
        (r + 1) * ((Cst' * x ^ (4 * ε)) ^ r + j₂) * (r * (C * x / ℓ)) ≤
      x ^ ((4 * r + 1) * ε) * (x / ℓ) := by
  have hx0 : 0 < x := by linarith
  set y := x ^ (4 * ε) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx (by linarith)
  set X := x / ℓ with hX
  have hX1 : 1 ≤ X := by rw [hX, le_div_iff₀ hℓ]; linarith
  set P := y ^ r with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hy1
  set A := max 1 Cov ^ r with hA
  set B := max 1 Cst' ^ r with hB
  have hA0 : 0 ≤ A := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hB0 : 0 ≤ B := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have e1 : (Cov * y) ^ (r - 1) ≤ A * P := by
    have hb : Cov * y ≤ max 1 Cov * y := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    have hb1 : 1 ≤ max 1 Cov * y := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hy1
    calc (Cov * y) ^ (r - 1) ≤ (max 1 Cov * y) ^ (r - 1) :=
          pow_le_pow_left₀ (mul_nonneg hCov (by linarith)) hb _
      _ ≤ (max 1 Cov * y) ^ r := pow_le_pow_right₀ hb1 (Nat.sub_le r 1)
      _ = A * P := by rw [hA, hP, mul_pow]
  have e2 : (Cst' * y) ^ r ≤ B * P := by
    rw [hB, hP, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hCst' (by linarith))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)) _
  have e3 : 2 / (c₁ * ℓ / x) * Cst = 2 * Cst / c₁ * X := by
    rw [hX]; field_simp
  have e4 : x ^ ((4 * r + 1) * ε) = P * x ^ ε := by
    rw [hP, hy, ← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]; ring_nf
  have hc0 : 0 ≤ 2 * Cst / c₁ := by positivity
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hj₁' : j₁ ≤ P * X := hj₁.trans (one_le_mul_of_one_le_of_one_le hP1 hX1)
  have hj₂' : j₂ ≤ P := hj₂.trans hP1
  have hCX : C * x / ℓ = C * X := by rw [hX]; ring
  rw [e3, e4, hCX]
  calc (r : ℝ) * ((Cov * y) ^ (r - 1) * (2 * Cst / c₁ * X) + j₁) +
        (r + 1) * ((Cst' * y) ^ r + j₂) * (r * (C * X))
      ≤ r * (A * P * (2 * Cst / c₁ * X) + P * X) + (r + 1) * (B * P + P) * (r * (C * X)) := by
        gcongr
    _ = P * X * (r * A * (2 * Cst / c₁) + r + (r + 1) * r * C * (B + 1)) := by ring
    _ ≤ P * X * x ^ ε := by
        gcongr
    _ = P * x ^ ε * X := by ring

/-!
## Scales
-/

theorem eventually_const_le_rpow (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ ε :=
  ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop K)

theorem eventually_const_mul_rpow_neg_le (K : ℝ) {α y : ℝ} (hα : 0 < α) (hy : 0 < y) :
    ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ (-α) ≤ y := by
  have h : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-α)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop).const_mul K
  exact (h.eventually (gt_mem_nhds hy)).mono fun _ h => h.le

theorem cmEll_le_rpow (N : ℕ) : (cmEll N : ℝ) ≤ (N : ℝ) ^ (1 - (1 / 300 : ℝ)) := by
  unfold cmEll
  have e : (1 - (1 / 100 : ℝ) / 3) = 1 - 1 / 300 := by norm_num
  rw [e]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- **Window radius**: `K_w w + r N^{1/1000} ℓ ≤ N^{1-1/1200}` for large `N`. -/
theorem eventually_window_le (Kw : ℝ) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, Kw * cmW n + r * ((n : ℝ) ^ (1 / 1000 : ℝ) * cmEll n) ≤
      (n : ℝ) ^ (1 - (1 / 1200 : ℝ)) := by
  filter_upwards [eventually_const_mul_rpow_neg_le Kw (by norm_num : (0 : ℝ) < 1 / 1200)
      (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_const_mul_rpow_neg_le (r : ℝ) (by norm_num : (0 : ℝ) < 3 / 2000)
      (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop 1] with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set T := (n : ℝ) ^ (1 - (1 / 1200 : ℝ)) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hn0 _
  have ew : cmW n = (n : ℝ) ^ (-(1 / 1200 : ℝ)) * T := by
    rw [hT, ← Real.rpow_add hn0, cmW]; norm_num
  have el : (n : ℝ) ^ (1 / 1000 : ℝ) * cmEll n ≤ (n : ℝ) ^ (-(3 / 2000 : ℝ)) * T := by
    calc (n : ℝ) ^ (1 / 1000 : ℝ) * cmEll n ≤ (n : ℝ) ^ (1 / 1000 : ℝ) * (n : ℝ) ^ (1 - (1 / 300 : ℝ)) :=
          mul_le_mul_of_nonneg_left (cmEll_le_rpow n) (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (-(3 / 2000 : ℝ)) * T := by
          rw [hT, ← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  calc Kw * cmW n + r * ((n : ℝ) ^ (1 / 1000 : ℝ) * cmEll n)
      ≤ Kw * ((n : ℝ) ^ (-(1 / 1200 : ℝ)) * T) + r * ((n : ℝ) ^ (-(3 / 2000 : ℝ)) * T) := by
        rw [ew]; gcongr
    _ = (Kw * (n : ℝ) ^ (-(1 / 1200 : ℝ)) + r * (n : ℝ) ^ (-(3 / 2000 : ℝ))) * T := by ring
    _ ≤ (1 / 2 + 1 / 2) * T := by gcongr
    _ = T := by ring

/-- **Centre in the bulk**: `M w/N ≤ r₀/64` for large `N`. -/
theorem eventually_center_le (M : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∀ᶠ n : ℕ in atTop, M * cmW n / n ≤ r₀ / 64 := by
  filter_upwards [eventually_const_mul_rpow_neg_le M (by norm_num : (0 : ℝ) < 1 / 600)
      (by positivity : 0 < r₀ / 64), eventually_ge_atTop 1] with n h1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : M * cmW n / n = M * (n : ℝ) ^ (-(1 / 600 : ℝ)) := by
    rw [cmW, mul_div_assoc]
    congr 1
    rw [div_eq_iff hn0.ne', ← Real.rpow_add_one hn0.ne']; norm_num
  rw [e]; exact h1

end BlockBand.Palm.MomentFlow
