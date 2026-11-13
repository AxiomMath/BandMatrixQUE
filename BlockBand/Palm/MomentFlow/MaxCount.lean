module

public import BlockBand.Palm.MomentFlow.IndProps

/-!
# Kernel comparisons and the local count for the maximum principle (deterministic)

* `kerAt_le_rate`: `N⁻¹η/(d² + η²) ≤ η · (N d²)⁻¹` (`d ≠ 0`): "replace `c_ij` by the smaller
  kernel" (hypothesis `hcK` of `maxPath`, with `shortFlowRate` in `kerAt_le_shortFlowRate`).
* `longKer_le_longCoupling`: `Σ_{|j-i| ≥ ℓ} K^η_ij ≤ η · longCoupling` when long pairs have
  distinct eigenvalues (hypothesis `hL` of `maxPath`; `longCoupling ≤ CN/ℓ` is clause 5 of
  `GoodEvent.spectralGoodEvent_s8`).
* `labelDist_lt_count`: for sorted eigenvalues, `|i - j| < #{k : |λ_k - λ_i| ≤ |λ_j - λ_i|}`.
* `count_le_kernel`: `#{k : |λ_k - λ_i| ≤ h} ≤ 2Nh Σ_k K^h_ik` (the local upper count from the
  averaged law).
* **`ramp_lip_of_count`**: if `Σ_k K^h_ik ≤ V_c` for all heights `h ∈ [η, 1]` and
  `β = 4rNV_c/wd ≥ 1`, then `|a_{ξ^{ij}} - a_ξ| ≤ min(1, β(|λ_j - λ_i| + η))` (hypothesis `hlip` of
  `maxPath`; in the paper, "the coefficient difference is at most `min(1, 2|j-i|/w)`" with the
  local count).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem kerAt_le_rate (lam : Fin N → ℝ) {η : ℝ} (hη : 0 ≤ η) {i j : Fin N}
    (hd : lam i ≠ lam j) : kerAt lam η i j ≤ η * ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ := by
  unfold kerAt
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  have hN : (0 : ℝ) < N := by exact_mod_cast h0
  have hd2 : 0 < (lam i - lam j) ^ 2 := by
    have : lam i - lam j ≠ 0 := sub_ne_zero.2 hd
    positivity
  have e : (lam j - lam i) ^ 2 = (lam i - lam j) ^ 2 := by ring
  rw [e, mul_inv, div_eq_mul_inv]
  have : ((lam i - lam j) ^ 2 + η ^ 2)⁻¹ ≤ ((lam i - lam j) ^ 2)⁻¹ :=
    inv_anti₀ hd2 (by nlinarith [sq_nonneg η])
  have h2 : (N : ℝ)⁻¹ * (η * ((lam i - lam j) ^ 2 + η ^ 2)⁻¹) ≤
      (N : ℝ)⁻¹ * (η * ((lam i - lam j) ^ 2)⁻¹) := by gcongr
  linarith [show (N : ℝ)⁻¹ * (η * ((lam i - lam j) ^ 2)⁻¹) =
    η * ((N : ℝ)⁻¹ * ((lam i - lam j) ^ 2)⁻¹) by ring]

theorem kerAt_le_shortFlowRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (u : ℝ) {η : ℝ} (hη : 0 ≤ η) {i j : Fin N}
    (hd : flowEigenvalue F a ω u i ≠ flowEigenvalue F a ω u j) (hl : labelDist i j < ℓ) :
    kerAt (fun k => flowEigenvalue F a ω u k) η i j ≤ η * shortFlowRate F a ω ℓ u i j := by
  have h := kerAt_le_rate (fun k => flowEigenvalue F a ω u k) hη hd
  unfold shortFlowRate maskRate flowRate
  simp only [hl, ite_true]
  exact h

theorem shortFlowRate_long (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (u : ℝ) {i j : Fin N} (hl : ℓ ≤ labelDist i j) : shortFlowRate F a ω ℓ u i j = 0 := by
  unfold shortFlowRate maskRate
  simp only [not_lt.2 hl, ite_false]

theorem longKer_le_longCoupling (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (u : ℝ) {η : ℝ} (hη : 0 ≤ η) (i : Fin N)
    (hd : ∀ j, ℓ ≤ labelDist i j → flowEigenvalue F a ω u i ≠ flowEigenvalue F a ω u j) :
    longKer (kerAt (fun k => flowEigenvalue F a ω u k) η) ℓ i ≤ η * longCoupling F a ω ℓ u i := by
  unfold longKer longCoupling
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hl := (Finset.mem_filter.1 hj).2
  have := kerAt_le_rate (fun k => flowEigenvalue F a ω u k) hη (hd j hl)
  unfold flowRate
  exact this

/-- For sorted values, the labels between `i` and `j` (inclusive) lie in the closed ball. -/
theorem labelDist_lt_count {lam : Fin N → ℝ} (hmono : Monotone lam) (i j : Fin N) :
    labelDist i j < (univ.filter fun k => |lam k - lam i| ≤ |lam j - lam i|).card := by
  classical
  set lo := min i j
  set hi := max i j
  have hsub : Finset.Icc lo hi ⊆ univ.filter fun k => |lam k - lam i| ≤ |lam j - lam i| := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine Finset.mem_filter.2 ⟨mem_univ k, ?_⟩
    rcases le_total i j with hij | hij
    · have h1 : lo = i := min_eq_left hij
      have h2 : hi = j := max_eq_right hij
      rw [h1] at hk; rw [h2] at hk
      have a1 := hmono hk.1; have a2 := hmono hk.2; have a3 := hmono hij
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · have h1 : lo = j := min_eq_right hij
      have h2 : hi = i := max_eq_left hij
      rw [h1] at hk; rw [h2] at hk
      have a1 := hmono hk.1; have a2 := hmono hk.2; have a3 := hmono hij
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Icc] at hcard
  have : labelDist i j + 1 = (hi : ℕ) + 1 - lo := by
    unfold labelDist
    rcases le_total i j with hij | hij
    · rw [show lo = i from min_eq_left hij, show hi = j from max_eq_right hij]
      have : (i : ℕ) ≤ j := hij
      omega
    · rw [show lo = j from min_eq_right hij, show hi = i from max_eq_left hij]
      have : (j : ℕ) ≤ i := hij
      omega
  omega

/-- Local upper count from the kernel: `#{|λ_k - λ_i| ≤ h} ≤ 2Nh Σ_k K^h_ik`. -/
theorem count_le_kernel (lam : Fin N → ℝ) {h : ℝ} (hh : 0 < h) (i : Fin N) :
    ((univ.filter fun k => |lam k - lam i| ≤ h).card : ℝ) ≤
      2 * N * h * ∑ k, kerAt lam h i k := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Fin.pos i)
  have hpt : ∀ k ∈ univ.filter (fun k => |lam k - lam i| ≤ h), 1 ≤ 2 * N * h * kerAt lam h i k := by
    intro k hk
    have hd := (Finset.mem_filter.1 hk).2
    have hd2 : (lam k - lam i) ^ 2 ≤ h ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    unfold kerAt
    rw [show 2 * (N : ℝ) * h * ((N : ℝ)⁻¹ * (h / ((lam k - lam i) ^ 2 + h ^ 2))) =
      2 * h ^ 2 / ((lam k - lam i) ^ 2 + h ^ 2) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc ((univ.filter fun k => |lam k - lam i| ≤ h).card : ℝ)
      = ∑ k ∈ univ.filter (fun k => |lam k - lam i| ≤ h), (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ univ.filter (fun k => |lam k - lam i| ≤ h), 2 * N * h * kerAt lam h i k :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ k, 2 * N * h * kerAt lam h i k :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => by
          have := kerAt_nonneg lam hh.le i k; positivity
    _ = 2 * N * h * ∑ k, kerAt lam h i k := by rw [Finset.mul_sum]

/-- **Ramp Lipschitz bound from the local count.** -/
theorem ramp_lip_of_count {r : ℕ} {lam : Fin N → ℝ} (hmono : Monotone lam) {η Vc wd β : ℝ}
    (hη : 0 < η) (hwd : 0 < wd) (hβ : β = 4 * r * N * Vc / wd) (hβ1 : 1 ≤ β) (k₀ : ℕ)
    {ξ : Occ N} (hξ : ξ ∈ sector N r) {i : Fin N} (hi : 0 < ξ i)
    (hVc : ∀ h, η ≤ h → h ≤ 1 → ∑ k, kerAt lam h i k ≤ Vc) (j : Fin N) :
    |ramp wd k₀ (remTarget ξ i j) - ramp wd k₀ ξ| ≤ min 1 (β * (|lam j - lam i| + η)) := by
  have h0 := ramp_remTarget_le hwd k₀ hξ hi j
  set d := |lam j - lam i|
  have hd0 : 0 ≤ d := abs_nonneg _
  by_cases hbig : 1 < max d η
  · have : 1 ≤ β * (d + η) := by
      have : 1 ≤ d + η := by
        rcases le_total d η with h | h
        · rw [max_eq_right h] at hbig; linarith
        · rw [max_eq_left h] at hbig; linarith
      nlinarith
    rw [min_eq_left this]
    exact h0.trans (min_le_left _ _)
  push Not at hbig
  set h := max d η
  have hh : 0 < h := lt_of_lt_of_le hη (le_max_right _ _)
  have hcount := labelDist_lt_count hmono i j
  have hsub : (univ.filter fun k => |lam k - lam i| ≤ |lam j - lam i|) ⊆
      univ.filter fun k => |lam k - lam i| ≤ h :=
    fun k hk => Finset.mem_filter.2 ⟨mem_univ k, (Finset.mem_filter.1 hk).2.trans (le_max_left _ _)⟩
  have hc2 := count_le_kernel lam hh i
  have hV := hVc h (le_max_right _ _) hbig
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hld : (labelDist i j : ℝ) ≤ 2 * N * h * Vc := by
    have h1 : (labelDist i j : ℝ) ≤ ((univ.filter fun k => |lam k - lam i| ≤ h).card : ℝ) := by
      have := (Finset.card_le_card hsub)
      exact_mod_cast (hcount.le.trans this)
    refine h1.trans (hc2.trans ?_)
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  refine h0.trans (min_le_min le_rfl ?_)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hhd : h ≤ d + η := max_le (by linarith) (by linarith)
  have hVc0 : 0 ≤ Vc := by
    have : (0 : ℝ) ≤ ∑ k, kerAt lam h i k := Finset.sum_nonneg fun k _ => kerAt_nonneg lam hh.le i k
    linarith
  calc 2 * r / wd * (labelDist i j : ℝ) ≤ 2 * r / wd * (2 * N * h * Vc) :=
        mul_le_mul_of_nonneg_left hld (by positivity)
    _ = (4 * r * N * Vc / wd) * h := by ring
    _ ≤ β * (d + η) := by
        rw [← hβ]
        exact mul_le_mul_of_nonneg_left hhd (by linarith)

end BlockBand.Palm.MomentFlow
