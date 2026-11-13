module

public import BlockBand.Transmission.SourceMixing.MomentAlgebra

/-!
# Real algebra of one mass-moment step

The scalar inequalities behind one layer of the recursion for the moments `E qⁿ` of the passive
mass.

* `mma_tangent`: `l qⁿ - qⁿ⁺¹ ≤ lⁿ⁺¹` for `q, l ≥ 0`.
* `mma_fluct_sum`: for `0 ≤ m ≤ Γq` and `σ = C_f q/√W` (`Γ, C_f, W ≥ 1`),
  `Σ_{k=2}^n C(n,k) m^{n-k} σ^k ≤ 2ⁿΓⁿC_fⁿ qⁿ/W`.
* `mma_layer`: the constants `c > 0`, `D₁, D₂ ≥ 0` depend on `n, α, ω₀, C_m, C_f, δ̄` only.
  If `0 ≤ q ≤ ω₀W`, `0 ≤ δ ≤ δ̄`, `0 ≤ m ≤ q/(1+αq/W) + C_m(δ+W⁻²)q` and
  `S ≤ mⁿ + Σ_{k=2}^n C(n,k) m^{n-k} σ^k` with `σ = C_f q/√W`, then for every `l ≥ 0`:
  `S ≤ qⁿ(1 - cl/W) + (c lⁿ⁺¹ + D₁ + D₂(Wδ)ⁿ⁺¹)/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open Finset

/-- The tangent-line bound behind the logistic linearization. -/
theorem mma_tangent (n : ℕ) {q l : ℝ} (hq : 0 ≤ q) (hl : 0 ≤ l) :
    l * q ^ n - q ^ (n + 1) ≤ l ^ (n + 1) := by
  have e : l * q ^ n - q ^ (n + 1) = q ^ n * (l - q) := by ring
  rw [e]
  rcases le_or_gt l q with h | h
  · have : q ^ n * (l - q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have : 0 ≤ l ^ (n + 1) := by positivity
    linarith
  · have h1 : q ^ n ≤ l ^ n := pow_le_pow_left₀ hq h.le n
    calc q ^ n * (l - q) ≤ l ^ n * l := mul_le_mul h1 (by linarith) (by linarith) (by positivity)
      _ = l ^ (n + 1) := by ring

/-- The fluctuation terms of the binomial expansion are `O(qⁿ/W)`. -/
theorem mma_fluct_sum (n : ℕ) {m q W Γ Cf : ℝ} (hm : 0 ≤ m) (hmq : m ≤ Γ * q) (hq : 0 ≤ q)
    (hΓ : 1 ≤ Γ) (hCf : 1 ≤ Cf) (hW : 1 ≤ W) :
    ∑ k ∈ Icc 2 n, (n.choose k : ℝ) * m ^ (n - k) * (Cf / Real.sqrt W * q) ^ k ≤
      2 ^ n * Γ ^ n * Cf ^ n * q ^ n / W := by
  set s := 1 / Real.sqrt W with hs
  have hsW : Real.sqrt W ≥ 1 := by rw [ge_iff_le, Real.one_le_sqrt]; exact hW
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; exact hsW
  have hs2 : s ^ 2 = 1 / W := by
    rw [hs, div_pow, Real.sq_sqrt (by linarith), one_pow]
  set A := Γ ^ n * Cf ^ n * q ^ n / W with hA
  have hterm : ∀ k ∈ Icc 2 n, (n.choose k : ℝ) * m ^ (n - k) * (Cf / Real.sqrt W * q) ^ k ≤
      (n.choose k : ℝ) * A := by
    intro k hk
    obtain ⟨hk2, hkn⟩ := mem_Icc.mp hk
    have e1 : Cf / Real.sqrt W * q = Cf * q * s := by rw [hs]; ring
    rw [e1]
    have hmk : m ^ (n - k) ≤ (Γ * q) ^ (n - k) := pow_le_pow_left₀ hm hmq _
    have hΓk : Γ ^ (n - k) ≤ Γ ^ n := pow_le_pow_right₀ hΓ (Nat.sub_le n k)
    have hCk : Cf ^ k ≤ Cf ^ n := pow_le_pow_right₀ hCf hkn
    have hsk : s ^ k ≤ 1 / W := by
      rw [← hs2]; exact pow_le_pow_of_le_one hs0 hs1 hk2
    have hqn : q ^ (n - k) * q ^ k = q ^ n := by rw [← pow_add, Nat.sub_add_cancel hkn]
    have hc0 : (0 : ℝ) ≤ n.choose k := by positivity
    have key : m ^ (n - k) * (Cf * q * s) ^ k ≤ A := by
      calc m ^ (n - k) * (Cf * q * s) ^ k ≤ (Γ * q) ^ (n - k) * (Cf * q * s) ^ k :=
            mul_le_mul_of_nonneg_right hmk (by positivity)
        _ = Γ ^ (n - k) * Cf ^ k * (q ^ (n - k) * q ^ k) * s ^ k := by ring
        _ ≤ Γ ^ n * Cf ^ n * (q ^ (n - k) * q ^ k) * (1 / W) := by
            have : 0 ≤ q ^ (n - k) * q ^ k := by positivity
            gcongr
        _ = A := by rw [hqn, hA]; ring
    calc (n.choose k : ℝ) * m ^ (n - k) * (Cf * q * s) ^ k
        = (n.choose k : ℝ) * (m ^ (n - k) * (Cf * q * s) ^ k) := by ring
      _ ≤ (n.choose k : ℝ) * A := mul_le_mul_of_nonneg_left key hc0
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Γ := by linarith
    have : 0 ≤ Cf := by linarith
    have : 0 < W := by linarith
    positivity
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_mul]
  have hsub : ∑ k ∈ Icc 2 n, (n.choose k : ℝ) ≤ ∑ k ∈ range (n + 1), (n.choose k : ℝ) := by
    refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
    rw [mem_range]; exact Nat.lt_succ_of_le (mem_Icc.mp hk).2
  have hsum : ∑ k ∈ range (n + 1), (n.choose k : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc (∑ k ∈ Icc 2 n, (n.choose k : ℝ)) * A ≤ 2 ^ n * A :=
        mul_le_mul_of_nonneg_right (hsub.trans hsum.le) hA0
    _ = 2 ^ n * Γ ^ n * Cf ^ n * q ^ n / W := by rw [hA]; ring

/-- `1/(1+u) ≤ 1 - u/(1+ū)` for `0 ≤ u ≤ ū`. -/
theorem mma_inv_le {u ub : ℝ} (hu : 0 ≤ u) (hub : u ≤ ub) :
    1 / (1 + u) ≤ 1 - u / (1 + ub) := by
  have h1 : 0 < 1 + u := by linarith
  have h2 : 0 < 1 + ub := by linarith
  have e : 1 - u / (1 + ub) - 1 / (1 + u) = u * (ub - u) / ((1 + u) * (1 + ub)) := by
    field_simp; ring
  have : 0 ≤ u * (ub - u) / ((1 + u) * (1 + ub)) :=
    div_nonneg (mul_nonneg hu (by linarith)) (by positivity)
  linarith

/-- One step of the mass-moment recursion, as a real inequality. -/
theorem mma_layer {n : ℕ} (hn : 1 ≤ n) {α ω₀ Cm Cf δb : ℝ} (hα : 0 < α) (hω₀ : 0 ≤ ω₀)
    (hCm : 0 ≤ Cm) (hCf : 1 ≤ Cf) (hδb : 0 ≤ δb) :
    ∃ c D₁ D₂ : ℝ, 0 < c ∧ 0 ≤ D₁ ∧ 0 ≤ D₂ ∧ ∀ W q m δ S : ℝ, 1 ≤ W → 0 ≤ q → q ≤ ω₀ * W →
      0 ≤ δ → δ ≤ δb → 0 ≤ m → m ≤ q / (1 + α * q / W) + Cm * (δ + W⁻¹ ^ 2) * q →
      S ≤ m ^ n + ∑ k ∈ Icc 2 n, (n.choose k : ℝ) * m ^ (n - k) * (Cf / Real.sqrt W * q) ^ k →
      ∀ l : ℝ, 0 ≤ l →
        S ≤ q ^ n * (1 - c * l / W) + (c * l ^ (n + 1) + D₁ + D₂ * (W * δ) ^ (n + 1)) / W := by
  set ub := α * ω₀
  set c₁ := α / (1 + ub)
  have hub : 0 ≤ ub := by positivity
  have hc₁ : 0 < c₁ := by positivity
  set t := c₁ / 4
  have ht : 0 < t := by positivity
  set Γ := 1 + Cm * (δb + 1)
  have hΓ : 1 ≤ Γ := by have : 0 ≤ Cm * (δb + 1) := by positivity
                        linarith
  set B := (n : ℝ) * Γ ^ (n - 1)
  have hB : 0 ≤ B := by have : 0 ≤ Γ := by linarith
                        positivity
  set Af := 2 ^ n * Γ ^ n * Cf ^ n
  have hAf : 0 ≤ Af := by have : 0 ≤ Γ := by linarith
                          have : 0 ≤ Cf := by linarith
                          positivity
  set A₂ := B * Cm
  set A₁ := B * Cm + Af
  have hA₂ : 0 ≤ A₂ := mul_nonneg hB hCm
  have hA₁ : 0 ≤ A₁ := add_nonneg hA₂ hAf
  refine ⟨c₁ / 2, A₁ ^ (n + 1) / t ^ n, A₂ ^ (n + 1) / t ^ n, by positivity, by positivity,
    by positivity, fun W q m δ S hW hq hqW hδ hδδ hm hmq hS l hl => ?_⟩
  have hW0 : 0 < W := by linarith
  set u := α * q / W
  have hu0 : 0 ≤ u := by positivity
  have huu : u ≤ ub := by
    have : q / W ≤ ω₀ := by rw [div_le_iff₀ hW0]; linarith
    calc u = α * (q / W) := by ring
      _ ≤ α * ω₀ := mul_le_mul_of_nonneg_left this hα.le
  set φ := 1 / (1 + u)
  have hφ0 : 0 ≤ φ := by positivity
  have hφ1 : φ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hφc : φ ≤ 1 - c₁ * q / W := by
    have h := mma_inv_le hu0 huu
    have e : u / (1 + ub) = c₁ * q / W := by ring
    rw [e] at h; exact h
  set ε := Cm * (δ + W⁻¹ ^ 2)
  have hiW : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
  have hiW0 : 0 ≤ W⁻¹ := by positivity
  have hiW2 : W⁻¹ ^ 2 ≤ W⁻¹ := by nlinarith
  have hε0 : 0 ≤ ε := by positivity
  have hεb : ε ≤ Cm * (δb + 1) := mul_le_mul_of_nonneg_left (by nlinarith) hCm
  have hmq' : m ≤ q * (φ + ε) := by
    have e : q / (1 + α * q / W) = q * φ := by simp only [φ, u]; ring
    rw [e] at hmq; linarith
  -- `mⁿ`
  have hφε : (φ + ε) ^ n ≤ φ + B * ε := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := ma_pow_sub_pow_le k hφ0 (by linarith : φ ≤ φ + ε)
    have hpk : (φ + ε) ^ k ≤ Γ ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    have hφn : φ ^ (k + 1) ≤ φ := by
      rw [pow_succ]; exact mul_le_of_le_one_left hφ0 (pow_le_one₀ hφ0 hφ1)
    have hBk : B = ((k : ℝ) + 1) * Γ ^ k := by
      simp only [B, Nat.add_sub_cancel]; push_cast; ring
    have : ((k : ℝ) + 1) * (φ + ε) ^ k * (φ + ε - φ) ≤ B * ε := by
      rw [hBk, add_sub_cancel_left]
      have : 0 ≤ (k : ℝ) + 1 := by positivity
      gcongr
    linarith
  have hmn : m ^ n ≤ q ^ n * (φ + B * ε) := by
    calc m ^ n ≤ (q * (φ + ε)) ^ n := pow_le_pow_left₀ hm hmq' n
      _ = q ^ n * (φ + ε) ^ n := mul_pow _ _ _
      _ ≤ q ^ n * (φ + B * ε) := mul_le_mul_of_nonneg_left hφε (by positivity)
  -- fluctuation terms
  have hmΓ : m ≤ Γ * q := by
    have : φ + ε ≤ Γ := by linarith
    calc m ≤ q * (φ + ε) := hmq'
      _ ≤ q * Γ := mul_le_mul_of_nonneg_left this hq
      _ = Γ * q := mul_comm _ _
  have hfl := mma_fluct_sum n hm hmΓ hq hΓ hCf hW
  -- Young
  have hqn : 0 ≤ q ^ n := by positivity
  have y1 := young_pow n hq (by positivity : 0 ≤ A₂ * (W * δ)) ht
  have y2 := young_pow n hq hA₁ ht
  have hpow : (A₂ * (W * δ)) ^ (n + 1) = A₂ ^ (n + 1) * (W * δ) ^ (n + 1) := mul_pow _ _ _
  have htan := mma_tangent n hq hl
  -- assemble (multiply through by `W`)
  have key : S * W ≤ q ^ n * W - c₁ / 2 * l * q ^ n + (c₁ / 2 * l ^ (n + 1) +
      A₁ ^ (n + 1) / t ^ n + A₂ ^ (n + 1) / t ^ n * (W * δ) ^ (n + 1)) := by
    have hS' : S * W ≤ (q ^ n * (φ + B * ε) + 2 ^ n * Γ ^ n * Cf ^ n * q ^ n / W) * W :=
      mul_le_mul_of_nonneg_right (by linarith) hW0.le
    have e1 : (q ^ n * (φ + B * ε) + 2 ^ n * Γ ^ n * Cf ^ n * q ^ n / W) * W =
        q ^ n * φ * W + q ^ n * (A₂ * (W * δ)) + A₂ * q ^ n * (W * W⁻¹ ^ 2) + Af * q ^ n := by
      simp only [ε, A₂, Af]; field_simp; ring
    have e2 : W * W⁻¹ ^ 2 = W⁻¹ := by field_simp
    have hφW : q ^ n * φ * W ≤ q ^ n * W - c₁ * q ^ (n + 1) := by
      have : q ^ n * φ * W ≤ q ^ n * (1 - c₁ * q / W) * W := by gcongr
      have e3 : q ^ n * (1 - c₁ * q / W) * W = q ^ n * W - c₁ * q ^ (n + 1) := by
        field_simp; ring
      linarith
    have hA2W : A₂ * q ^ n * W⁻¹ ≤ A₂ * q ^ n := by
      have : 0 ≤ A₂ * q ^ n := by positivity
      exact mul_le_of_le_one_right this hiW
    have e4 : q ^ n * A₁ = A₂ * q ^ n + Af * q ^ n := by simp only [A₁]; ring
    have e5 : t * q ^ (n + 1) = c₁ / 4 * q ^ (n + 1) := rfl
    rw [e1, e2] at hS'
    rw [hpow] at y1
    have htan' : c₁ / 2 * (l * q ^ n - q ^ (n + 1)) ≤ c₁ / 2 * l ^ (n + 1) :=
      mul_le_mul_of_nonneg_left htan (by positivity)
    have hdiv : A₂ ^ (n + 1) * (W * δ) ^ (n + 1) / t ^ n =
        A₂ ^ (n + 1) / t ^ n * (W * δ) ^ (n + 1) := by ring
    linarith [hS', hφW, hA2W, e4, y1, y2, htan', hdiv, e5]
  have e6 : q ^ n * (1 - c₁ / 2 * l / W) + (c₁ / 2 * l ^ (n + 1) + A₁ ^ (n + 1) / t ^ n +
      A₂ ^ (n + 1) / t ^ n * (W * δ) ^ (n + 1)) / W =
      (q ^ n * W - c₁ / 2 * l * q ^ n + (c₁ / 2 * l ^ (n + 1) +
      A₁ ^ (n + 1) / t ^ n + A₂ ^ (n + 1) / t ^ n * (W * δ) ^ (n + 1))) / W := by
    field_simp
  rw [e6, le_div_iff₀ hW0]
  exact key

end BlockBand.Transmission.SourceMixing
