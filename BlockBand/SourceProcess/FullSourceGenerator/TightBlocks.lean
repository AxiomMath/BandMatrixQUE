module

public import BlockBand.SourceProcess.FullSourceGenerator.TruncMart

/-!
# The discrete modulus of continuity through blocks

Real increments `d_i` adapted to `G_{i+1}`, with conditional drift `|E[d_i|G_i]| ≤ a + g_i` and
conditional second moment `E[d_i²|G_i] ≤ c + f_i` (`f, g ≥ 0` integrable). Cut `[0, Nℓ]` into
the `N` blocks `[mℓ, (m+1)ℓ]`.

* `abs_sub_le_three` (deterministic): if every block oscillation `|x(mℓ+y) - x(mℓ)|`, `y ≤ ℓ`,
  is at most `λ`, then `|x_b - x_a| ≤ 3λ` for `a ≤ b ≤ Nℓ`, `b - a ≤ ℓ` (same or adjacent blocks).
* `modulus_tail`: `P(∃ a ≤ b ≤ Nℓ, b ≤ a + ℓ, |Σ_{a≤i<b} d_i| > 3λ + ℓa + κ)` is at most
  `(16c²Nℓ·ℓ + 16F² + 8λ²F + 48D)/λ⁴ + G/κ` (`F = Σ E f_i`, `D = Σ E d_i⁴`, `G = Σ E g_i`):
  `block_tail` on each block, summed, and Markov for the summed drift errors.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Set Finset

/-- **Same or adjacent blocks**: the oscillation over a window of length `ℓ` is at most three
block oscillations. -/
theorem abs_sub_le_three {x : ℕ → ℝ} {ℓ N : ℕ} (hℓ : 0 < ℓ) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ∀ m < N, ∀ y ≤ ℓ, |x (m * ℓ + y) - x (m * ℓ)| ≤ lam) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ N * ℓ) (hba : b ≤ a + ℓ) : |x b - x a| ≤ 3 * lam := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp; linarith
  set m := a / ℓ
  have ha : m * ℓ + a % ℓ = a := Nat.div_add_mod' a ℓ
  have hr : a % ℓ < ℓ := Nat.mod_lt a hℓ
  have hmN : m < N := by
    by_contra hc
    have : N * ℓ ≤ m * ℓ := Nat.mul_le_mul_right ℓ (not_lt.mp hc)
    omega
  have h1 : |x a - x (m * ℓ)| ≤ lam := by
    have := h m hmN (a % ℓ) hr.le; rwa [ha] at this
  by_cases hcase : b ≤ m * ℓ + ℓ
  · obtain ⟨y, rfl⟩ : ∃ y, b = m * ℓ + y := ⟨b - m * ℓ, by omega⟩
    have h2 := h m hmN y (by omega)
    calc |x (m * ℓ + y) - x a| ≤ |x (m * ℓ + y) - x (m * ℓ)| + |x a - x (m * ℓ)| := by
          rw [abs_sub_comm (x a)]; exact abs_sub_le _ _ _
      _ ≤ 3 * lam := by linarith
  · have hm1 : m + 1 < N := by
      by_contra hc
      have : N * ℓ ≤ (m + 1) * ℓ := Nat.mul_le_mul_right ℓ (not_lt.mp hc)
      rw [Nat.succ_mul] at this; omega
    obtain ⟨y, rfl⟩ : ∃ y, b = (m + 1) * ℓ + y := ⟨b - (m + 1) * ℓ, by rw [Nat.succ_mul]; omega⟩
    have h2 := h (m + 1) hm1 y (by rw [Nat.succ_mul] at hba; omega)
    have h3 := h m hmN ℓ le_rfl
    rw [← Nat.succ_mul] at h3
    calc |x ((m + 1) * ℓ + y) - x a| ≤ |x ((m + 1) * ℓ + y) - x ((m + 1) * ℓ)| +
          |x ((m + 1) * ℓ) - x (m * ℓ)| + |x a - x (m * ℓ)| := by
          rw [abs_sub_comm (x a)]
          exact (abs_sub_le _ (x (m * ℓ)) _).trans (add_le_add_left (abs_sub_le _ _ _) _)
      _ ≤ 3 * lam := by linarith

/-- Regrouping a sum over `[0, Nℓ)` into the `N` blocks. -/
theorem sum_range_mul_eq (N ℓ : ℕ) (u : ℕ → ℝ) :
    ∑ i ∈ range (N * ℓ), u i = ∑ m ∈ range N, ∑ i ∈ range ℓ, u (m * ℓ + i) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The real arithmetic of the summed block bounds. -/
theorem sum_block_bound_le (N ℓ : ℕ) (c lam : ℝ) (Fm Dm : ℕ → ℝ) (hF0 : ∀ m, 0 ≤ Fm m) :
    ∑ m ∈ range N, (8 * (c * ℓ + Fm m) ^ 2 + 8 * lam ^ 2 * Fm m + 48 * Dm m) ≤
      16 * c ^ 2 * ((N : ℝ) * ℓ) * ℓ + 16 * (∑ m ∈ range N, Fm m) ^ 2 +
        8 * lam ^ 2 * ∑ m ∈ range N, Fm m + 48 * ∑ m ∈ range N, Dm m := by
  set F := ∑ m ∈ range N, Fm m
  have hle : ∀ m ∈ range N, Fm m ≤ F := fun m hm =>
    Finset.single_le_sum (f := Fm) (fun i _ => hF0 i) hm
  have hsq : ∑ m ∈ range N, Fm m ^ 2 ≤ F ^ 2 := by
    calc ∑ m ∈ range N, Fm m ^ 2 ≤ ∑ m ∈ range N, Fm m * F :=
          Finset.sum_le_sum fun m hm => by rw [sq]; exact mul_le_mul_of_nonneg_left (hle m hm) (hF0 m)
      _ = F ^ 2 := by rw [← Finset.sum_mul, sq]
  have h1 : ∀ m ∈ range N, 8 * (c * ℓ + Fm m) ^ 2 + 8 * lam ^ 2 * Fm m + 48 * Dm m ≤
      (16 * c ^ 2 * ℓ * ℓ + 16 * Fm m ^ 2) + (8 * lam ^ 2 * Fm m + 48 * Dm m) := fun m _ => by
    nlinarith [sq_nonneg (c * ℓ - Fm m)]
  refine (Finset.sum_le_sum h1).trans ?_
  have e1 : ∑ m ∈ range N, ((16 * c ^ 2 * ℓ * ℓ + 16 * Fm m ^ 2) + (8 * lam ^ 2 * Fm m +
      48 * Dm m)) = 16 * c ^ 2 * ((N : ℝ) * ℓ) * ℓ + 16 * ∑ m ∈ range N, Fm m ^ 2 +
        8 * lam ^ 2 * F + 48 * ∑ m ∈ range N, Dm m := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, F]
    ring
  rw [e1]
  nlinarith [hsq]

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (G : ℕ → MeasurableSpace Ω) (hG : ∀ i, G i ≤ m0) (hGmono : Monotone G)

include hG hGmono in
/-- **The discrete modulus bound.** -/
theorem modulus_tail (N ℓ : ℕ) (hℓ : 0 < ℓ) (d f g : ℕ → Ω → ℝ) (c a lam κ : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hlam : 0 < lam) (hκ : 0 < κ)
    (hdm : ∀ i, StronglyMeasurable[G (i + 1)] (d i))
    (hd4 : ∀ i < N * ℓ, Integrable (fun ω => d i ω ^ 4) μ)
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hf : ∀ i < N * ℓ, Integrable (f i) μ)
    (hvar : ∀ i < N * ℓ, μ[fun ω => d i ω ^ 2 | G i] ≤ᵐ[μ] fun ω => c + f i ω)
    (hg0 : ∀ i ω, 0 ≤ g i ω) (hg : ∀ i < N * ℓ, Integrable (g i) μ)
    (hdrift : ∀ i < N * ℓ, ∀ᵐ ω ∂μ, |μ[d i | G i] ω| ≤ a + g i ω) :
    μ {ω | ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
        3 * lam + ℓ * a + κ < |∑ i ∈ Finset.Ico x y, d i ω|} ≤
      ENNReal.ofReal ((16 * c ^ 2 * ((N : ℝ) * ℓ) * ℓ +
          16 * (∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ) ^ 2 +
          8 * lam ^ 2 * ∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ +
          48 * ∑ i ∈ range (N * ℓ), ∫ ω, d i ω ^ 4 ∂μ) / lam ^ 4) +
        ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ ω, g i ω ∂μ) / κ) := by
  set M : ℕ → Ω → ℝ := fun x ω => ∑ i ∈ range x, (d i ω - μ[d i | G i] ω) with hM
  set S0 : Set Ω := {ω | ¬ ∀ i, i < N * ℓ → |μ[d i | G i] ω| ≤ a + g i ω}
  set S1 : Set Ω := {ω | κ ≤ ∑ i ∈ range (N * ℓ), g i ω}
  set B : ℕ → Set Ω := fun m => {ω | ∃ y ≤ ℓ, lam < |∑ i ∈ range y,
    (d (m * ℓ + i) ω - μ[d (m * ℓ + i) | G (m * ℓ + i)] ω)|}
  -- the inclusion
  have hincl : {ω | ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧
      3 * lam + ℓ * a + κ < |∑ i ∈ Finset.Ico x y, d i ω|} ⊆
      S0 ∪ S1 ∪ ⋃ m ∈ range N, B m := by
    intro ω ⟨x, y, hxy, hyN, hyx, hgt⟩
    by_contra hout
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hout
    obtain ⟨⟨h0, h1⟩, h2⟩ := hout
    simp only [S0, Set.mem_ofPred_eq, not_not] at h0
    simp only [S1, Set.mem_ofPred_eq, not_le] at h1
    have hblk : ∀ m < N, ∀ z ≤ ℓ, |M (m * ℓ + z) ω - M (m * ℓ) ω| ≤ lam := fun m hm z hz => by
      have := h2 m (Finset.mem_range.mpr hm)
      simp only [B, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at this
      simp only [hM, Finset.sum_range_add, add_sub_cancel_left]
      exact this z hz
    have hmart := abs_sub_le_three (x := fun z => M z ω) hℓ hlam.le hblk hxy hyN hyx
    have hsplit : ∑ i ∈ Finset.Ico x y, d i ω =
        (M y ω - M x ω) + ∑ i ∈ Finset.Ico x y, μ[d i | G i] ω := by
      simp only [hM, ← Finset.sum_Ico_eq_sub _ hxy, ← Finset.sum_add_distrib, sub_add_cancel]
    have hsub : Finset.Ico x y ⊆ range (N * ℓ) := fun i hi =>
      Finset.mem_range.mpr ((Finset.mem_Ico.mp hi).2.trans_le hyN)
    have hdr : |∑ i ∈ Finset.Ico x y, μ[d i | G i] ω| ≤ ℓ * a + κ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i hi => h0 i (Finset.mem_range.mp (hsub hi))).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hc1 : ((y - x : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast (by omega : y - x ≤ ℓ)
      have hc2 : ∑ i ∈ Finset.Ico x y, g i ω ≤ ∑ i ∈ range (N * ℓ), g i ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hg0 i ω
      nlinarith
    have := abs_add_le (M y ω - M x ω) (∑ i ∈ Finset.Ico x y, μ[d i | G i] ω)
    rw [← hsplit] at this
    linarith
  -- the three pieces
  have hS0 : μ S0 = 0 := by
    have hae : ∀ᵐ ω ∂μ, ∀ i, i < N * ℓ → |μ[d i | G i] ω| ≤ a + g i ω :=
      ae_all_iff.2 fun i => by
        by_cases hi : i < N * ℓ
        · filter_upwards [hdrift i hi] with ω hω _ using hω
        · exact Filter.Eventually.of_forall fun ω h => absurd h hi
    exact ae_iff.mp hae
  have hgI : Integrable (fun ω => ∑ i ∈ range (N * ℓ), g i ω) μ :=
    integrable_finsetSum _ fun i hi => hg i (Finset.mem_range.mp hi)
  have hS1 : μ S1 ≤ ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ ω, g i ω ∂μ) / κ) := by
    have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun i _ => hg0 i ω) hgI κ
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hκ, ← integral_finsetSum _ fun i hi => hg i (Finset.mem_range.mp hi)]
    linarith
  set Fm : ℕ → ℝ := fun m => ∑ i ∈ range ℓ, ∫ ω, f (m * ℓ + i) ω ∂μ
  set Dm : ℕ → ℝ := fun m => ∑ i ∈ range ℓ, ∫ ω, d (m * ℓ + i) ω ^ 4 ∂μ
  have hBm : ∀ m < N, μ (B m) ≤ ENNReal.ofReal ((8 * (c * ℓ + Fm m) ^ 2 +
      8 * lam ^ 2 * Fm m + 48 * Dm m) / lam ^ 4) := fun m hm => by
    have hlt : ∀ i < ℓ, m * ℓ + i < N * ℓ := fun i hi => by
      have : (m + 1) * ℓ ≤ N * ℓ := Nat.mul_le_mul_right ℓ hm
      rw [Nat.succ_mul] at this; omega
    exact block_tail (fun i => G (m * ℓ + i)) (fun i => hG _)
      (fun i j hij => hGmono (by omega)) ℓ (fun i => d (m * ℓ + i)) (fun i => f (m * ℓ + i))
      c lam hc hlam (fun i => hdm _) (fun i hi => hd4 _ (hlt i hi)) (fun i => hf0 _)
      (fun i hi => hf _ (hlt i hi)) (fun i hi => hvar _ (hlt i hi))
  have hF0 : ∀ m, 0 ≤ Fm m := fun m => Finset.sum_nonneg fun i _ => integral_nonneg (hf0 _)
  have hFsum : ∑ m ∈ range N, Fm m = ∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ :=
    (sum_range_mul_eq N ℓ fun i => ∫ ω, f i ω ∂μ).symm
  have hDsum : ∑ m ∈ range N, Dm m = ∑ i ∈ range (N * ℓ), ∫ ω, d i ω ^ 4 ∂μ :=
    (sum_range_mul_eq N ℓ fun i => ∫ ω, d i ω ^ 4 ∂μ).symm
  have hD0 : ∀ m, 0 ≤ Dm m := fun m => Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => Even.pow_nonneg (by decide) _
  have hU : μ (⋃ m ∈ range N, B m) ≤ ENNReal.ofReal ((16 * c ^ 2 * ((N : ℝ) * ℓ) * ℓ +
      16 * (∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ) ^ 2 +
      8 * lam ^ 2 * ∑ i ∈ range (N * ℓ), ∫ ω, f i ω ∂μ +
      48 * ∑ i ∈ range (N * ℓ), ∫ ω, d i ω ^ 4 ∂μ) / lam ^ 4) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun m hm => hBm m (Finset.mem_range.mp hm)).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun m _ => by
      have := hF0 m; have := hD0 m; positivity]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.sum_div, ← hFsum, ← hDsum]
    exact div_le_div_of_nonneg_right (sum_block_bound_le N ℓ c lam Fm Dm hF0) (by positivity)
  refine (measure_mono hincl).trans ?_
  refine ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)).trans ?_
  rw [hS0, zero_add, add_comm]
  exact add_le_add hU hS1

end BlockBand.SourceProcess.FullSourceGenerator
