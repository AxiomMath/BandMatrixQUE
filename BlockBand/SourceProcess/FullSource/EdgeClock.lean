module

public import BlockBand.SourceProcess.FullSource.Clock

/-!
# `EdgeClockMomentsContract` from the propagation-length tag bound

`Tr Q_j = Σ_{k<j} q((k+1)/W) W⁻¹ (W⁻¹Tr Y_{j;k})`, `q = 1_{[t₁,t₁+R]}`. The nonzero terms have
`t₁W ≤ k+1 ≤ (t₁+R)W` (at most `RW + 1` of them, `card_window_le`) and propagation
`j - k ≤ (R + R₀)W + 1 ≤ 2R₀W + 1`; so `‖Tr Q_j‖_p ≤ (R₀ + 1) C_{p,2R₀}` with the constant of
`TagPropagationBulk` at `R = 2R₀`, chosen before `T` (`edgeClock_of_propagation`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- At most `RW + 1` integers `k` have `t₁W ≤ k + 1 ≤ (t₁+R)W`. -/
theorem card_window_le {W : ℝ} (hW : 0 ≤ W) {t₁ R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    (((Finset.range j).filter fun k : ℕ => t₁ * W ≤ k + 1 ∧ (k : ℝ) + 1 ≤ (t₁ + R) * W).card : ℝ)
      ≤ R * W + 1 := by
  set a : ℕ := ⌈t₁ * W⌉₊ - 1
  have hsub : (Finset.range j).filter (fun k : ℕ => t₁ * W ≤ k + 1 ∧ (k : ℝ) + 1 ≤ (t₁ + R) * W)
      ⊆ Finset.Icc a (a + ⌊R * W⌋₊) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, h1, h2⟩ := hk
    have hc : ⌈t₁ * W⌉₊ ≤ k + 1 := Nat.ceil_le.2 (by exact_mod_cast h1)
    have hc' : t₁ * W ≤ ⌈t₁ * W⌉₊ ∨ t₁ * W < 0 := by
      rcases le_or_gt 0 (t₁ * W) with h | h
      · exact Or.inl (Nat.le_ceil _)
      · exact Or.inr h
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have : (k : ℝ) - a ≤ R * W := by
      rcases hc' with h | h
      · have ha : ((a : ℕ) : ℝ) ≥ (⌈t₁ * W⌉₊ : ℝ) - 1 := by
          simp only [a]; rcases Nat.eq_zero_or_pos ⌈t₁ * W⌉₊ with h0 | h0
          · rw [h0]; simp
          · rw [Nat.cast_sub h0]; simp
        nlinarith
      · have h0 : ⌈t₁ * W⌉₊ = 0 := Nat.ceil_eq_zero.2 h.le
        have ha : a = 0 := by simp only [a, h0]
        rw [ha]; push_cast
        nlinarith
    have hk : k ≤ a + ⌊R * W⌋₊ := by
      have := Nat.le_floor (show ((k - a : ℕ) : ℝ) ≤ R * W by
        rcases le_total a k with h | h
        · rw [Nat.cast_sub h]; linarith
        · rw [Nat.sub_eq_zero_of_le h]; simp; positivity)
      omega
    exact hk
  calc (((Finset.range j).filter fun k : ℕ => t₁ * W ≤ k + 1 ∧ (k : ℝ) + 1 ≤ (t₁ + R) * W).card : ℝ)
      ≤ (Finset.Icc a (a + ⌊R * W⌋₊)).card := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊R * W⌋₊ + 1 := by
        rw [Nat.card_Icc, show a + ⌊R * W⌋₊ + 1 - a = ⌊R * W⌋₊ + 1 by omega]; push_cast; ring
    _ ≤ R * W + 1 := by linarith [Nat.floor_le (mul_nonneg hR hW)]

/-- **`EdgeClockMomentsContract` from the propagation-length tag bound.** -/
theorem edgeClock_of_propagation (h : TagPropagationBulk) : EdgeClockMomentsContract := by
  intro b hb hb' E hE1 hE2 R₀ p hR₀ hp
  obtain ⟨hκ, hE⟩ := mem_bulkInterval_min hE1 hE2
  obtain ⟨Ct, hCt⟩ := h b hb hb' _ (2 * R₀) p hκ hp
  set C' := max Ct 0
  have hC' : 0 ≤ C' := le_max_right _ _
  refine ⟨(R₀ + 1) * C', fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hCt T
  refine ⟨max W₀ 1, fun W hW t₁ R ht₁ hR hRR₀ hT j hj => ?_⟩
  have hWW₀ : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW1
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  set q : ℝ → ℝ := (Set.Icc t₁ (t₁ + R)).indicator fun _ => (1 : ℝ)
  set S := (Finset.range j).filter fun k : ℕ => t₁ * W ≤ k + 1 ∧ (k : ℝ) + 1 ≤ (t₁ + R) * W
  set f : ℕ → GrowthPath W → ℂ := fun k ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace
  have e : (fun ω => (intervalSource b E W j q ω).trace) = ∑ k ∈ Finset.range j,
      fun ω => ((q (((k + 1 : ℕ) : ℝ) / W) / W : ℝ) : ℂ) • f k ω := by
    funext ω
    rw [Finset.sum_apply, intervalSource, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    simp only [f]
    have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hWr.ne'
    push_cast
    field_simp
  rw [e]
  refine (eLpNorm_sum_le hp1).trans ?_
  have hterm : ∀ k ∈ Finset.range j,
      eLpNorm (fun ω => ((q (((k + 1 : ℕ) : ℝ) / W) / W : ℝ) : ℂ) • f k ω) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ if k ∈ S then ENNReal.ofReal (C' / W) else 0 := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [show (fun ω => ((q (((k + 1 : ℕ) : ℝ) / W) / W : ℝ) : ℂ) • f k ω) =
      ((q (((k + 1 : ℕ) : ℝ) / W) / W : ℝ) : ℂ) • f k from rfl, eLpNorm_const_smul]
    by_cases hq : (((k + 1 : ℕ) : ℝ) / W) ∈ Set.Icc t₁ (t₁ + R)
    · have hq1 : q (((k + 1 : ℕ) : ℝ) / W) = 1 := Set.indicator_of_mem hq _
      obtain ⟨h1, h2⟩ := hq
      push_cast at h1 h2
      have h1' : t₁ * W ≤ k + 1 := by rwa [le_div_iff₀ hWr] at h1
      have h2' : (k : ℝ) + 1 ≤ (t₁ + R) * W := by rwa [div_le_iff₀ hWr] at h2
      have hkS : k ∈ S := Finset.mem_filter.2 ⟨hk, h1', h2'⟩
      simp only [hkS, ↓reduceIte]
      rw [hq1]
      have hjT : (j : ℝ) ≤ T * W := hj.trans (mul_le_mul_of_nonneg_right hT hWr.le)
      have hjR : (j : ℝ) ≤ k + 2 * R₀ * W + 1 := by nlinarith
      have hb := hW₀ W hWW₀ E hE j k hk' hjT hjR
      rw [show ‖((1 / W : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (1 / W) by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)],
        show C' / W = 1 / W * C' by ring, ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_of_nonneg_left (hb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        zero_le
    · have hq0 : q (((k + 1 : ℕ) : ℝ) / W) = 0 := Set.indicator_of_notMem hq _
      rw [hq0]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  have hSf : (Finset.range j).filter (· ∈ S) = S := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (Finset.filter_subset _ _)]
  rw [← Finset.sum_filter, hSf, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ R * W + 1 := card_window_le hWr.le hR j
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (S.card : ℝ) * (C' / W) ≤ (R * W + 1) * (C' / W) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have h2 : (R * W + 1) * (C' / W) ≤ (R₀ + 1) * C' := by
    rw [show (R * W + 1) * (C' / W) = (R + 1 / W) * C' by field_simp]
    have : 1 / (W : ℝ) ≤ 1 := by rw [div_le_one hWr]; exact_mod_cast hW1
    nlinarith
  linarith

end BlockBand.SourceProcess.FullSource
