module

public import BlockBand.Palm.MomentFlow.IndProps
public import BlockBand.Palm.MomentFlow.StartBridge
public import BlockBand.Palm.FreshPalmAssembly

/-!
# Terminal form: `CM(r, M)` for all `r ≥ 1` gives `ConditionalMomentsStatement`

* `regVersion_exists`: regular versions exist for `0 < a ≤ c` (`momentGeneratorBridge_start`).
* `flowStart_pos`: `0 < c₀ - N^{-1/100}` for `N ≥ (c₀/2)^{-100}`.
* `window_le_w`: `N^{-1+1/2} ≤ 1 · w/N` for `N ≥ 1`.
* **`conditionalMoments_of_CM`**: `(∀ N, DysonBrownianMotion N) → (∀ r ≥ 1, CMWin r 1) →
  FreshPalmAssembly.ConditionalMomentsStatement`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Transmission
open scoped ENNReal

variable {N : ℕ}

theorem regVersion_exists (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (q : Fin N → ℂ) (r : ℕ) :
    ∃ Φ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F a c q r Φ :=
  momentGeneratorBridge_start hDBM F hF ha hac q r

theorem flowStart_pos {c₀ : ℝ} (hc₀ : 0 < c₀) {N : ℕ} (hN : (c₀ / 2) ^ (-100 : ℝ) ≤ N) :
    0 < c₀ - cmTau N := by
  have := FreshPalmAssembly.rpow_neg_hundredth_le (by linarith : 0 < c₀ / 2) hN
  unfold cmTau; linarith

theorem cmW_div (hN : 0 < N) : cmW N / N = (N : ℝ) ^ (-(1 / 600 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cmW
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hNp]
  norm_num

theorem window_le_w (hN : 1 ≤ N) : (N : ℝ) ^ (-1 + (1 / 2 : ℝ)) ≤ 1 * cmW N / N := by
  rw [one_mul, cmW_div (by omega)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)

theorem inRank_single (k : Fin N) (r : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    InRank k ρ (fun i => if i = k then r else 0) := by
  intro j hj
  have : j = k := by by_contra h; simp [h] at hj
  subst this; simpa [labelDist] using hρ

theorem single_mem_sector (k : Fin N) (r : ℕ) : (fun i => if i = k then r else 0) ∈ sector N r := by
  rw [mem_sector]; simp

theorem cmT_le_one (k : ℕ) : cmT k ≤ 1 := by
  unfold cmT; have : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
  linarith

theorem cmTau_pos (hN : 0 < N) : 0 < cmTau N := by
  unfold cmTau; exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

/-- **The terminal reduction**: `CMWin r 1` for all `r ≥ 1` gives `ConditionalMomentsStatement`. -/
theorem conditionalMoments_of_CM (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hCM : ∀ r : ℕ, 1 ≤ r → CMWin r 1) : FreshPalmAssembly.ConditionalMomentsStatement := by
  intro A c₀ r₀ s₀ v₀ hK r hr
  obtain ⟨κ, C, hκ, hD⟩ := hCM r hr A c₀ r₀ s₀ v₀ hK
  refine ⟨1 / 2, κ, C + 1, by norm_num, hκ, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hD (max D κ)
  refine ⟨max N₀ (⌈(c₀ / 2) ^ (-100 : ℝ)⌉₊ + 1), fun N hN F E hC q hq => ?_⟩
  have hN₀' : N₀ ≤ N := le_of_max_le_left hN
  have hNc : (c₀ / 2) ^ (-100 : ℝ) ≤ N := by
    have h1 := le_of_max_le_right hN
    have h2 : (c₀ / 2) ^ (-100 : ℝ) ≤ (⌈(c₀ / 2) ^ (-100 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈(c₀ / 2) ^ (-100 : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    push_cast at h3; linarith
  have hN1 : 1 ≤ N := by have := le_of_max_le_right hN; omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 < c₀ - cmTau N := flowStart_pos hK.1 hNc
  have hτ := cmTau_pos (show 0 < N by omega)
  obtain ⟨B, hB, hPB, hall⟩ := hN₀ N hN₀' F E hC q hq
  obtain ⟨Φ, hΦ⟩ := regVersion_exists (hDBM N) hC.1 ha (c := c₀) (by linarith [hτ]) q r
  refine ⟨B, hB, (hPB.trans (ENNReal.ofReal_le_ofReal ?_)), fun k => ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by
      simp only [neg_le_neg_iff]; exact le_max_left _ _)
  have hc₀ : c₀ ∈ Icc (c₀ - cmTau N) c₀ := ⟨by linarith, le_rfl⟩
  have hver := hΦ.1 c₀ hc₀ _ (single_mem_sector k r)
  filter_upwards [hall Φ hΦ, hver] with ω hω hv hωB hlam
  obtain ⟨e, he, hb⟩ := hω hωB
  have hσ : c₀ ∈ Icc (c₀ - cmTau N + cmT r * cmTau N) c₀ := by
    refine ⟨?_, le_rfl⟩
    have := cmT_le_one r
    nlinarith
  have h1 := hb c₀ hσ k (hlam.trans (window_le_w hN1)) _ (single_mem_sector k r)
    (inRank_single k r (by unfold cmW; positivity))
  have hec : e c₀ ≤ (N : ℝ) ^ (-max D κ) := he.2.2.2
  have hκD : (N : ℝ) ^ (-max D κ) ≤ (N : ℝ) ^ (-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by
      simp only [neg_le_neg_iff]; exact le_max_right _ _)
  show |condMoment F (c₀ - cmTau N) c₀ q c₀ (fun i => if i = k then r else 0) ω - 1| ≤ _
  rw [← hv]
  linarith

end BlockBand.Palm.MomentFlow
