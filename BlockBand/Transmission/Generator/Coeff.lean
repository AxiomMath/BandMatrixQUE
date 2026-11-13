module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Elementary facts about the drift `A_k` and the bracket `B_{kl}`

* `transmissionDrift_congr`: `A_k(P)` reads only `P_1, …, P_k`.
* `abs_transmissionDrift_le`: `|P_j| ≤ g` (`1 ≤ j ≤ k`) gives `|A_k(P)| ≤ D k² g²`.
* `abs_transmissionBracket_le`: `|P_{k+l}|, |P_{k+l+1}| ≤ g` gives `|B_{kl}(P)| ≤ 2D k l g`.
* `continuous_transmissionDrift`: continuity in coordinates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open BlockBand.Internal.Contracts.TransmissionStatements

theorem transmissionDrift_congr (D : ℝ) (k : ℕ) {P P' : ℕ → ℝ}
    (h : ∀ j, 1 ≤ j → j ≤ k → P j = P' j) :
    transmissionDrift D k P = transmissionDrift D k P' := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [transmissionDrift]
  unfold transmissionDrift
  rw [h 1 le_rfl hk, h k hk le_rfl]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
  rw [h j hj1 hj2.le, h (k - j) (by omega) (by omega), h (j + 1) (by omega) (by omega)]

theorem abs_transmissionDrift_le {D : ℝ} (hD : 0 ≤ D) (k : ℕ) {P : ℕ → ℝ} {g : ℝ}
    (hP : ∀ j, 1 ≤ j → j ≤ k → |P j| ≤ g) :
    |transmissionDrift D k P| ≤ D * k ^ 2 * g ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [transmissionDrift]
  have hg : 0 ≤ g := (abs_nonneg _).trans (hP 1 le_rfl hk)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 ≤ D * k / 2 := by positivity
  have hterm : ∀ j ∈ Finset.Ico 1 k, |P j * P (k - j) - P (j + 1) * P (k - j)| ≤ 2 * g ^ 2 := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    have h1 := hP j hj1 hj2.le
    have h2 := hP (k - j) (by omega) (by omega)
    have h3 := hP (j + 1) (by omega) (by omega)
    calc |P j * P (k - j) - P (j + 1) * P (k - j)|
        ≤ |P j| * |P (k - j)| + |P (j + 1)| * |P (k - j)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ g * g + g * g := by gcongr
      _ = 2 * g ^ 2 := by ring
  have hsum : |∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))| ≤
      (k - 1 : ℝ) * (2 * g ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk, Nat.cast_one]
  have hfirst : |-(D * k / 2) * P 1 * P k| ≤ D * k / 2 * g ^ 2 := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hc]
    have := mul_le_mul (hP 1 le_rfl hk) (hP k hk le_rfl) (abs_nonneg _) hg
    nlinarith
  unfold transmissionDrift
  calc _ ≤ |-(D * k / 2) * P 1 * P k| +
        |D * k / 2 * ∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))| :=
        abs_add_le _ _
    _ ≤ D * k / 2 * g ^ 2 + D * k / 2 * ((k - 1 : ℝ) * (2 * g ^ 2)) := by
        rw [abs_mul _ (∑ _ ∈ _, _), abs_of_nonneg hc]; gcongr
    _ ≤ D * k ^ 2 * g ^ 2 := by
        have : 0 ≤ D * k * g ^ 2 := by positivity
        nlinarith

theorem abs_transmissionBracket_le {D : ℝ} (hD : 0 ≤ D) (k l : ℕ) {P : ℕ → ℝ} {g : ℝ}
    (h1 : |P (k + l)| ≤ g) (h2 : |P (k + l + 1)| ≤ g) :
    |transmissionBracket D k l P| ≤ 2 * D * k * l * g := by
  unfold transmissionBracket
  have hc : 0 ≤ D * k * l := by positivity
  rw [abs_mul, abs_of_nonneg hc]
  have := (abs_sub _ _).trans (add_le_add h1 h2)
  nlinarith

theorem continuous_transmissionDrift {X : Type*} [TopologicalSpace X] (D : ℝ) (k : ℕ)
    {v : X → ℕ → ℝ} (hv : ∀ j, Continuous fun x => v x j) :
    Continuous fun x => transmissionDrift D k (v x) := by
  unfold transmissionDrift
  refine ((continuous_const.mul (hv 1)).mul (hv k)).add (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun j _ =>
    ((hv j).mul (hv (k - j))).sub ((hv (j + 1)).mul (hv (k - j)))

theorem continuous_transmissionBracket {X : Type*} [TopologicalSpace X] (D : ℝ) (k l : ℕ)
    {v : X → ℕ → ℝ} (hv : ∀ j, Continuous fun x => v x j) :
    Continuous fun x => transmissionBracket D k l (v x) := by
  unfold transmissionBracket
  exact continuous_const.mul ((hv _).sub (hv _))

end BlockBand.Transmission.Generator
