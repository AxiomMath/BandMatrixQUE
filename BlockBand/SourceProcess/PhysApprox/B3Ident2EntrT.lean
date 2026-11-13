module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Fatou
public import BlockBand.SourceProcess.CapCond.Recon

/-!
# Continuous approximations of the entrance eigenvalues

`t_k(ν)` (`seqExtract`) is not continuous in the weak topology of `FiniteMeasure [0,1]`. On trace
measures of transmission sequences it is uniformly approximated by a continuous functional built
from the smoothed counts `smCount`:
`T^δ_k(ν) = δ Σ_{j < M} cl01(smCount((j+1)δ, (j+2)δ)(ν) − k)`.

* `phiK_le`, `le_phiK` (`integral_cutWeight_le`, `le_smCount`):
  `1{(j+2)δ ≤ t_k} ≤ φ_j ≤ 1{(j+1)δ ≤ t_k}`.
* `sum_upper`, `sum_lower`: the counting bounds.
* **`abs_TK_sub_le`**: `|T^δ_k(ν) − t_k| ≤ 2δ` when `ν = Σ t_i δ_{t_i}`, `Mδ ≥ 1`; `TK_mem`:
  `T^δ_k(ν) ∈ [0, 1]`.
* `continuous_TK`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

/-- The `j`-th smoothed count step of `t_k`. -/
def phiK (δ : ℝ) (k j : ℕ) (ν : FiniteMeasure unitInterval) : ℝ :=
  cl01 (CapCond.smCount (((j : ℝ) + 1) * δ) (((j : ℝ) + 2) * δ) ν - k)

/-- **The continuous approximation of `t_k`.** -/
def TK (δ : ℝ) (M k : ℕ) (ν : FiniteMeasure unitInterval) : ℝ :=
  δ * ∑ j ∈ Finset.range M, phiK δ k j ν

theorem continuous_TK {δ : ℝ} (hδ : 0 < δ) (M k : ℕ) : Continuous (TK δ M k) :=
  continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_cl01.comp
    ((CapCond.continuous_smCount (by positivity) _).sub continuous_const))

theorem phiK_nonneg (δ : ℝ) (k j : ℕ) (ν : FiniteMeasure unitInterval) : 0 ≤ phiK δ k j ν :=
  cl01_nonneg _

variable {δ : ℝ} {ν : FiniteMeasure unitInterval} {t : ℕ → ℝ}

theorem phiK_le (hδ : 0 < δ) (hν : (ν : Measure unitInterval) = seqTraceMeasure t)
    (ht : IsTransmissionSequence t) (k j : ℕ) :
    phiK δ k j ν ≤ if ((j : ℝ) + 1) * δ ≤ t k then 1 else 0 := by
  split_ifs with hc
  · exact cl01_le_one _
  · have h1 : CapCond.smCount (((j : ℝ) + 1) * δ) (((j : ℝ) + 2) * δ) ν ≤ k :=
      CapCond.integral_cutWeight_le ν hν ht (by positivity) (by nlinarith) (not_le.1 hc)
    unfold phiK cl01
    exact max_le le_rfl ((min_le_right _ _).trans (by linarith))

theorem le_phiK (hδ : 0 < δ) (hν : (ν : Measure unitInterval) = seqTraceMeasure t)
    (ht : IsTransmissionSequence t) (k j : ℕ) :
    (if ((j : ℝ) + 2) * δ ≤ t k then 1 else 0) ≤ phiK δ k j ν := by
  split_ifs with hc
  · have h1 := CapCond.le_smCount ν hν ht (a := ((j : ℝ) + 1) * δ) (by positivity)
      (by nlinarith) hc
    unfold phiK cl01
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · exact phiK_nonneg _ _ _ _

theorem sum_upper (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) (M : ℕ) (g : ℕ → ℝ)
    (hg : ∀ j, g j ≤ if ((j : ℝ) + 1) * δ ≤ x then 1 else 0) :
    δ * ∑ j ∈ Finset.range M, g j ≤ x := by
  classical
  set n := ⌊x / δ⌋₊
  have h1 : ∑ j ∈ Finset.range M, g j ≤ ∑ j ∈ Finset.range M, (if j < n then (1 : ℝ) else 0) :=
    Finset.sum_le_sum fun j _ => (hg j).trans (by
      split_ifs with h2 h3 h3
      · exact le_rfl
      · exfalso; apply h3
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_floor (by
          rw [le_div_iff₀ hδ]; push_cast; linarith))
      · exact zero_le_one
      · exact le_rfl)
  have h2 : ∑ j ∈ Finset.range M, (if j < n then (1 : ℝ) else 0) ≤ n := by
    rw [Finset.sum_boole]
    have : ({j ∈ Finset.range M | j < n} : Finset ℕ) ⊆ Finset.range n := fun j hj =>
      Finset.mem_range.2 (Finset.mem_filter.1 hj).2
    exact_mod_cast (Finset.card_le_card this).trans (Finset.card_range n).le
  have h3 : δ * n ≤ x := by
    have := Nat.floor_le (div_nonneg hx hδ.le)
    rw [le_div_iff₀ hδ] at this; linarith
  nlinarith

theorem sum_lower (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) {M : ℕ}
    (hM : 1 ≤ (M : ℝ) * δ) (g : ℕ → ℝ) (hg0 : ∀ j, 0 ≤ g j)
    (hg : ∀ j : ℕ, (if ((j : ℝ) + 2) * δ ≤ x then 1 else 0) ≤ g j) :
    x - 2 * δ ≤ δ * ∑ j ∈ Finset.range M, g j := by
  set n := ⌊x / δ⌋₊
  have hlt : x / δ < n + 1 := Nat.lt_floor_add_one _
  have hxn : x < (n + 1) * δ := by rwa [div_lt_iff₀ hδ] at hlt
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : x - 2 * δ ≤ 0 := by rw [hn] at hxn; push_cast at hxn; linarith
    exact this.trans (mul_nonneg hδ.le (Finset.sum_nonneg fun j _ => hg0 j))
  have hnM : n - 1 ≤ M := by
    have h1 : (n : ℝ) ≤ x / δ := Nat.floor_le (div_nonneg hx hδ.le)
    have h2 : x / δ ≤ M := by rw [div_le_iff₀ hδ]; linarith
    have : (n : ℝ) ≤ M := h1.trans h2
    have : n ≤ M := by exact_mod_cast this
    omega
  have hsub : ∑ j ∈ Finset.range (n - 1), g j ≤ ∑ j ∈ Finset.range M, g j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnM) fun j _ _ => hg0 j
  have hone : ∑ j ∈ Finset.range (n - 1), (1 : ℝ) ≤ ∑ j ∈ Finset.range (n - 1), g j :=
    Finset.sum_le_sum fun j hj => by
      have hj' : j + 2 ≤ n := by have := Finset.mem_range.1 hj; omega
      have : ((j : ℝ) + 2) * δ ≤ x := by
        have h1 : (n : ℝ) * δ ≤ x := by
          have := Nat.floor_le (div_nonneg hx hδ.le)
          rw [le_div_iff₀ hδ] at this; exact this
        have h2 : ((j : ℝ) + 2) ≤ n := by exact_mod_cast hj'
        nlinarith
      simpa [this] using hg j
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_sub (by omega)] at hone
  push_cast at hone
  have := mul_le_mul_of_nonneg_left (hone.trans hsub) hδ.le
  nlinarith

/-- **`T^δ_k` is `2δ`-close to `t_k` on trace measures.** -/
theorem abs_TK_sub_le (hδ : 0 < δ) {M : ℕ} (hM : 1 ≤ (M : ℝ) * δ)
    (hν : (ν : Measure unitInterval) = seqTraceMeasure t) (ht : IsTransmissionSequence t)
    (k : ℕ) : |TK δ M k ν - t k| ≤ 2 * δ := by
  have hup := sum_upper hδ (ht.2.1 k).1 M (fun j => phiK δ k j ν) (phiK_le hδ hν ht k)
  have hlo := sum_lower hδ (ht.2.1 k).1 (ht.2.1 k).2 hM (fun j => phiK δ k j ν)
    (fun j => phiK_nonneg δ k j ν) (le_phiK hδ hν ht k)
  rw [abs_le]
  unfold TK
  constructor <;> linarith

theorem TK_mem (hδ : 0 < δ) {M : ℕ} (hν : (ν : Measure unitInterval) = seqTraceMeasure t)
    (ht : IsTransmissionSequence t) (k : ℕ) : 0 ≤ TK δ M k ν ∧ TK δ M k ν ≤ 1 :=
  ⟨mul_nonneg hδ.le (Finset.sum_nonneg fun j _ => phiK_nonneg δ k j ν),
    (sum_upper hδ (ht.2.1 k).1 M (fun j => phiK δ k j ν) (phiK_le hδ hν ht k)).trans
      (ht.2.1 k).2⟩

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
