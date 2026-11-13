module

public import BlockBand.Transmission.Generator.ModFour
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Modulus of continuity, abstract part III: blocks and the union bound

Setting of `ModDoob`, `μ` a probability measure. Blocks `[a + iL, a + iL + 2L)`, `i < nb`, cover
every pair `a ≤ r ≤ r' ≤ r + L`, `r < a + nb L`. The drift `d_u = E[Δ_u ∣ ℱ_u]` is split as
`|d_u| ≤ G_u + |e_u|` a.s.: `G` (`L²`, per block, Chebyshev) and `e` (`L¹`, summed over the
whole window, Markov).

* `modX_eq`: `X_{a+j} - X_a = N^a_j + Σ_{u<j} d_{a+u}` (everywhere);
* **`meas_modBad_le`**: `P(∃ r ≤ r' ≤ r + L, a ≤ r < a + nb L, η < |X_{r'} - X_r|) ≤
  nb·(320(2L)²M₄/(η/6)⁴ + (2L)²M_G/(η/3)²) + Σ_{u<(nb+1)L} ‖e_{a+u}‖₁/(η/3)`, given
  `E Δ⁴_{a+u} ≤ M₄`, `E G²_{a+u} ≤ M_G` for `u < (nb+1)L`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Markov for a nonnegative integrable real function. -/
theorem meas_ge_le_ofReal [IsFiniteMeasure μ] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f)
    (hf : Integrable f μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂μ) / c) := by
  have h := mul_meas_ge_le_integral_of_nonneg hf0 hf c
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hc, mul_comm]
  exact h

/-- Markov for a finite sum of absolute values, in `‖·‖₁`. -/
theorem meas_lt_sum_abs_le {e : ℕ → Ω → ℝ} (he : ∀ u, AEStronglyMeasurable (e u) μ) (s : Finset ℕ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | c < ∑ u ∈ s, |e u ω|} ≤ (∑ u ∈ s, eLpNorm (e u) 1 μ) / ENNReal.ofReal c := by
  have hsub : {ω | c < ∑ u ∈ s, |e u ω|} ⊆
      {ω | ENNReal.ofReal c ≤ ∑ u ∈ s, ‖e u ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs] at hω ⊢
    rw [← ENNReal.ofReal_sum_of_nonneg fun u _ => abs_nonneg _]
    exact ENNReal.ofReal_le_ofReal hω.le
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div
    (Finset.aemeasurable_fun_sum s fun u _ => (he u).enorm) (by simpa using hc)
    ENNReal.ofReal_ne_top).trans ?_)
  refine ENNReal.div_le_div_right (le_of_eq ?_) _
  rw [lintegral_finsetSum' s fun u _ => (he u).enorm]
  exact Finset.sum_congr rfl fun u _ => (eLpNorm_one_eq_lintegral_enorm (he (u))).symm

/-- The bad event of the modulus at block length `L`. -/
def modBad (X : ℕ → Ω → ℝ) (a L nb : ℕ) (η : ℝ) : Set Ω :=
  {ω | ∃ r r' : ℕ, a ≤ r ∧ r ≤ r' ∧ r < a + nb * L ∧ r' ≤ r + L ∧ η < |X r' ω - X r ω|}

theorem modX_eq (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (a j : ℕ) (ω : Ω) :
    X (a + j) ω - X a ω = modSum μ ℱ X a j ω + ∑ u ∈ range j, (μ[modInc X (a + u) | ℱ (a + u)]) ω := by
  induction j with
  | zero => simp [modSum_zero]
  | succ j ih =>
    rw [modSum_succ, sum_range_succ, Pi.add_apply]
    have e : X (a + (j + 1)) ω = X (a + j) ω + modInc X (a + j) ω := by
      simp only [modInc, Pi.sub_apply, ← add_assoc]; ring
    rw [e, modMart, Pi.sub_apply]
    linarith

section Main

variable [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {X : ℕ → Ω → ℝ}
  (hX : ∀ r, StronglyMeasurable[ℱ r] (X r)) {B : ℝ} (hB : ∀ r, ∀ᵐ ω ∂μ, |X r ω| ≤ B)
include hX hB

/-- **The modulus bound.** -/
theorem meas_modBad_le (G e : ℕ → Ω → ℝ)
    (hG2 : ∀ u, Integrable (fun ω => G u ω ^ 2) μ) (he : ∀ u, AEStronglyMeasurable (e u) μ)
    (hd : ∀ u, ∀ᵐ ω ∂μ, |(μ[modInc X u | ℱ u]) ω| ≤ G u ω + |e u ω|)
    {a L nb : ℕ} (hL : 0 < L) {η M₄ MG : ℝ} (hη : 0 < η)
    (h4 : ∀ u < (nb + 1) * L, ∫ ω, modInc X (a + u) ω ^ 4 ∂μ ≤ M₄)
    (hGM : ∀ u < (nb + 1) * L, ∫ ω, G (a + u) ω ^ 2 ∂μ ≤ MG) :
    μ (modBad X a L nb η) ≤
      ENNReal.ofReal (nb * (320 * (2 * L : ℝ) ^ 2 * M₄ / (η / 6) ^ 4 +
          (2 * L : ℝ) ^ 2 * MG / (η / 3) ^ 2)) +
        (∑ u ∈ range ((nb + 1) * L), eLpNorm (e (a + u)) 1 μ) / ENNReal.ofReal (η / 3) := by
  set E1 : ℕ → Set Ω := fun i => {ω | ∃ j ≤ 2 * L, η / 6 ≤ |modSum μ ℱ X (a + i * L) j ω|}
  set T : ℕ → Ω → ℝ := fun i ω => (2 * L : ℝ) * ∑ u ∈ range (2 * L), G (a + i * L + u) ω ^ 2
  set E2 : ℕ → Set Ω := fun i => {ω | (η / 3) ^ 2 ≤ T i ω}
  set E3 : Set Ω := {ω | η / 3 < ∑ u ∈ range ((nb + 1) * L), |e (a + u) ω|}
  have hgood : ∀ᵐ ω ∂μ, ∀ u, |(μ[modInc X u | ℱ u]) ω| ≤ G u ω + |e u ω| := ae_all_iff.2 hd
  -- the inclusion
  have hsub : modBad X a L nb η ≤ᵐ[μ] ((⋃ i ∈ range nb, (E1 i ∪ E2 i)) ∪ E3 : Set Ω) := by
    filter_upwards [hgood] with ω hω hbad
    obtain ⟨r, r', har, hrr, hrn, hrL, hη'⟩ := hbad
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, mem_range, not_or, not_exists] at hcon
    obtain ⟨hc12, hc3⟩ := hcon
    set i := (r - a) / L
    have hi : i < nb := (Nat.div_lt_iff_lt_mul hL).2 (by omega)
    have hai : i * L ≤ r - a := Nat.div_mul_le_self _ _
    have hai' : r - a < i * L + L := Nat.lt_div_mul_add hL
    obtain ⟨h1, h2⟩ := hc12 i hi
    set a' := a + i * L
    set j := r - a'
    set j' := r' - a'
    have hj : j ≤ 2 * L := by omega
    have hj' : j' ≤ 2 * L := by omega
    have hr : r = a' + j := by omega
    have hr' : r' = a' + j' := by omega
    have hjj : j ≤ j' := by omega
    simp only [E1, Set.mem_ofPred_eq, not_exists, not_and, not_le] at h1
    have n1 := h1 j hj
    have n2 := h1 j' hj'
    simp only [E2, Set.mem_ofPred_eq, not_le] at h2
    simp only [E3, Set.mem_ofPred_eq, not_lt] at hc3
    set d : ℕ → ℝ := fun u => (μ[modInc X u | ℱ u]) ω
    have ediff : X r' ω - X r ω = (modSum μ ℱ X a' j' ω - modSum μ ℱ X a' j ω) +
        ∑ u ∈ Ico j j', d (a' + u) := by
      have e1 := modX_eq (μ := μ) ℱ X a' j ω
      have e2 := modX_eq (μ := μ) ℱ X a' j' ω
      rw [← Finset.sum_range_add_sum_Ico _ hjj] at e2
      rw [hr, hr']
      linarith
    -- the drift sum
    have hD1 : |∑ u ∈ Ico j j', d (a' + u)| ≤ ∑ u ∈ range (2 * L), |d (a' + u)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun _ _ _ => abs_nonneg _
      simp only [mem_Ico] at hu; simp only [mem_range]; omega
    have hD2 : ∑ u ∈ range (2 * L), |d (a' + u)| ≤ ∑ u ∈ range (2 * L), G (a' + u) ω +
        ∑ u ∈ range (2 * L), |e (a' + u) ω| := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun u _ => hω _
    have hD3 : ∑ u ∈ range (2 * L), |e (a' + u) ω| ≤
        ∑ u ∈ range ((nb + 1) * L), |e (a + u) ω| := by
      have e' : ∑ u ∈ range (2 * L), |e (a' + u) ω| =
          ∑ v ∈ Ico (i * L) (i * L + 2 * L), |e (a + v) ω| := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) fun u _ => ?_
        simp only [a', add_assoc]
      rw [e']
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun _ _ _ => abs_nonneg _
      simp only [mem_Ico] at hu; simp only [mem_range]
      have : (i + 2) * L ≤ (nb + 1) * L := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    -- the `G` sum through `T`
    have hT : ∑ u ∈ range (2 * L), G (a' + u) ω ≤ η / 3 := by
      by_contra hlt
      rw [not_le] at hlt
      have hcs := sq_sum_le_card_mul_sum_sq (s := range (2 * L)) (f := fun u => G (a' + u) ω)
      rw [card_range] at hcs
      have : (η / 3) ^ 2 < (∑ u ∈ range (2 * L), G (a' + u) ω) ^ 2 :=
        pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      have hTe : T i ω = (2 * L : ℝ) * ∑ u ∈ range (2 * L), G (a' + u) ω ^ 2 := rfl
      push_cast at hcs
      linarith
    have hfin := abs_add_le (modSum μ ℱ X a' j' ω - modSum μ ℱ X a' j ω)
      (∑ u ∈ Ico j j', d (a' + u))
    have habs := abs_sub (modSum μ ℱ X a' j' ω) (modSum μ ℱ X a' j ω)
    rw [← ediff] at hfin
    linarith
  -- the measures
  have hM4 : 0 ≤ M₄ := (integral_nonneg fun ω => by positivity).trans (h4 0 (by positivity))
  have hMG : 0 ≤ MG := (integral_nonneg fun ω => by positivity).trans (hGM 0 (by positivity))
  set c1 : ℝ := 320 * (2 * L : ℝ) ^ 2 * M₄ / (η / 6) ^ 4
  set c2 : ℝ := (2 * L : ℝ) ^ 2 * MG / (η / 3) ^ 2
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hE1 : ∀ i ∈ range nb, μ (E1 i) ≤ ENNReal.ofReal c1 := by
    intro i hi
    rw [mem_range] at hi
    refine (meas_modSum_ge_le ℱ hX hB (a + i * L) (2 * L) (by positivity : 0 < η / 6)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity)))
    have := integral_modSum_pow_four_le ℱ hX hB (a + i * L) (2 * L) (M := M₄) fun u hu => by
      rw [add_assoc]
      refine h4 (i * L + u) ?_
      have : (i + 2) * L ≤ (nb + 1) * L := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    push_cast at this
    exact this
  have hE2 : ∀ i ∈ range nb, μ (E2 i) ≤ ENNReal.ofReal c2 := by
    intro i hi
    rw [mem_range] at hi
    have iT : Integrable (T i) μ := (integrable_finsetSum _ fun u _ => hG2 _).const_mul _
    refine (meas_ge_le_ofReal (ae_of_all _ fun ω => by positivity) iT (by positivity)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity)))
    show ∫ ω, (2 * L : ℝ) * ∑ u ∈ range (2 * L), G (a + i * L + u) ω ^ 2 ∂μ ≤ _
    rw [integral_const_mul, integral_finsetSum _ fun u _ => hG2 _]
    have hs : ∑ u ∈ range (2 * L), ∫ ω, G (a + i * L + u) ω ^ 2 ∂μ ≤ (2 * L : ℕ) * MG := by
      have := Finset.sum_le_sum (s := range (2 * L)) fun u hu =>
        (show ∫ ω, G (a + i * L + u) ω ^ 2 ∂μ ≤ MG by
          rw [add_assoc]
          refine hGM (i * L + u) ?_
          rw [mem_range] at hu
          have : (i + 2) * L ≤ (nb + 1) * L := Nat.mul_le_mul_right _ (by omega)
          nlinarith)
      rwa [sum_const, card_range, nsmul_eq_mul] at this
    push_cast at hs
    have h2L : (0 : ℝ) ≤ 2 * L := by positivity
    calc (2 * L : ℝ) * ∑ u ∈ range (2 * L), ∫ ω, G (a + i * L + u) ω ^ 2 ∂μ
        ≤ (2 * L : ℝ) * (2 * L * MG) := mul_le_mul_of_nonneg_left hs h2L
      _ = _ := by ring
  calc μ (modBad X a L nb η) ≤ μ ((⋃ i ∈ range nb, (E1 i ∪ E2 i)) ∪ E3) := measure_mono_ae hsub
    _ ≤ μ (⋃ i ∈ range nb, (E1 i ∪ E2 i)) + μ E3 := measure_union_le _ _
    _ ≤ (∑ i ∈ range nb, (μ (E1 i) + μ (E2 i))) + μ E3 :=
        add_le_add_left ((measure_biUnion_finset_le _ _).trans
          (sum_le_sum fun i _ => measure_union_le _ _)) _
    _ ≤ (∑ i ∈ range nb, ENNReal.ofReal (c1 + c2)) +
          (∑ u ∈ range ((nb + 1) * L), eLpNorm (e (a + u)) 1 μ) / ENNReal.ofReal (η / 3) := by
        refine add_le_add (sum_le_sum fun i hi => ?_)
          (meas_lt_sum_abs_le (fun u => he (a + u)) _ (by positivity))
        rw [ENNReal.ofReal_add hc1 hc2]
        exact add_le_add (hE1 i hi) (hE2 i hi)
    _ = _ := by
        rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

end Main

end BlockBand.Transmission.Generator
