module

public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Layers.GinibreTails
public import BlockBand.Coarea.GUELaw
public import BlockBand.Coarea.ProjectiveHaar

/-!
# The uniform clock-tags corollary, common-port part, from the two-positive-clocks lemma

`ClocksCommonPort.UniformClockTagsCommonPortContract` follows from the `ratio` field of
`ClocksCommonPort.TwoPositiveClocksCommonPortContract`, with no other input. With
`a_j = q Tr D_j / Tr D`, `q⁻¹ Σ_j a_j = 1`, so at most a fraction `1/K` of the tags has `a_j > K`;
each costs at most `2‖Φ‖`; on the others the lemma applies with `C = qD_j`, `Tr C ≤ K Tr D`,
uniformly (same `δ₀, W₀`), with `K = 4‖Φ‖/ε + 1`. This is the counting of the Palm part, with
traces in place of `Tr(Γ·)`. The remarks of the paper on physical weighting and on finitely many
independent tags (union bound) are not part of this file.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexOrder Matrix BoundedContinuousFunction

instance isProbabilityMeasure_commonPortProbeLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (commonPortProbeLaw W b) := by
  unfold commonPortProbeLaw BlockBand.Internal.Contracts.Layers.layerLaw; infer_instance

/-- `|∫ φ dμ| ≤ B` for a probability measure and `|φ| ≤ B`. -/
theorem abs_integral_le_of_abs_le_prob {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (φ : α → ℝ) (B : ℝ) (hB : ∀ x, |φ x| ≤ B) :
    |∫ x, φ x ∂μ| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := φ) (C := B)
    (Filter.Eventually.of_forall fun v => by simpa using hB v)
  simpa [probReal_univ] using h

/-- `0 ≤ Re Tr D` for `D ⪰ 0`. -/
theorem re_trace_nonneg_of_posSemidef {ι : Type*} [Fintype ι] {D : Matrix ι ι ℂ}
    (hD : D.PosSemidef) : 0 ≤ D.trace.re :=
  (Complex.nonneg_iff.mp hD.trace_nonneg).1

/-- **Uniform clock tags, common-port part**, from the two-positive-clocks lemma
`TwoPositiveClocksCommonPortContract` only. -/
theorem uniformClockTagsCommonPort_of_twoPositiveClocks
    (h : TwoPositiveClocksCommonPortContract) : UniformClockTagsCommonPortContract := by
  intro b hb hb' κ hκ Φ ε hε
  set B := ‖Φ‖
  have hB0 : 0 ≤ B := norm_nonneg _
  set K : ℝ := 4 * B / ε + 1 with hKdef
  have hK : 0 < K := by positivity
  obtain ⟨δ₀, W₀, hδ₀, hW₀⟩ := h.ratio b hb hb' κ hκ K Φ (ε / 2) (by positivity)
  refine ⟨δ₀, W₀, hδ₀, fun W hW hWW X hX e he hδ q hq Dt hDt hT d hd => ?_⟩
  classical
  set D := ∑ j, Dt j with hDdef
  set T := D.trace.re
  have hD : D.PosSemidef := by
    rw [hDdef]
    exact Finset.sum_induction _ (fun Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => Z.PosSemidef)
      (fun _ _ h₁ h₂ => h₁.add h₂) PosSemidef.zero fun j _ => hDt j
  set P : Fin q → ℝ := fun j =>
    ∫ x, Φ (ratioHalfLine ((q : ℂ) • Dt j) D d (commonPortProbe b e X x)) ∂commonPortProbeLaw W b
  set G : Fin q → ℝ := fun j =>
    ∫ x, Φ (ratioHalfLine ((q : ℂ) • Dt j) D d x) ∂circularVectorLaw (Fin 2 × Fin W)
  have hΦB : ∀ x, |Φ x| ≤ B := fun x => by
    simpa [Real.norm_eq_abs] using Φ.norm_coe_le_norm x
  have hP : ∀ j, |P j| ≤ B := fun j =>
    abs_integral_le_of_abs_le_prob _ _ B fun _ => hΦB _
  have hG : ∀ j, |G j| ≤ B := fun j =>
    abs_integral_le_of_abs_le_prob _ _ B fun _ => hΦB _
  set a : Fin q → ℝ := fun j => (q : ℝ) * (Dt j).trace.re
  have ha : ∀ j, 0 ≤ a j := fun j => mul_nonneg (Nat.cast_nonneg _)
    (re_trace_nonneg_of_posSemidef (hDt j))
  have hasum : ∑ j, a j ≤ q * T := by
    simp only [a, T, hDdef, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum, le_refl]
  have hgood : ∀ j, ¬ (K * T < a j) → |P j - G j| ≤ ε / 2 := by
    intro j hj
    have hC : ((q : ℂ) • Dt j).PosSemidef :=
      (hDt j).smul (by exact_mod_cast (Nat.cast_nonneg q))
    have hCT : ((q : ℂ) • Dt j).trace.re ≤ K * T := by
      have : ((q : ℂ) • Dt j).trace.re = a j := by
        simp [a, Matrix.trace_smul]
      rw [this]; exact not_lt.mp hj
    exact hW₀ W hW hWW X hX e he hδ D ((q : ℂ) • Dt j) hD hC hT hCT d hd
  have hbad : ∀ j, |P j - G j| ≤ 2 * B := fun j =>
    (abs_sub _ _).trans (by linarith [hP j, hG j])
  have hsplit : ∑ j, |P j - G j| ≤ q * (ε / 2) +
      ((Finset.univ.filter fun j => K * T < a j).card : ℝ) * (2 * B) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => K * T < a j)]
    have hb1 : ∑ j ∈ Finset.univ.filter (fun j => K * T < a j), |P j - G j| ≤
        ((Finset.univ.filter fun j => K * T < a j).card : ℝ) * (2 * B) := by
      have := Finset.sum_le_card_nsmul (Finset.univ.filter fun j => K * T < a j)
        (fun j => |P j - G j|) (2 * B) fun j _ => hbad j
      simpa [nsmul_eq_mul] using this
    have hg1 : ∑ j ∈ Finset.univ.filter (fun j => ¬ K * T < a j), |P j - G j| ≤
        q * (ε / 2) := by
      have := Finset.sum_le_card_nsmul (Finset.univ.filter fun j => ¬ K * T < a j)
        (fun j => |P j - G j|) (ε / 2) fun j hj => hgood j (Finset.mem_filter.mp hj).2
      have hcard : ((Finset.univ.filter fun j => ¬ K * T < a j).card : ℝ) ≤ q := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      simp only [nsmul_eq_mul] at this
      nlinarith
    linarith
  have hcount : ((Finset.univ.filter fun j => K * T < a j).card : ℝ) ≤ q / K := by
    set S := Finset.univ.filter fun j => K * T < a j
    have h1 : (S.card : ℝ) * (K * T) ≤ ∑ j ∈ S, a j := by
      have := Finset.card_nsmul_le_sum S a (K * T) fun j hj => (Finset.mem_filter.mp hj).2.le
      simpa [nsmul_eq_mul] using this
    have h2 : ∑ j ∈ S, a j ≤ ∑ j, a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => ha j
    rw [le_div_iff₀ hK]
    have : (S.card : ℝ) * K * T ≤ q * T := by nlinarith
    exact le_of_mul_le_mul_right (by linarith) hT
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiff : (q : ℝ)⁻¹ * ∑ j, P j - (q : ℝ)⁻¹ * ∑ j, G j =
      (q : ℝ)⁻¹ * ∑ j, (P j - G j) := by
    rw [← mul_sub, Finset.sum_sub_distrib]
  show |(q : ℝ)⁻¹ * ∑ j, P j - (q : ℝ)⁻¹ * ∑ j, G j| ≤ ε
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hqpos)]
  have h3 : |∑ j, (P j - G j)| ≤ ∑ j, |P j - G j| := Finset.abs_sum_le_sum_abs _ _
  have h4 : ((Finset.univ.filter fun j => K * T < a j).card : ℝ) * (2 * B) ≤
      (q / K) * (2 * B) := mul_le_mul_of_nonneg_right hcount (by positivity)
  have hKε : 4 * B ≤ ε * K := by
    rw [hKdef, mul_add, mul_div_assoc', mul_comm ε (4 * B), mul_div_assoc, div_self hε.ne',
      mul_one, mul_one]
    linarith
  have h5 : (q / K) * (2 * B) ≤ q * (ε / 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith
  rw [inv_mul_le_iff₀ hqpos]
  linarith

end BlockBand.Endpoints.Clock
