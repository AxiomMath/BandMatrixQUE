module

public import BlockBand.Critical.RelativeVectors.PhaseInv

/-!
# The phase-averaged cross sum with a localized window

For `Θ` with zero diagonal, vectors `a, b ∈ ℂ^N`, a window `J` with `|a_i|², |b_i|² ≤ B` on `J`,
and `|a_i|, |b_i| ≤ Z` everywhere, `phase_cross_window_le`:
`∫ |Σ_{ij} Θ_ij (θ_ia_i)(θ_jb_j)| dθ ≤ B (Σ_{ij} |Θ_ij|² + |Θ_ijΘ_ji|)^{1/2}
  + Z² Σ_{(i,j) ∉ J×J} |Θ_ij|`
(the window part by `phase_pairing_frame_le` and Cauchy–Schwarz in `θ`, the exterior part
pointwise for unit phases).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Finset

variable {N : ℕ}

/-- `S(θ) = Σ_{ij} Θ_ij (θ_ia_i)(θ_jb_j)`. -/
def phaseSum (Θ : Fin N → Fin N → ℂ) (a b θ : Fin N → ℂ) : ℂ :=
  ∑ i, ∑ j, Θ i j * ((θ i * a i) * (θ j * b j))

theorem continuous_phaseSum (Θ : Fin N → Fin N → ℂ) (a b : Fin N → ℂ) :
    Continuous (phaseSum Θ a b) := by
  unfold phaseSum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (((continuous_apply i).mul continuous_const).mul
    ((continuous_apply j).mul continuous_const))

theorem norm_phaseSum_le (Θ : Fin N → Fin N → ℂ) (a b θ : Fin N → ℂ) (hθ : ∀ i, ‖θ i‖ = 1)
    {Z : ℝ} (ha : ∀ i, ‖a i‖ ≤ Z) (hb : ∀ i, ‖b i‖ ≤ Z) :
    ‖phaseSum Θ a b θ‖ ≤ ∑ i, ∑ j, ‖Θ i j‖ * (Z * Z) := by
  unfold phaseSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hθ i, hθ j, one_mul, one_mul]
  have hZ : 0 ≤ Z := (norm_nonneg _).trans (ha i)
  exact mul_le_mul_of_nonneg_left (mul_le_mul (ha i) (hb j) (norm_nonneg _) hZ) (norm_nonneg _)

theorem integrable_phaseSum_norm (Θ : Fin N → Fin N → ℂ) (a b : Fin N → ℂ) {Z : ℝ}
    (ha : ∀ i, ‖a i‖ ≤ Z) (hb : ∀ i, ‖b i‖ ≤ Z) (p : ℕ) :
    Integrable (fun θ => ‖phaseSum Θ a b θ‖ ^ p) (phaseVectorLaw N) := by
  refine Integrable.of_bound (μ := phaseVectorLaw N)
    ((continuous_phaseSum Θ a b).norm.pow p).aestronglyMeasurable
    ((∑ i, ∑ j, ‖Θ i j‖ * (Z * Z)) ^ p) (ae_norm_phase_eq_one.mono fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_phaseSum_le Θ a b θ hθ ha hb) p

/-- `(∫ |S|)² ≤ ∫ |S|²` on the phase law. -/
theorem integral_norm_sq_le (Θ : Fin N → Fin N → ℂ) (a b : Fin N → ℂ) {Z : ℝ}
    (ha : ∀ i, ‖a i‖ ≤ Z) (hb : ∀ i, ‖b i‖ ≤ Z) :
    (∫ θ, ‖phaseSum Θ a b θ‖ ∂phaseVectorLaw N) ^ 2 ≤
      ∫ θ, ‖phaseSum Θ a b θ‖ ^ 2 ∂phaseVectorLaw N := by
  set m := ∫ θ, ‖phaseSum Θ a b θ‖ ∂phaseVectorLaw N
  have h1 := integrable_phaseSum_norm Θ a b ha hb 1
  have h2 := integrable_phaseSum_norm Θ a b ha hb 2
  simp only [pow_one] at h1
  have h0 : 0 ≤ ∫ θ, (‖phaseSum Θ a b θ‖ - m) ^ 2 ∂phaseVectorLaw N :=
    integral_nonneg fun _ => sq_nonneg _
  have e : ∫ θ, (‖phaseSum Θ a b θ‖ - m) ^ 2 ∂phaseVectorLaw N =
      ∫ θ, ‖phaseSum Θ a b θ‖ ^ 2 ∂phaseVectorLaw N - m ^ 2 := by
    have : (fun θ => (‖phaseSum Θ a b θ‖ - m) ^ 2) =
        fun θ => ‖phaseSum Θ a b θ‖ ^ 2 - (2 * m) * ‖phaseSum Θ a b θ‖ + m ^ 2 := by
      funext θ; ring
    have hA : Integrable (fun θ => ‖phaseSum Θ a b θ‖ ^ 2 - 2 * m * ‖phaseSum Θ a b θ‖)
        (phaseVectorLaw N) := h2.sub (h1.const_mul _)
    rw [this, integral_add hA (integrable_const _),
      integral_sub h2 (h1.const_mul _), integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  linarith

/-- **The phase-averaged cross sum with a window.** See the module docstring. -/
theorem phase_cross_window_le (Θ : Fin N → Fin N → ℂ) (hΘ : ∀ i, Θ i i = 0) (a b : Fin N → ℂ)
    (J : Finset (Fin N)) {B Z : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z) (haJ : ∀ i ∈ J, ‖a i‖ ^ 2 ≤ B)
    (hbJ : ∀ i ∈ J, ‖b i‖ ^ 2 ≤ B) (ha : ∀ i, ‖a i‖ ≤ Z) (hb : ∀ i, ‖b i‖ ≤ Z) :
    ∫ θ, ‖phaseSum Θ a b θ‖ ∂phaseVectorLaw N ≤
      B * Real.sqrt (∑ i, ∑ j, (‖Θ i j‖ ^ 2 + ‖Θ i j * Θ j i‖)) +
        Z * Z * ∑ i, ∑ j, (if i ∈ J ∧ j ∈ J then 0 else ‖Θ i j‖) := by
  classical
  -- the window part
  set aJ : Fin N → ℂ := fun i => if i ∈ J then a i else 0
  set bJ : Fin N → ℂ := fun i => if i ∈ J then b i else 0
  set ΘJ : Fin N → Fin N → ℂ := fun i j => if i ∈ J ∧ j ∈ J then 0 else Θ i j
  have hsplit : ∀ θ, phaseSum Θ a b θ = phaseSum Θ aJ bJ θ + phaseSum ΘJ a b θ := by
    intro θ
    unfold phaseSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [aJ, bJ, ΘJ]
    by_cases hi : i ∈ J <;> by_cases hj : j ∈ J <;> simp [hi, hj]
  have haJ' : ∀ i, ‖aJ i‖ ≤ Z := fun i => by
    simp only [aJ]; split_ifs
    · exact ha i
    · simpa using hZ
  have hbJ' : ∀ i, ‖bJ i‖ ≤ Z := fun i => by
    simp only [bJ]; split_ifs
    · exact hb i
    · simpa using hZ
  have i1 := integrable_phaseSum_norm Θ aJ bJ haJ' hbJ' 1
  have i2 := integrable_phaseSum_norm ΘJ a b ha hb 1
  simp only [pow_one] at i1 i2
  have hmain : ∫ θ, ‖phaseSum Θ a b θ‖ ∂phaseVectorLaw N ≤
      ∫ θ, ‖phaseSum Θ aJ bJ θ‖ ∂phaseVectorLaw N + ∫ θ, ‖phaseSum ΘJ a b θ‖ ∂phaseVectorLaw N := by
    rw [← integral_add i1 i2]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (i1.add i2) (Filter.Eventually.of_forall fun θ => ?_)
    show ‖phaseSum Θ a b θ‖ ≤ ‖phaseSum Θ aJ bJ θ‖ + ‖phaseSum ΘJ a b θ‖
    rw [hsplit θ]
    exact norm_add_le _ _
  -- window part
  have hw : ∫ θ, ‖phaseSum Θ aJ bJ θ‖ ∂phaseVectorLaw N ≤
      B * Real.sqrt (∑ i, ∑ j, (‖Θ i j‖ ^ 2 + ‖Θ i j * Θ j i‖)) := by
    have hpp := phase_pairing_frame_le Θ hΘ aJ bJ (B := B)
      (fun i => by simp only [aJ]; split_ifs with h
                   · exact haJ i h
                   · simpa using hB)
      (fun i => by simp only [bJ]; split_ifs with h
                   · exact hbJ i h
                   · simpa using hB)
    have hsq := integral_norm_sq_le Θ aJ bJ haJ' hbJ'
    have hnn : 0 ≤ ∫ θ, ‖phaseSum Θ aJ bJ θ‖ ∂phaseVectorLaw N :=
      integral_nonneg fun _ => norm_nonneg _
    have hS0 : 0 ≤ ∑ i, ∑ j, (‖Θ i j‖ ^ 2 + ‖Θ i j * Θ j i‖) := by positivity
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (sq_nonneg B)]
    refine Real.le_sqrt_of_sq_le ?_
    exact hsq.trans hpp
  -- exterior part
  have he : ∫ θ, ‖phaseSum ΘJ a b θ‖ ∂phaseVectorLaw N ≤
      Z * Z * ∑ i, ∑ j, (if i ∈ J ∧ j ∈ J then 0 else ‖Θ i j‖) := by
    have hb' : ∀ᵐ θ ∂phaseVectorLaw N, ‖phaseSum ΘJ a b θ‖ ≤ ∑ i, ∑ j, ‖ΘJ i j‖ * (Z * Z) :=
      ae_norm_phase_eq_one.mono fun θ hθ => norm_phaseSum_le ΘJ a b θ hθ ha hb
    refine (integral_mono_ae i2 (integrable_const _) hb').trans (le_of_eq ?_)
    rw [integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [ΘJ]
    split_ifs
    · simp
    · ring
  linarith

end BlockBand.Critical.RelativeVectors
