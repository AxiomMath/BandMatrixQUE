module

public import BlockBand.Endpoints.Normalization.LeadProfileCylinder

/-!
# The physical lead-profile theorem: deleting one block mass

We bound the change of a profile functional when one block mass is deleted and the rest
renormalized. The statements are deterministic.
* `sum_abs_deleted_sub`: for masses `m_i ≥ 0` on a finite set with total `S` and a coordinate
  `k₀` with `a = m_{k₀} < S`, the renormalized deleted vector `m'_i = 1{i≠k₀} m_i/(S - a)`
  satisfies `Σ_i |m'_i - m_i/S| = 2a/S` (exact total-variation identity).
* `abs_deleted_test_sub_le`: hence `|Σ_i m'_i φ_i - Σ_i (m_i/S) φ_i| ≤ 2a/S` for `|φ| ≤ 1`.
* `exists_profile_modulus`: for every `Φ ∈ C_b(𝒫(𝕋))` and `ε > 0` there is `C ≥ 0` with
  `|Φ(ν') - Φ(ν)| ≤ ε + C t` whenever `|∫φ dν' - ∫φ dν| ≤ t` for all continuous `|φ| ≤ 1`
  (from the cylinder approximation `exists_cylinder_approx` and uniform continuity on the cube).
* `abs_profile_deleted_sub_le`: the combination for finite Dirac profiles
  `ν = Σ_i (m_i/S) δ_{x_i}`, `ν' = Σ_i m'_i δ_{x_i}`: `|Φ(ν') - Φ(ν)| ≤ ε + 2C a/S`.

Use in the assembly: with `a/S = p_{α0}` (the block-0 mass fraction), the error is
`ε + 2C p_{α0}`; weighted by the block-0 Palm weight `n p_{α0} |w(u_α)|` it is controlled by
`ε E Σ_α |w(u_α)| + 2Cn E Σ_α |w(u_α)| p_{α0}²`, the second term being the vanishing block-atom bound
after cyclic averaging.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory
open BlockBand.Model.Construction
open scoped BoundedContinuousFunction

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The renormalized vector with coordinate `k₀` deleted. -/
def deletedMass (m : ι → ℝ) (k₀ : ι) (i : ι) : ℝ :=
  (if i = k₀ then 0 else m i) / (∑ j, m j - m k₀)

/-- **Exact deletion identity**: `Σ_i |m'_i - m_i/S| = 2 m_{k₀}/S`. -/
theorem sum_abs_deleted_sub (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (k₀ : ι)
    (hS : m k₀ < ∑ j, m j) :
    ∑ i, |deletedMass m k₀ i - m i / ∑ j, m j| = 2 * (m k₀ / ∑ j, m j) := by
  set S := ∑ j, m j with hSdef
  set a := m k₀
  have ha : 0 ≤ a := hm k₀
  have hSpos : 0 < S := lt_of_le_of_lt ha hS
  have hS'pos : 0 < S - a := sub_pos.mpr hS
  have hsplit := (Finset.add_sum_erase Finset.univ
    (fun i => |deletedMass m k₀ i - m i / S|) (Finset.mem_univ k₀)).symm
  rw [hsplit]
  have hk₀ : |deletedMass m k₀ k₀ - m k₀ / S| = a / S := by
    simp only [deletedMass, ↓reduceIte, zero_div, zero_sub, abs_neg]
    exact abs_of_nonneg (div_nonneg ha hSpos.le)
  have hrest : ∀ i ∈ Finset.univ.erase k₀,
      |deletedMass m k₀ i - m i / S| = m i * (a / (S * (S - a))) := by
    intro i hi
    have hik : i ≠ k₀ := Finset.ne_of_mem_erase hi
    simp only [deletedMass, hik, ↓reduceIte]
    have : m i / (S - a) - m i / S = m i * (a / (S * (S - a))) := by
      field_simp
      ring
    rw [this]
    exact abs_of_nonneg (mul_nonneg (hm i) (div_nonneg ha (mul_pos hSpos hS'pos).le))
  rw [hk₀, Finset.sum_congr rfl hrest, ← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.univ.erase k₀, m i = S - a := by
    rw [← Finset.add_sum_erase Finset.univ m (Finset.mem_univ k₀)] at hSdef
    linarith
  rw [hsum]
  field_simp
  ring

/-- Deleting a block changes a test integral `Σ_i q_i φ_i` (`|φ| ≤ 1`) by at most `2a/S`. -/
theorem abs_deleted_test_sub_le (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (k₀ : ι)
    (hS : m k₀ < ∑ j, m j) (φ : ι → ℝ) (hφ : ∀ i, |φ i| ≤ 1) :
    |∑ i, deletedMass m k₀ i * φ i - ∑ i, m i / (∑ j, m j) * φ i| ≤
      2 * (m k₀ / ∑ j, m j) := by
  rw [← Finset.sum_sub_distrib, ← sum_abs_deleted_sub m hm k₀ hS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hφ i)

end Finite

/-- **Modulus of a profile functional** in the dual norm of tests bounded by one: for every
`Φ ∈ C_b(𝒫(𝕋))` and `ε > 0` there is `C ≥ 0` with `|Φ(ν') - Φ(ν)| ≤ ε + Ct` whenever every
continuous `|φ| ≤ 1` has `|∫φ dν' - ∫φ dν| ≤ t`. -/
theorem exists_profile_modulus (Φ : MassProfile →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ν' : MassProfile) (t : ℝ),
      (∀ φ : C(Torus, ℝ), (∀ x, |φ x| ≤ 1) →
        |(∫ r, φ r ∂(ν' : Measure Torus)) - ∫ r, φ r ∂(ν : Measure Torus)| ≤ t) →
      |Φ ν' - Φ ν| ≤ ε + C * t := by
  obtain ⟨m, φ, ψ, hφ, happrox⟩ := exists_cylinder_approx Φ (ε / 3) (by positivity)
  have huc : UniformContinuous ψ := CompactSpace.uniformContinuous_of_continuous ψ.continuous
  obtain ⟨δ, hδ, hδψ⟩ := Metric.uniformContinuous_iff.mp huc (ε / 3) (by positivity)
  refine ⟨2 * ‖ψ‖ / δ, by positivity, fun ν ν' t ht => ?_⟩
  have hdist : dist (cylinderVec φ ν') (cylinderVec φ ν) ≤ t := by
    have ht0 : 0 ≤ t := (abs_nonneg _).trans (ht 0 (fun _ => by simp))
    refine (dist_pi_le_iff ht0).mpr fun i => ?_
    rw [Subtype.dist_eq, cylinderVec_coe φ hφ, cylinderVec_coe φ hφ, Real.dist_eq]
    exact ht (φ i) (hφ i)
  have hψ : |ψ (cylinderVec φ ν') - ψ (cylinderVec φ ν)| ≤ ε / 3 + 2 * ‖ψ‖ / δ * t := by
    by_cases hsmall : t < δ
    · have := hδψ (lt_of_le_of_lt hdist hsmall)
      rw [Real.dist_eq] at this
      have : 0 ≤ 2 * ‖ψ‖ / δ * t :=
        mul_nonneg (by positivity) ((abs_nonneg _).trans (ht 0 (fun _ => by simp)))
      linarith
    · push Not at hsmall
      have h1 : |ψ (cylinderVec φ ν') - ψ (cylinderVec φ ν)| ≤ 2 * ‖ψ‖ := by
        refine (abs_sub _ _).trans ?_
        have := ψ.norm_coe_le_norm (cylinderVec φ ν')
        have := ψ.norm_coe_le_norm (cylinderVec φ ν)
        simp only [Real.norm_eq_abs] at *
        linarith
      have h2 : 2 * ‖ψ‖ ≤ 2 * ‖ψ‖ / δ * t := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      linarith
  have e1 := happrox ν
  have e2 := happrox ν'
  have : Φ ν' - Φ ν = (Φ ν' - ψ (cylinderVec φ ν')) +
      (ψ (cylinderVec φ ν') - ψ (cylinderVec φ ν)) - (Φ ν - ψ (cylinderVec φ ν)) := by ring
  rw [this]
  have := abs_sub (Φ ν' - ψ (cylinderVec φ ν') + (ψ (cylinderVec φ ν') - ψ (cylinderVec φ ν)))
    (Φ ν - ψ (cylinderVec φ ν))
  have := abs_add_le (Φ ν' - ψ (cylinderVec φ ν')) (ψ (cylinderVec φ ν') - ψ (cylinderVec φ ν))
  linarith

/-- **Deletion of one block mass for a finite Dirac profile**: with
`ν = Σ_i (m_i/S) δ_{x_i}` and `ν' = Σ_i m'_i δ_{x_i}` (as measures), every `Φ ∈ C_b(𝒫(𝕋))`
and `ε > 0` admit `C ≥ 0` (depending on `Φ, ε` only) with
`|Φ(ν') - Φ(ν)| ≤ ε + 2C · m_{k₀}/S`. -/
theorem abs_profile_deleted_sub_le (Φ : MassProfile →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℝ), (∀ i, 0 ≤ m i) →
      ∀ (k₀ : ι), m k₀ < ∑ j, m j → ∀ (pts : ι → Torus) (ν ν' : MassProfile),
      (ν : Measure Torus) = ∑ i, ENNReal.ofReal (m i / ∑ j, m j) • Measure.dirac (pts i) →
      (ν' : Measure Torus) = ∑ i, ENNReal.ofReal (deletedMass m k₀ i) • Measure.dirac (pts i) →
      |Φ ν' - Φ ν| ≤ ε + C * (2 * (m k₀ / ∑ j, m j)) := by
  obtain ⟨C, hC, hmod⟩ := exists_profile_modulus Φ ε hε
  refine ⟨C, hC, fun {ι} _ _ m hm k₀ hS pts ν ν' hν hν' => hmod ν ν' _ fun φ hφ => ?_⟩
  have hSpos : 0 < ∑ j, m j := lt_of_le_of_lt (hm k₀) hS
  have hS'pos : 0 < ∑ j, m j - m k₀ := sub_pos.mpr hS
  have hint : ∀ (q : ι → ℝ), (∀ i, 0 ≤ q i) →
      ∫ r, φ r ∂(∑ i, ENNReal.ofReal (q i) • Measure.dirac (pts i)) = ∑ i, q i * φ (pts i) := by
    intro q hq
    rw [integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq i), smul_eq_mul]
  have hdel : ∀ i, 0 ≤ deletedMass m k₀ i := fun i => by
    unfold deletedMass
    split_ifs
    · simp
    · exact div_nonneg (hm i) hS'pos.le
  rw [hν, hν', hint _ hdel, hint _ (fun i => div_nonneg (hm i) hSpos.le)]
  exact abs_deleted_test_sub_le m hm k₀ hS (fun i => φ (pts i)) (fun i => hφ _)

end BlockBand.Endpoints.Normalization
