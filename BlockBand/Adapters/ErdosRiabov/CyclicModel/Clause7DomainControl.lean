module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause6DomainControl
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause7ZeroMode
public import Mathlib

/-!
# ER clause (vii) on an arbitrary fixed spectral domain

The Fourier zero-mode argument is independent of the spectral cutoff.  This
module exposes that fact with the same domain-dependent decay selected for
clause (vi) and a single comparison constant large enough for both clauses.
It does not assert a full admissibility package.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause7DomainControl

open ERClause7 ERClause6DomainControl ERDeterministicMDECore

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- A common comparison constant for the already proved arbitrary-domain
clauses (vi) and (vii). -/
def clause67DomainConstant (p : Params) (κ C₀ : ℝ) : ℝ :=
  max (clause6DomainConstant p κ C₀) (clause7ComparisonConstant p.b)

theorem clause67DomainConstant_nonneg (p : Params) (κ C₀ : ℝ) :
    0 ≤ clause67DomainConstant p κ C₀ := by
  unfold clause67DomainConstant
  apply (show 0 ≤ clause7ComparisonConstant p.b by
    unfold clause7ComparisonConstant
    have h₁ : 0 < 2 * p.b := mul_pos (by norm_num) p.b_pos
    have h₂ : 0 < 2 - 4 * p.b := by nlinarith [p.b_lt_half]
    exact (add_pos (one_div_pos.mpr h₁) (div_pos (by norm_num) h₂)).le).trans
  exact le_max_right _ _

/-- ER Definition 2.4(vii) for every fixed spectral cutoff.  The constant is
uniform in the dimensions, spectral points and sites. -/
theorem erTheta_zeroModeSubtracted_le_domain
    (p : Params) {κ ηExp C₀ : ℝ} {z₁ z₂ : ℂ}
    (h₁ : ERSpectralDomain p κ ηExp C₀ z₁)
    (h₂ : ERSpectralDomain p κ ηExp C₀ z₂)
    (_hsame : ERSameHalfPlane z₁ z₂) (a b : Site p.n p.W) :
    ‖erTheta p z₁ z₂ a b -
        (1 / (p.L : ℂ)) * ∑ c, erTheta p z₁ z₂ a c‖ ≤
      clause67DomainConstant p κ C₀ * (p.L : ℝ) / (p.W : ℝ) ^ 2 := by
  have hz₁ : z₁.im ≠ 0 := spectralDomain_im_ne_zero h₁
  have hz₂ : z₂.im ≠ 0 := spectralDomain_im_ne_zero h₂
  have hLnat : p.L ≠ 0 := Nat.ne_of_gt p.L_pos
  have hL : (p.L : ℂ) ≠ 0 := by exact_mod_cast hLnat
  have hLreal : (p.L : ℝ) ≠ 0 := by exact_mod_cast hLnat
  have hrewrite :
      erTheta p z₁ z₂ a b -
          (1 / (p.L : ℂ)) * ∑ c, erTheta p z₁ z₂ a c =
        (1 / (p.L : ℂ)) *
          ∑ c, (erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      p.card_site, nsmul_eq_mul]
    field_simp
  rw [hrewrite, norm_mul]
  have hnormL : ‖(1 / (p.L : ℂ))‖ = 1 / (p.L : ℝ) := by
    rw [norm_div]
    simp
  rw [hnormL]
  calc
    (1 / (p.L : ℝ)) *
        ‖∑ c, (erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c)‖ ≤
      (1 / (p.L : ℝ)) *
        ∑ c, ‖erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ (1 / (p.L : ℝ)) *
        ∑ _c : Site p.n p.W,
          (clause7ComparisonConstant p.b * p.ratio) := by
      gcongr with c
      exact norm_erTheta_sub_erTheta_le_fixedBond p hz₁ hz₂ a b c
    _ = clause7ComparisonConstant p.b * p.ratio := by
      simp only [Finset.sum_const, Finset.card_univ, p.card_site, nsmul_eq_mul]
      field_simp [hLreal]
    _ = clause7ComparisonConstant p.b * (p.L : ℝ) / (p.W : ℝ) ^ 2 := by
      rw [p.ratio_eq_dimension_div_sq]
      ring
    _ ≤ clause67DomainConstant p κ C₀ * (p.L : ℝ) / (p.W : ℝ) ^ 2 := by
      gcongr
      exact le_max_right _ _

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause7DomainControl
