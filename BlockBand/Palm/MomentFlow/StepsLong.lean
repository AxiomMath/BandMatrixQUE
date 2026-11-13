module

public import BlockBand.Palm.MomentFlow.LocalSpectral

/-!
# Long couplings against `Im q*G(λ_i + ih)q` (deterministic kernel comparison)

For Hermitian `H` with simple spectrum, if `|λ_i - λ_j| ≥ h` for `j ∈ S`, then
`Σ_{j ∈ S} c_ij X_j ≤ (2/h) Im q*(H - λ_i - ih)⁻¹q`, with `c_ij = (N(λ_i - λ_j)²)⁻¹` and
`X_j = N|q* u_j|²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- **Long couplings, deterministic form.** -/
theorem long_coupling_sum_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (hN : 0 < N) {h : ℝ} (hh : 0 < h) (q : Fin N → ℂ) (i : Fin N)
    (S : Finset (Fin N)) (hS : ∀ j ∈ S, h ≤ |freshEigenvalue H i - freshEigenvalue H j|) :
    ∑ j ∈ S, ((N : ℝ) * (freshEigenvalue H i - freshEigenvalue H j) ^ 2)⁻¹ *
        ((N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2) ≤
      2 / h * (star q ⬝ᵥ ((H - (⟨freshEigenvalue H i, h⟩ : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := by
  rw [← resolvent_im_spectral hH hs hN _ hh.ne' q]
  set lam := freshEigenvalue H
  set X : Fin N → ℝ := fun j => (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : ∀ j, 0 ≤ X j := fun j => by positivity
  have hterm : ∀ j ∈ S, ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ * X j ≤
      2 / h * ((N : ℝ)⁻¹ * (h / ((lam j - lam i) ^ 2 + h ^ 2) * X j)) := by
    intro j hj
    have hd := hS j hj
    have hd2 : h ^ 2 ≤ (lam i - lam j) ^ 2 := by
      rw [← sq_abs (lam i - lam j)]; exact pow_le_pow_left₀ hh.le hd 2
    have hpos : 0 < (lam i - lam j) ^ 2 := lt_of_lt_of_le (by positivity) hd2
    have hsym : (lam j - lam i) ^ 2 = (lam i - lam j) ^ 2 := by ring
    rw [hsym]
    have key : ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ ≤
        2 / h * ((N : ℝ)⁻¹ * (h / ((lam i - lam j) ^ 2 + h ^ 2))) := by
      rw [show 2 / h * ((N : ℝ)⁻¹ * (h / ((lam i - lam j) ^ 2 + h ^ 2))) =
          2 / ((N : ℝ) * ((lam i - lam j) ^ 2 + h ^ 2)) by field_simp]
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hd2, hNp]
    calc ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ * X j
        ≤ 2 / h * ((N : ℝ)⁻¹ * (h / ((lam i - lam j) ^ 2 + h ^ 2))) * X j :=
          mul_le_mul_of_nonneg_right key (hX j)
      _ = _ := by ring
  have hnn : ∀ j, 0 ≤ (N : ℝ)⁻¹ * (h / ((lam j - lam i) ^ 2 + h ^ 2) * X j) := fun j => by
    have := hX j; positivity
  calc ∑ j ∈ S, ((N : ℝ) * (lam i - lam j) ^ 2)⁻¹ * X j
      ≤ ∑ j ∈ S, 2 / h * ((N : ℝ)⁻¹ * (h / ((lam j - lam i) ^ 2 + h ^ 2) * X j)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j, 2 / h * ((N : ℝ)⁻¹ * (h / ((lam j - lam i) ^ 2 + h ^ 2) * X j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => mul_nonneg (by positivity) (hnn j)
    _ = 2 / h * ((N : ℝ)⁻¹ * ∑ j, h / ((lam j - lam i) ^ 2 + h ^ 2) * X j) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **Long couplings with the long-gap bound.** If `|λ_i - λ_j| ≥ c|i-j|/N` whenever
`|i-j| ≥ ℓ`, then `∑_{|j-i| ≥ ℓ} c_ij X_j ≤ (2N/(cℓ)) Im q*(H - λ_i - i cℓ/N)⁻¹ q`. -/
theorem long_rank_coupling_sum_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (hN : 0 < N) {c₁ : ℝ} (hc : 0 < c₁) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |freshEigenvalue H i - freshEigenvalue H j|)
    (q : Fin N → ℂ) (i : Fin N) :
    ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
        ((N : ℝ) * (freshEigenvalue H i - freshEigenvalue H j) ^ 2)⁻¹ *
          ((N : ℝ) * ‖star q ⬝ᵥ freshEigenvector H j‖ ^ 2) ≤
      2 / (c₁ * ℓ / N) * (star q ⬝ᵥ ((H - (⟨freshEigenvalue H i, c₁ * ℓ / N⟩ : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  refine long_coupling_sum_le hH hs hN (by positivity) q i _ fun j hj => ?_
  have hj' := (Finset.mem_filter.1 hj).2
  refine le_trans ?_ (hgap i j hj')
  have : (ℓ : ℝ) ≤ labelDist i j := by exact_mod_cast hj'
  rw [div_le_div_iff_of_pos_right hNp]
  exact mul_le_mul_of_nonneg_left this hc.le

end BlockBand.Palm.MomentFlow
