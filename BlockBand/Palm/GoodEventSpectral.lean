module

public import BlockBand.Palm.CoarseRelativeDyson
public import BlockBand.Model.Construction.OrderedEigenvalues
public import BlockBand.Palm.GoodEventNet

/-!
# Good spectral event: deterministic spectral layer

Deterministic facts about the increasing eigenvalues of a Hermitian matrix and the imaginary part
of its normalized resolvent trace.

* `freshEigenvalue_monotone`, `freshEigenvalue_weyl` (Weyl's inequality in `l2Norm` form),
  `freshEigenvalue_abs_le`, the `opB` forms, and `sum_freshEigenvalue` (spectral sums over the
  increasing enumeration equal sums over `hH.eigenvalues`).
* `im_trace_resolvent`: `Im⟨(H - x - iη)⁻¹⟩ = N⁻¹ Σ_k η/((λ_k - x)² + η²)`;
  `count_le_im`: `#{k : |λ_k - x| ≤ η} ≤ 2Nη Im⟨(H - x - iη)⁻¹⟩`;
  `im_le_count_add`: `Im⟨R(x+iη)⟩ ≤ #{|λ_k - x| ≤ L}/(Nη) + (2η/L) Im⟨R(x+iL)⟩`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
open BlockBand.Model.Construction BlockBand.Foundations.Spectral

variable {N : ℕ}

theorem freshEigenvalue_eq {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (k : Fin N) :
    freshEigenvalue H k = hH.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm k).rev := by
  unfold freshEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ hH]
  rfl

theorem freshEigenvalue_monotone {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    Monotone (freshEigenvalue H) := by
  intro i j hij
  rw [freshEigenvalue_eq hH, freshEigenvalue_eq hH]
  exact hH.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

theorem freshEigenvalue_weyl {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {ε : ℝ}
    (hε : ∀ x : Fin N → ℂ, l2Norm ((H - H') *ᵥ x) ≤ ε * l2Norm x) (k : Fin N) :
    |freshEigenvalue H k - freshEigenvalue H' k| ≤ ε := by
  rw [freshEigenvalue_eq hH, freshEigenvalue_eq hH']
  simp only [Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le
    (isSymmetric_toEuclideanLin_iff.mpr hH) (isSymmetric_toEuclideanLin_iff.mpr hH')
    finrank_euclideanSpace (fun x ↦ ?_)
  have h := hε (WithLp.ofLp x)
  rw [l2Norm_eq_norm, l2Norm_eq_norm, WithLp.toLp_ofLp] at h
  rw [← map_sub]
  exact h

theorem freshEigenvalue_abs_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {R : ℝ}
    (hR : ∀ x : Fin N → ℂ, l2Norm (H *ᵥ x) ≤ R * l2Norm x) (k : Fin N) :
    |freshEigenvalue H k| ≤ R := by
  have hZ : (0 : Matrix (Fin N) (Fin N) ℂ).IsHermitian := isHermitian_zero
  have hzero : freshEigenvalue (0 : Matrix (Fin N) (Fin N) ℂ) k = 0 := by
    rw [freshEigenvalue_eq hZ]
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply, Pi.zero_apply] using
      congrFun (hZ.eigenvalues_eq_zero_iff.mpr rfl)
        (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))
          (Fin.cast (Fintype.card_fin N).symm k).rev)
  have h := freshEigenvalue_weyl hH hZ (ε := R) (by simpa using hR) k
  rwa [hzero, sub_zero] at h

theorem sum_freshEigenvalue {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    ∑ k, f (freshEigenvalue H k) = ∑ i, f (hH.eigenvalues i) := by
  simp_rw [freshEigenvalue_eq hH]
  have h1 : ∑ k : Fin N, f (hH.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm k).rev) =
      ∑ j : Fin (Fintype.card (Fin N)), f (hH.eigenvalues₀ j) :=
    Fintype.sum_equiv ((finCongr (Fintype.card_fin N).symm).trans Fin.revPerm) _ _
      (fun k => rfl)
  rw [h1]
  exact Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))) _ _
    (fun j => by rw [hH.eigenvalues_apply_equivOfCardEq])

theorem scalar_resolvent_im (d x η : ℝ) :
    (certificateScalarResolvent d (⟨x, η⟩ : ℂ)).im = η / ((d - x) ^ 2 + η ^ 2) := by
  unfold certificateScalarResolvent
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
  ring

theorem im_trace_resolvent {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hN : 0 < N)
    (x η : ℝ) (hη : 0 < η) :
    ((N : ℂ)⁻¹ * ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im =
      (N : ℝ)⁻¹ * ∑ k, η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [trace_resolvent_eq_average hH (by simpa using hη.ne'), certificateAverage_im]
  simp only [certificateRealAverage, Fintype.expect_eq_sum_div_card, scalar_resolvent_im,
    Fintype.card_fin]
  rw [sum_freshEigenvalue hH (fun d => η / ((d - x) ^ 2 + η ^ 2)), div_eq_inv_mul]

theorem poisson_ge_of_near {d η : ℝ} (hη : 0 < η) (hd : |d| ≤ η) :
    1 ≤ 2 * η * (η / (d ^ 2 + η ^ 2)) := by
  have hd2 : d ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith

theorem poisson_split {d η L : ℝ} (hη : 0 < η) (hL : 0 < L) :
    η / (d ^ 2 + η ^ 2) ≤ (if |d| ≤ L then 1 / η else 0) + 2 * η / L * (L / (d ^ 2 + L ^ 2)) := by
  have h2 : 0 ≤ 2 * η / L * (L / (d ^ 2 + L ^ 2)) := by positivity
  split_ifs with hd
  · have : η / (d ^ 2 + η ^ 2) ≤ 1 / η := by
      rw [div_le_div_iff₀ (by positivity) hη]; nlinarith [sq_nonneg d]
    linarith
  · have hd' : L < |d| := lt_of_not_ge hd
    have hd2 : L ^ 2 < d ^ 2 := by
      have := pow_lt_pow_left₀ hd' hL.le two_ne_zero
      rwa [sq_abs] at this
    have heq : 2 * η / L * (L / (d ^ 2 + L ^ 2)) = 2 * η / (d ^ 2 + L ^ 2) := by
      field_simp
    rw [heq, zero_add, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg η, mul_pos hη hη]

theorem count_le_im {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hN : 0 < N)
    (x η : ℝ) (hη : 0 < η) :
    ((Finset.univ.filter fun k => |freshEigenvalue H k - x| ≤ η).card : ℝ) ≤
      2 * N * η * ((N : ℂ)⁻¹ * ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im := by
  rw [im_trace_resolvent hH hN x η hη]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : ∀ k, 0 ≤ η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2) := fun k => by positivity
  calc ((Finset.univ.filter fun k => |freshEigenvalue H k - x| ≤ η).card : ℝ)
      = ∑ _k ∈ Finset.univ.filter (fun k => |freshEigenvalue H k - x| ≤ η), (1 : ℝ) := by
        simp
    _ ≤ ∑ k ∈ Finset.univ.filter (fun k => |freshEigenvalue H k - x| ≤ η),
          2 * η * (η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact poisson_ge_of_near hη (Finset.mem_filter.mp hk).2
    _ ≤ ∑ k, 2 * η * (η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => mul_nonneg (by positivity) (hg k))
    _ = 2 * N * η * ((N : ℝ)⁻¹ * ∑ k, η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2)) := by
        rw [← Finset.mul_sum]
        field_simp

theorem im_le_count_add {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hN : 0 < N)
    (x η L : ℝ) (hη : 0 < η) (hL : 0 < L) :
    ((N : ℂ)⁻¹ * ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im ≤
      ((Finset.univ.filter fun k => |freshEigenvalue H k - x| ≤ L).card : ℝ) / (N * η) +
        2 * η / L *
          ((N : ℂ)⁻¹ * ((H - (⟨x, L⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im := by
  rw [im_trace_resolvent hH hN x η hη, im_trace_resolvent hH hN x L hL]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ k, η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2) ≤
      ((Finset.univ.filter fun k => |freshEigenvalue H k - x| ≤ L).card : ℝ) * (1 / η) +
        2 * η / L * ∑ k, L / ((freshEigenvalue H k - x) ^ 2 + L ^ 2) := by
    calc ∑ k, η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2)
        ≤ ∑ k, ((if |freshEigenvalue H k - x| ≤ L then 1 / η else 0) +
            2 * η / L * (L / ((freshEigenvalue H k - x) ^ 2 + L ^ 2))) :=
          Finset.sum_le_sum (fun k _ => poisson_split hη hL)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
            add_zero, Finset.sum_const, nsmul_eq_mul]
  calc (N : ℝ)⁻¹ * ∑ k, η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2)
      ≤ (N : ℝ)⁻¹ * (((Finset.univ.filter fun k => |freshEigenvalue H k - x| ≤ L).card : ℝ) *
          (1 / η) + 2 * η / L * ∑ k, L / ((freshEigenvalue H k - x) ^ 2 + L ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

theorem freshEigenvalue_weyl_opB {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) (k : Fin N) :
    |freshEigenvalue H k - freshEigenvalue H' k| ≤ opB (H - H') :=
  freshEigenvalue_weyl hH hH' (fun x => l2Norm_mulVec_le _ x) k

theorem freshEigenvalue_abs_le_opB {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (k : Fin N) : |freshEigenvalue H k| ≤ opB H :=
  freshEigenvalue_abs_le hH (fun x => l2Norm_mulVec_le _ x) k

end BlockBand.Palm.GoodEvent
