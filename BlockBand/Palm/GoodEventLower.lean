module

public import BlockBand.Palm.GoodEventSpectral

/-!
# Good spectral event: the fixed-time bulk lower count

Deterministic. If a Hermitian `H` satisfies the averaged local law
`|⟨(H - z)⁻¹⟩ - m_s(z)| ≤ N^{-1/3}` on the coarse domain (`|x - E| ≤ r₀/2`,
`N^{-1/100} ≤ η ≤ 1`, the good event of the coarse relative local law), then with
`v₀ ≤ Im m_s ≤ v₀⁻¹` (fresh regularity) every centred interval of radius
`L ≥ 16 N^{-1/100}/v₀²` around `x₀`, `|x₀ - E| ≤ r₀/2`, contains at least
`(v₀³/64) N min(L,1)` eigenvalues. Proof: `im_le_count_add` at heights `η = min(L,1) v₀²/16`
and `min(L,1)`; no dyadic shells and no upper count are needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative

variable {N : ℕ}

theorem im_sub_le_norm (a b : ℂ) : |a.im - b.im| ≤ ‖a - b‖ := by
  rw [← Complex.sub_im]
  exact Complex.abs_im_le_norm _

/-- **Fixed-time lower count** from the averaged coarse local law. -/
theorem lower_count_fixed (hN : 0 < N) {F H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    {c₀ E r₀ s₀ v₀ s : ℝ} (hR : FreshRegular F c₀ E r₀ s₀ v₀) (hs : s ∈ Set.Icc (c₀ - s₀) c₀)
    (hv₀ : 0 < v₀) (hr₀ : 0 < r₀)
    (hloc : ∀ x η : ℝ, |x - E| ≤ r₀ / 2 → (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 →
      ‖(N : ℂ)⁻¹ * ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace -
          freshDyson F s ⟨x, η⟩‖ ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)))
    (hsmall : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ v₀ / 2) (hsmall' : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ v₀⁻¹)
    (hh1 : 16 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 ≤ 1)
    {x₀ L : ℝ} (hx₀ : |x₀ - E| ≤ r₀ / 2) (hL : 16 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 ≤ L) :
    v₀ ^ 3 / 64 * N * min L 1 ≤
      ((Finset.univ.filter fun k => |freshEigenvalue H k - x₀| ≤ L).card : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hhdef
  have hhpos : 0 < h := Real.rpow_pos_of_pos hNr _
  -- v₀ ≤ 1 from the regularity at (s, E, η = 0)
  have hv1 : v₀ ^ 2 ≤ 1 := by
    have hb := fresh_regular_bounds hR hs (z := ⟨E, 0⟩) (by simp [hr₀.le]) le_rfl zero_le_one
    have h1 : v₀ ≤ v₀⁻¹ := hb.1.trans hb.2
    have h2 : v₀ * v₀ ≤ v₀ * v₀⁻¹ := mul_le_mul_of_nonneg_left h1 hv₀.le
    rw [mul_inv_cancel₀ hv₀.ne'] at h2
    nlinarith
  have hv2 : 0 < v₀ ^ 2 := by positivity
  set L' := min L 1 with hL'def
  have hL'1 : L' ≤ 1 := min_le_right _ _
  have hLL' : L' ≤ L := min_le_left _ _
  have hL'ge : 16 * h / v₀ ^ 2 ≤ L' := le_min hL hh1
  have h16 : h ≤ 16 * h / v₀ ^ 2 := by
    rw [le_div_iff₀ hv2]; nlinarith
  have hL'h : h ≤ L' := h16.trans hL'ge
  have hL'pos : 0 < L' := lt_of_lt_of_le hhpos hL'h
  set η := L' * v₀ ^ 2 / 16 with hηdef
  have hηh : h ≤ η := by
    have := mul_le_mul_of_nonneg_right hL'ge (by positivity : (0 : ℝ) ≤ v₀ ^ 2 / 16)
    rw [hηdef]
    calc h = 16 * h / v₀ ^ 2 * (v₀ ^ 2 / 16) := by field_simp
      _ ≤ L' * (v₀ ^ 2 / 16) := this
      _ = L' * v₀ ^ 2 / 16 := by ring
  have hηpos : 0 < η := lt_of_lt_of_le hhpos hηh
  have hη1 : η ≤ 1 := by
    rw [hηdef]
    have : L' * v₀ ^ 2 ≤ 1 * 1 := mul_le_mul hL'1 hv1 (by positivity) zero_le_one
    linarith
  have hr : |x₀ - E| ≤ r₀ := by linarith
  -- lower bound at height η
  have hlow : v₀ / 2 ≤ ((N : ℂ)⁻¹ *
      ((H - (⟨x₀, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im := by
    have hm := (fresh_regular_bounds hR hs (z := ⟨x₀, η⟩) hr hηpos.le hη1).1
    have hl := hloc x₀ η hx₀ hηh hη1
    have := im_sub_le_norm ((N : ℂ)⁻¹ *
      ((H - (⟨x₀, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace) (freshDyson F s ⟨x₀, η⟩)
    rw [abs_le] at this
    linarith
  -- upper bound at height L'
  have hup : ((N : ℂ)⁻¹ *
      ((H - (⟨x₀, L'⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im ≤ 2 * v₀⁻¹ := by
    have hm := (fresh_regular_bounds hR hs (z := ⟨x₀, L'⟩) hr hL'pos.le hL'1).2
    have hl := hloc x₀ L' hx₀ hL'h hL'1
    have := im_sub_le_norm ((N : ℂ)⁻¹ *
      ((H - (⟨x₀, L'⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace) (freshDyson F s ⟨x₀, L'⟩)
    rw [abs_le] at this
    linarith
  have hsplit := im_le_count_add hH hN x₀ η L' hηpos hL'pos
  have hcnt : ((Finset.univ.filter fun k => |freshEigenvalue H k - x₀| ≤ L').card : ℝ) ≤ ((Finset.univ.filter fun k => |freshEigenvalue H k - x₀| ≤ L).card : ℝ) := by
    have hsub : (Finset.univ.filter fun k => |freshEigenvalue H k - x₀| ≤ L') ⊆
        (Finset.univ.filter fun k => |freshEigenvalue H k - x₀| ≤ L) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact le_trans hk hLL'
    exact_mod_cast Finset.card_le_card hsub
  have hterm : 2 * η / L' * (2 * v₀⁻¹) = v₀ / 4 := by
    rw [hηdef]; field_simp; ring
  have h2 : 2 * η / L' * ((N : ℂ)⁻¹ *
      ((H - (⟨x₀, L'⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im ≤ v₀ / 4 := by
    rw [← hterm]
    exact mul_le_mul_of_nonneg_left hup (by positivity)
  have hq : v₀ / 4 ≤ ((Finset.univ.filter fun k => |freshEigenvalue H k - x₀| ≤ L').card : ℝ) /
      (N * η) := by linarith
  rw [le_div_iff₀ (by positivity)] at hq
  have : v₀ ^ 3 / 64 * N * L' = v₀ / 4 * (N * η) := by rw [hηdef]; ring
  rw [this]
  exact hq.trans hcnt

end BlockBand.Palm.GoodEvent
