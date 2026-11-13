module

public import BlockBand.Palm.CoarseRelativeQuadMean

/-!
# Coarse relative local law: assembly of `CoarseRelativeContract`

* `mean_close`: `|m_s(z) - E⟨G_s(z)⟩| ≤ N^{-1/3} N^{-1/100}/16` on the coarse domain, `N ≥ N₀`.
* `coarse_quad_pointwise`: for every `D'` there is `N₀` with
  `P((N^{-1/3}/2) q* Im M_s q < |q*(G_s - M_s)q|) ≤ N^{-D'}` uniformly over the fresh class,
  the variance window, the coarse domain and all `q ∈ ℂ^N`.
* `coarseRelative_holds`: `GaussianLpGradient → MultivariateGaussianIBP → CoarseRelativeContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

/-- `|m_s - m̄| ≤ N^{-1/3} N^{-1/100}/16` eventually, uniformly. -/
theorem mean_close (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
        FreshClass F A c₀ E r₀ s₀ v₀ → ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ z : ℂ,
        CoarseDomain N E r₀ z →
          ‖freshDyson F s z - meanTrace F s z‖ ≤
            (N : ℝ) ^ (-(1 / 3 : ℝ)) * ((N : ℝ) ^ (1 / 100 : ℝ))⁻¹ / 16 := by
  intro A c₀ r₀ s₀ v₀ hK
  obtain ⟨C₁, hC₁, hL1⟩ := coarseTrace_L1_le hLp
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  set B := 1 + v₀⁻¹ with hBdef
  have hB1 : 1 ≤ B := by have := inv_pos.mpr hv0; linarith
  obtain ⟨Na, hNa, ha⟩ := const_le_rpow_eventually (2 * C₁) (19 / 20) (by norm_num)
  obtain ⟨Nb, hNb, hb⟩ := const_le_rpow_eventually (64 * B * C₁) (179 / 300) (by norm_num)
  refine ⟨max Na Nb, lt_of_lt_of_le hNa (le_max_left _ _), ?_⟩
  intro N hN F E hC s hs z hz
  have hNa' : Na ≤ N := le_trans (le_max_left _ _) hN
  have hNb' : Nb ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le hNa hNa'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hF := hC.1
  obtain ⟨hs0, hss, hs1⟩ := fresh_s_bounds hK hs
  obtain ⟨hspos, -, hηpos, hm, -, hδm⟩ := coarse_domain_facts hNpos hK hC hs hz
  set η := z.im with hηdef
  set X := (N : ℝ) ^ (1 / 100 : ℝ) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by norm_num)
  have hXpos : 0 < X := by linarith
  have hh : (N : ℝ) ^ (-(1 / 100 : ℝ)) = X⁻¹ := by rw [hXdef, Real.rpow_neg hNr.le]
  have hηX : X⁻¹ ≤ η := by rw [← hh]; exact hz.2.1
  have hη1 : η ≤ 1 := hz.2.2
  have hηinv : η⁻¹ ≤ X := by
    have := inv_anti₀ (inv_pos.mpr hXpos) hηX
    rwa [inv_inv] at this
  have hXpow : ∀ k : ℕ, X ^ k = (N : ℝ) ^ ((k : ℝ) / 100) := by
    intro k
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  -- residual of m̄
  set mb := meanTrace F s z with hmb
  set t := Real.toNNReal (1 / N)
  have hmbim := meanTrace_im_pos hF hηpos (s := s) hNpos
  have hmbn := meanTrace_norm_le hF hηpos (s := s) hNpos
  have hwb : (z + (s : ℂ) * mb).im ≠ 0 :=
    (add_ofReal_mul_im_pos hspos hηpos.le hmbim).ne'
  set e := s * (η⁻¹ * η⁻¹) * (C₁ * (Real.sqrt s * (N : ℝ)⁻¹ * (η ^ 2)⁻¹)) with hedef
  have hres : ‖certificateDysonResidual hF.eigenvalues s z mb‖ ≤ e := by
    rw [residual_eq_trace_form hF hwb]
    have h1 := meanTrace_residual_le hF hspos.le hηpos hNpos hIBP
    have h2 := hL1 N hNpos F hF s hspos.le z hηpos
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- e ≤ C₁ N⁻¹ X⁴
  have hsqrt1 : Real.sqrt s ≤ 1 := by rw [Real.sqrt_le_one]; exact hs1.le
  have he : e ≤ C₁ * (N : ℝ)⁻¹ * X ^ 4 := by
    have hη4 : η⁻¹ * η⁻¹ * (η ^ 2)⁻¹ ≤ X ^ 4 := by
      rw [← inv_pow]
      have h0 : 0 ≤ η⁻¹ := by positivity
      calc η⁻¹ * η⁻¹ * (η⁻¹) ^ 2 ≤ X * X * X ^ 2 :=
            mul_le_mul (mul_le_mul hηinv hηinv h0 (by positivity))
              (pow_le_pow_left₀ h0 hηinv 2) (by positivity) (by positivity)
        _ = X ^ 4 := by ring
    calc e = (s * Real.sqrt s) * C₁ * (N : ℝ)⁻¹ * (η⁻¹ * η⁻¹ * (η ^ 2)⁻¹) := by
          rw [hedef]; ring
      _ ≤ 1 * C₁ * (N : ℝ)⁻¹ * X ^ 4 := by
          gcongr
          calc s * Real.sqrt s ≤ 1 * 1 :=
                mul_le_mul hs1.le hsqrt1 (Real.sqrt_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = C₁ * (N : ℝ)⁻¹ * X ^ 4 := by ring
  have he0 : 0 ≤ e := by positivity
  -- (a) s e ≤ η / 2
  have hcondA : 2 * C₁ * X ^ 5 ≤ N := by
    have h := ha N hNa'
    rw [hXpow 5]
    have h5 : ((5 : ℕ) : ℝ) / 100 = 1 / 20 := by norm_num
    rw [h5]
    calc 2 * C₁ * (N : ℝ) ^ (1 / 20 : ℝ) ≤ (N : ℝ) ^ (19 / 20 : ℝ) * (N : ℝ) ^ (1 / 20 : ℝ) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = N := by rw [← Real.rpow_add hNr]; norm_num
  have hse : s * e ≤ η / 2 := by
    have h1 : s * e ≤ e := by
      calc s * e ≤ 1 * e := mul_le_mul_of_nonneg_right hs1.le he0
        _ = e := one_mul e
    have h2 : C₁ * (N : ℝ)⁻¹ * X ^ 4 ≤ X⁻¹ / 2 := by
      calc C₁ * (N : ℝ)⁻¹ * X ^ 4 = (2 * C₁ * X ^ 5) * ((N : ℝ)⁻¹ * (X⁻¹ / 2)) := by
            field_simp
        _ ≤ N * ((N : ℝ)⁻¹ * (X⁻¹ / 2)) := mul_le_mul_of_nonneg_right hcondA (by positivity)
        _ = X⁻¹ / 2 := by field_simp
    linarith
  -- stability
  set δ₀ := X⁻¹ ^ 2 / (4 * B) with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  have hδ1 : δ₀ ≤ η / (η + s * (freshDyson F s z).im) := by
    refine le_trans ?_ hδm
    rw [hh, hδ₀]
    have hXi : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hX1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : X⁻¹ ^ 2 ≤ X⁻¹ := by
      calc X⁻¹ ^ 2 = X⁻¹ * X⁻¹ := pow_two _
        _ ≤ X⁻¹ * 1 := mul_le_mul_of_nonneg_left hXi (by positivity)
        _ = X⁻¹ := mul_one _
    nlinarith
  have hδ2 : δ₀ ≤ (η - s * e) / (η + s * mb.im) := by
    have hmbim' : mb.im ≤ η⁻¹ := (Complex.im_le_norm mb).trans hmbn
    have hden : η + s * mb.im ≤ 2 * η⁻¹ := by
      have h1 : s * mb.im ≤ η⁻¹ := by
        calc s * mb.im ≤ 1 * η⁻¹ := mul_le_mul hs1.le hmbim' hmbim.le zero_le_one
          _ = η⁻¹ := one_mul _
      have h2 : η ≤ η⁻¹ := by
        rw [le_inv_comm₀ hηpos hηpos]
        calc η ≤ 1 := hη1
          _ ≤ η⁻¹ := one_le_inv₀ hηpos |>.mpr hη1
      linarith
    have hdenpos : 0 < η + s * mb.im := by positivity
    have hnum : η / 2 ≤ η - s * e := by linarith
    have hlow : η ^ 2 / 4 ≤ (η - s * e) / (η + s * mb.im) := by
      rw [le_div_iff₀ hdenpos]
      calc η ^ 2 / 4 * (η + s * mb.im) ≤ η ^ 2 / 4 * (2 * η⁻¹) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ = η / 2 := by field_simp; ring
        _ ≤ η - s * e := hnum
    refine le_trans ?_ hlow
    rw [hδ₀]
    have h1 : X⁻¹ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hηX 2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hstab := approx_root_stability hF hNpos hspos hηpos hm hmbim hres hδ1 hδ2
  -- |m - m̄| ≤ N^{-1/3}/4
  set ε := (N : ℝ) ^ (-(1 / 3 : ℝ)) with hεdef
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hNr _
  have hcondB : 64 * B * C₁ * X ^ 7 ≤ N * ε := by
    have h := hb N hNb'
    have hsplit : (N : ℝ) * ε = (N : ℝ) ^ (7 / 100 : ℝ) * (N : ℝ) ^ (179 / 300 : ℝ) := by
      have h1 : (N : ℝ) * ε = (N : ℝ) ^ (1 + (-(1 / 3 : ℝ))) := by
        rw [Real.rpow_add hNr, Real.rpow_one]
      rw [h1, ← Real.rpow_add hNr]
      norm_num
    rw [hXpow 7, hsplit]
    have : ((7 : ℕ) : ℝ) / 100 = 7 / 100 := by norm_num
    rw [this]
    calc 64 * B * C₁ * (N : ℝ) ^ (7 / 100 : ℝ) = (N : ℝ) ^ (7 / 100 : ℝ) * (64 * B * C₁) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have h1 : ‖freshDyson F s z - mb‖ ≤ e / δ₀ := by
    rw [le_div_iff₀ hδ₀pos]; exact hstab
  refine h1.trans ?_
  rw [div_le_div_iff₀ hδ₀pos (by norm_num)]
  have h2 : e * 16 ≤ C₁ * (N : ℝ)⁻¹ * X ^ 4 * 16 := by linarith
  have h3 : C₁ * (N : ℝ)⁻¹ * X ^ 4 * 16 ≤ ε * X⁻¹ * δ₀ := by
    rw [hδ₀]
    have : C₁ * (N : ℝ)⁻¹ * X ^ 4 * 16 = (64 * B * C₁ * X ^ 7) * ((N : ℝ)⁻¹ *
        (X⁻¹ * (X⁻¹ ^ 2 / (4 * B)))) := by
      field_simp
      ring
    rw [this]
    calc (64 * B * C₁ * X ^ 7) * ((N : ℝ)⁻¹ * (X⁻¹ * (X⁻¹ ^ 2 / (4 * B))))
        ≤ (N * ε) * ((N : ℝ)⁻¹ * (X⁻¹ * (X⁻¹ ^ 2 / (4 * B)))) :=
          mul_le_mul_of_nonneg_right hcondB (by positivity)
      _ = ε * X⁻¹ * (X⁻¹ ^ 2 / (4 * B)) := by field_simp
  linarith

theorem nsq_pos_of_ne_zero {ι : Type} [Fintype ι] {v : ι → ℂ} (hv : v ≠ 0) : 0 < nsq v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have : 0 < ‖v k‖ ^ 2 := by
    have : v k ≠ 0 := by simpa using hk
    positivity
  exact lt_of_lt_of_le this
    (Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ k))

theorem coarseResolvent_measurable {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) :
    Measurable (fun G : Matrix (Fin N) (Fin N) ℂ => coarseResolvent F G s z) := by
  have h : (fun G : Matrix (Fin N) (Fin N) ℂ => coarseResolvent F G s z) = fun G =>
      Ring.inverse (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det •
        (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by
    funext G
    unfold coarseResolvent
    rw [Matrix.inv_def]
  rw [h]
  have h1 : Continuous fun G : Matrix (Fin N) (Fin N) ℂ =>
      (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by fun_prop
  have h2 : Continuous fun G : Matrix (Fin N) (Fin N) ℂ =>
      (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by fun_prop
  have h3 : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      Ring.inverse (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
    simp_rw [Ring.inverse_eq_inv']
    exact h1.measurable.inv
  exact h3.smul h2.measurable

theorem quadErr_measurable {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ)
    (q : Fin N → ℂ) : Measurable (fun G : Matrix (Fin N) (Fin N) ℂ => quadErr F G s z q) := by
  have hc : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ =>
      ‖star q ⬝ᵥ ((A - freshM F s z) *ᵥ q)‖) := by
    apply Continuous.norm
    apply Continuous.dotProduct continuous_const
    exact (continuous_id.sub continuous_const).matrix_mulVec continuous_const
  exact hc.measurable.comp (coarseResolvent_measurable F s z)

set_option maxHeartbeats 4000000 in

/-- The directional estimate at a fixed point, from the Gaussian inputs only. -/
theorem coarse_quad_pointwise (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ D' : ℝ, ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
        FreshClass F A c₀ E r₀ s₀ v₀ → ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ z : ℂ,
        CoarseDomain N E r₀ z → ∀ q : Fin N → ℂ,
          gueMeasure (Fin N) (Real.toNNReal (1 / N))
              {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z q < quadErr F G s z q} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro A c₀ r₀ s₀ v₀ hK D'
  obtain ⟨Nm, hNm, hmc⟩ := mean_close hLp hIBP A c₀ r₀ s₀ v₀ hK
  obtain ⟨C₁, C', hC₁, hC', hmean⟩ := quadFn_mean_le hLp hIBP
  obtain ⟨C, C'', hC, hC'', hfl⟩ := quad_fluctuation hLp
  set D'' := max D' 0 with hD''
  set p : ℝ := 300 * (D'' + 1) / 41 with hpdef
  have hp1 : 1 ≤ p := by
    have : 0 ≤ D'' := le_max_right _ _
    rw [hpdef, le_div_iff₀ (by norm_num)]
    linarith
  set K := 16 * C * Real.sqrt p * (2 + 4 * C'' ^ 2 * p) with hKdef
  have hK0 : 0 < K := by positivity
  obtain ⟨Na, hNa, ha⟩ := const_le_rpow_eventually (48 * (2 * C₁ + C' ^ 2)) (7 / 60) (by norm_num)
  obtain ⟨Nc, hNc, hc⟩ := const_le_rpow_eventually (K ^ p) 1 one_pos
  refine ⟨max (max Nm Na) Nc, ?_⟩
  intro N hN F E hC s hs z hz q
  have hNm' : Nm ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc' : Nc ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le hNc hNc'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  set ε := (N : ℝ) ^ (-(1 / 3 : ℝ)) with hεdef
  have hεpos : 0 < ε := Real.rpow_pos_of_pos hNr _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  by_cases hq : q = 0
  · subst hq
    have hempty : {G : Matrix (Fin N) (Fin N) ℂ | ε / 2 * quadIm F s z 0 < quadErr F G s z 0} = ∅ := by
      ext G
      simp [quadIm, quadErr]
    rw [hempty, measure_empty]
    exact bot_le
  have hF := hC.1
  obtain ⟨hs0, hss, hs1⟩ := fresh_s_bounds hK hs
  obtain ⟨hspos, -, hηpos, hm, -, -⟩ := coarse_domain_facts hNpos hK hC hs hz
  set η := z.im with hηdef
  set X := (N : ℝ) ^ (1 / 100 : ℝ) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by norm_num)
  have hXpos : 0 < X := by linarith
  have hh : (N : ℝ) ^ (-(1 / 100 : ℝ)) = X⁻¹ := by rw [hXdef, Real.rpow_neg hNr.le]
  have hηX : X⁻¹ ≤ η := by rw [← hh]; exact hz.2.1
  have hη1 : η ≤ 1 := hz.2.2
  have hηinv : η⁻¹ ≤ X := by
    have := inv_anti₀ (inv_pos.mpr hXpos) hηX
    rwa [inv_inv] at this
  have hηi1 : 1 ≤ η⁻¹ := one_le_inv₀ hηpos |>.mpr hη1
  have hXpow : ∀ k : ℕ, X ^ k = (N : ℝ) ^ ((k : ℝ) / 100) := by
    intro k
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  set t := Real.toNNReal (1 / N)
  set v := freshM F s z *ᵥ q with hv
  have hw : (freshW F s z).im ≠ 0 := (add_ofReal_mul_im_pos hspos hηpos.le hm).ne'
  have hv0 : 0 < nsq v := by
    apply nsq_pos_of_ne_zero
    intro hv0
    apply hq
    have h := hermitian_shift_mul_inv hF hw
    calc q = ((F - freshW F s z • (1 : Matrix (Fin N) (Fin N) ℂ)) * freshM F s z) *ᵥ q := by
          rw [freshM_eq, h, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, ← hv, hv0, mulVec_zero]
  set κ := quadIm F s z q with hκ
  have hκη : η * nsq v ≤ κ := by
    rw [hκ, quadIm, freshM_quad_im hF hw q, ← hv]
    have : 0 ≤ s * (freshDyson F s z).im := mul_nonneg hspos.le hm.le
    nlinarith [nsq_nonneg v]
  have hκpos : 0 < κ := lt_of_lt_of_le (mul_pos hηpos hv0) hκη
  -- the mean error
  have hmb := hmc N hNm' F E hC s hs z hz
  rw [← hXdef] at hmb
  have hmb' : ‖meanTrace F s z - freshDyson F s z‖ ≤ ε * X⁻¹ / 16 := by
    rw [norm_sub_rev]; exact hmb
  have hclose : s * ‖meanTrace F s z - freshDyson F s z‖ ≤ η := by
    calc s * ‖meanTrace F s z - freshDyson F s z‖ ≤ 1 * (ε * X⁻¹ / 16) :=
          mul_le_mul hs1.le hmb' (norm_nonneg _) zero_le_one
      _ ≤ X⁻¹ := by
          have : ε * X⁻¹ ≤ X⁻¹ := by
            calc ε * X⁻¹ ≤ 1 * X⁻¹ := mul_le_mul_of_nonneg_right hε1 (by positivity)
              _ = X⁻¹ := one_mul _
          have : 0 ≤ ε * X⁻¹ := by positivity
          linarith
      _ ≤ η := hηX
  have hME := hmean N hNpos F hF s hspos hs1.le z hηpos hη1 hm hclose q hv0
  rw [← hv] at hME
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hNsq : (N : ℝ)⁻¹ ≤ (Real.sqrt N)⁻¹ := by
    apply inv_anti₀ hsN
    calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          le_mul_of_one_le_right hsN.le (Real.one_le_sqrt.mpr hN1)
      _ = N := Real.mul_self_sqrt hNr.le
  have hcondA : 48 * (2 * C₁ + C' ^ 2) * X ^ 5 ≤ Real.sqrt N * ε := by
    have h := ha N hNa'
    have hsplit : Real.sqrt N * ε = (N : ℝ) ^ (5 / 100 : ℝ) * (N : ℝ) ^ (7 / 60 : ℝ) := by
      rw [Real.sqrt_eq_rpow, hεdef, ← Real.rpow_add hNr, ← Real.rpow_add hNr]
      norm_num
    rw [hXpow 5, hsplit]
    have : ((5 : ℕ) : ℝ) / 100 = 5 / 100 := by norm_num
    rw [this]
    calc 48 * (2 * C₁ + C' ^ 2) * (N : ℝ) ^ (5 / 100 : ℝ) =
        (N : ℝ) ^ (5 / 100 : ℝ) * (48 * (2 * C₁ + C' ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have hbr : 6 * η⁻¹ * (C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 +
      C' ^ 2 * (Real.sqrt N)⁻¹) ≤ ε * X⁻¹ / 8 := by
    have h0 : 0 ≤ η⁻¹ := by positivity
    have hη2 : (η⁻¹) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ h0 hηinv 2
    have hη3 : (η⁻¹) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ h0 hηinv 3
    have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX1 (by norm_num)
    have hX03 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    have hsi : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
    have hin : C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 +
        C' ^ 2 * (Real.sqrt N)⁻¹ ≤ (2 * C₁ + C' ^ 2) * X ^ 3 * (Real.sqrt N)⁻¹ := by
      have e1 : C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 ≤ C₁ * (Real.sqrt N)⁻¹ * X ^ 3 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hNsq hC₁.le) (hη2.trans hX23)
          (by positivity) (by positivity)
      have e2 : C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 ≤ C₁ * (Real.sqrt N)⁻¹ * X ^ 3 :=
        mul_le_mul_of_nonneg_left hη3 (by positivity)
      have e3 : C' ^ 2 * (Real.sqrt N)⁻¹ ≤ C' ^ 2 * (Real.sqrt N)⁻¹ * X ^ 3 :=
        le_mul_of_one_le_right (by positivity) hX03
      nlinarith
    have hstep : 6 * η⁻¹ * (C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 +
        C' ^ 2 * (Real.sqrt N)⁻¹) ≤ 6 * X * ((2 * C₁ + C' ^ 2) * X ^ 3 * (Real.sqrt N)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hηinv (by norm_num)) hin (by positivity)
        (by positivity)
    refine hstep.trans ?_
    calc 6 * X * ((2 * C₁ + C' ^ 2) * X ^ 3 * (Real.sqrt N)⁻¹)
        = (48 * (2 * C₁ + C' ^ 2) * X ^ 5) * ((Real.sqrt N)⁻¹ * X⁻¹ / 8) := by
          field_simp
          ring
      _ ≤ (Real.sqrt N * ε) * ((Real.sqrt N)⁻¹ * X⁻¹ / 8) :=
          mul_le_mul_of_nonneg_right hcondA (by positivity)
      _ = ε * X⁻¹ / 8 := by field_simp
  have hEQ : ‖∫ y, quadFn F s z t q y ∂coordLaw N - star q ⬝ᵥ (freshM F s z *ᵥ q)‖ ≤
      ε / 4 * κ := by
    refine hME.trans ?_
    have hsum : 2 * ‖meanTrace F s z - freshDyson F s z‖ +
        6 * η⁻¹ * (C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 +
          C' ^ 2 * (Real.sqrt N)⁻¹) ≤ ε / 4 * η := by
      have : ε * X⁻¹ ≤ ε * η := mul_le_mul_of_nonneg_left hηX hεpos.le
      linarith
    calc nsq v * _ ≤ nsq v * (ε / 4 * η) := mul_le_mul_of_nonneg_left hsum (nsq_nonneg v)
      _ = ε / 4 * (η * nsq v) := by ring
      _ ≤ ε / 4 * κ := mul_le_mul_of_nonneg_left hκη (by positivity)
  -- transfer to coordinates
  have hcoord : Measurable (gueCoord (ι := Fin N) t) := by
    have hc : Measurable (BlockBand.SourceProcess.circularBrownianCoordinates (ι := Fin N)) := by
      apply Measurable.of_eval
      intro u
      unfold BlockBand.SourceProcess.circularBrownianCoordinates
      fun_prop
    have hg : Continuous (gueSample (ι := Fin N) t) := by
      unfold gueSample
      fun_prop
    exact hg.measurable.comp hc
  have hS : MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | ε / 2 * κ < quadErr F G s z q} :=
    measurableSet_lt measurable_const (quadErr_measurable F s z q)
  rw [gueMeasure_eq_map_gaussianProduct, Measure.map_apply hcoord hS]
  have hsub : gueCoord t ⁻¹' {G : Matrix (Fin N) (Fin N) ℂ | ε / 2 * κ < quadErr F G s z q} ⊆
      {y | ε / 4 * κ ≤ ‖quadFn F s z t q y - ∫ y', quadFn F s z t q y' ∂coordLaw N‖} := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
    have heq : quadErr F (gueCoord t y) s z q =
        ‖quadFn F s z t q y - star q ⬝ᵥ (freshM F s z *ᵥ q)‖ := by
      unfold quadErr quadFn
      rw [sub_mulVec, dotProduct_sub]
    rw [heq] at hy
    have htri := norm_sub_le_norm_sub_add_norm_sub (quadFn F s z t q y)
      (∫ y', quadFn F s z t q y' ∂coordLaw N) (star q ⬝ᵥ (freshM F s z *ᵥ q))
    linarith
  refine (measure_mono hsub).trans ?_
  refine (hfl p hp1 N hNpos F hF s hspos hs1.le z hηpos hη1 hm q (ε / 4 * κ)
    (by positivity)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [← hv]
  set base := C * Real.sqrt p * (4 * Real.sqrt (s / N) * (η⁻¹) ^ 2 *
    ((2 + 4 * C'' ^ 2 * p) * nsq v)) / (ε / 4 * κ) with hbase
  have hbase0 : 0 ≤ base := by
    rw [hbase]
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (nsq_nonneg v)))
  set Y := (N : ℝ) ^ (-(41 / 300 : ℝ)) with hYdef
  have hbaseY : base ≤ K * Y := by
    have hsq : Real.sqrt (s / N) ≤ (Real.sqrt N)⁻¹ := by
      rw [Real.sqrt_div' _ hNr.le, div_eq_mul_inv]
      calc Real.sqrt s * (Real.sqrt N)⁻¹ ≤ 1 * (Real.sqrt N)⁻¹ :=
            mul_le_mul_of_nonneg_right (by rw [Real.sqrt_le_one]; exact hs1.le) (by positivity)
        _ = _ := one_mul _
    have hYeq : (Real.sqrt N)⁻¹ * X ^ 3 / ε = Y := by
      rw [hXpow 3, hεdef, hYdef, Real.sqrt_eq_rpow, ← Real.rpow_neg hNr.le, div_eq_mul_inv,
        ← Real.rpow_neg hNr.le, neg_neg, ← Real.rpow_add hNr, ← Real.rpow_add hNr]
      norm_num
    have hη3 : (η⁻¹) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by positivity) hηinv 3
    have hnum0 : 0 ≤ C * Real.sqrt p * (2 + 4 * C'' ^ 2 * p) := by positivity
    calc base ≤ C * Real.sqrt p * (4 * Real.sqrt (s / N) * (η⁻¹) ^ 2 *
          ((2 + 4 * C'' ^ 2 * p) * nsq v)) / (ε / 4 * (η * nsq v)) := by
          rw [hbase]
          apply div_le_div_of_nonneg_left _ (by positivity)
            (mul_le_mul_of_nonneg_left hκη (by positivity))
          exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
            (mul_nonneg (by positivity) (nsq_nonneg v)))
      _ = 16 * (C * Real.sqrt p * (2 + 4 * C'' ^ 2 * p)) * (Real.sqrt (s / N) * (η⁻¹) ^ 3 / ε) := by
          field_simp
          ring
      _ ≤ 16 * (C * Real.sqrt p * (2 + 4 * C'' ^ 2 * p)) * ((Real.sqrt N)⁻¹ * X ^ 3 / ε) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (mul_le_mul hsq hη3 (by positivity) (by positivity)) hεpos.le) (by positivity)
      _ = K * Y := by rw [hYeq, hKdef]; ring
  have hpow : base ^ p ≤ K ^ p * Y ^ p := by
    rw [← Real.mul_rpow hK0.le (by positivity)]
    exact Real.rpow_le_rpow hbase0 hbaseY (by linarith)
  have hYp : Y ^ p = (N : ℝ) ^ (-(D'' + 1)) := by
    rw [hYdef, ← Real.rpow_mul hNr.le, hpdef]
    congr 1
    ring
  have hKc := hc N hNc'
  rw [Real.rpow_one] at hKc
  have hND : (N : ℝ) * (N : ℝ) ^ (-(D'' + 1)) ≤ (N : ℝ) ^ (-D') := by
    have : (N : ℝ) * (N : ℝ) ^ (-(D'' + 1)) = (N : ℝ) ^ (-D'') := by
      have h1 : (N : ℝ) * (N : ℝ) ^ (-(D'' + 1)) = (N : ℝ) ^ (1 + (-(D'' + 1))) := by
        rw [Real.rpow_add hNr, Real.rpow_one]
      rw [h1]
      congr 1; ring
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by have := le_max_left D' 0; linarith)
  calc base ^ p ≤ K ^ p * Y ^ p := hpow
    _ ≤ (N : ℝ) * (N : ℝ) ^ (-(D'' + 1)) := by
        rw [hYp]; exact mul_le_mul_of_nonneg_right hKc (by positivity)
    _ ≤ (N : ℝ) ^ (-D') := hND

/-- **The coarse relative local law** `CoarseRelativeContract`, from the Gaussian inputs
`GaussianLpGradient` and `MultivariateGaussianIBP` only. -/
theorem coarseRelative_holds (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    CoarseRelativeContract := by
  apply coarseRelative_of_pointwise
  intro A c₀ r₀ s₀ v₀ hK D'
  obtain ⟨N₁, h₁⟩ := coarse_trace_pointwise hLp hIBP A c₀ r₀ s₀ v₀ hK D'
  obtain ⟨N₂, h₂⟩ := coarse_quad_pointwise hLp hIBP A c₀ r₀ s₀ v₀ hK D'
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN F E hC s hs z hz
  exact ⟨h₁ N (le_trans (le_max_left _ _) hN) F E hC s hs z hz,
    fun q => h₂ N (le_trans (le_max_right _ _) hN) F E hC s hs z hz q⟩

end BlockBand.Palm.CoarseRelative
