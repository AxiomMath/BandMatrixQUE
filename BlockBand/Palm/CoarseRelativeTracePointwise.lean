module

public import BlockBand.Palm.CoarseRelativeTraceMean

/-!
# Coarse relative local law: the trace estimate at a fixed spectral point

The exact mean equation and the `p = 1` gradient bound give the residual
`|m̄ - ⟨(F - z - s m̄)⁻¹⟩| ≤ C N⁻¹ η⁻⁴`; stability of approximate Dyson roots gives
`|m̄ - m_s| ≤ C' N^{-47/50}`; the fixed-moment Markov bound at
`p = 150 (max(D',0) + 1)/97` gives the tail bound for `|⟨G_s(z)⟩ - m_s(z)|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

/-- Every constant is eventually below a positive power of `N`. -/
theorem const_le_rpow_eventually (K a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → K ≤ (N : ℝ) ^ a := by
  refine ⟨⌈(max K 1) ^ a⁻¹⌉₊ + 1, Nat.succ_pos _, ?_⟩
  intro N hN
  have h0 : 0 ≤ (max K 1) ^ a⁻¹ := Real.rpow_nonneg (by positivity) _
  have h1 : (max K 1) ^ a⁻¹ ≤ N := by
    have := Nat.le_ceil ((max K 1) ^ a⁻¹)
    have h2 : ((⌈(max K 1) ^ a⁻¹⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  calc K ≤ max K 1 := le_max_left _ _
    _ = ((max K 1) ^ a⁻¹) ^ a := (Real.rpow_inv_rpow (by positivity) ha.ne').symm
    _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow h0 h1 ha.le

/-- The trace estimate at a fixed spectral point. -/
theorem coarse_trace_pointwise (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ D' : ℝ, ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
        FreshClass F A c₀ E r₀ s₀ v₀ → ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ z : ℂ,
        CoarseDomain N E r₀ z →
          gueMeasure (Fin N) (Real.toNNReal (1 / N))
              {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 < traceErr F G s z} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
  intro A c₀ r₀ s₀ v₀ hK D'
  obtain ⟨C₁, hC₁, hL1⟩ := coarseTrace_L1_le hLp
  obtain ⟨C₂, hC₂, hfl⟩ := coarseTrace_fluctuation_coord hLp
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  set B := 1 + v₀⁻¹ with hBdef
  have hB1 : 1 ≤ B := by have := inv_pos.mpr hv0; linarith
  set D'' := max D' 0 with hD''
  set p : ℝ := 150 * (D'' + 1) / 97 with hpdef
  have hp1 : 1 ≤ p := by
    have : 0 ≤ D'' := le_max_right _ _
    rw [hpdef, le_div_iff₀ (by norm_num)]
    linarith
  obtain ⟨Na, hNa, ha⟩ := const_le_rpow_eventually (2 * C₁) (19 / 20) (by norm_num)
  obtain ⟨Nb, hNb, hb⟩ := const_le_rpow_eventually (16 * B * C₁) (91 / 150) (by norm_num)
  obtain ⟨Nc, hNc, hc⟩ := const_le_rpow_eventually ((4 * C₂ * Real.sqrt p) ^ p) 1 one_pos
  refine ⟨max (max Na Nb) Nc, ?_⟩
  intro N hN F E hC s hs z hz
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc' : Nc ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le hNc hNc'
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
  have hcondB : 16 * B * C₁ * X ^ 6 ≤ N * ε := by
    have h := hb N hNb'
    have hsplit : (N : ℝ) * ε = (N : ℝ) ^ (6 / 100 : ℝ) * (N : ℝ) ^ (91 / 150 : ℝ) := by
      have h1 : (N : ℝ) * ε = (N : ℝ) ^ (1 + (-(1 / 3 : ℝ))) := by
        rw [Real.rpow_add hNr, Real.rpow_one]
      rw [h1, ← Real.rpow_add hNr]
      norm_num
    rw [hXpow 6, hsplit]
    have : ((6 : ℕ) : ℝ) / 100 = 6 / 100 := by norm_num
    rw [this]
    calc 16 * B * C₁ * (N : ℝ) ^ (6 / 100 : ℝ) = (N : ℝ) ^ (6 / 100 : ℝ) * (16 * B * C₁) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have hmm : ‖freshDyson F s z - mb‖ ≤ ε / 4 := by
    have h1 : ‖freshDyson F s z - mb‖ ≤ e / δ₀ := by
      rw [le_div_iff₀ hδ₀pos]; exact hstab
    refine h1.trans ?_
    rw [div_le_div_iff₀ hδ₀pos (by norm_num)]
    have h2 : e * 4 ≤ C₁ * (N : ℝ)⁻¹ * X ^ 4 * 4 := by linarith
    have h3 : C₁ * (N : ℝ)⁻¹ * X ^ 4 * 4 ≤ ε * δ₀ := by
      rw [hδ₀]
      have hX2 : X⁻¹ ^ 2 * X ^ 2 = 1 := by field_simp
      have : C₁ * (N : ℝ)⁻¹ * X ^ 4 * 4 = (16 * B * C₁ * X ^ 6) * ((N : ℝ)⁻¹ *
          (X⁻¹ ^ 2 / (4 * B))) := by
        field_simp
        ring
      rw [this]
      calc (16 * B * C₁ * X ^ 6) * ((N : ℝ)⁻¹ * (X⁻¹ ^ 2 / (4 * B)))
          ≤ (N * ε) * ((N : ℝ)⁻¹ * (X⁻¹ ^ 2 / (4 * B))) :=
            mul_le_mul_of_nonneg_right hcondB (by positivity)
        _ = ε * (X⁻¹ ^ 2 / (4 * B)) := by field_simp
    linarith
  -- event inclusion and the fluctuation bound
  have hmeasG := coarseTrace_measurable F s z
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
  have hS : MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | ε / 2 < traceErr F G s z} :=
    measurableSet_lt measurable_const ((hmeasG.sub measurable_const).norm)
  rw [gueMeasure_eq_map_gaussianProduct, Measure.map_apply hcoord hS]
  have hsub : gueCoord t ⁻¹' {G : Matrix (Fin N) (Fin N) ℂ | ε / 2 < traceErr F G s z} ⊆
      {y | ε / 4 ≤ ‖coarseTraceFn F s z t y - ∫ y', coarseTraceFn F s z t y' ∂coordLaw N‖} := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, traceErr] at hy
    simp only [Set.mem_ofPred_eq]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      ((N : ℂ)⁻¹ * (coarseResolvent F (gueCoord t y) s z).trace) mb (freshDyson F s z)
    have hmm' : ‖mb - freshDyson F s z‖ ≤ ε / 4 := by rw [norm_sub_rev]; exact hmm
    have : ε / 4 ≤ ‖(N : ℂ)⁻¹ * (coarseResolvent F (gueCoord t y) s z).trace - mb‖ := by
      linarith
    exact this
  refine (measure_mono hsub).trans ?_
  refine (hfl p hp1 N hNpos F hF s hspos.le z hηpos (ε / 4) (by positivity)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  -- real arithmetic for the tail
  set base := C₂ * Real.sqrt p * (Real.sqrt s * (N : ℝ)⁻¹ * (η ^ 2)⁻¹) / (ε / 4) with hbase
  have hbase0 : 0 ≤ base := by positivity
  set Y := (N : ℝ) ^ (-(97 / 150 : ℝ)) with hYdef
  have hbaseY : base ≤ 4 * C₂ * Real.sqrt p * Y := by
    have hη2 : (η ^ 2)⁻¹ ≤ X ^ 2 := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hηinv 2
    have hYeq : X ^ 2 * (N : ℝ)⁻¹ / ε = Y := by
      rw [hXpow 2, hεdef, hYdef, ← Real.rpow_neg_one, div_eq_mul_inv, ← Real.rpow_neg hNr.le,
        neg_neg, ← Real.rpow_add hNr, ← Real.rpow_add hNr]
      norm_num
    calc base = 4 * C₂ * Real.sqrt p * (Real.sqrt s * ((η ^ 2)⁻¹ * (N : ℝ)⁻¹ / ε)) := by
          rw [hbase]; field_simp
      _ ≤ 4 * C₂ * Real.sqrt p * (1 * (X ^ 2 * (N : ℝ)⁻¹ / ε)) := by
          gcongr
      _ = 4 * C₂ * Real.sqrt p * Y := by rw [one_mul, hYeq]
  have hpow : base ^ p ≤ (4 * C₂ * Real.sqrt p) ^ p * Y ^ p := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
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
  calc base ^ p ≤ (4 * C₂ * Real.sqrt p) ^ p * Y ^ p := hpow
    _ ≤ (N : ℝ) * (N : ℝ) ^ (-(D'' + 1)) := by
        rw [hYp]; exact mul_le_mul_of_nonneg_right hKc (by positivity)
    _ ≤ (N : ℝ) ^ (-D') := hND

end BlockBand.Palm.CoarseRelative
