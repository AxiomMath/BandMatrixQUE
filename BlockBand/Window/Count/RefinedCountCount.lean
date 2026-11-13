module

public import BlockBand.Window.Count.RefinedCount
public import BlockBand.Window.Count.SharperFreshCount
public import BlockBand.Window.Count.RingFreshBlock

/-!
# The refined count: count clause

Under the physical law, `‖N_H(e) - N F_sc(e)‖_q ≤ C_q a_{n,W}` uniformly in `n ≤ TW`, the
realization and `e ∈ bulkInterval κ`, with `a_{n,W} = √n + n/W + W^{2/5} log(2W)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

set_option maxHeartbeats 1600000 in
/-- The count clause of the refined count. Physical law `model.law`; `b, κ, T, q ≥ 1` first,
then `C_q`; for every admissible `p` with `p.b = b`, `n ≤ TW`, every realization and every
deterministic `e ∈ bulkInterval κ`: `‖N_H(e) - N F_sc(e)‖_q ≤ C_q a_{n,W}`. No lower bound on
`n/W`. Dependencies: `RingFreshBlockSplitAE` (the almost-sure fresh-block split, proved as
`ringFreshBlockSplitAE`; the everywhere form `RingFreshBlockSplit` cannot hold: its transport
clauses fail at non-Hermitian `H`),
`SharperFreshCountStatement`, `MatchedTracesContract.commonPort`,
`RingCompensatedPhaseContract.fluctuation`, `RankLocationContract.count_mean` and
`.count_moment`, `FreshCountContract.mean`. -/
theorem refinedCount_count_of (hSplit : RingFreshBlockSplitAE)
    (hSharp : SharperFreshCountStatement) (hMT : MatchedTracesContract)
    (hRing : RingCompensatedPhaseContract) (hRank : RankLocationContract)
    (hFresh : FreshCountContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : BlockBand.Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (e : ℝ), e ∈ bulkInterval κ →
      eLpNorm (fun H => (physicalCount p H e : ℝ) - p.N * semicircleCDF e) (ENNReal.ofReal q)
          (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal (Cq * countScale p.n p.W) := by
  intro b hb hb' κ T hκ q hq
  obtain ⟨Cr, hCr⟩ := hRing.fluctuation b hb hb' κ T hκ q hq
  obtain ⟨Cm, hCm⟩ := hRank.count_mean b hb hb' κ T hκ
  obtain ⟨Ck, hCk⟩ := hRank.count_moment b hb hb' κ T hκ q hq
  obtain ⟨ε₀, CT, hε₀, hCT⟩ := hMT.commonPort b hb hb' κ T hκ
  obtain ⟨dstar, CF, hds, hCF⟩ := hFresh.mean b hb hb' κ hκ
  obtain ⟨Cs, hCs⟩ := hSharp (1 - 2 * b) (by linarith) q hq
  set W₀ : ℝ := 2 * q / ε₀ with hW₀
  set Cr' := max Cr 0
  set Ck' := max Ck 0
  set Cm' := max Cm 0
  set CF' := max CF 0
  set Cs' := max Cs 0
  set CT' := max CT 0
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Cfl : ℝ := 2 * (Cr' + Cs' / Real.log 2 + (CF' + 3 / dstar ^ 2) * CT' ^ 2 * (2 * q) + CF')
  have hCfl : 0 ≤ Cfl := by positivity
  refine ⟨Ck' * Real.sqrt W₀ + Cfl + Cm', ?_⟩
  intro p hpb hpT model e he
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix) with hμ
  have ha1 := one_le_countScale p
  have hE2 := abs_le_two_of_mem_bulk hκ he
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hNHm : Measurable (fun H : p.SiteMatrix => (physicalCount p H e : ℝ)) :=
    measurable_negativeCount_real.comp (measurable_id.sub_const _)
  by_cases hWs : (p.W : ℝ) < W₀
  · have h := hCk p hpb hpT model .physical e he
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Ck * Real.sqrt p.W ≤ Ck' * Real.sqrt W₀ :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hWs.le) (le_max_right _ _))
    have h2 : 0 ≤ Ck' * Real.sqrt W₀ := mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
    have h3 : 0 ≤ Cm' := le_max_right _ _
    nlinarith
  have hWbig : W₀ ≤ p.W := not_lt.mp hWs
  have hpc : p.c = 1 - 2 * b := by simp [BlockBand.Parameters.c, hpb]
  obtain ⟨Sg, Af, hSgm, hAfm, hSgH, hschur, hphase, htrace, hlaw⟩ := hSplit p model 0 e
  set γ : Measure (Matrix (Fin p.W) (Fin p.W) ℂ) :=
    gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * b) / p.W)) with hγ
  have hγp : gueMeasure (Fin p.W) (Real.toNNReal (p.c / p.W)) = γ := by rw [hpc]
  rw [hγp] at hlaw
  have : IsProbabilityMeasure γ := isProbabilityMeasure_gueMeasure' _
  set ν := μ.map Sg with hν
  have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- the fresh count, its conditional mean, and the centered fresh count
  set nf : Matrix (Fin p.W) (Fin p.W) ℂ × Matrix (Fin p.W) (Fin p.W) ℂ → ℝ :=
    fun z => (negativeCount (z.2 - (e : ℂ) • 1 - z.1) : ℝ) with hnf
  have hsubm : Measurable (fun z : Matrix (Fin p.W) (Fin p.W) ℂ × Matrix (Fin p.W) (Fin p.W) ℂ =>
      z.2 - (e : ℂ) • 1 - z.1) := by
    have hent : ∀ a b', Measurable (fun M : Matrix (Fin p.W) (Fin p.W) ℂ => M a b') :=
      fun a b' => measurable_pi_iff.mp (measurable_pi_iff.mp measurable_id a) b'
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b' => ?_
    simp only [Matrix.sub_apply]
    exact (((hent a b').comp measurable_snd).sub_const _).sub ((hent a b').comp measurable_fst)
  have hnfm : Measurable nf := measurable_negativeCount_real.comp hsubm
  set mS : Matrix (Fin p.W) (Fin p.W) ℂ → ℝ := fun S => ∫ A, nf (S, A) ∂γ with hmS
  have hmSm : Measurable mS := (hnfm.stronglyMeasurable.integral_prod_right' (ν := γ)).measurable
  set zf : Matrix (Fin p.W) (Fin p.W) ℂ × Matrix (Fin p.W) (Fin p.W) ℂ → ℝ :=
    fun z => if z.1.IsHermitian then nf z - mS z.1 else 0 with hzf
  have hzfm : Measurable zf :=
    Measurable.ite (measurableSet_isHermitian.preimage measurable_fst)
      (hnfm.sub (hmSm.comp measurable_fst)) measurable_const
  set Θ : Matrix (Fin p.W) (Fin p.W) ℂ → ℝ := fun S => phaseCount (commonZ p.b e) S
  set κ0 : ℝ := (1 - 2 * b) * p.W / (2 * Real.pi) * (matchedA e ^ 2).im with hκ0
  set Mf : Matrix (Fin p.W) (Fin p.W) ℂ → ℝ := fun S => mS S - Θ S - κ0 with hMf
  set Ξ : p.SiteMatrix → ℝ := fun H => ringCompensatedPhase p 0 H e with hΞ
  set K : ℝ := (∫ H, Ξ H ∂μ) + κ0 with hK
  -- a.s. decomposition
  have hdec : (fun H => (physicalCount p H e : ℝ) - K) =ᵐ[μ]
      fun H => ((Ξ H - ∫ H', Ξ H' ∂μ) + zf (Sg H, Af H)) + Mf (Sg H) := by
    filter_upwards [hschur, hphase] with H hH hphH
    have hzH : zf (Sg H, Af H) = nf (Sg H, Af H) - mS (Sg H) := by
      simp only [hzf, hSgH H, ↓reduceIte]
    have hnfH : nf (Sg H, Af H) = (negativeCount (Af H - (e : ℂ) • 1 - Sg H) : ℝ) := rfl
    show (physicalCount p H e : ℝ) - K =
      ((Ξ H - ∫ H', Ξ H' ∂μ) + zf (Sg H, Af H)) + (mS (Sg H) - Θ (Sg H) - κ0)
    rw [hH, hzH, hnfH, hK, hphH]; ring
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  set u : ℝ := (p.W : ℝ) ^ (1 / 3 : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  -- (Ξ) the compensated phase
  have hΞb := hCr p hpb hpT model 0 e he
  -- (Z) the fresh fluctuation
  have hZ : eLpNorm (fun H => zf (Sg H, Af H)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cs' * u) := by
    have hmap : eLpNorm (fun H => zf (Sg H, Af H)) (ENNReal.ofReal q) μ =
        eLpNorm zf (ENNReal.ofReal q) (μ.map (fun H => (Sg H, Af H))) :=
      (eLpNorm_map_measure hzfm.aestronglyMeasurable (hSgm.prodMk hAfm).aemeasurable).symm
    rw [hmap, hlaw]
    refine eLpNorm_prod_le_of_slices ν γ zf hzfm.aestronglyMeasurable hq fun S => ?_
    by_cases hS : S.IsHermitian
    · have h := hCs p.W p.W_pos (-S) hS.neg e
      simp only at h
      have hfun : (fun y => zf (S, y)) = fun A =>
          (negativeCount (A + -S - (e : ℂ) • 1) : ℝ) -
            ∫ A', (negativeCount (A' + -S - (e : ℂ) • 1) : ℝ) ∂γ := by
        funext y
        have hr : ∀ A : Matrix (Fin p.W) (Fin p.W) ℂ, A + -S - (e : ℂ) • 1 = A - (e : ℂ) • 1 - S :=
          fun A => by abel
        simp only [hzf, hS, ↓reduceIte, hnf, hmS, hr]
      rw [hfun]
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu0
    · have hfun : (fun y => zf (S, y)) = fun _ => (0 : ℝ) := by
        funext y; simp only [hzf, hS, ↓reduceIte]
      rw [hfun, eLpNorm_fun_zero]; exact zero_le
  -- (M) the predictable fresh-mean error
  set D : p.SiteMatrix → ℝ := fun H =>
    ‖oneBlockTrace p 0 ((commonZ p.b e • 1 - oneBlockComplement p 0 H e)⁻¹) - matchedA e‖ with hD
  set δ : ℝ := CT' * Real.sqrt (2 * q) / p.W with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have h2q : 2 * q ≤ ε₀ * p.W := by
    have := hWbig; rw [hW₀, div_le_iff₀ hε₀] at this; linarith
  have hDq : eLpNorm D (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal δ := by
    have h := hCT p hpb hpT model 0 e he (2 * q) (by linarith) h2q
    rw [← hpb] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (by positivity)
  have hDm : AEStronglyMeasurable D μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDq)
  set L : ℝ := (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) with hL
  have hL0 : 0 ≤ L := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  set A : ℝ := (CF' + 3 / dstar ^ 2) * p.W with hA
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ CF' * L := mul_nonneg (le_max_right _ _) hL0
  have hMpt : ∀ᵐ H ∂μ, |Mf (Sg H)| ≤ A * D H ^ 2 + CF' * L := by
    filter_upwards [htrace] with H htrH
    have hDH : D H = ‖(p.W : ℂ)⁻¹ * ((commonZ p.b e • 1 - Sg H)⁻¹).trace - matchedA e‖ := by
      simp only [hD]; rw [htrH]
    have hD0 : 0 ≤ D H := norm_nonneg _
    by_cases hdd : D H ≤ dstar
    · have h := hCF p.W p.W_pos (Sg H) (hSgH H) e he
      simp only at h
      rw [← commonZ_eq b hE2, show commonZ b e = commonZ p.b e by rw [hpb], ← hDH] at h
      have h' := h hdd
      have hMeq : Mf (Sg H) = (∫ A, (negativeCount (A - (e : ℂ) • 1 - Sg H) : ℝ) ∂γ) -
          phaseCount (commonZ p.b e) (Sg H) - (1 - 2 * b) * p.W / (2 * Real.pi) *
            (matchedA e ^ 2).im := rfl
      rw [hMeq]
      calc _ ≤ CF * (p.W * D H ^ 2 + L) := h'
        _ ≤ CF' * (p.W * D H ^ 2 + L) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ A * D H ^ 2 + CF' * L := by
            have : CF' * p.W * D H ^ 2 ≤ A * D H ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              rw [hA]; apply mul_le_mul_of_nonneg_right _ (by positivity)
              have : 0 ≤ 3 / dstar ^ 2 := by positivity
              linarith
            nlinarith
    · have hdd' : dstar < D H := lt_of_not_ge hdd
      have hm : |mS (Sg H)| ≤ p.W := by
        have := norm_integral_le_of_norm_le_const (μ := γ) (f := fun A => nf (Sg H, A))
          (C := (p.W : ℝ)) (Filter.Eventually.of_forall fun A => by
            show ‖(negativeCount (A - (e : ℂ) • 1 - Sg H) : ℝ)‖ ≤ p.W
            rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
            have h0 := negativeCount_le_card (A - (e : ℂ) • 1 - Sg H)
            rwa [Fintype.card_fin] at h0)
        simpa [Real.norm_eq_abs] using this
      have hθ : |Θ (Sg H)| ≤ p.W := by simpa using abs_phaseCount_le (commonZ p.b e) (Sg H)
      have hk : |κ0| ≤ p.W := by
        rw [hκ0, abs_mul, abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - 2 * b),
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Nat.abs_cast]
        have hi := norm_matchedA_sq_im_le hE2
        have h1 : (1 - 2 * b) * (p.W : ℝ) / (2 * Real.pi) ≤ p.W := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_gt_three]
        calc _ ≤ (1 - 2 * b) * (p.W : ℝ) / (2 * Real.pi) * 1 :=
              mul_le_mul_of_nonneg_left hi
                (div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (by positivity))
          _ ≤ p.W := by linarith
      have h3 : |Mf (Sg H)| ≤ 3 * p.W := by
        have : Mf (Sg H) = mS (Sg H) - Θ (Sg H) - κ0 := rfl
        rw [this]
        calc _ ≤ |mS (Sg H)| + |Θ (Sg H)| + |κ0| := by
              have := abs_sub (mS (Sg H) - Θ (Sg H)) κ0
              have := abs_sub (mS (Sg H)) (Θ (Sg H))
              linarith
          _ ≤ 3 * p.W := by linarith
      have hratio : 1 ≤ D H ^ 2 / dstar ^ 2 := by
        rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ hds.le hdd'.le 2
      calc |Mf (Sg H)| ≤ 3 * p.W := h3
        _ ≤ 3 * p.W * (D H ^ 2 / dstar ^ 2) := le_mul_of_one_le_right (by positivity) hratio
        _ = (3 / dstar ^ 2) * p.W * D H ^ 2 := by ring
        _ ≤ A * D H ^ 2 + CF' * L := by
            have : (3 / dstar ^ 2) * p.W * D H ^ 2 ≤ A * D H ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              rw [hA]; apply mul_le_mul_of_nonneg_right _ (by positivity)
              have : 0 ≤ CF' := le_max_right _ _
              linarith
            linarith
  have hΞm : AEStronglyMeasurable (fun H => Ξ H - ∫ H', Ξ H' ∂μ) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΞb)
  have hZm : AEStronglyMeasurable (fun H => zf (Sg H, Af H)) μ :=
    (hzfm.comp (hSgm.prodMk hAfm)).aestronglyMeasurable
  have hMm : AEStronglyMeasurable (fun H => Mf (Sg H)) μ := by
    refine (((hNHm.sub_const K).aestronglyMeasurable.sub hΞm).sub hZm).congr ?_
    filter_upwards [hdec] with H hH
    simp only [Pi.sub_apply] at hH ⊢
    linarith
  have hMb := eLpNorm_le_of_sq_bound μ (fun H => Mf (Sg H)) D hDm hMm (fun H => norm_nonneg _)
    hq hA0 hB0 hδ0 hMpt hDq
  have hΞb' : eLpNorm (fun H => Ξ H - ∫ H', Ξ H' ∂μ) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cr' * Real.sqrt p.n) :=
    hΞb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  have hNK : eLpNorm (fun H => (physicalCount p H e : ℝ) - K) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cr' * Real.sqrt p.n) + ENNReal.ofReal (Cs' * u) +
        ENNReal.ofReal (A * δ ^ 2 + CF' * L) := by
    rw [eLpNorm_congr_ae hdec]
    calc _ ≤ eLpNorm (fun H => (Ξ H - ∫ H', Ξ H' ∂μ) + zf (Sg H, Af H)) (ENNReal.ofReal q) μ +
          eLpNorm (fun H => Mf (Sg H)) (ENNReal.ofReal q) μ := eLpNorm_add_le hp1
      _ ≤ (eLpNorm (fun H => Ξ H - ∫ H', Ξ H' ∂μ) (ENNReal.ofReal q) μ +
            eLpNorm (fun H => zf (Sg H, Af H)) (ENNReal.ofReal q) μ) +
          eLpNorm (fun H => Mf (Sg H)) (ENNReal.ofReal q) μ := by
          gcongr; exact eLpNorm_add_le hp1
      _ ≤ _ := by gcongr
  -- centering
  have hint : Integrable (fun H : p.SiteMatrix => (physicalCount p H e : ℝ)) μ := by
    refine Integrable.of_bound hNHm.aestronglyMeasurable (Fintype.card p.Site : ℝ)
      (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact negativeCount_le_card _
  have hcent : eLpNorm (fun H => (physicalCount p H e : ℝ) - ∫ H', (physicalCount p H' e : ℝ) ∂μ)
      (ENNReal.ofReal q) μ ≤
      2 * eLpNorm (fun H => (physicalCount p H e : ℝ) - K) (ENNReal.ofReal q) μ := by
    have h := eLpNorm_sub_integral_le μ (fun H => (physicalCount p H e : ℝ) - K) hq
    have hI : (∫ H, ((physicalCount p H e : ℝ) - K) ∂μ) =
        (∫ H, (physicalCount p H e : ℝ) ∂μ) - K := by
      rw [integral_sub hint (integrable_const K)]; simp
    rw [hI] at h
    convert h using 2
    funext H; ring
  have hmean := hCm p hpb hpT model .physical e he
  change |(∫ H, (physicalCount p H e : ℝ) ∂μ) - p.N * semicircleCDF e| ≤ _ at hmean
  set Lm : ℝ := (p.n : ℝ) / p.W + (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) with hLm
  have hLm0 : 0 ≤ Lm := add_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hL0
  have hconst : eLpNorm (fun _ : p.SiteMatrix =>
      (∫ H, (physicalCount p H e : ℝ) ∂μ) - p.N * semicircleCDF e) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cm' * Lm) := by
    rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hmean.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hLm0))
  have hsplit : (fun H => (physicalCount p H e : ℝ) - p.N * semicircleCDF e) = fun H =>
      ((physicalCount p H e : ℝ) - ∫ H', (physicalCount p H' e : ℝ) ∂μ) +
        ((∫ H, (physicalCount p H e : ℝ) ∂μ) - p.N * semicircleCDF e) := by
    funext H; ring
  have hCr0 : 0 ≤ Cr' := le_max_right _ _
  have hCs0 : 0 ≤ Cs' := le_max_right _ _
  have hCm0 : 0 ≤ Cm' := le_max_right _ _
  have hCF0 : 0 ≤ CF' := le_max_right _ _
  have h1 : 0 ≤ Cr' * Real.sqrt p.n := mul_nonneg hCr0 (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Cs' * u := mul_nonneg hCs0 hu0
  have h3 : 0 ≤ A * δ ^ 2 + CF' * L := add_nonneg (mul_nonneg hA0 (sq_nonneg _)) hB0
  have h4 : 0 ≤ Cm' * Lm := mul_nonneg hCm0 hLm0
  rw [hsplit]
  calc _ ≤ eLpNorm (fun H => (physicalCount p H e : ℝ) - ∫ H', (physicalCount p H' e : ℝ) ∂μ)
          (ENNReal.ofReal q) μ +
        eLpNorm (fun _ : p.SiteMatrix =>
          (∫ H, (physicalCount p H e : ℝ) ∂μ) - p.N * semicircleCDF e) (ENNReal.ofReal q) μ :=
        eLpNorm_add_le hp1
    _ ≤ 2 * (ENNReal.ofReal (Cr' * Real.sqrt p.n) + ENNReal.ofReal (Cs' * u) +
          ENNReal.ofReal (A * δ ^ 2 + CF' * L)) + ENNReal.ofReal (Cm' * Lm) := by
        gcongr
        exact hcent.trans (by gcongr)
    _ = ENNReal.ofReal (2 * (Cr' * Real.sqrt p.n + Cs' * u + (A * δ ^ 2 + CF' * L)) +
          Cm' * Lm) := by
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3,
          show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (add_nonneg (add_nonneg h1 h2) h3)) h4]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        set a := countScale p.n p.W with ha
        have hna : Real.sqrt p.n ≤ a := by
          rw [ha]; unfold countScale
          have : 0 ≤ (p.n : ℝ) / p.W := by positivity
          linarith
        have hua : u ≤ a / Real.log 2 := rpow_third_le_countScale p
        have hLa : L ≤ a := by
          rw [ha]; unfold countScale
          have : 0 ≤ Real.sqrt p.n + (p.n : ℝ) / p.W := by positivity
          linarith
        have hLma : Lm ≤ a := by
          rw [ha]; unfold countScale
          have : 0 ≤ Real.sqrt p.n := Real.sqrt_nonneg _
          linarith
        have hAδ : A * δ ^ 2 ≤ (CF' + 3 / dstar ^ 2) * CT' ^ 2 * (2 * q) := by
          have hWp : (0 : ℝ) < p.W := by linarith
          have heq : A * δ ^ 2 = (CF' + 3 / dstar ^ 2) * CT' ^ 2 * (2 * q) / p.W := by
            rw [hA, hδ, div_pow, mul_pow, Real.sq_sqrt (by linarith)]
            field_simp
          rw [heq]
          exact div_le_self (by positivity) hW1
        set Q : ℝ := (CF' + 3 / dstar ^ 2) * CT' ^ 2 * (2 * q) with hQ
        have hQ0 : 0 ≤ Q := mul_nonneg (mul_nonneg (add_nonneg hCF0 (div_nonneg (by norm_num)
          (sq_nonneg _))) (sq_nonneg _)) (by linarith)
        have e1 : Cr' * Real.sqrt p.n ≤ Cr' * a := mul_le_mul_of_nonneg_left hna hCr0
        have e2 : Cs' * u ≤ Cs' / Real.log 2 * a := by
          calc Cs' * u ≤ Cs' * (a / Real.log 2) := mul_le_mul_of_nonneg_left hua hCs0
            _ = Cs' / Real.log 2 * a := by ring
        have e3 : Q ≤ Q * a := le_mul_of_one_le_right hQ0 ha1
        have e4 : CF' * L ≤ CF' * a := mul_le_mul_of_nonneg_left hLa hCF0
        have e5 : Cm' * Lm ≤ Cm' * a := mul_le_mul_of_nonneg_left hLma hCm0
        have e6 : 0 ≤ Ck' * Real.sqrt W₀ * a :=
          mul_nonneg (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) (by linarith)
        have hfin : (Ck' * Real.sqrt W₀ + Cfl + Cm') * a =
            Ck' * Real.sqrt W₀ * a + 2 * (Cr' * a + Cs' / Real.log 2 * a + Q * a + CF' * a) +
              Cm' * a := by
          simp only [Cfl, hQ]; ring
        rw [hfin]
        nlinarith

end BlockBand.Window.Count
