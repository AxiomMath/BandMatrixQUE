module

public import BlockBand.Palm.MomentFlow.MultiColIto
public import BlockBand.Palm.MomentFlow.MultiRowAny

/-!
# Column form: `r`-particle finite speed, quantitative, from any start

`multi_col_any`: for the short moment flow started from `δ_{ξ₀}` at any time `s ≥ a`, with an
event `G` on which the long-gap clauses and a uniform gap hold on `[s,u]` and the far matching
weights are at most `δ₀`, the probability that the mass at time `u` outside the matching ball of
radius `rR` exceeds `e` is bounded explicitly, through the reciprocal matching weight and the
stopped Itô formula.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N : ℕ}

/-- **`r`-particle finite speed in the matching distance, column form, any start `a ≤ s`.** -/
theorem multi_col_any (r : ℕ) (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s u : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hsu : s ≤ u)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {ξ₀ : Occ N} (hξ₀ : ξ₀ ∈ sector N r) {x : Fin r → Fin N}
    (hx : x ∈ labs r ξ₀) (R : ℝ)
    {E r₀ ν d R₀ c₁ C₁ g K δ₀ e : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR₀ : 0 < R₀)
    (hρ : d + 2 * R₀ ≤ r₀ / 16) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hg : 0 < g) (hK0 : 0 ≤ K)
    (hK : (r * (2 * ℓ * (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) +
          (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N)) +
        r ^ 2 * ((ν * weightConst) ^ 2 *
          (Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ^ 2 + 1)) / (2 * N)) +
        r * (2 * ℓ + r) * (ν * weightConst) ^ 2 *
          Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ^ 3 / N +
        r ^ 2 * (ν * weightConst) ^ 2 / N ≤ K)
    (hδ₀ : 0 < δ₀) (he : 0 < e) (G : Set (FlowSample N))
    (hG : ∀ ω ∈ G, (∀ k : Fin N, 0 < ξ₀ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) →
      ω.1.IsHermitian ∧
      (∀ σ ∈ Icc s u,
        (∀ i j : Fin N, ℓ ≤ labelDist i j →
          c₁ * labelDist i j / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) ∧
        (∀ i j : Fin N, labelDist i j < ℓ →
          min |flowEigenvalue F a ω σ i - E| |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 →
          |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| ≤ C₁ * ℓ / N) ∧
        (∀ i j : Fin N, i ≠ j → g < |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)) ∧
      (∀ ζ ∈ sector N r, (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) →
        permW (rlPhi ν 0 d R₀) (flowEigenvalue F a ω u)
          (fun m => flowEigenvalue F a ω s (x m)) ζ ≤ δ₀)) :
    flowLaw N a {ω | (∀ k : Fin N, 0 < ξ₀ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if ζ = ξ₀ then 1 else 0) ∧
          e < ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist ξ₀ ζ : ℝ)), Φ u ζ} ≤
      flowLaw N a Gᶜ + ENNReal.ofReal (δ₀ / (Real.exp (-(K * (u - s))) * e)) := by
  classical
  set μ := flowLaw N a with hμ
  have hr₀ : 0 ≤ r₀ := by linarith
  set sL : ℝ≥0 := Real.toNNReal (s - a) with hsLdef
  set T : ℝ≥0 := Real.toNNReal (u - s) with hTdef
  have hsL : (sL : ℝ) = s - a := Real.coe_toNNReal _ (by linarith)
  have hT : (T : ℝ) = u - s := Real.coe_toNNReal _ (by linarith)
  set φ := rlPhi ν 0 d R₀ with hφdef
  have hφc : Continuous φ := (rlPhi_contDiff hd hR₀).continuous
  have hφp : ∀ z, 0 < φ z := fun z => rlPhi_pos z
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (rlPhi_pos z).le
  set σe := sectorEnum N r with hσe
  set farD : Occ N → Prop := fun ζ => (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) with hfarD
  obtain ⟨wt, hwt⟩ : ∃ wt : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ,
      wt = fun q lam c => (permW φ lam c (σe q))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf : (Fin N → ℝ) → Fin r → ℝ,
      Cf = fun lam m => clampC E r₀ (lam (x m)) := ⟨_, rfl⟩
  obtain ⟨Vf, hVf⟩ : ∃ Vf : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ,
      Vf = fun lam q => if σe q = ξ₀ ∧ (permW φ lam (Cf lam) ξ₀)⁻¹ ≤ 1 then 1 else 0 :=
    ⟨_, rfl⟩
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : FlowSample N → Fin r → ℝ,
      c₀ = fun ω => Cf (flowLam F sL ω) := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : FlowSample N → Fin (sectorCard N r) → ℝ,
      v₀ = fun ω => Vf (flowLam F sL ω) := ⟨_, rfl⟩
  set ρ := flowStop F sL ℓ E r₀ c₁ C₁ g with hρdef
  set Kc := Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) with hKc
  -- measurability at the start
  have hlam0 : Measurable[shiftFiltration (flowFiltration N) sL 0] (flowLam F (sL + 0)) :=
    flowLam_adapted F (sL + 0)
  have hle0 : flowFiltration N sL ≤ shiftFiltration (flowFiltration N) sL 0 :=
    (flowFiltration N).mono (le_of_eq (add_zero sL).symm)
  have hCm : Measurable Cf := by
    rw [hCf]
    exact measurable_pi_iff.mpr fun m =>
      (continuous_clampC E r₀).measurable.comp (measurable_pi_apply (x m))
  have hCc : Continuous Cf := by
    rw [hCf]
    exact continuous_pi fun m => (continuous_clampC E r₀).comp (continuous_apply (x m))
  have hVm : Measurable Vf := by
    rw [hVf]
    refine measurable_pi_iff.mpr fun q => Measurable.ite ?_ measurable_const measurable_const
    by_cases hq : σe q = ξ₀
    · simp only [hq, true_and]
      have hc1 : Continuous fun z : (Fin N → ℝ) × (Fin r → ℝ) => permW φ z.1 z.2 ξ₀ :=
        (permW_contDiff (N := N) (r := r) (φ := φ) (rlPhi_contDiff hd hR₀) ξ₀).continuous
      have hc2 : Continuous fun lam : Fin N → ℝ => (lam, Cf lam) := continuous_id.prodMk hCc
      have hc3 := hc1.comp hc2
      have hc : Continuous fun lam : Fin N → ℝ => permW φ lam (Cf lam) ξ₀ := hc3
      exact measurableSet_le (hc.measurable.inv) measurable_const
    · simp only [hq, false_and, Set.ofPred_false]; exact MeasurableSet.empty
  have hV01 : ∀ lam q, 0 ≤ Vf lam q ∧ Vf lam q ≤ 1 := by
    intro lam q
    rw [hVf]; dsimp only
    split_ifs <;> norm_num
  have hc₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] c₀ := by
    rw [hc₀def]; exact (hCm.comp (flowLam_adapted F sL)).mono hle0 le_rfl
  have hv₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] v₀ := by
    rw [hv₀def]; exact (hVm.comp (flowLam_adapted F sL)).mono hle0 le_rfl
  have hv₀ : ∀ ω q, 0 ≤ v₀ ω q ∧ v₀ ω q ≤ 1 := fun ω q => by rw [hv₀def]; exact hV01 _ q
  have hwcd : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => wt q z.1 z.2) :=
    fun q => by rw [hwt]; exact invW_contDiff (rlPhi_contDiff hd hR₀) hφp (sectorEnum_mem r q)
  -- the weight bound and the drift hypothesis
  set m₀ : ℝ := Real.exp (-(2 * ν * R₀)) with hm₀
  have hm₀p : 0 < m₀ := Real.exp_pos _
  set Wm : ℝ := (m₀ ^ r)⁻¹ with hWm
  have hWm0 : 0 ≤ Wm := by positivity
  have hw0 : ∀ q lam c, 0 ≤ wt q lam c := fun q lam c => by
    rw [hwt]; exact inv_nonneg.2 (permW_pos hφp lam c (sectorEnum_mem r q)).le
  have hwM : ∀ q lam c, wt q lam c ≤ Wm := by
    intro q lam c
    rw [hwt, hWm]
    exact inv_anti₀ (by positivity) (permW_ge_pow hm₀p.le (fun z => rlPhi_ge_exp hν hR₀ z) lam c
      (sectorEnum_mem r q))
  have hcomp : ∀ x' z, |z - x'| ≤ 2 * C₁ * ℓ / N → φ z ≤ Kc * φ x' := by
    intro x' z hxz
    refine (rlPhi_le_exp_mul hν hd hR₀ x' z).trans
      (mul_le_mul_of_nonneg_right ?_ (rlPhi_pos x').le)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxz
      (mul_nonneg hν weightConst_pos.le))
  have hdet : ∀ lam lam0 : Fin N → ℝ, lam ∉ stopSet N ℓ E r₀ c₁ C₁ g →
      ∀ vv : Fin (sectorCard N r) → ℝ, (∀ q, 0 ≤ vv q) →
      ∑ q, wt q lam (Cf lam0) * ∑ q', cfgMat (cfgRate N lam ℓ g) r q q' * vv q' +
        ∑ q, vv q * ∑ i, (dysonDrift N lam i *
          (-(permF1 φ (rlPhi1 ν 0 d R₀) lam (Cf lam0) (σe q) i) /
            permW φ lam (Cf lam0) (σe q) ^ 2) +
          (-(permF2 φ (rlPhi1 ν 0 d R₀) (rlPhi2 ν 0 d R₀) lam (Cf lam0) (σe q) i) /
              permW φ lam (Cf lam0) (σe q) ^ 2 +
            2 * permF1 φ (rlPhi1 ν 0 d R₀) lam (Cf lam0) (σe q) i ^ 2 /
              permW φ lam (Cf lam0) (σe q) ^ 3) / (2 * N)) ≤
      K * ∑ q, wt q lam (Cf lam0) * vv q := by
    intro lam lam0 hlam vv hvv
    simp only [stopSet, Set.mem_union, not_or] at hlam
    obtain ⟨h1, h2⟩ := relaxed_of_not_mem_failSet hlam.1
    have h3 : ∀ i j : Fin N, i ≠ j → g ≤ |lam i - lam j| := by
      intro i j hij
      by_contra hlt
      push Not at hlt
      exact hlam.2 ⟨i, j, hij, hlt.le⟩
    have hrate : cfgRate N (lam) ℓ g = cfgRate N (lam) ℓ 0 :=
      cfgRate_eq_zero_gap hg.le h3
    have hsh : ∀ m k l, l ≠ k → labelDist k l < ℓ →
        |lam l - lam k| ≤ 2 * C₁ * ℓ / N ∨
          (rlPhi1 ν 0 d R₀ (lam k - Cf lam0 m) = 0 ∧
            φ (lam l - Cf lam0 m) = φ (lam k - Cf lam0 m)) := by
      intro m k l hlk hd'
      have hcl : |Cf lam0 m - E| ≤ r₀ / 16 := by
        rw [hCf]; exact abs_clampC_sub_le hr₀ _
      have hh := rlPhi_short_close_or_flat (ν := ν) (E := 0) (d := d) (R := R₀) (r₀ := r₀ / 2)
        (G := 2 * C₁ * ℓ / N) hR₀ (by linarith)
        (fun l => lam l - Cf lam0 m) ℓ (fun i j hij hm => by
          have hdiff : (lam i - Cf lam0 m) - (lam j - Cf lam0 m) =
              lam i - lam j := by ring
          rw [hdiff]
          refine h2 i j hij ?_
          simp only [sub_zero] at hm
          rcases min_le_iff.1 hm with hm | hm
          · refine (min_le_left _ _).trans ?_
            calc |lam i - E|
                ≤ |lam i - Cf lam0 m| + |Cf lam0 m - E| := abs_sub_le _ _ _
              _ ≤ r₀ / 2 / 8 + r₀ / 16 := add_le_add hm hcl
              _ = r₀ / 8 := by ring
          · refine (min_le_right _ _).trans ?_
            calc |lam j - E|
                ≤ |lam j - Cf lam0 m| + |Cf lam0 m - E| := abs_sub_le _ _ _
              _ ≤ r₀ / 2 / 8 + r₀ / 16 := add_le_add hm hcl
              _ = r₀ / 8 := by ring) k l hlk hd'
      rcases hh with hh | hh
      · left; simpa only [sub_sub_sub_cancel_right] using hh
      · exact Or.inr hh
    have hQ := inv_Q_le (lam) ℓ r (Cf lam0) vv hvv
      (rlPhi_hasDerivAt hd hR₀) (rlPhi1_hasDerivAt hd hR₀) hφp (abs_rlPhi1_le hν hd hR₀)
      (mul_nonneg hν weightConst_pos.le) (abs_rlPhi2_le hν hd hR₀)
      (by have := weightConst_pos; positivity) (Real.exp_pos _) hcomp (half_pos hc₁) hsh
      (fun k l _ hkl => h1 k l hkl)
    rw [hwt]; simp only [hrate]
    exact hQ.trans (mul_le_mul_of_nonneg_right hK (Finset.sum_nonneg fun q _ =>
      mul_nonneg (inv_nonneg.2 (permW_pos hφp _ _ (sectorEnum_mem r q)).le) (hvv q)))
  have hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => wt q (fun m => lam m + if m = i then s else 0) c)
      (-(permF1 φ (rlPhi1 ν 0 d R₀) lam c (σe q) i) / permW φ lam c (σe q) ^ 2) 0 :=
    fun q lam c i => by
      rw [hwt]
      exact hasDerivAt_invW_line (rlPhi_hasDerivAt hd hR₀) hφp lam c (sectorEnum_mem r q) i
  have hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => -(permF1 φ (rlPhi1 ν 0 d R₀) (fun m => lam m + if m = i then s else 0) c
          (σe q) i) / permW φ (fun m => lam m + if m = i then s else 0) c (σe q) ^ 2)
      (-(permF2 φ (rlPhi1 ν 0 d R₀) (rlPhi2 ν 0 d R₀) lam c (σe q) i) /
          permW φ lam c (σe q) ^ 2 +
        2 * permF1 φ (rlPhi1 ν 0 d R₀) lam c (σe q) i ^ 2 / permW φ lam c (σe q) ^ 3) 0 :=
    fun q lam c i => hasDerivAt_invD1_line (rlPhi_hasDerivAt hd hR₀) (rlPhi1_hasDerivAt hd hR₀)
      hφp lam c (sectorEnum_mem r q) i
  have hexp0 := gen_mf_expectation_any r hIto hStop hDBM hN hF ha sL ℓ hg hCm hVm hV01
    (w := wt) hwcd hd1 hd2 hWm0 hw0 hwM hK0 hdet T
  have hexp : ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => gTilted K wt
        ((u : ℝ), gState F sL ℓ g r c₀ v₀ u ω)) ρ T ω ∂flowLaw N a ≤
      ∫ ω, gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω) ∂flowLaw N a := by
    rw [hc₀def, hv₀def]
    exact hexp0
  -- the stopped value
  set X : FlowSample N → ℝ := stoppedProcess (fun (xx : ℝ≥0) ω => gTilted K wt
      ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω)) ρ T with hXdef
  have hmass0 : ∀ ω, mfMass F sL ℓ g r v₀ 0 ω = v₀ ω := fun ω =>
    (adaptedMass_solution (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω le_rfl).1
  have hone : ∑ q : Fin (sectorCard N r), (if σe q = ξ₀ then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (sectorIndex hξ₀)]
    · rw [ite_eq_left (by rw [hσe]; exact sectorEnum_index hξ₀)]
    · intro q _ hq
      rw [ite_eq_right]
      intro h
      apply hq
      apply sectorEnum_injective r
      rw [sectorEnum_index hξ₀]; exact h
    · simp
  have hinit_pt : ∀ ω, gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω) ≤ 1 := by
    intro ω
    rw [gState, gTilted_sumVec, hmass0]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    calc ∑ q, wt q (flowLam F (sL + 0) ω) (c₀ ω) * v₀ ω q
        ≤ ∑ q : Fin (sectorCard N r), (if σe q = ξ₀ then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun q _ => by
            rw [hv₀def, hVf]
            dsimp only
            split_ifs with h1 h2
            · rw [mul_one, hwt, add_zero, hc₀def]; dsimp only; rw [h1.1]; exact h1.2
            · exact absurd h1.1 h2
            · rw [mul_zero]; norm_num
            · rw [mul_zero]
      _ = 1 := hone
  have hinit : ∫ ω, gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω) ∂μ ≤ 1 := by
    by_cases hi : Integrable (fun ω => gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω)) μ
    · calc _ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono hi (integrable_const _) hinit_pt
        _ = 1 := by simp
    · rw [integral_undef hi]; norm_num
  have hXint_le : ∫ ω, X ω ∂μ ≤ 1 := hexp.trans hinit
  -- integrability of the stopped value
  have hYc : ∀ ω, Continuous fun xx : ℝ≥0 => gState F sL ℓ g r c₀ v₀ xx ω := fun ω =>
    continuous_sumVec.comp (((flowLam_continuous hF ω).comp
      (continuous_const.add continuous_id)).prodMk (continuous_sumVec.comp
        (continuous_const.prodMk (adaptedMass_continuous (mfCoeff_continuous hN hF sL ℓ hg r)
          v₀ ω))))
  have hYa : ∀ xx, Measurable[shiftFiltration (flowFiltration N) sL xx]
      (fun ω => gState F sL ℓ g r c₀ v₀ xx ω) := by
    intro xx
    have h1 := flowLam_adapted F (sL + xx)
    have h2 := adaptedMass_measurable (shiftFiltration (flowFiltration N) sL)
      (mfCoeff_adapted hN F sL ℓ hg r) (mfCoeff_continuous hN hF sL ℓ hg r) hv₀m xx
    have h3 : Measurable[shiftFiltration (flowFiltration N) sL xx] c₀ :=
      hc₀m.mono ((shiftFiltration (flowFiltration N) sL).mono (zero_le (a := xx))) le_rfl
    exact continuous_sumVec.measurable.comp (h1.prodMk
      (continuous_sumVec.measurable.comp (h3.prodMk h2)))
  have hΦcont : Continuous (gTilted (N := N) (r := r) (M := sectorCard N r) K wt) :=
    (gTilted_contDiff hwcd).continuous
  have hΦcont : Continuous (gTilted (N := N) (r := r) (M := sectorCard N r) K wt) :=
    (gTilted_contDiff hwcd).continuous
  have hpt0 : ∀ (xx : ℝ≥0) ω, 0 ≤ gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω) := by
    intro xx ω
    rw [gState, gTilted_sumVec]
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun q _ => mul_nonneg (hw0 _ _ _)
      (mfMass_mem_unit hN hF sL ℓ hg r hv₀ xx ω q).1)
  have hptbd : ∀ (xx : ℝ≥0) ω, gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω) ≤
      sectorCard N r * Wm := by
    intro xx ω
    rw [gState, gTilted_sumVec]
    have hexp1 : Real.exp (-(K * xx)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg xx; nlinarith)
    have hs0 : 0 ≤ ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ xx ω q :=
      Finset.sum_nonneg fun q _ => mul_nonneg (hw0 _ _ _)
        (mfMass_mem_unit hN hF sL ℓ hg r hv₀ xx ω q).1
    have hs1 : ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ xx ω q ≤
        sectorCard N r * Wm := by
      calc _ ≤ ∑ _q : Fin (sectorCard N r), Wm := Finset.sum_le_sum fun q _ => by
            have hm := mfMass_mem_unit hN hF sL ℓ hg r hv₀ xx ω q
            calc _ ≤ Wm * 1 := mul_le_mul (hwM _ _ _) hm.2 hm.1 hWm0
              _ = Wm := mul_one _
        _ = _ := by simp
    calc _ ≤ 1 * ((sectorCard N r : ℝ) * Wm) := mul_le_mul hexp1 hs1 hs0 zero_le_one
      _ = _ := one_mul _
  have hXa : ∀ xx, StronglyMeasurable[shiftFiltration (flowFiltration N) sL xx]
      (fun ω => gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω)) := fun xx =>
    (hΦcont.measurable.comp (measurable_const.prodMk (hYa xx))).stronglyMeasurable
  have hXc : ∀ ω, Continuous fun xx : ℝ≥0 =>
      gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω) := fun ω =>
    hΦcont.comp (NNReal.continuous_coe.prodMk (hYc ω))
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous hXa hXc
  have hm := hprog.stronglyMeasurable_stoppedProcess
    (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g) T
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => by simp only [hXdef, stoppedProcess]; exact hpt0 _ ω
  have hXint : Integrable X μ :=
    Integrable.of_bound hm.aestronglyMeasurable ((sectorCard N r) * Wm)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
        simp only [hXdef, stoppedProcess]; exact hptbd _ ω)
  -- Markov
  set θ := Real.exp (-(K * (u - s))) * e / δ₀ with hθ
  have hθpos : 0 < θ := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hX0) hXint θ
  have hmeas : μ {ω | θ ≤ X ω} ≤ ENNReal.ofReal (1 / θ) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hθpos]
    have : θ * μ.real {ω | θ ≤ X ω} ≤ 1 := hmk.trans hXint_le
    rw [measureReal_def] at this
    linarith
  -- containment
  have hsub : {ω | (∀ k : Fin N, 0 < ξ₀ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if ζ = ξ₀ then 1 else 0) ∧
          e < ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist ξ₀ ζ : ℝ)), Φ u ζ} ⊆
      Gᶜ ∪ {ω | θ ≤ X ω} := by
    rintro ω ⟨hbulk, Φ, hΦ, hΦ0, hΦu⟩
    by_cases hωG : ω ∈ G
    swap
    · exact Or.inl hωG
    right
    obtain ⟨hH, hcl, hfarW⟩ := hG ω hωG hbulk
    have hlamS : flowLam F sL ω = flowEigenvalue F a ω s := flowLam_eq_eig F a hH has
    have hocc : ∀ m, 0 < ξ₀ (x m) := by
      intro m
      rw [← mem_labs.1 hx, ← card_filter_eq_occOf]
      exact Finset.card_pos.2 ⟨m, by simp⟩
    have hc0 : c₀ ω = fun m => flowEigenvalue F a ω s (x m) := by
      funext m
      rw [hc₀def, hCf]; simp only [hlamS]
      exact clampC_eq (hbulk _ (hocc m))
    have hlam_t : ∀ xx : ℝ≥0, flowLam F (sL + xx) ω = flowEigenvalue F a ω (s + xx) := by
      intro xx
      rw [flowLam_add_eq_eig F a hH, NNReal.coe_add, hsL]
      congr 1; ring
    have hcond : (permW φ (flowLam F sL ω) (Cf (flowLam F sL ω)) ξ₀)⁻¹ ≤ 1 := by
      have : Cf (flowLam F sL ω) = fun m => flowEigenvalue F a ω s (x m) := by
        rw [hc₀def] at hc0; exact hc0
      rw [this, hlamS]
      exact inv_le_one_of_one_le₀ (permW_start_ge_one hφ0 (rlPhi_zero hd hR₀) _ hx)
    have hρT : ¬ ρ ω ≤ T := by
      have hiff := hitTime_le_iff (X := fun xx ω => flowLam F (sL + xx) ω)
        (K := stopSet N ℓ E r₀ c₁ C₁ g) (ω := ω)
        ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))
        ((isClosed_failSet N ℓ E r₀ c₁ C₁).union (isClosed_gapSet N g)) T
      rw [hρdef, flowStop, hiff]
      rintro ⟨xx, hxT, hxs⟩
      simp only [stopSet, Set.mem_union] at hxs
      have hxT' : (xx : ℝ) ≤ u - s := by rw [← hT]; exact_mod_cast hxT
      have hσ : s + (xx : ℝ) ∈ Icc s u := ⟨by linarith [xx.2], by linarith⟩
      obtain ⟨h1, h2, h3⟩ := hcl _ hσ
      simp only [hlam_t xx] at hxs
      rcases hxs with hxs | hxs
      · exact not_mem_failSet_of_clauses hℓ hc₁ hC₁ hN h1 h2 hxs
      · obtain ⟨i, j, hij, hle⟩ := hxs
        exact absurd hle (not_le.mpr (h3 i j hij))
    have hTρ : (T : WithTop ℝ≥0) ≤ ρ ω := (lt_of_not_ge hρT).le
    have hXω : X ω = gTilted K wt ((T : ℝ), gState F sL ℓ g r c₀ v₀ T ω) := by
      simp only [hXdef, stoppedProcess, min_eq_left hTρ]
      rfl
    set Lc := mfCoeff F sL ℓ g r with hLc
    have hsol := adaptedMass_solution (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω
      (T := u - s) (by linarith)
    have hsh := forwardMass_shift_to hsol s
    have hsu' : s + (u - s) = u := by ring
    rw [hsu'] at hsh
    have hmf := isMomentFlowSolution_of_forwardMass
      (c := fun σ => cfgRate N (flowLam F (sL + Real.toNNReal (σ - s)) ω) ℓ g) hsh
    have hmf' : IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u
        (fun σ => cfgExt r (adaptedMass Lc v₀ (σ - s) ω)) := by
      refine hmf.congr_rate fun σ hσ i j hij => ?_
      have hσs : ((Real.toNNReal (σ - s) : ℝ≥0) : ℝ) = σ - s :=
        Real.coe_toNNReal _ (by linarith [hσ.1])
      have hl : flowLam F (sL + Real.toNNReal (σ - s)) ω = flowEigenvalue F a ω σ := by
        rw [hlam_t, hσs]; congr 1; ring
      show cfgRate N (flowLam F (sL + Real.toNNReal (σ - s)) ω) ℓ g i j = _
      rw [hl, shortFlowRate_eq_cfgRate F a ω ℓ σ hij]
      have hgap := (hcl σ ⟨hσ.1.le, hσ.2.le⟩).2.2
      rw [cfgRate_eq_zero_gap hg.le fun i j h => (hgap i j h).le]
    have h0 : ∀ ζ ∈ sector N r, Φ s ζ = cfgExt r (adaptedMass Lc v₀ (s - s) ω) ζ := by
      intro ζ hζ
      rw [sub_self, hΦ0 ζ hζ, cfgExt_of_mem _ hζ]
      have : adaptedMass Lc v₀ 0 ω = v₀ ω := hsol.1
      rw [this, hv₀def, hVf]
      dsimp only
      rw [hσe, sectorEnum_index hζ]
      by_cases hz : ζ = ξ₀
      · rw [ite_eq_left hz, ite_eq_left ⟨hz, hcond⟩]
      · rw [ite_eq_right hz, ite_eq_right fun h => hz h.1]
    have hval : ∀ ζ (hζ : ζ ∈ sector N r), Φ u ζ = mfMass F sL ℓ g r v₀ T ω (sectorIndex hζ) := by
      intro ζ hζ
      have heq := hΦ.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j)
        hmf' h0 u ⟨hsu, le_rfl⟩ ζ hζ
      rw [heq, cfgExt_of_mem _ hζ]
      simp only [mfMass, hT, hLc]
    have htail : ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist ξ₀ ζ : ℝ)), Φ u ζ =
        ∑ q, if (r : ℝ) * R < (occDist ξ₀ (σe q) : ℝ) then mfMass F sL ℓ g r v₀ T ω q
          else 0 := by
      rw [Finset.sum_filter, ← sum_sectorEnum r (fun ζ =>
        if (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) then Φ u ζ else 0)]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq := sectorEnum_mem r q
      have hidx : sectorIndex hq = q := sectorEnum_injective r (sectorEnum_index hq)
      rw [hval _ hq, hidx]
    have hlu : flowLam F (sL + T) ω = flowEigenvalue F a ω u := by
      rw [hlam_t T, hT]; ring_nf
    have hc0' : c₀ ω = fun m => flowEigenvalue F a ω s (x m) := hc0
    have hpt : ∀ q, (if (r : ℝ) * R < (occDist ξ₀ (σe q) : ℝ) then mfMass F sL ℓ g r v₀ T ω q
        else 0) / δ₀ ≤ wt q (flowLam F (sL + T) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ T ω q := by
      intro q
      have hm := (mfMass_mem_unit hN hF sL ℓ hg r hv₀ T ω q).1
      split_ifs with hfq
      · have hb := hfarW (σe q) (sectorEnum_mem r q) hfq
        have hp := permW_pos hφp (flowEigenvalue F a ω u)
          (fun m => flowEigenvalue F a ω s (x m)) (sectorEnum_mem r q)
        have hwq : 1 / δ₀ ≤ wt q (flowLam F (sL + T) ω) (c₀ ω) := by
          rw [hwt]; dsimp only; rw [hlu, hc0', ← one_div]
          exact one_div_le_one_div_of_le hp hb
        calc mfMass F sL ℓ g r v₀ T ω q / δ₀ = 1 / δ₀ * mfMass F sL ℓ g r v₀ T ω q := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hwq hm
      · rw [zero_div]; exact mul_nonneg (hw0 _ _ _) hm
    show θ ≤ X ω
    rw [hXω, gState, gTilted_sumVec, hT]
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset (Fin (sectorCard N r))))
      => hpt q
    rw [← Finset.sum_div, ← htail] at hsum
    have hed : e / δ₀ ≤ (∑ ζ ∈ (sector N r).filter
        (fun ζ => (r : ℝ) * R < (occDist ξ₀ ζ : ℝ)), Φ u ζ) / δ₀ :=
      div_le_div_of_nonneg_right hΦu.le hδ₀.le
    calc θ = Real.exp (-(K * (u - s))) * (e / δ₀) := by rw [hθ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hed.trans hsum) (Real.exp_pos _).le
  calc μ _ ≤ μ (Gᶜ ∪ {ω | θ ≤ X ω}) := measure_mono hsub
    _ ≤ μ Gᶜ + μ {ω | θ ≤ X ω} := measure_union_le _ _
    _ ≤ μ Gᶜ + ENNReal.ofReal (1 / θ) := add_le_add le_rfl hmeas
    _ = _ := by rw [hθ]; congr 2; field_simp

end BlockBand.Palm.MomentFlow
