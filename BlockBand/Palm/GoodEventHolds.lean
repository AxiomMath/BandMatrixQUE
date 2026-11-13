module

public import BlockBand.Palm.GoodEventAssembly

/-!
# Good spectral event: `SpectralGoodEventContract` and a finer-scale variant

* `spectralGoodEvent_scales θ κ` (`0 < θ`, `0 < κ < 1/100`): the six clauses of the contract at
  the scales `t = N^{-θ}`, `a = c - t`, `ℓ = ⌊N^{1-κ}⌋`, `h = N^{-1/100}`, simultaneously for all
  `s ∈ [a, c]`, outside an outer `flowLaw N a`-probability `N^{-D}`.
* `spectralGoodEvent_holds`: `SpectralGoodEventContract` (`θ = 1/500`, `κ = 13/5000`).
* `spectralGoodEvent_s8`: the variant at `θ = 1/100`, `τ = N^{-1/100}`, `a = c - τ`,
  `ℓ = ⌊N^{1-(1/100)/3}⌋`, with displacement `≤ C√τ`.

Only the Gaussian inputs `GaussianLpGradient` and `MultivariateGaussianIBP` are hypotheses
(through `coarseRelative_holds`, the coarse trace layer and the Gaussian norm tail).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Palm.CoarseRelative BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

variable {N : ℕ}

/-- The upper-mesh failure probability at one mesh time. -/
theorem upperBad_le {Cu : ℝ}
    (hUT : ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian →
      ∀ s : ℝ, 0 < s → ∀ z : ℂ, 0 < z.im →
      s * (z.im⁻¹ * z.im⁻¹) * (Cu * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹)) ≤ 1 →
        gueMeasure (Fin N) (Real.toNNReal (1 / N))
            {G | 3 + 1 / s < ((N : ℂ)⁻¹ * (coarseResolvent F G s z).trace).im} ≤
          ENNReal.ofReal ((Cu * Real.sqrt p * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹)) ^ p))
    (hCu : 0 < Cu) {p : ℝ} (hp1 : 1 ≤ p) (hN0 : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {σ h : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hh : 0 < h) (K₀ : ℕ)
    (hres : h⁻¹ * h⁻¹ * (Cu * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)) ≤ 1) :
    gueMeasure (Fin N) (Real.toNNReal (1 / N)) (upperBad F σ h K₀) ≤
      ENNReal.ofReal ((2 * (K₀ : ℝ) + 3) *
        (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)) ^ p) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set X : ℝ := (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)) ^ p with hXdef
  have hcov : upperBad F σ h K₀ ⊆ ⋃ k ∈ Finset.Icc (-((K₀ : ℤ) + 1)) ((K₀ : ℤ) + 1),
      {G | 3 + 1 / σ < ((N : ℂ)⁻¹ * (coarseResolvent F G σ ⟨(k : ℝ) * h, h⟩).trace).im} := by
    intro G hG
    obtain ⟨k, hk, hk'⟩ := hG
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc]
    exact ⟨k, abs_le.mp hk, hk'⟩
  refine (measure_mono hcov).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hs1 : Real.sqrt σ ≤ 1 := Real.sqrt_le_one.mpr hσ1
  have hs0 : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
  have hpos1 : 0 ≤ h⁻¹ * h⁻¹ * (Cu * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)) := by positivity
  have hcond : σ * (h⁻¹ * h⁻¹) * (Cu * (Real.sqrt σ * (N : ℝ)⁻¹ * (h ^ 2)⁻¹)) ≤ 1 := by
    have e : σ * (h⁻¹ * h⁻¹) * (Cu * (Real.sqrt σ * (N : ℝ)⁻¹ * (h ^ 2)⁻¹)) =
        (σ * Real.sqrt σ) * (h⁻¹ * h⁻¹ * (Cu * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹))) := by ring
    have hss : σ * Real.sqrt σ ≤ 1 := by
      calc σ * Real.sqrt σ ≤ 1 * 1 := mul_le_mul hσ1 hs1 hs0 zero_le_one
        _ = 1 := one_mul 1
    rw [e]
    calc (σ * Real.sqrt σ) * (h⁻¹ * h⁻¹ * (Cu * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)))
        ≤ 1 * (h⁻¹ * h⁻¹ * (Cu * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹))) := mul_le_mul_of_nonneg_right hss hpos1
      _ ≤ 1 := by rw [one_mul]; exact hres
  have hbase : Cu * Real.sqrt p * (Real.sqrt σ * (N : ℝ)⁻¹ * (h ^ 2)⁻¹) ≤
      Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹) := by
    have h0 : 0 ≤ Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹) := by positivity
    calc Cu * Real.sqrt p * (Real.sqrt σ * (N : ℝ)⁻¹ * (h ^ 2)⁻¹)
        = Real.sqrt σ * (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)) := by ring
      _ ≤ 1 * (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (h ^ 2)⁻¹)) := mul_le_mul_of_nonneg_right hs1 h0
      _ = _ := one_mul _
  have hXle : (Cu * Real.sqrt p * (Real.sqrt σ * (N : ℝ)⁻¹ * (h ^ 2)⁻¹)) ^ p ≤ X :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hterm : ∀ k ∈ Finset.Icc (-((K₀ : ℤ) + 1)) ((K₀ : ℤ) + 1),
      gueMeasure (Fin N) (Real.toNNReal (1 / N)) {G | 3 + 1 / σ < ((N : ℂ)⁻¹ *
        (coarseResolvent F G σ ⟨(k : ℝ) * h, h⟩).trace).im} ≤ ENNReal.ofReal X := by
    intro k _
    have h1 := hUT p hp1 N hN0 F hF σ hσ ⟨(k : ℝ) * h, h⟩ hh hcond
    exact h1.trans (ENNReal.ofReal_le_ofReal hXle)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  have hcard : (((K₀ : ℤ) + 1 + 1 - -((K₀ : ℤ) + 1)).toNat : ℝ≥0∞) =
      ENNReal.ofReal (2 * (K₀ : ℝ) + 3) := by
    have : ((K₀ : ℤ) + 1 + 1 - -((K₀ : ℤ) + 1)).toNat = 2 * K₀ + 3 := by omega
    rw [this, ← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [hcard, ← ENNReal.ofReal_mul (by positivity)]

/-- The norm failure probability for `GUE_N(1/N)`. -/
theorem normBad_le {Kn : ℝ} (hKn : 0 < Kn)
    (hNT : ∀ (N : ℕ), 0 < N → ∀ σ : ℝ, 0 ≤ σ → ∀ r : ℝ, 0 < r →
      gueMeasure (Fin N) (Real.toNNReal (σ / N)) {M | r < opB M} ≤
        ENNReal.ofReal ((Kn * Real.sqrt σ / r) ^ N)) (hN0 : 0 < N) :
    gueMeasure (Fin N) (Real.toNNReal (1 / N)) {G | 2 * Kn < opB G} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
  have h1 := hNT N hN0 1 zero_le_one (2 * Kn) (by positivity)
  rw [Real.sqrt_one, mul_one] at h1
  have e : Kn / (2 * Kn) = 1 / 2 := by field_simp
  rw [e] at h1
  exact h1

/-- The initial matrix is almost surely Hermitian. -/
theorem flowLaw_not_hermitian (a : ℝ) :
    flowLaw N a {ω : FlowSample N | ¬ ω.1.IsHermitian} = 0 := by
  have : {ω : FlowSample N | ¬ ω.1.IsHermitian} =
      {M : Matrix (Fin N) (Fin N) ℂ | ¬ M.IsHermitian} ×ˢ Set.univ := by
    ext ω; simp
  rw [this, flowLaw, Measure.prod_prod, gueMeasure_not_hermitian, zero_mul]

/-- Final summation: `0 + 2·2^{-N} + 2^m Y ≤ …`. -/
theorem final_sum_le {S₁ S₂ : ℝ≥0∞} {Y q₀ B : ℝ} {m : ℕ} (hS₁ : S₁ = 0)
    (hS₂ : S₂ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N)) (hY0 : 0 ≤ Y)
    {T : ℕ → ℝ≥0∞} (hT : ∀ j ∈ Finset.range (2 ^ m), T j ≤ ENNReal.ofReal Y)
    (h2m : (2 : ℝ) ^ m ≤ 1 + q₀) (hq₀ : 0 ≤ q₀) {Y' : ℝ} (hYY : Y ≤ Y')
    (hB : 2 * (1 / 2 : ℝ) ^ N + (1 + q₀) * Y' ≤ B) :
    (S₁ + S₂) + ∑ j ∈ Finset.range (2 ^ m), T j ≤ ENNReal.ofReal B := by
  have hsum : ∑ j ∈ Finset.range (2 ^ m), T j ≤ ENNReal.ofReal ((2 : ℝ) ^ m * Y) := by
    refine (Finset.sum_le_sum hT).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [hS₁, zero_add]
  refine (add_le_add hS₂ hsum).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : (2 : ℝ) ^ m * Y ≤ (1 + q₀) * Y' :=
    mul_le_mul h2m hYY hY0 (by linarith)
  linarith

/-- **The good spectral event at general scales.** -/
theorem spectralGoodEvent_scales (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (hκ1 : κ < 1 / 100) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∃ c₁ C₁ C b₀ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < C ∧ 0 < b₀ ∧
      ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        flowLaw N (c - (N : ℝ) ^ (-θ)) {ω | ¬ ∀ s ∈ Set.Icc (c - (N : ℝ) ^ (-θ)) c,
          GoodAt F (c - (N : ℝ) ^ (-θ)) ω E r₀ c₁ C₁ C b₀ ⌊(N : ℝ) ^ (1 - κ)⌋₊
            ((N : ℝ) ^ (-(1 / 100 : ℝ))) ((N : ℝ) ^ (-θ)) s} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro A c r₀ s₀ v₀ hK
  have hK' := hK
  obtain ⟨hc0, hc1, hr₀, hs₀, hs₀c, hv₀⟩ := hK'
  obtain ⟨Cu, hCu, hUT⟩ := im_upper_tail hIBP hLp
  obtain ⟨K₁, hK₁, hCE⟩ := chain_event hLp
  obtain ⟨Kn, hKn, hNT⟩ := opB_tail_gue hLp
  have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
  have hC₀ : (0 : ℝ) < 3 + 2 / c := by positivity
  have hc' := goodC'_pos hv₀ hr₀
  have hc₁ := goodc₁_pos hC₀ hv₀ hr₀
  obtain ⟨Cbig, hCbig⟩ : ∃ Cbig : ℝ, Cbig = max (max (8 * (3 + 2 / c))
      (4 / goodc₁ (3 + 2 / c) v₀ r₀ ^ 2)) (K₁ / (1 - chainRatio)) := ⟨_, rfl⟩
  have hC8 : 8 * (3 + 2 / c) ≤ Cbig := hCbig ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hC4 : 4 / goodc₁ (3 + 2 / c) v₀ r₀ ^ 2 ≤ Cbig :=
    hCbig ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hCK : K₁ / (1 - chainRatio) ≤ Cbig := hCbig ▸ le_max_right _ _
  refine ⟨goodc₁ (3 + 2 / c) v₀ r₀, 1 + 1 / goodC' v₀ r₀, Cbig, goodC' v₀ r₀ ^ 2 / 9, hc₁,
    by positivity, lt_of_lt_of_le (by positivity) hC8, by positivity, ?_⟩
  intro D
  obtain ⟨Ncr, hNcr⟩ := (coarseRelative_holds hLp hIBP) A c r₀ s₀ v₀ hK 0 (D + 1)
  obtain ⟨Nsc, hNsc⟩ := scales_eventually hθ hκ hκ1 hs₀ hc0 hC₀ hv₀ hr₀ hc' hCu
  obtain ⟨p, hp1, Npr, hNpr⟩ := prob_eventually A D Cu (2 * Kn)
    (2 * (K₁ / (1 - chainRatio)) ^ 4) hCu (by positivity) (by positivity)
  refine ⟨max (max Ncr Nsc) Npr, ?_⟩
  intro N hN F E hC
  obtain ⟨h8, hts₀, htc, hℓ1, hsc1, hsc3, hsc3', hsc3'', hsc4, hsc4', hsm, hsm', hh1, hres⟩ :=
    hNsc N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hNcr' := hNcr N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hpr := hNpr N (le_trans (le_max_right _ _) hN)
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have ht : 0 < (N : ℝ) ^ (-θ) := Real.rpow_pos_of_pos hNr _
  have hhpos : 0 < (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_pos_of_pos hNr _
  generalize htdef : (N : ℝ) ^ (-θ) = t at *
  generalize hℓdef : ⌊(N : ℝ) ^ (1 - κ)⌋₊ = ℓ at *
  generalize hhdef : (N : ℝ) ^ (-(1 / 100 : ℝ)) = h at hhpos hpr
  have hapos : 0 < c - t := by linarith
  have has₀ : c - s₀ ≤ c - t := by linarith
  generalize hadef : c - t = a at *
  have hat : a = c - t := hadef.symm
  -- mesh in time
  obtain ⟨m, hm, h2m⟩ := exists_mesh_level hK₁ hhpos
  have hst : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hmod : K₁ * Real.sqrt t * chainRatio ^ m / (1 - chainRatio) ≤ h := by
    refine le_trans ?_ hm
    apply div_le_div_of_nonneg_right _ hq1.le
    have h0 : 0 ≤ K₁ * chainRatio ^ m := by have := chainRatio_pos; positivity
    calc K₁ * Real.sqrt t * chainRatio ^ m = Real.sqrt t * (K₁ * chainRatio ^ m) := by ring
      _ ≤ 1 * (K₁ * chainRatio ^ m) := mul_le_mul_of_nonneg_right hst h0
      _ = K₁ * chainRatio ^ m := one_mul _
  -- mesh in space
  have hNA : 0 ≤ (N : ℝ) ^ A := Real.rpow_nonneg hNr.le _
  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : ℕ, K₀ = ⌈((N : ℝ) ^ A + 2 * Kn) / h⌉₊ := ⟨_, rfl⟩
  have hK₀ : (N : ℝ) ^ A + 2 * Kn ≤ (K₀ : ℝ) * h := by
    have := Nat.le_ceil (((N : ℝ) ^ A + 2 * Kn) / h)
    rw [div_le_iff₀ hhpos, ← hK₀def] at this
    exact this
  have hK₀' : 2 * (K₀ : ℝ) + 3 ≤ 2 * (((N : ℝ) ^ A + 2 * Kn) / h + 1) + 3 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ ((N : ℝ) ^ A + 2 * Kn) / h)
    rw [← hK₀def] at this
    linarith
  subst hhdef
  -- the covering of the bad set
  have hsub : {ω : FlowSample N | ¬ ∀ s ∈ Set.Icc a c,
      GoodAt F a ω E r₀ (goodc₁ (3 + 2 / c) v₀ r₀) (1 + 1 / goodC' v₀ r₀) Cbig
        (goodC' v₀ r₀ ^ 2 / 9) ℓ ((N : ℝ) ^ (-(1 / 100 : ℝ))) t s} ⊆
      ({ω : FlowSample N | ¬ ω.1.IsHermitian} ∪ {ω | ¬ ChainGood K₁ t ω.2}) ∪
        ⋃ j ∈ Finset.range (2 ^ m), {ω | flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∈
          (upperBad F (a + (j : ℝ) * t / 2 ^ m) ((N : ℝ) ^ (-(1 / 100 : ℝ))) K₀ ∪
            localBad F E r₀ (a + (j : ℝ) * t / 2 ^ m)) ∪ {G | 2 * Kn < opB G}} := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
      Finset.mem_range] at hcon
    obtain ⟨⟨hH, hCh⟩, hJ⟩ := hcon
    push Not at hH hCh
    refine good_of_events hN0 hK hC ht hat has₀ hK₁.le hmod hK₀ hℓ1 hsc1 hsc3 hsc3' hsc3''
      hsc4 hsc4' hsm hsm' hh1 hH hCh ?_ hC8 hC4 hCK
    intro j hj
    obtain ⟨⟨h1, h2⟩, h3⟩ := hJ j hj
    exact ⟨h1, h2, h3⟩
  refine (measure_mono hsub).trans ?_
  refine ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _))).trans ?_
  have hX0 : 0 ≤ (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹)) ^ p := by
    positivity
  refine final_sum_le (Y := (2 * (K₀ : ℝ) + 3) *
      (Cu * Real.sqrt p * ((N : ℝ)⁻¹ * (((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 2)⁻¹)) ^ p +
        (N : ℝ) ^ (-(D + 1)) + (1 / 2 : ℝ) ^ N)
    (flowLaw_not_hermitian a) (hCE N h8 a t ht) (by positivity) ?_ h2m
    (by positivity) ?_ hpr
  · intro j hj
    rw [Finset.mem_range] at hj
    have h2m0 : (0 : ℝ) < 2 ^ m := by positivity
    have hjt : (j : ℝ) * t / 2 ^ m ≤ t := by
      rw [div_le_iff₀ h2m0]
      have : (j : ℝ) ≤ 2 ^ m := by exact_mod_cast hj.le
      calc (j : ℝ) * t ≤ 2 ^ m * t := mul_le_mul_of_nonneg_right this ht.le
        _ = t * 2 ^ m := mul_comm _ _
    have hj0 : 0 ≤ (j : ℝ) * t / 2 ^ m := by positivity
    have hsja : a ≤ a + (j : ℝ) * t / 2 ^ m := le_add_of_nonneg_right hj0
    have hsjc : a + (j : ℝ) * t / 2 ^ m ≤ c := by linarith
    have hsjpos : 0 < a + (j : ℝ) * t / 2 ^ m := lt_of_lt_of_le hapos hsja
    have hsj1 : a + (j : ℝ) * t / 2 ^ m ≤ 1 := le_trans hsjc hc1.le
    have hsjreg : a + (j : ℝ) * t / 2 ^ m ∈ Set.Icc (c - s₀) c :=
      Set.mem_Icc.mpr ⟨le_trans has₀ hsja, hsjc⟩
    refine (flowLaw_preimage_normalized_le hN0 hapos hsja _).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    have hU := upperBad_le hUT hCu hp1 hN0 hC.1 hsjpos hsj1 hhpos K₀ hres
    have hL : gueMeasure (Fin N) (Real.toNNReal (1 / N))
        (localBad F E r₀ (a + (j : ℝ) * t / 2 ^ m)) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
      hNcr' F E hC _ hsjreg ∅ (by simp)
    have hNm := normBad_le hKn hNT hN0
    refine (add_le_add (add_le_add hU hL) hNm).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  · have := mul_le_mul_of_nonneg_right hK₀' hX0
    linarith

/-- **`SpectralGoodEventContract`**: the long-gap estimate with the counts, long couplings and
displacement, at `θ = 1/500`, `κ = 13/5000`, `h = N^{-1/100}`.
Only the Gaussian inputs `GaussianLpGradient` and `MultivariateGaussianIBP` are assumed. -/
theorem spectralGoodEvent_holds (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    SpectralGoodEventContract := by
  intro A c r₀ s₀ v₀ hK
  obtain ⟨c₁, C₁, C, b₀, h1, h2, h3, h4, hD⟩ := spectralGoodEvent_scales hLp hIBP (1 / 500)
    (13 / 5000) (by norm_num) (by norm_num) (by norm_num) A c r₀ s₀ v₀ hK
  refine ⟨c₁, C₁, C, b₀, h1, h2, h3, h4, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hD D
  exact ⟨N₀, fun N hN F E hC => hN₀ N hN F E hC⟩

/-- **The finer-scale good event**: `θ = 1/100`, `τ = N^{-1/100}`, `a' = c - τ`,
`ℓ' = ⌊N^{1-(1/100)/3}⌋`, `h = N^{-1/100}`. Fixed regularity constants and `A` first, then
`c₁, C₁, C, b₀ > 0`, then every `D` has `N₀`; for `N ≥ N₀` and every `F` in the class, outside
an outer `flowLaw N a'`-probability `N^{-D}`, simultaneously for all `s ∈ [a', c]`: long gaps
`|λ_i - λ_j| ≥ c₁|i-j|/N` for `|i-j| ≥ ℓ'`; short gaps `|λ_i - λ_j| ≤ C₁ℓ'/N` for `|i-j| < ℓ'`
meeting the bulk `r₀/8`-window; the coarse upper count `#[x,y] ≤ CN((y-x) + h)`; the bulk lower
count `#[x,y] ≥ c₁N(y-x)` on `[x,y] ⊂ [E - r₀/8, E + r₀/8]`, `y - x ≥ ℓ'/N`; the long-coupling
bounds; and the displacement `‖H_s - H_{a'}‖ ≤ C√τ`. -/
theorem spectralGoodEvent_s8 (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∃ c₁ C₁ C b₀ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < C ∧ 0 < b₀ ∧
      ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
        let a : ℝ := c - τ
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        let h : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
        flowLaw N a {ω | ¬ ∀ s ∈ Set.Icc a c,
          (∀ i j : Fin N, ℓ ≤ labelDist i j →
            c₁ * (labelDist i j : ℝ) / N ≤
              |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|) ∧
          (∀ i j : Fin N, labelDist i j < ℓ →
            min |flowEigenvalue F a ω s i - E| |flowEigenvalue F a ω s j - E| ≤ r₀ / 8 →
            |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| ≤ C₁ * ℓ / N) ∧
          (∀ x y : ℝ, x ≤ y →
            ((Finset.univ.filter fun i : Fin N =>
                flowEigenvalue F a ω s i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h)) ∧
          (∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
            c₁ * N * (y - x) ≤
              ((Finset.univ.filter fun i : Fin N =>
                flowEigenvalue F a ω s i ∈ Set.Icc x y).card : ℝ)) ∧
          (∀ i : Fin N, longCoupling F a ω ℓ s i ≤ C * N / ℓ ∧
            (|flowEigenvalue F a ω s i - E| ≤ r₀ / 8 → b₀ * N / ℓ ≤ longCoupling F a ω ℓ s i)) ∧
          (∀ x : Fin N → ℂ, l2Norm ((flowMatrix F a ω s - flowMatrix F a ω a) *ᵥ x) ≤
            C * Real.sqrt τ * l2Norm x)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro A c r₀ s₀ v₀ hK
  obtain ⟨c₁, C₁, C, b₀, h1, h2, h3, h4, hD⟩ := spectralGoodEvent_scales hLp hIBP (1 / 100)
    ((1 / 100 : ℝ) / 3) (by norm_num) (by norm_num) (by norm_num) A c r₀ s₀ v₀ hK
  refine ⟨c₁, C₁, C, b₀, h1, h2, h3, h4, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hD D
  exact ⟨N₀, fun N hN F E hC => hN₀ N hN F E hC⟩

end BlockBand.Palm.GoodEvent
