module

public import BlockBand.Critical.RelativeVectors.ComparisonTotal
public import BlockBand.Critical.RelativeVectors.IntervalEvent
public import BlockBand.Critical.RelativeVectors.Coarse

/-!
# The main clause of the relative mixed-vector theorem

`relativeMixedVectors_comparison` is proved in three parts:
1. `exists_rmv_sets`: the measurable good event `𝒜` (interval and distant-label bounds, the
   long-gap event `𝓡`, localization, simple spectrum), `step1_goodPaths` with `D₁`, and the
   path-measurable good paths `𝒢 ⊆ simplePathSet ∩ longGapPathSet`.
2. `compare_of_duhamel`: the Duhamel identity for the phase-averaged test, the integrated
   generator difference on `𝒜` (`goodSample_integral_le`), the crude bound off `𝒜`
   (`crudeSample_integral_le`) and the equilibration (`equilSample_le`).
3. `rmv_total_le`: the total error is `≤ rmvConst · N^{-1/5000}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative

theorem rpow_neg_gap_le {x : ℝ} (hx : 4 ≤ x) {D E : ℝ} (hDE : D + 2 ≤ E) :
    4 * x ^ (-E) ≤ x ^ (-D) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have e : x ^ (-E) = x ^ (-D) * x ^ (-(E - D)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have h2 : x ^ (-(E - D)) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : x ^ (-(2 : ℝ)) ≤ 1 / 16 := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hp : 0 ≤ x ^ (-D) := by positivity
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left (h2.trans h3) hp]

theorem gammaShiftConst_nonneg {c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    0 ≤ gammaShiftConst c r₀ s₀ v₀ := by
  have hκ'0 : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
  have hv0 := hK.2.2.2.2.2
  have hc0 := hK.1
  have hs0 := hK.2.2.2.1
  have hr₀ := hK.2.2.1
  unfold gammaShiftConst
  positivity

set_option maxHeartbeats 4000000 in
/-- **The relative mixed-vector theorem, main clause.** See the module docstring. -/
theorem relativeMixedVectors_comparison
    (hD : ∀ N r, RelativeDuhamelStatement N r)
    (hRF : ∀ N r, ReferenceFlowStatement N r)
    (hCR : CoarseRelativeContract) (hLp : GaussianLpGradient)
    (hSG : SpectralGoodEventContract) (hRL : RelativeLocalizationContract)
    (hDBM : ∀ N, DysonBrownianMotion N) :
    RelativeMixedVectorsComparison := by
  intro A c r₀ s₀ v₀ hK r k Cw
  obtain ⟨c₁, C₁, Csp, b₀, hc₁, hC₁, hCsp, hb₀, hSGD⟩ := hSG A c r₀ s₀ v₀ hK
  have hr₀ : 0 < r₀ := hK.2.2.1
  have hs₀ : 0 < s₀ := hK.2.2.2.1
  set Iabs := |intB4 c r₀ s₀ v₀ r| with hIabs
  set Rabs := |relCompConst c r₀ s₀ v₀ r| with hRabs
  set Cdabs := |relDistConst c r₀ s₀ v₀ r| with hCdabs
  have hγ := gammaShiftConst_nonneg hK
  refine ⟨1 / 5000, by norm_num,
    rmvConst r k A c r₀ s₀ v₀ Iabs Rabs (gammaShiftConst c r₀ s₀ v₀) c₁ Csp Cdabs b₀,
    fun D => ?_⟩
  set p : ℝ := 3 + 2 * max A 1 with hp
  have hp0 : 5 ≤ p := by have := le_max_right A 1; rw [hp]; linarith
  set D₁ : ℝ := max D 0 + p * 5 + 1 with hD₁
  set Dsp : ℝ := 2 * D₁ + p * 10 + 2 with hDsp
  obtain ⟨Nco, hNco⟩ := relativeCoarse_event hCR hLp hK r Dsp
  obtain ⟨Niv, hNiv⟩ := relativeInterval_event hCR hLp hK r Dsp
  obtain ⟨Nsg, hNsg⟩ := hSGD Dsp
  obtain ⟨Nsp, hNsp⟩ := hRL.reference_finite_speed A c r₀ s₀ v₀ hK b₀ hb₀ Cw Dsp
  obtain ⟨Nρ, hNρ⟩ := centralRho_small hc₁ hCsp.le hr₀
  have ht0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 500 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nt, hNt⟩ := (eventually_atTop.1 (ht0.eventually (gt_mem_nhds hs₀)))
  refine ⟨max (max (max Nco Niv) (max Nsg Nsp)) (max (max Nρ Nt) 4), ?_⟩
  intro N hN F E hC V hV
  have hNco' := hNco N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)) F E hC V hV
  have hNiv' := hNiv N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)) F E hC V hV
  have hNsg' := hNsg N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)) F E hC
  have hNsp' := hNsp N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)) F E hC
  have hρ8 := hNρ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hN))
  have hts : (N : ℝ) ^ (-(1 / 500 : ℝ)) < s₀ := hNt N (le_trans (le_trans (le_max_right _ _)
    (le_max_left _ _)) (le_trans (le_max_right _ _) hN))
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  dsimp only at hNsg' hNsp'
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  -- the scales
  set t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ)) with ht
  set a : ℝ := rmvStart c N with ha
  have hat : a = c - t := rfl
  have ht0' : 0 < t := by positivity
  have hca : c - a = t := by rw [hat]; ring
  have hac : a < c := by linarith
  have ha0 : 0 < a := by
    have := hK.2.2.2.2.1
    have := hK.1
    linarith
  set ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have hx : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 13 / 5000 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    exact Nat.one_le_iff_ne_zero.mpr (by intro h0; rw [Nat.floor_eq_zero] at h0; linarith)
  set w : ℕ := ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
    (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ with hw
  have hw1 : 1 ≤ w := rmv_w_pos hN1
  have hsq : Real.sqrt t ≤ (w : ℝ) / N := rmv_sqrt_le_w hN1
  -- the reference flow
  obtain ⟨Ωaux, _, Paux, hPaux, 𝓜, Ξ, hmeas, hflow⟩ :=
    hRF N r F a c b₀ ℓ hC.1 hac hb₀ (by omega)
  -- the constants of the good event
  set Ccomp : ℝ := Rabs * (N * (N : ℝ) ^ (-(1 / 100 : ℝ))) with hCcomp
  set Mint : ℝ := 147 * Iabs * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) with hMint
  have hD' : 4 * (N : ℝ) ^ (-Dsp) ≤ (N : ℝ) ^ (-(2 * D₁)) :=
    rpow_neg_gap_le hN4r (by rw [hDsp]; nlinarith)
  have hEx := exists_rmv_sets (r := r) (E := E) (r₀ := r₀) (V := V) (t := t) (ℓ := ℓ) (w := w)
    (c₁ := c₁) (Csp := Csp) (b₀ := b₀) (Ccomp := Ccomp) (Cd := Cdabs) (Mint := Mint)
    (Cw := Cw) (Dsp := Dsp) (D₁ := D₁) (D' := Dsp)
    (hDBM N) hN0 hC.1 ha0 hac.le _ _ _ _ hNco' hNiv' hNsg' hNsp' ?_ ?_ hD'
  rotate_left
  · -- the good samples
    intro ω hh hs h1 h2 h3 h4
    simp only [Set.mem_ofPred_eq, not_not, not_exists, not_and, not_lt] at h1 h2 h3 h4
    have hss : ∀ σ ∈ Icc a c, BlockBand.Critical.WeightedDensity.SimpleSpectrum
        (flowMatrix F a ω σ) := fun σ hσ =>
      ⟨ps_flowMatrix_isHermitian hC.1 a hh σ, (hs σ hσ).injective⟩
    have hca' : a ∈ Icc a c := left_mem_Icc.mpr hac.le
    refine ⟨hh, hs, (h3 a hca').2.2.2.1, fun σ hσ => (h3 σ hσ).2.2.2.2.2,
      fun σ hσ => (h3 σ hσ).1, fun σ hσ i => ((h3 σ hσ).2.2.2.2.1 i).2,
      fun σ hσ i hi => ?_, fun σ hσ j hj q => ?_, fun σ hσ x y hx hxy hy p => ?_,
      fun k' hk' P hP => h4 k' hk' P hP⟩
    · refine ((h1 σ hσ (hss σ hσ)).1 i hi).trans ?_
      unfold relCompConst
      rw [hCcomp, hRabs]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    · refine ((h1 σ hσ (hss σ hσ)).2 j hj q).trans ?_
      rw [hCdabs]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    · refine (h2 σ hσ (hss σ hσ) x y hx hxy hy p).trans ?_
      rw [hMint, hIabs]
      have : (0 : ℝ) ≤ (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) * nsq p := by
        have := nsq_nonneg p; positivity
      nlinarith [le_abs_self (intB4 c r₀ s₀ v₀ r)]
  · intro ω _ h3 σ hσ i j hij
    simp only [Set.mem_ofPred_eq, not_not] at h3
    exact (h3 σ hσ).1 i j hij
  obtain ⟨𝒜, 𝒢, h𝒜m, h𝒜good, h𝒢m, h𝒢c, h𝒢sub, h𝒢B⟩ := hEx
  refine ⟨𝒢, h𝒢m, h𝒢c.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have h1 := rpow_neg_gap_le hN4r (D := D) (E := D₁) (by rw [hD₁]; nlinarith [le_max_left D 0])
    have h2 := rpow_neg_gap_le hN4r (D := D) (E := Dsp)
      (by rw [hDsp, hD₁]; nlinarith [le_max_left D 0, le_max_right D 0])
    have : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := by positivity
    linarith
  intro ι hι B hBm hBG hwin f hf
  have hRef : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω) := fun ω h => (hflow ω h).1
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  set Zsq := frameZsq N A c s₀ v₀ with hZsq
  have hZsq0 : 0 ≤ Zsq := frameZsq_nonneg hK
  set ε : ℝ := (rmvP N A ^ 5)⁻¹ with hε
  have hε0 : 0 < ε := by have := one_le_rmvP hN1 A; positivity
  set δ : ℝ := c₁ * ℓ / N with hδ
  have hδ0 : 0 < δ := by positivity
  have hCcomp0 : 0 ≤ Ccomp := by positivity
  have hMint0 : 0 ≤ Mint := by positivity
  have hCd0 : 0 ≤ Cdabs := abs_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  set Tot : ℝ := t * tbQ0 N r k (diagXJ N c r₀ s₀ v₀ t ℓ w c₁ Csp Mint Cdabs) Ccomp
        (Real.sqrt Zsq) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε +
      tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * Zsq + 1))
          (Real.sqrt Zsq) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε * (k * (N : ℝ) ^ (-Dsp))
    with hTotdef
  set Cru : ℝ := t * (tbQ0 N r k 0 0 (Real.sqrt Zsq) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2))
        (b₀ * N / ℓ) 1 +
      tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * Zsq + 1))
          (Real.sqrt Zsq) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) 1 * k) with hCrudef
  set Eqb : ℝ := Real.exp (-(b₀ * N * t / (2 * ℓ))) *
    (Real.sqrt (N * r * Zsq) + Real.sqrt ((N : ℝ) * r)) with hEqbdef
  have hTot0 : 0 ≤ Tot := by
    rw [hTotdef]; unfold tbQ0 tbQ1 diagXJ
    have := Real.sqrt_nonneg Zsq
    positivity
  have hCru0 : 0 ≤ Cru := by
    rw [hCrudef]; unfold tbQ0 tbQ1
    have := Real.sqrt_nonneg Zsq
    positivity
  have hHerm := BlockBand.Palm.RelativeLocalization.ae_fst_isHermitian (N := N) a
  have hpath : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) ∧
      ∀ σ ∈ Icc a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
        c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| := by
    filter_upwards [hHerm] with ω hh hωB
    have hmem := h𝒢sub (hBG hωB)
    exact ⟨(mem_simplePathSet_iff hC.1 hac.le hh).mp hmem.1,
      (mem_longGapPathSet_iff hC.1 hac.le hh).mp hmem.2⟩
  have hBae : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) ∧
      ∀ i j : Fin N, ℓ ≤ labelDist i j →
        δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| := by
    filter_upwards [hpath] with ω hω hωB σ hσ
    obtain ⟨hs, hg⟩ := hω hωB
    refine ⟨hs σ hσ, fun i j hij => le_trans ?_ (hg σ hσ i j hij)⟩
    have : (ℓ : ℝ) ≤ labelDist i j := by exact_mod_cast hij
    rw [hδ]
    gcongr
  have hTot : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ω ∈ 𝒜 → ∫ s in Ioc a c,
      |rmvGenDiff F a b₀ ℓ V (rmvBackward Paux 𝓜 Ξ c fun ω => arrayTest ι (f ω)) ω s| ≤ Tot := by
    refine Filter.Eventually.of_forall fun ω hωB hω𝒜 => ?_
    have hG := h𝒜good ω hω𝒜
    have hRω := hflow ω hG.simple
    have h := goodSample_integral_le hN0 hK hC hV hat ht0'.le hts.le hℓ1 hw1 hsq hc₁ hCsp.le hb₀
      hCcomp0 hCd0 hMint0 hρ8 hG hRω.1 hRω.2 ι (hwin ω hωB) (hf.c2 ω) hε0
    rw [hca] at h
    exact h
  have hCru : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ∫ s in Ioc a c,
      |rmvGenDiff F a b₀ ℓ V (rmvBackward Paux 𝓜 Ξ c fun ω => arrayTest ι (f ω)) ω s| ≤ Cru := by
    filter_upwards [hpath] with ω hω hωB
    obtain ⟨hs, hg⟩ := hω hωB
    have h := crudeSample_integral_le hN0 hK hC hV hac.le hℓ1 hc₁ hb₀ hg (hRef ω hs) ι (hf.c2 ω)
    rw [hca] at h
    exact h
  have hEq : ∀ᵐ ω ∂flowLaw N a, ω ∈ B →
      |rmvBackward Paux 𝓜 Ξ c (fun ω => arrayTest ι (f ω)) ω a
          (frameArray V (flowMatrix F a ω a)) -
        ∫ z, arrayTest ι (f ω) z ∂gaussianMarkLaw N r| ≤ Eqb := by
    filter_upwards [hpath] with ω hω hωB
    have h := equilSample_le hac.le (hRef ω (hω hωB).1) (isArrayC2Bounded_arrayTest ι (hf.c2 ω))
      (frameArray V (flowMatrix F a ω a))
    rw [hca] at h
    refine h.trans ?_
    rw [hEqbdef]
    gcongr
    exact arrayNormSq_frameArray_le hN0 hK hC hV _
  have hη := h𝒢B B hBm hBG
  have hcmp := compare_of_duhamel (hD N r) hC.1 ha0 hac hb₀ (by omega) Paux 𝓜 Ξ hmeas hRef V ι hι
    f hf hδ0 B hBm hBae 𝒜 h𝒜m hTot0 hCru0 hTot hCru hEq hη
  have hD₁' : (3 + 2 * max A 1) * ((5 : ℕ) : ℝ) ≤ D₁ := by
    rw [hD₁]; push_cast; nlinarith [le_max_right D 0]
  have hDsp' : (3 + 2 * max A 1) * ((10 : ℕ) : ℝ) ≤ Dsp := by
    rw [hDsp, hD₁]; push_cast; nlinarith [le_max_right D 0]
  have htot := rmv_total_le hN1 hK r k (abs_nonneg (intB4 c r₀ s₀ v₀ r))
    (abs_nonneg (relCompConst c r₀ s₀ v₀ r)) hCd0 hγ hc₁ hCsp.le hb₀ hD₁' hDsp'
  refine hcmp.trans ?_
  rw [← measureReal_def]
  exact mul_le_mul_of_nonneg_right htot measureReal_nonneg

end BlockBand.Critical.RelativeVectors
