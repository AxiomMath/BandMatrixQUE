module

public import BlockBand.Palm.MomentFlow.Steps2Long
public import BlockBand.Palm.MomentFlow.BridgeODE
public import BlockBand.Palm.FreshPalmShift

/-!
# Long couplings against the one-particle conditional moments, averaged over `𝓛`

`long_coupling_conditional`: at a fixed time `s`, off an `𝓛`-measurable set of probability
`≤ N^{-D}`, for every label `i` in the bulk window,
`Σ_{|j-i| ≥ ℓ} c_ij(s) E[X_j(s) | 𝓛] ≤ (2N/(c₁ℓ)) Cst q*Γq + N^{2-D}‖q‖²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.Palm

variable {N : ℕ}

theorem momentMonomial_single (X : Fin N → ℝ) (j : Fin N) :
    momentMonomial X (Pi.single j 1) = X j := by
  classical
  unfold momentMonomial
  rw [Finset.prod_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp

theorem condMoment_single (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (σ : ℝ)
    (j : Fin N) :
    condMoment F a c q σ (Pi.single j 1) =
      (flowLaw N a)[flowOverlap F a q σ j | pathSigma F a a c] := by
  unfold condMoment
  congr 1
  funext ω
  exact momentMonomial_single _ j

theorem measurable_flowRate_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) {σ : ℝ}
    (hσ : σ ∈ Icc s c) (i j : Fin N) :
    Measurable[pathSigma F a s c] (fun ω : FlowSample N => flowRate F a ω σ i j) := by
  unfold flowRate
  exact (measurable_const.mul (((measurable_flowEigenvalue_pathSigma F a s c hσ i).sub
    (measurable_flowEigenvalue_pathSigma F a s c hσ j)).pow_const 2)).inv

/-- **Long couplings averaged over `𝓛`, at a fixed time.** -/
theorem long_coupling_conditional (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N) {A c r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε5 : ε < 1 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        ∀ q : Fin N → ℂ, ∀ s ∈ Ioc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c, ∀ i : Fin N,
          ∃ B : Set (FlowSample N),
            MeasurableSet[pathSigma F (c - (N : ℝ) ^ (-(1 / 100 : ℝ)))
              (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c] B ∧
            flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            ∀ᵐ ω ∂flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))), ω ∉ B →
              |flowEigenvalue F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i - E| ≤ r₀ / 2 →
              ∑ j ∈ Finset.univ.filter
                  (fun j => ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j),
                flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j *
                  condMoment F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c q s (Pi.single j 1) ω ≤
              2 / (c₁ * ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ / N) * Cst *
                  quadForm (freshGamma F c E) q +
                (N : ℝ) ^ (2 - D) * ∑ k, ‖q k‖ ^ 2 := by
  have hK' := hK
  obtain ⟨c₁, hc₁, Cst, hCst, hW⟩ :=
    long_coupling_event_bound_measurable hELG hMDE hLp hIBP (A := A) hK hε hε5
  obtain ⟨c₂, C₁, C₀, b₀, hc₂, -, -, -, hS8⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK'
  refine ⟨c₁, hc₁, Cst, hCst, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hW (2 * D + 1)
  obtain ⟨N₂, hN₂⟩ := hS8 (D + 1)
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ N₂ ≤ n) ∧ (4 : ℝ) ≤ n ∧
      (2 : ℝ) ≤ (n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) ∧
      4 / c₂ ^ 2 ≤ (n : ℝ) ^ (1 - (2 / 300 : ℝ)) := by
    refine ((eventually_ge_atTop N₁).and (eventually_ge_atTop N₂)).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 4).and
      ((eventually_rpow_ge (by norm_num) _).and (eventually_rpow_ge (by norm_num) _)))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC q s hs i => ?_⟩
  obtain ⟨⟨hNN₁, hNN₂⟩, hN4, hℓ2, hℓN⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNp
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
  set a : ℝ := c - τ
  set ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
  set μ := flowLaw N a
  have hsI : s ∈ Icc a c := ⟨hs.1.le, hs.2⟩
  have hℓge : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2 ≤ ℓ := by
    have h3 : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) < (ℓ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith [hℓ2, h3]
  -- the good set `G` and the weights
  set G : Set (FlowSample N) := {ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2 ∧
    ∀ j : Fin N, ℓ ≤ labelDist i j → flowRate F a ω s i j ≤ 1}
  have hGm : MeasurableSet[pathSigma F a a c] G := by
    have h1 : MeasurableSet[pathSigma F a a c]
        {ω : FlowSample N | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2} :=
      (Measurable.comp (g := fun x : ℝ => |x - E|) (by fun_prop)
        (measurable_flowEigenvalue_pathSigma F a a c hsI i)) measurableSet_Iic
    have h2 : MeasurableSet[pathSigma F a a c] {ω : FlowSample N | ∀ j : Fin N, ℓ ≤ labelDist i j →
        flowRate F a ω s i j ≤ 1} := by
      have e : {ω : FlowSample N | ∀ j : Fin N, ℓ ≤ labelDist i j → flowRate F a ω s i j ≤ 1} =
          ⋂ j : Fin N, {ω | ℓ ≤ labelDist i j → flowRate F a ω s i j ≤ 1} := by
        ext ω; simp
      rw [e]
      refine MeasurableSet.iInter fun j => ?_
      by_cases hj : ℓ ≤ labelDist i j
      · simp only [hj, true_implies]
        exact (measurable_flowRate_pathSigma F a a c hsI i j) measurableSet_Iic
      · simp only [hj, false_implies, Set.ofPred_true, MeasurableSet.univ]
    exact h1.inter h2
  set w : Fin N → FlowSample N → ℝ := fun j ω =>
    if ℓ ≤ labelDist i j then G.indicator (fun ω => flowRate F a ω s i j) ω else 0
  set X : Fin N → FlowSample N → ℝ := fun j ω => flowOverlap F a q s j ω
  have hw : ∀ j, StronglyMeasurable[pathSigma F a a c] (w j) := by
    intro j
    by_cases hj : ℓ ≤ labelDist i j
    · have : w j = G.indicator (fun ω => flowRate F a ω s i j) := by
        funext ω; simp [w, hj]
      rw [this]
      exact ((measurable_flowRate_pathSigma F a a c hsI i j).indicator hGm).stronglyMeasurable
    · have : w j = fun _ => 0 := by funext ω; simp [w, hj]
      rw [this]; exact stronglyMeasurable_const
  have hw0 : ∀ j ω, 0 ≤ w j ω := by
    intro j ω
    simp only [w]
    split_ifs
    · exact Set.indicator_nonneg (fun ω _ => flowRate_nonneg F a ω s i j) ω
    · exact le_rfl
  have hwK : ∀ j ω, w j ω ≤ 1 := by
    intro j ω
    simp only [w]
    split_ifs with hj
    · by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω]; exact hω.2 j hj
      · rw [Set.indicator_of_notMem hω]; norm_num
    · norm_num
  set Bq : ℝ := (N : ℝ) * ∑ k, ‖q k‖ ^ 2
  have hBq : 0 ≤ Bq := by positivity
  have hX : ∀ j, Measurable (X j) := fun j => measurable_flowOverlap F a q s j
  have hX0 : ∀ j ω, 0 ≤ X j ω := fun j ω => by simp only [X, flowOverlap]; positivity
  have hXB : ∀ j ω, X j ω ≤ Bq := fun j ω => FreshPalmAssembly.overlap_le_nsq _ q j
  -- the bad set
  obtain ⟨BadW, hBadWm, hBadWP, hBadW⟩ := hN₁ N hNN₁ F E hC q
  have hsimp := ae_simple (hDBM N) hC.1 a
  set Z : Set (FlowSample N) := {ω | ¬ (ω.1.IsHermitian ∧
    ∀ σ : ℝ, a < σ → HasSimpleSpectrum N (flowMatrix F a ω σ))}
  have hZ : μ Z = 0 := by
    have := hsimp
    rw [ae_iff] at this
    exact this
  set Bad := toMeasurable μ (BadW ∪ Z)
  have hBadm : MeasurableSet Bad := measurableSet_toMeasurable _ _
  have hBadP : μ Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(2 * D + 1))) +
      ENNReal.ofReal ((N : ℝ) ^ (-(2 * D + 1))) := by
    rw [measure_toMeasurable]
    exact (measure_union_le _ _).trans (by rw [hZ, add_zero]; exact hBadWP)
  set bnd : ℝ := 2 / (c₁ * ℓ / N) * Cst * quadForm (freshGamma F c E) q
  have hγ : 0 ≤ quadForm (freshGamma F c E) q := by
    rw [freshGamma_quad_eq hC.1]
    exact mul_nonneg hK'.1.le (Finset.sum_nonneg fun _ _ => by positivity)
  have hbnd : 0 ≤ bnd := by positivity
  have hgood : ∀ ω ∉ Bad, ∑ j, w j ω * X j ω ≤ bnd := by
    intro ω hω
    have hω' : ω ∉ BadW ∪ Z := fun h' => hω (subset_toMeasurable _ _ h')
    have hωW : ω ∉ BadW := fun h' => hω' (Or.inl h')
    have hωZ : ω ∉ Z := fun h' => hω' (Or.inr h')
    simp only [Z, Set.mem_ofPred_eq, not_not] at hωZ
    by_cases hG : ω ∈ G
    · have e : ∑ j, w j ω * X j ω = ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
          flowRate F a ω s i j * flowOverlap F a q s j ω := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : ℓ ≤ labelDist i j
        · simp [w, X, hj, Set.indicator_of_mem hG]
        · simp [w, hj]
      rw [e]
      exact hBadW ω hωW hωZ.1 s hsI (hωZ.2 s hs.1) i hG.1
    · have e : ∀ j, w j ω = 0 := fun j => by
        simp only [w]; split_ifs
        · exact Set.indicator_of_notMem hG _
        · rfl
      simp only [e, zero_mul, Finset.sum_const_zero]
      exact hbnd
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  obtain ⟨B₀, hB₀m, hB₀P, hB₀⟩ := condExp_weighted_sum_le_of_small (μ := μ) (pathSigma_le F a a c)
    w X hbnd zero_le_one hBq ht hw hw0 hwK hX hX0 hXB hBadm hgood
  -- the `𝓛`-measurable exceptional set
  set B := B₀ ∪ {ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2} \ G
  have hbulkm : MeasurableSet[pathSigma F a a c]
      {ω : FlowSample N | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2} :=
    (Measurable.comp (g := fun x : ℝ => |x - E|) (by fun_prop)
        (measurable_flowEigenvalue_pathSigma F a a c hsI i)) measurableSet_Iic
  refine ⟨B, hB₀m.union (hbulkm.diff hGm), ?_, ?_⟩
  · -- probability: `P(B₀) ≤ P(Bad)/t ≤ N^{-D}/2`, `P(bulk \ G) ≤ P(s8 bad) ≤ N^{-D}/2`
    have hP1 : μ B₀ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) := by
      have hfin : μ Bad ≠ ⊤ := measure_ne_top _ _
      have hreal : μ.real Bad ≤ 2 * (N : ℝ) ^ (-(2 * D + 1)) := by
        have := ENNReal.toReal_mono (by finiteness) hBadP
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.toReal_ofReal
          (by positivity)] at this
        simpa [Measure.real, two_mul] using this
      have hkey : 2 * (N : ℝ) ^ (-(2 * D + 1)) / (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-D) / 2 := by
        rw [div_le_div_iff₀ ht (by norm_num)]
        have e : (N : ℝ) ^ (-(2 * D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
          rw [← Real.rpow_add hNp, ← Real.rpow_neg_one, ← Real.rpow_add hNp]; congr 1; ring
        rw [e]
        have hinv : (N : ℝ)⁻¹ ≤ 1 / 4 := by
          rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hN4
        have hpos : 0 ≤ (N : ℝ) ^ (-D) * (N : ℝ) ^ (-D) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hinv hpos]
      have : μ.real B₀ ≤ (N : ℝ) ^ (-D) / 2 :=
        hB₀P.trans ((div_le_div_of_nonneg_right hreal ht.le).trans hkey)
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ B₀)]
      exact ENNReal.ofReal_le_ofReal this
    have hP2 : μ ({ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2} \ G) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) := by
      have h8 := hN₂ N hNN₂ F E hC
      refine (measure_mono ?_).trans (h8.trans (ENNReal.ofReal_le_ofReal ?_))
      · intro ω ⟨hb, hnG⟩ hall
        apply hnG
        refine ⟨hb, fun j hj => ?_⟩
        have hgap := (hall s hsI).1 i j hj
        have hd : (ℓ : ℝ) ≤ labelDist i j := by exact_mod_cast hj
        have hℓpos : (0 : ℝ) < ℓ := by linarith [Real.rpow_pos_of_pos hNp (1 - (1 / 100 : ℝ) / 3)]
        have hgl : c₂ * ℓ / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| :=
          le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hc₂.le) hNp.le) hgap
        have hgp : 0 < c₂ * ℓ / N := by positivity
        have hpos : 0 < (N : ℝ) * (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) ^ 2 := by
          have : 0 < |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| := lt_of_lt_of_le hgp hgl
          have h2 : 0 < (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) ^ 2 := by
            rw [← sq_abs]; positivity
          positivity
        unfold flowRate
        rw [inv_le_one₀ hpos]
        have hsq : (c₂ * ℓ / N) ^ 2 ≤ (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) ^ 2 := by
          rw [← sq_abs (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j)]
          exact pow_le_pow_left₀ hgp.le hgl 2
        -- `N (c₂ℓ/N)² = c₂²ℓ²/N ≥ 1`
        have hℓ2' : (N : ℝ) ^ (1 - (2 / 300 : ℝ)) * N ≤ ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_add_one hNp.ne']
          exact le_of_eq (by congr 1; norm_num)
        have hl4 : ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)) ^ 2 ≤ 4 * (ℓ : ℝ) ^ 2 := by
          have h0 : 0 ≤ (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) := by positivity
          nlinarith [hℓge]
        have hmain : (N : ℝ) ≤ c₂ ^ 2 * (ℓ : ℝ) ^ 2 := by
          have h1 : 4 / c₂ ^ 2 * N ≤ 4 * (ℓ : ℝ) ^ 2 :=
            le_trans (mul_le_mul_of_nonneg_right hℓN hNp.le) (hℓ2'.trans hl4)
          have hc2 : 0 < c₂ ^ 2 := by positivity
          have : 4 / c₂ ^ 2 * N * c₂ ^ 2 = 4 * N := by field_simp
          nlinarith
        calc (1 : ℝ) ≤ (N : ℝ) * (c₂ * ℓ / N) ^ 2 := by
              rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
              nlinarith
          _ ≤ (N : ℝ) * (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq hNp.le
      · have e : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hNp]; congr 1; ring
        rw [e]
        have hinv : (N : ℝ)⁻¹ ≤ 1 / 2 := by
          rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left hinv ht.le]
    calc μ B ≤ μ B₀ + μ ({ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2} \ G) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) :=
          add_le_add hP1 hP2
      _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · filter_upwards [hB₀] with ω hω hωB hbulk
    have hωB₀ : ω ∉ B₀ := fun h' => hωB (Or.inl h')
    have hG : ω ∈ G := by
      by_contra hG; exact hωB (Or.inr ⟨hbulk, hG⟩)
    have h := hω hωB₀
    have e : ∑ j, w j ω * (μ[X j | pathSigma F a a c]) ω = ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
        flowRate F a ω s i j * condMoment F a c q s (Pi.single j 1) ω := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [condMoment_single]
      by_cases hj : ℓ ≤ labelDist i j
      · have hw' : w j ω = flowRate F a ω s i j := by
          simp only [w, hj, ite_true]; exact Set.indicator_of_mem hG _
        rw [hw']; simp only [hj, ite_true]; rfl
      · have hw' : w j ω = 0 := by simp only [w, hj, ite_false]
        rw [hw']; simp only [hj, ite_false, zero_mul]
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    have e2 : (N : ℝ) ^ (2 - D) = (N : ℝ) * (N : ℝ) * (N : ℝ) ^ (-D) := by
      rw [show (2 : ℝ) - D = 1 + 1 + -D by ring, Real.rpow_add hNp, Real.rpow_add hNp,
        Real.rpow_one]
    simp only [Fintype.card_fin, Bq, bnd, e2]
    ring

end BlockBand.Palm.MomentFlow
