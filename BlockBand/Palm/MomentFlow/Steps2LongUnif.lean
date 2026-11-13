module

public import BlockBand.Palm.MomentFlow.Steps2LongCond
public import BlockBand.Palm.MomentFlow.Steps2Gap
public import BlockBand.Palm.MomentFlow.BridgeRelabel

/-!
# Long couplings averaged over `𝓛`, uniformly in time, for a regular version of the moments

* `measurableSet_forall_Icc_le`: if `f s` is `m`-measurable for every `s ∈ [a,c]` and
  `s ↦ f s ω` is continuous on `[a,c]` for every `ω`, then `{ω | ∀ s ∈ [a,c], f s ω ≤ b}` is
  `m`-measurable (countable dense subset of the subtype `[a,c]`).
* `hasSimpleSpectrum_of_injective`.
* **`long_coupling_uniform`** (hyp. `ExternalLocalGUE`, `MDEBranchIdentification`,
  `GaussianLpGradient`, `MultivariateGaussianIBP`, `∀ N, DysonBrownianMotion N`): on the short-flow
  scales, for every label `i` and **every** jointly regular version `Φ` of the one-particle
  conditional moments (`Φ σ δ_j =ᵐ condMoment F a c q σ δ_j` for each `σ ∈ [a,c]`, and a.s.
  continuous in `σ`, e.g. the version of `momentGeneratorBridge_start`): there is an `𝓛`-measurable
  `B` with `P(B) ≤ N^{-D}` such that a.e. off `B`, **for all** `s ∈ [a, c]` with
  `|λ_i(s) - E| < r₀/2`: `Σ_{|j-i|≥ℓ} c_ij(s) Φ(s, δ_j) ≤ (2N/(c₁ℓ)) Cst q*Γq + N^{2-D}‖q‖²`, and
  moreover `c_ij(s) ≤ 1` for all long pairs and all `s ∈ [a,c]` off `B`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.Palm

variable {N : ℕ}

/-- Closed conditions holding at all times of `[a,c]` define measurable sets. -/
theorem measurableSet_forall_Icc_le {Ω : Type*} {m : MeasurableSpace Ω} {a c : ℝ}
    {f : ℝ → Ω → ℝ} (hf : ∀ s ∈ Icc a c, Measurable[m] (f s))
    (hc : ∀ ω, ContinuousOn (fun s => f s ω) (Icc a c)) (b : ℝ) :
    MeasurableSet[m] {ω | ∀ s ∈ Icc a c, f s ω ≤ b} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc a c)
  have e : {ω | ∀ s ∈ Icc a c, f s ω ≤ b} = ⋂ d ∈ D, {ω | f (d : ℝ) ω ≤ b} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h d _ => h d d.2, fun h s hs => ?_⟩
    have hcl : IsClosed {x : Icc a c | f x ω ≤ b} :=
      isClosed_le ((hc ω).domRestrict) continuous_const
    have hsub : D ⊆ {x : Icc a c | f x ω ≤ b} := fun d hd => h d hd
    have : (⟨s, hs⟩ : Icc a c) ∈ closure D := hDd ⟨s, hs⟩
    exact (hcl.closure_subset_iff.2 hsub) this
  rw [e]
  exact MeasurableSet.biInter hDc fun d _ => (hf d d.2) measurableSet_Iic

theorem hasSimpleSpectrum_of_injective {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hinj : ∀ i j : Fin N, i ≠ j → freshEigenvalue K i ≠ freshEigenvalue K j) :
    HasSimpleSpectrum N K := by
  rw [hasSimpleSpectrum_iff_strictMono hK]
  exact (RelativeLocalization.freshEigenvalue_monotone hK).strictMono_of_injective
    fun i j h => by_contra fun hij => hinj i j hij h

theorem rpow_neg_succ_le_half {N : ℕ} (hN : (2 : ℝ) ≤ N) (D : ℝ) :
    (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 2 := by
  have hNp : (0 : ℝ) < N := by linarith
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  have e : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hNp]; congr 1; ring
  rw [e]
  have hinv : (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hN
  have := mul_le_mul_of_nonneg_left hinv ht.le
  linarith

theorem two_rpow_div_le {N : ℕ} (hN : (4 : ℝ) ≤ N) (D : ℝ) :
    2 * (N : ℝ) ^ (-(2 * D + 1)) / (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-D) / 2 := by
  have hNp : (0 : ℝ) < N := by linarith
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  rw [div_le_div_iff₀ ht (by norm_num)]
  have e : (N : ℝ) ^ (-(2 * D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [← Real.rpow_add hNp, ← Real.rpow_neg_one, ← Real.rpow_add hNp]; congr 1; ring
  rw [e]
  have hinv : (N : ℝ)⁻¹ ≤ 1 / 4 := by
    rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hN
  have hpos : 0 ≤ (N : ℝ) ^ (-D) * (N : ℝ) ^ (-D) := by positivity
  have := mul_le_mul_of_nonneg_left hinv hpos
  nlinarith

/-- A long gap `≥ c₂ℓ/N` gives `N(λ_i - λ_j)² ≥ 1` once `4/c₂² ≤ N^{1-2/300}`. -/
theorem one_le_N_gap_sq {N : ℕ} (hNp : (0 : ℝ) < N) {c₂ : ℝ} (hc₂ : 0 < c₂) {ℓ : ℕ}
    (hℓge : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2 ≤ ℓ)
    (hℓN : 4 / c₂ ^ 2 ≤ (N : ℝ) ^ (1 - (2 / 300 : ℝ))) {x : ℝ}
    (hgl : c₂ * ℓ / N ≤ |x|) : 1 ≤ (N : ℝ) * x ^ 2 := by
  have hℓpos : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓge
  have hgp : 0 < c₂ * ℓ / N := by positivity
  have hsq : (c₂ * ℓ / N) ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ hgp.le hgl 2
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
  have h1 : (1 : ℝ) ≤ (N : ℝ) * (c₂ * ℓ / N) ^ 2 := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hNp.le]

/-- **Long couplings averaged over `𝓛`, uniformly in time**, for any regular version `Φ`. -/
theorem long_coupling_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N) {A c r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε5 : ε < 1 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        ∀ q : Fin N → ℂ, ∀ i : Fin N, ∀ Φ : ℝ → Occ N → FlowSample N → ℝ,
          (∀ σ ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c, ∀ j : Fin N,
            Φ σ (Pi.single j 1) =ᵐ[flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ)))]
              condMoment F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c q σ (Pi.single j 1)) →
          (∀ᵐ ω ∂flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))), ∀ j : Fin N,
            ContinuousOn (fun σ => Φ σ (Pi.single j 1) ω)
              (Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c)) →
          ∃ B : Set (FlowSample N),
            MeasurableSet[pathSigma F (c - (N : ℝ) ^ (-(1 / 100 : ℝ)))
              (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c] B ∧
            flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            (∀ ω ∉ B, ∀ s ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c, ∀ j : Fin N,
              ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j →
              flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j ≤ 1) ∧
            ∀ᵐ ω ∂flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))), ω ∉ B →
              ∀ s ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c,
              |flowEigenvalue F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i - E| < r₀ / 2 →
              ∑ j ∈ Finset.univ.filter
                  (fun j => ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j),
                flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j *
                  Φ s (Pi.single j 1) ω ≤
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
      4 / c₂ ^ 2 ≤ (n : ℝ) ^ (1 - (2 / 300 : ℝ)) ∧
      (n : ℝ) ^ (-(1 / 100 : ℝ)) < c := by
    refine ((eventually_ge_atTop N₁).and (eventually_ge_atTop N₂)).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 4).and
      ((eventually_rpow_ge (by norm_num) _).and ((eventually_rpow_ge (by norm_num) _).and
      ((((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
        tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hK.1))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC q i Φ hΦv hΦc => ?_⟩
  obtain ⟨⟨hNN₁, hNN₂⟩, hN4, hℓ2, hℓN, hτc⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
  set a : ℝ := c - τ
  have ha : 0 < a := by simp only [a]; linarith
  set ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
  set μ := flowLaw N a
  have hℓge : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2 ≤ ℓ := by
    have h3 : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) < (ℓ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith [hℓ2, h3]
  have hℓpos : (0 : ℝ) < ℓ := by linarith [Real.rpow_pos_of_pos hNp (1 - (1 / 100 : ℝ) / 3)]
  have hℓ1 : 1 ≤ ℓ := by exact_mod_cast (show (1 : ℝ) ≤ ℓ by linarith)
  have hne : ∀ j : Fin N, ℓ ≤ labelDist i j → i ≠ j := by
    intro j hj hij; subst hij; simp [labelDist] at hj; omega
  -- the long-gap set `G` (all times, all long pairs `i, j`)
  set G : Set (FlowSample N) := {ω | ∀ j : Fin N, ℓ ≤ labelDist i j → ∀ s ∈ Icc a c,
    1 - (N : ℝ) * (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) ^ 2 ≤ 0}
  have hGm : MeasurableSet[pathSigma F a a c] G := by
    have e : G = ⋂ j : Fin N, {ω | ℓ ≤ labelDist i j → ∀ s ∈ Icc a c,
        1 - (N : ℝ) * (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) ^ 2 ≤ 0} := by
      ext ω; simp [G]
    rw [e]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hj : ℓ ≤ labelDist i j
    · simp only [hj, true_implies]
      refine measurableSet_forall_Icc_le (fun s hs => ?_) (fun ω => ?_) 0
      · exact measurable_const.sub (measurable_const.mul
          (((measurable_flowEigenvalue_pathSigma F a a c hs i).sub
            (measurable_flowEigenvalue_pathSigma F a a c hs j)).pow_const 2))
      · exact (continuous_const.sub (continuous_const.mul
          (((continuous_flowEigenvalue hC.1 a ω i).sub
            (continuous_flowEigenvalue hC.1 a ω j)).pow 2))).continuousOn
    · simp only [hj, false_implies, Set.ofPred_true, MeasurableSet.univ]
  have hGrate : ∀ ω ∈ G, ∀ s ∈ Icc a c, ∀ j : Fin N, ℓ ≤ labelDist i j →
      flowRate F a ω s i j ≤ 1 := by
    intro ω hω s hs j hj
    have h := hω j hj s hs
    unfold flowRate
    exact inv_le_one_of_one_le₀ (by linarith)
  -- the bad set of the pathwise bound
  obtain ⟨BadW, hBadWm, hBadWP, hBadW⟩ := hN₁ N hNN₁ F E hC q
  set Z : Set (FlowSample N) := {ω | ¬ (ω.1.IsHermitian ∧ ∀ σ : ℝ, a ≤ σ → ∀ i j : Fin N,
    i ≠ j → flowEigenvalue F a ω σ i ≠ flowEigenvalue F a ω σ j)}
  have hZ : μ Z = 0 := ae_iff.1 (ae_noCollision (hDBM N) hC.1 ha)
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
  set Bq : ℝ := (N : ℝ) * ∑ k, ‖q k‖ ^ 2
  have hBq : 0 ≤ Bq := by positivity
  -- weights at time `s`
  set w : ℝ → Fin N → FlowSample N → ℝ := fun s j ω =>
    if ℓ ≤ labelDist i j then
      (G ∩ {ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2}).indicator
        (fun ω => flowRate F a ω s i j) ω else 0
  have hbulkm : ∀ s ∈ Icc a c, MeasurableSet[pathSigma F a a c]
      {ω : FlowSample N | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2} := fun s hs =>
    (Measurable.comp (g := fun x : ℝ => |x - E|) (by fun_prop)
      (measurable_flowEigenvalue_pathSigma F a a c hs i)) measurableSet_Iic
  have hw : ∀ s ∈ Icc a c, ∀ j, StronglyMeasurable[pathSigma F a a c] (w s j) := by
    intro s hs j
    by_cases hj : ℓ ≤ labelDist i j
    · have : w s j = (G ∩ {ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2}).indicator
          (fun ω => flowRate F a ω s i j) := by funext ω; simp [w, hj]
      rw [this]
      exact ((measurable_flowRate_pathSigma F a a c hs i j).indicator
        (hGm.inter (hbulkm s hs))).stronglyMeasurable
    · have : w s j = fun _ => 0 := by funext ω; simp [w, hj]
      rw [this]; exact stronglyMeasurable_const
  have hw0 : ∀ s j ω, 0 ≤ w s j ω := by
    intro s j ω
    simp only [w]
    split_ifs
    · exact Set.indicator_nonneg (fun ω _ => flowRate_nonneg F a ω s i j) ω
    · exact le_rfl
  have hwK : ∀ s ∈ Icc a c, ∀ j ω, w s j ω ≤ 1 := by
    intro s hs j ω
    simp only [w]
    split_ifs with hj
    · by_cases hω : ω ∈ G ∩ {ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2}
      · rw [Set.indicator_of_mem hω]; exact hGrate ω hω.1 s hs j hj
      · rw [Set.indicator_of_notMem hω]; norm_num
    · norm_num
  have hX : ∀ s j, Measurable (fun ω => flowOverlap F a q s j ω) := fun s j =>
    measurable_flowOverlap F a q s j
  have hX0 : ∀ s j ω, 0 ≤ flowOverlap F a q s j ω := fun s j ω => by
    simp only [flowOverlap]; positivity
  have hXB : ∀ s j ω, flowOverlap F a q s j ω ≤ Bq := fun s j ω =>
    FreshPalmAssembly.overlap_le_nsq _ q j
  have hgood : ∀ s ∈ Icc a c, ∀ ω ∉ Bad, ∑ j, w s j ω * flowOverlap F a q s j ω ≤ bnd := by
    intro s hs ω hω
    have hω' : ω ∉ BadW ∪ Z := fun h' => hω (subset_toMeasurable _ _ h')
    have hωW : ω ∉ BadW := fun h' => hω' (Or.inl h')
    have hωZ : ω ∉ Z := fun h' => hω' (Or.inr h')
    simp only [Z, Set.mem_ofPred_eq, not_not] at hωZ
    by_cases hG : ω ∈ G ∩ {ω | |flowEigenvalue F a ω s i - E| ≤ r₀ / 2}
    · have e : ∑ j, w s j ω * flowOverlap F a q s j ω =
          ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
            flowRate F a ω s i j * flowOverlap F a q s j ω := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : ℓ ≤ labelDist i j
        · simp [w, hj, Set.indicator_of_mem hG]
        · simp [w, hj]
      rw [e]
      have hsimp : HasSimpleSpectrum N (flowMatrix F a ω s) :=
        hasSimpleSpectrum_of_injective (flowMatrix_isHermitian hC.1 a hωZ.1 s)
          fun k l hkl => hωZ.2 s hs.1 k l hkl
      exact hBadW ω hωW hωZ.1 s hs hsimp i hG.2
    · have e : ∀ j, w s j ω = 0 := fun j => by
        simp only [w]; split_ifs
        · exact Set.indicator_of_notMem hG _
        · rfl
      simp only [e, zero_mul, Finset.sum_const_zero]
      exact hbnd
  -- one `𝓛`-set for the conditional probability of `Bad`
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  obtain ⟨B₀, hB₀m, hB₀P, hB₀⟩ := condExp_indicator_compl_small (μ := μ) (pathSigma_le F a a c)
    hBadm.compl ht
  rw [compl_compl] at hB₀P hB₀
  -- a countable dense set of times
  obtain ⟨Dt, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc a c)
  have : Countable Dt := hDc.to_subtype
  have hae : ∀ᵐ ω ∂μ, ∀ d : Dt, ∑ j, w (d : Icc a c) j ω *
      (μ[fun ω => flowOverlap F a q ((d : Icc a c) : ℝ) j ω | pathSigma F a a c]) ω ≤
      bnd + Fintype.card (Fin N) * 1 * Bq *
        (μ[Bad.indicator (fun _ => (1 : ℝ)) | pathSigma F a a c]) ω := by
    refine ae_all_iff.2 fun d => ?_
    have hd := (d : Icc a c).2
    exact condExp_weighted_sum_le (μ := μ) (pathSigma_le F a a c) (w (d : Icc a c))
      (fun j ω => flowOverlap F a q ((d : Icc a c) : ℝ) j ω) hbnd zero_le_one hBq
      (hw _ hd) (hw0 _) (hwK _ hd) (hX _) (hX0 _) (hXB _) hBadm (hgood _ hd)
  have hver : ∀ᵐ ω ∂μ, ∀ d : Dt, ∀ j : Fin N,
      (μ[fun ω => flowOverlap F a q ((d : Icc a c) : ℝ) j ω | pathSigma F a a c]) ω =
        Φ ((d : Icc a c) : ℝ) (Pi.single j 1) ω := by
    refine ae_all_iff.2 fun d => ae_all_iff.2 fun j => ?_
    have h := hΦv _ (d : Icc a c).2 j
    rw [condMoment_single] at h
    filter_upwards [h] with ω hω
    exact hω.symm
  -- the exceptional `𝓛`-set
  set B := B₀ ∪ Gᶜ
  have hP2 : μ Gᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) := by
    have h8 := hN₂ N hNN₂ F E hC
    refine (measure_mono ?_).trans (h8.trans (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hnG hall
      apply hnG
      intro j hj s hs
      have hgap := (hall s hs).1 i j hj
      have hd : (ℓ : ℝ) ≤ labelDist i j := by exact_mod_cast hj
      have hgl : c₂ * ℓ / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| :=
        le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hc₂.le) hNp.le) hgap
      have := one_le_N_gap_sq hNp hc₂ hℓge hℓN hgl
      linarith
    · exact rpow_neg_succ_le_half (by linarith) D
  have hP1 : μ B₀ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) := by
    have hreal : μ.real Bad ≤ 2 * (N : ℝ) ^ (-(2 * D + 1)) := by
      have := ENNReal.toReal_mono (by finiteness) hBadP
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.toReal_ofReal
        (by positivity)] at this
      simpa [Measure.real, two_mul] using this
    have hkey := two_rpow_div_le hN4 D
    have : μ.real B₀ ≤ (N : ℝ) ^ (-D) / 2 :=
      hB₀P.trans ((div_le_div_of_nonneg_right hreal ht.le).trans hkey)
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ B₀)]
    exact ENNReal.ofReal_le_ofReal this
  refine ⟨B, hB₀m.union hGm.compl, ?_, ?_, ?_⟩
  · calc μ B ≤ μ B₀ + μ Gᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) :=
          add_le_add hP1 hP2
      _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · intro ω hω s hs j hj
    exact hGrate ω (not_not.1 fun h => hω (Or.inr h)) s hs j hj
  · filter_upwards [hae, hver, hΦc] with ω hωa hωv hωc hωB s hs hbulk
    have hωB₀ : ω ∉ B₀ := fun h' => hωB (Or.inl h')
    have hG : ω ∈ G := not_not.1 fun h => hωB (Or.inr h)
    set M : ℝ := bnd + (N : ℝ) ^ (2 - D) * ∑ k, ‖q k‖ ^ 2
    have hMeq : bnd + Fintype.card (Fin N) * 1 * Bq * (N : ℝ) ^ (-D) = M := by
      have e2 : (N : ℝ) ^ (2 - D) = (N : ℝ) * (N : ℝ) * (N : ℝ) ^ (-D) := by
        rw [show (2 : ℝ) - D = 1 + 1 + -D by ring, Real.rpow_add hNp, Real.rpow_add hNp,
          Real.rpow_one]
      simp only [M, Fintype.card_fin, Bq, e2]; ring
    -- the sum as a function on the subtype `[a,c]`
    set f : Icc a c → ℝ := fun x => ∑ j ∈ Finset.univ.filter (fun j => ℓ ≤ labelDist i j),
      flowRate F a ω x i j * Φ x (Pi.single j 1) ω
    have hfc : Continuous f := by
      refine continuous_finsetSum _ fun j hj => ?_
      have hj' := (Finset.mem_filter.1 hj).2
      have hrate : Continuous fun x : Icc a c => flowRate F a ω x i j := by
        unfold flowRate
        refine Continuous.inv₀ (continuous_const.mul ((((continuous_flowEigenvalue hC.1 a ω i).sub
          (continuous_flowEigenvalue hC.1 a ω j)).pow 2).comp continuous_subtype_val)) fun x => ?_
        have h := hG j hj' x x.2
        have : (0 : ℝ) < (N : ℝ) * (flowEigenvalue F a ω x i - flowEigenvalue F a ω x j) ^ 2 := by
          linarith
        exact this.ne'
      exact hrate.mul ((hωc j).domRestrict)
    set U : Set (Icc a c) := {x | |flowEigenvalue F a ω x i - E| < r₀ / 2}
    have hU : IsOpen U :=
      isOpen_lt ((continuous_abs.comp ((continuous_flowEigenvalue hC.1 a ω i).sub
        continuous_const)).comp continuous_subtype_val) continuous_const
    have hDU : ∀ x ∈ U ∩ Dt, f x ≤ M := by
      intro x ⟨hxU, hxD⟩
      have h1 := hωa ⟨x, hxD⟩
      have h2 : (μ[Bad.indicator (fun _ => (1 : ℝ)) | pathSigma F a a c]) ω < (N : ℝ) ^ (-D) :=
        hB₀ ω hωB₀
      have hGx : ω ∈ G ∩ {ω | |flowEigenvalue F a ω x i - E| ≤ r₀ / 2} := ⟨hG, le_of_lt (show |flowEigenvalue F a ω x i - E| < r₀ / 2 from hxU)⟩
      have e : ∑ j, w x j ω * (μ[fun ω => flowOverlap F a q (x : ℝ) j ω |
          pathSigma F a a c]) ω = f x := by
        simp only [f]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hωv ⟨x, hxD⟩ j]
        by_cases hj : ℓ ≤ labelDist i j
        · have hw' : w x j ω = flowRate F a ω x i j := by
            simp only [w, hj, ite_true]; exact Set.indicator_of_mem hGx _
          rw [hw']; simp only [hj, ite_true]
        · have hw' : w x j ω = 0 := by simp only [w, hj, ite_false]
          rw [hw']; simp only [hj, ite_false, zero_mul]
      change ∑ j, w x j ω * (μ[fun ω => flowOverlap F a q (x : ℝ) j ω |
          pathSigma F a a c]) ω ≤ _ at h1
      rw [e] at h1
      rw [← hMeq]
      refine h1.trans ?_
      have hc0 : (0 : ℝ) ≤ Fintype.card (Fin N) * 1 * Bq := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2.le hc0]
    have hcl : IsClosed {x : Icc a c | f x ≤ M} := isClosed_le hfc continuous_const
    have hsU : (⟨s, hs⟩ : Icc a c) ∈ U := by
      show |flowEigenvalue F a ω s i - E| < r₀ / 2
      exact hbulk
    have hsub : U ⊆ closure (U ∩ Dt) := hDd.open_subset_closure_inter hU
    have hmem : (⟨s, hs⟩ : Icc a c) ∈ {x : Icc a c | f x ≤ M} :=
      hcl.closure_subset_iff.2 hDU (hsub hsU)
    exact hmem

/-- The additive error `N^{2-D}‖q‖²` of the conditional long-coupling bounds is a multiple of
`q*Γq`: it is `≤ N^{2-D+2max(A,1)}/(v₀ lowConst) · q*Γq`. -/
theorem additive_error_le_gamma {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    (q : Fin N → ℂ) (D : ℝ) :
    (N : ℝ) ^ (2 - D) * ∑ k, ‖q k‖ ^ 2 ≤
      (N : ℝ) ^ (2 - D + 2 * max A 1) / (v₀ * CoarseRelative.lowConst c₀ s₀ v₀) *
        quadForm (freshGamma F c₀ E) q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := nsq_le_of_gamma hN hK hC q
  have h0 : 0 ≤ (N : ℝ) ^ (2 - D) := by positivity
  calc (N : ℝ) ^ (2 - D) * ∑ k, ‖q k‖ ^ 2 = (N : ℝ) ^ (2 - D) * CoarseRelative.nsq q := rfl
    _ ≤ (N : ℝ) ^ (2 - D) * ((N : ℝ) ^ (2 * max A 1) * quadForm (freshGamma F c₀ E) q /
          (v₀ * CoarseRelative.lowConst c₀ s₀ v₀)) := mul_le_mul_of_nonneg_left h h0
    _ = _ := by rw [Real.rpow_add hNp]; ring

end BlockBand.Palm.MomentFlow
