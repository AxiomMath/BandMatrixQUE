module

public import BlockBand.Palm.MomentFlow.PropMloc
public import BlockBand.Palm.MomentFlow.PropLong
public import BlockBand.Palm.MomentFlow.PropLongShort

/-!
# The `r ≥ 2` local long-jump bound, uniform in time

* `four_rpow_le`: `4 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 4`.
* **`d6_uniform`**: for every `RegVersion Φ`, a.e. off one 𝓛-measurable `B` (`P(B) ≤ N^{-D}`):
  for all bulk `ξ` (particles within `r₀/2` of `E` on `[a, c₀]`), occupied `i` and all times `σ`,
  `Σ_{|j-i|≥ℓ} c_ij(σ)(ξ_j+1)Φ(σ, ξ^{ij}) ≤ (Cov N^{4ε})^{r-1}(2N/(c₁ℓ))Cst + N(N/c₂²)B₁^r N^{-D}`.
  Proof: removal identity (`condExp_remove_mul_ne`) at a countable dense set of times;
  pull-out (`condExp_weighted_sum_le`) with 𝓛-measurable weights `1_{bulk} min(c_ij, N/c₂²)`;
  pathwise `P_i ≤ (Cov N^{4ε})^{r-1}` (overlap line) times `Σ_long c_ij X_j ≤ (2N/(c₁ℓ))Cst`
  (`long_coupling_event_bound_measurable`); long rates `≤ N/c₂²` on the separation event of
  `longCoupling_good`; continuity in `σ` on collision-free paths.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.Palm BlockBand.Palm.CoarseRelative

variable {N : ℕ}

theorem four_rpow_le {N : ℕ} (hN : (4 : ℝ) ≤ N) (D : ℝ) :
    4 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  have hNp : (0 : ℝ) < N := by linarith
  have e : (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hNp]; congr 1; ring
  rw [e]
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  have : 4 * (N : ℝ)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hNp]; exact hN
  nlinarith

/-- **Local long-jump bound, uniform in time** (`r ≥ 2`; from `ExternalLocalGUE`,
`MDEBranchIdentification`, `GaussianLpGradient`, `MultivariateGaussianIBP`,
`DysonBrownianMotion`). For every `RegVersion Φ`, a.e. off one 𝓛-measurable `B`
(`P(B) ≤ N^{-D}`): for every `ξ` in the `r`-sector whose particles stay within `r₀/2` of `E` on
`[a, c₀]`, every occupied `i` and every time `σ`,
`Σ_{|j-i| ≥ ℓ} c_ij(σ) (ξ_j + 1) Φ(σ, ξ^{ij}) ≤ (Cov N^{4ε})^{r-1} · (2N/(c₁ℓ)) Cst + N (N/c₂²) B₁^r N^{-D}`,
`B₁ = max(1, N‖q‖²)`. (Removal identity: `(ξ_j+1) F_r(ξ^{ij}) = E[P_i X_j | 𝓛]`; pathwise
`P_i ≤ (Cov N^{4ε})^{r-1}` on the bulk and `Σ_long c_ij X_j ≤ (2N/(c₁ℓ)) Cst`.) -/
theorem d6_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N) {A c₀ r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε5 : ε < 1 / 5) :
    ∃ c₁ c₂ Cst Cov : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ Cst ∧ 0 ≤ Cov ∧
      ∀ (r : ℕ) (D : ℝ), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
          flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ Φ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q r Φ →
            ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B → ∀ ξ ∈ sector N r, ∀ i : Fin N, 0 < ξ i →
              (∀ k : Fin N, 0 < ξ k → ∀ σ' ∈ Icc (c₀ - cmTau N) c₀,
                  |flowEigenvalue F (c₀ - cmTau N) ω σ' k - E| ≤ r₀ / 2) →
              ∀ σ ∈ Icc (c₀ - cmTau N) c₀,
                ∑ j ∈ univ.filter (fun j => cmEll N ≤ labelDist i j),
                    flowRate F (c₀ - cmTau N) ω σ i j * ((ξ j : ℝ) + 1) * Φ σ (move ξ i j) ω ≤
                  (Cov * (N : ℝ) ^ (4 * ε)) ^ (r - 1) *
                      (2 / (c₁ * cmEll N / N) * Cst) +
                    (N : ℝ) * ((N : ℝ) / c₂ ^ 2) * max 1 ((N : ℝ) * nsq q) ^ r *
                      (N : ℝ) ^ (-D) := by
  classical
  obtain ⟨Cov, hCov, hOv⟩ := overlap_event_uniform hELG hMDE hLp (A := A) hK (ε := ε) hε
    (by linarith)
  obtain ⟨c₁, hc₁, Cst, hCst, hLE⟩ :=
    long_coupling_event_bound_measurable hELG hMDE hLp hIBP (A := A) hK hε hε5
  obtain ⟨c₂, C₂, hc₂, -, hSep⟩ := longCoupling_good hLp hIBP (A := A) hK
  refine ⟨c₁, c₂, Cst, Cov, hc₁, hc₂, hCst, hCov, fun r D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hOv (2 * D + 1)
  obtain ⟨N₂, hN₂⟩ := hLE (2 * D + 1)
  obtain ⟨N₃, hN₃⟩ := hSep (D + 1)
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 ((hτ0.eventually (ge_mem_nhds hK.2.2.2.1)).and
    ((eventually_ge_atTop (max (max N₁ N₂) (max N₃ 4)))))
  refine ⟨N₄, fun N hN F E hC q hq => ?_⟩
  obtain ⟨hτs, hNN⟩ := hN₄ N hN
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hNN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hNN)
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hNN)
  have hN4 : 4 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hNN)
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hNpos : 0 < N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  set τ := cmTau N with hτdef
  set a := c₀ - τ
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hNp _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hNpos) (by norm_num)
  have hτs' : τ ≤ s₀ := hτs
  have ha0 : 0 < a := by simp only [a]; linarith [hK.2.2.2.2.1, hK.1]
  have hac : a ≤ c₀ := by linarith
  set ℓ := cmEll N
  have hℓ1 : 1 ≤ ℓ := Nat.le_floor (by
    rw [Nat.cast_one]; exact Real.one_le_rpow (by exact_mod_cast hNpos) (by norm_num))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  -- bad events
  obtain ⟨Bov, hBovm, hPBov, hBov⟩ := hN₁ N hN1 F E hC a τ ha0.le hτpos hτ1
    (by simp only [a]; linarith) (by simp only [a]; linarith) q
  obtain ⟨BL, hBLm, hPBL, hBL⟩ := hN₂ N hN2 F E hC q
  obtain ⟨Bs, hBsm, hPBs, hBs⟩ := hN₃ N hN3 F E hC
  set μ := flowLaw N a
  have hm := pathSigma_le F a a c₀
  set Null : Set (FlowSample N) := {ω | ¬ (ω.1.IsHermitian ∧ ∀ σ : ℝ, a ≤ σ → ∀ i j : Fin N,
    i ≠ j → flowEigenvalue F a ω σ i ≠ flowEigenvalue F a ω σ j)}
  have hNull : μ Null = 0 := by
    have h := ae_noCollision (hDBM N) hC.1 ha0
    rwa [ae_iff] at h
  set Bad := Bov ∪ BL ∪ toMeasurable μ Null
  have hBadm : MeasurableSet Bad := (hBovm.union hBLm).union (measurableSet_toMeasurable _ _)
  have hPBad : μ.real Bad ≤ 3 * (N : ℝ) ^ (-(2 * D + 1)) := by
    have h1 : μ Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(2 * D + 1))) +
        (ENNReal.ofReal ((N : ℝ) ^ (-(2 * D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(2 * D + 1)))) := by
      refine (measure_union_le _ _).trans ?_
      rw [measure_toMeasurable, hNull, add_zero]
      exact (measure_union_le _ _).trans (add_le_add hPBov hPBL)
    have h2 : μ Bad ≤ ENNReal.ofReal (3 * (N : ℝ) ^ (-(2 * D + 1))) := by
      refine h1.trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  obtain ⟨B₀, hB₀, hμB₀, hoff⟩ := condExp_indicator_compl_small (μ := μ) hm hBadm.compl ht
  rw [compl_compl] at hμB₀ hoff
  refine ⟨B₀ ∪ Bs, hB₀.union hBsm, ?_, fun Φ hΦ => ?_⟩
  · have h1 : μ.real B₀ ≤ 3 * (N : ℝ) ^ (-(D + 1)) := by
      refine hμB₀.trans ?_
      rw [div_le_iff₀ ht]
      have : (N : ℝ) ^ (-(2 * D + 1)) = (N : ℝ) ^ (-(D + 1)) * (N : ℝ) ^ (-D) := by
        rw [← Real.rpow_add hNp]; ring_nf
      rw [this] at hPBad; linarith
    have h1' : μ B₀ ≤ ENNReal.ofReal (3 * (N : ℝ) ^ (-(D + 1))) := by
      rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal h1
    refine (measure_union_le _ _).trans ((add_le_add h1' hPBs).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith [four_rpow_le hN4r D])
  -- constants
  set B₁ : ℝ := max 1 ((N : ℝ) * nsq q)
  have hB₁ : 1 ≤ B₁ := le_max_left _ _
  set bP : ℝ := (Cov * (N : ℝ) ^ (4 * ε)) ^ (r - 1)
  set bL : ℝ := 2 / (c₁ * ℓ / N) * Cst
  have hbP : 0 ≤ bP := by positivity
  have hbL : 0 ≤ bL := by positivity
  set Kc : ℝ := (N : ℝ) / c₂ ^ 2
  have hKc : 0 ≤ Kc := by positivity
  set X : ℝ → FlowSample N → Fin N → ℝ := fun σ ω k => flowOverlap F a q σ k ω
  have hX0 : ∀ σ ω k, 0 ≤ X σ ω k := fun σ ω k => by simp only [X, flowOverlap]; positivity
  have hXB : ∀ σ ω k, X σ ω k ≤ B₁ := fun σ ω k =>
    (FreshPalmAssembly.overlap_le_nsq (flowMatrix F a ω σ) q k).trans (le_max_right _ _)
  set S : Occ N → Set (FlowSample N) := fun ξ => {ω | ∀ v ∈ Icc a c₀, ∀ k : Fin N, 0 < ξ k →
    |flowEigenvalue F a ω v k - E| ≤ r₀ / 2}
  have hSm : ∀ ξ, MeasurableSet[pathSigma F a a c₀] (S ξ) := fun ξ =>
    measurableSet_bulk F hC.1 le_rfl le_rfl ξ E (r₀ / 2)
  -- weights and observables
  set w : ℝ → Occ N → Fin N → Fin N → FlowSample N → ℝ := fun σ ξ i j ω =>
    (S ξ).indicator (fun ω => if ℓ ≤ labelDist i j then min (flowRate F a ω σ i j) Kc else 0) ω
  set Y : ℝ → Occ N → Fin N → Fin N → FlowSample N → ℝ := fun σ ξ i j ω =>
    momentMonomial (X σ ω) (remove ξ i) * X σ ω j
  have hwm : ∀ σ ∈ Icc a c₀, ∀ ξ i j, StronglyMeasurable[pathSigma F a a c₀] (w σ ξ i j) := by
    intro σ hσ ξ i j
    refine (Measurable.indicator ?_ (hSm ξ)).stronglyMeasurable
    by_cases hl : ℓ ≤ labelDist i j
    · simp only [hl, ite_true]
      exact (measurable_flowRate_pathSigma F a a c₀ hσ i j).min measurable_const
    · simp only [hl, ite_false]; exact measurable_const
  have hw0 : ∀ σ ξ i j ω, 0 ≤ w σ ξ i j ω := fun σ ξ i j ω => by
    simp only [w]
    refine indicator_nonneg (fun ω _ => ?_) ω
    split_ifs
    · exact le_min (flowRate_nonneg F a ω σ i j) hKc
    · exact le_rfl
  have hwK : ∀ σ ξ i j ω, w σ ξ i j ω ≤ Kc := fun σ ξ i j ω => by
    simp only [w]
    by_cases hS : ω ∈ S ξ
    · rw [indicator_of_mem hS]; split_ifs
      · exact min_le_right _ _
      · exact hKc
    · rw [indicator_of_notMem hS]; exact hKc
  have hYm : ∀ σ ξ i j, Measurable (Y σ ξ i j) := fun σ ξ i j =>
    ((measurable_momentMonomial _).comp (Measurable.of_eval fun k =>
      measurable_flowOverlap F a q σ k)).mul (measurable_flowOverlap F a q σ j)
  have hY0 : ∀ σ ξ i j ω, 0 ≤ Y σ ξ i j ω := fun σ ξ i j ω =>
    mul_nonneg (momentMonomial_nonneg (hX0 σ ω) _) (hX0 σ ω j)
  have hYB : ∀ σ ξ, ξ ∈ sector N r → ∀ i, 0 < ξ i → ∀ j ω, Y σ ξ i j ω ≤ B₁ ^ r := by
    intro σ ξ hξ i hi j ω
    have h1 := momentMonomial_le_pow (hX0 σ ω) (remove_mem_sector hξ hi) fun k _ => hXB σ ω k
    have hr1 : 1 ≤ r := by
      have := (mem_sector.1 hξ) ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    calc Y σ ξ i j ω ≤ B₁ ^ (r - 1) * B₁ :=
          mul_le_mul h1 (hXB σ ω j) (hX0 σ ω j) (by positivity)
      _ = B₁ ^ r := by rw [← pow_succ]; congr 1; omega
  -- pathwise bound
  have hgood : ∀ σ ∈ Icc a c₀, ∀ ξ ∈ sector N r, ∀ i, 0 < ξ i → ∀ ω ∉ Bad,
      ∑ j, w σ ξ i j ω * Y σ ξ i j ω ≤ bP * bL := by
    intro σ hσ ξ hξ i hi ω hω
    by_cases hS : ω ∈ S ξ
    · have hω1 : ω ∉ Bov := fun h => hω (Or.inl (Or.inl h))
      have hω2 : ω ∉ BL := fun h => hω (Or.inl (Or.inr h))
      have hω3 : ω ∉ Null := fun h => hω (Or.inr (subset_toMeasurable _ _ h))
      simp only [Null, mem_ofPred_eq, not_not] at hω3
      have hH := hω3.1
      have hsimp : HasSimpleSpectrum N (flowMatrix F a ω σ) :=
        hasSimpleSpectrum_of_injective (BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hC.1 a hH σ)
          fun i j hij => hω3.2 σ hσ.1 i j hij
      have hP : momentMonomial (X σ ω) (remove ξ i) ≤ bP := by
        refine momentMonomial_le_pow (hX0 σ ω) (remove_mem_sector hξ hi) fun k hk => ?_
        have hk' : 0 < ξ k := by
          unfold remove at hk
          by_cases hki : k = i
          · subst hki; exact hi
          · rwa [Function.update_of_ne hki] at hk
        have := hBov ω hω1 hH σ ⟨hσ.1, by simp only [a]; linarith [hσ.2]⟩ hsimp k (hS σ hσ k hk')
        rw [hq, mul_one] at this
        exact this
      have hL := hBL ω hω2 hH σ hσ hsimp i (hS σ hσ i hi)
      rw [hq, mul_one] at hL
      calc ∑ j, w σ ξ i j ω * Y σ ξ i j ω
          ≤ ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
              flowRate F a ω σ i j * (momentMonomial (X σ ω) (remove ξ i) * X σ ω j) := by
            rw [Finset.sum_filter]
            refine Finset.sum_le_sum fun j _ => ?_
            simp only [w, Y, indicator_of_mem hS]
            split_ifs
            · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hY0 σ ξ i j ω)
            · simp
        _ = momentMonomial (X σ ω) (remove ξ i) *
              ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j), flowRate F a ω σ i j * X σ ω j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ bP * bL := mul_le_mul hP hL (Finset.sum_nonneg fun j _ =>
              mul_nonneg (flowRate_nonneg F a ω σ i j) (hX0 σ ω j)) hbP
    · have : ∀ j, w σ ξ i j ω = 0 := fun j => by simp only [w, indicator_of_notMem hS]
      simp only [this, zero_mul, Finset.sum_const_zero]
      exact mul_nonneg hbP hbL
  -- dense times
  obtain ⟨Dt, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc a c₀)
  have : Countable Dt := hDc.to_subtype
  have hae : ∀ᵐ ω ∂μ, ∀ d : Dt, ∀ ξ : sector N r, ∀ i : Fin N, 0 < (ξ : Occ N) i →
      (∑ j, w (d : Icc a c₀) ξ i j ω * (μ[Y (d : Icc a c₀) ξ i j | pathSigma F a a c₀]) ω ≤
        bP * bL + Fintype.card (Fin N) * Kc * B₁ ^ r *
          (μ[Bad.indicator (fun _ => (1 : ℝ)) | pathSigma F a a c₀]) ω) ∧
      ∀ j : Fin N, i ≠ j → (μ[Y (d : Icc a c₀) ξ i j | pathSigma F a a c₀]) ω =
        ((ξ : Occ N) j + 1) * Φ ((d : Icc a c₀) : ℝ) (move ξ i j) ω := by
    refine ae_all_iff.2 fun d => ae_all_iff.2 fun ξ => ae_all_iff.2 fun i => ?_
    by_cases hi : 0 < (ξ : Occ N) i
    · have hd := (d : Icc a c₀).2
      have h1 := condExp_weighted_sum_le (μ := μ) hm (w (d : Icc a c₀) ξ i)
        (Y (d : Icc a c₀) ξ i) (mul_nonneg hbP hbL) hKc (by positivity) (hwm _ hd ξ i)
        (hw0 _ ξ i) (hwK _ ξ i) (hYm _ ξ i) (hY0 _ ξ i) (hYB _ ξ ξ.2 i hi) hBadm
        (hgood _ hd ξ ξ.2 i hi)
      have h2 : ∀ᵐ ω ∂μ, ∀ j : Fin N, i ≠ j →
          (μ[Y (d : Icc a c₀) ξ i j | pathSigma F a a c₀]) ω =
            ((ξ : Occ N) j + 1) * Φ ((d : Icc a c₀) : ℝ) (move ξ i j) ω := by
        refine ae_all_iff.2 fun j => ?_
        by_cases hij : i = j
        · exact Eventually.of_forall fun ω h => absurd hij h
        · have e1 := condExp_remove_mul_ne (m := pathSigma F a a c₀) μ
            (fun ω => X (d : Icc a c₀) ω) (ξ : Occ N) hij
          have e2 := hΦ.1 _ hd (move ξ i j) (move_mem_sector ξ.2 hij hi)
          filter_upwards [e1, e2] with ω h1 h2
          intro _
          simp only [Y]
          rw [h1, Pi.smul_apply, smul_eq_mul, h2]
          rfl
      filter_upwards [h1, h2] with ω h1 h2 _
      exact ⟨h1, h2⟩
    · exact Eventually.of_forall fun ω h => absurd h hi
  filter_upwards [hae, hΦ.2, ae_noCollision (hDBM N) hC.1 ha0] with ω hω hsol hcol hωB ξ hξ i hi
    hbulk σ hσ
  have hωB₀ : ω ∉ B₀ := fun h => hωB (Or.inl h)
  have hωBs : ω ∉ Bs := fun h => hωB (Or.inr h)
  have hsmall := hoff ω hωB₀
  have hS : ω ∈ S ξ := fun v hv k hk => hbulk k hk v hv
  -- on `Bsᶜ`, long rates are `≤ Kc`
  have hrate : ∀ v ∈ Icc a c₀, ∀ j, ℓ ≤ labelDist i j → flowRate F a ω v i j ≤ Kc := by
    intro v hv j hj
    have hsep := (hBs ω hωBs v hv).1 i j hj
    have hlj : (1 : ℝ) ≤ labelDist i j := le_trans hℓr (by exact_mod_cast hj)
    have hg : c₂ / N ≤ |flowEigenvalue F a ω v i - flowEigenvalue F a ω v j| := by
      refine le_trans ?_ hsep
      rw [div_le_div_iff_of_pos_right hNp]; nlinarith
    unfold flowRate
    have hgp : 0 < c₂ / N := by positivity
    have hsq : (c₂ / N) ^ 2 ≤ (flowEigenvalue F a ω v i - flowEigenvalue F a ω v j) ^ 2 := by
      rw [← sq_abs (flowEigenvalue F a ω v i - _)]; exact pow_le_pow_left₀ hgp.le hg 2
    have hpos : 0 < (N : ℝ) * (flowEigenvalue F a ω v i - flowEigenvalue F a ω v j) ^ 2 :=
      mul_pos hNp (lt_of_lt_of_le (by positivity) hsq)
    rw [inv_le_comm₀ hpos (by positivity)]
    simp only [Kc]
    rw [inv_div]
    calc c₂ ^ 2 / N = (N : ℝ) * (c₂ / N) ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq hNp.le
  -- continuity of both sides
  have hgap : ∀ x ∈ Icc a c₀, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l :=
    fun x hx k l hkl => hcol.2 x hx.1 k l hkl
  have hcr := continuousOn_flowRate hC.1 a ω hgap
  have hLc : ContinuousOn (fun σ => ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      flowRate F a ω σ i j * ((ξ j : ℝ) + 1) * Φ σ (move ξ i j) ω) (Icc a c₀) := by
    refine continuousOn_finsetSum _ fun j hj => ?_
    have hj' : ℓ ≤ labelDist i j := (Finset.mem_filter.1 hj).2
    have hij : i ≠ j := by
      intro h; subst h; simp [labelDist] at hj'; omega
    exact ((continuousOn_pi.1 (continuousOn_pi.1 hcr i) j).mul continuousOn_const).mul
      (hsol _ (move_mem_sector hξ hij hi)).1
  refine le_of_dense_open hDd hLc continuousOn_const continuousOn_const
    (u := fun _ => (0 : ℝ)) (δ := 1) (fun x hx _ => ?_) σ hσ zero_lt_one
  obtain ⟨h1, h2⟩ := hω ⟨x, hx⟩ ⟨ξ, hξ⟩ i hi
  have e : ∑ j, w x ξ i j ω * (μ[Y x ξ i j | pathSigma F a a c₀]) ω =
      ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
        flowRate F a ω x i j * ((ξ j : ℝ) + 1) * Φ x (move ξ i j) ω := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, indicator_of_mem hS]
    split_ifs with hj
    · have hij : i ≠ j := by
        intro h; subst h; simp [labelDist] at hj; omega
      rw [min_eq_left (hrate x x.2 j hj), h2 j hij]; ring
    · simp
  simp only at h1
  rw [e] at h1
  refine h1.trans ?_
  have hc0 : 0 ≤ (Fintype.card (Fin N) : ℝ) * Kc * B₁ ^ r := by positivity
  rw [Fintype.card_fin] at hc0 ⊢
  nlinarith [mul_le_mul_of_nonneg_left hsmall.le hc0]

end BlockBand.Palm.MomentFlow
