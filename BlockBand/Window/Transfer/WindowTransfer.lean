module

public import BlockBand.Window.Transfer.PhysicalScalarSplit
public import BlockBand.Window.Transfer.CriticalWindowRemainder
public import BlockBand.Window.Transfer.Semicircle
public import BlockBand.Window.Count.Statement

/-!
# The window transfer theorem from the refined count

Proves `WindowTransferContract` from `RefinedCountStatement` (`windowTransfer_of_refinedCount`).

Choices (after `b, T, E, ρ, w, ϑ, q`, before the model, the observables and `ε`):
* a support radius `M` of `w`, a sup bound `K` of `w`, `β = π` (density bound `ρ_sc ≤ 1/π`);
* `D_q = max(C_q,0) + K_q`, `D_2 = max(C_2,0) + K_2` (`C_q` from the location clause
  of the refined count, `K_q = ‖N(0,1)‖_q`, covering `‖t‖_q ≤ K_q σ ≤ K_q a_{n,W}/N`);
* `g = min(F_sc(E) - ϑ, 1 - ϑ - F_sc(E))`, `d = πg/2`, `N_0 = max(2/g, 4M/(ρd))`;
* `C = bulkTransferConstant` (depends on `b, q, ρ, M, D_q` only);
* `r(n,W) = boundaryRankRemainder(p, ρ, d, D_2, 2)` if `nW ≥ N_0`, `r(n,W) = nW·K` otherwise
  (and `0` off the admissible range). It tends to zero along every critical sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Transfer

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- `refinedRankScale p` is `a_{n,W} = countScale n W` by definition. -/
theorem refinedRankScale_eq_countScale (p : Parameters) :
    refinedRankScale p = countScale p.n p.W := rfl

/-- A pointwise bound by a nonnegative constant bounds the integral under a probability law
(integrable or not). -/
theorem integral_le_of_forall_le_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ x, f x ≤ c) :
    ∫ x, f x ∂μ ≤ c := by
  by_cases hi : Integrable f μ
  · calc ∫ x, f x ∂μ ≤ ∫ _, c ∂μ := integral_mono hi (integrable_const c) hf
      _ = c := by simp
  · rw [integral_undef hi]
    exact hc

/-- The observable-independent remainder `r_{n,W}` of the window transfer theorem. -/
def windowRemainder (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (ρ d D N₀ K : ℝ) (n W : ℕ) : ℝ :=
  if h : 4 ≤ n ∧ 0 < W then
    if N₀ ≤ ((n * W : ℕ) : ℝ) then
      boundaryRankRemainder ⟨n, W, b, h.1, h.2, hb, hb'⟩ ρ d D 2
    else ((n * W : ℕ) : ℝ) * K
  else 0

/-- `r_{n,W} → 0` along every critical sequence with ratio `τ > 0`. -/
theorem windowRemainder_tendsto (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (ρ d D N₀ K : ℝ)
    (hρ : 0 < ρ) (hd : 0 < d) (hD : 0 ≤ D) (τ : ℝ) (s : CriticalSequence τ) (hτ : 0 < τ) :
    Tendsto (fun j => windowRemainder b hb hb' ρ d D N₀ K (s.n j) (s.W j)) atTop (𝓝 0) := by
  have hlim := critical_boundary_rank_remainder_tendsto s hτ b hb hb' ρ d D 2 hρ hd hD
    (by norm_num)
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  apply hlim.congr'
  filter_upwards [hW.eventually_ge_atTop N₀] with j hj
  have hNW : N₀ ≤ ((s.n j * s.W j : ℕ) : ℝ) := by
    refine hj.trans ?_
    have h1 : (1 : ℝ) ≤ s.n j := by exact_mod_cast (le_trans (by norm_num) (s.n_ge_four j))
    push_cast
    nlinarith [(Nat.cast_nonneg (s.W j) : (0 : ℝ) ≤ s.W j)]
  unfold windowRemainder
  rw [dite_eq_left ⟨s.n_ge_four j, s.W_pos j⟩, ite_eq_left hNW]
  rfl

/-- Finite window bound in the large-dimension regime (`N ≥ N₀`), for one parameter `p`.
All inputs are the deterministic choices of the module docstring, the `L^q` and `L^2`
location bounds of the bulk ranks (as given by the refined count), and the observable
hypotheses of `WindowTransferContract`. -/
theorem window_transfer_large_dimension (p : Parameters) (model : p.GaussianRingModel)
    (E ρ : ℝ) (hρ : 0 < ρ) (w : ℝ → ℝ) (hw : Continuous w) (hcs : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) (M : ℝ) (hM : 0 ≤ M)
    (hsupp : ∀ x, w x ≠ 0 → |x| ≤ M) (ϑ : ℝ) (hϑ : 0 < ϑ)
    (q : ℝ) (hq : 1 < q) (Cq C2 : ℝ)
    (hCq : ∀ α, IsBulkRank p ϑ α →
      eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
        (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (Cq * countScale p.n p.W / p.N))
    (hC2 : ∀ α, IsBulkRank p ϑ α →
      eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
        (ENNReal.ofReal 2) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (C2 * countScale p.n p.W / p.N))
    (g : ℝ) (hg : 0 < g) (hgl : g ≤ semicircleCDF E - ϑ) (hgr : g ≤ 1 - ϑ - semicircleCDF E)
    (hNg : 2 / g ≤ (p.N : ℝ)) (hNw : 4 * M / (ρ * (Real.pi * (g / 2))) ≤ (p.N : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : Fin p.N → p.SiteMatrix → ℝ) (hAm : ∀ α, Measurable (A α))
    (hA01 : ∀ α H, 0 ≤ A α H ∧ A α H ≤ 1) (hAinv : ∀ α, IsScalarShiftInvariant (A α))
    (hmean : ∀ α, IsBulkRank p ϑ α →
      ∫ H, A α H ∂(model.law : Measure p.SiteMatrix) ≤ ε) :
    windowExpectation p model E ρ w A ≤
      bulkTransferConstant p q ρ Real.pi (max Cq 0 + gaussianMomentConstant q) M *
          (countScale p.n p.W / Real.sqrt p.n) * ε ^ (1 - 1 / q) +
        boundaryRankRemainder p ρ (Real.pi * (g / 2))
          (max C2 0 + gaussianMomentConstant 2) 2 := by
  classical
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix) with hμ
  set Nr : ℝ := (p.N : ℝ) with hNr
  set a : ℝ := refinedRankScale p with ha_def
  set d : ℝ := Real.pi * (g / 2) with hd_def
  have hd : 0 < d := by positivity
  have hpi := Real.pi_pos
  have ha : Real.sqrt (p.n : ℝ) ≤ a := refined_rank_scale_ge_sqrt p
  have hn4 : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (p.n : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have ha1 : 1 ≤ a := hsqrt1.trans ha
  -- `1/N ≤ g/2` and the window width
  have hinvN : 1 / Nr ≤ g / 2 := by
    rw [div_le_iff₀ hN]
    have := (div_le_iff₀ hg).mp hNg
    linarith
  have hwidth : 4 * (M / (Nr * ρ)) ≤ d := by
    have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < ρ * d)).mp hNw
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  -- boundary ranks `lo + 1 = ⌈ϑN⌉`, `hi + 1 = ⌊(1-ϑ)N⌋`
  have hϑN : 0 < ϑ * Nr := by positivity
  have hceil_pos : 0 < ⌈ϑ * Nr⌉₊ := Nat.ceil_pos.mpr hϑN
  have hceil_le : ⌈ϑ * Nr⌉₊ ≤ p.N := by
    apply Nat.ceil_le.mpr
    have : ϑ ≤ 1 := by linarith [hgl, hgr, hg]
    nlinarith
  have hgsum : 2 * g ≤ 1 - 2 * ϑ := by linarith
  have hfloor_one : (1 : ℝ) ≤ (1 - ϑ) * Nr := by
    have h2 : 2 ≤ g * Nr := by have := (div_le_iff₀ hg).mp hNg; linarith
    nlinarith
  have hfloor_pos : 0 < ⌊(1 - ϑ) * Nr⌋₊ := Nat.floor_pos.mpr hfloor_one
  have hfloor_le : ⌊(1 - ϑ) * Nr⌋₊ ≤ p.N := by
    apply Nat.floor_le_of_le
    nlinarith
  let lo : Fin p.N := ⟨⌈ϑ * Nr⌉₊ - 1, by omega⟩
  let hi : Fin p.N := ⟨⌊(1 - ϑ) * Nr⌋₊ - 1, by omega⟩
  have hlo1 : ((lo.val + 1 : ℕ) : ℝ) = (⌈ϑ * Nr⌉₊ : ℝ) := by
    congr 1; simp only [lo]; omega
  have hhi1 : ((hi.val + 1 : ℕ) : ℝ) = (⌊(1 - ϑ) * Nr⌋₊ : ℝ) := by
    congr 1; simp only [hi]; omega
  have hlo_ge : ϑ * Nr ≤ ((lo.val + 1 : ℕ) : ℝ) := hlo1 ▸ Nat.le_ceil _
  have hlo_lt : ((lo.val + 1 : ℕ) : ℝ) < ϑ * Nr + 1 := hlo1 ▸ Nat.ceil_lt_add_one hϑN.le
  have hhi_le : ((hi.val + 1 : ℕ) : ℝ) ≤ (1 - ϑ) * Nr :=
    hhi1 ▸ Nat.floor_le (by linarith)
  have hhi_gt : (1 - ϑ) * Nr < ((hi.val + 1 : ℕ) : ℝ) + 1 :=
    hhi1 ▸ Nat.lt_floor_add_one _
  -- levels of the boundary ranks
  have hlo_level : ((lo.val + 1 : ℕ) : ℝ) / Nr ≤ semicircleCDF E - g / 2 := by
    rw [div_le_iff₀ hN]
    have : 1 ≤ g / 2 * Nr := by have := (div_le_iff₀ hN).mp hinvN; linarith
    nlinarith
  have hhi_level : semicircleCDF E + g / 2 ≤ ((hi.val + 1 : ℕ) : ℝ) / Nr := by
    rw [le_div_iff₀ hN]
    have : 1 ≤ g / 2 * Nr := by have := (div_le_iff₀ hN).mp hinvN; linarith
    nlinarith
  have helo : classicalLocation p lo ≤ E - d := by
    have := classicalLocation_le_of_level p lo E (g / 2) (by positivity) hlo_level
    simpa [hd_def] using this
  have hehi : E + d ≤ classicalLocation p hi := by
    have := le_classicalLocation_of_level p hi E (g / 2) (by positivity) hhi_level
    simpa [hd_def] using this
  -- bulk membership
  have hlo_bulk : IsBulkRank p ϑ lo := by
    refine ⟨(le_div_iff₀ hN).mpr (by linarith), ?_⟩
    have := hlo_level
    have : semicircleCDF E - g / 2 ≤ 1 - ϑ := by linarith
    linarith
  have hhi_bulk : IsBulkRank p ϑ hi := by
    refine ⟨?_, (div_le_iff₀ hN).mpr (by linarith)⟩
    have : ϑ ≤ semicircleCDF E + g / 2 := by linarith
    linarith
  have hbulk : ∀ i ∈ Finset.Icc lo hi, IsBulkRank p ϑ i := by
    intro i hi'
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi'
    have h1' : ((lo.val + 1 : ℕ) : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Fin.le_def.mp h1)
    have h2' : ((i.val + 1 : ℕ) : ℝ) ≤ ((hi.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Fin.le_def.mp h2)
    exact ⟨hlo_bulk.1.trans (div_le_div_of_nonneg_right h1' hN.le),
      (div_le_div_of_nonneg_right h2' hN.le).trans hhi_bulk.2⟩
  -- traceless moment bounds
  have hσ := originalScalarSigma_le_scale p a ha
  have hmoment (r Cr : ℝ) (hr : 1 ≤ r)
      (hCr : ∀ α, IsBulkRank p ϑ α →
        eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
          (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (Cr * countScale p.n p.W / p.N))
      (i : Fin p.N) (hib : IsBulkRank p ϑ i) :
      eLpNorm (fun y => physicalOrderedEigenvalue p y i - classicalLocation p i)
        (ENNReal.ofReal r) (μ.map p.tracelessGaussianMatrix) ≤
        ENNReal.ofReal ((max Cr 0 + gaussianMomentConstant r) * a / Nr) := by
    have hL : eLpNorm (fun H => physicalOrderedEigenvalue p H i - classicalLocation p i)
        (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (max Cr 0 * a / Nr) :=
      (hCr i hib).trans (ENNReal.ofReal_le_ofReal (by
        rw [← refinedRankScale_eq_countScale]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hN.le))
    refine (traceless_rank_eLpNorm_le model i _ r _ hr (by positivity) hL).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hK := gaussianMomentConstant_nonneg r
    have : gaussianMomentConstant r * originalScalarSigma p ≤
        gaussianMomentConstant r * (a / Nr) := mul_le_mul_of_nonneg_left hσ hK
    rw [add_mul, add_div]
    rw [mul_div_assoc (gaussianMomentConstant r)]
    linarith
  -- the primitive chart
  have hsplit := windowExpectation_eq_split model E ρ w A hAinv
  have hfull := full_window_bulk_plus_outside_remainder p μ p.tracelessGaussianMatrix
    p.scalarTrace p.measurable_tracelessGaussianMatrix p.measurable_scalarTrace
    (scalarTrace_hasLaw_original model) (traceless_indep_scalarTrace model) A
    (fun i y => physicalOrderedEigenvalue p y i) hAm
    (fun i => measurable_physicalOrderedEigenvalue p i) (fun i y => (hA01 i y).1)
    (fun i y => (hA01 i y).2) w hw hcs hw1 hw0 (Finset.Icc lo hi) (classicalLocation p)
    (Nr * semicircleCDF E) q ρ Real.pi (max Cq 0 + gaussianMomentConstant q) a M E ε hq hρ hpi
    (by have := gaussianMomentConstant_nonneg q; positivity) ha ha1 hM hε hε1 hsupp
    (fun i _ => classicalLocation_separation p i E)
    (fun i hi' => hmoment q Cq hq.le hCq i (hbulk i hi'))
    (fun i hi' => by
      have h := hmean i (hbulk i hi')
      refine le_of_eq_of_le ?_ h
      exact integral_congr_ae (Eventually.of_forall fun H =>
        scalarShiftInvariant_traceless (hAinv i) H))
  have hout := outside_remainder_two_boundary_moments p (μ.map p.tracelessGaussianMatrix)
    (fun i y => physicalOrderedEigenvalue p y i)
    (fun i => measurable_physicalOrderedEigenvalue p i)
    (fun y => physicalOrderedEigenvalue_monotone p y) lo hi (classicalLocation p lo)
    (classicalLocation p hi) w hw hcs hw1 hw0 ρ M E d 2
    ((max C2 0 + gaussianMomentConstant 2) * a / Nr) hρ hd (by norm_num)
    (by have := gaussianMomentConstant_nonneg 2; positivity) hsupp hwidth helo hehi
    (hmoment 2 C2 (by norm_num) hC2 lo hlo_bulk) (hmoment 2 C2 (by norm_num) hC2 hi hhi_bulk)
  rw [hsplit]
  refine hfull.2.trans (add_le_add le_rfl ?_)
  refine hout.trans (le_of_eq ?_)
  unfold boundaryRankRemainder
  rw [mul_div_assoc]

/-- Small-dimension bound: `𝒱_{n,W} ≤ N K` whenever `w ≤ K` (`0 ≤ A ≤ 1`). -/
theorem windowExpectation_le_dimension (p : Parameters) (model : p.GaussianRingModel)
    (E ρ : ℝ) (w : ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (K : ℝ) (hK : ∀ x, w x ≤ K)
    (A : Fin p.N → p.SiteMatrix → ℝ) (hA01 : ∀ α H, 0 ≤ A α H ∧ A α H ≤ 1) :
    windowExpectation p model E ρ w A ≤ (p.N : ℝ) * K := by
  have hK0 : 0 ≤ K := (hw0 0).trans (hK 0)
  unfold windowExpectation
  apply integral_le_of_forall_le_const _ _ _ (by positivity)
  intro H
  calc (∑ α : Fin p.N, w ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E)) * A α H)
      ≤ ∑ _α : Fin p.N, K := Finset.sum_le_sum fun α _ =>
        (mul_le_of_le_one_right (hw0 _) (hA01 α H).2).trans (hK _)
    _ = (p.N : ℝ) * K := by simp

/-- The window transfer theorem, conditional only on the refined count (`RefinedCountStatement`,
of which only the `location` clause is used).
Law: the exact physical Gaussian block-band law `model.law` of every `GaussianRingModel`; raw
`H`, increasing eigenvalues `physicalOrderedEigenvalue`, zero-based ranks with the one-based
`IsBulkRank`. Domain: `0 < b < 1/2`, `T`, `E² < 4`, `ρ > 0`, continuous compactly supported
`w ≥ 0` with `∫ w = 1`, `0 < ϑ < 1/2` with `ϑ < F_sc(E) < 1 - ϑ`, `q > 1`; then every
`4 ≤ n ≤ TW`, `W ≥ 1`. Quantifier order exactly as in `WindowTransferContract`: `C` and
`r : ℕ → ℕ → ℝ` are chosen from `(b,T,E,ρ,w,ϑ,q)` only (see the module docstring), before the
model, `ε` and the Borel scalar-shift-invariant observables `0 ≤ A_α ≤ 1`, which may be
arbitrarily correlated with the spectrum. Conclusion:
`𝒱_{n,W} ≤ C (a_{n,W}/√n) ε^{1-1/q} + r(n,W)`, with `r → 0` along every critical sequence
of ratio `τ > 0`. The proof uses the Gaussian trace decomposition of the physical law
(`windowExpectation_eq_split`), `full_window_bulk_plus_outside_remainder`,
`outside_remainder_two_boundary_moments` and `critical_boundary_rank_remainder_tendsto`. -/
theorem windowTransfer_of_refinedCount (h : BlockBand.Window.Count.RefinedCountStatement) :
    WindowTransferContract := by
  intro b hb hb' T E ρ _hE hρ w hw hcs hw0 hw1 ϑ hϑ hϑ' hϑF hFϑ q hq
  -- support radius and sup bound of `w`
  obtain ⟨M₀, hM₀⟩ := hcs.isCompact.isBounded.exists_norm_le
  set M := max M₀ 0 with hM_def
  have hM : 0 ≤ M := le_max_right _ _
  have hsupp : ∀ x, w x ≠ 0 → |x| ≤ M := fun x hx =>
    (hM₀ x (subset_tsupport w hx)).trans (le_max_left _ _)
  obtain ⟨K, hK⟩ := hw.bounded_above_of_compact_support hcs
  have hK' : ∀ x, w x ≤ K := fun x => (le_abs_self (w x)).trans (hK x)
  -- location constants at the orders `q` and `2`
  obtain ⟨Cq, hCq⟩ := h.location b hb hb' T ϑ hϑ hϑ' q hq.le
  obtain ⟨C2, hC2⟩ := h.location b hb hb' T ϑ hϑ hϑ' 2 (by norm_num)
  set Dq := max Cq 0 + gaussianMomentConstant q with hDq
  set D2 := max C2 0 + gaussianMomentConstant 2 with hD2
  have hD2nn : 0 ≤ D2 := add_nonneg (le_max_right _ _) (gaussianMomentConstant_nonneg 2)
  set g := min (semicircleCDF E - ϑ) (1 - ϑ - semicircleCDF E) with hg_def
  have hg : 0 < g := lt_min (by linarith) (by linarith)
  set d := Real.pi * (g / 2) with hd_def
  have hd : 0 < d := by positivity
  set N₀ := max (2 / g) (4 * M / (ρ * d)) with hN₀
  let p₀ : Parameters := ⟨4, 1, b, le_rfl, one_pos, hb, hb'⟩
  refine ⟨bulkTransferConstant p₀ q ρ Real.pi Dq M,
    windowRemainder b hb hb' ρ d D2 N₀ K, ?_, ?_⟩
  · intro τ s hτ
    exact windowRemainder_tendsto b hb hb' ρ d D2 N₀ K hρ hd hD2nn τ s hτ
  · intro n W hn hW hnT p model ε hε hε1 A hAm hA01 hAinv hmean
    have hC0 : 0 ≤ bulkTransferConstant p₀ q ρ Real.pi Dq M := by
      have hq1 : 0 < q - 1 := by linarith
      unfold bulkTransferConstant
      have hcap : 0 ≤ cappedRankConstant p₀ q ρ Real.pi Dq M := by
        unfold cappedRankConstant largeRankConstant fixedRankCutoff
        have : 0 ≤ Dq := add_nonneg (le_max_right _ _) (gaussianMomentConstant_nonneg q)
        have := Real.pi_pos
        have hq0 : 0 < q := by linarith
        have hc : 0 < p₀.c := p₀.c_pos
        positivity
      have hc : 0 < p₀.c := p₀.c_pos
      exact mul_nonneg (mul_nonneg zero_le_two (div_nonneg (by positivity) hq1.le))
        (by positivity)
    have hterm : 0 ≤ bulkTransferConstant p₀ q ρ Real.pi Dq M *
        (countScale n W / Real.sqrt n) * ε ^ (1 - 1 / q) := by
      have hcs0 : 0 ≤ countScale (n : ℝ) (W : ℝ) :=
        (Real.sqrt_nonneg _).trans (refined_rank_scale_ge_sqrt p)
      have := Real.rpow_nonneg hε.le (1 - 1 / q)
      positivity
    have hr : windowRemainder b hb hb' ρ d D2 N₀ K n W =
        if N₀ ≤ ((n * W : ℕ) : ℝ) then boundaryRankRemainder p ρ d D2 2
        else ((n * W : ℕ) : ℝ) * K := by
      unfold windowRemainder
      rw [dite_eq_left ⟨hn, hW⟩]
    rw [hr]
    split_ifs with hbig
    · have hNbig : N₀ ≤ (p.N : ℝ) := hbig
      have hmain := window_transfer_large_dimension p model E ρ hρ w hw hcs hw0 hw1 M hM hsupp
        ϑ hϑ q hq Cq C2 (fun α hα => hCq p rfl hnT model α hα)
        (fun α hα => hC2 p rfl hnT model α hα) g hg (min_le_left _ _) (min_le_right _ _)
        ((le_max_left _ _).trans hNbig) ((le_max_right _ _).trans hNbig) ε hε hε1 A hAm hA01
        hAinv hmean
      exact hmain
    · exact (windowExpectation_le_dimension p model E ρ w hw0 K hK' A hA01).trans
        (le_add_of_nonneg_left hterm)

end BlockBand.Window.Transfer
