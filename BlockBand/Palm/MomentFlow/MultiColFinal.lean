module

public import BlockBand.Palm.MomentFlow.MultiColRow
public import BlockBand.Palm.MomentFlow.MultiColScales
public import BlockBand.Palm.MomentFlow.MultiFinal
public import BlockBand.Palm.MomentFlow.StepsMultiColSpec

/-!
# `MultiShortColumnSpeed` holds

* `permW_far_le'`: far configurations have small matching weight (centres at time `s`, positions
  at time `u`);
* `multi_col_fixed`: the bound `N^{-D}` at one `N` under the scale inequalities (hypothesis
  `P3` for `kappaCol`), far weights at time `u` via the upper count at `u` and the displacement;
* `multiShortColumnSpeed_holds`: `ε ≤ 1/300` by `multi_col_fixed` with `c' = min(1/C, r₀/64)/2`;
  `ε > 1/300` trivially (no far configuration), `c' = 1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Palm.RelativeLocalization
open scoped NNReal ENNReal Matrix

variable {N : ℕ}

/-- Far configurations have a small matching weight (arbitrary centres). -/
theorem permW_far_le' {r : ℕ} {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (lam : Fin N → ℝ) (c : Fin r → ℝ)
    {ξ₀ ζ : Occ N} {x : Fin r → Fin N} (hx : x ∈ labs r ξ₀) (hζ : ζ ∈ sector N r) {R δ : ℝ}
    (hR0 : 0 ≤ R) (hfar : (r : ℝ) * R < (occDist ξ₀ ζ : ℝ)) (hδ0 : 0 ≤ δ)
    (hsep : ∀ (m : Fin r) (j : Fin N), R < (labelDist (x m) j : ℝ) → φ (lam j - c m) ≤ δ) :
    permW φ lam c ζ ≤ (r : ℝ) ^ r * (N : ℝ) ^ r * δ := by
  have hpt : ∀ y ∈ labs r ζ, pW φ lam c y ≤ δ := by
    intro y hy
    obtain ⟨m, hm⟩ := exists_far_of_occDist hx hy hR0 hfar
    rw [pW_eq_mul _ _ _ _ m]
    have hx1 : pWx φ lam c y m ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => hφ0 _) (fun _ _ => hφ1 _)
    calc φ (lam (y m) - c m) * pWx φ lam c y m
        ≤ δ * 1 := mul_le_mul (hsep _ _ hm) hx1 (pWx_nonneg hφ0 _ _ _ _) hδ0
      _ = δ := mul_one δ
  unfold permW
  calc cfgFact ζ * ∑ y ∈ labs r ζ, pW φ lam c y
      ≤ (r : ℝ) ^ r * (((labs r ζ).card : ℝ) * δ) := by
        refine mul_le_mul (cfgFact_le hζ) ?_ (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 _ _ y)
          (by positivity)
        calc ∑ y ∈ labs r ζ, pW φ lam c y ≤ ∑ _y ∈ labs r ζ, δ := Finset.sum_le_sum hpt
          _ = _ := by simp
    _ ≤ (r : ℝ) ^ r * ((N : ℝ) ^ r * δ) := by
        gcongr; exact card_labs_le ζ
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- The column-form bound `N^{-D}` at a single `N`, under the scale inequalities for `kappaCol`
(hypothesis `P3`) and the spectral good event; far weights are evaluated at time `u` via the upper
count at `u` and the displacement `2C√τ` (`permW_far_le'`). -/
theorem multi_col_fixed (r : ℕ) (hr : 1 ≤ r)
    (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {E c τ r₀ c₁ C₁ C b₀ ε D c₂ h : ℝ}
    {ℓ : ℕ} (hτ0 : 0 ≤ τ) (ha : 0 < c - τ) (hr₀ : 0 < r₀) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hC : 0 < C) (hc₂C : c₂ ≤ 1 / C) (hc₂r : c₂ ≤ r₀ / 64)
    (hℓ : 1 ≤ ℓ)
    (P2 : (ℓ : ℝ) / N ≤ r₀ / 32)
    (P3 : kappaCol N ℓ r r₀ c₁ C₁ * τ ≤ 1)
    (P4 : (N : ℝ) / ℓ * (2 * C * Real.sqrt τ) ≤ 1)
    (P5 : (N : ℝ) / ℓ * h ≤ 1)
    (P6 : (N : ℝ) ^ ε ≤ (N : ℝ) / ℓ)
    (P7 : (N : ℝ) ^ r * ((r : ℝ) ^ r * (N : ℝ) ^ r) * Real.exp (3 + r) *
      Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) ≤ (N : ℝ) ^ (-D) / 3)
    (hbad : flowLaw N (c - τ) {ω | ¬ ∀ s ∈ Set.Icc (c - τ) c,
          (∀ i j : Fin N, ℓ ≤ labelDist i j →
            c₁ * (labelDist i j : ℝ) / N ≤
              |flowEigenvalue F (c - τ) ω s i - flowEigenvalue F (c - τ) ω s j|) ∧
          (∀ i j : Fin N, labelDist i j < ℓ →
            min |flowEigenvalue F (c - τ) ω s i - E| |flowEigenvalue F (c - τ) ω s j - E| ≤
              r₀ / 8 →
            |flowEigenvalue F (c - τ) ω s i - flowEigenvalue F (c - τ) ω s j| ≤ C₁ * ℓ / N) ∧
          (∀ x y : ℝ, x ≤ y →
            ((Finset.univ.filter fun i : Fin N =>
                flowEigenvalue F (c - τ) ω s i ∈ Set.Icc x y).card : ℝ) ≤
              C * N * ((y - x) + h)) ∧
          (∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
            c₁ * N * (y - x) ≤
              ((Finset.univ.filter fun i : Fin N =>
                flowEigenvalue F (c - τ) ω s i ∈ Set.Icc x y).card : ℝ)) ∧
          (∀ i : Fin N, longCoupling F (c - τ) ω ℓ s i ≤ C * N / ℓ ∧
            (|flowEigenvalue F (c - τ) ω s i - E| ≤ r₀ / 8 →
              b₀ * N / ℓ ≤ longCoupling F (c - τ) ω ℓ s i)) ∧
          (∀ x : Fin N → ℂ, l2Norm ((flowMatrix F (c - τ) ω s -
              flowMatrix F (c - τ) ω (c - τ)) *ᵥ x) ≤ C * Real.sqrt τ * l2Norm x)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D) / 3))
    (s u : ℝ) (has : c - τ ≤ s) (hsu : s ≤ u) (huc : u ≤ c) (ξ : Occ N) (hξ : ξ ∈ sector N r) :
    flowLaw N (c - τ) {ω | (∀ k : Fin N, 0 < ξ k →
          |flowEigenvalue F (c - τ) ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F (c - τ) ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if ζ = ξ then 1 else 0) ∧
          Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) <
            ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * ((N : ℝ) ^ ε * ℓ) < (occDist ξ ζ : ℝ)),
              Φ u ζ} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  classical
  set a := c - τ with hadef
  set μ := flowLaw N a with hμ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hND : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNr _
  obtain ⟨x, hx⟩ := exists_occOf r ξ hξ
  have hx' : x ∈ labs r ξ := mem_labs.2 hx
  set sL : ℝ≥0 := Real.toNNReal (s - a) with hsLdef
  set T : ℝ≥0 := Real.toNNReal (u - s) with hTdef
  have hsL : (sL : ℝ) = s - a := Real.coe_toNNReal _ (by linarith)
  have hT : (T : ℝ) = u - s := Real.coe_toNNReal _ (by linarith)
  -- the gap level
  have hlim := tendsto_gapWin_any hDBM hF ha sL T
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 (ENNReal.ofReal ((N : ℝ) ^ (-D) / 3))
    (ENNReal.ofReal_pos.2 (by positivity))).exists
  set g : ℝ := 1 / ((n : ℝ) + 1) with hgdef
  have hg : 0 < g := by positivity
  -- parameters
  set ν : ℝ := (N : ℝ) / ℓ with hνdef
  set d : ℝ := (ℓ : ℝ) / N with hddef
  set R₀ : ℝ := r₀ / 64 with hR₀def
  set R : ℝ := (N : ℝ) ^ ε * ℓ with hRdef
  have hν : 0 ≤ ν := by positivity
  have hd : 0 < d := by positivity
  have hR₀ : 0 < R₀ := by positivity
  have hρ : d + 2 * R₀ ≤ r₀ / 16 := by rw [hddef, hR₀def]; linarith
  have hR0 : 0 ≤ R := by positivity
  set K : ℝ := max (kappaCol N ℓ r r₀ c₁ C₁) 0 with hKdef
  set φ := rlPhi ν 0 d R₀ with hφdef
  set δ₁ : ℝ := Real.exp (-(c₂ * (N : ℝ) ^ ε - 3)) with hδ₁
  set δ₀ : ℝ := (r : ℝ) ^ r * (N : ℝ) ^ r * δ₁ with hδ₀
  set e : ℝ := Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) with hedef
  -- the good set
  obtain ⟨Good8, hGood8⟩ : ∃ Good8 : Set (FlowSample N), Good8 = {ω | ∀ s ∈ Set.Icc a c,
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
            C * Real.sqrt τ * l2Norm x)} := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Set (FlowSample N),
      G = {ω | ω.1.IsHermitian} ∩ Good8 ∩ (gapWin F sL T g)ᶜ := ⟨_, rfl⟩
  have hG : ∀ ω ∈ G, (∀ k : Fin N, 0 < ξ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) →
      ω.1.IsHermitian ∧
      (∀ σ ∈ Icc s u,
        (∀ i j : Fin N, ℓ ≤ labelDist i j →
          c₁ * labelDist i j / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) ∧
        (∀ i j : Fin N, labelDist i j < ℓ →
          min |flowEigenvalue F a ω σ i - E| |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 →
          |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| ≤ C₁ * ℓ / N) ∧
        (∀ i j : Fin N, i ≠ j → g < |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)) ∧
      (∀ ζ ∈ sector N r, (r : ℝ) * R < (occDist ξ ζ : ℝ) →
        permW φ (flowEigenvalue F a ω u) (fun m => flowEigenvalue F a ω s (x m)) ζ ≤ δ₀) := by
    intro ω hω _
    rw [hGdef] at hω
    obtain ⟨⟨hH, h8⟩, hgap⟩ := hω
    rw [hGood8] at h8
    have hσa : ∀ σ ∈ Icc s u, σ ∈ Icc a c := fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hlam_t : ∀ xx : ℝ≥0, flowLam F (sL + xx) ω = flowEigenvalue F a ω (s + xx) := by
      intro xx
      rw [flowLam_add_eq_eig F a hH, NNReal.coe_add, hsL]
      congr 1; ring
    -- displacement
    have hdisp : ∀ σ ∈ Icc a c, ∀ k : Fin N,
        |flowEigenvalue F a ω σ k - flowEigenvalue F a ω a k| ≤ C * Real.sqrt τ := by
      intro σ hσ k
      exact abs_freshEigenvalue_sub_le (flowMatrix_isHermitian' hF a hH σ)
        (flowMatrix_isHermitian' hF a hH a) (h8 σ hσ).2.2.2.2.2 k
    refine ⟨hH, fun σ hσ => ⟨(h8 σ (hσa σ hσ)).1, (h8 σ (hσa σ hσ)).2.1, ?_⟩, ?_⟩
    · -- gaps
      intro i j hij
      by_contra hle
      push Not at hle
      apply hgap
      refine ⟨Real.toNNReal (σ - s), ?_, ?_⟩
      · rw [hTdef]; exact Real.toNNReal_le_toNNReal (by linarith [hσ.2])
      · rw [hlam_t, Real.coe_toNNReal _ (by linarith [hσ.1]), show s + (σ - s) = σ by ring]
        exact ⟨i, j, hij, hle⟩
    · -- far configurations, at time `u`
      intro ζ hζ hfar
      have hu8 := h8 u ⟨by linarith, huc⟩
      have hmono : Monotone (flowEigenvalue F a ω u) :=
        freshEigenvalue_monotone (flowMatrix_isHermitian' hF a hH u)
      refine permW_far_le' (fun z => (rlPhi_pos z).le) (rlPhi_le_one hν hR₀) _ _ hx' hζ hR0 hfar
        (by positivity) fun m j hkj => ?_
      set k := x m
      have hcnt := labelDist_succ_le_count hmono hu8.2.2.1 k j
      have h1 := hdisp u ⟨by linarith, huc⟩ k
      have h2 := hdisp s ⟨has, by linarith⟩ k
      have hks : |flowEigenvalue F a ω u k - flowEigenvalue F a ω s k| ≤ 2 * C * Real.sqrt τ := by
        calc _ ≤ |flowEigenvalue F a ω u k - flowEigenvalue F a ω a k| +
              |flowEigenvalue F a ω a k - flowEigenvalue F a ω s k| := abs_sub_le _ _ _
          _ ≤ C * Real.sqrt τ + C * Real.sqrt τ := add_le_add h1 (by rw [abs_sub_comm]; exact h2)
          _ = _ := by ring
      set Δ := flowEigenvalue F a ω u j - flowEigenvalue F a ω s k
      set Δ' := flowEigenvalue F a ω u j - flowEigenvalue F a ω u k
      have hΔ' : R / (C * N) - h ≤ |Δ'| := by
        have h1 : R + 1 ≤ C * N * (|Δ'| + h) := by linarith
        have hCN : 0 < C * N := by positivity
        have h2 : R / (C * N) ≤ |Δ'| + h := by
          rw [div_le_iff₀ hCN]; linarith
        linarith
      have hΔ : R / (C * N) - h - 2 * C * Real.sqrt τ ≤ |Δ| := by
        have : |Δ'| ≤ |Δ| + |flowEigenvalue F a ω u k - flowEigenvalue F a ω s k| := by
          have e : Δ' = Δ - (flowEigenvalue F a ω u k - flowEigenvalue F a ω s k) := by ring
          rw [e]; exact abs_sub _ _
        linarith
      refine (rlPhi_le_exp hν hR₀ Δ).trans (Real.exp_le_exp.mpr ?_)
      rw [sub_zero]
      have hA : (N : ℝ) ^ ε / C - 3 ≤ ν * (|Δ| - d) := by
        have e1 : ν * (R / (C * N)) = (N : ℝ) ^ ε / C := by
          rw [hνdef, hRdef]; field_simp
        have e2 : ν * d = 1 := by rw [hνdef, hddef]; field_simp
        have h3 := mul_le_mul_of_nonneg_left hΔ hν
        rw [mul_sub, mul_sub, e1] at h3
        rw [mul_sub, e2]
        have hP4 : ν * (2 * C * Real.sqrt τ) ≤ 1 := P4
        linarith
      have hB : (N : ℝ) ^ ε * (r₀ / 64) ≤ ν * R₀ := by
        rw [hR₀def]; exact mul_le_mul_of_nonneg_right P6 (by positivity)
      have hc2a : c₂ * (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε / C := by
        rw [div_eq_mul_one_div, mul_comm ((N : ℝ) ^ ε)]
        exact mul_le_mul_of_nonneg_right hc₂C (by positivity)
      have hc2b : c₂ * (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε * (r₀ / 64) := by
        rw [mul_comm c₂]; exact mul_le_mul_of_nonneg_left hc₂r (by positivity)
      have hmin : c₂ * (N : ℝ) ^ ε - 3 ≤ ν * min (|Δ| - d) R₀ := by
        rw [mul_min_of_nonneg _ _ hν]
        exact le_min (by linarith) (by linarith)
      linarith
  -- the quantitative bound
  have hmain := multi_col_any r hIto hStop hDBM hN hF ha has hsu hℓ hξ hx' R
    (E := E) (r₀ := r₀) (ν := ν) (d := d) (R₀ := R₀) (c₁ := c₁) (C₁ := C₁) (g := g) (K := K)
    (δ₀ := δ₀) (e := e) hν hd hR₀ hρ hc₁ hC₁ hg (le_max_right _ _) (le_max_left _ _)
    (by positivity) (Real.exp_pos _) G hG
  refine hmain.trans ?_
  -- the complement of the good set
  have hGc : μ Gᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) +
      ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) := by
    have hsub : Gᶜ ⊆ ({ω : FlowSample N | ¬ ω.1.IsHermitian} ∪ Good8ᶜ) ∪ gapWin F sL T g := by
      intro ω hω
      rw [hGdef] at hω
      simp only [Set.compl_inter, Set.mem_union, Set.mem_compl_iff,
        Set.mem_ofPred_eq, not_not] at hω ⊢
      tauto
    calc μ Gᶜ ≤ μ (({ω : FlowSample N | ¬ ω.1.IsHermitian} ∪ Good8ᶜ) ∪ gapWin F sL T g) :=
          measure_mono hsub
      _ ≤ μ ({ω : FlowSample N | ¬ ω.1.IsHermitian} ∪ Good8ᶜ) + μ (gapWin F sL T g) :=
          measure_union_le _ _
      _ ≤ (μ {ω : FlowSample N | ¬ ω.1.IsHermitian} + μ Good8ᶜ) + μ (gapWin F sL T g) :=
          add_le_add (measure_union_le _ _) le_rfl
      _ ≤ (0 + ENNReal.ofReal ((N : ℝ) ^ (-D) / 3)) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) := by
          refine add_le_add (add_le_add ?_ ?_) hn.le
          · rw [hμ, BlockBand.Palm.GoodEvent.flowLaw_not_hermitian]
          · rw [hGood8, Set.compl_ofPred]; exact hbad
      _ = _ := by rw [zero_add]
  -- the Markov term
  have hMk : δ₀ / (Real.exp (-(K * (u - s))) * e) ≤ (N : ℝ) ^ (-D) / 3 := by
    have hus : u - s ≤ τ := by linarith
    have hK0 : 0 ≤ K := le_max_right _ _
    have hKτ : K * (u - s) ≤ 1 := by
      calc K * (u - s) ≤ K * τ := mul_le_mul_of_nonneg_left hus hK0
        _ ≤ 1 := by
          rw [hKdef, max_mul_of_nonneg _ _ hτ0, zero_mul]
          exact max_le P3 zero_le_one
    have hden : Real.exp (-(K * (u - s))) * e =
        Real.exp (-(K * (u - s)) + -(c₂ / 2 * (N : ℝ) ^ ε)) := by
      rw [Real.exp_add]
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ r := one_le_pow₀ (by exact_mod_cast hN)
    rw [hden, hδ₀, hδ₁]
    have hexp : Real.exp (-(c₂ * (N : ℝ) ^ ε - 3)) /
        Real.exp (-(K * (u - s)) + -(c₂ / 2 * (N : ℝ) ^ ε)) ≤
        Real.exp (3 + r) * Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hrr : 0 ≤ (r : ℝ) ^ r * (N : ℝ) ^ r := by positivity
    have hE : 0 ≤ Real.exp (3 + r) * Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) := by positivity
    calc (r : ℝ) ^ r * (N : ℝ) ^ r * Real.exp (-(c₂ * (N : ℝ) ^ ε - 3)) /
          Real.exp (-(K * (u - s)) + -(c₂ / 2 * (N : ℝ) ^ ε))
        = ((r : ℝ) ^ r * (N : ℝ) ^ r) *
          (Real.exp (-(c₂ * (N : ℝ) ^ ε - 3)) /
            Real.exp (-(K * (u - s)) + -(c₂ / 2 * (N : ℝ) ^ ε))) := by ring
      _ ≤ ((r : ℝ) ^ r * (N : ℝ) ^ r) *
          (Real.exp (3 + r) * Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε))) :=
          mul_le_mul_of_nonneg_left hexp hrr
      _ ≤ (N : ℝ) ^ r * ((r : ℝ) ^ r * (N : ℝ) ^ r) *
          (Real.exp (3 + r) * Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε))) := by
          have := mul_le_mul_of_nonneg_right hN1 (mul_nonneg hrr hE)
          nlinarith
      _ = _ := by ring
      _ ≤ _ := P7
  calc μ Gᶜ + ENNReal.ofReal (δ₀ / (Real.exp (-(K * (u - s))) * e))
      ≤ (ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 3)) +
          ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) := add_le_add hGc (ENNReal.ofReal_le_ofReal hMk)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **`MultiShortColumnSpeed` holds.** -/
theorem multiShortColumnSpeed_holds (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) : MultiShortColumnSpeed := by
  intro A c r₀ s₀ v₀ hK r hr ε hε
  obtain ⟨c₁, C₁, C, b₀, hc₁, hC₁, hC, hb₀, hD⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  obtain ⟨hc0, -, hr₀, -, -, -⟩ := hK
  by_cases hε3 : ε ≤ 1 / 300
  · set c₂ : ℝ := min (1 / C) (r₀ / 64) with hc₂def
    have hc₂ : 0 < c₂ := lt_min (by positivity) (by positivity)
    refine ⟨c₂ / 2, by positivity, fun D => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hD (D + 1)
    obtain ⟨N₂, hN₂⟩ := multi_scales r (D := D) (C₁ := C₁) hε hε3 hC hc₁ hr₀ hc0 hc₂
    obtain ⟨N₃, hN₃⟩ := multi_scales_col r (C₁ := C₁) hc₁ hr₀
    refine ⟨max (max (max N₁ N₂) N₃) 3, fun N hN F E hFC => ?_⟩
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hN
    have hN2 : N₂ ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) hN
    have hN3' : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
    have hNpos : 0 < N := by omega
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    obtain ⟨-, ha, hℓ, P2, -, P4, P5, P6, P7⟩ := hN₂ N hN2
    have P3 := hN₃ N hN3'
    have hbad0 := hN₁ N hN1 F E hFC
    have hbad : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 3 := by
      have hNp : (0 : ℝ) < N := by linarith
      rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hNp, Real.rpow_neg_one]
      have hND : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) hNr) hND.le
    intro a ℓ R s u has hsu huc ξ hξ
    exact multi_col_fixed r hr (hIto _) hStop (hDBM N) hNpos hFC.1 (E := E) (c := c)
      (τ := (N : ℝ) ^ (-(1 / 100 : ℝ))) (r₀ := r₀) (c₁ := c₁) (C₁ := C₁) (C := C) (b₀ := b₀)
      (ε := ε) (D := D) (c₂ := c₂) (h := (N : ℝ) ^ (-(1 / 100 : ℝ))) (ℓ := ℓ)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) ha hr₀ hc₁ hC₁ hC (min_le_left _ _)
      (min_le_right _ _) hℓ P2 P3 P4 P5 P6 P7
      (hbad0.trans (ENNReal.ofReal_le_ofReal hbad)) s u has hsu huc ξ hξ
  · push Not at hε3
    refine ⟨1, one_pos, fun D => ?_⟩
    obtain ⟨N₂, hN₂⟩ := multi_scales_large hε3
    refine ⟨max N₂ 1, fun N hN F E hFC => ?_⟩
    intro a ℓ R s u has hsu huc ξ hξ
    have hNR : (N : ℝ) ≤ R := hN₂ N (le_trans (le_max_left _ _) hN)
    have hfilt : (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist ξ ζ : ℝ)) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun ζ hζ hlt => ?_
      have h1 : (occDist ξ ζ : ℝ) ≤ r * ((N : ℝ) - 1) := by
        have := occDist_le_sector hξ hζ
        have h1N : 1 ≤ N := le_trans (le_max_right _ _) hN
        have : ((occDist ξ ζ : ℕ) : ℝ) ≤ ((r * (N - 1) : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_mul, Nat.cast_sub h1N, Nat.cast_one] at this
        exact this
      have h2 : (r : ℝ) * ((N : ℝ) - 1) < (r : ℝ) * R := by
        have hr' : (0 : ℝ) < r := by exact_mod_cast hr
        nlinarith
      linarith
    have hempty : {ω : FlowSample N | (∀ k : Fin N, 0 < ξ k →
          |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if ζ = ξ then 1 else 0) ∧
          Real.exp (-(1 * (N : ℝ) ^ ε)) <
            ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist ξ ζ : ℝ)), Φ u ζ} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, Φ, -, -, hΦu⟩
      rw [hfilt, Finset.sum_empty] at hΦu
      exact absurd hΦu (not_lt.mpr (Real.exp_pos _).le)
    rw [hempty, measure_empty]
    exact bot_le

end BlockBand.Palm.MomentFlow
