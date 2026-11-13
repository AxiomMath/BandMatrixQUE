module

public import BlockBand.Palm.MomentFlow.MultiFixed

/-!
# `MultiShortFiniteSpeed` at one `N` under explicit scale inequalities

Under the scale inequalities

* (`P2`) `ℓ/N ≤ r₀/32`, (`P3`) `κ_r τ ≤ 1`, (`P4`) `ν · 2C√τ ≤ 1`, (`P5`) `ν h ≤ 1`,
  (`P6`) `N^ε ≤ ν`,
* (`P7`) `N^r · r^r N^r · e^{3+r} · e^{-c₂N^ε/2} ≤ N^{-D}/3`,

and the bound `≤ N^{-D}/3` on the bad event of the spectral good event, the event of
`MultiShortFiniteSpeed` has probability `≤ N^{-D}` for every `a ≤ s ≤ u ≤ c` and `ξ` in the sector.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal ENNReal Matrix

variable {N : ℕ}

/-- The explicit rate `κ_r` at the scales `ν = N/ℓ`, `d = ℓ/N`, `R₀ = r₀/64`. -/
def kappaR (N ℓ r : ℕ) (r₀ c₁ C₁ : ℝ) : ℝ :=
  let ν : ℝ := (N : ℝ) / ℓ
  let d : ℝ := (ℓ : ℝ) / N
  let R₀ : ℝ := r₀ / 64
  r * (2 * ℓ * (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
          Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) / N +
        2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) +
        (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N)) +
      r ^ 2 * ((ν * weightConst) ^ 2 *
        (Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ^ 2 + 1)) / (2 * N)

theorem multi_fixed (r : ℕ) (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {E c τ r₀ c₁ C₁ C b₀ ε D c₂ h : ℝ}
    {ℓ : ℕ} (hτ0 : 0 ≤ τ) (ha : 0 < c - τ) (hr₀ : 0 < r₀) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hC : 0 < C) (hc₂C : c₂ ≤ 1 / C) (hc₂r : c₂ ≤ r₀ / 64)
    (hℓ : 1 ≤ ℓ)
    (P2 : (ℓ : ℝ) / N ≤ r₀ / 32)
    (P3 : kappaR N ℓ r r₀ c₁ C₁ * τ ≤ 1)
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
          (∀ ζ ∈ sector N r, Φ s ζ =
            if (r : ℝ) * ((N : ℝ) ^ ε * ℓ) < (occDist ξ ζ : ℝ) then 1 else 0) ∧
          Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) < Φ u ξ} ≤
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
  set K : ℝ := max (kappaR N ℓ r r₀ c₁ C₁) 0 with hKdef
  set φ := rlPhi ν 0 d R₀ with hφdef
  set δ₁ : ℝ := Real.exp (-(c₂ * (N : ℝ) ^ ε - 2)) with hδ₁
  set δ₀ : ℝ := (r : ℝ) ^ r * (N : ℝ) ^ r * δ₁ with hδ₀
  set w : ℝ := Real.exp (-(r * 1)) with hwdef
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
        permW φ (flowEigenvalue F a ω s) (fun m => flowEigenvalue F a ω s (x m)) ζ ≤ δ₀) ∧
      w ≤ permW φ (flowEigenvalue F a ω u) (fun m => flowEigenvalue F a ω s (x m)) ξ := by
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
    refine ⟨hH, fun σ hσ => ⟨(h8 σ (hσa σ hσ)).1, (h8 σ (hσa σ hσ)).2.1, ?_⟩, ?_, ?_⟩
    · -- gaps
      intro i j hij
      by_contra hle
      push Not at hle
      apply hgap
      refine ⟨Real.toNNReal (σ - s), ?_, ?_⟩
      · rw [hTdef]; exact Real.toNNReal_le_toNNReal (by linarith [hσ.2])
      · rw [hlam_t, Real.coe_toNNReal _ (by linarith [hσ.1]), show s + (σ - s) = σ by ring]
        exact ⟨i, j, hij, hle⟩
    · -- far configurations
      intro ζ hζ hfar
      have hs8 := h8 s ⟨has, by linarith⟩
      have hmono : Monotone (flowEigenvalue F a ω s) :=
        freshEigenvalue_monotone (flowMatrix_isHermitian' hF a hH s)
      refine permW_far_le (fun z => (rlPhi_pos z).le) (rlPhi_le_one hν hR₀) _ hx' hζ hR0 hfar
        (by positivity) fun k j hkj => ?_
      have hcnt := labelDist_succ_le_count hmono hs8.2.2.1 k j
      set Δ := flowEigenvalue F a ω s j - flowEigenvalue F a ω s k
      have hΔ : R / (C * N) - h ≤ |Δ| := by
        have h1 : R + 1 ≤ C * N * (|Δ| + h) := by linarith
        have hCN : 0 < C * N := by positivity
        have h2 : R / (C * N) ≤ |Δ| + h := by
          rw [div_le_iff₀ hCN]; linarith
        linarith
      refine (rlPhi_le_exp hν hR₀ Δ).trans (Real.exp_le_exp.mpr ?_)
      rw [sub_zero]
      have hA : (N : ℝ) ^ ε / C - 2 ≤ ν * (|Δ| - d) := by
        have e1 : ν * (R / (C * N)) = (N : ℝ) ^ ε / C := by
          rw [hνdef, hRdef]; field_simp
        have e2 : ν * d = 1 := by rw [hνdef, hddef]; field_simp
        have h3 := mul_le_mul_of_nonneg_left hΔ hν
        rw [mul_sub, e1] at h3
        rw [mul_sub, e2]
        linarith
      have hB : (N : ℝ) ^ ε * (r₀ / 64) ≤ ν * R₀ := by
        rw [hR₀def]; exact mul_le_mul_of_nonneg_right P6 (by positivity)
      have hc2a : c₂ * (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε / C := by
        rw [div_eq_mul_one_div, mul_comm ((N : ℝ) ^ ε)]
        exact mul_le_mul_of_nonneg_right hc₂C (by positivity)
      have hc2b : c₂ * (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε * (r₀ / 64) := by
        rw [mul_comm c₂]; exact mul_le_mul_of_nonneg_left hc₂r (by positivity)
      have hmin : c₂ * (N : ℝ) ^ ε - 2 ≤ ν * min (|Δ| - d) R₀ := by
        rw [mul_min_of_nonneg _ _ hν]
        exact le_min (by linarith) (by linarith)
      linarith
    · -- terminal weight
      refine permW_terminal_ge (fun z => (rlPhi_pos z).le) _ _ hx' fun m => ?_
      refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_le_rlPhi hν hd hR₀ _)
      rw [sub_zero]
      have h1 := hdisp u ⟨by linarith, huc⟩ (x m)
      have h2 := hdisp s ⟨has, by linarith⟩ (x m)
      have h3 : |flowEigenvalue F a ω u (x m) - flowEigenvalue F a ω s (x m)| ≤
          2 * C * Real.sqrt τ := by
        calc _ ≤ |flowEigenvalue F a ω u (x m) - flowEigenvalue F a ω a (x m)| +
              |flowEigenvalue F a ω a (x m) - flowEigenvalue F a ω s (x m)| := abs_sub_le _ _ _
          _ ≤ C * Real.sqrt τ + C * Real.sqrt τ := add_le_add h1 (by rw [abs_sub_comm]; exact h2)
          _ = _ := by ring
      have := mul_le_mul_of_nonneg_left h3 hν
      linarith
  -- the quantitative bound
  have hmain := multi_match_row_any r hIto hStop hDBM hN hF ha has hsu hℓ hξ hx' R
    (E := E) (r₀ := r₀) (ν := ν) (d := d) (R₀ := R₀) (c₁ := c₁) (C₁ := C₁) (g := g) (K := K)
    (δ₀ := δ₀) (w := w) (e := e) hν hd hR₀ hρ hc₁ hC₁ hg (le_max_right _ _) (le_max_left _ _)
    (by positivity) (Real.exp_pos _) (Real.exp_pos _) G hG
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
  have hMk : (sectorCard N r : ℝ) * δ₀ / (Real.exp (-(K * (u - s))) * w * e) ≤
      (N : ℝ) ^ (-D) / 3 := by
    have hus : u - s ≤ τ := by linarith
    have hK0 : 0 ≤ K := le_max_right _ _
    have hKτ : K * (u - s) ≤ 1 := by
      calc K * (u - s) ≤ K * τ := mul_le_mul_of_nonneg_left hus hK0
        _ ≤ 1 := by
          rw [hKdef, max_mul_of_nonneg _ _ hτ0, zero_mul]
          exact max_le P3 zero_le_one
    have hden : Real.exp (-(K * (u - s))) * w * e =
        Real.exp (-(K * (u - s)) + -(r * 1) + -(c₂ / 2 * (N : ℝ) ^ ε)) := by
      rw [Real.exp_add, Real.exp_add]
    have hsc : (sectorCard N r : ℝ) ≤ (N : ℝ) ^ r := by exact_mod_cast card_sector_le (N := N) r
    rw [hden, hδ₀, hδ₁]
    have hexp : Real.exp (-(c₂ * (N : ℝ) ^ ε - 2)) /
        Real.exp (-(K * (u - s)) + -(r * 1) + -(c₂ / 2 * (N : ℝ) ^ ε)) ≤
        Real.exp (3 + r) * Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε)) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc (sectorCard N r : ℝ) * ((r : ℝ) ^ r * (N : ℝ) ^ r * Real.exp (-(c₂ * (N : ℝ) ^ ε - 2))) /
          Real.exp (-(K * (u - s)) + -(r * 1) + -(c₂ / 2 * (N : ℝ) ^ ε))
        = (sectorCard N r : ℝ) * ((r : ℝ) ^ r * (N : ℝ) ^ r) *
          (Real.exp (-(c₂ * (N : ℝ) ^ ε - 2)) /
            Real.exp (-(K * (u - s)) + -(r * 1) + -(c₂ / 2 * (N : ℝ) ^ ε))) := by ring
      _ ≤ (N : ℝ) ^ r * ((r : ℝ) ^ r * (N : ℝ) ^ r) *
          (Real.exp (3 + r) * Real.exp (-(c₂ / 2 * (N : ℝ) ^ ε))) := by
          gcongr
      _ = _ := by ring
      _ ≤ _ := P7
  calc μ Gᶜ + ENNReal.ofReal ((sectorCard N r : ℝ) * δ₀ / (Real.exp (-(K * (u - s))) * w * e))
      ≤ (ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 3)) +
          ENNReal.ofReal ((N : ℝ) ^ (-D) / 3) := add_le_add hGc (ENNReal.ofReal_le_ofReal hMk)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end BlockBand.Palm.MomentFlow
