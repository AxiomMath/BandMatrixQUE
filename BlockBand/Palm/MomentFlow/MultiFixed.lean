module

public import BlockBand.Palm.MomentFlow.MultiRowAny
public import BlockBand.Palm.GoodEventHolds

/-!
# The fixed-`N` form of `MultiShortFiniteSpeed`

* `cfgFact_le`, `card_labs_le`, `permW_far_le`, `permW_terminal_ge`: deterministic weight bounds
  (far configurations through `exists_far_of_occDist` and the upper count; the terminal weight
  through the identity matching).
* `tendsto_gapWin_any`: small gaps on `[s,u]` have vanishing probability from every start
  (`s = a` by the restart map).
* proved in the sibling module `MultiFixedMain` from these: `multi_fixed`, for one `N`, explicit scale inequalities and the bound on the bad event of the
  spectral good event give the bound `N^{-D}` for the event of `MultiShortFiniteSpeed`, with
  `c' = c₂/2`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal ENNReal

variable {N r : ℕ}

/-!
### Deterministic weight bounds
-/

theorem cfgFact_le {ζ : Occ N} (hζ : ζ ∈ sector N r) : cfgFact ζ ≤ (r : ℝ) ^ r := by
  unfold cfgFact
  rw [← mem_sector.1 hζ, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  have hi : ζ i ≤ ∑ j, ζ j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h1 : (ζ i).factorial ≤ (ζ i) ^ (ζ i) := Nat.factorial_le_pow _
  have h2 : (ζ i) ^ (ζ i) ≤ (∑ j, ζ j) ^ (ζ i) := Nat.pow_le_pow_left hi _
  exact_mod_cast h1.trans h2

theorem one_le_cfgFact (ζ : Occ N) : 1 ≤ cfgFact ζ := by
  have := Finset.prod_le_prod₀ (s := (univ : Finset (Fin N))) (f := fun _ => (1 : ℝ))
    (g := fun i => ((ζ i).factorial : ℝ)) (fun _ _ => zero_le_one)
    (fun i _ => by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  simpa [cfgFact] using this

theorem card_labs_le (ζ : Occ N) : ((labs r ζ).card : ℝ) ≤ (N : ℝ) ^ r := by
  have : (labs r ζ).card ≤ N ^ r :=
    (Finset.card_le_univ _).trans (by simp)
  exact_mod_cast this

/-- Far configurations have a small matching weight. -/
theorem permW_far_le {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) (lam : Fin N → ℝ)
    {ξ₀ ζ : Occ N} {x : Fin r → Fin N} (hx : x ∈ labs r ξ₀) (hζ : ζ ∈ sector N r) {R δ : ℝ}
    (hR0 : 0 ≤ R) (hfar : (r : ℝ) * R < (occDist ξ₀ ζ : ℝ)) (hδ0 : 0 ≤ δ)
    (hsep : ∀ k j : Fin N, R < (labelDist k j : ℝ) → φ (lam j - lam k) ≤ δ) :
    permW φ lam (fun m => lam (x m)) ζ ≤ (r : ℝ) ^ r * (N : ℝ) ^ r * δ := by
  have hpt : ∀ y ∈ labs r ζ, pW φ lam (fun m => lam (x m)) y ≤ δ := by
    intro y hy
    obtain ⟨m, hm⟩ := exists_far_of_occDist hx hy hR0 hfar
    rw [pW_eq_mul _ _ _ _ m]
    have hx1 : pWx φ lam (fun m => lam (x m)) y m ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => hφ0 _) (fun _ _ => hφ1 _)
    calc φ (lam (y m) - lam (x m)) * pWx φ lam (fun m => lam (x m)) y m
        ≤ δ * 1 := mul_le_mul (hsep _ _ hm) hx1 (pWx_nonneg hφ0 _ _ _ _) hδ0
      _ = δ := mul_one δ
  unfold permW
  calc cfgFact ζ * ∑ y ∈ labs r ζ, pW φ lam (fun m => lam (x m)) y
      ≤ (r : ℝ) ^ r * (((labs r ζ).card : ℝ) * δ) := by
        refine mul_le_mul (cfgFact_le hζ) ?_ (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 _ _ y)
          (by positivity)
        calc ∑ y ∈ labs r ζ, pW φ lam (fun m => lam (x m)) y ≤ ∑ _y ∈ labs r ζ, δ :=
              Finset.sum_le_sum hpt
          _ = _ := by simp
    _ ≤ (r : ℝ) ^ r * ((N : ℝ) ^ r * δ) := by
        gcongr; exact card_labs_le ζ
    _ = _ := by ring

/-- The terminal weight of `ξ₀` is at least the identity-matching term. -/
theorem permW_terminal_ge {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    {ξ₀ : Occ N} {x : Fin r → Fin N} (hx : x ∈ labs r ξ₀) {θ : ℝ}
    (hθ : ∀ m, Real.exp (-θ) ≤ φ (lam (x m) - c m)) :
    Real.exp (-(r * θ)) ≤ permW φ lam c ξ₀ := by
  have h1 : Real.exp (-(r * θ)) ≤ pW φ lam c x := by
    have : Real.exp (-(r * θ)) = ∏ _m : Fin r, Real.exp (-θ) := by
      rw [Finset.prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun m _ => hθ m
  have h2 : pW φ lam c x ≤ ∑ y ∈ labs r ξ₀, pW φ lam c y :=
    Finset.single_le_sum (f := fun y => pW φ lam c y) (fun y _ => pW_nonneg hφ0 _ _ y) hx
  unfold permW
  calc Real.exp (-(r * θ)) ≤ ∑ y ∈ labs r ξ₀, pW φ lam c y := h1.trans h2
    _ ≤ cfgFact ξ₀ * ∑ y ∈ labs r ξ₀, pW φ lam c y :=
        le_mul_of_one_le_left (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 _ _ y)
          (one_le_cfgFact ξ₀)

/-!
### Small gaps from every start
-/

theorem gapWin_eq_iUnion (F : Matrix (Fin N) (Fin N) ℂ) (sL T : ℝ≥0) (g : ℝ) :
    gapWin F sL T g = ⋃ p : {p : Fin N × Fin N // p.1 ≠ p.2}, pairWin F sL T p.1.1 p.1.2 g := by
  refine Set.Subset.antisymm (gapWin_subset F sL T g) ?_
  intro ω hω
  obtain ⟨p, x, hx, hg⟩ := Set.mem_iUnion.mp hω
  exact ⟨x, hx, p.1.1, p.1.2, p.2, hg⟩

theorem measurableSet_gapWin {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (sL T : ℝ≥0)
    (g : ℝ) : MeasurableSet (gapWin F sL T g) := by
  rw [gapWin_eq_iUnion]
  exact MeasurableSet.iUnion fun p => measurableSet_pairWin hF sL T _ _ g

/-- **Small gaps on the window, every start** (base `a > 0`). -/
theorem tendsto_gapWin_any (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (sL T : ℝ≥0) :
    Tendsto (fun n : ℕ => flowLaw N a (gapWin F sL T (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le (zero_le (a := sL)) with h0 | hpos
  swap
  · exact tendsto_gapWin hDBM hF a hpos T
  subst h0
  set a' := a / 2 with ha'def
  have ha'0 : 0 ≤ a' := by positivity
  have ha'a : a' ≤ a := by linarith
  set sL' : ℝ≥0 := Real.toNNReal (a - a')
  have hsL'pos : 0 < sL' := Real.toNNReal_pos.mpr (by linarith)
  have hmp := measurePreserving_restartMap (N := N) ha'0 ha'a
  have hlim := tendsto_gapWin hDBM hF a' hsL'pos T
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    fun n => ?_
  rw [← hmp.measure_preimage (measurableSet_gapWin hF 0 T _).nullMeasurableSet]
  calc flowLaw N a' (restartMap a' a ⁻¹' gapWin F 0 T (1 / ((n : ℝ) + 1)))
      ≤ flowLaw N a' (gapWin F sL' T (1 / ((n : ℝ) + 1)) ∪ {ω | ¬ ω.1.IsHermitian}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hH : ω.1.IsHermitian
        · left
          obtain ⟨x, hx, hg⟩ := hω
          refine ⟨x, hx, ?_⟩
          rw [flowLam_restart ha'a hH x]; exact hg
        · exact Or.inr hH
    _ ≤ flowLaw N a' (gapWin F sL' T (1 / ((n : ℝ) + 1))) +
          flowLaw N a' {ω | ¬ ω.1.IsHermitian} := measure_union_le _ _
    _ = flowLaw N a' (gapWin F sL' T (1 / ((n : ℝ) + 1))) := by
        rw [BlockBand.Palm.GoodEvent.flowLaw_not_hermitian, add_zero]

end BlockBand.Palm.MomentFlow
