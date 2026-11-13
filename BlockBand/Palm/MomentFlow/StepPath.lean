module

public import BlockBand.Palm.MomentFlow.StepFlow
public import BlockBand.Palm.MomentFlow.MaxPath

/-!
# The induction step along one path (deterministic)

Fixed: a short rate path `c` on `[a, b]`, eigenvalue paths `lam`, the full-flow `r`-moments `Φ`,
the `(r-1)`-moments `Ψ`, a finite set `K` of admissible centres and for each centre `k₀ ∈ K`
two short-flow solutions on `[a, b]`: `g k₀` from the flattened datum `Av Φ(a)` (ramp of width
`wd` centred at `k₀`) and `h k₀` from the indicator of the ramp window `{rampDist k₀ ≤ wd}`
(the finite-speed flow of `PropagationP6`). The induction-hypothesis error `eI` is continuous.

* `stepRho`: the continuous error
  `ρ = eI + Σ_{k₀ ∈ K} (Σ_ζ (|g_{k₀} - Av Φ| - Main)_+ + (G+1) Σ_{rampDist > 2wd} h_{k₀})`
  (the error `e_D`, built from the deviations themselves, not from their bounds).
* `continuousOn_stepRho`, `stepRho_nonneg`.
* **`stepPath`**: with the removal average in its raw relative form `|remSum Φ - VΨ| ≤ e_A Ψ + e_B`
  (`e_A ≤ 1`),
  the averaged law, the long kernel bound, `CM(r-1)` with error `E₄ + eI`, the ramp count bound,
  and the rough bound `0 ≤ Φ(a) ≤ G` on the ramp window, for every centre `k₀ ∈ K`, time
  `σ ∈ [s, b]` and `ξ₀` with `rampDist k₀ ξ₀ ≤ wd/2`:
  `|Φ(σ, ξ₀) - 1| ≤ Main + ρ(σ) + G e^{-(rv/η)(σ-s)} + maxPathErr/(rv/η) + ∫_s^σ maxPathCoef ρ`
  with `e_R = e_A(1 + E₄) + e_B`. The comparison `|g - 1| ≤ (G+1) h` off the window is
  `abs_sub_one_le_of_initial`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- The continuous error of the step along one path. -/
def stepRho (r : ℕ) (K : Finset (Fin N)) (wd Main G : ℝ) (eI : ℝ → ℝ) (Φ : ℝ → Occ N → ℝ)
    (g h : Fin N → ℝ → Occ N → ℝ) (u : ℝ) : ℝ :=
  eI u + ∑ k₀ ∈ K, (∑ ζ ∈ sector N r,
      max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) +
    (G + 1) * ∑ ζ ∈ (sector N r).filter (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)), h k₀ u ζ)

theorem continuousOn_stepRho {r : ℕ} {K : Finset (Fin N)} {wd Main G : ℝ} {eI : ℝ → ℝ}
    {Φ : ℝ → Occ N → ℝ} {g h : Fin N → ℝ → Occ N → ℝ} {S : Set ℝ} (heI : ContinuousOn eI S)
    (hΦ : ∀ ζ ∈ sector N r, ContinuousOn (fun u => Φ u ζ) S)
    (hg : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, ContinuousOn (fun u => g k₀ u ζ) S)
    (hh : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, ContinuousOn (fun u => h k₀ u ζ) S) :
    ContinuousOn (stepRho r K wd Main G eI Φ g h) S := by
  unfold stepRho
  refine heI.add (continuousOn_finsetSum _ fun k₀ hk₀ => ?_)
  refine (continuousOn_finsetSum _ fun ζ hζ => ?_).add (continuousOn_const.mul
    (continuousOn_finsetSum _ fun ζ hζ => hh k₀ hk₀ ζ (Finset.mem_filter.1 hζ).1))
  unfold avFlat
  exact (continuous_const.max continuous_id).comp_continuousOn ((((hg k₀ hk₀ ζ hζ).sub
    ((continuousOn_const.mul (hΦ ζ hζ)).add continuousOn_const)).abs).sub continuousOn_const)

theorem stepRho_nonneg {r : ℕ} {K : Finset (Fin N)} {wd Main G : ℝ} {eI : ℝ → ℝ}
    {Φ : ℝ → Occ N → ℝ} {g h : Fin N → ℝ → Occ N → ℝ} {u : ℝ} (heI : 0 ≤ eI u) (hG : 0 ≤ G)
    (hh : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, 0 ≤ h k₀ u ζ) :
    0 ≤ stepRho r K wd Main G eI Φ g h u := by
  unfold stepRho
  refine add_nonneg heI (Finset.sum_nonneg fun k₀ hk₀ => add_nonneg
    (Finset.sum_nonneg fun ζ _ => le_max_left _ _) (mul_nonneg (by linarith)
      (Finset.sum_nonneg fun ζ hζ => hh k₀ hk₀ ζ (Finset.mem_filter.1 hζ).1)))

theorem eI_le_stepRho {r : ℕ} {K : Finset (Fin N)} {wd Main G : ℝ} {eI : ℝ → ℝ}
    {Φ : ℝ → Occ N → ℝ} {g h : Fin N → ℝ → Occ N → ℝ} {u : ℝ} (hG : 0 ≤ G)
    (hh : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, 0 ≤ h k₀ u ζ) :
    eI u ≤ stepRho r K wd Main G eI Φ g h u := by
  unfold stepRho
  have : 0 ≤ ∑ k₀ ∈ K, (∑ ζ ∈ sector N r,
      max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) +
    (G + 1) * ∑ ζ ∈ (sector N r).filter (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)),
      h k₀ u ζ) :=
    Finset.sum_nonneg fun k₀ hk₀ => add_nonneg
      (Finset.sum_nonneg fun ζ _ => le_max_left _ _) (mul_nonneg (by linarith)
        (Finset.sum_nonneg fun ζ hζ => hh k₀ hk₀ ζ (Finset.mem_filter.1 hζ).1))
  linarith

theorem term_le_stepRho {r : ℕ} {K : Finset (Fin N)} {wd Main G : ℝ} {eI : ℝ → ℝ}
    {Φ : ℝ → Occ N → ℝ} {g h : Fin N → ℝ → Occ N → ℝ} {u : ℝ} (heI : 0 ≤ eI u) (hG : 0 ≤ G)
    (hh : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, 0 ≤ h k₀ u ζ) {k₀ : Fin N} (hk₀ : k₀ ∈ K) :
    ∑ ζ ∈ sector N r, max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) +
      (G + 1) * ∑ ζ ∈ (sector N r).filter (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)),
        h k₀ u ζ ≤ stepRho r K wd Main G eI Φ g h u := by
  unfold stepRho
  have := Finset.single_le_sum (f := fun k₀ => ∑ ζ ∈ sector N r,
      max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) +
    (G + 1) * ∑ ζ ∈ (sector N r).filter (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)), h k₀ u ζ)
    (fun k₀ hk₀ => add_nonneg
      (Finset.sum_nonneg fun ζ _ => le_max_left _ _) (mul_nonneg (by linarith)
        (Finset.sum_nonneg fun ζ hζ => hh k₀ hk₀ ζ (Finset.mem_filter.1 hζ).1))) hk₀
  linarith

/-- **The induction step along one path.** -/
theorem stepPath {r ℓ L : ℕ} (hr : 1 ≤ r) {c : ℝ → Fin N → Fin N → ℝ} {lam : ℝ → Fin N → ℝ}
    {a s b η G v Vb E₂ E₃ E₄ eA eB Main β wd : ℝ} (has : a ≤ s) (hsb : s ≤ b) (hη : 0 < η)
    (hv : 0 < v) (hvVb : v ≤ Vb) (hG1 : 1 ≤ G) (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃) (hE₄ : 0 ≤ E₄)
    (heA0 : 0 ≤ eA) (heA1 : eA ≤ 1) (heB : 0 ≤ eB) (hMain : 0 ≤ Main) (hβ : 0 ≤ β)
    (hwd : 0 < wd)
    (hc0 : ∀ u ∈ Ioo a b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    (hcK : ∀ u ∈ Ioo s b, ∀ i j, i ≠ j → labelDist i j < ℓ → kerAt (lam u) η i j ≤ η * c u i j)
    (hcl : ∀ u ∈ Ioo s b, ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c u i j = 0)
    {Φ Ψ : ℝ → Occ N → ℝ} (hΦc : ∀ ζ ∈ sector N r, ContinuousOn (fun u => Φ u ζ) (Icc s b))
    (hΦ0 : ∀ u ∈ Icc s b, ∀ ξ ∈ sector N r, 0 ≤ Φ u ξ)
    {eI : ℝ → ℝ} (heIc : ContinuousOn eI (Icc s b)) (heI0 : ∀ u ∈ Icc s b, 0 ≤ eI u)
    (K : Finset (Fin N)) (g h : Fin N → ℝ → Occ N → ℝ)
    (hg : ∀ k₀ ∈ K, IsMomentFlowSolution c r a b (g k₀))
    (hh : ∀ k₀ ∈ K, IsMomentFlowSolution c r a b (h k₀))
    (hga : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, g k₀ a ζ = avFlat (ramp wd (k₀ : ℕ)) (Φ a) ζ)
    (hha : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r,
      h k₀ a ζ = if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ wd then 1 else 0)
    (hΦa : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, (rampDist (k₀ : ℕ) ζ : ℝ) ≤ wd →
      0 ≤ Φ a ζ ∧ Φ a ζ ≤ G)
    (V : ℝ → ℝ → Fin N → ℝ)
    (hV : ∀ k₀ ∈ K, ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd →
      ∀ i, 0 < ξ i →
      v ≤ V η u i ∧ V η u i ≤ Vb ∧ ∀ k ≤ L, 0 ≤ V (2 ^ k * η) u i ∧ V (2 ^ k * η) u i ≤ Vb)
    (hR2 : ∀ k₀ ∈ K, ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd →
      ∀ i, 0 < ξ i →
      |remSum (kerAt (lam u) η) (Φ u) ξ i - V η u i * Ψ u (remove ξ i)| ≤
        eA * Ψ u (remove ξ i) + eB ∧
      ∀ k ≤ L, |remSum (kerAt (lam u) (2 ^ k * η)) (Φ u) ξ i -
        V (2 ^ k * η) u i * Ψ u (remove ξ i)| ≤ eA * Ψ u (remove ξ i) + eB)
    (hAv : ∀ k₀ ∈ K, ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd →
      ∀ i, 0 < ξ i →
      |∑ j, kerAt (lam u) η i j - V η u i| ≤ E₂ ∧
      ∀ k ≤ L, |∑ j, kerAt (lam u) (2 ^ k * η) i j - V (2 ^ k * η) u i| ≤ E₂)
    (hL : ∀ k₀ ∈ K, ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd →
      ∀ i, 0 < ξ i → longKer (kerAt (lam u) η) ℓ i ≤ E₃)
    (hIH : ∀ k₀ ∈ K, ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd →
      ∀ i, 0 < ξ i → |Ψ u (remove ξ i) - 1| ≤ E₄ + eI u)
    (hlip : ∀ k₀ ∈ K, ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd →
      ∀ i, 0 < ξ i → ∀ j,
      |ramp wd (k₀ : ℕ) (remTarget ξ i j) - ramp wd (k₀ : ℕ) ξ| ≤
        min 1 (β * (|lam u j - lam u i| + η))) :
    ∀ k₀ ∈ K, ∀ σ ∈ Icc s b, ∀ ξ₀ ∈ sector N r, (rampDist (k₀ : ℕ) ξ₀ : ℝ) ≤ wd / 2 →
      |Φ σ ξ₀ - 1| ≤ Main + stepRho r K wd Main G eI Φ g h σ +
        G * Real.exp (-((r : ℝ) * v / η) * (σ - s)) +
        maxPathErr N r η β G Vb E₂ E₃ E₄ (eA * (1 + E₄) + eB) Main L / ((r : ℝ) * v / η) +
        ∫ t in s..σ, maxPathCoef N r η β v Vb E₂ L * stepRho r K wd Main G eI Φ g h t := by
  intro k₀ hk₀
  set ρ := stepRho r K wd Main G eI Φ g h with hρdef
  have hG0 : 0 ≤ G := by linarith
  -- positivity of the window flows
  have hh0 : ∀ k₀ ∈ K, ∀ u ∈ Icc a b, ∀ ζ ∈ sector N r, 0 ≤ h k₀ u ζ := by
    intro k hk u hu ζ hζ
    refine (hh k hk).ge_of_initial_ge hc0 (m := 0) (fun ξ hξ => ?_) u hu ζ hζ
    rw [hha k hk ξ hξ]; split_ifs <;> norm_num
  have hsub : Icc s b ⊆ Icc a b := Set.Icc_subset_Icc has le_rfl
  have hρc : ContinuousOn ρ (Icc s b) :=
    continuousOn_stepRho heIc hΦc (fun k hk ζ hζ => ((hg k hk) ζ hζ).1.mono hsub)
      (fun k hk ζ hζ => ((hh k hk) ζ hζ).1.mono hsub)
  have hρ0 : ∀ u ∈ Icc s b, 0 ≤ ρ u := fun u hu =>
    stepRho_nonneg (heI0 u hu) hG0 (fun k hk ζ hζ => hh0 k hk u (hsub hu) ζ hζ)
  have heIρ : ∀ u ∈ Icc s b, eI u ≤ ρ u := fun u hu =>
    eI_le_stepRho hG0 (fun k hk ζ hζ => hh0 k hk u (hsub hu) ζ hζ)
  have hterm : ∀ u ∈ Icc s b,
      ∑ ζ ∈ sector N r, max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) +
      (G + 1) * ∑ ζ ∈ (sector N r).filter (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)),
        h k₀ u ζ ≤ ρ u := fun u hu =>
    term_le_stepRho (heI0 u hu) hG0 (fun k hk ζ hζ => hh0 k hk u (hsub hu) ζ hζ) hk₀
  -- the flattened datum lies in `[0, G]`
  have hga0 : ∀ ζ ∈ sector N r, 0 ≤ g k₀ a ζ ∧ g k₀ a ζ ≤ G := by
    intro ζ hζ
    rw [hga k₀ hk₀ ζ hζ]
    unfold avFlat
    have h0 := ramp_nonneg wd (k₀ : ℕ) ζ
    have h1 := ramp_le_one wd (k₀ : ℕ) ζ
    by_cases hw : (rampDist (k₀ : ℕ) ζ : ℝ) ≤ wd
    · obtain ⟨hΦ1, hΦ2⟩ := hΦa k₀ hk₀ ζ hζ hw
      constructor <;> nlinarith
    · rw [ramp_eq_zero hwd (le_of_lt (not_le.1 hw))]
      constructor <;> linarith
  have hgs : ∀ ζ ∈ sector N r, 0 ≤ g k₀ s ζ ∧ g k₀ s ζ ≤ G := by
    intro ζ hζ
    have hs : s ∈ Icc a b := ⟨has, hsb⟩
    exact ⟨(hg k₀ hk₀).ge_of_initial_ge hc0 (fun ξ hξ => (hga0 ξ hξ).1) s hs ζ hζ,
      (hg k₀ hk₀).le_of_initial_le hc0 (fun ξ hξ => (hga0 ξ hξ).2) s hs ζ hζ⟩
  -- comparison off the window
  have hX3 : ∀ u ∈ Icc a b, ∀ ζ ∈ sector N r, |g k₀ u ζ - 1| ≤ (G + 1) * h k₀ u ζ := by
    refine abs_sub_one_le_of_initial hc0 (hg k₀ hk₀) (hh k₀ hk₀) fun ζ hζ => ?_
    rw [hga k₀ hk₀ ζ hζ, hha k₀ hk₀ ζ hζ]
    unfold avFlat
    have h0 := ramp_nonneg wd (k₀ : ℕ) ζ
    have h1 := ramp_le_one wd (k₀ : ℕ) ζ
    split_ifs with hw
    · obtain ⟨hΦ1, hΦ2⟩ := hΦa k₀ hk₀ ζ hζ hw
      have e : ramp wd (k₀ : ℕ) ζ * Φ a ζ + (1 - ramp wd (k₀ : ℕ) ζ) - 1 =
          ramp wd (k₀ : ℕ) ζ * (Φ a ζ - 1) := by ring
      rw [e, abs_mul, abs_of_nonneg h0]
      have : |Φ a ζ - 1| ≤ G := abs_le.2 ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg (Φ a ζ - 1)]
    · rw [ramp_eq_zero hwd (le_of_lt (not_le.1 hw))]; simp
  have hcs : ∀ u ∈ Ioo s b, ∀ i j, i ≠ j → 0 ≤ c u i j := fun u hu =>
    hc0 u ⟨lt_of_le_of_lt has hu.1, hu.2⟩
  have hmp := maxPath (N := N) (r := r) (ℓ := ℓ) (L := L) hr (c := c) (lam := lam)
    (s := s) (b := b) (η := η) (G := G) (v := v) (Vb := Vb) (E₂ := E₂) (E₃ := E₃) (E₄ := E₄)
    (eR := eA * (1 + E₄) + eB) (Main := Main) (β := β) hsb hη hv hvVb hG1 hE₂ hE₃ hE₄
    (by positivity) hMain hβ hcs hcK hcl (g := g k₀) (Φ := Φ) (Ψ := Ψ)
    ((hg k₀ hk₀).mono_left has) (fun ζ hζ => (hgs ζ hζ).1) (fun ζ hζ => (hgs ζ hζ).2)
    (fun u hu ξ hξ => hΦ0 u (Ioo_subset_Icc_self hu) ξ hξ) hρc hρ0
    (fun ξ => (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * wd) (ramp wd (k₀ : ℕ))
    (fun ξ => ⟨ramp_nonneg _ _ _, ramp_le_one _ _ _⟩) V
    (hV k₀ hk₀)
    (fun u hu ξ hξ hP i hi => by
      have hu' := Ioo_subset_Icc_self hu
      have hIHu := hIH k₀ hk₀ u hu ξ hξ hP i hi
      have hΨ : Ψ u (remove ξ i) ≤ 1 + E₄ + ρ u := by
        have := (abs_le.1 hIHu).2; linarith [heIρ u hu']
      have hfix : eA * Ψ u (remove ξ i) + eB ≤ eA * (1 + E₄) + eB + ρ u := by
        have h1 := mul_le_mul_of_nonneg_left hΨ heA0
        have h2 : eA * ρ u ≤ ρ u := by nlinarith [hρ0 u hu']
        nlinarith
      obtain ⟨h1, h2⟩ := hR2 k₀ hk₀ u hu ξ hξ hP i hi
      exact ⟨h1.trans hfix, fun k hk => (h2 k hk).trans hfix⟩)
    (hAv k₀ hk₀) (hL k₀ hk₀)
    (fun u hu ξ hξ hP i hi => (hIH k₀ hk₀ u hu ξ hξ hP i hi).trans
      (by linarith [heIρ u (Ioo_subset_Icc_self hu)]))
    (hlip k₀ hk₀)
    (fun u hu ζ hζ => by
      have h1 := hterm u hu
      have h2 : max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) ≤
          ∑ ζ ∈ sector N r, max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) :=
        Finset.single_le_sum (f := fun ζ => max 0
          (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main))
          (fun _ _ => le_max_left _ _) hζ
      have h3 : 0 ≤ (G + 1) * ∑ ζ ∈ (sector N r).filter
          (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)), h k₀ u ζ :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun ζ hζ =>
          hh0 k₀ hk₀ u (hsub hu) ζ (Finset.mem_filter.1 hζ).1)
      have h4 := le_max_right 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main)
      linarith)
    (fun u hu ξ hξ hP => by
      have hu' := Ioo_subset_Icc_self hu
      have h1 := hX3 u (hsub hu') ξ hξ
      have hmem : ξ ∈ (sector N r).filter (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)) :=
        Finset.mem_filter.2 ⟨hξ, not_le.1 hP⟩
      have h2 : h k₀ u ξ ≤ ∑ ζ ∈ (sector N r).filter
          (fun ζ => 2 * wd < (rampDist (k₀ : ℕ) ζ : ℝ)), h k₀ u ζ :=
        Finset.single_le_sum (f := fun ζ => h k₀ u ζ) (fun ζ hζ =>
          hh0 k₀ hk₀ u (hsub hu') ζ (Finset.mem_filter.1 hζ).1) hmem
      have h3 : 0 ≤ ∑ ζ ∈ sector N r,
          max 0 (|g k₀ u ζ - avFlat (ramp wd (k₀ : ℕ)) (Φ u) ζ| - Main) :=
        Finset.sum_nonneg fun _ _ => le_max_left _ _
      have h4 := hterm u hu'
      have h5 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ G + 1)
      linarith)
  intro σ hσ ξ₀ hξ₀ hd
  exact hmp σ hσ ξ₀ hξ₀ (ramp_eq_one hwd hd)

end BlockBand.Palm.MomentFlow
