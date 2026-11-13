module

public import BlockBand.Palm.MomentFlow.Tail6

/-!
# Localized Duhamel bound with time-integrated finite-speed tails

* `continuousOn_flowRate`, `continuousOn_shortFlowRate`: rates continuous on collision-free
  intervals.
* `longShort_sample`: `duhamel_localized` with a backward short row whose integrated tail
  outside `W` is `≤ η` gives `|F(u,ξ) - g(u,ξ)| ≤ e(u-s) + Kη`.
* **`longShort_multi`**: combined with the finite-speed tail `tail6_multi` and `ae_noCollision`, one
  `pathSigma`-measurable bad set of probability `≤ N^{-D}` off which the bound holds with
  `η = N^{-D}` for every full/short solution pair and every pair of long-generator bounds `e`
  (on the `occDist` ball of radius `rR`) and `K` (global); `e` and `K` are universally
  quantified in the conclusion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory intervalIntegral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

theorem continuousOn_flowRate {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    (ω : FlowSample N) {s u : ℝ}
    (hgap : ∀ x ∈ Icc s u, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l) :
    ContinuousOn (flowRate F a ω) (Icc s u) := by
  refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => ?_
  by_cases hkl : k = l
  · subst hkl
    have e : (fun x => flowRate F a ω x k k) = fun _ => 0 := by funext x; simp [flowRate]
    rw [e]; exact continuousOn_const
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast k.pos.ne'
    refine ContinuousOn.inv₀ (Continuous.continuousOn (continuous_const.mul
      (((continuous_flowEigenvalue hF a ω k).sub (continuous_flowEigenvalue hF a ω l)).pow 2)))
      fun x hx => ?_
    exact mul_ne_zero hN0 (pow_ne_zero 2 (sub_ne_zero.2 (hgap x hx k l hkl)))

theorem continuousOn_shortFlowRate {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) {s u : ℝ}
    (hgap : ∀ x ∈ Icc s u, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l) :
    ContinuousOn (shortFlowRate F a ω ℓ) (Icc s u) := by
  have h := continuousOn_flowRate hF a ω hgap
  refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => ?_
  by_cases hd : labelDist k l < ℓ
  · have e : (fun x => shortFlowRate F a ω ℓ x k l) = fun x => flowRate F a ω x k l := by
      funext x; simp [shortFlowRate, maskRate, hd]
    rw [e]; exact continuousOn_pi.1 (continuousOn_pi.1 h k) l
  · have e : (fun x => shortFlowRate F a ω ℓ x k l) = fun _ => 0 := by
      funext x; simp [shortFlowRate, maskRate, hd]
    rw [e]; exact continuousOn_const

/-- **Sample level**: Duhamel (`duhamel_localized`) with a backward short row whose
time-integrated tail outside `W` is `≤ η`: `|F(u,ξ) - g(u,ξ)| ≤ e(u-s) + Kη`. -/
theorem longShort_sample {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) {r : ℕ} {s u e K η : ℝ} (hsu : s ≤ u) (he : 0 ≤ e) (hK : 0 ≤ K)
    (hgap : ∀ x ∈ Icc s u, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l)
    {Φ G w : ℝ → Occ N → ℝ} (hΦ : IsMomentFlowSolution (flowRate F a ω) r s u Φ)
    (hG : IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u G)
    (h0 : ∀ ζ ∈ sector N r, Φ s ζ = G s ζ) (W : Finset (Occ N))
    (hloc : ∀ v ∈ Icc s u, ∀ ζ ∈ sector N r, ζ ∈ W →
      |momentGenerator (flowRate F a ω v) (Φ v) ζ -
        momentGenerator (shortFlowRate F a ω ℓ v) (Φ v) ζ| ≤ e)
    (hglob : ∀ v ∈ Icc s u, ∀ ζ ∈ sector N r,
      |momentGenerator (flowRate F a ω v) (Φ v) ζ -
        momentGenerator (shortFlowRate F a ω ℓ v) (Φ v) ζ| ≤ K)
    {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hw : IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r s u w)
    (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ)
    (htail : (∫ v in s..u, ∑ ζ ∈ sector N r \ W, w v ζ) ≤ η) :
    |Φ u ξ - G u ξ| ≤ e * (u - s) + K * η := by
  have hcF := continuousOn_flowRate hF a ω hgap
  have hcS := continuousOn_shortFlowRate hF a ω ℓ hgap
  have h := duhamel_localized hsu he (fun v _ i j _ => shortFlowRate_nonneg F a ω ℓ v i j)
    (fun v _ i j => shortFlowRate_symm F a ω ℓ v i j) hΦ hG h0
    (fun ζ hζ => (continuousOn_momentGenerator hcF (fun ζ hζ => (hΦ ζ hζ).1) hζ).sub
      (continuousOn_momentGenerator hcS (fun ζ hζ => (hΦ ζ hζ).1) hζ)) W hloc hglob hξ hw hwu
  exact h.trans (by gcongr)

/-- **Long versus short moments**, every `r ≥ 1` (from `MultiShortFiniteSpeed` and
`DysonBrownianMotion`). For every `D`, `N ≥ N₀`, fresh `F`, deterministic `a ≤ s ≤ u ≤ c`, `ξ`:
one `pathSigma`-measurable `B`, `P(B) ≤ N^{-D}`, such that a.e. off `B`, under bulk positions of
the particles of `ξ` on `[s,u]`: for **every** full-flow solution `Φ` and short-flow solution `G`
with `G(s) = Φ(s)` and every pair of long-generator bounds `e` (on the `occDist` ball of radius
`rR`) and `K` (on the sector), `|Φ(u,ξ) - G(u,ξ)| ≤ e(u-s) + K N^{-D}`. -/
theorem longShort_multi (hMS : MultiShortFiniteSpeed) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) {r : ℕ} (hr : 1 ≤ r) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        let R : ℝ := (N : ℝ) ^ ε * ℓ
        ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ ξ ∈ sector N r,
          ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
            flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
              (∀ v ∈ Icc s u, ∀ k : Fin N, 0 < ξ k →
                |flowEigenvalue F a ω v k - E| ≤ r₀ / 16) →
              ∀ (Φ G : ℝ → Occ N → ℝ) (e K : ℝ), 0 ≤ e → 0 ≤ K →
                IsMomentFlowSolution (flowRate F a ω) r s u Φ →
                IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u G →
                (∀ ζ ∈ sector N r, Φ s ζ = G s ζ) →
                (∀ v ∈ Icc s u, ∀ ζ ∈ sector N r, ζ ∈ occBall r R ξ →
                  |momentGenerator (flowRate F a ω v) (Φ v) ζ -
                    momentGenerator (shortFlowRate F a ω ℓ v) (Φ v) ζ| ≤ e) →
                (∀ v ∈ Icc s u, ∀ ζ ∈ sector N r,
                  |momentGenerator (flowRate F a ω v) (Φ v) ζ -
                    momentGenerator (shortFlowRate F a ω ℓ v) (Φ v) ζ| ≤ K) →
                |Φ u ξ - G u ξ| ≤ e * (u - s) + K * (N : ℝ) ^ (-D) := by
  intro D
  obtain ⟨N₀, hN₀⟩ := tail6_multi hMS hDBM (A := A) hK hr hε D
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      tendsto_natCast_atTop_atTop |>.eventually (gt_mem_nhds hK.1))
  refine ⟨max N₀ (max N₁ 1), fun N hN F E hC => ?_⟩
  intro a ℓ R s u has hsu huc ξ hξ
  obtain ⟨B, hBm, hBμ, hBae⟩ := hN₀ N (le_of_max_le_left hN) F E hC s u has hsu huc ξ hξ
  have hN1 : 1 ≤ N := le_of_max_le_right (le_of_max_le_right hN)
  have hτ : (N : ℝ) ^ (-(1 / 100 : ℝ)) < c := hN₁ N (le_of_max_le_left (le_of_max_le_right hN))
  have ha : 0 < a := by simp only [a]; linarith
  refine ⟨B, hBm, hBμ, ?_⟩
  filter_upwards [hBae, ae_noCollision (hDBM N) hC.1 ha] with ω hω hcol hωB hbulk
    Φ G e K he hK0 hΦ hG h0 hloc hglob
  obtain ⟨w, hw, hwu, hint, -⟩ := hω hωB hbulk
  exact longShort_sample hC.1 a ω ℓ hsu he hK0 (fun x hx k l hkl => hcol.2 x (has.trans hx.1) k l hkl)
    hΦ hG h0 _ hloc hglob hξ hw hwu hint

end BlockBand.Palm.MomentFlow
