module

public import BlockBand.Palm.MomentFlow.StepsLongFlow
public import BlockBand.Palm.MomentFlow.EventHeight

/-!
# Long couplings on the good event, bounded by `N/ℓ · q*Γq` (pathwise)

`long_coupling_event_bound`: outside an event of probability `≤ 2N^{-D}`, for every time `s` of
the window with simple spectrum and every label `i` in the bulk window,
`Σ_{|j-i| ≥ ℓ} c_ij(s) X_j(s) ≤ (2N/(c₁ℓ)) Cst q*Γq`, from the long-gap clause and the isotropic
upper bound.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs

variable {N : ℕ}

set_option maxHeartbeats 800000 in

/-- **Long couplings on the good event.** -/
theorem long_coupling_event_bound (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) {A c r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε5 : ε < 1 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        ∀ q : Fin N → ℂ, ∃ Bad : Set (FlowSample N),
          flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) Bad ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D)) + ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ s ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c,
            HasSimpleSpectrum N (flowMatrix F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s) →
            ∀ i : Fin N,
              |flowEigenvalue F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i - E| ≤ r₀ / 2 →
              ∑ j ∈ Finset.univ.filter
                  (fun j => ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j),
                flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j *
                  flowOverlap F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) q s j ω ≤
              2 / (c₁ * ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ / N) * Cst *
                quadForm (freshGamma F c E) q := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  obtain ⟨c₁, hc₁, hlong⟩ := long_flow_coupling_event hLp hIBP A c r₀ s₀ v₀ hK'
  obtain ⟨Cst, hCst, hiso⟩ := isotropic_upper_uniform hELG hMDE hLp (A := A) hK' hε
    (by linarith)
  refine ⟨c₁, hc₁, Cst, hCst, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hlong D
  obtain ⟨N₂, hN₂⟩ := hiso D
  have hpθ : (0 : ℝ) < 1 / 100 := by norm_num
  have hp300 : (0 : ℝ) < 1 / 300 := by norm_num
  have hpe : (0 : ℝ) < 1 - 4 * ε - 1 / 300 := by linarith
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ N₂ ≤ n) ∧ (1 : ℝ) ≤ n ∧
      (n : ℝ) ^ (-(1 / 100 : ℝ)) ≤ s₀ ∧ (n : ℝ) ^ (-(1 / 300 : ℝ)) ≤ 1 / c₁ ∧
      (2 : ℝ) ≤ (n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) ∧
      2 / c₁ ≤ (n : ℝ) ^ (1 - 4 * ε - 1 / 300) := by
    refine ((eventually_ge_atTop N₁).and (eventually_ge_atTop N₂)).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 1).and
      ((eventually_rpow_le hpθ hs0).and
      ((eventually_rpow_le hp300 (by positivity)).and
      ((eventually_rpow_ge (by norm_num) _).and (eventually_rpow_ge hpe _)))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC q => ?_⟩
  obtain ⟨⟨hNN₁, hNN₂⟩, hN1, hτs, hτ300, hℓ2, hℓe⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hNpos : 0 < N := by exact_mod_cast hNp
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
  set ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hNp _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hX : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / N = (N : ℝ) ^ (-(1 / 300 : ℝ)) := by
    rw [← Real.rpow_sub_one hNp.ne']; congr 1; norm_num
  have hℓle : (ℓ : ℝ) ≤ (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) := Nat.floor_le (by positivity)
  have hℓge : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2 ≤ ℓ := by
    have h3 : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) < (ℓ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith [hℓ2, h3]
  have hℓpos : 0 < ℓ := by
    have : (1 : ℝ) ≤ ℓ := by linarith
    exact_mod_cast (show (0 : ℝ) < ℓ by linarith)
  set h : ℝ := c₁ * ℓ / N
  have hh1 : h ≤ 1 := by
    have : h ≤ c₁ * (N : ℝ) ^ (-(1 / 300 : ℝ)) := by
      simp only [h]; rw [mul_div_assoc, ← hX]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hℓle hNp.le) hc₁.le
    have h2 : c₁ * (N : ℝ) ^ (-(1 / 300 : ℝ)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hτ300 hc₁.le
      rwa [mul_one_div_cancel hc₁.ne'] at this
    linarith
  have hhη : (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h := by
    have hlow : c₁ * (N : ℝ) ^ (-(1 / 300 : ℝ)) / 2 ≤ h := by
      simp only [h]
      rw [show c₁ * (N : ℝ) ^ (-(1 / 300 : ℝ)) / 2 =
        c₁ * ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2) / N by rw [← hX]; ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hℓge hc₁.le) hNp.le
    have e : (N : ℝ) ^ (-(1 - 4 * ε)) * (N : ℝ) ^ (1 - 4 * ε - 1 / 300) =
        (N : ℝ) ^ (-(1 / 300 : ℝ)) := by
      rw [← Real.rpow_add hNp]; congr 1; ring
    have hpos : 0 < (N : ℝ) ^ (-(1 - 4 * ε)) := Real.rpow_pos_of_pos hNp _
    have : (N : ℝ) ^ (-(1 - 4 * ε)) * (2 / c₁) ≤ (N : ℝ) ^ (-(1 / 300 : ℝ)) := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hℓe hpos.le
    have : (N : ℝ) ^ (-(1 - 4 * ε)) ≤ c₁ * (N : ℝ) ^ (-(1 / 300 : ℝ)) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      have e2 : (N : ℝ) ^ (-(1 - 4 * ε)) * (2 / c₁) * c₁ = (N : ℝ) ^ (-(1 - 4 * ε)) * 2 := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right this hc₁.le]
    linarith
  obtain ⟨Bad₁, hP₁, hB₁⟩ := hN₁ N hNN₁ F E hC
  obtain ⟨Bad₂, -, hP₂, hB₂⟩ := hN₂ N hNN₂ F E hC (c - τ) τ (by linarith) hτ0 hτ1
    (by linarith) (by linarith) q
  refine ⟨Bad₁ ∪ Bad₂, (measure_union_le _ _).trans (add_le_add hP₁ hP₂), ?_⟩
  intro ω hω hH s hs hsimp i hi
  have hω₁ : ω ∉ Bad₁ := fun h' => hω (Or.inl h')
  have hω₂ : ω ∉ Bad₂ := fun h' => hω (Or.inr h')
  have hl := hB₁ ω hω₁ hH s hs hsimp hNpos hℓpos q i
  have hs' : s ∈ Icc (c - τ) (c - τ + τ) := by rw [sub_add_cancel]; exact hs
  have hi' := hB₂ ω hω₂ hH s hs' (flowEigenvalue F (c - τ) ω s i) hi h hhη hh1
  have hcoef : 0 ≤ 2 / (c₁ * ℓ / N) := by positivity
  calc _ ≤ 2 / (c₁ * ℓ / N) * (star q ⬝ᵥ ((flowMatrix F (c - τ) ω s -
        (⟨flowEigenvalue F (c - τ) ω s i, c₁ * ℓ / N⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := hl
    _ ≤ 2 / (c₁ * ℓ / N) * (Cst * quadForm (freshGamma F c E) q) :=
        mul_le_mul_of_nonneg_left hi' hcoef
    _ = _ := by ring

end BlockBand.Palm.MomentFlow
