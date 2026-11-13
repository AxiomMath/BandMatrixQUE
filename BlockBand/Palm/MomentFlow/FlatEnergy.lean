module

public import BlockBand.Palm.MomentFlow.LongGenScales

/-!
# Window energies for `Flattening`

* **`energy_near_target`** (from `GaussianLpGradient`, `MultivariateGaussianIBP` via
  `spectralGoodEvent_s8`): one `𝓛`-measurable `B`, `P(B) ≤ N^{-D}`. Off `B`, if
  `|λ_{k₀}(u) - E| ≤ r₀/64` at some `u ∈ [a,c]` and `|k - k₀| ≤ 4K_w w`, then for all `v ∈ [a,c]`
  `|λ_k(v) - λ_{k₀}(u)| ≤ 2C√τ + 2max(ℓ/N, (4K_w w + 1)/(c₁N))`. The proof uses the displacement
  clause with Weyl, and `label_proximity` at time `a`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem energy_near_target (hLp : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient)
    (hIBP : BlockBand.Internal.Contracts.Inputs.MultivariateGaussianIBP)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (Kw : ℝ) :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c - cmTau N) (c - cmTau N) c] B ∧
          flowLaw N (c - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ ω ∉ B, ∀ k₀ k : Fin N, ∀ u ∈ Icc (c - cmTau N) c,
            |flowEigenvalue F (c - cmTau N) ω u k₀ - E| ≤ r₀ / 64 →
            (labelDist k₀ k : ℝ) ≤ 4 * (Kw * cmW N) →
            ∀ v ∈ Icc (c - cmTau N) c,
              |flowEigenvalue F (c - cmTau N) ω v k - flowEigenvalue F (c - cmTau N) ω u k₀| ≤
                2 * (C * Real.sqrt (cmTau N)) +
                  2 * max ((cmEll N : ℝ) / N) ((4 * (Kw * cmW N) + 1) / (c₁ * N)) := by
  classical
  obtain ⟨c₁, C₁, C, b₀, hc₁, -, hC, -, hS8⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  refine ⟨c₁, C, hc₁, hC, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hS8 D
  have hwin : ∀ᶠ n : ℕ in atTop, 4 * (Kw * cmW n) ≤ (n : ℝ) ^ (1 - (1 / 1200 : ℝ)) := by
    filter_upwards [eventually_window_le (4 * Kw) 0] with n hn
    rw [Nat.cast_zero, zero_mul, add_zero] at hn
    linarith
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (((eventually_small_scales (C := C) hc₁ hK.2.2.1
    (by norm_num : (0 : ℝ) < 1 / 1200)).and hwin).and (eventually_ge_atTop (max N₁ 1)))
  refine ⟨N₂, fun N hN F E hFC => ?_⟩
  obtain ⟨⟨⟨-, hΔr⟩, hw4⟩, hNN⟩ := hN₂ N hN
  have hN1 : N₁ ≤ N := le_of_max_le_left hNN
  have hNpos : 0 < N := le_of_max_le_right hNN
  have hS := hN₁ N hN1 F E hFC
  dsimp only at hS
  set a : ℝ := c - cmTau N with ha_def
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
  set ρ : ℝ := 4 * (Kw * cmW N)
  set Δ : ℝ := 2 * max ((cmEll N : ℝ) / N) ((ρ + 1) / (c₁ * N))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hΔr' : Δ ≤ r₀ / 32 := by
    refine le_trans ?_ hΔr
    refine mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hF := hFC.1
  have hτ0 : 0 ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have ha : a ∈ Icc a c := ⟨le_rfl, by simp only [a, cmTau]; linarith⟩
  set G1 : Set (FlowSample N) := ⋂ k : Fin N, {ω | ∀ s ∈ Icc a c,
    |flowEigenvalue F a ω s k - flowEigenvalue F a ω a k| ≤ C * Real.sqrt τ}
  set G2 : Set (FlowSample N) := ⋂ k₀ : Fin N, ⋂ k : Fin N,
    ({ω | |flowEigenvalue F a ω a k₀ - E| ≤ r₀ / 16}ᶜ ∪
      {ω | (labelDist k₀ k : ℝ) ≤ ρ → |flowEigenvalue F a ω a k - flowEigenvalue F a ω a k₀| ≤ Δ})
  have hm : ∀ k, Measurable[pathSigma F a a c] fun ω => flowEigenvalue F a ω a k :=
    fun k => measurable_flowEigenvalue_pathSigma F a a c ha k
  have hG1 : MeasurableSet[pathSigma F a a c] G1 := by
    refine MeasurableSet.iInter fun k => measurableSet_forall_Icc_le (fun s hs => ?_)
      (fun ω => ?_) _
    · exact continuous_abs.measurable.comp
        ((measurable_flowEigenvalue_pathSigma F a a c hs k).sub (hm k))
    · exact ((continuous_flowEigenvalue hF a ω k).sub continuous_const).abs.continuousOn
  have hG2 : MeasurableSet[pathSigma F a a c] G2 := by
    refine MeasurableSet.iInter fun k₀ => MeasurableSet.iInter fun k => ?_
    refine MeasurableSet.union (MeasurableSet.compl ?_) ?_
    · exact measurableSet_le (continuous_abs.measurable.comp ((hm k₀).sub_const E))
        measurable_const
    · by_cases hd : (labelDist k₀ k : ℝ) ≤ ρ
      · simp only [hd, forall_const]
        exact measurableSet_le (continuous_abs.measurable.comp ((hm k).sub (hm k₀)))
          measurable_const
      · simp only [hd, false_implies, ofPred_true, MeasurableSet.univ]
  refine ⟨(G1 ∩ G2)ᶜ, (hG1.inter hG2).compl, ?_, ?_⟩
  · have hnull : flowLaw N a {ω : FlowSample N | ¬ ω.1.IsHermitian} = 0 := by
      have := BlockBand.Palm.RelativeLocalization.ae_fst_isHermitian (N := N) a
      rwa [ae_iff] at this
    refine measure_le_of_null_union hnull hS fun ω hH hgood => ?_
    simp only [Set.mem_compl_iff, not_not]
    have hH : ω.1.IsHermitian := not_not.1 hH
    have hgood := not_not.1 (show ¬¬ _ from hgood)
    have hHa := BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hF a hH a
    refine ⟨mem_iInter.2 fun k => fun s hs => ?_, mem_iInter.2 fun k₀ => mem_iInter.2 fun k => ?_⟩
    · have hHs := BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hF a hH s
      exact BlockBand.Palm.GoodEvent.freshEigenvalue_weyl hHs hHa (hgood s hs).2.2.2.2.2 k
    · by_cases hE : |flowEigenvalue F a ω a k₀ - E| ≤ r₀ / 16
      · refine Or.inr fun hd => ?_
        exact label_proximity (lam := fun k => flowEigenvalue F a ω a k)
          (fun i j hij => BlockBand.Palm.GoodEvent.freshEigenvalue_monotone hHa hij) hc₁ hNpos
          (hgood a ha).2.2.2.1 rfl hΔr' hE hd
      · exact Or.inl hE
  · intro ω hω k₀ k u hu hk₀ hd v hv
    obtain ⟨h1, h2⟩ := not_not.1 hω
    have hu1 := mem_iInter.1 h1 k₀ u hu
    have hv1 := mem_iInter.1 h1 k v hv
    have hsq : C * Real.sqrt τ ≤ r₀ / 128 := (hN₂ N hN).1.1.1
    have hk₀a : |flowEigenvalue F a ω a k₀ - E| ≤ r₀ / 16 := by
      have := abs_sub_le (flowEigenvalue F a ω a k₀) (flowEigenvalue F a ω u k₀) E
      rw [abs_sub_comm] at hu1
      linarith [hK.2.2.1]
    have hp : |flowEigenvalue F a ω a k - flowEigenvalue F a ω a k₀| ≤ Δ := by
      rcases mem_iInter.1 (mem_iInter.1 h2 k₀) k with h | h
      · exact absurd hk₀a h
      · exact h hd
    have e1 := abs_sub_le (flowEigenvalue F a ω v k) (flowEigenvalue F a ω a k)
      (flowEigenvalue F a ω u k₀)
    have e2 := abs_sub_le (flowEigenvalue F a ω a k) (flowEigenvalue F a ω a k₀)
      (flowEigenvalue F a ω u k₀)
    have e4 := abs_sub_comm (flowEigenvalue F a ω a k₀) (flowEigenvalue F a ω u k₀)
    have hτe : τ = cmTau N := rfl
    rw [← hτe]
    linarith

end BlockBand.Palm.MomentFlow
