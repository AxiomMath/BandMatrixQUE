module

public import BlockBand.Palm.MomentFlow.Tail6
public import BlockBand.Palm.GoodEventHolds

/-!
# Bulk positions on the whole interval near the target configuration

* `card_between_le`, `label_proximity` (deterministic): for an ordered spectrum satisfying the
  bulk lower count, labels within distance `ρ` of a bulk label `k₀` are within energy
  `Δ = 2 max(ℓ/N, (ρ+1)/(c₁N))` of `λ_{k₀}`.
* `measure_le_of_null_union`: bookkeeping for "bad ⊆ null ∪ small".
* `eventually_small_scales`: `C√τ ≤ r₀/128` and `Δ ≤ r₀/32` for `ρ = N^{1-κ'}`, `N` large.
* **`bulk_near_target`** (consumes `GaussianLpGradient`, `MultivariateGaussianIBP` via
  `spectralGoodEvent_s8`): one `pathSigma F a a c`-measurable bad set of probability `≤ N^{-D}`
  off which `|λ_{k₀}(u) - E| ≤ r₀/64` at one time `u ∈ [a,c]` and `|k - k₀| ≤ N^{1-κ'}` imply
  `|λ_k(v) - E| ≤ r₀/16` at every `v ∈ [a,c]` (displacement clause + Weyl, lower count at time `a`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Points strictly between `λ_{k₀}` and `λ_k` (ordered spectrum) have labels strictly between. -/
theorem card_between_le {lam : Fin N → ℝ} (hmono : Monotone lam) {k₀ k : Fin N} {x y : ℝ}
    (hxy : x ≤ y) (hx : lam k₀ < x) (hy : y < lam k) :
    ((Finset.univ.filter fun i : Fin N => lam i ∈ Icc x y).card : ℝ) + 1 ≤ labelDist k₀ k := by
  have hsub : (Finset.univ.filter fun i : Fin N => lam i ∈ Icc x y) ⊆ Finset.Ioo k₀ k := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    refine Finset.mem_Ioo.2 ⟨?_, ?_⟩
    · by_contra h; push Not at h; linarith [hmono h, hi'.1]
    · by_contra h; push Not at h; linarith [hmono h, hi'.2]
  have hk : k₀ < k := by
    by_contra h; push Not at h; linarith [hmono h]
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Ioo] at hc
  have hkk : (k₀ : ℕ) < k := hk
  have hn : (Finset.univ.filter fun i : Fin N => lam i ∈ Icc x y).card + 1 ≤ labelDist k₀ k := by
    unfold labelDist; omega
  exact_mod_cast hn

/-- **Label proximity from the bulk lower count** (deterministic). -/
theorem label_proximity {lam : Fin N → ℝ} (hmono : Monotone lam) {E r₀ c₁ : ℝ} {ℓ : ℕ}
    (hc₁ : 0 < c₁) (hN : 0 < N)
    (hcount : ∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      c₁ * N * (y - x) ≤ ((Finset.univ.filter fun i : Fin N => lam i ∈ Icc x y).card : ℝ))
    {ρ Δ : ℝ} (hΔ : Δ = 2 * max ((ℓ : ℝ) / N) ((ρ + 1) / (c₁ * N))) (hΔr : Δ ≤ r₀ / 32)
    {k₀ k : Fin N} (hk₀ : |lam k₀ - E| ≤ r₀ / 16) (hd : (labelDist k₀ k : ℝ) ≤ ρ) :
    |lam k - lam k₀| ≤ Δ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (ℓ : ℝ) / N ≤ Δ / 2 := by rw [hΔ]; linarith [le_max_left ((ℓ : ℝ) / N) ((ρ + 1) / (c₁ * N))]
  have hm2 : ρ + 1 ≤ c₁ * N * (Δ / 2) := by
    have h := le_max_right ((ℓ : ℝ) / N) ((ρ + 1) / (c₁ * N))
    rw [div_le_iff₀ (by positivity)] at h
    rw [hΔ]; nlinarith
  have hρ1 : 0 < ρ + 1 := by linarith [(Nat.cast_nonneg (labelDist k₀ k) : (0 : ℝ) ≤ _)]
  have hΔ0 : 0 < Δ := by
    rw [hΔ]
    have : 0 < (ρ + 1) / (c₁ * N) := by positivity
    linarith [le_max_right ((ℓ : ℝ) / N) ((ρ + 1) / (c₁ * N))]
  have hE := abs_le.1 hk₀
  rw [abs_le]
  constructor
  · by_contra h; push Not at h
    have hc := hcount (lam k₀ - 3 * Δ / 4) (lam k₀ - Δ / 4) (by linarith) (by linarith) (by linarith)
    have hb := card_between_le hmono (k₀ := k) (k := k₀) (x := lam k₀ - 3 * Δ / 4)
      (y := lam k₀ - Δ / 4) (by linarith) (by linarith) (by linarith)
    rw [labelDist_comm] at hb
    nlinarith
  · by_contra h; push Not at h
    have hc := hcount (lam k₀ + Δ / 4) (lam k₀ + 3 * Δ / 4) (by linarith) (by linarith) (by linarith)
    have hb := card_between_le hmono (k₀ := k₀) (k := k) (x := lam k₀ + Δ / 4)
      (y := lam k₀ + 3 * Δ / 4) (by linarith) (by linarith) (by linarith)
    nlinarith

theorem eventually_small_scales {c₁ C r₀ κ' : ℝ} (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) (hκ' : 0 < κ') :
    ∀ᶠ n : ℕ in atTop, C * Real.sqrt ((n : ℝ) ^ (-(1 / 100 : ℝ))) ≤ r₀ / 128 ∧
      2 * max ((⌊(n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℝ) / n)
        (((n : ℝ) ^ (1 - κ') + 1) / (c₁ * n)) ≤ r₀ / 32 := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have t1 : Tendsto (fun n : ℕ => C * Real.sqrt ((n : ℝ) ^ (-(1 / 100 : ℝ)))) atTop (nhds 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp hn)).const_mul C
    simpa using this
  have t2 : Tendsto (fun n : ℕ => 2 * max ((n : ℝ) ^ (-(1 / 300 : ℝ)))
      (((n : ℝ) ^ (-κ') + (n : ℝ) ^ (-(1 : ℝ))) / c₁)) atTop (nhds 0) := by
    have a1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 300)).comp hn
    have a2 := (tendsto_rpow_neg_atTop hκ').comp hn
    have a3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp hn
    have := ((a1.max ((a2.add a3).div_const c₁)).const_mul 2)
    simpa using this
  filter_upwards [t1.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < r₀ / 128)),
    t2.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < r₀ / 32)), eventually_ge_atTop 1]
    with n h1 h2 hn1
  refine ⟨h1, le_trans ?_ h2⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine mul_le_mul_of_nonneg_left (max_le_max ?_ (le_of_eq ?_)) (by norm_num)
  · have hfl : (⌊(n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℝ) ≤ (n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) :=
      Nat.floor_le (by positivity)
    calc (⌊(n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℝ) / n
        ≤ (n : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / n := div_le_div_of_nonneg_right hfl hnpos.le
      _ = (n : ℝ) ^ (-(1 / 300 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hnpos]; norm_num
  · have e : (n : ℝ) ^ (1 - κ') = n * (n : ℝ) ^ (-κ') := by
      rw [sub_eq_add_neg, Real.rpow_add hnpos, Real.rpow_one]
    rw [e, Real.rpow_neg_one]; field_simp

theorem measure_le_of_null_union {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B S Z : Set Ω} {x : ENNReal} (hZ : μ Z = 0) (hS : μ S ≤ x)
    (h : ∀ ω, ω ∉ Z → ω ∉ S → ω ∉ B) : μ B ≤ x := by
  refine (measure_mono fun ω hω => ?_).trans ((measure_union_le Z S).trans (by rw [hZ, zero_add]; exact hS))
  by_contra hc
  rw [Set.mem_union, not_or] at hc
  exact h ω hc.1 hc.2 hω

/-- **Bulk on the whole interval near the target configuration** (uses the hypotheses
`GaussianLpGradient`, `MultivariateGaussianIBP` through `spectralGoodEvent_s8`). One
`pathSigma`-measurable `B`, `P(B) ≤ N^{-D}`: off `B`, if `|λ_{k₀}(u) - E| ≤ r₀/64` at some
`u ∈ [a,c]`, every label `k` with `|k - k₀| ≤ N^{1-κ'}` has `|λ_k(v) - E| ≤ r₀/16` at all
`v ∈ [a,c]`. (Displacement clause + Weyl, and the bulk lower count at time `a`.) -/
theorem bulk_near_target (hLp : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient)
    (hIBP : BlockBand.Internal.Contracts.Inputs.MultivariateGaussianIBP)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) {κ' : ℝ} (hκ' : 0 < κ') :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
          flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ ω ∉ B, ∀ k₀ k : Fin N, ∀ u ∈ Icc a c, |flowEigenvalue F a ω u k₀ - E| ≤ r₀ / 64 →
            (labelDist k₀ k : ℝ) ≤ (N : ℝ) ^ (1 - κ') →
            ∀ v ∈ Icc a c, |flowEigenvalue F a ω v k - E| ≤ r₀ / 16 := by
  classical
  obtain ⟨c₁, C₁, C, b₀, hc₁, -, hC, -, hS8⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  intro D
  obtain ⟨N₁, hN₁⟩ := hS8 D
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((eventually_small_scales (C := C) hc₁ hK.2.2.1 hκ').and
    (eventually_ge_atTop (max N₁ 1)))
  refine ⟨N₂, fun N hN F E hFC => ?_⟩
  intro a
  obtain ⟨⟨hsq, hΔr⟩, hNN⟩ := hN₂ N hN
  have hN1 : N₁ ≤ N := le_of_max_le_left hNN
  have hNpos : 0 < N := le_of_max_le_right hNN
  have hS := hN₁ N hN1 F E hFC
  dsimp only at hS
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
  set ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
  set ρ : ℝ := (N : ℝ) ^ (1 - κ')
  set Δ : ℝ := 2 * max ((ℓ : ℝ) / N) ((ρ + 1) / (c₁ * N))
  have hF := hFC.1
  have hτ0 : 0 ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have ha : a ∈ Icc a c := ⟨le_rfl, by simp only [a]; linarith⟩
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
          (hgood a ha).2.2.2.1 rfl hΔr hE hd
      · exact Or.inl hE
  · intro ω hω k₀ k u hu hk₀ hd v hv
    obtain ⟨h1, h2⟩ := not_not.1 hω
    have hu1 := mem_iInter.1 h1 k₀ u hu
    have hv1 := mem_iInter.1 h1 k v hv
    have hk₀a : |flowEigenvalue F a ω a k₀ - E| ≤ r₀ / 16 := by
      have := abs_sub_le (flowEigenvalue F a ω a k₀) (flowEigenvalue F a ω u k₀) E
      rw [abs_sub_comm] at hu1
      linarith [hK.2.2.1]
    have hp : |flowEigenvalue F a ω a k - flowEigenvalue F a ω a k₀| ≤ Δ := by
      rcases mem_iInter.1 (mem_iInter.1 h2 k₀) k with h | h
      · exact absurd hk₀a h
      · exact h hd
    have e1 := abs_sub_le (flowEigenvalue F a ω v k) (flowEigenvalue F a ω a k) E
    have e2 := abs_sub_le (flowEigenvalue F a ω a k) (flowEigenvalue F a ω a k₀) E
    have e3 := abs_sub_le (flowEigenvalue F a ω a k₀) (flowEigenvalue F a ω u k₀) E
    have e4 := abs_sub_comm (flowEigenvalue F a ω a k₀) (flowEigenvalue F a ω u k₀)
    linarith [hK.2.2.1]

end BlockBand.Palm.MomentFlow
