module

public import BlockBand.Palm.MomentFlow.StepPath
public import BlockBand.Palm.MomentFlow.StepAsym
public import BlockBand.Palm.MomentFlow.StepErr
public import BlockBand.Palm.MomentFlow.AvgMeas
public import BlockBand.Palm.MomentFlow.RemUnif
public import BlockBand.Palm.MomentFlow.PropLongShort
public import BlockBand.Palm.MomentFlow.MaxCount

/-!
# The induction step on one sample

* `coef_rpow_le_abs`: `C N^{C₁ε} X ≤ |C| N^{|C₁|ε} X`.
* **`stepSample`**: the `CM(r, M)` conclusion on one sample, with the constant part
  `Main + G e^{-(rv₀/η) 2^{-(r+1)} τ} + maxPathErr/(rv₀/η)` and an explicit integrated-error
  bound `(1 + K_co N)(1 + N^{r+1}(3 + (|C₂⁴|+1)N)) N^{-D'}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Transmission BlockBand.Palm.CoarseRelative BlockBand.Palm

variable {N : ℕ}

theorem coef_rpow_le_abs {C C₁ ε X : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hX : 0 ≤ X) :
    C * (N : ℝ) ^ (C₁ * ε) * X ≤ |C| * (N : ℝ) ^ (|C₁| * ε) * X := by
  have h1 : (N : ℝ) ^ (C₁ * ε) ≤ (N : ℝ) ^ (|C₁| * ε) :=
    rpow_le_rpow_exp hN (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  have h2 : C * (N : ℝ) ^ (C₁ * ε) ≤ |C| * (N : ℝ) ^ (|C₁| * ε) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
  exact mul_le_mul_of_nonneg_right h2 hX

theorem inRank_mono {k₀ : Fin N} {ρ ρ' : ℝ} {ξ : Occ N} (h : InRank k₀ ρ ξ) (hρ : ρ ≤ ρ') :
    InRank k₀ ρ' ξ := fun j hj => (h j hj).trans hρ

theorem labelDist_le_rampDist (k₀ : Fin N) {ξ : Occ N} {i : Fin N} (hi : 0 < ξ i) :
    (labelDist i k₀ : ℝ) ≤ rampDist (k₀ : ℕ) ξ := by
  exact_mod_cast (rampDist_le_iff k₀ ξ _).1 le_rfl i hi

set_option maxHeartbeats 1000000 in
/-- The induction step on one sample: construction and the `maxPath` bound. -/
theorem stepSample_core {r : ℕ} (hr : 1 ≤ r) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {q : Fin N → ℂ} {ω : FlowSample N} {Φ Ψ : ℝ → Occ N → FlowSample N → ℝ}
    {M Kw M' Kδ C₁₃ C₂₃ C₁₄ C₂₄ CR CA CL κ' C' KB p ε D' : ℝ}
    (hKw : Kw = 2 * (|M| + 1)) (hKδ : Kδ = |C₂₄| * (|M| + Kw) + 1)
    (hM' : |C₂₄| * (|M| + Kw) + 2 * Kw ≤ M')
    (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
    (hCR : 0 ≤ CR) (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hKB : 1 ≤ KB) (hD' : 0 ≤ D')
    (hN : 1 ≤ N) (hτs : cmTau N ≤ s₀)
    (hδ : Kδ * (cmW N / N) ≤ r₀ / 2) (hEA1 : stEA CR (slowConst c₀ r₀ s₀ v₀) v₀ Kδ ε N ≤ 1)
    (hE21 : stE2 CA ε N ≤ 1) (hβ1 : 1 ≤ stBeta r (v₀⁻¹ + 1) Kw N)
    (hcoll : ∀ σ, c₀ - cmTau N ≤ σ → ∀ i j : Fin N, i ≠ j →
      flowEigenvalue F (c₀ - cmTau N) ω σ i ≠ flowEigenvalue F (c₀ - cmTau N) ω σ j)
    (hherm : ω.1.IsHermitian)
    (hΦs : IsMomentFlowSolution (flowRate F (c₀ - cmTau N) ω) r (c₀ - cmTau N) c₀
      (fun σ ξ => Φ σ ξ ω))
    (hΦ0 : ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ξ ∈ sector N r, 0 ≤ Φ u ξ ω)
    (hΨ0 : ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ξ ∈ sector N (r - 1), 0 ≤ Ψ u ξ ω)
    (hqB : max 1 ((N : ℝ) * nsq q) ≤ stB1 KB p N)
    (hR2 : ∀ k : ℕ, k ≤ stL N → ∀ ξ ∈ sector N r, ∀ i : Fin N, 0 < ξ i →
      ∀ s ∈ Icc (c₀ - cmTau N) c₀,
      |flowEigenvalue F (c₀ - cmTau N) ω s i - E| < Kδ * (cmW N / N) →
      |∑ j, remKernel F (c₀ - cmTau N) ω s i j (2 ^ k * cmEta N ε) * remCoef ξ i j *
          zeroExt r Φ s (remTarget ξ i j) ω -
        (freshDyson F s ⟨flowEigenvalue F (c₀ - cmTau N) ω s i, 2 ^ k * cmEta N ε⟩).im *
          zeroExt (r - 1) Ψ s (remove ξ i) ω| ≤
        (CR * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * (2 ^ k * cmEta N ε)) +
            v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ *
              (Kδ * (cmW N / N) + 2 ^ k * cmEta N ε + (c₀ - s))) *
          zeroExt (r - 1) Ψ s (remove ξ i) ω +
        max 1 ((N : ℝ) * nsq q) ^ r *
          ((N : ℝ) * ((N : ℝ)⁻¹ * (2 ^ k * cmEta N ε)⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) *
          (N : ℝ) ^ (-(D' + (((r : ℝ) + 1) * (p + 1) + 1))))
    (hAvg : ∀ σ ∈ Icc (c₀ - cmTau N) c₀, ∀ x : ℝ, |x - E| ≤ r₀ / 2 →
      ∀ h : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h → h ≤ 1 →
      |(N : ℝ)⁻¹ * ∑ k, h / ((flowEigenvalue F (c₀ - cmTau N) ω σ k - x) ^ 2 + h ^ 2) -
        (freshDyson F σ ⟨x, h⟩).im| ≤ CA * (N : ℝ) ^ ε / ((N : ℝ) * h))
    (hLong : ∀ s ∈ Icc (c₀ - cmTau N) c₀, ∀ i : Fin N,
      longCoupling F (c₀ - cmTau N) ω (cmEll N) s i ≤ CL * N / cmEll N)
    (hIH : ∃ e : ℝ → ℝ, ContErr e (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ k₀ - E| ≤ M' * cmW N / N →
        ∀ ξ ∈ sector N (r - 1), InRank k₀ (M' * cmW N) ξ →
          |Ψ σ ξ ω - 1| ≤ C' * (N : ℝ) ^ (-κ') + e σ)
    (hP6 : ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
        ∀ h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
          (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ =
            if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N then 1 else 0) →
          ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
            2 * (Kw * cmW N) < (rampDist (k₀ : ℕ) ζ : ℝ) → h u ζ ≤ e u)
    (hL3 : ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
        ∀ h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
          (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ = Φ (c₀ - cmTau N) ζ ω) →
          ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
            (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
            |Φ u ζ ω - h u ζ| ≤
              C₂₃ * (N : ℝ) ^ (C₁₃ * ε) * ((N : ℝ) * cmTau N / cmEll N) + e u)
    (hL4 : ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
        (∀ ζ ∈ sector N r, (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
          0 ≤ Φ (c₀ - cmTau N) ζ ω ∧
            Φ (c₀ - cmTau N) ζ ω ≤ C₂₄ * (N : ℝ) ^ (C₁₄ * ε)) ∧
        (∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ j : Fin N,
          (labelDist j k₀ : ℝ) ≤ 4 * (Kw * cmW N) →
          |flowEigenvalue F (c₀ - cmTau N) ω u j - E| ≤ C₂₄ * (M + Kw) * cmW N / N) ∧
        ∀ g h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r g →
          ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
          (∀ ζ ∈ sector N r, g (c₀ - cmTau N) ζ =
            avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ' => Φ (c₀ - cmTau N) ζ' ω) ζ) →
          (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ = Φ (c₀ - cmTau N) ζ ω) →
          ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
            |g u ζ - avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (h u) ζ| ≤
              C₂₄ * (N : ℝ) ^ (C₁₄ * ε) * ((cmEll N : ℝ) / cmW N) + e u) :
    ∃ ρ e₃ e₄ e₆ e' : ℝ → ℝ, IntErr e₃ (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      IntErr e₄ (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      IntErr e₆ (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ContErr e' (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ContinuousOn ρ (Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀) ∧
      (∀ u ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, 0 ≤ ρ u ∧
        ρ u ≤ e' u + (N : ℝ) * ((N : ℝ) ^ r * (e₃ u + e₄ u) +
          (stG C₁₄ C₂₄ ε N + 1) * ((N : ℝ) ^ r * e₆ u))) ∧
      ∀ σ ∈ Icc (c₀ - cmTau N + cmT r * cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ k₀ - E| ≤ M * cmW N / N →
        ∀ ξ ∈ sector N r, InRank k₀ (M * cmW N) ξ →
          |Φ σ ξ ω - 1| ≤ (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N + stG C₁₄ C₂₄ ε N *
            Real.exp (-((r : ℝ) * v₀ / cmEta N ε) * ((1 / 2 : ℝ) ^ (r + 1) * cmTau N)) +
            maxPathErr N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) (stG C₁₄ C₂₄ ε N)
              (max v₀ v₀⁻¹) (stE2 CA ε N) (stE3 CL ε N) (stE4 C' κ' N)
              (stEA CR (slowConst c₀ r₀ s₀ v₀) v₀ Kδ ε N * (1 + stE4 C' κ' N) +
                stEB r KB p v₀ ε N)
              (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) (stL N) / ((r : ℝ) * v₀ / cmEta N ε)) + ρ σ +
            ∫ t in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..σ,
              maxPathCoef N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) v₀ (max v₀ v₀⁻¹)
                (stE2 CA ε N) (stL N) * ρ t := by
  classical
  -- basic scales
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ : 0 < cmTau N := cmTau_pos (by omega)
  have hη : 0 < cmEta N ε := cmEta_pos hN ε
  have hw : 0 < cmW N := cmW_pos hN
  have hKw0 : 0 < Kw := by rw [hKw]; positivity
  have hwd : 0 < Kw * cmW N := mul_pos hKw0 hw
  have hv₀ : 0 < v₀ := hK.2.2.2.2.2
  have hslow := slowConst_nonneg hK
  have hr₀ : 0 < r₀ := hK.2.2.1
  have hac : c₀ - cmTau N ≤ c₀ := by linarith
  have hT0 : 0 ≤ cmT (r - 1) := by
    unfold cmT
    have : ((1 : ℝ) / 2) ^ (r - 1 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hT1 := cmT_le_one (r - 1)
  have hTr : cmT r - cmT (r - 1) = (1 / 2 : ℝ) ^ (r + 1) := by
    unfold cmT
    rw [Nat.sub_add_cancel hr, pow_succ]; ring
  have hTr1 := cmT_le_one r
  have has : c₀ - cmTau N ≤ c₀ - cmTau N + cmT (r - 1) * cmTau N := by nlinarith
  have hsb : c₀ - cmTau N + cmT (r - 1) * cmTau N ≤ c₀ := by nlinarith
  have hηle : cmEta N ε ≤ 1 := asym_eta_le_one hN hε hε5
  have hηge : (N : ℝ) ^ (-(1 - 4 * ε)) ≤ cmEta N ε := asym_eta_ge hN hε hε5
  have h2L : ∀ k ≤ stL N, (2 : ℝ) ^ k * cmEta N ε ≤ 2 ^ stL N * cmEta N ε := fun k hk =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hη.le
  have h2L1 : (2 : ℝ) ^ stL N * cmEta N ε ≤ 1 := (asym_two_pow_eta hN hε hε5).trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num))
  have hkη : ∀ k : ℕ, cmEta N ε ≤ 2 ^ k * cmEta N ε := fun k =>
    le_mul_of_one_le_left hη.le (one_le_pow₀ (by norm_num))
  have hs₀c : c₀ - s₀ ≤ c₀ - cmTau N := by linarith
  have hmono : ∀ u, Monotone (fun k => flowEigenvalue F (c₀ - cmTau N) ω u k) := fun u =>
    BlockBand.Palm.RelativeLocalization.freshEigenvalue_monotone
      (flowMatrix_isHermitian hC.1 _ hherm u)
  -- rates and flows
  have hgap : ∀ x ∈ Icc (c₀ - cmTau N) c₀, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F (c₀ - cmTau N) ω x k ≠ flowEigenvalue F (c₀ - cmTau N) ω x l :=
    fun x hx k l hkl => hcoll x hx.1 k l hkl
  have hcont := continuousOn_shortFlowRate hC.1 (c₀ - cmTau N) ω (cmEll N) hgap
  have hc0 : ∀ u ∈ Ioo (c₀ - cmTau N) c₀, ∀ i j : Fin N, i ≠ j →
      0 ≤ shortFlowRate F (c₀ - cmTau N) ω (cmEll N) u i j :=
    fun u _ i j _ => shortFlowRate_nonneg F _ ω _ u i j
  obtain ⟨e₆, he₆, hP6'⟩ := hP6
  obtain ⟨e₃, he₃, hL3'⟩ := hL3
  obtain ⟨e₄, he₄, hL4'⟩ := hL4
  obtain ⟨e', he', hIH'⟩ := hIH
  have hF := fun f : Occ N → ℝ => exists_forward hac hcont r f
  let gf : Fin N → ℝ → Occ N → ℝ := fun k₀ =>
    Classical.choose (hF (avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ => Φ (c₀ - cmTau N) ζ ω)))
  have hgf : ∀ k₀ : Fin N, IsMomentFlowSolution (shortFlowRate F (c₀ - cmTau N) ω (cmEll N)) r
      (c₀ - cmTau N) c₀ (gf k₀) ∧ ∀ ζ ∈ sector N r, gf k₀ (c₀ - cmTau N) ζ =
        avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ => Φ (c₀ - cmTau N) ζ ω) ζ :=
    fun k₀ => Classical.choose_spec (hF _)
  let hf : Fin N → ℝ → Occ N → ℝ := fun k₀ =>
    Classical.choose (hF (fun ζ => if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N then 1 else 0))
  have hhf : ∀ k₀ : Fin N, IsMomentFlowSolution (shortFlowRate F (c₀ - cmTau N) ω (cmEll N)) r
      (c₀ - cmTau N) c₀ (hf k₀) ∧ ∀ ζ ∈ sector N r, hf k₀ (c₀ - cmTau N) ζ =
        if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N then 1 else 0 :=
    fun k₀ => Classical.choose_spec (hF _)
  obtain ⟨hsf, hsf1, hsf2⟩ := hF (fun ζ => Φ (c₀ - cmTau N) ζ ω)
  let K : Finset (Fin N) := univ.filter fun k₀ => ∃ σ₀ ∈ Icc (c₀ - cmTau N) c₀,
    |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N
  have hKmem : ∀ k₀ ∈ K, ∃ σ₀ ∈ Icc (c₀ - cmTau N) c₀,
      |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N :=
    fun k₀ hk => (Finset.mem_filter.1 hk).2
  -- per-centre consequences of the Props
  have hC₂₄ : ∀ X : ℝ, 0 ≤ X → C₂₄ * (N : ℝ) ^ (C₁₄ * ε) * X ≤
      |C₂₄| * (N : ℝ) ^ (|C₁₄| * ε) * X := fun X hX => coef_rpow_le_abs hN hε.le hX
  have hC₂₃ : ∀ X : ℝ, 0 ≤ X → C₂₃ * (N : ℝ) ^ (C₁₃ * ε) * X ≤
      |C₂₃| * (N : ℝ) ^ (|C₁₃| * ε) * X := fun X hX => coef_rpow_le_abs hN hε.le hX
  have hEn : |C₂₄| * (|M| + Kw) * cmW N / N < Kδ * (cmW N / N) := by
    rw [hKδ, mul_div_assoc]
    have : 0 < cmW N / N := by positivity
    nlinarith
  have hEn'' : ∀ k₀ ∈ K, ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ j : Fin N,
      (labelDist j k₀ : ℝ) ≤ 4 * (Kw * cmW N) →
      |flowEigenvalue F (c₀ - cmTau N) ω u j - E| ≤ |C₂₄| * (|M| + Kw) * cmW N / N := by
    intro k₀ hk u hu j hj
    obtain ⟨σ₀, hσ₀, hE₀⟩ := hKmem k₀ hk
    have h1 := (hL4' σ₀ hσ₀ k₀ hE₀).2.1 u hu j hj
    have h2 : C₂₄ * (M + Kw) ≤ |C₂₄| * (|M| + Kw) := by
      calc C₂₄ * (M + Kw) ≤ |C₂₄ * (M + Kw)| := le_abs_self _
        _ = |C₂₄| * |M + Kw| := abs_mul _ _
        _ ≤ |C₂₄| * (|M| + Kw) := mul_le_mul_of_nonneg_left
            ((abs_add_le M Kw).trans (by rw [abs_of_pos hKw0])) (abs_nonneg _)
    have h3 : C₂₄ * (M + Kw) * cmW N / N ≤ |C₂₄| * (|M| + Kw) * cmW N / N := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have hEn' : ∀ k₀ ∈ K, ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ j : Fin N,
      (labelDist j k₀ : ℝ) ≤ 4 * (Kw * cmW N) →
      |flowEigenvalue F (c₀ - cmTau N) ω u j - E| < Kδ * (cmW N / N) :=
    fun k₀ hk u hu j hj => (hEn'' k₀ hk u hu j hj).trans_lt hEn
  -- energies of the occupied labels of window configurations
  have hEnξ : ∀ k₀ ∈ K, ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ξ : Occ N,
      (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * (Kw * cmW N) → ∀ i, 0 < ξ i →
      |flowEigenvalue F (c₀ - cmTau N) ω u i - E| < Kδ * (cmW N / N) := by
    intro k₀ hk u hu ξ hP i hi
    refine hEn' k₀ hk u hu i ((labelDist_le_rampDist k₀ hi).trans (by linarith))
  have hIcc : ∀ u ∈ Ioo (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, u ∈ Icc (c₀ - cmTau N) c₀ :=
    fun u hu => ⟨has.trans hu.1.le, hu.2.le⟩
  set V : ℝ → ℝ → Fin N → ℝ := fun h u i =>
    (freshDyson F u ⟨flowEigenvalue F (c₀ - cmTau N) ω u i, h⟩).im with hVdef
  have hVb : ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ i : Fin N,
      |flowEigenvalue F (c₀ - cmTau N) ω u i - E| ≤ r₀ → ∀ h, 0 ≤ h → h ≤ 1 →
      v₀ ≤ V h u i ∧ V h u i ≤ v₀⁻¹ := by
    intro u hu i hi h h0 h1
    exact fresh_regular_bounds hC.2.2 ⟨hs₀c.trans hu.1, hu.2⟩ (z := ⟨_, h⟩) hi h0 h1
  have hAvk : ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ i : Fin N,
      |flowEigenvalue F (c₀ - cmTau N) ω u i - E| ≤ r₀ / 2 → ∀ h, cmEta N ε ≤ h → h ≤ 1 →
      |∑ j, kerAt (fun k => flowEigenvalue F (c₀ - cmTau N) ω u k) h i j - V h u i| ≤
        stE2 CA ε N := by
    intro u hu i hi h hh hh1
    have h1 := averaged_measurable_kerAt i (hAvg u hu _ hi h (hηge.trans hh) hh1)
    refine h1.trans ?_
    unfold stE2
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hh hNp.le
  -- the removal average in the form of `stepPath`
  have hR2' : ∀ k₀ ∈ K, ∀ u ∈ Ioo (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀,
      ∀ ξ ∈ sector N r, (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * (Kw * cmW N) → ∀ i, 0 < ξ i →
      ∀ k ≤ stL N,
      |remSum (kerAt (fun k => flowEigenvalue F (c₀ - cmTau N) ω u k) (2 ^ k * cmEta N ε))
          (fun ζ => Φ u ζ ω) ξ i - V (2 ^ k * cmEta N ε) u i * Ψ u (remove ξ i) ω| ≤
        stEA CR (slowConst c₀ r₀ s₀ v₀) v₀ Kδ ε N * Ψ u (remove ξ i) ω +
          stEB r KB p v₀ ε N := by
    intro k₀ hk u hu ξ hξ hP i hi k hkL
    have hu' := hIcc u hu
    have h := hR2 k hkL ξ hξ i hi u hu' (hEnξ k₀ hk u hu' ξ hP i hi)
    have e1 : ∑ j, remKernel F (c₀ - cmTau N) ω u i j (2 ^ k * cmEta N ε) * remCoef ξ i j *
        zeroExt r Φ u (remTarget ξ i j) ω =
        remSum (kerAt (fun k => flowEigenvalue F (c₀ - cmTau N) ω u k) (2 ^ k * cmEta N ε))
          (fun ζ => Φ u ζ ω) ξ i := by
      unfold remSum
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zeroExt_of_mem Φ (remTarget_mem_sector hξ hi j)]; rfl
    have e2 : zeroExt (r - 1) Ψ u (remove ξ i) ω = Ψ u (remove ξ i) ω :=
      zeroExt_of_mem Ψ (remove_mem_sector hξ hi) u ω
    rw [e1, e2] at h
    refine h.trans (add_le_add (mul_le_mul_of_nonneg_right ?_
      (hΨ0 u hu' _ (remove_mem_sector hξ hi))) ?_)
    · unfold stEA
      have a1 : CR * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * (2 ^ k * cmEta N ε)) ≤
          CR * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * cmEta N ε) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by positivity))
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hkη k) hNp.le))
      have a2 : Kδ * (cmW N / N) + 2 ^ k * cmEta N ε + (c₀ - u) ≤
          Kδ * (cmW N / N) + 2 ^ stL N * cmEta N ε + cmTau N := by
        have := h2L k hkL; linarith [hu'.1]
      have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ v₀⁻¹ * slowConst c₀ r₀ s₀ v₀)
      linarith
    · unfold stEB
      have hB1 : (1 : ℝ) ≤ max 1 ((N : ℝ) * nsq q) := le_max_left _ _
      have b1 : max 1 ((N : ℝ) * nsq q) ^ r ≤ stB1 KB p N ^ r :=
        pow_le_pow_left₀ (by linarith) hqB r
      have b2 : (N : ℝ) * ((N : ℝ)⁻¹ * (2 ^ k * cmEta N ε)⁻¹ * max 1 ((N : ℝ) * nsq q)) +
          v₀⁻¹ ≤ stB1 KB p N / cmEta N ε + v₀⁻¹ := by
        have e : (N : ℝ) * ((N : ℝ)⁻¹ * (2 ^ k * cmEta N ε)⁻¹ * max 1 ((N : ℝ) * nsq q)) =
            max 1 ((N : ℝ) * nsq q) / (2 ^ k * cmEta N ε) := by field_simp
        rw [e]
        have : max 1 ((N : ℝ) * nsq q) / (2 ^ k * cmEta N ε) ≤ stB1 KB p N / cmEta N ε :=
          div_le_div₀ (by linarith) hqB hη (hkη k)
        linarith
      have b3 : (N : ℝ) ^ (-(D' + (((r : ℝ) + 1) * (p + 1) + 1))) ≤
          (N : ℝ) ^ (-(((r : ℝ) + 1) * (p + 1) + 1)) := rpow_le_rpow_exp hN (by linarith)
      have b0 : 0 ≤ (N : ℝ) * ((N : ℝ)⁻¹ * (2 ^ k * cmEta N ε)⁻¹ * max 1 ((N : ℝ) * nsq q)) +
          v₀⁻¹ := by positivity
      have hB0 : 0 ≤ stB1 KB p N := zero_le_one.trans (hB1.trans hqB)
      have c1 := mul_le_mul b1 b2 b0 (pow_nonneg hB0 r)
      exact mul_le_mul c1 b3 (by positivity) (mul_nonneg (pow_nonneg hB0 r) (by positivity))
  -- the other inputs of `stepPath`
  have hδr : ∀ k₀ ∈ K, ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ξ : Occ N,
      (rampDist (k₀ : ℕ) ξ : ℝ) ≤ 2 * (Kw * cmW N) → ∀ i, 0 < ξ i →
      |flowEigenvalue F (c₀ - cmTau N) ω u i - E| ≤ r₀ / 2 := fun k₀ hk u hu ξ hP i hi =>
    ((hEnξ k₀ hk u hu ξ hP i hi).trans_le hδ).le
  have hG1 : 1 ≤ stG C₁₄ C₂₄ ε N := by
    unfold stG
    have : 0 ≤ |C₂₄| * (N : ℝ) ^ (|C₁₄| * ε) := by positivity
    linarith
  have hℓ1 : 1 ≤ cmEll N := by have := cmEll_pos hN; exact_mod_cast this
  have hΦa : ∀ k₀ ∈ K, ∀ ζ ∈ sector N r, (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
      0 ≤ Φ (c₀ - cmTau N) ζ ω ∧ Φ (c₀ - cmTau N) ζ ω ≤ stG C₁₄ C₂₄ ε N := by
    intro k₀ hk ζ hζ hd
    obtain ⟨σ₀, hσ₀, hE₀⟩ := hKmem k₀ hk
    obtain ⟨h1, h2⟩ := (hL4' σ₀ hσ₀ k₀ hE₀).1 ζ hζ hd
    refine ⟨h1, h2.trans ?_⟩
    have := hC₂₄ 1 zero_le_one
    simp only [mul_one] at this
    unfold stG; linarith
  have hb := stepPath (N := N) (r := r) (ℓ := cmEll N) (L := stL N) hr
    (c := shortFlowRate F (c₀ - cmTau N) ω (cmEll N))
    (lam := fun u k => flowEigenvalue F (c₀ - cmTau N) ω u k)
    (a := c₀ - cmTau N) (s := c₀ - cmTau N + cmT (r - 1) * cmTau N) (b := c₀) (η := cmEta N ε)
    (G := stG C₁₄ C₂₄ ε N) (v := v₀) (Vb := max v₀ v₀⁻¹) (E₂ := stE2 CA ε N)
    (E₃ := stE3 CL ε N) (E₄ := stE4 C' κ' N) (eA := stEA CR (slowConst c₀ r₀ s₀ v₀) v₀ Kδ ε N)
    (eB := stEB r KB p v₀ ε N) (Main := stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N)
    (β := stBeta r (v₀⁻¹ + 1) Kw N) (wd := Kw * cmW N)
    has hsb hη hv₀ (le_max_left _ _) hG1 (by unfold stE2; positivity)
    (by unfold stE3; have := cmEll_pos hN; positivity) (by unfold stE4; positivity)
    (by have : 0 ≤ Kδ := by rw [hKδ]; positivity
        unfold stEA; unfold cmTau; positivity) hEA1
    (by unfold stEB stB1; have : (0 : ℝ) ≤ KB := by linarith
        positivity)
    (by unfold stMain; have := cmEll_pos hN; unfold cmTau; positivity)
    (by unfold stBeta; positivity) hwd hc0
    (fun u hu i j hij hl => kerAt_le_shortFlowRate F _ ω _ u hη.le
      (hcoll u (hIcc u hu).1 i j hij) hl)
    (fun u _ i j _ hl => shortFlowRate_long F _ ω _ u hl)
    (Φ := fun u ζ => Φ u ζ ω) (Ψ := fun u ζ => Ψ u ζ ω)
    (fun ζ hζ => (hΦs ζ hζ).1.mono (Icc_subset_Icc has le_rfl))
    (fun u hu ξ hξ => hΦ0 u ⟨has.trans hu.1, hu.2⟩ ξ hξ)
    (eI := e') he'.1 he'.2.1 K gf hf (fun k₀ _ => (hgf k₀).1) (fun k₀ _ => (hhf k₀).1)
    (fun k₀ _ => (hgf k₀).2) (fun k₀ _ => (hhf k₀).2) hΦa V
    (fun k₀ hk u hu ξ hξ hP i hi => by
      have hu' := hIcc u hu
      have hr0 : |flowEigenvalue F (c₀ - cmTau N) ω u i - E| ≤ r₀ := by
        have := hδr k₀ hk u hu' ξ hP i hi; linarith
      obtain ⟨a1, a2⟩ := hVb u hu' i hr0 (cmEta N ε) hη.le hηle
      refine ⟨a1, a2.trans (le_max_right _ _), fun k hk => ?_⟩
      obtain ⟨b1, b2⟩ := hVb u hu' i hr0 (2 ^ k * cmEta N ε) (by positivity)
        ((h2L k hk).trans h2L1)
      exact ⟨hv₀.le.trans b1, b2.trans (le_max_right _ _)⟩)
    (fun k₀ hk u hu ξ hξ hP i hi => by
      have h0 := hR2' k₀ hk u hu ξ hξ hP i hi 0 (Nat.zero_le _)
      simp only [pow_zero, one_mul] at h0
      exact ⟨h0, fun k hk' => hR2' k₀ hk u hu ξ hξ hP i hi k hk'⟩)
    (fun k₀ hk u hu ξ hξ hP i hi => by
      have hu' := hIcc u hu
      have hr0 := hδr k₀ hk u hu' ξ hP i hi
      exact ⟨hAvk u hu' i hr0 _ le_rfl hηle, fun k hk' => hAvk u hu' i hr0 _ (hkη k)
        ((h2L k hk').trans h2L1)⟩)
    (fun k₀ hk u hu ξ hξ hP i hi => by
      have hu' := hIcc u hu
      have h1 := longKer_le_longCoupling F (c₀ - cmTau N) ω (cmEll N) u hη.le i
        (fun j hj => hcoll u hu'.1 i j (by
          rintro rfl; simp [labelDist] at hj; omega))
      refine h1.trans ?_
      unfold stE3
      exact mul_le_mul_of_nonneg_left (hLong u hu' i) hη.le)
    (fun k₀ hk u hu ξ hξ hP i hi => by
      have hu' := hIcc u hu
      have hus : u ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ := ⟨hu.1.le, hu.2.le⟩
      have hE0 : |flowEigenvalue F (c₀ - cmTau N) ω u k₀ - E| ≤ M' * cmW N / N := by
        refine (hEn'' k₀ hk u hu' k₀ (by simp [labelDist]; positivity)).trans ?_
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg C₂₄, abs_nonneg M])
          (by positivity)
      have hR : InRank k₀ (M' * cmW N) (remove ξ i) := by
        refine inRank_mono (inRank_remove (inRank_of_rampDist_le hP) i) ?_
        have : 2 * Kw ≤ M' := by nlinarith [abs_nonneg C₂₄, abs_nonneg M]
        nlinarith
      have h := hIH' u hus k₀ hE0 (remove ξ i) (remove_mem_sector hξ hi) hR
      refine h.trans ?_
      unfold stE4
      have := mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity :
        (0 : ℝ) ≤ (N : ℝ) ^ (-κ'))
      linarith)
    (fun k₀ hk u hu ξ hξ hP i hi j => by
      have hu' := hIcc u hu
      have hr0 := hδr k₀ hk u hu' ξ hP i hi
      refine ramp_lip_of_count (hmono u) hη hwd rfl hβ1 (k₀ : ℕ) hξ hi (fun h hh hh1 => ?_) j
      have a1 := hAvk u hu' i hr0 h hh hh1
      have hr0' : |flowEigenvalue F (c₀ - cmTau N) ω u i - E| ≤ r₀ := by linarith
      have a2 := (hVb u hu' i hr0' h (hη.le.trans hh) hh1).2
      have := (abs_le.1 a1).2
      linarith)
  -- the continuous error and its bound
  have hsub : Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ ⊆ Icc (c₀ - cmTau N) c₀ :=
    Icc_subset_Icc has le_rfl
  have hG0 : 0 ≤ stG C₁₄ C₂₄ ε N := by linarith
  have hhf0 : ∀ k₀ ∈ K, ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r, 0 ≤ hf k₀ u ζ := by
    intro k₀ _ u hu ζ hζ
    refine (hhf k₀).1.ge_of_initial_ge hc0 (m := 0) (fun ξ hξ => ?_) u hu ζ hζ
    rw [(hhf k₀).2 ξ hξ]; split_ifs <;> norm_num
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = stepRho r K (Kw * cmW N) (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N)
      (stG C₁₄ C₂₄ ε N) e' (fun u ζ => Φ u ζ ω) gf hf := ⟨_, rfl⟩
  have hρc : ContinuousOn ρ (Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀) := hρdef ▸
    continuousOn_stepRho he'.1 (fun ζ hζ => (hΦs ζ hζ).1.mono hsub)
      (fun k₀ _ ζ hζ => ((hgf k₀).1 ζ hζ).1.mono hsub)
      (fun k₀ _ ζ hζ => ((hhf k₀).1 ζ hζ).1.mono hsub)
  have hρ0 : ∀ u ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, 0 ≤ ρ u := fun u hu => hρdef ▸
    stepRho_nonneg (he'.2.1 u hu) hG0 (fun k₀ hk ζ hζ => hhf0 k₀ hk u (hsub hu) ζ hζ)
  have hρb : ∀ u ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, ρ u ≤
      e' u + (N : ℝ) * ((N : ℝ) ^ r * (e₃ u + e₄ u) +
        (stG C₁₄ C₂₄ ε N + 1) * ((N : ℝ) ^ r * e₆ u)) := by
    intro u hu
    have hu' := hsub hu
    have h30 := he₃.1 u hu'
    have h40 := he₄.1 u hu'
    have h60 := he₆.1 u hu'
    rw [hρdef]; unfold stepRho
    refine add_le_add le_rfl ?_
    have hcard := card_sector_le_real N r
    have hterm : ∀ k₀ ∈ K, ∑ ζ ∈ sector N r, max 0 (|gf k₀ u ζ -
          avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ => Φ u ζ ω) ζ| -
            stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) +
        (stG C₁₄ C₂₄ ε N + 1) * ∑ ζ ∈ (sector N r).filter
          (fun ζ => 2 * (Kw * cmW N) < (rampDist (k₀ : ℕ) ζ : ℝ)), hf k₀ u ζ ≤
        (N : ℝ) ^ r * (e₃ u + e₄ u) + (stG C₁₄ C₂₄ ε N + 1) * ((N : ℝ) ^ r * e₆ u) := by
      intro k₀ hk
      obtain ⟨σ₀, hσ₀, hE₀⟩ := hKmem k₀ hk
      have hA : ∑ ζ ∈ sector N r, max 0 (|gf k₀ u ζ -
          avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ => Φ u ζ ω) ζ| -
            stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) ≤ (N : ℝ) ^ r * (e₃ u + e₄ u) := by
        refine (Finset.sum_le_sum (g := fun _ => e₃ u + e₄ u) fun ζ hζ => ?_).trans ?_
        · refine max_le (by linarith) ?_
          have c1 := (hL4' σ₀ hσ₀ k₀ hE₀).2.2 (gf k₀) hsf (hgf k₀).1 hsf1 (hgf k₀).2 hsf2 u hu'
            ζ hζ
          have c1' := c1.trans (add_le_add (hC₂₄ _ (by
            have := cmEll_pos hN; positivity)) le_rfl)
          have c2 : |avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (hsf u) ζ -
              avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ => Φ u ζ ω) ζ| ≤
              |C₂₃| * (N : ℝ) ^ (|C₁₃| * ε) * ((N : ℝ) * cmTau N / cmEll N) + e₃ u := by
            unfold avFlat
            have e : ramp (Kw * cmW N) (k₀ : ℕ) ζ * hsf u ζ + (1 - ramp (Kw * cmW N) (k₀ : ℕ) ζ) -
                (ramp (Kw * cmW N) (k₀ : ℕ) ζ * Φ u ζ ω + (1 - ramp (Kw * cmW N) (k₀ : ℕ) ζ)) =
                ramp (Kw * cmW N) (k₀ : ℕ) ζ * (hsf u ζ - Φ u ζ ω) := by ring
            rw [e, abs_mul, abs_of_nonneg (ramp_nonneg _ _ _)]
            by_cases hd : (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N
            · have d1 := hL3' σ₀ hσ₀ k₀ hE₀ hsf hsf1 hsf2 u hu' ζ hζ hd
              have d2 := d1.trans (add_le_add (hC₂₃ _ (by
                have := cmEll_pos hN; unfold cmTau; positivity)) le_rfl)
              rw [abs_sub_comm] at d2
              have d3 := ramp_le_one (Kw * cmW N) (k₀ : ℕ) ζ
              have d4 := abs_nonneg (hsf u ζ - Φ u ζ ω)
              nlinarith [ramp_nonneg (Kw * cmW N) (k₀ : ℕ) ζ]
            · rw [ramp_eq_zero hwd (le_of_lt (not_le.1 hd)), zero_mul]
              have : 0 ≤ |C₂₃| * (N : ℝ) ^ (|C₁₃| * ε) * ((N : ℝ) * cmTau N / cmEll N) := by
                have := cmEll_pos hN; unfold cmTau; positivity
              linarith
          have c3 := abs_sub_le (gf k₀ u ζ) (avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (hsf u) ζ)
            (avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ => Φ u ζ ω) ζ)
          unfold stMain
          linarith
        · rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (by linarith)
      have hB : ∑ ζ ∈ (sector N r).filter
          (fun ζ => 2 * (Kw * cmW N) < (rampDist (k₀ : ℕ) ζ : ℝ)), hf k₀ u ζ ≤
          (N : ℝ) ^ r * e₆ u := by
        refine (Finset.sum_le_sum (g := fun _ => e₆ u) fun ζ hζ => ?_).trans ?_
        · obtain ⟨hζs, hζd⟩ := Finset.mem_filter.1 hζ
          exact hP6' σ₀ hσ₀ k₀ hE₀ (hf k₀) (hhf k₀).1 (hhf k₀).2 u hu' ζ hζs hζd
        · rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ h60
          exact (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans hcard
      have := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ stG C₁₄ C₂₄ ε N + 1)
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := Finset.card_le_univ K
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hTr' : cmT (r - 1) ≤ cmT r := by
    have : 0 ≤ (1 / 2 : ℝ) ^ (r + 1) := by positivity
    linarith
  have hsa : c₀ - cmTau N + cmT (r - 1) * cmTau N ≤ c₀ - cmTau N + cmT r * cmTau N := by nlinarith
  refine ⟨ρ, e₃, e₄, e₆, e', he₃, he₄, he₆, he', hρc, fun u hu => ⟨hρ0 u hu, hρb u hu⟩, ?_⟩
  intro σ hσ k₀ hE₀ ξ hξ hR
  have hσa : σ ∈ Icc (c₀ - cmTau N) c₀ := ⟨by nlinarith [hσ.1], hσ.2⟩
  have hk : k₀ ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, σ, hσa, hE₀⟩
  have hσs : σ ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ := ⟨hsa.trans hσ.1, hσ.2⟩
  have hd : (rampDist (k₀ : ℕ) ξ : ℝ) ≤ Kw * cmW N / 2 := by
    have h1 : InRank k₀ (|M| * cmW N) ξ :=
      inRank_mono hR (mul_le_mul_of_nonneg_right (le_abs_self M) hw.le)
    refine (rampDist_le_of_inRank (by positivity) h1).trans ?_
    rw [hKw]; nlinarith [abs_nonneg M]
  have h := hb k₀ hk σ hσs ξ hξ hd
  have hexp : stG C₁₄ C₂₄ ε N * Real.exp (-((r : ℝ) * v₀ / cmEta N ε) *
        (σ - (c₀ - cmTau N + cmT (r - 1) * cmTau N))) ≤
      stG C₁₄ C₂₄ ε N * Real.exp (-((r : ℝ) * v₀ / cmEta N ε) *
        ((1 / 2 : ℝ) ^ (r + 1) * cmTau N)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hG0
    have h1 : (1 / 2 : ℝ) ^ (r + 1) * cmTau N ≤ σ - (c₀ - cmTau N + cmT (r - 1) * cmTau N) := by
      rw [← hTr]
      have e : (cmT r - cmT (r - 1)) * cmTau N = cmT r * cmTau N - cmT (r - 1) * cmTau N := by
        ring
      linarith only [hσ.1, e]
    have h2 : 0 ≤ (r : ℝ) * v₀ / cmEta N ε := by positivity
    exact mul_le_mul_of_nonpos_left h1 (neg_nonpos.2 h2)
  rw [← hρdef] at h
  linarith only [h, hexp]

/-- **The induction step on one sample.** -/
theorem stepSample {r : ℕ} (hr : 1 ≤ r) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {q : Fin N → ℂ} {ω : FlowSample N} {Φ Ψ : ℝ → Occ N → FlowSample N → ℝ}
    {M Kw M' Kδ C₁₃ C₂₃ C₁₄ C₂₄ CR CA CL κ' C' KB p ε D' : ℝ}
    (hKw : Kw = 2 * (|M| + 1)) (hKδ : Kδ = |C₂₄| * (|M| + Kw) + 1)
    (hM' : |C₂₄| * (|M| + Kw) + 2 * Kw ≤ M')
    (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
    (hCR : 0 ≤ CR) (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hKB : 1 ≤ KB) (hD' : 0 ≤ D')
    (hN : 1 ≤ N) (hτs : cmTau N ≤ s₀)
    (hδ : Kδ * (cmW N / N) ≤ r₀ / 2) (hEA1 : stEA CR (slowConst c₀ r₀ s₀ v₀) v₀ Kδ ε N ≤ 1)
    (hE21 : stE2 CA ε N ≤ 1) (hβ1 : 1 ≤ stBeta r (v₀⁻¹ + 1) Kw N)
    (hcoef : maxPathCoef N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) v₀ (max v₀ v₀⁻¹)
      (stE2 CA ε N) (stL N) ≤ stKco r v₀ * N)
    (hGN : stG C₁₄ C₂₄ ε N ≤ (|C₂₄| + 1) * N)
    (hcoll : ∀ σ, c₀ - cmTau N ≤ σ → ∀ i j : Fin N, i ≠ j →
      flowEigenvalue F (c₀ - cmTau N) ω σ i ≠ flowEigenvalue F (c₀ - cmTau N) ω σ j)
    (hherm : ω.1.IsHermitian)
    (hΦs : IsMomentFlowSolution (flowRate F (c₀ - cmTau N) ω) r (c₀ - cmTau N) c₀
      (fun σ ξ => Φ σ ξ ω))
    (hΦ0 : ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ξ ∈ sector N r, 0 ≤ Φ u ξ ω)
    (hΨ0 : ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ξ ∈ sector N (r - 1), 0 ≤ Ψ u ξ ω)
    (hqB : max 1 ((N : ℝ) * nsq q) ≤ stB1 KB p N)
    (hR2 : ∀ k : ℕ, k ≤ stL N → ∀ ξ ∈ sector N r, ∀ i : Fin N, 0 < ξ i →
      ∀ s ∈ Icc (c₀ - cmTau N) c₀,
      |flowEigenvalue F (c₀ - cmTau N) ω s i - E| < Kδ * (cmW N / N) →
      |∑ j, remKernel F (c₀ - cmTau N) ω s i j (2 ^ k * cmEta N ε) * remCoef ξ i j *
          zeroExt r Φ s (remTarget ξ i j) ω -
        (freshDyson F s ⟨flowEigenvalue F (c₀ - cmTau N) ω s i, 2 ^ k * cmEta N ε⟩).im *
          zeroExt (r - 1) Ψ s (remove ξ i) ω| ≤
        (CR * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * (2 ^ k * cmEta N ε)) +
            v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ *
              (Kδ * (cmW N / N) + 2 ^ k * cmEta N ε + (c₀ - s))) *
          zeroExt (r - 1) Ψ s (remove ξ i) ω +
        max 1 ((N : ℝ) * nsq q) ^ r *
          ((N : ℝ) * ((N : ℝ)⁻¹ * (2 ^ k * cmEta N ε)⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) *
          (N : ℝ) ^ (-(D' + (((r : ℝ) + 1) * (p + 1) + 1))))
    (hAvg : ∀ σ ∈ Icc (c₀ - cmTau N) c₀, ∀ x : ℝ, |x - E| ≤ r₀ / 2 →
      ∀ h : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h → h ≤ 1 →
      |(N : ℝ)⁻¹ * ∑ k, h / ((flowEigenvalue F (c₀ - cmTau N) ω σ k - x) ^ 2 + h ^ 2) -
        (freshDyson F σ ⟨x, h⟩).im| ≤ CA * (N : ℝ) ^ ε / ((N : ℝ) * h))
    (hLong : ∀ s ∈ Icc (c₀ - cmTau N) c₀, ∀ i : Fin N,
      longCoupling F (c₀ - cmTau N) ω (cmEll N) s i ≤ CL * N / cmEll N)
    (hIH : ∃ e : ℝ → ℝ, ContErr e (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ k₀ - E| ≤ M' * cmW N / N →
        ∀ ξ ∈ sector N (r - 1), InRank k₀ (M' * cmW N) ξ →
          |Ψ σ ξ ω - 1| ≤ C' * (N : ℝ) ^ (-κ') + e σ)
    (hP6 : ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
        ∀ h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
          (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ =
            if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N then 1 else 0) →
          ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
            2 * (Kw * cmW N) < (rampDist (k₀ : ℕ) ζ : ℝ) → h u ζ ≤ e u)
    (hL3 : ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
        ∀ h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
          (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ = Φ (c₀ - cmTau N) ζ ω) →
          ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
            (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
            |Φ u ζ ω - h u ζ| ≤
              C₂₃ * (N : ℝ) ^ (C₁₃ * ε) * ((N : ℝ) * cmTau N / cmEll N) + e u)
    (hL4 : ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) ∧
      ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
        (∀ ζ ∈ sector N r, (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
          0 ≤ Φ (c₀ - cmTau N) ζ ω ∧
            Φ (c₀ - cmTau N) ζ ω ≤ C₂₄ * (N : ℝ) ^ (C₁₄ * ε)) ∧
        (∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ j : Fin N,
          (labelDist j k₀ : ℝ) ≤ 4 * (Kw * cmW N) →
          |flowEigenvalue F (c₀ - cmTau N) ω u j - E| ≤ C₂₄ * (M + Kw) * cmW N / N) ∧
        ∀ g h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r g →
          ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
          (∀ ζ ∈ sector N r, g (c₀ - cmTau N) ζ =
            avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ' => Φ (c₀ - cmTau N) ζ' ω) ζ) →
          (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ = Φ (c₀ - cmTau N) ζ ω) →
          ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
            |g u ζ - avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (h u) ζ| ≤
              C₂₄ * (N : ℝ) ^ (C₁₄ * ε) * ((cmEll N : ℝ) / cmW N) + e u) :
    ∃ e : ℝ → ℝ, ContErr e (c₀ - cmTau N + cmT r * cmTau N) c₀
        ((1 + stKco r v₀ * N) *
          ((1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) * (N : ℝ) ^ (-D'))) ∧
      ∀ σ ∈ Icc (c₀ - cmTau N + cmT r * cmTau N) c₀, ∀ k₀ : Fin N,
        |flowEigenvalue F (c₀ - cmTau N) ω σ k₀ - E| ≤ M * cmW N / N →
        ∀ ξ ∈ sector N r, InRank k₀ (M * cmW N) ξ →
          |Φ σ ξ ω - 1| ≤ (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N + stG C₁₄ C₂₄ ε N *
            Real.exp (-((r : ℝ) * v₀ / cmEta N ε) * ((1 / 2 : ℝ) ^ (r + 1) * cmTau N)) +
            maxPathErr N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) (stG C₁₄ C₂₄ ε N)
              (max v₀ v₀⁻¹) (stE2 CA ε N) (stE3 CL ε N) (stE4 C' κ' N)
              (stEA CR (slowConst c₀ r₀ s₀ v₀) v₀ Kδ ε N * (1 + stE4 C' κ' N) +
                stEB r KB p v₀ ε N)
              (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) (stL N) / ((r : ℝ) * v₀ / cmEta N ε)) + e σ := by

  obtain ⟨ρ, e₃, e₄, e₆, e', he₃, he₄, he₆, he', hρc, hρb', hfin⟩ := stepSample_core hr hK hC
    hKw hKδ hM' hε hε5 hCR hCA hCL hKB hD' hN hτs hδ hEA1 hE21 hβ1 hcoll hherm hΦs hΦ0 hΨ0 hqB
    hR2 hAvg hLong hIH hP6 hL3 hL4
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hv₀ : 0 < v₀ := hK.2.2.2.2.2
  have hτ : 0 < cmTau N := cmTau_pos (by omega)
  have hac : c₀ - cmTau N ≤ c₀ := by linarith
  have hT0 : 0 ≤ cmT (r - 1) := by
    unfold cmT
    have : ((1 : ℝ) / 2) ^ (r - 1 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hT1 := cmT_le_one (r - 1)
  have hTr : cmT r - cmT (r - 1) = (1 / 2 : ℝ) ^ (r + 1) := by
    unfold cmT
    rw [Nat.sub_add_cancel hr, pow_succ]; ring
  have hTr1 := cmT_le_one r
  have has : c₀ - cmTau N ≤ c₀ - cmTau N + cmT (r - 1) * cmTau N := by
    have := mul_nonneg hT0 hτ.le; linarith only [this]
  have hsb : c₀ - cmTau N + cmT (r - 1) * cmTau N ≤ c₀ := by
    have := mul_le_of_le_one_left hτ.le hT1; linarith only [this]
  have hsub : Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ ⊆ Icc (c₀ - cmTau N) c₀ :=
    Icc_subset_Icc has le_rfl
  have hG0 : 0 ≤ stG C₁₄ C₂₄ ε N := by
    unfold stG; have : 0 ≤ |C₂₄| * (N : ℝ) ^ (|C₁₄| * ε) := by positivity
    linarith only [this]
  have hρ0 : ∀ u ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, 0 ≤ ρ u :=
    fun u hu => (hρb' u hu).1
  obtain ⟨bnd, hbnd⟩ : ∃ bnd : ℝ → ℝ, bnd = fun u => e' u + (N : ℝ) * ((N : ℝ) ^ r *
      (e₃ u + e₄ u) + (stG C₁₄ C₂₄ ε N + 1) * ((N : ℝ) ^ r * e₆ u)) := ⟨_, rfl⟩
  have hρb : ∀ u ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀, ρ u ≤ bnd u := by
    intro u hu; rw [hbnd]; exact (hρb' u hu).2
  -- integrals
  have hsc' : c₀ - cmTau N + cmT (r - 1) * cmTau N ≤ c₀ := hsb
  have hI : ∀ {e : ℝ → ℝ}, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D')) →
      IntervalIntegrable e volume (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ ∧
      (∫ u in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..c₀, e u) ≤ (N : ℝ) ^ (-D') := by
    intro e he
    have i1 : IntervalIntegrable e volume (c₀ - cmTau N) (c₀ - cmTau N + cmT (r - 1) * cmTau N) :=
      he.2.1.mono_set (by rw [uIcc_of_le has, uIcc_of_le hac]; exact Icc_subset_Icc le_rfl hsb)
    have i2 : IntervalIntegrable e volume (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ :=
      he.2.1.mono_set (by rw [uIcc_of_le hsb, uIcc_of_le hac]; exact Icc_subset_Icc has le_rfl)
    refine ⟨i2, ?_⟩
    have h := intervalIntegral.integral_add_adjacent_intervals i1 i2
    have h0 : 0 ≤ ∫ u in (c₀ - cmTau N)..(c₀ - cmTau N + cmT (r - 1) * cmTau N), e u :=
      intervalIntegral.integral_nonneg has fun u hu => he.1 u ⟨hu.1, hu.2.trans hsb⟩
    linarith [he.2.2.1]
  obtain ⟨i3, j3⟩ := hI he₃
  obtain ⟨i4, j4⟩ := hI he₄
  obtain ⟨i6, j6⟩ := hI he₆
  have i' : IntervalIntegrable e' volume (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ :=
    he'.1.intervalIntegrable_of_Icc hsb
  have hbi : IntervalIntegrable bnd volume (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ := by
    rw [hbnd]
    exact i'.add (((i3.add i4).const_mul _).add ((i6.const_mul _).const_mul _) |>.const_mul _)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) * (N : ℝ) ^ (-D') :=
    ⟨_, rfl⟩
  have hGN' : stG C₁₄ C₂₄ ε N + 1 ≤ (|C₂₄| + 1) * N + 1 := by linarith
  have hpowr : (N : ℝ) * (N : ℝ) ^ r = (N : ℝ) ^ (r + 1) := by ring
  have hD0 : 0 ≤ (N : ℝ) ^ (-D') := by positivity
  have hbX : (∫ u in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..c₀, bnd u) ≤ X := by
    simp only [hbnd]
    rw [intervalIntegral.integral_add i' (((i3.add i4).const_mul _).add
        ((i6.const_mul _).const_mul _) |>.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((i3.add i4).const_mul _) ((i6.const_mul _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add i3 i4]
    have j' := he'.2.2.1
    have k1 : (N : ℝ) ^ r * ((∫ u in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..c₀, e₃ u) +
        ∫ u in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..c₀, e₄ u) ≤
        (N : ℝ) ^ r * (2 * (N : ℝ) ^ (-D')) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have k2 : (stG C₁₄ C₂₄ ε N + 1) * ((N : ℝ) ^ r *
        ∫ u in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..c₀, e₆ u) ≤
        ((|C₂₄| + 1) * N + 1) * ((N : ℝ) ^ r * (N : ℝ) ^ (-D')) :=
      mul_le_mul hGN' (mul_le_mul_of_nonneg_left j6 (by positivity)) (by
        have := intervalIntegral.integral_nonneg (μ := volume) hsb fun u hu => he₆.1 u (hsub hu)
        positivity) (by positivity)
    have k3 := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hNp.le
    have e : (N : ℝ) ^ (-D') + (N : ℝ) * ((N : ℝ) ^ r * (2 * (N : ℝ) ^ (-D')) +
        ((|C₂₄| + 1) * N + 1) * ((N : ℝ) ^ r * (N : ℝ) ^ (-D'))) = X := by
      rw [hX, ← hpowr]; ring
    linarith
  have hbc : bnd c₀ ≤ X := by
    simp only [hbnd]
    have j' := he'.2.2.2
    have a3 := he₃.2.2.2
    have a4 := he₄.2.2.2
    have a6 := he₆.2.2.2
    have h60 := he₆.1 c₀ ⟨hac, le_rfl⟩
    have k1 : (N : ℝ) ^ r * (e₃ c₀ + e₄ c₀) ≤ (N : ℝ) ^ r * (2 * (N : ℝ) ^ (-D')) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have k2 : (stG C₁₄ C₂₄ ε N + 1) * ((N : ℝ) ^ r * e₆ c₀) ≤
        ((|C₂₄| + 1) * N + 1) * ((N : ℝ) ^ r * (N : ℝ) ^ (-D')) :=
      mul_le_mul hGN' (mul_le_mul_of_nonneg_left a6 (by positivity)) (by positivity)
        (by positivity)
    have k3 := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hNp.le
    have e : (N : ℝ) ^ (-D') + (N : ℝ) * ((N : ℝ) ^ r * (2 * (N : ℝ) ^ (-D')) +
        ((|C₂₄| + 1) * N + 1) * ((N : ℝ) ^ r * (N : ℝ) ^ (-D'))) = X := by
      rw [hX, ← hpowr]; ring
    linarith
  have hTrr : cmT (r - 1) ≤ cmT r := by
    have : 0 ≤ (1 / 2 : ℝ) ^ (r + 1) := by positivity
    linarith
  have hsa : c₀ - cmTau N + cmT (r - 1) * cmTau N ≤ c₀ - cmTau N + cmT r * cmTau N := by
    have := mul_le_mul_of_nonneg_right hTrr hτ.le; linarith only [this]
  have hac' : c₀ - cmTau N + cmT r * cmTau N ≤ c₀ := by
    have := mul_le_of_le_one_left hτ.le hTr1; linarith only [this]
  have hca' : c₀ - (c₀ - cmTau N + cmT r * cmTau N) ≤ 1 := by
    have h1 : cmTau N ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
    have h2 : 0 ≤ cmT r := by
      unfold cmT
      have : (1 / 2 : ℝ) ^ (r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have := mul_nonneg h2 hτ.le
    linarith only [h1, this]
  have hKco := stKco_nonneg r hv₀
  have hKN : 0 ≤ stKco r v₀ * N := mul_nonneg hKco hNp.le
  have hbX' : (∫ u in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..c₀, bnd u) ≤
      (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) * (N : ℝ) ^ (-D') := by
    rw [← hX]; exact hbX
  have hbc' : bnd c₀ ≤ (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) * (N : ℝ) ^ (-D') := by
    rw [← hX]; exact hbc
  refine ⟨_, contErr_of_rho hsa hac' hca' hKN hρc hρ0 hρb hbi hbX' hbc', ?_⟩
  intro σ hσ k₀ hE₀ ξ hξ hR
  have h := hfin σ hσ k₀ hE₀ ξ hξ hR
  have hσs : σ ∈ Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ := ⟨hsa.trans hσ.1, hσ.2⟩
  have hint : (∫ t in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..σ,
        maxPathCoef N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) v₀ (max v₀ v₀⁻¹) (stE2 CA ε N)
          (stL N) * ρ t) ≤
      ∫ t in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..σ, stKco r v₀ * N * ρ t := by
    have hsub' : Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) σ ⊆
        Icc (c₀ - cmTau N + cmT (r - 1) * cmTau N) c₀ := Icc_subset_Icc le_rfl hσ.2
    refine intervalIntegral.integral_mono_on hσs.1
      ((continuousOn_const.mul (hρc.mono hsub')).intervalIntegrable_of_Icc hσs.1)
      ((continuousOn_const.mul (hρc.mono hsub')).intervalIntegrable_of_Icc hσs.1)
      fun t ht => mul_le_mul_of_nonneg_right hcoef (hρ0 t (hsub' ht))
  show |Φ σ ξ ω - 1| ≤ _ + (ρ σ + ∫ t in (c₀ - cmTau N + cmT (r - 1) * cmTau N)..σ,
    stKco r v₀ * N * ρ t)
  linarith only [h, hint]

end BlockBand.Palm.MomentFlow
