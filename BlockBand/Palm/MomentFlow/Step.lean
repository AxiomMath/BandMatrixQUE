module

public import BlockBand.Palm.MomentFlow.StepSample
public import BlockBand.Palm.MomentFlow.PropLong
public import BlockBand.Palm.MomentFlow.IndInduct

/-!
# The conditional-moments lemma: the induction step and the lemma

* `prob_union7`, `nsq_bound` (`max(1, N‖q‖²) ≤ K_B N^{1+2max(A,1)}` from `q*Γq = 1`),
  `rpow_tail`, `ContErr.mono_bound`.
* **`cmWin_step`**: `∀ r ≥ 1, (∀ M, CMWin (r-1) M) → ∀ M, CMWin r M`, with
  `κ_r = min(κ_{r-1}, 1/1000)` (`κ_{r-1}` of `CM(r-1)` at the window multiple
  `M' = |C₂⁴|(|M| + K_w) + 2K_w`, `K_w = 2(|M|+1)`), `ε = 1/(10⁵(|C₁³| + |C₁⁴| + 1))`, and
  `D' = max(D, 0) + r + 4` for all components.
* **`conditionalMoments_of`**: `FreshPalmAssembly.ConditionalMomentsStatement` from the same
  hypotheses (via `conditionalMoments_of_step`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.Inputs
open BlockBand.Palm.CoarseRelative BlockBand.Palm
open scoped ENNReal

variable {N : ℕ}

theorem prob_union7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {B₁ B₂ B₃ B₄ B₅ B₆ B₇ : Set Ω} {x y : ℝ}
    (h₁ : μ B₁ ≤ ENNReal.ofReal x) (h₂ : μ B₂ ≤ ENNReal.ofReal x) (h₃ : μ B₃ ≤ ENNReal.ofReal x)
    (h₄ : μ B₄ ≤ ENNReal.ofReal x) (h₅ : μ B₅ ≤ ENNReal.ofReal x) (h₆ : μ B₆ ≤ ENNReal.ofReal x)
    (h₇ : μ B₇ ≤ ENNReal.ofReal x) (hxy : 7 * x ≤ y) :
    μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇) ≤ ENNReal.ofReal y := by
  have h : μ (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇) ≤ 7 * ENNReal.ofReal x := by
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)) h₅)) h₆)) h₇).trans
      (le_of_eq ?_)
    ring
  refine h.trans ?_
  rw [show (7 : ℝ≥0∞) = ENNReal.ofReal 7 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hxy

theorem nsq_bound {F : Matrix (Fin N) (Fin N) ℂ} (hN : 1 ≤ N) {A c₀ E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀) {q : Fin N → ℂ}
    (hq : quadForm (freshGamma F c₀ E) q = 1) :
    max 1 ((N : ℝ) * nsq q) ≤
      stB1 (1 / (v₀ * lowConst c₀ s₀ v₀) + 1) (1 + 2 * max A 1) N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := FreshPalmAssembly.lowConst_pos hK
  have h := freshGamma_quad_lower (by omega) hK hC q
  rw [hq] at h
  have hm : 0 < (N : ℝ) ^ (-(2 * max A 1)) := Real.rpow_pos_of_pos hNp _
  have h1 : nsq q ≤ (N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c₀ s₀ v₀) := by
    rw [le_div_iff₀ (by linarith [hl]), Real.rpow_neg hNp.le] at *
    have : v₀ * lowConst c₀ s₀ v₀ * ((N : ℝ) ^ (2 * max A 1))⁻¹ * nsq q * (N : ℝ) ^ (2 * max A 1)
        ≤ (N : ℝ) ^ (2 * max A 1) :=
      by nlinarith [Real.rpow_pos_of_pos hNp (2 * max A 1)]
    have e : v₀ * lowConst c₀ s₀ v₀ * ((N : ℝ) ^ (2 * max A 1))⁻¹ * nsq q *
        (N : ℝ) ^ (2 * max A 1) = nsq q * (v₀ * lowConst c₀ s₀ v₀) := by
      field_simp
    linarith
  have hP : (N : ℝ) ^ (1 + 2 * max A 1) = N * (N : ℝ) ^ (2 * max A 1) := by
    rw [Real.rpow_add hNp, Real.rpow_one]
  have hP1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 + 2 * max A 1) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  unfold stB1
  refine max_le ?_ ?_
  · have : 0 ≤ 1 / (v₀ * lowConst c₀ s₀ v₀) := by positivity
    nlinarith
  · have h2 : (N : ℝ) * nsq q ≤ (N : ℝ) * ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c₀ s₀ v₀)) :=
      mul_le_mul_of_nonneg_left h1 hNp.le
    have e : (N : ℝ) * ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c₀ s₀ v₀)) =
        1 / (v₀ * lowConst c₀ s₀ v₀) * (N : ℝ) ^ (1 + 2 * max A 1) := by
      rw [hP]; field_simp
    nlinarith

theorem rpow_tail {N : ℕ} (hN : 1 ≤ N) {X D : ℝ} (r : ℕ) (hX : X ≤ (N : ℝ) ^ (r + 4)) :
    X * (N : ℝ) ^ (-(max D 0 + ((r : ℝ) + 4))) ≤ (N : ℝ) ^ (-D) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ (N : ℝ) ^ (-(max D 0 + ((r : ℝ) + 4))) := by positivity
  refine (mul_le_mul_of_nonneg_right hX h0).trans ?_
  rw [show (N : ℝ) ^ (r + 4) = (N : ℝ) ^ (((r + 4 : ℕ) : ℝ)) from (Real.rpow_natCast _ _).symm,
    ← Real.rpow_add hNp]
  refine rpow_le_rpow_exp hN ?_
  push_cast
  have := le_max_left D 0
  linarith

theorem ContErr.mono_bound {e : ℝ → ℝ} {s c b b' : ℝ} (h : ContErr e s c b) (hb : b ≤ b') :
    ContErr e s c b' := ⟨h.1, h.2.1, h.2.2.1.trans hb, h.2.2.2.trans hb⟩

/-- **The induction step** `CM(r-1, ·) ⇒ CM(r, ·)`. -/
theorem cmWin_step (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hP6 : PropagationP6) (hL3 : LongShortPropagation) (hL4 : Flattening) :
    ∀ r : ℕ, 1 ≤ r → (∀ M : ℝ, CMWin (r - 1) M) → ∀ M : ℝ, CMWin r M := by
  intro r hr hIH M A c₀ r₀ s₀ v₀ hK
  have hc₀ : 0 < c₀ := hK.1
  have hr₀ : 0 < r₀ := hK.2.2.1
  have hs₀ : 0 < s₀ := hK.2.2.2.1
  have hv₀ : 0 < v₀ := hK.2.2.2.2.2
  have hs₀c : s₀ < c₀ / 2 := hK.2.2.2.2.1
  obtain ⟨Kw, hKw⟩ : ∃ Kw : ℝ, Kw = 2 * (|M| + 1) := ⟨_, rfl⟩
  have hKw0 : 0 < Kw := by rw [hKw]; positivity
  obtain ⟨C₁₃, C₂₃, hL3c⟩ := hL3 A c₀ r₀ s₀ v₀ hK r hr M Kw hKw0
  obtain ⟨C₁₄, C₂₄, hL4c⟩ := hL4 A c₀ r₀ s₀ v₀ hK r hr M Kw hKw0
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = |C₂₄| * (|M| + Kw) + 2 * Kw := ⟨_, rfl⟩
  obtain ⟨κ', C', hκ', hIHc⟩ := hIH M' A c₀ r₀ s₀ v₀ hK
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (100000 * (|C₁₃| + |C₁₄| + 1)) := ⟨_, rfl⟩
  have hden : 0 < 100000 * (|C₁₃| + |C₁₄| + 1) := by positivity
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεC : (|C₁₃| + |C₁₄| + 1) * ε = 1 / 100000 := by rw [hεdef]; field_simp
  have hε5 : ε ≤ 1 / 100000 := by
    have : 0 ≤ (|C₁₃| + |C₁₄|) * ε := by positivity
    nlinarith
  have h13 : |C₁₃| * ε ≤ 1 / 100000 := by
    have : 0 ≤ (|C₁₄| + 1) * ε := by positivity
    nlinarith
  have h14 : |C₁₄| * ε ≤ 1 / 100000 := by
    have : 0 ≤ (|C₁₃| + 1) * ε := by positivity
    nlinarith
  have hε4 : ε < 1 / 4 := by linarith
  have hε1000 : ε < 1 / 1000 := by linarith
  obtain ⟨CR, hCR, hR2c⟩ := removal_average_uniform hELG hMDE hLp hDBM (A := A) hK hε hε4
  obtain ⟨CA, hCA, hAvc⟩ := averaged_measurable hELG hMDE hLp (A := A) hK hε hε4
  obtain ⟨c₁L, CL, -, hCL, hLongc⟩ := longCoupling_good hLp hIBP (A := A) hK
  obtain ⟨Kδ, hKδ⟩ : ∃ Kδ : ℝ, Kδ = |C₂₄| * (|M| + Kw) + 1 := ⟨_, rfl⟩
  have hKδ0 : 0 ≤ Kδ := by rw [hKδ]; positivity
  obtain ⟨KB, hKBdef⟩ : ∃ KB : ℝ, KB = 1 / (v₀ * lowConst c₀ s₀ v₀) + 1 := ⟨_, rfl⟩
  have hKB : 1 ≤ KB := by
    rw [hKBdef]; have := FreshPalmAssembly.lowConst_pos hK
    have : 0 ≤ 1 / (v₀ * lowConst c₀ s₀ v₀) := by positivity
    linarith
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 1 + 2 * max A 1 := ⟨_, rfl⟩
  have hp : 0 ≤ p := by rw [hpdef]; have := le_max_right A 1; linarith
  have hasym := step_asym hr hv₀ (slowConst_nonneg hK) hr₀ hs₀ hc₀ hKw0 hKδ0 hCR hCA hCL.le hκ'
    hKB hp hε hε5 h13 h14 (C' := C') (CL := CL) (C₂₃ := C₂₃) (C₂₄ := C₂₄)
  refine ⟨min κ' (1 / 1000), stCfin r v₀ (slowConst c₀ r₀ s₀ v₀) Kw Kδ C₂₃ C₂₄ CR CA CL C' KB,
    lt_min hκ' (by norm_num), fun D => ?_⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ℝ, D' = max D 0 + ((r : ℝ) + 4) := ⟨_, rfl⟩
  have hD'0 : 0 ≤ D' := by rw [hD']; have := le_max_right D 0; positivity
  obtain ⟨N₁, hN₁⟩ := hR2c r (D' + (((r : ℝ) + 1) * (p + 1) + 1))
  obtain ⟨N₂, hN₂⟩ := hAvc D'
  obtain ⟨N₃, hN₃⟩ := hLongc D'
  obtain ⟨N₄, hN₄⟩ := hIHc D'
  obtain ⟨N₅, hN₅⟩ := hP6 A c₀ r₀ s₀ v₀ hK r hr M Kw hKw0 D'
  obtain ⟨N₆, hN₆⟩ := hL3c ε hε hε1000 D'
  obtain ⟨N₇, hN₇⟩ := hL4c ε hε hε1000 D'
  obtain ⟨N₈, hN₈⟩ := Filter.eventually_atTop.1 hasym
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ N₈)),
    fun N hNN F E hC q hq => ?_⟩
  have hle : ∀ {a b c d e f g h : ℕ}, max (max (max a b) (max c d)) (max (max e f) (max g h)) ≤ N →
      a ≤ N ∧ b ≤ N ∧ c ≤ N ∧ d ≤ N ∧ e ≤ N ∧ f ≤ N ∧ g ≤ N ∧ h ≤ N := by
    intro a b c d e f g h H
    simp only [max_le_iff] at H
    tauto
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hle hNN
  obtain ⟨hN, hτc, hτs, hδ, hEA1, hE21, hβ1, hmain, hcoef, hpoly⟩ := hN₈ N h₈
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ := cmTau_pos (N := N) (by omega)
  have ha : 0 < c₀ - cmTau N := by linarith
  have hac : c₀ - cmTau N < c₀ := by linarith
  have hs : c₀ - s₀ ≤ c₀ - cmTau N := by linarith
  have hca : c₀ - (c₀ - cmTau N) ≤ 1 := by
    have : cmTau N ≤ 1 := by linarith [hK.2.1]
    linarith
  obtain ⟨B₁, hB₁, hPB₁, hR2B⟩ := hN₁ N h₁ F E hC q hq (c₀ - cmTau N) c₀ ha hac le_rfl hs hca
  obtain ⟨B₂, hB₂, hPB₂, hAvB⟩ := hN₂ N h₂ F E hC (c₀ - cmTau N) c₀ ha.le hac hca hs le_rfl
  obtain ⟨B₃, hB₃, hPB₃, hLongB⟩ := hN₃ N h₃ F E hC
  obtain ⟨B₄, hB₄, hPB₄, hIHB⟩ := hN₄ N h₄ F E hC q hq
  obtain ⟨B₅, hB₅, hPB₅, hP6B⟩ := hN₅ N h₅ F E hC
  obtain ⟨B₆, hB₆, hPB₆, hL3B⟩ := hN₆ N h₆ F E hC q hq
  obtain ⟨B₇, hB₇, hPB₇, hL4B⟩ := hN₇ N h₇ F E hC q hq
  have hPB₁' : flowLaw N (c₀ - cmTau N) B₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
    hPB₁.trans (ENNReal.ofReal_le_ofReal (rpow_le_rpow_exp hN (by
      have : 0 ≤ ((r : ℝ) + 1) * (p + 1) + 1 := by positivity
      linarith)))
  refine ⟨B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ B₇,
    (((((hB₁.union hB₂).union hB₃).union hB₄).union hB₅).union hB₆).union hB₇,
    prob_union7 _ hPB₁' hPB₂ hPB₃ hPB₄ hPB₅ hPB₆ hPB₇ ?_, fun Φ hΦ => ?_⟩
  · have h7 : (7 : ℝ) ≤ (N : ℝ) ^ (r + 4) := by
      have : 0 ≤ (1 + stKco r v₀ * N) * (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) := by
        have := stKco_nonneg r hv₀; positivity
      linarith
    have := rpow_tail hN (D := D) r h7
    rw [hD']; linarith
  obtain ⟨Ψ, hΨ⟩ := regVersion_exists (hDBM N) hC.1 ha hac.le q (r - 1)
  have hzΦ := zeroExt_version hΦ
  have hzΨ := zeroExt_version hΨ
  have hR2' := hR2B (zeroExt r Φ) (zeroExt (r - 1) Ψ) hzΦ.1 hzΨ.1
    (by filter_upwards [hzΦ.2, hzΨ.2] with ω h1 h2 ζ; exact ⟨h1 ζ, h2 ζ⟩)
  have hη := cmEta_pos hN ε
  have hηge := asym_eta_ge hN hε hε5
  have h2L1 : (2 : ℝ) ^ stL N * cmEta N ε ≤ 1 := (asym_two_pow_eta hN hε hε5).trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num))
  have hδ0 : 0 ≤ Kδ * (cmW N / N) := by have := cmW_pos hN; positivity
  have hR2pt : ∀ k : ℕ, ∀ ξ : Occ N, ∀ i : Fin N, ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N),
      ω ∉ B₁ → k ≤ stL N → ξ ∈ sector N r → 0 < ξ i →
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
          (N : ℝ) ^ (-(D' + (((r : ℝ) + 1) * (p + 1) + 1))) := by
    intro k ξ i
    by_cases hk : k ≤ stL N
    · by_cases hξ : ξ ∈ sector N r
      · by_cases hi : 0 < ξ i
        · have hk1 : 2 ^ k * cmEta N ε ≤ 1 :=
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hη.le).trans h2L1
          have hk0 : (N : ℝ) ^ (-(1 - 4 * ε)) ≤ 2 ^ k * cmEta N ε :=
            hηge.trans (le_mul_of_one_le_left hη.le (one_le_pow₀ (by norm_num)))
          filter_upwards [hR2' (2 ^ k * cmEta N ε) hk0 hk1 (Kδ * (cmW N / N)) hδ0 hδ ξ hξ i hi]
            with ω hω hωB _ _ _
          exact hω hωB
        · exact Eventually.of_forall fun ω _ _ _ h => absurd h hi
      · exact Eventually.of_forall fun ω _ _ h => absurd h hξ
    · exact Eventually.of_forall fun ω _ h => absurd h hk
  have hR2ae := ae_all_iff.2 fun k => ae_all_iff.2 fun ξ => ae_all_iff.2 fun i => hR2pt k ξ i
  have hIHae := hIHB Ψ hΨ
  have hL3ae := hL3B Φ hΦ
  have hL4ae := hL4B Φ hΦ
  have hcollae := ae_noCollision (hDBM N) hC.1 ha
  have hΦ0ae := regVersion_nonneg hac.le hΦ
  have hΨ0ae := regVersion_nonneg hac.le hΨ
  have hqB : max 1 ((N : ℝ) * nsq q) ≤ stB1 KB p N := by
    rw [hKBdef, hpdef]; exact nsq_bound hN hK hC hq
  have hGN := asym_G_le_N (C₂ := C₂₄) hN hε hε5 h14
  filter_upwards [hR2ae, hIHae, hP6B, hL3ae, hL4ae, hcollae, hΦ0ae, hΨ0ae, hΦ.2] with ω hR2ω
    hIHω hP6ω hL3ω hL4ω hcollω hΦ0ω hΨ0ω hΦsω hωB
  simp only [Set.mem_union, not_or] at hωB
  obtain ⟨⟨⟨⟨⟨⟨g₁, g₂⟩, g₃⟩, g₄⟩, g₅⟩, g₆⟩, g₇⟩ := hωB
  obtain ⟨e, he, hb⟩ := stepSample hr hK hC (q := q) (Φ := Φ) (Ψ := Ψ) hKw hKδ
    (le_of_eq hM'.symm) hε hε5 hCR hCA hCL.le hKB hD'0 hN hτs hδ hEA1 hE21 hβ1 hcoef hGN
    hcollω.2 hcollω.1 hΦsω hΦ0ω hΨ0ω hqB
    (fun k hk ξ hξ i hi => hR2ω k ξ i g₁ hk hξ hi) (hAvB ω g₂)
    (fun s hs i => (hLongB ω g₃ s hs).2 i) (hIHω g₄) (hP6ω g₅) (hL3ω g₆) (hL4ω g₇)
  refine ⟨e, he.mono_bound ?_, fun σ hσ k₀ hE₀ ξ hξ hR =>
    (hb σ hσ k₀ hE₀ ξ hξ hR).trans (add_le_add hmain le_rfl)⟩
  have hX : (1 + stKco r v₀ * N) * (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) ≤
      (N : ℝ) ^ (r + 4) := by linarith
  have := rpow_tail hN (D := D) r hX
  rw [hD']
  calc (1 + stKco r v₀ * N) * ((1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) *
        (N : ℝ) ^ (-(max D 0 + ((r : ℝ) + 4))))
      = (1 + stKco r v₀ * N) * (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) *
        (N : ℝ) ^ (-(max D 0 + ((r : ℝ) + 4))) := by ring
    _ ≤ _ := this

/-- **The conditional-moments lemma**, from the propositions `PropagationP6`, `LongShortPropagation`,
`Flattening` and the inputs taken as hypotheses. -/
theorem conditionalMoments_of (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    (hP6 : PropagationP6) (hL3 : LongShortPropagation) (hL4 : Flattening) :
    BlockBand.Palm.FreshPalmAssembly.ConditionalMomentsStatement :=
  conditionalMoments_of_step hDBM (cmWin_step hELG hMDE hLp hIBP hDBM hP6 hL3 hL4)

end BlockBand.Palm.MomentFlow
