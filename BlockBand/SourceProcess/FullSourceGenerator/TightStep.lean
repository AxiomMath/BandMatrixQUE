module

public import BlockBand.SourceProcess.FullSourceGenerator.TightCond
public import BlockBand.SourceProcess.FullSourceGenerator.Calculus
public import BlockBand.SourceProcess.FullSourceGenerator.LoadBound
public import BlockBand.SourceProcess.FullSourceGenerator.PastMeas
public import BlockBand.SourceProcess.FullSource.PathSetup

/-!
# One step of `tight` along the path

* `stronglyMeasurable_stepInc`: `d_i` is `growthSigma W (i+1)`-measurable;
* `integrable_realVal_pow4`: `X_j⁴` is integrable given a moment of the load `wordLoad`
  (`FullSourceStops.lintegral_wordLoad_pow_le`);
* `ae_abs_condExp_stepInc_le` (drift) and `condExp_stepInc_sq_le` (variance), after the last
  injection (`t₀ < (i+1)/W`): `|E_i d_i| ≤ C_𝒜/W + ‖driftErr Φ i‖`,
  `E_i d_i² ≤ C_Γ/W + ‖carreErr Φ i‖` a.e., where `driftErr`, `carreErr` are the integrands of
  `EarlySummed`;
* `integral_stepInc_pow4_le`: `E d_i⁴ ≤ Σ_{r≤4} C(4,r) C_X^{4-r} E‖driftErr (Φ^r) i‖`
  (`fourth_cancel`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W nT nI : ℕ}

/-- `X_j = Re Φ(Z_j)`. -/
def realVal (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ) (Φ : TracePoly nT nI) :
    GrowthPath W → ℝ := fun ω => (polyValue b E k q W j ω Φ).re

/-- The stopped increment `1{i<σ_K}(X_{i+1} - X_i)`. -/
def stepInc (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W : ℕ)
    (Φ : TracePoly nT nI) (i : ℕ) : GrowthPath W → ℝ :=
  (alive b E k q K ε W i).indicator fun ω =>
    realVal b E k q W (i + 1) Φ ω - realVal b E k q W i Φ ω

/-- The integrand of the first clause of `EarlySummed`. -/
def driftErr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W : ℕ)
    (Φ : TracePoly nT nI) (j : ℕ) : GrowthPath W → ℂ :=
  (alive b E k q K ε W j).indicator fun ω =>
    (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
      polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) | growthSigma W j] ω -
    (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)

/-- The integrand of the second clause of `EarlySummed`. -/
def carreErr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W : ℕ)
    (Φ : TracePoly nT nI) (j : ℕ) : GrowthPath W → ℂ :=
  (alive b E k q K ε W j).indicator fun ω =>
    (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
      (polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) ^ 2) | growthSigma W j] ω -
    (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)

/-- Real values along the path. -/
def IsRealPoly (b E : ℝ) (q : Fin nI → ℝ → ℝ) (Φ : TracePoly nT nI) : Prop :=
  ∀ (W : ℕ) (k : Fin nT → ℕ) (j : ℕ) (ω : GrowthPath W),
    (((polyValue b E k q W j ω Φ).re : ℝ) : ℂ) = polyValue b E k q W j ω Φ

theorem isOrdinaryPoly_pow {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) (r : ℕ) :
    IsOrdinaryPoly (Φ ^ r) := fun w hw => hΦ w (vars_pow Φ r hw)

theorem isRealPoly_pow {b E : ℝ} {q : Fin nI → ℝ → ℝ} {Φ : TracePoly nT nI}
    (hR : IsRealPoly b E q Φ) (r : ℕ) : IsRealPoly b E q (Φ ^ r) := fun W k j ω => by
  have h := hR W k j ω
  simp only [polyValue, map_pow] at h ⊢
  rw [← h, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem wordGenerator_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) (b E : ℝ)
    (q : Fin nI → ℝ → ℝ) (t : ℝ) : wordGenerator b E q t Φ ∈ ordPoly nT nI := by
  rw [wordGenerator_eq]
  exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (C_mem_ordPoly _) (genCore_mem hΦ))
    (Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ (C_mem_ordPoly _)
      (pderiv_mem_supported (mem_ordPoly_of_isOrdinaryPoly hΦ) w))

theorem wordCarre_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) (b E : ℝ) :
    wordCarre b E Φ ∈ ordPoly nT nI := by
  rw [wordCarre_eq]; exact Subalgebra.mul_mem _ (C_mem_ordPoly _) (carreCore_mem hΦ)

/-- After the last injection the generator does not depend on time. -/
theorem wordGenerator_congr_time (b E : ℝ) (q : Fin nI → ℝ → ℝ) {t t' : ℝ}
    (h : ∀ a, q a t = q a t') (Φ : TracePoly nT nI) :
    wordGenerator b E q t Φ = wordGenerator b E q t' Φ := by
  have hI : (wordInjection b q t : TraceWord nT nI → ℂ) = wordInjection b q t' := by
    funext w
    rcases w with _ | ⟨⟨ℓ, s⟩, _ | ⟨y, tl⟩⟩
    · rfl
    · cases ℓ <;> simp [wordInjection, h]
    · cases ℓ <;> rfl
  unfold wordGenerator; rw [hI]

theorem growthSigma_le' (W r : ℕ) :
    growthSigma W r ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
  Measurable.comap_le (by fun_prop)

section Step

variable (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (Φ : TracePoly nT nI)

theorem measurable_realVal_past {i j : ℕ} (h : i ≤ j) :
    Measurable[growthSigma W j] (realVal b E k q W i Φ) :=
  Complex.measurable_re.comp (measurable_polyValue_past b E k q h Φ)

theorem stronglyMeasurable_stepInc (i : ℕ) :
    StronglyMeasurable[growthSigma W (i + 1)] (stepInc b E k q K ε W Φ i) := by
  refine (Measurable.stronglyMeasurable ?_)
  refine Measurable.indicator ((measurable_realVal_past b E k q Φ le_rfl).sub
    (measurable_realVal_past b E k q Φ (Nat.le_succ i))) ?_
  exact FullSource.growthSigma_mono (Nat.le_succ i) _
    (ContractingWords.measurableSet_alive b E k q K ε i)

theorem stepInc_eq_zero {i : ℕ} {ω : GrowthPath W} (h : ω ∉ alive b E k q K ε W i) :
    stepInc b E k q K ε W Φ i ω = 0 := Set.indicator_of_notMem h _

/-- `X_j⁴` is integrable given a moment of the load. -/
theorem integrable_realVal_pow4 (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W)
    (hq : IsIntervalTests q) (hΦ : IsOrdinaryPoly Φ) (j : ℕ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hL : ∫⁻ ω, ENNReal.ofReal (wordLoad b E k q W j ω) ^ (4 * polyExp Φ + 1)
      ∂growthPathLaw W b ≤ C) :
    Integrable (fun ω => realVal b E k q W j Φ ω ^ 4) (growthPathLaw W b) := by
  have hm : AEStronglyMeasurable (fun ω => realVal b E k q W j Φ ω ^ 4) (growthPathLaw W b) :=
    ((measurable_realVal_past b E k q Φ le_rfl).mono (growthSigma_le' W j) le_rfl).pow_const
      4 |>.aestronglyMeasurable
  refine ⟨hm, ?_⟩
  set c := polyConst Φ ^ 4
  have hpt : ∀ᵐ ω ∂growthPathLaw W b, ‖realVal b E k q W j Φ ω ^ 4‖ₑ ≤
      ENNReal.ofReal c * ENNReal.ofReal (wordLoad b E k q W j ω) ^ (4 * polyExp Φ + 1) := by
    filter_upwards [ae_norm_polyValue_ord_le (nT := nT) hb hE1 hE2 hW q hq,
      one_le_wordLoad_ae (nT := nT) hb hE1 hE2 hW q hq] with ω h1 h2
    have hL1 := h2 j k
    have hX : |realVal b E k q W j Φ ω| ≤ polyConst Φ * wordLoad b E k q W j ω ^ polyExp Φ :=
      (Complex.abs_re_le_norm _).trans (h1 j k Φ (mem_ordPoly_of_isOrdinaryPoly hΦ))
    have h4 : realVal b E k q W j Φ ω ^ 4 ≤ c * wordLoad b E k q W j ω ^ (4 * polyExp Φ + 1) := by
      have := pow_le_pow_left₀ (abs_nonneg _) hX 4
      rw [Even.pow_abs (by decide), mul_pow, ← pow_mul] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [mul_comm]; exact pow_le_pow_right₀ hL1 (Nat.le_succ _)
    rw [Real.enorm_eq_ofReal (Even.pow_nonneg (by decide) _), ← ENNReal.ofReal_pow
      (by linarith), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h4
  refine (lintegral_mono_ae hpt).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hL.trans_lt hC.lt_top)

variable {b E}

/-- The complex increment is the real one. -/
theorem indicator_polyValue_sub (hR : IsRealPoly b E q Φ) (i : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (alive b E k q K ε W i).indicator (fun ω =>
      (polyValue b E k q W (i + 1) ω Φ - polyValue b E k q W i ω Φ) ^ n) =
      fun ω => ((stepInc b E k q K ε W Φ i ω ^ n : ℝ) : ℂ) := by
  funext ω
  by_cases h : ω ∈ alive b E k q K ε W i
  · simp only [stepInc, Set.indicator_of_mem h, realVal]
    push_cast; rw [hR, hR]
  · simp [stepInc, Set.indicator_of_notMem h, zero_pow hn]

theorem indicator_polyValue_sub_one (hR : IsRealPoly b E q Φ) (i : ℕ) :
    (alive b E k q K ε W i).indicator (fun ω =>
      polyValue b E k q W (i + 1) ω Φ - polyValue b E k q W i ω Φ) =
      fun ω => ((stepInc b E k q K ε W Φ i ω : ℝ) : ℂ) := by
  have h := indicator_polyValue_sub (W := W) k q K ε Φ hR i one_ne_zero
  simpa only [pow_one] using h

theorem indicator_polyValue_pow_sub (hR : IsRealPoly b E q Φ) (i r : ℕ) :
    (alive b E k q K ε W i).indicator (fun ω =>
      polyValue b E k q W (i + 1) ω (Φ ^ r) - polyValue b E k q W i ω (Φ ^ r)) =
      fun ω => (((alive b E k q K ε W i).indicator (fun ω =>
        realVal b E k q W (i + 1) Φ ω ^ r - realVal b E k q W i Φ ω ^ r) ω : ℝ) : ℂ) := by
  funext ω
  by_cases h : ω ∈ alive b E k q K ε W i
  · simp only [Set.indicator_of_mem h, realVal, polyValue, map_pow]
    have h1 := hR W k (i + 1) ω
    have h2 := hR W k i ω
    simp only [polyValue] at h1 h2
    push_cast; rw [h1, h2]
  · simp [Set.indicator_of_notMem h]

/-- The bound `C_Ψ(1 + K + K²)^{N_Ψ}` of an ordinary polynomial before the stop. -/
def aliveBound (K : ℝ) (Ψ : TracePoly nT nI) : ℝ := polyConst Ψ * (1 + K + K ^ 2) ^ polyExp Ψ

theorem aliveBound_nonneg {K : ℝ} (hK : 0 ≤ K) (Ψ : TracePoly nT nI) : 0 ≤ aliveBound K Ψ :=
  mul_nonneg (polyConst_nonneg Ψ) (by positivity)

variable (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (hq : IsIntervalTests q)
  (hΦ : IsOrdinaryPoly Φ) (hR : IsRealPoly b E q Φ) (hK : 0 ≤ K)

include hb hE1 hE2 hW hq hΦ hR hK in
/-- **Drift of one step.** -/
theorem ae_abs_condExp_stepInc_le {t₀ : ℝ} (hq0 : ∀ a t, t₀ < t → q a t = 0) {i : ℕ}
    (hi : ε * W ≤ i) (hit : t₀ < ((i + 1 : ℕ) : ℝ) / W) :
    ∀ᵐ ω ∂growthPathLaw W b,
      |(growthPathLaw W b)[stepInc b E k q K ε W Φ i | growthSigma W i] ω| ≤
        (W : ℝ)⁻¹ * aliveBound K (wordGenerator b E q (t₀ + 1) Φ) +
          ‖driftErr b E k q K ε W Φ i ω‖ := by
  have hgen : wordGenerator b E q (((i + 1 : ℕ) : ℝ) / W) Φ = wordGenerator b E q (t₀ + 1) Φ :=
    wordGenerator_congr_time b E q (fun a => by rw [hq0 a _ hit, hq0 a _ (by linarith)]) Φ
  have hP : ∀ᵐ ω ∂growthPathLaw W b, ω ∈ alive b E k q K ε W i →
      ‖polyValue b E k q W i ω (wordGenerator b E q (((i + 1 : ℕ) : ℝ) / W) Φ)‖ ≤
        aliveBound K (wordGenerator b E q (t₀ + 1) Φ) := by
    filter_upwards [ae_polyValue_le_of_alive (nT := nT) hb hE1 hE2 hW q hq K ε] with ω hω hA
    rw [hgen]; exact hω i k _ (wordGenerator_mem hΦ b E q _) hi hA
  have h := ae_abs_condExp_le (μ := growthPathLaw W b)
    (ContractingWords.measurableSet_alive b E k q K ε i) (d := stepInc b E k q K ε W Φ i)
    (fun ω h => stepInc_eq_zero b E k q K ε Φ h) (s := (W : ℝ)⁻¹) (by positivity)
    (aliveBound_nonneg hK _) hP
  filter_upwards [h] with ω hω
  have e : driftErr b E k q K ε W Φ i ω = (alive b E k q K ε W i).indicator (fun ω =>
      (growthPathLaw W b)[fun ω => ((stepInc b E k q K ε W Φ i ω : ℝ) : ℂ) | growthSigma W i] ω -
        (((W : ℝ)⁻¹ : ℝ) : ℂ) * polyValue b E k q W i ω
          (wordGenerator b E q (((i + 1 : ℕ) : ℝ) / W) Φ)) ω := by
    simp only [driftErr, indicator_polyValue_sub_one (W := W) k q K ε Φ hR, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [e]; exact hω

include hb hE1 hE2 hW hq hΦ hR hK in
/-- **Conditional second moment of one step.** -/
theorem condExp_stepInc_sq_le {i : ℕ} (hi : ε * W ≤ i) :
    (growthPathLaw W b)[fun ω => stepInc b E k q K ε W Φ i ω ^ 2 | growthSigma W i] ≤ᵐ[
      growthPathLaw W b] fun ω => (W : ℝ)⁻¹ * aliveBound K (wordCarre b E Φ) +
        ‖carreErr b E k q K ε W Φ i ω‖ := by
  have hP : ∀ᵐ ω ∂growthPathLaw W b, ω ∈ alive b E k q K ε W i →
      ‖polyValue b E k q W i ω (wordCarre b E Φ)‖ ≤ aliveBound K (wordCarre b E Φ) := by
    filter_upwards [ae_polyValue_le_of_alive (nT := nT) hb hE1 hE2 hW q hq K ε] with ω hω hA
    exact hω i k _ (wordCarre_mem hΦ b E) hi hA
  have h := ae_abs_condExp_le (μ := growthPathLaw W b)
    (ContractingWords.measurableSet_alive b E k q K ε i)
    (d := fun ω => stepInc b E k q K ε W Φ i ω ^ 2)
    (fun ω h => by simp [stepInc_eq_zero b E k q K ε Φ h]) (s := (W : ℝ)⁻¹) (by positivity)
    (aliveBound_nonneg hK _) hP
  filter_upwards [h] with ω hω
  have e : carreErr b E k q K ε W Φ i ω = (alive b E k q K ε W i).indicator (fun ω =>
      (growthPathLaw W b)[fun ω => ((stepInc b E k q K ε W Φ i ω ^ 2 : ℝ) : ℂ) |
        growthSigma W i] ω - (((W : ℝ)⁻¹ : ℝ) : ℂ) * polyValue b E k q W i ω (wordCarre b E Φ))
      ω := by
    simp only [carreErr, indicator_polyValue_sub (W := W) k q K ε Φ hR i two_ne_zero, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [e]; exact (le_abs_self _).trans hω

include hb hE1 hE2 hW hq hΦ hR hK in
/-- **Fourth moment of one step** (`fourth_cancel`). -/
theorem integral_stepInc_pow4_le {i : ℕ} (hi : ε * W ≤ i)
    (hX4 : Integrable (fun ω => realVal b E k q W i Φ ω ^ 4) (growthPathLaw W b))
    (hX4' : Integrable (fun ω => realVal b E k q W (i + 1) Φ ω ^ 4) (growthPathLaw W b))
    (hei : ∀ r < 5, Integrable (fun ω => ‖driftErr b E k q K ε W (Φ ^ r) i ω‖)
      (growthPathLaw W b)) :
    ∫ ω, stepInc b E k q K ε W Φ i ω ^ 4 ∂growthPathLaw W b ≤
      ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * aliveBound K Φ ^ (4 - r) *
        ∫ ω, ‖driftErr b E k q K ε W (Φ ^ r) i ω‖ ∂growthPathLaw W b := by
  set A := alive b E k q K ε W i
  set P : ℕ → GrowthPath W → ℂ := fun r ω =>
    polyValue b E k q W i ω (wordGenerator b E q (((i + 1 : ℕ) : ℝ) / W) (Φ ^ r))
  have hfun : ∀ r, (fun ω => ‖driftErr b E k q K ε W (Φ ^ r) i ω‖) = fun ω =>
      ‖A.indicator (fun ω => (growthPathLaw W b)[fun ω => ((A.indicator (fun ω =>
        realVal b E k q W (i + 1) Φ ω ^ r - realVal b E k q W i Φ ω ^ r) ω : ℝ) : ℂ) |
          growthSigma W i] ω - (((W : ℝ)⁻¹ : ℝ) : ℂ) * P r ω) ω‖ := fun r => by
    funext ω
    simp only [driftErr, indicator_polyValue_pow_sub (W := W) k q K ε Φ hR i r, Complex.ofReal_inv,
      Complex.ofReal_natCast, A, P]
  have hCX : ∀ᵐ ω ∂growthPathLaw W b, ω ∈ A → |realVal b E k q W i Φ ω| ≤ aliveBound K Φ := by
    filter_upwards [ae_polyValue_le_of_alive (nT := nT) hb hE1 hE2 hW q hq K ε] with ω hω hA
    exact (Complex.abs_re_le_norm _).trans
      (hω i k Φ (mem_ordPoly_of_isOrdinaryPoly hΦ) hi hA)
  have hcancel : ∀ ω, ∑ r ∈ range 5, ((Nat.choose 4 r : ℕ) : ℂ) *
      (-((realVal b E k q W i Φ ω : ℝ) : ℂ)) ^ (4 - r) * P r ω = 0 := fun ω => by
    have h := fourth_cancel b E q (((i + 1 : ℕ) : ℝ) / W) Φ (wordValue b E k q W i ω)
    have hr := hR W k i ω
    simp only [polyValue] at hr
    simp only [realVal, polyValue, P, hr]
    exact h
  have key := integral_pow4_le (growthSigma_le' W i)
    (ContractingWords.measurableSet_alive b E k q K ε i)
    (measurable_realVal_past b E k q Φ le_rfl).stronglyMeasurable
    ((measurable_realVal_past b E k q Φ le_rfl).mono (growthSigma_le' W (i + 1))
      le_rfl).aestronglyMeasurable hX4 hX4' (aliveBound_nonneg hK Φ) hCX ((W : ℝ)⁻¹) P hcancel
    (fun r hr => by rw [← hfun r]; exact hei r hr)
  refine (le_of_eq ?_).trans (key.trans_eq (Finset.sum_congr rfl fun r _ => by rw [hfun r]))
  rfl

end Step

end BlockBand.SourceProcess.FullSourceGenerator
