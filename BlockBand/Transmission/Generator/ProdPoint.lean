module

public import BlockBand.Transmission.Generator.ProdTools

/-!
# fdd convergence of tested functionals of polynomial growth

**`poly_point`**: for a bounded continuous past test `Φ` and a continuous `H` of `q` power sums
with `|H(x)| ≤ c(1 + Σ|x_i|)⁴`, the tested values `E_n[Φ H(P at pt)]` have second moments bounded
by one constant `K`, **uniformly** over point families `pt` with times in `[s, T]` (eventually in
`n`), the limit inherits the bound, and `E_n[Φ H] → E[Φ H]` (`fdd_tendsto`). Moments: eighth
moments of `Tr T^k` from the length-uniform contract (`moment_pow_along`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

theorem one_add_sum_pow_le {q : ℕ} (x : Fin q → ℝ) :
    (1 + ∑ i, |x i|) ^ 8 ≤ ((q : ℝ) + 1) ^ 7 * (1 + ∑ i, |x i| ^ 8) := by
  set f : Fin (q + 1) → ℝ := Fin.cons 1 fun i => |x i|
  have hf : ∀ i ∈ Finset.univ, 0 ≤ f i := fun i _ => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [f]
    · simp [f]
  have h := pow_sum_div_card_le_sum_pow hf 7
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_succ, f, Fin.cons_zero,
    Fin.cons_succ, one_pow] at h
  have hq : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) ^ 7 := by positivity
  rw [div_le_iff₀ hq] at h
  push_cast at h
  linarith

theorem enorm_sq_mul_le {m q : ℕ} (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    {H : (Fin q → ℝ) → ℝ} {c : ℝ} (hc : ∀ x, |H x| ≤ c * (1 + ∑ i, |x i|) ^ 4)
    (y : Fin m → ℝ) (x : Fin q → ℝ) :
    ‖Φ y * H x‖ₑ ^ 2 ≤
      ENNReal.ofReal (‖Φ‖ ^ 2 * c ^ 2 * ((q : ℝ) + 1) ^ 7) * (1 + ∑ i, ‖x i‖ₑ ^ 8) := by
  have hZ0 : 0 ≤ 1 + ∑ i, |x i| := by positivity
  have hc0 : 0 ≤ c * (1 + ∑ i, |x i|) ^ 4 := (abs_nonneg _).trans (hc x)
  have hS0 : 0 ≤ 1 + ∑ i, |x i| ^ 8 := by positivity
  have h1 : (Φ y * H x) ^ 2 ≤ ‖Φ‖ ^ 2 * c ^ 2 * ((q : ℝ) + 1) ^ 7 * (1 + ∑ i, |x i| ^ 8) := by
    have hΦ : |Φ y| ^ 2 ≤ ‖Φ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_bcf_le Φ y) 2
    have hH : |H x| ^ 2 ≤ (c * (1 + ∑ i, |x i|) ^ 4) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hc x) 2
    have hP := one_add_sum_pow_le x
    have e1 : (Φ y * H x) ^ 2 = |Φ y| ^ 2 * |H x| ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
    have e2 : (c * (1 + ∑ i, |x i|) ^ 4) ^ 2 = c ^ 2 * (1 + ∑ i, |x i|) ^ 8 := by ring
    rw [e1]
    calc |Φ y| ^ 2 * |H x| ^ 2 ≤ ‖Φ‖ ^ 2 * (c ^ 2 * (1 + ∑ i, |x i|) ^ 8) := by
          rw [← e2]; exact mul_le_mul hΦ hH (sq_nonneg _) (sq_nonneg _)
      _ ≤ ‖Φ‖ ^ 2 * (c ^ 2 * (((q : ℝ) + 1) ^ 7 * (1 + ∑ i, |x i| ^ 8))) := by
          gcongr
      _ = _ := by ring
  rw [enorm_sq_eq]
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow (abs_nonneg _)]

variable {Ω : Type*} [MeasurableSpace Ω]

theorem lintegral_poly_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {q : ℕ} {X : Fin q → α → ℝ} (hX : ∀ i, Measurable (X i)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ∫⁻ ω, ‖X i ω‖ₑ ^ 8 ∂μ ≤ ENNReal.ofReal C) {A : ℝ} (hA : 0 ≤ A) {f : α → ℝ}
    (hf : ∀ ω, ‖f ω‖ₑ ^ 2 ≤ ENNReal.ofReal A * (1 + ∑ i, ‖X i ω‖ₑ ^ 8)) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (A * (1 + q * C)) := by
  have hm : ∀ i, Measurable fun ω => ‖X i ω‖ₑ ^ 8 := fun i => (hX i).enorm.pow_const 8
  have hm2 : Measurable fun ω => ∑ i, ‖X i ω‖ₑ ^ 8 := Finset.measurable_fun_sum _ fun i _ => hm i
  have hm3 : Measurable fun ω => (1 : ℝ≥0∞) + ∑ i, ‖X i ω‖ₑ ^ 8 := measurable_const.add hm2
  calc ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ ≤ ∫⁻ ω, ENNReal.ofReal A * (1 + ∑ i, ‖X i ω‖ₑ ^ 8) ∂μ :=
        lintegral_mono hf
    _ = ENNReal.ofReal A * (1 + ∑ i, ∫⁻ ω, ‖X i ω‖ₑ ^ 8 ∂μ) := by
        rw [lintegral_const_mul _ hm3,
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_finsetSum _ fun i _ => hm i]
    _ ≤ ENNReal.ofReal A * (1 + ∑ _i : Fin q, ENNReal.ofReal C) := by
        gcongr with i; exact hC i
    _ = ENNReal.ofReal (A * (1 + q * C)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul hA, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **Tested functionals of polynomial growth**, uniformly over times in `[s, T]`. -/
theorem poly_point (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ}
    (hS : LimitSetup b e P Pk σ) {s T : ℝ} (hs : 0 < s) {m q : ℕ}
    (pts : Fin m → ℕ × ℝ) (hpts : ∀ l, 1 ≤ (pts l).1 ∧ 0 < (pts l).2)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) {H : (Fin q → ℝ) → ℝ} (hH : Continuous H)
    {c : ℝ} (hc : ∀ x, |H x| ≤ c * (1 + ∑ i, |x i|) ^ 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ᶠ n in atTop, ∀ pt : Fin q → ℕ × ℝ, (∀ i, 1 ≤ (pt i).1 ∧ s ≤ (pt i).2 ∧ (pt i).2 ≤ T) →
        ∫⁻ ω, ‖Φ (finVec b e (σ n) pts ω) * H (finVec b e (σ n) pt ω)‖ₑ ^ 2
          ∂growthPathLaw (σ n) b ≤ ENNReal.ofReal K) ∧
      ∀ pt : Fin q → ℕ × ℝ, (∀ i, 1 ≤ (pt i).1 ∧ s ≤ (pt i).2 ∧ (pt i).2 ≤ T) →
        ∫⁻ ω, ‖Φ (limVec Pk pts ω) * H (limVec Pk pt ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal K ∧
        Tendsto (fun n => ∫ ω, Φ (finVec b e (σ n) pts ω) * H (finVec b e (σ n) pt ω)
            ∂growthPathLaw (σ n) b) atTop
          (𝓝 (∫ ω, Φ (limVec Pk pts ω) * H (limVec Pk pt ω) ∂P)) := by
  have := hS.prob
  obtain ⟨C₈, hC₈0, hC₈⟩ := moment_pow_along hLU hb0 hb hE1 hE2 he hs 8 (by norm_num)
  obtain ⟨W₈, hW₈⟩ := hC₈ T
  set A := ‖Φ‖ ^ 2 * c ^ 2 * ((q : ℝ) + 1) ^ 7
  have hA : 0 ≤ A := by positivity
  set K := A * (1 + q * C₈)
  have hfin : ∀ᶠ n in atTop, ∀ pt : Fin q → ℕ × ℝ,
      (∀ i, 1 ≤ (pt i).1 ∧ s ≤ (pt i).2 ∧ (pt i).2 ≤ T) →
      ∫⁻ ω, ‖Φ (finVec b e (σ n) pts ω) * H (finVec b e (σ n) pt ω)‖ₑ ^ 2
        ∂growthPathLaw (σ n) b ≤ ENNReal.ofReal K := by
    filter_upwards [hS.tends.eventually_ge_atTop W₈] with n hn pt hpt
    exact lintegral_poly_le (X := fun i ω => finVec b e (σ n) pt ω i)
      (fun i => measurable_pathPower _ _ _ _) hC₈0
      (fun i => hW₈ _ hn _ (hpt i).2.1 (hpt i).2.2 _ (hpt i).1) hA
      (fun ω => enorm_sq_mul_le Φ hc _ _)
  refine ⟨K, by positivity, hfin, fun pt hpt => ?_⟩
  have hpt' : ∀ i, 1 ≤ (pt i).1 ∧ 0 < (pt i).2 := fun i =>
    ⟨(hpt i).1, lt_of_lt_of_le hs (hpt i).2.1⟩
  have hall := append_pos hpts hpt'
  set G : (Fin (m + q) → ℝ) → ℝ := fun x => Φ (fun l => x (Fin.castAdd q l)) *
    H (fun l => x (Fin.natAdd m l))
  have hG : Continuous G := (Φ.continuous.comp (continuous_pi fun l => continuous_apply _)).mul
    (hH.comp (continuous_pi fun l => continuous_apply _))
  have hfinG : ∀ n ω, G (finVec b e (σ n) (Fin.append pts pt) ω) =
      Φ (finVec b e (σ n) pts ω) * H (finVec b e (σ n) pt ω) := by
    intro n ω
    obtain ⟨h1, h2⟩ := finVec_append b e (σ n) pts pt ω
    simp only [G, h1, h2]
  have hlimG : ∀ ω, G (limVec Pk (Fin.append pts pt) ω) =
      Φ (limVec Pk pts ω) * H (limVec Pk pt ω) := by
    intro ω
    obtain ⟨h1, h2⟩ := limVec_append Pk pts pt ω
    simp only [G, h1, h2]
  have hC : ∀ᶠ N in atTop, ∫⁻ ω, ‖G (finVec b e (σ N) (Fin.append pts pt) ω)‖ₑ ^ 2
      ∂growthPathLaw (σ N) b ≤ ENNReal.ofReal K := by
    filter_upwards [hfin] with n hn
    simp only [hfinG]; exact hn pt hpt
  obtain ⟨hL, hT⟩ := fdd_tendsto hS.meas hS.fdd _ hall hG hC
  simp only [hfinG, hlimG] at hL hT
  exact ⟨hL, hT⟩

end BlockBand.Transmission.Generator
