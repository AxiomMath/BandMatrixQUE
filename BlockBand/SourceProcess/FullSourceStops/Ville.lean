module

public import BlockBand.Internal.Contracts.TransmissionUniform2

/-!
# A maximal inequality for weighted supermartingales, and a dyadic tail bound

* `ville`: let `Y_m ≥ 0` be measurable and `c ≥ 1`. Assume that on each no-hit event
  `S_m = {Y_i < λ, i ≤ m}`, `∫_{S_m} Y_{m+1} ≤ c ∫_{S_m} Y_m`. Then `λ P(S_mᶜ) ≤ c^m E Y_0`.
  The proof is the stopped-process argument, in pointwise form:
  `F_m = λ1_{S_mᶜ} + 1_{S_m}Y_m` satisfies `F_{m+1} ≤ λ1_{S_mᶜ} + 1_{S_m}Y_{m+1}`.
* `lintegral_le_of_dyadic_tail`: if `4^i P{2^i ≤ X} ≤ A` for every `i`, then `E X ≤ 1 + 4A`
  (probability measure).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*}

/-- The no-hit event `S_m = {Y_i < λ for all i ≤ m}`. -/
def noHit (Y : ℕ → Ω → ℝ≥0∞) (lam : ℝ≥0∞) (m : ℕ) : Set Ω := {ω | ∀ i, i ≤ m → Y i ω < lam}

theorem measurableSet_noHit [MeasurableSpace Ω] {Y : ℕ → Ω → ℝ≥0∞} (hY : ∀ i, Measurable (Y i)) (lam : ℝ≥0∞)
    (m : ℕ) : MeasurableSet (noHit Y lam m) := by
  have : noHit Y lam m = ⋂ i, ⋂ (_ : i ≤ m), {ω | Y i ω < lam} := by ext ω; simp [noHit]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt (hY i) measurable_const

theorem mem_noHit_succ {Y : ℕ → Ω → ℝ≥0∞} {lam : ℝ≥0∞} {m : ℕ} {ω : Ω} :
    ω ∈ noHit Y lam (m + 1) ↔ ω ∈ noHit Y lam m ∧ Y (m + 1) ω < lam := by
  simp only [noHit, Set.mem_ofPred_eq]
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega), h (m + 1) le_rfl⟩
  · rintro ⟨h, h'⟩ i hi
    rcases Nat.le_succ_iff.mp hi with hi | rfl
    · exact h i hi
    · exact h'

/-- The pointwise stopped value `F_m = λ1_{S_mᶜ} + 1_{S_m}Y_m`. -/
def villeF (Y : ℕ → Ω → ℝ≥0∞) (lam : ℝ≥0∞) (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (noHit Y lam m)ᶜ.indicator (fun _ => lam) ω + (noHit Y lam m).indicator (Y m) ω

theorem villeF_zero_le (Y : ℕ → Ω → ℝ≥0∞) (lam : ℝ≥0∞) (ω : Ω) : villeF Y lam 0 ω ≤ Y 0 ω := by
  by_cases h : ω ∈ noHit Y lam 0
  · simp [villeF, h]
  · have h' : lam ≤ Y 0 ω := by
      by_contra hc
      exact h fun i hi => by rw [Nat.le_zero.mp hi]; exact not_le.mp hc
    simp [villeF, h, h']

theorem villeF_succ_le (Y : ℕ → Ω → ℝ≥0∞) (lam : ℝ≥0∞) (m : ℕ) (ω : Ω) :
    villeF Y lam (m + 1) ω ≤
      (noHit Y lam m)ᶜ.indicator (fun _ => lam) ω + (noHit Y lam m).indicator (Y (m + 1)) ω := by
  by_cases h : ω ∈ noHit Y lam m
  · by_cases h' : Y (m + 1) ω < lam
    · have h1 : ω ∈ noHit Y lam (m + 1) := mem_noHit_succ.mpr ⟨h, h'⟩
      simp [villeF, h, h1]
    · have h1 : ω ∉ noHit Y lam (m + 1) := fun hh => h' (mem_noHit_succ.mp hh).2
      simp only [villeF, Set.indicator_of_mem (Set.mem_compl h1), Set.indicator_of_notMem h1,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h), Set.indicator_of_mem h, add_zero,
        zero_add]
      exact not_lt.mp h'
  · have h1 : ω ∉ noHit Y lam (m + 1) := fun hh => h (mem_noHit_succ.mp hh).1
    simp [villeF, h, h1]

theorem lintegral_villeF_le [MeasurableSpace Ω] (μ : Measure Ω) {Y : ℕ → Ω → ℝ≥0∞} (hY : ∀ i, Measurable (Y i))
    (lam c : ℝ≥0∞) (hc : 1 ≤ c)
    (hstep : ∀ m, ∫⁻ ω, (noHit Y lam m).indicator (Y (m + 1)) ω ∂μ ≤
      c * ∫⁻ ω, (noHit Y lam m).indicator (Y m) ω ∂μ) (m : ℕ) :
    ∫⁻ ω, villeF Y lam m ω ∂μ ≤ c ^ m * ∫⁻ ω, Y 0 ω ∂μ := by
  induction m with
  | zero => simpa using lintegral_mono (villeF_zero_le Y lam)
  | succ m ih =>
    have hS := measurableSet_noHit hY lam m
    have hm1 : Measurable ((noHit Y lam m)ᶜ.indicator fun _ : Ω => lam) :=
      measurable_const.indicator hS.compl
    calc ∫⁻ ω, villeF Y lam (m + 1) ω ∂μ
        ≤ ∫⁻ ω, ((noHit Y lam m)ᶜ.indicator (fun _ => lam) ω +
            (noHit Y lam m).indicator (Y (m + 1)) ω) ∂μ := lintegral_mono (villeF_succ_le Y lam m)
      _ = ∫⁻ ω, (noHit Y lam m)ᶜ.indicator (fun _ => lam) ω ∂μ +
            ∫⁻ ω, (noHit Y lam m).indicator (Y (m + 1)) ω ∂μ := lintegral_add_left hm1 _
      _ ≤ c * ∫⁻ ω, (noHit Y lam m)ᶜ.indicator (fun _ => lam) ω ∂μ +
            c * ∫⁻ ω, (noHit Y lam m).indicator (Y m) ω ∂μ := by
          gcongr
          · exact le_mul_of_one_le_left bot_le hc
          · exact hstep m
      _ = c * ∫⁻ ω, villeF Y lam m ω ∂μ := by
          rw [← mul_add, ← lintegral_add_left hm1]; rfl
      _ ≤ c * (c ^ m * ∫⁻ ω, Y 0 ω ∂μ) := by gcongr
      _ = c ^ (m + 1) * ∫⁻ ω, Y 0 ω ∂μ := by rw [pow_succ]; ring

/-- **Maximal inequality for weighted supermartingales.** -/
theorem ville [MeasurableSpace Ω] (μ : Measure Ω) {Y : ℕ → Ω → ℝ≥0∞} (hY : ∀ i, Measurable (Y i))
    (lam c : ℝ≥0∞) (hc : 1 ≤ c)
    (hstep : ∀ m, ∫⁻ ω, (noHit Y lam m).indicator (Y (m + 1)) ω ∂μ ≤
      c * ∫⁻ ω, (noHit Y lam m).indicator (Y m) ω ∂μ) (m : ℕ) :
    lam * μ (noHit Y lam m)ᶜ ≤ c ^ m * ∫⁻ ω, Y 0 ω ∂μ := by
  refine le_trans ?_ (lintegral_villeF_le μ hY lam c hc hstep m)
  rw [← lintegral_indicator_const (measurableSet_noHit hY lam m).compl]
  exact lintegral_mono fun ω => le_add_right le_rfl

/-- The complement of the no-hit event. -/
theorem compl_noHit (Y : ℕ → Ω → ℝ≥0∞) (lam : ℝ≥0∞) (m : ℕ) :
    (noHit Y lam m)ᶜ = {ω | ∃ i, i ≤ m ∧ lam ≤ Y i ω} := by
  ext ω; simp [noHit]

/-- Pointwise dyadic decomposition: `x ≤ 1 + Σ_i 2^{i+1} 1_{2^i ≤ x}`. -/
theorem le_one_add_dyadic (x : ℝ≥0∞) :
    x ≤ 1 + ∑' i : ℕ, (2 : ℝ≥0∞) ^ (i + 1) * {y : ℝ≥0∞ | (2 : ℝ≥0∞) ^ i ≤ y}.indicator 1 x := by
  by_cases hx1 : x ≤ 1
  · exact hx1.trans le_self_add
  push Not at hx1
  by_cases hxt : x = ⊤
  · subst hxt
    have : ∑' i : ℕ, (2 : ℝ≥0∞) ^ (i + 1) * {y : ℝ≥0∞ | (2 : ℝ≥0∞) ^ i ≤ y}.indicator 1 ⊤ = ⊤ := by
      refine top_unique ((ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm.le.trans
        (ENNReal.tsum_le_tsum fun i => ?_))
      rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
      exact one_le_pow₀ (by norm_num)
    rw [this]; exact le_top
  have hr : 1 ≤ x.toReal := by
    have := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hxt).mpr hx1.le
    simpa using this
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  have hxe : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hxt).symm
  have h2 : ∀ m : ℕ, (2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := fun m => by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have hmem : x ∈ {y : ℝ≥0∞ | (2 : ℝ≥0∞) ^ n ≤ y} := by
    show (2 : ℝ≥0∞) ^ n ≤ x
    rw [hxe, h2]; exact ENNReal.ofReal_le_ofReal hn1
  refine le_trans ?_ le_add_self
  refine le_trans ?_ (ENNReal.le_tsum n)
  simp only [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
  rw [hxe, h2]; exact ENNReal.ofReal_le_ofReal hn2.le

/-- **From a dyadic tail to the first moment.** -/
theorem lintegral_le_of_dyadic_tail [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (A : ℝ≥0∞)
    (h : ∀ i : ℕ, (4 : ℝ≥0∞) ^ i * μ {ω | (2 : ℝ≥0∞) ^ i ≤ X ω} ≤ A) :
    ∫⁻ ω, X ω ∂μ ≤ 1 + 4 * A := by
  have hmeas : ∀ i : ℕ, MeasurableSet {ω | (2 : ℝ≥0∞) ^ i ≤ X ω} := fun i =>
    measurableSet_le measurable_const hX
  have hterm : ∀ i : ℕ, (2 : ℝ≥0∞) ^ (i + 1) * μ {ω | (2 : ℝ≥0∞) ^ i ≤ X ω} ≤
      2 * A * (2⁻¹) ^ i := by
    intro i
    have h22 : (2 : ℝ≥0∞) ^ i * (2⁻¹) ^ i = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    have h4 : (4 : ℝ≥0∞) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
    calc (2 : ℝ≥0∞) ^ (i + 1) * μ {ω | (2 : ℝ≥0∞) ^ i ≤ X ω}
        = 2 * ((4 : ℝ≥0∞) ^ i * μ {ω | (2 : ℝ≥0∞) ^ i ≤ X ω}) * (2⁻¹) ^ i := by
          rw [h4, pow_succ]
          calc (2 : ℝ≥0∞) ^ i * 2 * μ {ω | 2 ^ i ≤ X ω}
              = 2 * (2 ^ i * μ {ω | 2 ^ i ≤ X ω}) * (2 ^ i * (2⁻¹) ^ i) := by rw [h22]; ring
            _ = _ := by ring
      _ ≤ 2 * A * (2⁻¹) ^ i := by gcongr; exact h i
  calc ∫⁻ ω, X ω ∂μ
      ≤ ∫⁻ ω, (1 + ∑' i : ℕ, (2 : ℝ≥0∞) ^ (i + 1) *
          {ω | (2 : ℝ≥0∞) ^ i ≤ X ω}.indicator 1 ω) ∂μ := by
        refine lintegral_mono fun ω => (le_one_add_dyadic (X ω)).trans_eq ?_
        rfl
    _ = 1 + ∑' i : ℕ, (2 : ℝ≥0∞) ^ (i + 1) * μ {ω | (2 : ℝ≥0∞) ^ i ≤ X ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun i => ((measurable_one.indicator (hmeas i)).const_mul _).aemeasurable]
        congr 1; congr 1; funext i
        rw [lintegral_const_mul _ (measurable_one.indicator (hmeas i)),
          lintegral_indicator_one (hmeas i)]
    _ ≤ 1 + ∑' i : ℕ, 2 * A * (2⁻¹) ^ i := add_le_add_right (ENNReal.tsum_le_tsum hterm) 1
    _ = 1 + 4 * A := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        ring

end BlockBand.SourceProcess.FullSourceStops
