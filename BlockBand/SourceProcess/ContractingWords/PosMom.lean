module

public import BlockBand.SourceProcess.ContractingWords.PosCut
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Moments of products of slot bilinears

* `prod_le_sum_pow`: `Π_{i∈s} z_i ≤ Σ_{i∈s} z_i^{|s|}` for `z ≥ 0`, `s ≠ ∅`;
* `prod_moment`: if `E|f_i|^{|s|} ≤ B` for `i ∈ s`, then `Π_{i∈s}|f_i|` is integrable and
  `E Π_{i∈s}|f_i| ≤ |s| B` (no Hölder needed);
* `SlotMoments Δ M β`: for every slot `p` and unit vectors, `x*Δ_p y` is measurable and
  `E|x*Δ_p y|^m ≤ β^m`, `1 ≤ m ≤ M`;
* `remSum_le`: `Σ_{t ⊆ Fin r, k ≤ |t|} |t| β^{|t|} ≤ 2^r r (β^k + β^{r+3})`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements

theorem prod_le_sum_pow {I : Type*} (s : Finset I) (hs : s.Nonempty) (z : I → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∏ i ∈ s, z i ≤ ∑ i ∈ s, z i ^ s.card := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s z hs
  calc ∏ i ∈ s, z i ≤ ∏ _i ∈ s, z j := Finset.prod_le_prod₀ (fun i _ => hz i) hmax
    _ = z j ^ s.card := Finset.prod_const _
    _ ≤ ∑ i ∈ s, z i ^ s.card :=
        Finset.single_le_sum (f := fun i => z i ^ s.card) (fun i _ => pow_nonneg (hz i) _) hj

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Products of `L^{|s|}` variables.** -/
theorem prod_moment {I : Type*} (s : Finset I) (hs : s.Nonempty) (f : I → Ω → ℂ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (f i) μ)
    (hi : ∀ i ∈ s, Integrable (fun ω => ‖f i ω‖ ^ s.card) μ) {B : ℝ}
    (hB : ∀ i ∈ s, ∫ ω, ‖f i ω‖ ^ s.card ∂μ ≤ B) :
    Integrable (fun ω => ∏ i ∈ s, f i ω) μ ∧ ∫ ω, ∏ i ∈ s, ‖f i ω‖ ∂μ ≤ s.card * B := by
  have hS : Integrable (fun ω => ∑ i ∈ s, ‖f i ω‖ ^ s.card) μ := integrable_finsetSum _ hi
  have hpt : ∀ ω, ∏ i ∈ s, ‖f i ω‖ ≤ ∑ i ∈ s, ‖f i ω‖ ^ s.card := fun ω =>
    prod_le_sum_pow s hs (fun i => ‖f i ω‖) fun _ => norm_nonneg _
  have hmP : AEStronglyMeasurable (fun ω => ∏ i ∈ s, f i ω) μ :=
    Finset.aestronglyMeasurable_fun_prod s hm
  have hmN : AEStronglyMeasurable (fun ω => ∏ i ∈ s, ‖f i ω‖) μ :=
    Finset.aestronglyMeasurable_fun_prod s fun i hi => (hm i hi).norm
  refine ⟨hS.mono' hmP (Filter.Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [norm_prod]; exact hpt ω
  · calc ∫ ω, ∏ i ∈ s, ‖f i ω‖ ∂μ ≤ ∫ ω, ∑ i ∈ s, ‖f i ω‖ ^ s.card ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            Finset.prod_nonneg fun _ _ => norm_nonneg _) hS (Filter.Eventually.of_forall hpt)
      _ = ∑ i ∈ s, ∫ ω, ‖f i ω‖ ^ s.card ∂μ := integral_finsetSum _ hi
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hB
      _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Slot moments**: every slot bilinear at unit vectors is measurable with
`E|x*Δ_p y|^m ≤ β^m` for `1 ≤ m ≤ M`. -/
def SlotMoments {P : Type*} (μ : Measure Ω) (Δ : Ω → P → Matrix n n ℂ) (M : ℕ) (β : ℝ) : Prop :=
  ∀ p (u v : n → ℂ), vecNorm u ≤ 1 → vecNorm v ≤ 1 →
    AEStronglyMeasurable (fun ω => bilinear u (Δ ω p) v) μ ∧
    ∀ m : ℕ, 1 ≤ m → m ≤ M → Integrable (fun ω => ‖bilinear u (Δ ω p) v‖ ^ m) μ ∧
      ∫ ω, ‖bilinear u (Δ ω p) v‖ ^ m ∂μ ≤ β ^ m

theorem pow_le_two_ends {β : ℝ} (hβ : 0 ≤ β) {k m r : ℕ} (hk : k ≤ m) (hm : m ≤ r) :
    β ^ m ≤ β ^ k + β ^ r := by
  rcases le_total β 1 with h | h
  · have := pow_le_pow_of_le_one hβ h hk
    linarith [pow_nonneg hβ r]
  · have := pow_le_pow_right₀ h hm
    linarith [pow_nonneg hβ k]

/-- The remainder sum over subsets with at least `k` elements. -/
theorem remSum_le {r k : ℕ} {β : ℝ} (hβ : 0 ≤ β) :
    ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => k ≤ t.card),
        (t.card : ℝ) * β ^ t.card ≤ 2 ^ r * r * (β ^ k + β ^ (r + 3)) := by
  have hterm : ∀ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => k ≤ t.card),
      (t.card : ℝ) * β ^ t.card ≤ r * (β ^ k + β ^ (r + 3)) := fun t ht => by
    have hk' := (Finset.mem_filter.mp ht).2
    have hr : t.card ≤ r := by simpa using Finset.card_le_univ t
    have hb := pow_le_two_ends hβ hk' (hr.trans (Nat.le_add_right r 3))
    have hr' : (t.card : ℝ) ≤ r := by exact_mod_cast hr
    exact mul_le_mul hr' hb (pow_nonneg hβ _) (Nat.cast_nonneg _)
  calc _ ≤ ∑ _t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => k ≤ t.card),
        (r : ℝ) * (β ^ k + β ^ (r + 3)) := Finset.sum_le_sum hterm
    _ ≤ ∑ _t ∈ (Finset.univ : Finset (Fin r)).powerset, (r : ℝ) * (β ^ k + β ^ (r + 3)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by
          positivity
    _ = 2 ^ r * r * (β ^ k + β ^ (r + 3)) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring

end BlockBand.SourceProcess.ContractingWords
