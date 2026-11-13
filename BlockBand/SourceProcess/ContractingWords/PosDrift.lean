module

public import BlockBand.SourceProcess.ContractingWords.PosMom
public import BlockBand.SourceProcess.ContractingWords.LayerCore

/-!
# The random expansion of one word to second order

A word `posTr A T` with a positional cut `(c, x, y)`, old separators `‖σ_p‖ ≤ 1`, random
increments `Δ_p` with `SlotMoments μ Δ M β`, `X_t = posTr A (pw σ Δ t)`:
* `term_moment`: `X_t` is integrable and `E|X_t| ≤ (Σ|c_l|)|t|β^{|t|}` (`1 ≤ |t| ≤ M`);
* `drift_expand`: `|E posTr A (σ+Δ) - posTr A σ - Σ_{|t|=1} EX_t - Σ_{|t|=2} EX_t|
  ≤ (Σ|c_l|) 2^r r (β³ + β^{r+3})` (`r ≤ M`);
* `first_mean`: `E X_{{p}} = posTr A (pw σ m {p})`, `m_p = E Δ_p`;
* `second_mean`: `E X_{{p,q}} = Σ_l c_l E[(x_{lp}*Δ_p y_{lp})(x_{lq}*Δ_q y_{lq})] Π_{others} x*σy`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {A : Fin r → Matrix n n ℂ}
  {ι : Type} [Fintype ι] {c : ι → ℂ} {x y : ι → Fin r → n → ℂ}

/-- The four-way split of a sum over subsets by cardinality. -/
theorem sum_powerset_split {M : Type*} [AddCommMonoid M] (f : Finset (Fin r) → M) :
    ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset, f t = f ∅ +
      ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 1), f t +
      ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 2), f t +
      ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => 3 ≤ t.card), f t := by
  set S := (Finset.univ : Finset (Fin r)).powerset
  have hpt : ∀ t, f t = (if t.card = 0 then f t else 0) + (if t.card = 1 then f t else 0) +
      (if t.card = 2 then f t else 0) + (if 3 ≤ t.card then f t else 0) := fun t => by
    rcases Nat.lt_or_ge t.card 3 with h | h
    · interval_cases hc : t.card <;> simp
    · have h0 : t.card ≠ 0 := by omega
      have h1 : t.card ≠ 1 := by omega
      have h2 : t.card ≠ 2 := by omega
      simp [h0, h1, h2, h]
  have h0 : ∑ t ∈ S, (if t.card = 0 then f t else 0) = f ∅ := by
    simp only [Finset.card_eq_zero]
    rw [Finset.sum_ite_eq']
    simp [S]
  conv_lhs => rw [Finset.sum_congr rfl fun t _ => hpt t]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, h0,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]

variable (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
  (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
  {σ : Fin r → Matrix n n ℂ} {Δ : Ω → Fin r → Matrix n n ℂ} {M : ℕ} {β : ℝ}

omit [IsProbabilityMeasure μ] in
include hrep hxy in
/-- **One term**: integrable, with `E|X_t| ≤ (Σ|c_l|)|t|β^{|t|}`. -/
theorem term_moment (hσ : ∀ p, ‖σ p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β) {t : Finset (Fin r)}
    (ht : t.Nonempty) (htM : t.card ≤ M) :
    Integrable (fun ω => posTr A (pw σ (Δ ω) t)) μ ∧
      ∫ ω, ‖posTr A (pw σ (Δ ω) t)‖ ∂μ ≤ (∑ l, ‖c l‖) * (t.card * β ^ t.card) := by
  have h1 : 1 ≤ t.card := Finset.card_pos.mpr ht
  have hP : ∀ l, Integrable (fun ω => ∏ p ∈ t, bilinear (x l p) (Δ ω p) (y l p)) μ ∧
      ∫ ω, ∏ p ∈ t, ‖bilinear (x l p) (Δ ω p) (y l p)‖ ∂μ ≤ t.card * β ^ t.card := fun l =>
    prod_moment t ht (fun p ω => bilinear (x l p) (Δ ω p) (y l p))
      (fun p _ => (hΔ p _ _ (hxy l p).1 (hxy l p).2).1)
      (fun p _ => ((hΔ p _ _ (hxy l p).1 (hxy l p).2).2 _ h1 htM).1)
      (fun p _ => ((hΔ p _ _ (hxy l p).1 (hxy l p).2).2 _ h1 htM).2)
  have hfun : (fun ω => posTr A (pw σ (Δ ω) t)) = fun ω => ∑ l, c l *
      ((∏ p ∈ t, bilinear (x l p) (Δ ω p) (y l p)) *
        ∏ p ∈ Finset.univ \ t, bilinear (x l p) (σ p) (y l p)) :=
    funext fun ω => posTr_pw hrep σ (Δ ω) t
  have hint : Integrable (fun ω => posTr A (pw σ (Δ ω) t)) μ := by
    rw [hfun]
    exact integrable_finsetSum _ fun l _ => ((hP l).1.mul_const _).const_mul _
  refine ⟨hint, ?_⟩
  have hdom : Integrable (fun ω => ∑ l, ‖c l‖ * ∏ p ∈ t, ‖bilinear (x l p) (Δ ω p) (y l p)‖) μ :=
    integrable_finsetSum _ fun l _ => ((hP l).1.norm.congr (Filter.Eventually.of_forall
      fun ω => by simp [norm_prod])).const_mul _
  calc ∫ ω, ‖posTr A (pw σ (Δ ω) t)‖ ∂μ ≤
        ∫ ω, ∑ l, ‖c l‖ * ∏ p ∈ t, ‖bilinear (x l p) (Δ ω p) (y l p)‖ ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hdom
          (Filter.Eventually.of_forall fun ω => norm_posTr_pw_le hrep hxy hσ (Δ ω) t)
    _ = ∑ l, ‖c l‖ * ∫ ω, ∏ p ∈ t, ‖bilinear (x l p) (Δ ω p) (y l p)‖ ∂μ := by
        rw [integral_finsetSum _ fun l _ => ((hP l).1.norm.congr (Filter.Eventually.of_forall
          fun ω => by simp [norm_prod])).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ ≤ ∑ l, ‖c l‖ * (t.card * β ^ t.card) :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hP l).2 (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

include hrep hxy in
/-- **The second-order expansion of the mean.** -/
theorem drift_expand (hσ : ∀ p, ‖σ p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β) (hβ : 0 ≤ β)
    (hrM : r ≤ M) :
    (∀ t : Finset (Fin r), Integrable (fun ω => posTr A (pw σ (Δ ω) t)) μ) ∧
    ‖∫ ω, posTr A (σ + Δ ω) ∂μ - posTr A σ -
        ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 1),
          ∫ ω, posTr A (pw σ (Δ ω) t) ∂μ -
        ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t.card = 2),
          ∫ ω, posTr A (pw σ (Δ ω) t) ∂μ‖ ≤
      (∑ l, ‖c l‖) * (2 ^ r * r * (β ^ 3 + β ^ (r + 3))) := by
  have hint : ∀ t : Finset (Fin r), Integrable (fun ω => posTr A (pw σ (Δ ω) t)) μ := by
    intro t
    rcases t.eq_empty_or_nonempty with rfl | ht
    · have e0 : ∀ ω, pw σ (Δ ω) ∅ = σ := fun ω => funext fun i => by simp [pw]
      simp only [e0]; exact integrable_const _
    · exact (term_moment hrep hxy hσ hΔ ht ((Finset.card_le_univ t).trans (by simpa using hrM))).1
  refine ⟨hint, ?_⟩
  have hsum : ∫ ω, posTr A (σ + Δ ω) ∂μ =
      ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset, ∫ ω, posTr A (pw σ (Δ ω) t) ∂μ := by
    simp only [posTr_add hrep]
    exact integral_finsetSum _ fun t _ => hint t
  have hE0 : ∫ ω, posTr A (pw σ (Δ ω) ∅) ∂μ = posTr A σ := by
    have : ∀ ω, pw σ (Δ ω) ∅ = σ := fun ω => funext fun i => by simp [pw]
    simp [this]
  rw [hsum, sum_powerset_split, hE0]
  have e : ∀ a b c d : ℂ, a + b + c + d - a - b - c = d := fun _ _ _ _ => by ring
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter (fun t => 3 ≤ t.card),
        (∑ l, ‖c l‖) * (t.card * β ^ t.card) := Finset.sum_le_sum fun t ht => by
          have h3 := (Finset.mem_filter.mp ht).2
          have hne : t.Nonempty := Finset.card_pos.mp (by omega)
          exact (norm_integral_le_integral_norm _).trans (term_moment hrep hxy hσ hΔ hne
            ((Finset.card_le_univ t).trans (by simpa using hrM))).2
    _ = (∑ l, ‖c l‖) * ∑ t ∈ (Finset.univ : Finset (Fin r)).powerset.filter
          (fun t => 3 ≤ t.card), (t.card : ℝ) * β ^ t.card := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (remSum_le hβ)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)

omit [IsProbabilityMeasure μ] in
include hrep in
/-- **First order**: `E X_{{p}} = posTr A (pw σ (EΔ) {p})`. -/
theorem first_mean (hent : ∀ p i j, Integrable (fun ω => Δ ω p i j) μ) (p : Fin r) :
    ∫ ω, posTr A (pw σ (Δ ω) {p}) ∂μ =
      posTr A (pw σ (fun q => matrixExpect μ fun ω => Δ ω q) {p}) := by
  simp only [posTr_pw hrep, Finset.prod_singleton]
  rw [integral_finsetSum _ fun l _ =>
    ((integrable_bilinear_of (hent p) _ _).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_mul_const, FullSource.integral_bilinear _ (hent p)]

omit [IsProbabilityMeasure μ] in
include hrep in
/-- **Second order**: `E X_{{p,q}} = Σ_l c_l E[δ_{lp}δ_{lq}] Π_{others} x*σy`. -/
theorem second_mean {p q : Fin r} (hpq : p ≠ q)
    (hint : ∀ l, Integrable (fun ω => bilinear (x l p) (Δ ω p) (y l p) *
      bilinear (x l q) (Δ ω q) (y l q)) μ) :
    ∫ ω, posTr A (pw σ (Δ ω) {p, q}) ∂μ =
      ∑ l, c l * ((∫ ω, bilinear (x l p) (Δ ω p) (y l p) *
        bilinear (x l q) (Δ ω q) (y l q) ∂μ) *
          ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i)) := by
  simp only [posTr_pw hrep, Finset.prod_pair hpq]
  rw [integral_finsetSum _ fun l _ => ((hint l).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_mul_const]

end BlockBand.SourceProcess.ContractingWords
