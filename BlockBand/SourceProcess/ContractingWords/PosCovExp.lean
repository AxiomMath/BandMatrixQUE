module

public import BlockBand.SourceProcess.ContractingWords.PosCov

/-!
# The second conditional increment of two words, expanded

* `posTr_sub_eq`: `posTr A (σ+Δ) - posTr A σ = Σ_{t≠∅} posTr A (pw σ Δ t)`;
* `cov_expand`: `|E[UU'] - Σ_{p,q} E[X_{{p}}X'_{{q}}]| ≤ ΓΓ' 2^{r+r'}(r+r')(β³ + β^{r+r'})`;
* `cross_mean`: `E[X_{{p}}X'_{{q}}] = Σ_{l,l'} c_l c'_{l'} E[δ_{lp}δ'_{l'q}] Π x*σy Π x'*σ'y'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {n : Type} [Fintype n] [DecidableEq n] {r r' : ℕ} {A : Fin r → Matrix n n ℂ}
  {A' : Fin r' → Matrix n n ℂ} {ι ι' : Type} [Fintype ι] [Fintype ι'] {c : ι → ℂ} {c' : ι' → ℂ}
  {x y : ι → Fin r → n → ℂ} {x' y' : ι' → Fin r' → n → ℂ}

/-- The nonempty subsets. -/
abbrev nonemptySubsets (r : ℕ) : Finset (Finset (Fin r)) :=
  (Finset.univ : Finset (Fin r)).powerset.filter fun t => t ≠ ∅

theorem posTr_sub_eq (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ Δ : Fin r → Matrix n n ℂ) :
    posTr A (σ + Δ) - posTr A σ = ∑ t ∈ nonemptySubsets r, posTr A (pw σ Δ t) := by
  rw [posTr_add hrep, ← Finset.sum_filter_add_sum_filter_not _ (fun t => t = ∅)]
  have h : (Finset.univ : Finset (Fin r)).powerset.filter (fun t => t = ∅) = {∅} := by
    ext t; simp
  have h0 : pw σ Δ ∅ = σ := funext fun i => by simp [pw]
  rw [h, Finset.sum_singleton, h0]; ring

variable (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
  (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
  (hrep' : ∀ T, posTr A' T = ∑ l, c' l * ∏ p, bilinear (x' l p) (T p) (y' l p))
  (hxy' : ∀ l p, vecNorm (x' l p) ≤ 1 ∧ vecNorm (y' l p) ≤ 1)
  {σ : Fin r → Matrix n n ℂ} {σ' : Fin r' → Matrix n n ℂ} {Δ : Ω → Fin r → Matrix n n ℂ}
  {Δ' : Ω → Fin r' → Matrix n n ℂ} {M : ℕ} {β : ℝ}

include hrep hxy hrep' hxy' in
/-- **The covariance expansion.** -/
theorem cov_expand (hσ : ∀ p, ‖σ p‖ ≤ 1) (hσ' : ∀ p, ‖σ' p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β)
    (hΔ' : SlotMoments μ Δ' M β) (hβ : 0 ≤ β) (hM : r + r' ≤ M) :
    ‖∫ ω, (posTr A (σ + Δ ω) - posTr A σ) * (posTr A' (σ' + Δ' ω) - posTr A' σ') ∂μ -
        ∑ p, ∑ q, ∫ ω, posTr A (pw σ (Δ ω) {p}) * posTr A' (pw σ' (Δ' ω) {q}) ∂μ‖ ≤
      (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (2 ^ r * 2 ^ r' * ((r + r' : ℕ) * (β ^ 3 + β ^ (r + r' + 3)))) := by
  set S := nonemptySubsets r ×ˢ nonemptySubsets r'
  set F : Finset (Fin r) × Finset (Fin r') → Ω → ℂ := fun T ω =>
    posTr A (pw σ (Δ ω) T.1) * posTr A' (pw σ' (Δ' ω) T.2)
  have hmem : ∀ T ∈ S, T.1.Nonempty ∧ T.2.Nonempty ∧ T.1.card + T.2.card ≤ M := fun T hT => by
    simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hT
    refine ⟨Finset.nonempty_iff_ne_empty.mpr hT.1.2, Finset.nonempty_iff_ne_empty.mpr hT.2.2, ?_⟩
    have := Finset.card_le_univ T.1; have := Finset.card_le_univ T.2
    simp only [Fintype.card_fin] at *; omega
  have hPM : ∀ T ∈ S, Integrable (F T) μ ∧ ∫ ω, ‖F T ω‖ ∂μ ≤ (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) *
      ((T.1.card + T.2.card : ℕ) * β ^ (T.1.card + T.2.card)) := fun T hT =>
    pair_moment hrep hxy hrep' hxy' hσ hσ' hΔ hΔ' (hmem T hT).1 (hmem T hT).2.2
  have hUU : ∀ ω, (posTr A (σ + Δ ω) - posTr A σ) * (posTr A' (σ' + Δ' ω) - posTr A' σ') =
      ∑ T ∈ S, F T ω := fun ω => by
    rw [posTr_sub_eq hrep, posTr_sub_eq hrep', Finset.sum_mul_sum, ← Finset.sum_product']
  simp only [hUU]
  rw [integral_finsetSum _ fun T hT => (hPM T hT).1,
    ← Finset.sum_filter_add_sum_filter_not S (fun T => T.1.card = 1 ∧ T.2.card = 1)]
  have hQ : S.filter (fun T => T.1.card = 1 ∧ T.2.card = 1) =
      (Finset.univ.powerset.filter fun t : Finset (Fin r) => t.card = 1) ×ˢ
        (Finset.univ.powerset.filter fun t : Finset (Fin r') => t.card = 1) := by
    ext ⟨t, t'⟩
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> rintro rfl <;> simp at h1 h2
  rw [hQ, Finset.sum_product, sum_card_one]
  simp only [sum_card_one (fun t' => ∫ ω, F (_, t') ω ∂μ)]
  rw [add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ T ∈ S.filter (fun T => ¬ (T.1.card = 1 ∧ T.2.card = 1)), ‖∫ ω, F T ω ∂μ‖ ≤
      (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * ((r + r' : ℕ) * (β ^ 3 + β ^ (r + r' + 3))) := fun T hT => by
    obtain ⟨hT, hn⟩ := Finset.mem_filter.mp hT
    obtain ⟨h1, h2, hM'⟩ := hmem T hT
    have c1 := Finset.card_pos.mpr h1
    have c2 := Finset.card_pos.mpr h2
    have hr1 := Finset.card_le_univ T.1
    have hr2 := Finset.card_le_univ T.2
    simp only [Fintype.card_fin] at hr1 hr2
    have h3 : 3 ≤ T.1.card + T.2.card := by omega
    refine (norm_integral_le_integral_norm _).trans ((hPM T hT).2.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hp := pow_le_two_ends hβ h3 (by omega : T.1.card + T.2.card ≤ r + r' + 3)
    have hc : ((T.1.card + T.2.card : ℕ) : ℝ) ≤ ((r + r' : ℕ) : ℝ) := by
      exact_mod_cast (by omega : T.1.card + T.2.card ≤ r + r')
    exact mul_le_mul hc hp (pow_nonneg hβ _) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcS : ((S.filter (fun T => ¬ (T.1.card = 1 ∧ T.2.card = 1))).card : ℝ) ≤ 2 ^ r * 2 ^ r' := by
    have h1 := Finset.card_filter_le S (fun T => ¬ (T.1.card = 1 ∧ T.2.card = 1))
    have h2 : S.card ≤ 2 ^ r * 2 ^ r' := by
      rw [Finset.card_product]
      refine Nat.mul_le_mul ?_ ?_ <;>
      · refine (Finset.card_filter_le _ _).trans ?_
        simp
    exact_mod_cast h1.trans h2
  have h0 : 0 ≤ (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * ((r + r' : ℕ) * (β ^ 3 + β ^ (r + r' + 3))) := by
    have := Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => norm_nonneg (c l)
    have := Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => norm_nonneg (c' l)
    positivity
  calc _ ≤ (2 ^ r * 2 ^ r' : ℝ) * ((∑ l, ‖c l‖) * (∑ l, ‖c' l‖) *
        ((r + r' : ℕ) * (β ^ 3 + β ^ (r + r' + 3)))) := mul_le_mul_of_nonneg_right hcS h0
    _ = _ := by ring

include hrep hrep' in
/-- **Cross first order.** -/
theorem cross_mean (p : Fin r) (q : Fin r')
    (hint : ∀ l l', Integrable (fun ω => bilinear (x l p) (Δ ω p) (y l p) *
      bilinear (x' l' q) (Δ' ω q) (y' l' q)) μ) :
    ∫ ω, posTr A (pw σ (Δ ω) {p}) * posTr A' (pw σ' (Δ' ω) {q}) ∂μ =
      ∑ l, ∑ l', c l * c' l' * ((∫ ω, bilinear (x l p) (Δ ω p) (y l p) *
        bilinear (x' l' q) (Δ' ω q) (y' l' q) ∂μ) *
          ((∏ i ∈ Finset.univ \ {p}, bilinear (x l i) (σ i) (y l i)) *
            ∏ i ∈ Finset.univ \ {q}, bilinear (x' l' i) (σ' i) (y' l' i))) := by
  simp only [posTr_pw hrep, posTr_pw hrep', Finset.prod_singleton, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun l' _ => by
    have := ((hint l l').const_mul (c l * c' l')).mul_const
      ((∏ i ∈ Finset.univ \ {p}, bilinear (x l i) (σ i) (y l i)) *
        ∏ i ∈ Finset.univ \ {q}, bilinear (x' l' i) (σ' i) (y' l' i))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_); simp only; ring]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun l' _ => by
    have := ((hint l l').const_mul (c l * c' l')).mul_const
      ((∏ i ∈ Finset.univ \ {p}, bilinear (x l i) (σ i) (y l i)) *
        ∏ i ∈ Finset.univ \ {q}, bilinear (x' l' i) (σ' i) (y' l' i))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_); simp only; ring]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [← integral_mul_const, ← integral_const_mul]
  congr 1; funext ω; ring

end BlockBand.SourceProcess.ContractingWords
