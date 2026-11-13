module

public import BlockBand.SourceProcess.ContractingWords.PosAbstract

/-!
# The abstract one-layer drift of one word

`drift_abstract`: with `Γ = Σ_l |c_l|`,
`|E posTr(σ+Δ) - posTr σ - Σ_p posTr(pw σ m {p}) - Σ_{p<q} Σ_k κ_k pairF(p,q,G_k,H_k)|
 ≤ Γ(2^r r(β³ + β^{r+3}) + r²(ε + μ₀²))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {A : Fin r → Matrix n n ℂ}
  {ι : Type} [Fintype ι] {c : ι → ℂ} {x y : ι → Fin r → n → ℂ}

omit [Fintype ι] in
theorem norm_prod_old_le (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
    {σ : Fin r → Matrix n n ℂ} (hσ : ∀ p, ‖σ p‖ ≤ 1) (l : ι) (s : Finset (Fin r)) :
    ‖∏ i ∈ s, bilinear (x l i) (σ i) (y l i)‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun p _ => ?_
  have h := norm_bilinear_le (x l p) (σ p) (y l p)
  have := (hxy l p).1; have := (hxy l p).2; have := hσ p
  have := vecNorm_nonneg (x l p); have := vecNorm_nonneg (y l p)
  calc _ ≤ vecNorm (x l p) * ‖σ p‖ * vecNorm (y l p) := h
    _ ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

variable (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
  (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
  {σ : Fin r → Matrix n n ℂ} {Δ : Ω → Fin r → Matrix n n ℂ} {M : ℕ} {β : ℝ}

include hrep hxy in
omit [IsProbabilityMeasure μ] in
/-- **One pair of slots.** -/
theorem pair_term (hσ : ∀ p, ‖σ p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β) {μ₀ : ℝ}
    (hm : ∀ p, ‖slotMean μ Δ p‖ ≤ μ₀) {p q : Fin r} (hpq : p ≠ q) (hM : 2 ≤ M)
    (κ : Fin 4 → ℂ) (G H : Fin 4 → Matrix n n ℂ) {ε : ℝ}
    (hcov : ∀ u v u' v' : n → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 → vecNorm u' ≤ 1 →
      vecNorm v' ≤ 1 →
      ‖∫ ω, bilinear u (Δ ω p) v * bilinear u' (Δ ω q) v' ∂μ -
          bilinear u (slotMean μ Δ p) v * bilinear u' (slotMean μ Δ q) v' -
          ∑ k, κ k * crossedTensor u v u' v' (G k) (H k)‖ ≤ ε) :
    ‖∫ ω, posTr A (pw σ (Δ ω) {p, q}) ∂μ - ∑ k, κ k * pairF A σ p q (G k) (H k)‖ ≤
      (∑ l, ‖c l‖) * (ε + μ₀ ^ 2) := by
  have hint : ∀ l, Integrable (fun ω => bilinear (x l p) (Δ ω p) (y l p) *
      bilinear (x l q) (Δ ω q) (y l q)) μ := fun l => by
    have hc : ({p, q} : Finset (Fin r)).card = 2 := Finset.card_pair hpq
    have h := (prod_moment {p, q} ⟨p, by simp⟩ (fun i ω => bilinear (x l i) (Δ ω i) (y l i))
      (fun i _ => (hΔ i _ _ (hxy l i).1 (hxy l i).2).1)
      (fun i _ => ((hΔ i _ _ (hxy l i).1 (hxy l i).2).2 _ (by omega) (by omega)).1)
      (fun i _ => ((hΔ i _ _ (hxy l i).1 (hxy l i).2).2 _ (by omega) (by omega)).2)).1
    simpa only [Finset.prod_pair hpq] using h
  rw [second_mean hrep hpq hint]
  set m := slotMean μ Δ
  set er : ι → ℂ := fun l => ∫ ω, bilinear (x l p) (Δ ω p) (y l p) *
      bilinear (x l q) (Δ ω q) (y l q) ∂μ - bilinear (x l p) (m p) (y l p) *
        bilinear (x l q) (m q) (y l q) -
      ∑ k, κ k * crossedTensor (x l p) (y l p) (x l q) (y l q) (G k) (H k)
  have hmean : posTr A (pw σ m {p, q}) = ∑ l, c l * ((bilinear (x l p) (m p) (y l p) *
      bilinear (x l q) (m q) (y l q)) *
        ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i)) := by
    rw [posTr_pw hrep, Finset.sum_congr rfl fun l _ => by rw [Finset.prod_pair hpq]]
  have hten : ∑ k, κ k * pairF A σ p q (G k) (H k) = ∑ l, c l *
      ((∑ k, κ k * crossedTensor (x l p) (y l p) (x l q) (y l q) (G k) (H k)) *
        ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i)) := by
    simp only [pairF, ← pair_units hrep σ hpq]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  have e : ∑ l, c l * ((∫ ω, bilinear (x l p) (Δ ω p) (y l p) *
        bilinear (x l q) (Δ ω q) (y l q) ∂μ) *
          ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i)) -
        ∑ k, κ k * pairF A σ p q (G k) (H k) =
      posTr A (pw σ m {p, q}) +
        ∑ l, c l * (er l * ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i)) := by
    rw [hmean, hten, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by simp only [er]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_posTr_pw_mean hrep hxy hσ hm {p, q}
  rw [Finset.card_pair hpq] at h1
  have h2 : ‖∑ l, c l * (er l * ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i))‖ ≤
      (∑ l, ‖c l‖) * ε := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hc : ‖er l‖ ≤ ε := hcov (x l p) (y l p) (x l q) (y l q) (hxy l p).1 (hxy l p).2
      (hxy l q).1 (hxy l q).2
    have h3 := norm_prod_old_le hxy hσ l (Finset.univ \ {p, q})
    calc _ ≤ ε * 1 := mul_le_mul hc h3 (norm_nonneg _) ((norm_nonneg _).trans hc)
      _ = ε := mul_one _
  calc _ ≤ (∑ l, ‖c l‖) * μ₀ ^ 2 + (∑ l, ‖c l‖) * ε := add_le_add h1 h2
    _ = _ := by ring

theorem double_sum_le {r : ℕ} (z : Fin r → Fin r → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p q, p ≠ q → ‖z p q‖ ≤ B) :
    ‖∑ p, ∑ q ∈ Finset.Ioi p, z p q‖ ≤ r ^ 2 * B := by
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _p : Fin r, (r : ℝ) * B := Finset.sum_le_sum fun p _ => by
        refine (norm_sum_le _ _).trans ?_
        calc _ ≤ ∑ _q ∈ Finset.Ioi p, B := Finset.sum_le_sum fun q hq =>
              hz p q (ne_of_lt (Finset.mem_Ioi.mp hq))
          _ = (Finset.Ioi p).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ r * B := by
              refine mul_le_mul_of_nonneg_right ?_ hB
              have := Finset.card_le_univ (Finset.Ioi p)
              simp only [Fintype.card_fin] at this
              exact_mod_cast this
    _ = r ^ 2 * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

include hrep hxy in
/-- **The abstract one-layer drift.** -/
theorem drift_abstract (hσ : ∀ p, ‖σ p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β) (hβ : 0 ≤ β)
    (hrM : r ≤ M) (hM2 : 2 ≤ M) (hent : ∀ p i j, Integrable (fun ω => Δ ω p i j) μ) {μ₀ : ℝ}
    (hm : ∀ p, ‖slotMean μ Δ p‖ ≤ μ₀) (κ : Fin r → Fin r → Fin 4 → ℂ)
    (G H : Fin r → Fin r → Fin 4 → Matrix n n ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcov : ∀ p q, p ≠ q → ∀ u v u' v' : n → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 →
      vecNorm u' ≤ 1 → vecNorm v' ≤ 1 →
      ‖∫ ω, bilinear u (Δ ω p) v * bilinear u' (Δ ω q) v' ∂μ -
          bilinear u (slotMean μ Δ p) v * bilinear u' (slotMean μ Δ q) v' -
          ∑ k, κ p q k * crossedTensor u v u' v' (G p q k) (H p q k)‖ ≤ ε) :
    ‖∫ ω, posTr A (σ + Δ ω) ∂μ - posTr A σ - ∑ p, posTr A (pw σ (slotMean μ Δ) {p}) -
        ∑ p, ∑ q ∈ Finset.Ioi p, ∑ k, κ p q k * pairF A σ p q (G p q k) (H p q k)‖ ≤
      (∑ l, ‖c l‖) * (2 ^ r * r * (β ^ 3 + β ^ (r + 3)) + r ^ 2 * (ε + μ₀ ^ 2)) := by
  obtain ⟨-, hD⟩ := drift_expand hrep hxy hσ hΔ hβ hrM
  rw [sum_card_one, sum_card_two] at hD
  have h1 : ∀ p, ∫ ω, posTr A (pw σ (Δ ω) {p}) ∂μ = posTr A (pw σ (slotMean μ Δ) {p}) :=
    fun p => first_mean hrep hent p
  simp only [h1] at hD
  have hΓ : 0 ≤ ∑ l, ‖c l‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ (∑ l, ‖c l‖) * (ε + μ₀ ^ 2) := by positivity
  have hP := double_sum_le (fun p q => ∫ ω, posTr A (pw σ (Δ ω) {p, q}) ∂μ -
      ∑ k, κ p q k * pairF A σ p q (G p q k) (H p q k)) hB fun p q hpq =>
    pair_term hrep hxy hσ hΔ hm hpq hM2 (κ p q) (G p q) (H p q) (hcov p q hpq)
  have e : ∫ ω, posTr A (σ + Δ ω) ∂μ - posTr A σ - ∑ p, posTr A (pw σ (slotMean μ Δ) {p}) -
        ∑ p, ∑ q ∈ Finset.Ioi p, ∑ k, κ p q k * pairF A σ p q (G p q k) (H p q k) =
      (∫ ω, posTr A (σ + Δ ω) ∂μ - posTr A σ - ∑ p, posTr A (pw σ (slotMean μ Δ) {p}) -
        ∑ p, ∑ q ∈ Finset.Ioi p, ∫ ω, posTr A (pw σ (Δ ω) {p, q}) ∂μ) +
      ∑ p, ∑ q ∈ Finset.Ioi p, (∫ ω, posTr A (pw σ (Δ ω) {p, q}) ∂μ -
        ∑ k, κ p q k * pairF A σ p q (G p q k) (H p q k)) := by
    simp only [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ (∑ l, ‖c l‖) * (2 ^ r * r * (β ^ 3 + β ^ (r + 3))) +
        r ^ 2 * ((∑ l, ‖c l‖) * (ε + μ₀ ^ 2)) := add_le_add hD hP
    _ = _ := by ring

end BlockBand.SourceProcess.ContractingWords
