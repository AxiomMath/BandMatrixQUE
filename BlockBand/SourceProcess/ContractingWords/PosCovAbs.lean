module

public import BlockBand.SourceProcess.ContractingWords.PosDriftAbs

/-!
# The abstract one-layer covariance of two words

`cov_abstract`: for two words in positional cut form with separators `σ + Δ`, `‖σ_p‖ ≤ 1`, and
slot fluctuations `Δ` with bounded moments, the covariance of the increments
`posTr A (σ + Δ) - posTr A σ` is the sum of the cross functionals `crossF` of the slot
covariances, up to an explicit error.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {n : Type} [Fintype n] [DecidableEq n] {r r' : ℕ} {A : Fin r → Matrix n n ℂ}
  {A' : Fin r' → Matrix n n ℂ} {ι ι' : Type} [Fintype ι] [Fintype ι'] {c : ι → ℂ} {c' : ι' → ℂ}
  {x y : ι → Fin r → n → ℂ} {x' y' : ι' → Fin r' → n → ℂ}

/-- The contracted cross functional of a slot `p` of one word and `q` of the other. -/
def crossF (A σ : Fin r → Matrix n n ℂ) (A' σ' : Fin r' → Matrix n n ℂ) (p : Fin r) (q : Fin r')
    (G H : Matrix n n ℂ) : ℂ :=
  ∑ c₁, ∑ b, ∑ a, ∑ d, G a d * H c₁ b *
    (posTr A (pw σ (units1 p a b) {p}) * posTr A' (pw σ' (units1 q c₁ d) {q}))

theorem integrable_mul_of_sq {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) μ) : Integrable (fun ω => f ω * g ω) μ := by
  refine (hf2.add hg2).mono' (hf.mul hg) (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  show ‖f ω‖ * ‖g ω‖ ≤ ‖f ω‖ ^ 2 + ‖g ω‖ ^ 2
  nlinarith [norm_nonneg (f ω), norm_nonneg (g ω), sq_nonneg (‖f ω‖ - ‖g ω‖)]

variable (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
  (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1)
  (hrep' : ∀ T, posTr A' T = ∑ l, c' l * ∏ p, bilinear (x' l p) (T p) (y' l p))
  (hxy' : ∀ l p, vecNorm (x' l p) ≤ 1 ∧ vecNorm (y' l p) ≤ 1)
  {σ : Fin r → Matrix n n ℂ} {σ' : Fin r' → Matrix n n ℂ} {Δ : Ω → Fin r → Matrix n n ℂ}
  {Δ' : Ω → Fin r' → Matrix n n ℂ} {M : ℕ} {β : ℝ}

include hrep hxy hrep' hxy' in
/-- **One cross pair of slots.** -/
theorem cross_term (hσ : ∀ p, ‖σ p‖ ≤ 1) (hσ' : ∀ p, ‖σ' p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β)
    (hΔ' : SlotMoments μ Δ' M β) (hM2 : 2 ≤ M) {μ₀ : ℝ} (hm : ∀ p, ‖slotMean μ Δ p‖ ≤ μ₀)
    (hm' : ∀ q, ‖slotMean μ Δ' q‖ ≤ μ₀) (p : Fin r) (q : Fin r') (κ : Fin 4 → ℂ)
    (G H : Fin 4 → Matrix n n ℂ) {ε : ℝ}
    (hcov : ∀ u v u' v' : n → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 → vecNorm u' ≤ 1 →
      vecNorm v' ≤ 1 →
      ‖∫ ω, bilinear u (Δ ω p) v * bilinear u' (Δ' ω q) v' ∂μ -
          bilinear u (slotMean μ Δ p) v * bilinear u' (slotMean μ Δ' q) v' -
          ∑ k, κ k * crossedTensor u v u' v' (G k) (H k)‖ ≤ ε) :
    ‖∫ ω, posTr A (pw σ (Δ ω) {p}) * posTr A' (pw σ' (Δ' ω) {q}) ∂μ -
        ∑ k, κ k * crossF A σ A' σ' p q (G k) (H k)‖ ≤
      (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (ε + μ₀ ^ 2) := by
  have hint : ∀ l l', Integrable (fun ω => bilinear (x l p) (Δ ω p) (y l p) *
      bilinear (x' l' q) (Δ' ω q) (y' l' q)) μ := fun l l' =>
    integrable_mul_of_sq (hΔ p _ _ (hxy l p).1 (hxy l p).2).1
      (hΔ' q _ _ (hxy' l' q).1 (hxy' l' q).2).1
      ((hΔ p _ _ (hxy l p).1 (hxy l p).2).2 2 (by norm_num) hM2).1
      ((hΔ' q _ _ (hxy' l' q).1 (hxy' l' q).2).2 2 (by norm_num) hM2).1
  rw [cross_mean hrep hrep' p q hint]
  set m := slotMean μ Δ
  set m' := slotMean μ Δ'
  set K : ι → ι' → ℂ := fun l l' => (∏ i ∈ Finset.univ \ {p}, bilinear (x l i) (σ i) (y l i)) *
    ∏ i ∈ Finset.univ \ {q}, bilinear (x' l' i) (σ' i) (y' l' i)
  set er : ι → ι' → ℂ := fun l l' => ∫ ω, bilinear (x l p) (Δ ω p) (y l p) *
      bilinear (x' l' q) (Δ' ω q) (y' l' q) ∂μ - bilinear (x l p) (m p) (y l p) *
        bilinear (x' l' q) (m' q) (y' l' q) -
      ∑ k, κ k * crossedTensor (x l p) (y l p) (x' l' q) (y' l' q) (G k) (H k)
  have hmean : posTr A (pw σ m {p}) * posTr A' (pw σ' m' {q}) = ∑ l, ∑ l', c l * c' l' *
      ((bilinear (x l p) (m p) (y l p) * bilinear (x' l' q) (m' q) (y' l' q)) * K l l') := by
    rw [posTr_pw hrep, posTr_pw hrep', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    simp only [K, Finset.prod_singleton]; ring
  have hten : ∑ k, κ k * crossF A σ A' σ' p q (G k) (H k) = ∑ l, ∑ l', c l * c' l' *
      ((∑ k, κ k * crossedTensor (x l p) (y l p) (x' l' q) (y' l' q) (G k) (H k)) * K l l') := by
    simp only [crossF, ← cross_units hrep hrep' σ σ' p q]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun k _ => by simp only [K]; ring
  have e : ∑ l, ∑ l', c l * c' l' * ((∫ ω, bilinear (x l p) (Δ ω p) (y l p) *
        bilinear (x' l' q) (Δ' ω q) (y' l' q) ∂μ) * K l l') -
        ∑ k, κ k * crossF A σ A' σ' p q (G k) (H k) =
      posTr A (pw σ m {p}) * posTr A' (pw σ' m' {q}) +
        ∑ l, ∑ l', c l * c' l' * (er l l' * K l l') := by
    rw [hmean, hten, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l' _ => by simp only [er]; ring
  simp only [K] at e
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖posTr A (pw σ m {p}) * posTr A' (pw σ' m' {q})‖ ≤
      (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * μ₀ ^ 2 := by
    rw [norm_mul]
    have a1 := norm_posTr_pw_mean hrep hxy hσ hm {p}
    have a2 := norm_posTr_pw_mean hrep' hxy' hσ' hm' {q}
    rw [Finset.card_singleton, pow_one] at a1 a2
    calc _ ≤ ((∑ l, ‖c l‖) * μ₀) * ((∑ l, ‖c' l‖) * μ₀) :=
          mul_le_mul a1 a2 (norm_nonneg _) ((norm_nonneg _).trans a1)
      _ = _ := by ring
  have h2 : ‖∑ l, ∑ l', c l * c' l' * (er l l' * K l l')‖ ≤
      (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * ε := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l' _ => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hc : ‖er l l'‖ ≤ ε := hcov (x l p) (y l p) (x' l' q) (y' l' q) (hxy l p).1 (hxy l p).2
      (hxy' l' q).1 (hxy' l' q).2
    have k1 := norm_prod_old_le hxy hσ l (Finset.univ \ {p})
    have k2 := norm_prod_old_le hxy' hσ' l' (Finset.univ \ {q})
    have hk : ‖K l l'‖ ≤ 1 := by
      simp only [K, norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul k1 k2 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    have := mul_le_mul hc hk (norm_nonneg _) ((norm_nonneg _).trans hc)
    simp only [K, norm_mul] at hk this
    calc _ ≤ ‖c l‖ * ‖c' l'‖ * (ε * 1) := by gcongr
      _ = _ := by ring
  calc _ ≤ (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * μ₀ ^ 2 + (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * ε :=
        add_le_add h1 h2
    _ = _ := by ring

include hrep hxy hrep' hxy' in
/-- **The abstract one-layer covariance.** -/
theorem cov_abstract (hσ : ∀ p, ‖σ p‖ ≤ 1) (hσ' : ∀ p, ‖σ' p‖ ≤ 1) (hΔ : SlotMoments μ Δ M β)
    (hΔ' : SlotMoments μ Δ' M β) (hβ : 0 ≤ β) (hM : r + r' ≤ M) (hM2 : 2 ≤ M) {μ₀ : ℝ}
    (hm : ∀ p, ‖slotMean μ Δ p‖ ≤ μ₀) (hm' : ∀ q, ‖slotMean μ Δ' q‖ ≤ μ₀)
    (κ : Fin r → Fin r' → Fin 4 → ℂ) (G H : Fin r → Fin r' → Fin 4 → Matrix n n ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcov : ∀ p q, ∀ u v u' v' : n → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 → vecNorm u' ≤ 1 →
      vecNorm v' ≤ 1 →
      ‖∫ ω, bilinear u (Δ ω p) v * bilinear u' (Δ' ω q) v' ∂μ -
          bilinear u (slotMean μ Δ p) v * bilinear u' (slotMean μ Δ' q) v' -
          ∑ k, κ p q k * crossedTensor u v u' v' (G p q k) (H p q k)‖ ≤ ε) :
    ‖∫ ω, (posTr A (σ + Δ ω) - posTr A σ) * (posTr A' (σ' + Δ' ω) - posTr A' σ') ∂μ -
        ∑ p, ∑ q, ∑ k, κ p q k * crossF A σ A' σ' p q (G p q k) (H p q k)‖ ≤
      (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (2 ^ r * 2 ^ r' * ((r + r' : ℕ) * (β ^ 3 + β ^ (r + r' + 3))) +
        r * r' * (ε + μ₀ ^ 2)) := by
  have hD := cov_expand hrep hxy hrep' hxy' hσ hσ' hΔ hΔ' hβ hM
  have hΓ : 0 ≤ (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) := mul_nonneg
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hB : 0 ≤ (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (ε + μ₀ ^ 2) := by positivity
  have hP : ‖∑ p, ∑ q, (∫ ω, posTr A (pw σ (Δ ω) {p}) * posTr A' (pw σ' (Δ' ω) {q}) ∂μ -
      ∑ k, κ p q k * crossF A σ A' σ' p q (G p q k) (H p q k))‖ ≤
        r * r' * ((∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (ε + μ₀ ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _p : Fin r, (r' : ℝ) * ((∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (ε + μ₀ ^ 2)) :=
          Finset.sum_le_sum fun p _ => by
            refine (norm_sum_le _ _).trans ?_
            calc _ ≤ ∑ _q : Fin r', (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (ε + μ₀ ^ 2) :=
                  Finset.sum_le_sum fun q _ => cross_term hrep hxy hrep' hxy' hσ hσ' hΔ hΔ' hM2
                    hm hm' p q (κ p q) (G p q) (H p q) (hcov p q)
              _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have e : ∫ ω, (posTr A (σ + Δ ω) - posTr A σ) * (posTr A' (σ' + Δ' ω) - posTr A' σ') ∂μ -
        ∑ p, ∑ q, ∑ k, κ p q k * crossF A σ A' σ' p q (G p q k) (H p q k) =
      (∫ ω, (posTr A (σ + Δ ω) - posTr A σ) * (posTr A' (σ' + Δ' ω) - posTr A' σ') ∂μ -
        ∑ p, ∑ q, ∫ ω, posTr A (pw σ (Δ ω) {p}) * posTr A' (pw σ' (Δ' ω) {q}) ∂μ) +
      ∑ p, ∑ q, (∫ ω, posTr A (pw σ (Δ ω) {p}) * posTr A' (pw σ' (Δ' ω) {q}) ∂μ -
        ∑ k, κ p q k * crossF A σ A' σ' p q (G p q k) (H p q k)) := by
    simp only [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ (∑ l, ‖c l‖) * (∑ l, ‖c' l‖) *
        (2 ^ r * 2 ^ r' * ((r + r' : ℕ) * (β ^ 3 + β ^ (r + r' + 3)))) +
        r * r' * ((∑ l, ‖c l‖) * (∑ l, ‖c' l‖) * (ε + μ₀ ^ 2)) := add_le_add hD hP
    _ = _ := by ring

end BlockBand.SourceProcess.ContractingWords
