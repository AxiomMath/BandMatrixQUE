module

public import BlockBand.Transmission.SourceMixing.TraceCov
public import BlockBand.Transmission.SourceMixing.WordAlg
public import BlockBand.Transmission.PassiveCovariance.WordReplicaId

/-!
# Pointwise algebra of the one-step expansion of `E[𝒢·w(𝒢)]`

* `sum_G_wordFormDeriv`: `Σ_β G_{σβ} DΨ_β(E_{σρ}) = -Σ_j (Gα_j)_{σσ}(γ_j)_{ργ}`;
* `sum_wordForm_mul`: `Σ_β Ψ_β G_{ρβ} = (G w)_{ργ}`;
* `pointwise_family`: the sum over `β` and over a family of sites `σ(y)` of the replica
  integrand, as a self-energy term plus the crossed terms;
* `integrable_poly`: functions bounded by `K(1 + B)^r` are integrable (by the `moments` clause of
  the passive bounds).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem single_form {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (β γ : n) :
    star (Pi.single β (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single γ 1) = M β γ := by
  simp [dotProduct, mulVec, Pi.single_apply]

theorem mul_single_mul_apply' {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (i j β γ : n) : (A * Matrix.single i j (1 : ℂ) * B) β γ = A β i * B j γ := by
  simp only [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_mul, mul_ite, mul_one,
    mul_zero, zero_mul]
  simp [ite_and, Finset.sum_ite_eq]

/-- `Ψ_β = (w(G))_{βγ}` with `a = e_β`, `c = e_γ`. -/
theorem wordForm_single (Kh G : LayerMat W) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → LayerMat W) (β γ : LayerSite W .oneBlockOnePort) :
    wordForm Kh (Pi.single β 1) (Pi.single γ 1) wd D G = wordVal Kh G wd D β γ :=
  single_form _ β γ

theorem sum_G_wordFormDeriv (Kh G : LayerMat W) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → LayerMat W) (σ ρ γ : LayerSite W .oneBlockOnePort) :
    ∑ β, G σ β * wordFormDeriv Kh (Pi.single β 1) (Pi.single γ 1) wd D G (Matrix.single σ ρ 1) =
      -∑ j, (G * wordAlpha Kh G ℓ wd D j) σ σ * wordGamma Kh G ℓ wd D j ρ γ := by
  simp only [wordFormDeriv_apply, single_form, mul_single_mul_apply']
  simp only [Matrix.mul_apply, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun β _ => by ring

theorem sum_wordForm_mul (Kh G : LayerMat W) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → LayerMat W) (ρ γ : LayerSite W .oneBlockOnePort) :
    ∑ β, wordForm Kh (Pi.single β 1) (Pi.single γ 1) wd D G * G ρ β = (G * wordVal Kh G wd D) ρ γ := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [wordForm_single]; ring

/-- The replica integrand summed over `β` and a family of sites `σ`. -/
theorem pointwise_family (Kh G : LayerMat W) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → LayerMat W) (σ : Fin W → LayerSite W .oneBlockOnePort)
    (ρ γ : LayerSite W .oneBlockOnePort) (κ : ℂ) :
    ∑ β, ∑ y, κ * (G (σ y) β *
        wordFormDeriv Kh (Pi.single β 1) (Pi.single γ 1) wd D G (Matrix.single (σ y) ρ 1) -
        wordForm Kh (Pi.single β 1) (Pi.single γ 1) wd D G * (G (σ y) (σ y) * G ρ β)) =
      -(κ * ∑ y, G (σ y) (σ y)) * (G * wordVal Kh G wd D) ρ γ -
        ∑ j, (κ * ∑ y, (G * wordAlpha Kh G ℓ wd D j) (σ y) (σ y)) *
          wordGamma Kh G ℓ wd D j ρ γ := by
  rw [Finset.sum_comm]
  have h1 : ∀ y, ∑ β, κ * (G (σ y) β *
        wordFormDeriv Kh (Pi.single β 1) (Pi.single γ 1) wd D G (Matrix.single (σ y) ρ 1) -
        wordForm Kh (Pi.single β 1) (Pi.single γ 1) wd D G * (G (σ y) (σ y) * G ρ β)) =
      κ * (-∑ j, (G * wordAlpha Kh G ℓ wd D j) (σ y) (σ y) * wordGamma Kh G ℓ wd D j ρ γ) -
        κ * G (σ y) (σ y) * (G * wordVal Kh G wd D) ρ γ := fun y => by
    rw [← sum_G_wordFormDeriv, ← sum_wordForm_mul, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun β _ => by ring
  simp only [h1, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, mul_neg,
    Finset.sum_neg_distrib, neg_mul]
  rw [Finset.sum_comm (f := fun y j => κ * ((G * wordAlpha Kh G ℓ wd D j) (σ y) (σ y) *
    wordGamma Kh G ℓ wd D j ρ γ))]
  have e : ∀ j y, κ * ((G * wordAlpha Kh G ℓ wd D j) (σ y) (σ y) * wordGamma Kh G ℓ wd D j ρ γ) =
      κ * (G * wordAlpha Kh G ℓ wd D j) (σ y) (σ y) * wordGamma Kh G ℓ wd D j ρ γ :=
    fun _ _ => by ring
  simp only [e]
  ring

theorem sum_phys_eq (M : LayerMat W) : ∑ y, M (phys y) (phys y) = (W : ℂ) * blkTr M 0 := by
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  have hW : (W : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  rw [blkTr, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]
  simp [Matrix.trace, blkAt, siteOf]

theorem sum_port_eq (M : LayerMat W) : ∑ y, M (port y) (port y) = (W : ℂ) * blkTr M 1 := by
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  have hW : (W : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  rw [blkTr, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]
  simp [Matrix.trace, blkAt, siteOf]

/-- Integrability from a polynomial bound in `1 + B`, uniformly over passive inputs. -/
theorem integrable_poly (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (r : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (layerLaw W b .oneBlockOnePort) →
      ∀ K : ℝ, (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r) →
        Integrable F (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, h⟩ := memLp_two_of_poly hA hb0 hb h1 h2 (r + 1) (by omega)
  refine ⟨W₀, fun W hW X hX F hF K hK =>
    (h W hW X hX F hF (max K 0) fun ω => ?_).integrable one_le_two⟩
  have h1' := one_le_one_add_btFun b E X ω
  have h0 : 0 ≤ (1 + btFun b E X ω) ^ r := by positivity
  calc ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r := hK ω
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ r := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ (r + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1' (by omega)) (le_max_right _ _)

end BlockBand.Transmission.SourceMixing
