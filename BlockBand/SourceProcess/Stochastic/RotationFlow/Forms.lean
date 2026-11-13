module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Algebra
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Quadratic forms of the rotation–damping flow and their Itô drifts

Matrices carry the Frobenius norm. For one coefficient value `r` (symmetric, `≥ 0`), `κ ≥ 0`,
`A = rotationDrift r κ`, `Σ_α = rotationNoise r α`, a matrix `Y` and a real scalar `λ`
(the radial truncation factor; `λ = 1` for the flow itself):

* `entryForm k j (X, Y) = Re(conj X_kj · Y_kj)` (real bilinear), `entryForm k j Y Y = |Y_kj|²`;
* `entryForm_drift`, `entryForm_noise`: the product-rule drift of `|Y_kj|²` along
  `dY = λAY dt + ∑ λΣ_αY dW^α` is `2λ d_k |Y_kj|² + λ² ∑_{m≠k} r_km |Y_mj|²`
  (`d_k = -½(∑_{m≠k} r_km + κ_k)`); for `λ = 1` this is `∑_l L_kl |Y_lj|²`, `L = massGenerator`
  (`entry_drift_eq_massGenerator`);
* `frob_drift_nonpos`: the drift of `‖Y‖²` is `≤ 0` for `0 ≤ λ ≤ 1`;
* `frob_diffusion_eq_zero`: the diffusion of `‖Y‖²` vanishes (skew-Hermitian noise).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open Matrix BlockBand.Internal.Contracts.TransmissionFlow
open BlockBand.SourceProcess.Stochastic.SourceSDE
open scoped BigOperators

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ}

/-- `(X, Y) ↦ Re(conj X_kj · Y_kj)` as a continuous real-bilinear form. -/
def entryForm (k j : Fin N) :=
  toCLM₂ (F₁ := Matrix (Fin N) (Fin N) ℂ) (F₂ := Matrix (Fin N) (Fin N) ℂ) (F₃ := ℝ)
    (LinearMap.mk₂ ℝ (fun X Y => (star (X k j) * Y k j).re)
    (fun _ _ _ => by simp only [Matrix.add_apply, star_add, add_mul, Complex.add_re])
    (fun _ _ _ => by
      simp only [Matrix.smul_apply, star_smul, star_trivial, smul_mul_assoc, Complex.smul_re])
    (fun _ _ _ => by simp only [Matrix.add_apply, mul_add, Complex.add_re])
    (fun _ _ _ => by simp only [Matrix.smul_apply, mul_smul_comm, Complex.smul_re]))

theorem entryForm_apply (k j : Fin N) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    entryForm k j X Y = (star (X k j) * Y k j).re := rfl

theorem entryForm_self (k j : Fin N) (X : Matrix (Fin N) (Fin N) ℂ) :
    entryForm k j X X = ‖X k j‖ ^ 2 := by
  rw [entryForm_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

theorem reInner_eq_sum (X Y : Matrix (Fin N) (Fin N) ℂ) :
    reInner X Y = ∑ k, ∑ j, entryForm k j X Y := by
  rw [reInner_apply, Matrix.trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rfl

theorem norm_sq_eq_sum (X : Matrix (Fin N) (Fin N) ℂ) : ‖X‖ ^ 2 = ∑ k, ∑ j, ‖X k j‖ ^ 2 := by
  rw [← reInner_self, reInner_eq_sum]
  simp only [entryForm_self]

theorem norm_entry_le (X : Matrix (Fin N) (Fin N) ℂ) (k j : Fin N) : ‖X k j‖ ≤ ‖X‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_eq_sum]
  refine (Finset.single_le_sum (f := fun j' => ‖X k j'‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun k' => ∑ j', ‖X k' j'‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)

/-- The diagonal coefficient `d_k = -½(∑_{m≠k} r_km + κ_k)`. -/
def driftDiag (r : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (k : Fin N) : ℝ :=
  -(1 / 2 : ℝ) * ((∑ m ∈ Finset.univ.erase k, r k m) + κ k)

theorem entryForm_drift (r : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (lam : ℝ)
    (Y : Matrix (Fin N) (Fin N) ℂ) (k j : Fin N) :
    entryForm k j (lam • (rotationDrift r κ * Y)) Y + entryForm k j Y (lam • (rotationDrift r κ * Y))
      = 2 * lam * driftDiag r κ k * ‖Y k j‖ ^ 2 := by
  simp only [map_smul, _root_.smul_apply, smul_eq_mul, entryForm_apply,
    rotationDrift_mul_apply, driftDiag, star_mul', Complex.star_def, Complex.conj_ofReal]
  have h1 : (((-(1 / 2 : ℝ)) * ((∑ m ∈ Finset.univ.erase k, r k m) + κ k) : ℝ) : ℂ) *
      (starRingEnd ℂ) (Y k j) * Y k j = ((((-(1 / 2 : ℝ)) * ((∑ m ∈ Finset.univ.erase k, r k m)
        + κ k)) * ‖Y k j‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.conj_mul']
    push_cast
    ring
  have h2 : (starRingEnd ℂ) (Y k j) * ((((-(1 / 2 : ℝ)) * ((∑ m ∈ Finset.univ.erase k, r k m) +
      κ k) : ℝ) : ℂ) * Y k j) = ((((-(1 / 2 : ℝ)) * ((∑ m ∈ Finset.univ.erase k, r k m) + κ k)) *
        ‖Y k j‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  rw [h1, h2, Complex.ofReal_re]
  ring

theorem entryForm_noise (r : Fin N → Fin N → ℝ) (hs : ∀ k l, r k l = r l k)
    (hr : ∀ k l, 0 ≤ r k l) (lam : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ) (k j : Fin N) :
    ∑ α : (Fin N × Fin N) × Fin 2,
        entryForm k j (lam • (rotationNoise r α * Y)) (lam • (rotationNoise r α * Y)) =
      lam ^ 2 * ∑ m ∈ Finset.univ.erase k, r k m * ‖Y m j‖ ^ 2 := by
  simp only [entryForm_self, Matrix.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← Finset.mul_sum, sum_norm_sq_rotationNoise_mul_apply r hs hr]

/-- **Entry drift** (`λ = 1`) is the mass generator acting on the row index. -/
theorem entry_drift_eq_massGenerator (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (x : ℝ)
    (hs : ∀ k l, r x k l = r x l k) (hr : ∀ k l, 0 ≤ r x k l) (Y : Matrix (Fin N) (Fin N) ℂ)
    (k j : Fin N) :
    entryForm k j (rotationDrift (r x) (κ x) * Y) Y + entryForm k j Y (rotationDrift (r x) (κ x) * Y)
        + ∑ α, entryForm k j (rotationNoise (r x) α * Y) (rotationNoise (r x) α * Y) =
      ∑ l, massGenerator r κ x k l * ‖Y l j‖ ^ 2 := by
  have h1 := entryForm_drift (r x) (κ x) 1 Y k j
  have h2 := entryForm_noise (r x) hs hr 1 Y k j
  simp only [one_smul] at h1 h2
  rw [h1, h2, sum_massGenerator_mul, driftDiag]
  ring

/-- `∑_k ∑_{m≠k} r_km f_m = ∑_m (∑_{k≠m} r_mk) f_m` for symmetric `r`. -/
theorem sum_erase_swap (r : Fin N → Fin N → ℝ) (hs : ∀ k l, r k l = r l k) (f : Fin N → ℝ) :
    ∑ k, ∑ m ∈ Finset.univ.erase k, r k m * f m =
      ∑ m, (∑ k ∈ Finset.univ.erase m, r m k) * f m := by
  have h : ∀ k, ∑ m ∈ Finset.univ.erase k, r k m * f m = ∑ m, r k m * f m - r k k * f k :=
    fun k => by rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]; ring
  have h' : ∀ m, (∑ k ∈ Finset.univ.erase m, r m k) * f m = (∑ k, r m k) * f m - r m m * f m :=
    fun m => by rw [← Finset.sum_erase_add _ _ (Finset.mem_univ m)]; ring
  simp only [h, h', Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [hs]

/-- The row sum `R_k = ∑_{m≠k} r_km`. -/
def rowSum (r : Fin N → Fin N → ℝ) (k : Fin N) : ℝ := ∑ m ∈ Finset.univ.erase k, r k m

/-- The Itô drift of `‖Y‖²` in diagonal form. -/
theorem frob_drift_eq (r : Fin N → Fin N → ℝ) (hs : ∀ k l, r k l = r l k)
    (hr : ∀ k l, 0 ≤ r k l) (κ : Fin N → ℝ) (lam : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ) :
    reInner (lam • (rotationDrift r κ * Y)) Y + reInner Y (lam • (rotationDrift r κ * Y)) +
      ∑ α, reInner (lam • (rotationNoise r α * Y)) (lam • (rotationNoise r α * Y)) =
      ∑ k, ∑ j, (2 * lam * driftDiag r κ k + lam ^ 2 * rowSum r k) * ‖Y k j‖ ^ 2 := by
  have hnoise : ∑ α, reInner (lam • (rotationNoise r α * Y)) (lam • (rotationNoise r α * Y)) =
      ∑ k, ∑ j, lam ^ 2 * ∑ m ∈ Finset.univ.erase k, r k m * ‖Y m j‖ ^ 2 := by
    simp only [reInner_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => entryForm_noise r hs hr lam Y k j
  have hdrift : reInner (lam • (rotationDrift r κ * Y)) Y +
      reInner Y (lam • (rotationDrift r κ * Y)) =
      ∑ k, ∑ j, 2 * lam * driftDiag r κ k * ‖Y k j‖ ^ 2 := by
    simp only [reInner_eq_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
      entryForm_drift r κ lam Y k j
  have hswap : ∑ k, ∑ j, lam ^ 2 * ∑ m ∈ Finset.univ.erase k, r k m * ‖Y m j‖ ^ 2 =
      ∑ k, ∑ j, lam ^ 2 * rowSum r k * ‖Y k j‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun k j => lam ^ 2 * rowSum r k * ‖Y k j‖ ^ 2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Finset.mul_sum]
    rw [sum_erase_swap r hs (fun m => ‖Y m j‖ ^ 2)]
    simp only [rowSum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro m _
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hdrift, hnoise, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Contraction drift**: the Itô drift of `‖Y‖²` is nonpositive for `0 ≤ λ ≤ 1`. -/
theorem frob_drift_nonpos (r : Fin N → Fin N → ℝ) (hs : ∀ k l, r k l = r l k)
    (hr : ∀ k l, 0 ≤ r k l) (κ : Fin N → ℝ) (hκ : ∀ k, 0 ≤ κ k) {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (Y : Matrix (Fin N) (Fin N) ℂ) :
    reInner (lam • (rotationDrift r κ * Y)) Y + reInner Y (lam • (rotationDrift r κ * Y)) +
      ∑ α, reInner (lam • (rotationNoise r α * Y)) (lam • (rotationNoise r α * Y)) ≤ 0 := by
  rw [frob_drift_eq r hs hr κ lam Y]
  refine Finset.sum_nonpos fun k _ => Finset.sum_nonpos fun j _ => ?_
  refine mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  have hR : 0 ≤ rowSum r k := Finset.sum_nonneg fun m _ => hr k m
  have e : 2 * lam * driftDiag r κ k + lam ^ 2 * rowSum r k =
      -(lam * κ k) - lam * (1 - lam) * rowSum r k := by
    simp only [driftDiag, rowSum]
    ring
  rw [e]
  have := mul_nonneg h0 (hκ k)
  have := mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) hR
  linarith

/-- **Contraction diffusion**: the Itô diffusion of `‖Y‖²` vanishes. -/
theorem frob_diffusion_eq_zero (r : Fin N → Fin N → ℝ) (lam : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ)
    (α : (Fin N × Fin N) × Fin 2) :
    reInner (lam • (rotationNoise r α * Y)) Y + reInner Y (lam • (rotationNoise r α * Y)) = 0 := by
  simp only [map_smul, _root_.smul_apply, smul_eq_mul, reInner_apply, conjTranspose_mul,
    rotationNoise_conjTranspose, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, trace_neg,
    Complex.neg_re]
  ring

end BlockBand.SourceProcess.Stochastic.RotationFlow
