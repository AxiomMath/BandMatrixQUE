module

public import Mathlib

/-!
# Exact scalar phase resolution (deterministic core)

We prove the phase-resolution identity `(1/(2π)) ∫₀^{2π} A_θ A_θᴴ dθ = I` for a scattering matrix
`S` with `S Sᴴ = I` and invertible transmission, where the far port is closed by a phase `e^{iθ}`.

## Setting

`ι` is an arbitrary finite type with decidable equality (in the application
`ι = Fin W`). A scattering matrix is `S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ`,
port `0` = near, port `1` = far, with blocks
`r = S₀₀`, `t' = S₀₁`, `t = S₁₀` (`transmission S`, near incoming → far
outgoing) and `r' = S₁₁` (`farReflection S`). The far port is closed by the
scalar unitary `e^{iθ} I` (`phase θ = exp(θ i)`), and

* `phaseGamma r' t θ = Γ_θ = (I - e^{iθ} r')⁻¹ e^{iθ} t`,
* `phaseA r' t θ = A_θ = [I ; Γ_θ]` (a `(Fin 2 × ι) × ι` matrix: block row `0`
  is `I`, block row `1` is `Γ_θ`),
* `phaseIntegral F` is the *unnormalised* entrywise integral
  `(∫₀^{2π} F(θ) dθ)ᵢⱼ = ∫ θ in 0..2π, F θ i j` (Lebesgue measure,
  `intervalIntegral`).

## Results (for every finite `ι`, every `S`, with the stated hypotheses)

Hypotheses: `S * Sᴴ = 1` (only the far block row of this identity is used)
and `IsUnit (transmission S).det` (equivalently `t tᴴ` positive definite,
`isUnit_det_of_posDef`). No normality of `r'` is assumed.

* `transmission_mul_add_farReflection_mul`: `t tᴴ + r' r'ᴴ = I`.
* `exists_contraction_of_coisometry`, `strict_contraction_of_coisometry`,
  `l2_opNorm_lt_one_of_coisometry`: `‖r'ᴴ v‖² ≤ c ‖v‖²` with a uniform
  `0 ≤ c < 1`, hence `‖r'ᴴ v‖ < ‖v‖` for `v ≠ 0` and `‖r'‖ < 1` in the
  `ℓ²` operator norm (`Matrix.Norms.L2Operator`); `tendsto_pow_of_coisometry`:
  `r'ⁿ → 0`.
* `det_one_sub_smul_ne_zero`: `I - z r'` is invertible for every `|z| = 1`,
  so `Γ_θ` is an inverse for every real `θ`; `continuous_phaseGamma`.
* `phaseIntegral_phaseGamma`: `∫₀^{2π} Γ_θ dθ = 0`.
* `phaseIntegral_phaseGamma_mul_conjTranspose`: `∫₀^{2π} Γ_θ Γ_θᴴ dθ = 2π I`.
* `phaseIntegral_phaseA`: `∫₀^{2π} A_θ A_θᴴ dθ = 2π I_{2W}`.
* `phase_resolution_average` (main, `ι = Fin W`) and
  `phase_resolution_average_general` (any finite `ι`): for all `x y`,
  `(1/(2π)) ∫₀^{2π} (A_θ A_θᴴ) x y dθ = (1 : Matrix _ _ ℂ) x y`, i.e.
  the phase-resolution identity; `phase_resolution_average_of_posDef` takes
  `t tᴴ ≻ 0` instead of `det t ≠ 0`.
* `clock_after_closure`, `clock_after_closure_normSq`: for any
  `U : Matrix κ (Fin 2 × ι) ℂ`, `Y = Uᴴ U` and any `g`,
  `‖U (A g)‖² = gᴴ (Aᴴ Y A) g` (pure algebra, any `A`).

## Method

Instead of a Neumann series expansion of `Γ_θ`, we avoid series and
interchange of limits: the fixed-point identity `Γ_θ = e^{iθ}(t + r' Γ_θ)`
gives, for the Fourier moments `G_k = ∫ e^{ikθ} Γ_θ dθ`, the recursion
`G_k = r' G_{k+1}` (since `∫ e^{imθ} = 0`, `m ≥ 1`), so `G_0 = r'ⁿ G_n` with
`|(G_n)ᵢⱼ| ≤ ∫ |(Γ_θ)ᵢⱼ| dθ` uniformly in `n`; `r'ⁿ → 0` forces `G_0 = 0`.
Using `|e^{iθ}| = 1`, `X = ∫ Γ Γᴴ` satisfies `X = 2π t tᴴ + r' X r'ᴴ`
(the cross terms are `r' G_0 tᴴ` and its adjoint), hence
`Y = X/(2π) - I` satisfies `Y = r' Y r'ᴴ = r'ⁿ Y (r'ⁿ)ᴴ → 0`. The decay
`r'ⁿ → 0` comes from `‖r'ᴴ v‖² = ‖v‖² - ‖tᴴ v‖²` and the Frobenius bound
`‖v‖² ≤ (‖(tᴴ)⁻¹‖²_F + 1) ‖tᴴ v‖²`.

## Scope

This is the deterministic core only. For the finite Gaussian path the
identity holds almost surely; the almost-sure unitarity and invertibility of
the finite-path transmission `t` enter here only as hypotheses and are proved
in `negativeClock_ae_scattering`. The scattering equations (that the full
incoming vector is `A_θ g`, and the interior solution is `U A_θ g`) are not
derived here; `clock_after_closure` is the algebraic identity used once they
are known.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open Matrix Filter Topology Real
open scoped ComplexConjugate

namespace BlockBand.Endpoints.Clock

section VectorNorm

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean norm `‖v‖² = ∑ᵢ |vᵢ|²` of a complex vector. -/
def vecNormSq (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem vecNormSq_nonneg (v : ι → ℂ) : 0 ≤ vecNormSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `vᴴ v = ‖v‖²`. -/
theorem star_dotProduct_self_eq (v : ι → ℂ) : star v ⬝ᵥ v = (vecNormSq v : ℂ) := by
  simp only [dotProduct, vecNormSq, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using Complex.conj_mul' (v i)

theorem vecNormSq_eq_zero_iff (v : ι → ℂ) : vecNormSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).1 h
    funext i
    simpa using this i (Finset.mem_univ _)
  · rintro rfl; simp [vecNormSq]

theorem norm_sq_le_vecNormSq (v : ι → ℂ) (i : ι) : ‖v i‖ ^ 2 ≤ vecNormSq v :=
  Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem vecNormSq_smul (c : ℂ) (v : ι → ℂ) : vecNormSq (c • v) = ‖c‖ ^ 2 * vecNormSq v := by
  simp [vecNormSq, Finset.mul_sum, mul_pow]

/-- `‖Bᴴ v‖² = vᴴ (B Bᴴ) v`. -/
theorem vecNormSq_conjTranspose_mulVec (B : Matrix ι ι ℂ) (v : ι → ℂ) :
    (vecNormSq (Bᴴ *ᵥ v) : ℂ) = star v ⬝ᵥ ((B * Bᴴ) *ᵥ v) := by
  rw [← star_dotProduct_self_eq, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec,
    mulVec_mulVec]

/-- Frobenius bound `‖B w‖² ≤ (∑ᵢⱼ |Bᵢⱼ|²) ‖w‖²`. -/
theorem vecNormSq_mulVec_le (B : Matrix ι ι ℂ) (w : ι → ℂ) :
    vecNormSq (B *ᵥ w) ≤ (∑ i, ∑ j, ‖B i j‖ ^ 2) * vecNormSq w := by
  unfold vecNormSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(B *ᵥ w) i‖ ≤ ∑ j, ‖B i j‖ * ‖w j‖ := by
    simp only [mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  calc ‖(B *ᵥ w) i‖ ^ 2 ≤ (∑ j, ‖B i j‖ * ‖w j‖) ^ 2 := by
        gcongr
    _ ≤ (∑ j, ‖B i j‖ ^ 2) * ∑ j, ‖w j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end VectorNorm

section Contraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pythagoras for a co-isometric block row `[t r']`: if `t tᴴ + r' r'ᴴ = I` then
`‖tᴴ v‖² + ‖r'ᴴ v‖² = ‖v‖²` for every `v`. -/
theorem vecNormSq_add_of_coisometry (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1)
    (v : ι → ℂ) : vecNormSq (tᴴ *ᵥ v) + vecNormSq (r'ᴴ *ᵥ v) = vecNormSq v := by
  apply Complex.ofReal_injective
  push_cast
  rw [vecNormSq_conjTranspose_mulVec, vecNormSq_conjTranspose_mulVec, ← star_dotProduct_self_eq,
    ← dotProduct_add, ← add_mulVec, h, one_mulVec]

/-- Uniform strict contraction: if `t tᴴ + r' r'ᴴ = I` and `det t ≠ 0`, there is
`0 ≤ c < 1` with `‖r'ᴴ v‖² ≤ c ‖v‖²` for every `v`. -/
theorem exists_contraction_of_coisometry (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1)
    (ht : IsUnit t.det) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ v : ι → ℂ, vecNormSq (r'ᴴ *ᵥ v) ≤ c * vecNormSq v := by
  set B : Matrix ι ι ℂ := (tᴴ)⁻¹
  set F : ℝ := (∑ i, ∑ j, ‖B i j‖ ^ 2) + 1
  have hF0 : 0 ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hFpos : 0 < F := by positivity
  have htH : IsUnit (tᴴ).det := by
    rw [det_conjTranspose]; exact ht.star
  have key : ∀ v : ι → ℂ, vecNormSq v ≤ F * vecNormSq (tᴴ *ᵥ v) := by
    intro v
    have hv : v = B *ᵥ (tᴴ *ᵥ v) := by
      rw [mulVec_mulVec, nonsing_inv_mul _ htH, one_mulVec]
    calc vecNormSq v = vecNormSq (B *ᵥ (tᴴ *ᵥ v)) := by rw [← hv]
      _ ≤ (∑ i, ∑ j, ‖B i j‖ ^ 2) * vecNormSq (tᴴ *ᵥ v) := vecNormSq_mulVec_le _ _
      _ ≤ F * vecNormSq (tᴴ *ᵥ v) := by
        gcongr
        · exact vecNormSq_nonneg _
        · simp [F]
  refine ⟨1 - F⁻¹, ?_, ?_, ?_⟩
  · have : F⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simp [F, hF0])
    linarith
  · have := inv_pos.2 hFpos; linarith
  · intro v
    have h1 := vecNormSq_add_of_coisometry t r' h v
    have h2 := key v
    have h3 : F⁻¹ * vecNormSq v ≤ vecNormSq (tᴴ *ᵥ v) := by
      rw [inv_mul_le_iff₀ hFpos]; exact h2
    nlinarith

/-- Strict contraction: `‖r'ᴴ v‖ < ‖v‖` for every `v ≠ 0`. -/
theorem strict_contraction_of_coisometry (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1)
    (ht : IsUnit t.det) (v : ι → ℂ) (hv : v ≠ 0) : vecNormSq (r'ᴴ *ᵥ v) < vecNormSq v := by
  obtain ⟨c, -, hc1, hc⟩ := exists_contraction_of_coisometry t r' h ht
  have hpos : 0 < vecNormSq v :=
    lt_of_le_of_ne (vecNormSq_nonneg v) (Ne.symm ((vecNormSq_eq_zero_iff v).not.2 hv))
  calc vecNormSq (r'ᴴ *ᵥ v) ≤ c * vecNormSq v := hc v
    _ < 1 * vecNormSq v := by gcongr
    _ = vecNormSq v := one_mul _

open scoped Matrix.Norms.L2Operator in
/-- `‖r'‖ < 1` in the `ℓ²` operator norm (`Matrix.Norms.L2Operator`). -/
theorem l2_opNorm_lt_one_of_coisometry (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1)
    (ht : IsUnit t.det) : ‖r'‖ < 1 := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_contraction_of_coisometry t r' h ht
  rw [← l2_opNorm_conjTranspose]
  have hle : ‖r'ᴴ‖ ≤ Real.sqrt c := by
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul hc0]
    apply Real.sqrt_le_sqrt
    simpa [vecNormSq] using hc x.ofLp
  exact hle.trans_lt ((Real.sqrt_lt' one_pos).2 (by simpa using hc1))

/-- `r'ⁿ → 0` (entrywise, i.e. in the product topology of `Matrix ι ι ℂ`). -/
theorem tendsto_pow_of_coisometry (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1)
    (ht : IsUnit t.det) : Tendsto (fun n : ℕ => r' ^ n) atTop (𝓝 0) := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_contraction_of_coisometry t r' h ht
  have hpow : ∀ (n : ℕ) (v : ι → ℂ), vecNormSq ((r'ᴴ) ^ n *ᵥ v) ≤ c ^ n * vecNormSq v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', ← mulVec_mulVec, pow_succ']
      calc vecNormSq (r'ᴴ *ᵥ ((r'ᴴ) ^ n *ᵥ v)) ≤ c * vecNormSq ((r'ᴴ) ^ n *ᵥ v) := hc _
        _ ≤ c * (c ^ n * vecNormSq v) := by gcongr; exact ih v
        _ = c * c ^ n * vecNormSq v := by ring
  have hent : ∀ i j, Tendsto (fun n : ℕ => (r' ^ n) i j) atTop (𝓝 0) := by
    intro i j
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun n : ℕ => ‖(r' ^ n) i j‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => sq_nonneg _) (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1)
      have e : (r' ^ n) i j = star (((r'ᴴ) ^ n *ᵥ Pi.single i 1) j) := by
        rw [mulVec_single_one, ← conjTranspose_pow, col_apply, conjTranspose_apply, star_star]
      have := norm_sq_le_vecNormSq ((r'ᴴ) ^ n *ᵥ Pi.single i 1) j
      have h2 := hpow n (Pi.single i 1)
      have h3 : vecNormSq (Pi.single i (1 : ℂ)) = 1 := by
        simp [vecNormSq, Pi.single_apply, apply_ite]
      rw [e, norm_star]
      rw [h3, mul_one] at h2
      exact this.trans h2
    have := hsq.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hent i j

/-- `I - z r'` is invertible for every `|z| = 1`. -/
theorem det_one_sub_smul_ne_zero (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1)
    (ht : IsUnit t.det) {z : ℂ} (hz : ‖z‖ = 1) : (1 - z • r').det ≠ 0 := by
  intro hdet
  have hdet' : (1 - z • r')ᴴ.det = 0 := by rw [det_conjTranspose, hdet, star_zero]
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.2 hdet'
  have e : (1 - z • r')ᴴ = 1 - star z • r'ᴴ := by
    simp [conjTranspose_sub, conjTranspose_smul]
  rw [e, sub_mulVec, one_mulVec, smul_mulVec, sub_eq_zero] at hw
  have h1 := vecNormSq_add_of_coisometry t r' h w
  have h2 : vecNormSq (r'ᴴ *ᵥ w) = vecNormSq w := by
    have : vecNormSq w = ‖star z‖ ^ 2 * vecNormSq (r'ᴴ *ᵥ w) := by
      conv_lhs => rw [hw]
      exact vecNormSq_smul _ _
    rw [this, norm_star, hz]; ring
  have h3 : vecNormSq (tᴴ *ᵥ w) = 0 := by linarith
  rw [vecNormSq_eq_zero_iff] at h3
  have htH : IsUnit (tᴴ).det := by rw [det_conjTranspose]; exact ht.star
  apply hw0
  have := congrArg (fun v => (tᴴ)⁻¹ *ᵥ v) h3
  simpa [mulVec_mulVec, nonsing_inv_mul _ htH] using this

open scoped ComplexOrder in
/-- If `t tᴴ` is positive definite then `det t` is a unit. -/
theorem isUnit_det_of_posDef (t : Matrix ι ι ℂ) (ht : (t * tᴴ).PosDef) : IsUnit t.det := by
  have hpos := ht.det_pos
  rw [det_mul, det_conjTranspose] at hpos
  refine Ne.isUnit fun h0 => ?_
  rw [h0, zero_mul] at hpos
  exact lt_irrefl _ hpos

end Contraction

section PhaseIntegral

/-- The unimodular phase `e^{iθ}`. -/
def phase (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

@[fun_prop]
theorem continuous_phase : Continuous phase := by
  unfold phase; fun_prop

theorem norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem phase_mul_star (θ : ℝ) : phase θ * star (phase θ) = 1 := by
  have := Complex.mul_conj' (phase θ)
  rw [norm_phase] at this
  simpa using this

/-- `∫₀^{2π} e^{imθ} dθ = 0` for every natural `m ≠ 0`. -/
theorem integral_phase_pow {m : ℕ} (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, phase θ ^ m = 0 := by
  have hc : (m : ℂ) * Complex.I ≠ 0 := by
    simp [hm, Complex.I_ne_zero]
  have e : ∀ θ : ℝ, phase θ ^ m = Complex.exp (((m : ℂ) * Complex.I) * θ) := by
    intro θ
    rw [phase, ← Complex.exp_nat_mul]; ring_nf
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  have h2 : Complex.exp ((m : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_nat_mul_two_pi_mul_I m]; push_cast; ring_nf
  rw [h2]; simp

variable {m n : Type*}

/-- Unnormalised entrywise phase integral: `(phaseIntegral F)ᵢⱼ = ∫₀^{2π} F(θ)ᵢⱼ dθ`. -/
def phaseIntegral (F : ℝ → Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.of fun i j => ∫ θ in (0 : ℝ)..2 * π, F θ i j

theorem phaseIntegral_apply (F : ℝ → Matrix m n ℂ) (i : m) (j : n) :
    phaseIntegral F i j = ∫ θ in (0 : ℝ)..2 * π, F θ i j := rfl

theorem intervalIntegrable_entry {F : ℝ → Matrix m n ℂ} (hF : Continuous F) (i : m) (j : n) :
    IntervalIntegrable (fun θ => F θ i j) MeasureTheory.volume 0 (2 * π) :=
  (hF.matrix_elem i j).intervalIntegrable _ _

theorem phaseIntegral_add {F G : ℝ → Matrix m n ℂ} (hF : Continuous F) (hG : Continuous G) :
    phaseIntegral (fun θ => F θ + G θ) = phaseIntegral F + phaseIntegral G := by
  ext i j
  simp only [phaseIntegral_apply, Matrix.add_apply]
  exact intervalIntegral.integral_add (intervalIntegrable_entry hF i j)
    (intervalIntegrable_entry hG i j)

theorem phaseIntegral_const (P : Matrix m n ℂ) :
    phaseIntegral (fun _ => P) = ((2 * π : ℝ) : ℂ) • P := by
  ext i j
  simp [phaseIntegral_apply, intervalIntegral.integral_const]

theorem phaseIntegral_pow_smul_const (P : Matrix m n ℂ) {k : ℕ} (hk : k ≠ 0) :
    phaseIntegral (fun θ => phase θ ^ k • P) = 0 := by
  ext i j
  simp only [phaseIntegral_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [intervalIntegral.integral_mul_const, integral_phase_pow hk, zero_mul]

theorem phaseIntegral_conjTranspose (F : ℝ → Matrix m n ℂ) :
    phaseIntegral (fun θ => (F θ)ᴴ) = (phaseIntegral F)ᴴ := by
  ext i j
  simp only [phaseIntegral_apply, conjTranspose_apply]
  exact intervalIntegral.intervalIntegral_conj

theorem phaseIntegral_mul_left [Fintype m] {l : Type*} (P : Matrix l m ℂ)
    {F : ℝ → Matrix m n ℂ} (hF : Continuous F) :
    phaseIntegral (fun θ => P * F θ) = P * phaseIntegral F := by
  ext i j
  simp only [phaseIntegral_apply, mul_apply]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (intervalIntegrable_entry hF k j).const_mul (P i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact intervalIntegral.integral_const_mul _ _

theorem phaseIntegral_mul_right [Fintype n] {l : Type*} (Q : Matrix n l ℂ)
    {F : ℝ → Matrix m n ℂ} (hF : Continuous F) :
    phaseIntegral (fun θ => F θ * Q) = phaseIntegral F * Q := by
  ext i j
  simp only [phaseIntegral_apply, mul_apply]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (intervalIntegrable_entry hF i k).mul_const (Q k j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact intervalIntegral.integral_mul_const _ _

theorem phaseIntegral_sandwich [Fintype m] [Fintype n] {l p : Type*} (P : Matrix l m ℂ)
    (Q : Matrix n p ℂ) {F : ℝ → Matrix m n ℂ} (hF : Continuous F) :
    phaseIntegral (fun θ => P * F θ * Q) = P * phaseIntegral F * Q := by
  rw [phaseIntegral_mul_right Q (continuous_const.matrix_mul hF), phaseIntegral_mul_left P hF]

theorem norm_phaseIntegral_pow_smul_le (F : ℝ → Matrix m n ℂ) (k : ℕ) (i : m) (j : n) :
    ‖phaseIntegral (fun θ => phase θ ^ k • F θ) i j‖ ≤ ∫ θ in (0 : ℝ)..2 * π, ‖F θ i j‖ := by
  rw [phaseIntegral_apply]
  refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
  congr 1; funext θ
  simp [norm_pow, norm_phase]

end PhaseIntegral

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Γ_θ = (I - e^{iθ} r')⁻¹ e^{iθ} t` (far port closed by `e^{iθ} I`). -/
def phaseGamma (r' t : Matrix ι ι ℂ) (θ : ℝ) : Matrix ι ι ℂ :=
  (1 - phase θ • r')⁻¹ * (phase θ • t)

/-- `A_θ = [I ; Γ_θ]`: block row `0` (near) is `I`, block row `1` (far) is `Γ_θ`. -/
def phaseA (r' t : Matrix ι ι ℂ) (θ : ℝ) : Matrix (Fin 2 × ι) ι ℂ :=
  Matrix.of fun p j => ![(1 : Matrix ι ι ℂ), phaseGamma r' t θ] p.1 p.2 j

variable (t r' : Matrix ι ι ℂ) (h : t * tᴴ + r' * r'ᴴ = 1) (ht : IsUnit t.det)
include h ht

theorem continuous_phaseGamma : Continuous (phaseGamma r' t) := by
  have hc : Continuous fun θ : ℝ => 1 - phase θ • r' :=
    continuous_const.sub (continuous_phase.smul continuous_const)
  have hinv : Continuous fun θ : ℝ => (1 - phase θ • r')⁻¹ := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    have hu : IsUnit (1 - phase θ • r').det :=
      (det_one_sub_smul_ne_zero t r' h ht (norm_phase θ)).isUnit
    refine (continuousAt_matrix_inv _ ?_).comp hc.continuousAt
    rw [← hu.unit_spec]
    exact NormedRing.inverse_continuousAt _
  exact hinv.matrix_mul (continuous_phase.smul continuous_const)

/-- Fixed-point form of the closure: `Γ_θ = e^{iθ} (t + r' Γ_θ)`. -/
theorem phaseGamma_eq (θ : ℝ) :
    phaseGamma r' t θ = phase θ • (t + r' * phaseGamma r' t θ) := by
  have hu : IsUnit (1 - phase θ • r').det :=
    (det_one_sub_smul_ne_zero t r' h ht (norm_phase θ)).isUnit
  have h1 : (1 - phase θ • r') * phaseGamma r' t θ = phase θ • t := by
    rw [phaseGamma, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [sub_mul, Matrix.one_mul, smul_mul_assoc] at h1
  rw [smul_add, ← h1]; abel

/-- `∫₀^{2π} Γ_θ dθ = 0` (entrywise). -/
theorem phaseIntegral_phaseGamma : phaseIntegral (phaseGamma r' t) = 0 := by
  have hΓ := continuous_phaseGamma t r' h ht
  set G : ℕ → Matrix ι ι ℂ := fun k => phaseIntegral (fun θ => phase θ ^ k • phaseGamma r' t θ)
  have hcont : ∀ k : ℕ, Continuous fun θ => phase θ ^ k • phaseGamma r' t θ :=
    fun k => (continuous_phase.pow k).smul hΓ
  have hrec : ∀ k, G k = r' * G (k + 1) := by
    intro k
    have e : (fun θ => phase θ ^ k • phaseGamma r' t θ) =
        fun θ => phase θ ^ (k + 1) • t + r' * (phase θ ^ (k + 1) • phaseGamma r' t θ) := by
      funext θ
      conv_lhs => rw [phaseGamma_eq t r' h ht θ]
      rw [smul_smul, ← pow_succ, smul_add, Matrix.mul_smul]
    simp only [G]
    rw [e, phaseIntegral_add (by fun_prop) (continuous_const.matrix_mul (hcont _)),
      phaseIntegral_pow_smul_const _ (Nat.succ_ne_zero k),
      zero_add, phaseIntegral_mul_left _ (hcont _)]
  have hiter : ∀ n : ℕ, G 0 = r' ^ n * G n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrec n, ← Matrix.mul_assoc, ← pow_succ]
  have hG0 : G 0 = phaseIntegral (phaseGamma r' t) := by simp [G]
  rw [← hG0]
  have hpow := tendsto_pow_of_coisometry t r' h ht
  ext i j
  rw [Matrix.zero_apply]
  set C : ι → ℝ := fun k => ∫ θ in (0 : ℝ)..2 * π, ‖phaseGamma r' t θ k j‖
  have hbound : ∀ n : ℕ, ‖G 0 i j‖ ≤ ∑ k, ‖(r' ^ n) i k‖ * C k := by
    intro n
    rw [hiter n, mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    gcongr
    exact norm_phaseIntegral_pow_smul_le _ n k j
  have hlim : Tendsto (fun n : ℕ => ∑ k, ‖(r' ^ n) i k‖ * C k) atTop (𝓝 0) := by
    have : (0 : ℝ) = ∑ k : ι, ‖(0 : ℂ)‖ * C k := by simp
    rw [this]
    refine tendsto_finsetSum _ fun k _ => (Tendsto.norm ?_).mul_const _
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hpow i) k
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hbound)

/-- `∫₀^{2π} Γ_θ Γ_θᴴ dθ = 2π I` (entrywise); no normality of `r'` is used. -/
theorem phaseIntegral_phaseGamma_mul_conjTranspose :
    phaseIntegral (fun θ => phaseGamma r' t θ * (phaseGamma r' t θ)ᴴ) =
      ((2 * π : ℝ) : ℂ) • 1 := by
  have hΓ := continuous_phaseGamma t r' h ht
  set X := phaseIntegral (fun θ => phaseGamma r' t θ * (phaseGamma r' t θ)ᴴ)
  have hΓH : Continuous fun θ => (phaseGamma r' t θ)ᴴ := hΓ.matrix_conjTranspose
  have hGG : Continuous fun θ => phaseGamma r' t θ * (phaseGamma r' t θ)ᴴ :=
    hΓ.matrix_mul hΓH
  have hpt : ∀ θ, phaseGamma r' t θ * (phaseGamma r' t θ)ᴴ =
      t * tᴴ + (t * (phaseGamma r' t θ)ᴴ * r'ᴴ + (r' * phaseGamma r' t θ * tᴴ +
        r' * (phaseGamma r' t θ * (phaseGamma r' t θ)ᴴ) * r'ᴴ)) := by
    intro θ
    set Γ := phaseGamma r' t θ
    have e := phaseGamma_eq t r' h ht θ
    calc Γ * Γᴴ = (phase θ • (t + r' * Γ)) * (phase θ • (t + r' * Γ))ᴴ := by rw [← e]
      _ = (phase θ * star (phase θ)) • ((t + r' * Γ) * (t + r' * Γ)ᴴ) := by
        rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = _ := by
        rw [phase_mul_star, one_smul]
        simp only [conjTranspose_add, conjTranspose_mul]
        noncomm_ring
  have hX : X = ((2 * π : ℝ) : ℂ) • (t * tᴴ) + r' * X * r'ᴴ := by
    have h0 := phaseIntegral_phaseGamma t r' h ht
    calc X = phaseIntegral (fun θ => t * tᴴ + (t * (phaseGamma r' t θ)ᴴ * r'ᴴ +
        (r' * phaseGamma r' t θ * tᴴ +
          r' * (phaseGamma r' t θ * (phaseGamma r' t θ)ᴴ) * r'ᴴ))) := by
          simp only [X]; congr 1; funext θ; exact hpt θ
      _ = ((2 * π : ℝ) : ℂ) • (t * tᴴ) + (t * (phaseIntegral (phaseGamma r' t))ᴴ * r'ᴴ +
          (r' * phaseIntegral (phaseGamma r' t) * tᴴ + r' * X * r'ᴴ)) := by
          rw [phaseIntegral_add (by fun_prop) (by fun_prop),
            phaseIntegral_add (by fun_prop) (by fun_prop),
            phaseIntegral_add (by fun_prop) (by fun_prop),
            phaseIntegral_const, phaseIntegral_sandwich _ _ hΓH, phaseIntegral_sandwich _ _ hΓ,
            phaseIntegral_sandwich _ _ hGG, phaseIntegral_conjTranspose]
      _ = _ := by rw [h0]; simp
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    have : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  set Y := ((2 * π : ℝ) : ℂ)⁻¹ • X - 1 with hYdef
  have hY : Y = r' * Y * r'ᴴ := by
    have ht' : t * tᴴ = 1 - r' * r'ᴴ := by rw [← h]; abel
    simp only [Y]
    conv_lhs => rw [hX]
    rw [smul_add, smul_smul, inv_mul_cancel₀ hπ, one_smul, ht', Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    abel
  have hiter : ∀ n : ℕ, Y = r' ^ n * Y * (r' ^ n)ᴴ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, conjTranspose_mul,
        show r' ^ n * r' * Y * (r'ᴴ * (r' ^ n)ᴴ) = r' ^ n * (r' * Y * r'ᴴ) * (r' ^ n)ᴴ by
          simp only [Matrix.mul_assoc], ← hY]
      exact ih
  have hpow := tendsto_pow_of_coisometry t r' h ht
  have hf : Continuous fun A : Matrix ι ι ℂ => A * Y * Aᴴ :=
    (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose
  have hlim := (hf.tendsto 0).comp hpow
  simp only [Matrix.zero_mul, conjTranspose_zero, Matrix.mul_zero] at hlim
  have hlim' : Tendsto (fun _ : ℕ => Y) atTop (𝓝 0) := by
    refine hlim.congr fun n => ?_
    exact (hiter n).symm
  have hY0 : Y = 0 := tendsto_nhds_unique tendsto_const_nhds hlim'
  have : ((2 * π : ℝ) : ℂ)⁻¹ • X = 1 := sub_eq_zero.1 hY0
  rw [← this, smul_smul, mul_inv_cancel₀ hπ, one_smul]

/-- `∫₀^{2π} A_θ A_θᴴ dθ = 2π I_{2W}` (entrywise, unnormalised). -/
theorem phaseIntegral_phaseA :
    phaseIntegral (fun θ => phaseA r' t θ * (phaseA r' t θ)ᴴ) = ((2 * π : ℝ) : ℂ) • 1 := by
  have h0 := phaseIntegral_phaseGamma t r' h ht
  have h1 := phaseIntegral_phaseGamma_mul_conjTranspose t r' h ht
  have hc := phaseIntegral_conjTranspose (phaseGamma r' t)
  rw [h0, conjTranspose_zero] at hc
  have hk := phaseIntegral_const (1 : Matrix ι ι ℂ)
  ext ⟨a, i⟩ ⟨b, j⟩
  have key : phaseIntegral (fun θ => phaseA r' t θ * (phaseA r' t θ)ᴴ) (a, i) (b, j) =
      phaseIntegral (fun θ => ![(1 : Matrix ι ι ℂ), phaseGamma r' t θ] a *
        (![(1 : Matrix ι ι ℂ), phaseGamma r' t θ] b)ᴴ) i j := rfl
  rw [key]
  fin_cases a <;> fin_cases b
  · simpa [Matrix.one_apply, Prod.ext_iff] using congrFun (congrFun hk i) j
  · simpa [Matrix.one_apply, Prod.ext_iff] using congrFun (congrFun hc i) j
  · simpa [Matrix.one_apply, Prod.ext_iff] using congrFun (congrFun h0 i) j
  · simpa [Matrix.one_apply, Prod.ext_iff] using congrFun (congrFun h1 i) j

end Core

section Scattering

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `(a, b)` block `S_{ab}` of a `2 × 2` block matrix on `Fin 2 × ι`
(port `0` = near, port `1` = far). -/
def scatteringBlock (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (a b : Fin 2) : Matrix ι ι ℂ :=
  Matrix.of fun i j => S (a, i) (b, j)

/-- Transmission `t = S₁₀` (near incoming → far outgoing). -/
def transmission (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) : Matrix ι ι ℂ := scatteringBlock S 1 0

/-- Far reflection `r' = S₁₁`. -/
def farReflection (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) : Matrix ι ι ℂ := scatteringBlock S 1 1

/-- Unitarity `S Sᴴ = I` gives `t tᴴ + r' r'ᴴ = I` (far block row). -/
theorem transmission_mul_add_farReflection_mul (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ)
    (hS : S * Sᴴ = 1) :
    transmission S * (transmission S)ᴴ + farReflection S * (farReflection S)ᴴ = 1 := by
  ext i j
  have := congrFun (congrFun hS (1, i)) (1, j)
  simp only [mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, conjTranspose_apply,
    Matrix.one_apply, Prod.mk.injEq, true_and] at this
  simpa [transmission, farReflection, scatteringBlock, mul_apply, Matrix.one_apply,
    conjTranspose_apply] using this

/-- `A_θ` built from the blocks of `S`: `[I ; (I - e^{iθ} S₁₁)⁻¹ e^{iθ} S₁₀]`. -/
def scatteringPhaseA (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (θ : ℝ) : Matrix (Fin 2 × ι) ι ℂ :=
  phaseA (farReflection S) (transmission S) θ

/-- the phase-resolution lemma, the phase-resolution identity, deterministic core, any finite
`ι`: for every `S` with `S Sᴴ = I` and `det S₁₀ ≠ 0`, and all `x y`,
`(1/(2π)) ∫₀^{2π} (A_θ A_θᴴ) x y dθ = δ_{xy}`. -/
theorem phase_resolution_average_general (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ)
    (hS : S * Sᴴ = 1) (ht : IsUnit (transmission S).det) (x y : Fin 2 × ι) :
    ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..2 * π, (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y =
      (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) x y := by
  have := congrFun (congrFun (phaseIntegral_phaseA _ _
    (transmission_mul_add_farReflection_mul S hS) ht) x) y
  rw [phaseIntegral_apply] at this
  simp only [scatteringPhaseA]
  rw [this, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ hπ, Complex.ofReal_one, one_mul]

/-- **The phase-resolution identity** (deterministic core). For every `W`, every
`S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ` with `S Sᴴ = I` and invertible
transmission `t = S₁₀`, and all indices `x y`,
`(1/(2π)) ∫₀^{2π} (A_θ A_θᴴ) x y dθ = (I_{2W}) x y`, where
`A_θ = [I ; (I - e^{iθ} r')⁻¹ e^{iθ} t]`, `r' = S₁₁`. -/
theorem phase_resolution_average {W : ℕ} (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hS : S * Sᴴ = 1) (ht : IsUnit (transmission S).det) :
    ∀ x y : Fin 2 × Fin W, ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..2 * π, (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y =
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) x y :=
  phase_resolution_average_general S hS ht

open scoped ComplexOrder in
/-- Variant of `phase_resolution_average` with `t tᴴ ≻ 0` in place of `det t ≠ 0`. -/
theorem phase_resolution_average_of_posDef {W : ℕ}
    (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hS : S * Sᴴ = 1) (ht : (transmission S * (transmission S)ᴴ).PosDef) :
    ∀ x y : Fin 2 × Fin W, ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..2 * π, (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y =
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) x y :=
  phase_resolution_average S hS (isUnit_det_of_posDef _ ht)

end Scattering

section Clock

variable {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]

/-- Clock identity after closure (the phase-resolution lemma, last sentence): for any
`U : Matrix κ (Fin 2 × ι) ℂ` (interior solution map), any `A` and any `g`,
`(U A g)ᴴ (U A g) = gᴴ (Aᴴ (Uᴴ U) A) g`; with `A = A_θ` and `Y = Uᴴ U` this says the
one-input clock after closure is `A_θᴴ Y A_θ`. -/
theorem clock_after_closure (U : Matrix κ (Fin 2 × ι) ℂ) (A : Matrix (Fin 2 × ι) ρ ℂ)
    (g : ρ → ℂ) :
    star (U *ᵥ (A *ᵥ g)) ⬝ᵥ (U *ᵥ (A *ᵥ g)) = star g ⬝ᵥ ((Aᴴ * (Uᴴ * U) * A) *ᵥ g) := by
  rw [star_mulVec, ← dotProduct_mulVec, star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/-- Norm form of `clock_after_closure`: `‖U A g‖² = gᴴ (Aᴴ (Uᴴ U) A) g`. -/
theorem clock_after_closure_normSq (U : Matrix κ (Fin 2 × ι) ℂ) (A : Matrix (Fin 2 × ι) ρ ℂ)
    (g : ρ → ℂ) :
    ((vecNormSq (U *ᵥ (A *ᵥ g)) : ℝ) : ℂ) = star g ⬝ᵥ ((Aᴴ * (Uᴴ * U) * A) *ᵥ g) := by
  rw [← star_dotProduct_self_eq, clock_after_closure]

/-- `clock_after_closure_normSq` specialised to `A = A_θ`. -/
theorem clock_after_closure_phaseA [DecidableEq ι] (U : Matrix κ (Fin 2 × ι) ℂ)
    (r' t : Matrix ι ι ℂ) (θ : ℝ) (g : ι → ℂ) :
    ((vecNormSq (U *ᵥ (phaseA r' t θ *ᵥ g)) : ℝ) : ℂ) =
      star g ⬝ᵥ (((phaseA r' t θ)ᴴ * (Uᴴ * U) * phaseA r' t θ) *ᵥ g) :=
  clock_after_closure_normSq U _ g

end Clock

end BlockBand.Endpoints.Clock
