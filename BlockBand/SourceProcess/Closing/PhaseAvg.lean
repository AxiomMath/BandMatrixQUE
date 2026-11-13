module

public import BlockBand.SourceProcess.Closing.Defs

/-!
# The phase average of matrix-valued functions

`phaseAvg f` is the entrywise average of `f(θ)` over the uniform phase `θ ∈ [0, 2π)`. It is
linear, commutes with constant left and right factors and with `ᴴ` for continuous `f`, and kills
`z^k` for `k ≥ 1` (`integral_phase_pow`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory Matrix Filter Topology
open scoped Matrix ComplexConjugate

variable {ι : Type*}

/-- The entrywise phase average `E_z f(θ)`. -/
def phaseAvg (f : ℝ → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∫ θ, f θ i j ∂phaseLaw

theorem continuous_phase : Continuous phase :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem norm_phase (θ : ℝ) : ‖phase θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem phase_mul_star (θ : ℝ) : phase θ * star (phase θ) = 1 := by
  have h := Complex.mul_conj' (phase θ)
  rw [norm_phase] at h
  simpa using h

theorem integrable_of_continuous {f : ℝ → ℂ} (hf : Continuous f) : Integrable f phaseLaw := by
  have h1 : IntegrableOn f (Set.Icc 0 (2 * Real.pi)) volume := hf.integrableOn_Icc
  have h2 : IntegrableOn f (Set.Ico 0 (2 * Real.pi)) volume := h1.mono_set Set.Ico_subset_Icc_self
  exact h2.smul_measure ENNReal.ofReal_ne_top

theorem integrable_entry {f : ℝ → Matrix ι ι ℂ} (hf : Continuous f) (i j : ι) :
    Integrable (fun θ => f θ i j) phaseLaw :=
  integrable_of_continuous ((continuous_apply j).comp ((continuous_apply i).comp hf))

theorem phaseAvg_add {f g : ℝ → Matrix ι ι ℂ} (hf : Continuous f) (hg : Continuous g) :
    phaseAvg (fun θ => f θ + g θ) = phaseAvg f + phaseAvg g := by
  ext i j
  simp only [phaseAvg, of_apply, Matrix.add_apply]
  exact integral_add (integrable_entry hf i j) (integrable_entry hg i j)

theorem phaseAvg_sub {f g : ℝ → Matrix ι ι ℂ} (hf : Continuous f) (hg : Continuous g) :
    phaseAvg (fun θ => f θ - g θ) = phaseAvg f - phaseAvg g := by
  ext i j
  simp only [phaseAvg, of_apply, Matrix.sub_apply]
  exact integral_sub (integrable_entry hf i j) (integrable_entry hg i j)

theorem phaseAvg_mul_left [Fintype ι] (N : Matrix ι ι ℂ) {f : ℝ → Matrix ι ι ℂ} (hf : Continuous f) :
    phaseAvg (fun θ => N * f θ) = N * phaseAvg f := by
  ext i j
  simp only [phaseAvg, of_apply, mul_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_entry hf k j).const_mul (N i k)]
  simp_rw [integral_const_mul]

theorem phaseAvg_mul_right [Fintype ι] (N : Matrix ι ι ℂ) {f : ℝ → Matrix ι ι ℂ} (hf : Continuous f) :
    phaseAvg (fun θ => f θ * N) = phaseAvg f * N := by
  ext i j
  simp only [phaseAvg, of_apply, mul_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_entry hf i k).mul_const (N k j)]
  simp_rw [integral_mul_const]

theorem phaseAvg_conjTranspose {f : ℝ → Matrix ι ι ℂ} :
    phaseAvg (fun θ => (f θ)ᴴ) = (phaseAvg f)ᴴ := by
  ext i j
  simp only [phaseAvg, of_apply, conjTranspose_apply]
  exact integral_conj

theorem phaseAvg_const (C : Matrix ι ι ℂ) : phaseAvg (fun _ => C) = C := by
  ext i j
  simp [phaseAvg]

/-- **Phase orthogonality** `E_z z^k = 0` for `k ≥ 1`. -/
theorem integral_phase_pow {k : ℕ} (hk : 1 ≤ k) : ∫ θ, phase θ ^ k ∂phaseLaw = 0 := by
  have hc : ((k : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) Complex.I_ne_zero
  have e : ∀ θ : ℝ, phase θ ^ k = Complex.exp ((k : ℂ) * Complex.I * θ) := by
    intro θ
    rw [phase, ← Complex.exp_nat_mul]
    ring_nf
  simp_rw [e]
  rw [phaseLaw, integral_smul_measure, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
    integral_exp_mul_complex hc]
  have h1 : Complex.exp ((k : ℂ) * Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
    rw [← Complex.exp_nat_mul_two_pi_mul_I k]
    ring_nf
  push_cast
  simp [h1]

theorem phaseAvg_phase_pow_smul {k : ℕ} (hk : 1 ≤ k) (C : Matrix ι ι ℂ) :
    phaseAvg (fun θ => phase θ ^ k • C) = 0 := by
  ext i j
  simp only [phaseAvg, of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [integral_mul_const, integral_phase_pow hk, zero_mul]

/-- `‖E_z z^k f_{ij}‖ ≤ E_z ‖f_{ij}‖`. -/
theorem norm_phaseAvg_pow_smul_le (k : ℕ) (f : ℝ → Matrix ι ι ℂ) (i j : ι) :
    ‖phaseAvg (fun θ => phase θ ^ k • f θ) i j‖ ≤ ∫ θ, ‖f θ i j‖ ∂phaseLaw := by
  simp only [phaseAvg, of_apply, Matrix.smul_apply, smul_eq_mul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext θ
  rw [norm_mul, norm_pow, norm_phase, one_pow, one_mul]

end BlockBand.SourceProcess.Closing
