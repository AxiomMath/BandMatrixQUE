module

public import BlockBand.Transmission.LawClauses.HessianScalar
public import BlockBand.Internal.Contracts.TransmissionPath
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Spectral integral representation of `Tr X^p`

* `fracTrace_eq_sum_eigenvalues`: `fracTrace p X = Σ_i λ_i^p` (roots of the characteristic
  polynomial are the eigenvalues);
* `inv_add_smul_eq`, `trace_inv_add_smul_re`: `(X + s)⁻¹ = U diag((λ+s)⁻¹) U*`,
  `Re Tr (X + s)⁻¹ = Σ_i (λ_i + s)⁻¹` (`λ_i + s ≠ 0`);
* **`fracTrace_eq_integral`**: `Tr X^p = (sin πp/π) ∫_0^∞ s^{p-1}(n - s Re Tr (X+s)⁻¹) ds`,
  from `λ^p = (sin πp/π) ∫_0^∞ s^{p-1} λ/(λ+s) ds` (`HessianScalar`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Set Real Matrix
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `fracTrace p X = Σ_i λ_i^p` for positive definite `X`. -/
theorem fracTrace_eq_sum_eigenvalues {X : Matrix ι ι ℂ} (hX : X.PosDef) (p : ℝ) :
    fracTrace p X = ∑ i, hX.1.eigenvalues i ^ p := by
  rw [fracTrace, hX.1.roots_charpoly_eq_eigenvalues, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [max_eq_left (hX.eigenvalues_pos i).le]

/-- `X + s = U diag(λ + s) U*`. -/
theorem add_smul_eq_spectral {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (s : ℝ) :
    X + (s : ℂ) • (1 : Matrix ι ι ℂ) =
      (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (fun i => ((hX.eigenvalues i + s : ℝ) : ℂ)) *
        star (hX.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U : Matrix ι ι ℂ := ((hX.eigenvectorUnitary : unitaryGroup ι ℂ) : Matrix ι ι ℂ)
  have hspec := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hd : diagonal (fun i => ((hX.eigenvalues i + s : ℝ) : ℂ)) =
      Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) + (s : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  conv_lhs => rw [hspec]
  rw [hd, mul_add, add_mul, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hUU]

/-- `(X + s)⁻¹ = U diag((λ + s)⁻¹) U*` when every `λ_i + s ≠ 0`. -/
theorem inv_add_smul_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (s : ℝ)
    (hs : ∀ i, hX.eigenvalues i + s ≠ 0) :
    (X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ =
      (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (fun i => (((hX.eigenvalues i + s)⁻¹ : ℝ) : ℂ)) *
        star (hX.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U : Matrix ι ι ℂ := ((hX.eigenvectorUnitary : unitaryGroup ι ℂ) : Matrix ι ι ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  refine Matrix.inv_eq_left_inv ?_
  rw [add_smul_eq_spectral hX s]
  have hdd : diagonal (fun i => (((hX.eigenvalues i + s)⁻¹ : ℝ) : ℂ)) *
      diagonal (fun i => ((hX.eigenvalues i + s : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hs i), Complex.ofReal_one]
  calc U * diagonal (fun i => (((hX.eigenvalues i + s)⁻¹ : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => ((hX.eigenvalues i + s : ℝ) : ℂ)) * star U)
      = U * (diagonal (fun i => (((hX.eigenvalues i + s)⁻¹ : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => ((hX.eigenvalues i + s : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hUU, Matrix.mul_one, hdd, Matrix.mul_one, hUU']

/-- `Re Tr (X + s)⁻¹ = Σ_i (λ_i + s)⁻¹`. -/
theorem trace_inv_add_smul_re {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (s : ℝ)
    (hs : ∀ i, hX.eigenvalues i + s ≠ 0) :
    ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re = ∑ i, (hX.eigenvalues i + s)⁻¹ := by
  rw [inv_add_smul_eq hX s hs, trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- `λ^p = (sin πp/π) ∫_0^∞ s^{p-1} λ/(λ+s) ds`. -/
theorem rpow_eq_integral {p l : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hl : 0 < l) :
    l ^ p = Real.sin (π * p) / π * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) * (l / (l + s)) := by
  have hsin : 0 < Real.sin (π * p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [integral_rpow_mul_div_add hp0 hp1 hl]
  field_simp

theorem integrableOn_rpow_mul_div_add {p l : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hl : 0 < l) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) * (l / (l + s))) (Ioi 0) := by
  have h := (integrableOn_rpow_div_pow (q := p - 1) (k := 1) (by linarith) (by push_cast; linarith)
    hl).const_mul l
  refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
  simp only [pow_one]; ring

/-- On `(0,∞)` the integrand of `fracTrace_eq_integral` is `Σ_i s^{p-1} λ_i/(λ_i+s)`. -/
theorem fracTrace_integrand_eq {X : Matrix ι ι ℂ} (hX : X.PosDef) (p : ℝ) {s : ℝ} (hs0 : 0 < s) :
    s ^ (p - 1) * ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) =
      ∑ i, s ^ (p - 1) * (hX.1.eigenvalues i / (hX.1.eigenvalues i + s)) := by
  have hev := hX.eigenvalues_pos
  have hne : ∀ i, hX.1.eigenvalues i + s ≠ 0 := fun i => by linarith [hev i]
  rw [trace_inv_add_smul_re hX.1 s hne, ← Finset.mul_sum]
  congr 1
  have h : ∀ i, hX.1.eigenvalues i / (hX.1.eigenvalues i + s) =
      1 - s * (hX.1.eigenvalues i + s)⁻¹ := fun i => by
    have := hne i
    field_simp; ring
  simp_rw [h, Finset.sum_sub_distrib, Finset.mul_sum]
  simp

/-- The integrand of `fracTrace_eq_integral` is integrable on `(0,∞)`. -/
theorem integrableOn_fracTrace_integrand {X : Matrix ι ι ℂ} (hX : X.PosDef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) *
      ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re)) (Ioi 0) := by
  have h := integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) Finset.univ fun i _ =>
    integrableOn_rpow_mul_div_add hp0 hp1 (hX.eigenvalues_pos i)
  refine IntegrableOn.congr_fun h (fun s hs => ?_) measurableSet_Ioi
  rw [fracTrace_integrand_eq hX p hs]

/-- **Integral representation** `Tr X^p = (sin πp/π) ∫_0^∞ s^{p-1}(n - s Re Tr (X+s)⁻¹) ds`
for positive definite `X`, `0 < p < 1`. -/
theorem fracTrace_eq_integral {X : Matrix ι ι ℂ} (hX : X.PosDef) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    fracTrace p X = Real.sin (π * p) / π * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
      ((Fintype.card ι : ℝ) - s * ((X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) := by
  have hev := hX.eigenvalues_pos
  rw [fracTrace_eq_sum_eigenvalues hX p]
  simp_rw [rpow_eq_integral hp0 hp1 (hev _)]
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ =>
    integrableOn_rpow_mul_div_add hp0 hp1 (hev i)]
  congr 1
  exact (setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    fracTrace_integrand_eq hX p hs).symm

end BlockBand.Transmission.LawClauses
