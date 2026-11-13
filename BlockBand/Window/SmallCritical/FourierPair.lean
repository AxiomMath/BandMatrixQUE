module

public import BlockBand.Window.SmallCritical.Mode

/-!
# An atom lower bound for sums of Fourier coefficients

The Wiener-identity step of the small-critical theorem,
`lim (2M+1)^{-1} Σ_{|m|≤M} |ν̂_m|² = Σ_x ν({x})²`, applied to an atom of mass `a > 0`. Only the
inequality direction is needed, in
the finite (Fejér-type) form proved here for every finite measure `ν` on `𝕋`:

`ν({r₀})² M² ≤ Σ_{j,k<M} |ν̂_{L(j-k)}|²`  for all `L, M ∈ ℕ`, `r₀ ∈ 𝕋`,

where `ν̂_m = ∫ e^{-2πimr} ν(dr)`. Proof: `Σ_{j,k} |ν̂_{L(j-k)}|² = ∫∫ |Σ_{j<M} e^{2πiLj(r'-r)}|²
d(ν⊗ν)`, a nonnegative integrand equal to `M²` at `(r₀, r₀)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped ENNReal NNReal

/-- The pair character `e_j(r, r') = e^{-2πiLjr} e^{2πiLjr'}`. -/
def pairChar (L j : ℕ) (z : Torus × Torus) : ℂ :=
  fourier (-((L : ℤ) * j)) z.1 * fourier ((L : ℤ) * j) z.2

theorem continuous_pairChar (L j : ℕ) : Continuous (pairChar L j) :=
  ((fourier _).continuous.comp continuous_fst).mul ((fourier _).continuous.comp continuous_snd)

theorem pairChar_mul_conj (L j k : ℕ) (z : Torus × Torus) :
    pairChar L j z * conj (pairChar L k z) =
      fourier (-((L : ℤ) * ((j : ℤ) - k))) z.1 * fourier ((L : ℤ) * ((j : ℤ) - k)) z.2 := by
  unfold pairChar
  simp only [map_mul, ← fourier_neg, neg_neg]
  have h1 : fourier (-((L : ℤ) * ((j : ℤ) - k))) z.1 =
      fourier (-((L : ℤ) * j)) z.1 * fourier ((L : ℤ) * k) z.1 := by
    rw [← fourier_add]; congr 1; ring
  have h2 : fourier ((L : ℤ) * ((j : ℤ) - k)) z.2 =
      fourier ((L : ℤ) * j) z.2 * fourier (-((L : ℤ) * k)) z.2 := by
    rw [← fourier_add]; congr 1; ring
  rw [h1, h2]
  ring

theorem pairChar_diag (L j : ℕ) (r : Torus) : pairChar L j (r, r) = 1 := by
  unfold pairChar
  rw [← fourier_add, neg_add_cancel, fourier_zero]

/-- `ν({r₀})² M² ≤ Σ_{j,k<M} |ν̂_{L(j-k)}|²`. -/
theorem fourier_pair_sum_ge (ν : Measure Torus) [IsFiniteMeasure ν] (r₀ : Torus) (L M : ℕ) :
    ν.real {r₀} ^ 2 * (M : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
        ‖∫ r, fourier (-((L : ℤ) * ((j : ℤ) - k))) r ∂ν‖ ^ 2 := by
  set μ : Measure (Torus × Torus) := ν.prod ν with hμ
  have hint : ∀ f : Torus × Torus → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  set S : Torus × Torus → ℂ := fun z => ∑ j ∈ Finset.range M, pairChar L j z with hS
  have hSc : Continuous S := continuous_finsetSum _ fun j _ => continuous_pairChar L j
  -- each pair is a product integral
  have hpair : ∀ j k : ℕ, ((‖∫ r, fourier (-((L : ℤ) * ((j : ℤ) - k))) r ∂ν‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, pairChar L j z * conj (pairChar L k z) ∂μ := by
    intro j k
    simp_rw [pairChar_mul_conj]
    rw [hμ, integral_prod_mul (fun r => fourier (-((L : ℤ) * ((j : ℤ) - k))) r)
      (fun r => fourier ((L : ℤ) * ((j : ℤ) - k)) r)]
    have hc : (∫ r, fourier ((L : ℤ) * ((j : ℤ) - k)) r ∂ν) =
        conj (∫ r, fourier (-((L : ℤ) * ((j : ℤ) - k))) r ∂ν) := by
      rw [← integral_conj]
      congr 1; funext r; rw [← fourier_neg, neg_neg]
    rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsum : ((∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
      ‖∫ r, fourier (-((L : ℤ) * ((j : ℤ) - k))) r ∂ν‖ ^ 2 : ℝ) : ℂ) =
      ((∫ z, Complex.normSq (S z) ∂μ : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_sum, hpair]
    rw [← integral_complex_ofReal]
    have hfun : (fun z => ((Complex.normSq (S z) : ℝ) : ℂ)) =
        fun z => ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
          pairChar L j z * conj (pairChar L k z) := by
      funext z
      rw [← Complex.mul_conj, hS, map_sum, Finset.sum_mul_sum]
    have hjk : ∀ j k : ℕ, Integrable (fun z => pairChar L j z * conj (pairChar L k z)) μ :=
      fun j k => hint _ ((continuous_pairChar L j).mul
        (Complex.continuous_conj.comp (continuous_pairChar L k)))
    rw [hfun, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hjk j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hjk j k]
  have hsumR := Complex.ofReal_injective hsum
  rw [hsumR]
  -- lower bound by the singleton
  have hnn : 0 ≤ᵐ[μ] fun z => Complex.normSq (S z) :=
    Eventually.of_forall fun z => Complex.normSq_nonneg _
  have hSi : Integrable (fun z => Complex.normSq (S z)) μ :=
    (Complex.continuous_normSq.comp hSc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hset := setIntegral_le_integral (s := {(r₀, r₀)}) hSi hnn
  rw [integral_singleton] at hset
  have hS0 : S (r₀, r₀) = M := by
    rw [hS]; simp [pairChar_diag]
  rw [hS0, Complex.normSq_natCast, smul_eq_mul] at hset
  have hprod : μ.real {(r₀, r₀)} = ν.real {r₀} ^ 2 := by
    rw [hμ, ← Set.singleton_prod_singleton, Measure.real, Measure.prod_prod, ENNReal.toReal_mul,
      sq]
    rfl
  rw [hprod] at hset
  calc ν.real {r₀} ^ 2 * (M : ℝ) ^ 2 = ν.real {r₀} ^ 2 * ((M : ℝ) * M) := by ring
    _ ≤ _ := hset

end BlockBand.Window.SmallCritical
