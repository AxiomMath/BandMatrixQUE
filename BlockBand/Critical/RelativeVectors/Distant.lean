module

public import BlockBand.Critical.RelativeVectors.FrameArray
public import BlockBand.Critical.WeightedDensity.Spectral

/-!
# The distant region at height one

The deterministic part of the distant-label bound: for every Hermitian `K` with simple spectrum
(`WeightedDensity.SimpleSpectrum`, a.s. for `F + G_s`), frame `V`, test vector `q ∈ ℂ^r`, `r₀ > 0`
and every label `j` with `|λ_j - E| ≤ r₀/8`,
`Σ_{|λ_i-E|>r₀/4} |q^*z_i|²/(N(λ_i-λ_j)²) ≤ (4 + 64/r₀²) Im((Vq)^*(K - E - i)⁻¹(Vq))`
(`distant_sum_le`), with `z_i = frameArray V K i = √N V^*u_i`. The coarse law at height `1` then
gives the distant-label bound (`relativeCoarse_event`).

* `im_resolvent_quad_eq`: `Im w^*(K - E - i)⁻¹w = Σ_ℓ |w^*u_ℓ|²/((λ_ℓ-E)² + 1)`.
* `norm_star_frameArray_sq`: `|q^*z_i|² = N |(Vq)^*u_i|²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
  BlockBand.Coarea.FreshPalm

variable {N r : ℕ}

theorem im_resolvent_quad_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (w : Fin N → ℂ) (E : ℝ) :
    (star w ⬝ᵥ ((K - ((E : ℂ) + Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ w)).im =
      ∑ ℓ, Complex.normSq (star w ⬝ᵥ freshEigenvector K ℓ) /
        ((freshEigenvalue K ℓ - E) ^ 2 + 1) := by
  rw [hK.inv_eq_sum (z := (E : ℂ) + Complex.I) (by simp), Matrix.sum_mulVec, dotProduct_sum,
    Complex.im_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [smul_mulVec, dotProduct_smul, freshProjector, vecMulVec_mulVec]
  set u := freshEigenvector K ℓ
  set a := star w ⬝ᵥ u with ha
  have hprod : star w ⬝ᵥ (MulOpposite.op (star u ⬝ᵥ w) • u) = (Complex.normSq a : ℂ) := by
    rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, star_dotProduct, ← ha,
      Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hprod, smul_eq_mul, mul_comm, Complex.im_ofReal_mul, Complex.inv_im]
  have hns : Complex.normSq (((freshEigenvalue K ℓ : ℝ) : ℂ) - ((E : ℂ) + Complex.I)) =
      (freshEigenvalue K ℓ - E) ^ 2 + 1 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hns]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.I_im, zero_sub]
  ring

theorem norm_star_frameArray_sq (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (q : Fin r → ℂ) (i : Fin N) :
    ‖star q ⬝ᵥ frameArray V K i‖ ^ 2 =
      N * Complex.normSq (star (V *ᵥ q) ⬝ᵥ freshEigenvector K i) := by
  have h : star q ⬝ᵥ frameArray V K i =
      ((Real.sqrt N : ℝ) : ℂ) * (star (V *ᵥ q) ⬝ᵥ freshEigenvector K i) := by
    rw [frameArray, dotProduct_smul, smul_eq_mul, dotProduct_mulVec, star_mulVec]
  rw [h, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Complex.normSq_eq_norm_sq]

/-- **Distant region, deterministic part of the distant-label bound.** See the module docstring. -/
theorem distant_sum_le {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (V : Matrix (Fin N) (Fin r) ℂ) (q : Fin r → ℂ) {E r₀ : ℝ} (hr₀ : 0 < r₀) (j : Fin N)
    (hj : |freshEigenvalue K j - E| ≤ r₀ / 8) :
    ∑ i ∈ Finset.univ.filter (fun i => r₀ / 4 < |freshEigenvalue K i - E|),
        ‖star q ⬝ᵥ frameArray V K i‖ ^ 2 /
          ((N : ℝ) * (freshEigenvalue K i - freshEigenvalue K j) ^ 2) ≤
      (4 + 64 / r₀ ^ 2) * (star (V *ᵥ q) ⬝ᵥ
        ((K - ((E : ℂ) + Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ (V *ᵥ q))).im := by
  rw [im_resolvent_quad_eq hK, Finset.mul_sum]
  set w := V *ᵥ q
  refine (Finset.sum_le_sum fun i hi => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => by
      have : 0 ≤ Complex.normSq (star w ⬝ᵥ freshEigenvector K i) := Complex.normSq_nonneg _
      positivity)
  have hi' : r₀ / 4 < |freshEigenvalue K i - E| := (Finset.mem_filter.1 hi).2
  set x := freshEigenvalue K i - E with hx
  set d := freshEigenvalue K i - freshEigenvalue K j with hd
  have hdx : d = x - (freshEigenvalue K j - E) := by rw [hd, hx]; ring
  have hd1 : |x| / 2 ≤ |d| := by
    rw [hdx]
    have := abs_sub_abs_le_abs_sub x (freshEigenvalue K j - E)
    linarith
  have hd2 : r₀ / 8 ≤ |d| := by linarith
  have hdpos : 0 < d ^ 2 := by
    have : 0 < |d| := lt_of_lt_of_le (by positivity) hd2
    rw [← sq_abs]; positivity
  have hkey : x ^ 2 + 1 ≤ (4 + 64 / r₀ ^ 2) * d ^ 2 := by
    have h1 : x ^ 2 ≤ 4 * d ^ 2 := by
      rw [← sq_abs x, ← sq_abs d]; nlinarith [abs_nonneg x, abs_nonneg d]
    have h2 : 1 ≤ 64 / r₀ ^ 2 * d ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul, ← sq_abs d]
      nlinarith [abs_nonneg d]
    nlinarith
  rw [norm_star_frameArray_sq]
  set s := Complex.normSq (star w ⬝ᵥ freshEigenvector K i)
  have hs : 0 ≤ s := Complex.normSq_nonneg _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact Fin.elim0 i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_div_mul_left _ _ hNr.ne']
  rw [div_le_iff₀ hdpos, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hkey hs
  nlinarith

end BlockBand.Critical.RelativeVectors
