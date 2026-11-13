module

public import BlockBand.Native.Johansson.Defs

/-!
# Johansson's formula (2.18): the inverse heat transform and biorthogonality

The inverse heat transform as a Gaussian average, and the biorthogonality of the shifted heat
kernels and the polynomials `q_j`.

* `heatInvEval_holds : HeatInvEvalStatement`, the evaluation `T P (v) = ∫ P(v + iy) dN(0,S)(y)`
  (every `S`, including `S = 0`, where `N(0,0)` is the Dirac mass);
* `biorthogonal_holds : BiorthogonalStatement`, `∫ p_S(u - d_k) q_j(u) du = δ_jk`, together with
  the integrability of every product `p_S(· - d_k) q_j`.

Proof: Taylor expansion through Hasse derivatives; odd Gaussian moments vanish
(`gaussianReal_map_neg`); for `X, Y` i.i.d. `N(0,S)`, `E[(X + iY)^m] = 0` for `m ≥ 1` by rotation
invariance of the planar Gaussian (`IsGaussian.map_rotation_eq_self`); hence
`∫ p_S(u - a) (T P)(u) du = E[P(a + X + iY)] = P(a)` (Fubini on `N(0,S) ⊗ N(0,S)`).
The polynomials `q_j = biorthPoly S d j` are real (`ℝ[X]`) by definition; their degree is at most
`N - 1` (`natDegree_biorthPoly_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal NNReal BigOperators

/-!
## Algebraic and moment preliminaries
-/

theorem eval_add_eq_sum_hasseDeriv {R : Type*} [CommRing R] (Q : R[X]) {n : ℕ}
    (hn : Q.natDegree < n) (z w : R) :
    Q.eval (z + w) = ∑ k ∈ Finset.range n, (hasseDeriv k Q).eval z * w ^ k := by
  rw [add_comm, ← taylor_eval, eval_eq_sum_range' (by rwa [natDegree_taylor])]
  simp only [taylor_coeff]

theorem integrable_pow_gaussianReal (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (gaussianReal m v) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun y => y) (by simp) k

theorem integrable_cpow_gaussianReal (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun y : ℝ => (y : ℂ) ^ k) (gaussianReal m v) := by
  have := (integrable_pow_gaussianReal m v k).ofReal (𝕜 := ℂ)
  simpa using this

theorem gaussMoment_zero (S : ℝ≥0) : gaussMoment S 0 = 1 := by
  simp [gaussMoment]

theorem gaussMoment_odd (S : ℝ≥0) {k : ℕ} (hk : Odd k) : gaussMoment S k = 0 := by
  have h : gaussMoment S k = -gaussMoment S k := by
    unfold gaussMoment
    conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := (0 : ℝ)) (v := S)]
    rw [integral_map (by fun_prop) (by fun_prop), ← integral_neg]
    congr 1; ext y; rw [hk.neg_pow]
  linarith

theorem sum_range_eq_sum_range_even {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)
    (hodd : ∀ k, Odd k → f k = 0) (hbig : ∀ k, n ≤ k → f k = 0) :
    ∑ k ∈ Finset.range n, f k = ∑ r ∈ Finset.range n, f (2 * r) := by
  have h1 : ∑ k ∈ Finset.range n, f k = ∑ k ∈ Finset.range (2 * n), f k := by
    refine Finset.sum_subset (by intro k; simp; omega) ?_
    intro k _ hk
    exact hbig k (by simpa using hk)
  have h2 : ∑ r ∈ Finset.range n, f (2 * r) =
      ∑ k ∈ (Finset.range n).image (2 * ·), f k :=
    (Finset.sum_image (by intro a _ b _ h; simpa using h)).symm
  rw [h1, h2]
  symm
  refine Finset.sum_subset (by intro k; simp; omega) ?_
  intro k hk hk'
  apply hodd
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | h
  · exfalso; apply hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨r, by omega, by omega⟩
  · exact h

/-!
## `T P (v) = ∫ P(v + iy) dN(0,S)(y)`
-/

/-- **`HeatInvEvalStatement`**: `T P (v) = ∫ P(v + iy) dN(0,S)(y)`, for every `S ≥ 0`. -/
theorem heatInvEval_holds : HeatInvEvalStatement := by
  intro S P v
  set n := P.natDegree + 1
  have hQ : (P.map (algebraMap ℝ ℂ)).natDegree < n :=
    Nat.lt_succ_of_le (natDegree_map_le)
  have hexp : ∀ y : ℝ, (P.map (algebraMap ℝ ℂ)).eval ((v : ℂ) + (y : ℂ) * Complex.I) =
      ∑ k ∈ Finset.range n, (((hasseDeriv k P).eval v : ℝ) : ℂ) * Complex.I ^ k *
        (y : ℂ) ^ k := by
    intro y
    rw [eval_add_eq_sum_hasseDeriv _ hQ]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hv : (v : ℂ) = algebraMap ℝ ℂ v := rfl
    rw [hasseDeriv_map, eval_map, mul_pow, hv, eval₂_at_apply, Complex.coe_algebraMap]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun k _ => (integrable_cpow_gaussianReal 0 S k).const_mul _)]
  simp_rw [integral_const_mul]
  have hmom : ∀ k : ℕ, ∫ y, (y : ℂ) ^ k ∂gaussianReal 0 S = (gaussMoment S k : ℂ) := by
    intro k
    have := integral_complex_ofReal (μ := gaussianReal 0 S) (f := fun y : ℝ => y ^ k)
    simpa [gaussMoment] using this
  simp_rw [hmom]
  rw [sum_range_eq_sum_range_even _ n]
  · simp only [heatInv, eval_finsetSum, eval_mul, eval_C]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_mul, Complex.I_sq]
    ring
  · intro k hk
    simp [gaussMoment_odd S hk]
  · intro k hk
    simp [hasseDeriv_eq_zero_of_lt_natDegree P k (by omega)]
/-!
## Circular moments of the planar Gaussian
-/

/-- `(X + iY)^k` is integrable for `X, Y` i.i.d. `N(0,S)`. -/
theorem integrable_planar_pow (S : ℝ≥0) (k : ℕ) :
    Integrable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ k)
      ((gaussianReal 0 S).prod (gaussianReal 0 S)) := by
  simp_rw [add_pow]
  refine integrable_finsetSum _ fun m _ => ?_
  have h := ((integrable_cpow_gaussianReal 0 S m).mul_prod
    ((integrable_cpow_gaussianReal 0 S (k - m)).mul_const (Complex.I ^ (k - m)))).mul_const
    ((k.choose m : ℕ) : ℂ)
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [mul_pow, mul_assoc]

/-- `E[(X + iY)^k] = 0` for `k ≥ 1`: rotate by `π/k`, which multiplies `(X + iY)^k` by `-1`. -/
theorem integral_planar_pow_eq_zero (S : ℝ≥0) {k : ℕ} (hk : k ≠ 0) :
    ∫ p : ℝ × ℝ, ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ k
      ∂((gaussianReal 0 S).prod (gaussianReal 0 S)) = 0 := by
  set θ : ℝ := Real.pi / k
  set μ := (gaussianReal 0 S).prod (gaussianReal 0 S)
  set f : ℝ × ℝ → ℂ := fun p => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ k
  have hrot : μ.map (ContinuousLinearMap.rotation θ) = μ :=
    IsGaussian.map_rotation_eq_self (by simp [integral_id_gaussianReal]) θ
  have hw : ∀ p : ℝ × ℝ, f (ContinuousLinearMap.rotation θ p) = -f p := by
    intro p
    have hrw : (((ContinuousLinearMap.rotation θ p).1 : ℂ) +
        ((ContinuousLinearMap.rotation θ p).2 : ℂ) * Complex.I) =
        Complex.exp (-((θ : ℂ) * Complex.I)) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      rw [← neg_mul, Complex.exp_mul_I, ContinuousLinearMap.rotation_apply]
      simp only [smul_eq_mul, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    have hpow : Complex.exp (-((θ : ℂ) * Complex.I)) ^ k = -1 := by
      rw [← Complex.exp_nat_mul]
      have : (k : ℂ) * -((θ : ℂ) * Complex.I) = -(Real.pi * Complex.I) := by
        simp only [θ]
        push_cast
        field_simp
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    simp only [f]
    rw [hrw, mul_pow, hpow, neg_one_mul]
  have h1 : ∫ p, f p ∂μ = ∫ p, f (ContinuousLinearMap.rotation θ p) ∂μ := by
    conv_lhs => rw [← hrot]
    exact integral_map (by fun_prop) (by fun_prop)
  simp_rw [hw, integral_neg] at h1
  change ∫ p, f p ∂μ = 0
  linear_combination h1 / 2

/-!
## Integrals against `p_S(· - a)`
-/

theorem integrable_eval_gaussianReal (m : ℝ) (v : ℝ≥0) (R : ℝ[X]) :
    Integrable (fun u => R.eval u) (gaussianReal m v) := by
  simp_rw [eval_eq_sum_range]
  exact integrable_finsetSum _ fun i _ => (integrable_pow_gaussianReal m v i).const_mul _

theorem integrable_gaussKernel_mul (S : ℝ≥0) (hS : 0 < S) (a : ℝ) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal a S)) :
    Integrable (fun u => gaussKernel S a u * f u) := by
  rw [gaussianReal_of_var_ne_zero _ hS.ne', gaussianPDF_def,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (ae_of_all _ fun _ => by simp)]
    at hf
  refine hf.congr (ae_of_all _ fun u => ?_)
  simp [gaussKernel, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]

theorem integral_gaussKernel_mul (S : ℝ≥0) (hS : 0 < S) (a : ℝ) (f : ℝ → ℝ) :
    ∫ u, gaussKernel S a u * f u = ∫ x, f (a + x) ∂gaussianReal 0 S := by
  have h := integral_map_equiv (μ := gaussianReal 0 S) (MeasurableEquiv.addLeft a) f
  have hm : (gaussianReal 0 S).map (MeasurableEquiv.addLeft a) = gaussianReal a S := by
    have := gaussianReal_map_const_add (μ := 0) (v := S) a
    rw [zero_add] at this
    exact this
  rw [hm] at h
  calc ∫ u, gaussKernel S a u * f u = ∫ y, f y ∂gaussianReal a S := by
        rw [integral_gaussianReal_eq_integral_smul hS.ne']; rfl
    _ = _ := h

/-- `∫ p_S(u - a) (T P)(u) du = P(a)`. -/
theorem integral_gaussKernel_mul_heatInv (S : ℝ≥0) (hS : 0 < S) (P : ℝ[X]) (a : ℝ) :
    ∫ u, gaussKernel S a u * (heatInv S P).eval u = P.eval a := by
  apply Complex.ofReal_injective
  rw [integral_gaussKernel_mul S hS, ← integral_complex_ofReal]
  have hT : HeatInvEvalStatement := heatInvEval_holds
  unfold HeatInvEvalStatement at hT
  simp_rw [hT]
  set Q := P.map (algebraMap ℝ ℂ)
  set n := P.natDegree + 1
  have hQ : Q.natDegree < n := Nat.lt_succ_of_le (natDegree_map_le)
  set μ := (gaussianReal 0 S).prod (gaussianReal 0 S)
  have hq : ∀ p : ℝ × ℝ, Q.eval ((a : ℂ) + ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) =
      ∑ k ∈ Finset.range n, (hasseDeriv k Q).eval (a : ℂ) *
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ k := fun p =>
    eval_add_eq_sum_hasseDeriv Q hQ _ _
  have hint : Integrable (fun p : ℝ × ℝ =>
      Q.eval ((a : ℂ) + ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) μ := by
    simp_rw [hq]
    exact integrable_finsetSum _ fun k _ => (integrable_planar_pow S k).const_mul _
  have h1 : (fun x : ℝ => ∫ y, Q.eval (((a + x : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      ∂gaussianReal 0 S) =
      fun x : ℝ => ∫ y, Q.eval ((a : ℂ) + ((x : ℂ) + (y : ℂ) * Complex.I)) ∂gaussianReal 0 S := by
    ext x; congr 1; ext y; push_cast; ring_nf
  rw [h1, ← integral_prod _ hint]
  simp_rw [hq]
  rw [integral_finsetSum _ fun k _ => (integrable_planar_pow S k).const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single 0]
  · have ha : (a : ℂ) = algebraMap ℝ ℂ a := rfl
    simp only [Q, hasseDeriv_zero, LinearMap.id_apply, eval_map, pow_zero, integral_const,
      probReal_univ, one_smul, mul_one]
    rw [ha, eval₂_at_apply, Complex.coe_algebraMap]
  · intro k _ hk
    rw [integral_planar_pow_eq_zero S hk, mul_zero]
  · intro h; simp [n] at h

/-!
## Biorthogonality
-/

theorem lagrangeBasis_eval {n : ℕ} (d : Fin n → ℝ) (hd : StrictMono d) (j k : Fin n) :
    (lagrangeBasis d j).eval (d k) = if j = k then 1 else 0 := by
  have hinj : Set.InjOn d (Finset.univ : Finset (Fin n)) := fun _ _ _ _ h => hd.injective h
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ _)

/-- **`BiorthogonalStatement`**: `∫ p_S(u - d_k) q_j(u) du = δ_jk`, with integrability. -/
theorem biorthogonal_holds : BiorthogonalStatement := by
  intro N S hS d hd j k
  refine ⟨integrable_gaussKernel_mul S hS (d k) (integrable_eval_gaussianReal _ _ _), ?_⟩
  rw [biorthPoly, integral_gaussKernel_mul_heatInv S hS, lagrangeBasis_eval d hd]

/-!
## Degree of the biorthogonal polynomials
-/

theorem natDegree_heatInv_le (S : ℝ≥0) (P : ℝ[X]) : (heatInv S P).natDegree ≤ P.natDegree := by
  unfold heatInv
  refine natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  exact (natDegree_hasseDeriv_le _ _).trans (Nat.sub_le _ _)

theorem natDegree_lagrangeBasis_le {n : ℕ} (d : Fin n → ℝ) (j : Fin n) :
    (lagrangeBasis d j).natDegree ≤ n - 1 := by
  unfold lagrangeBasis Lagrange.basis
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ Finset.univ.erase j, (Lagrange.basisDivisor (d j) (d i)).natDegree
      ≤ ∑ _i ∈ Finset.univ.erase j, 1 :=
        Finset.sum_le_sum fun i _ => by
          unfold Lagrange.basisDivisor
          exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
    _ = n - 1 := by simp

/-- `natDegree q_j ≤ N - 1`. The coefficients of `q_j` are real by construction (`ℝ[X]`). -/
theorem natDegree_biorthPoly_le {n : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (j : Fin n) :
    (biorthPoly S d j).natDegree ≤ n - 1 :=
  (natDegree_heatInv_le S _).trans (natDegree_lagrangeBasis_le d j)

end BlockBand.Native.Johansson
