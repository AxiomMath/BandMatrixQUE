module

public import BlockBand.Endpoints.Response.NearSchattenGeneratorScalar

/-!
# Scalar algebra for the finite-width trace generator: polynomials and the spectral form

* `nsfDivDiff d₁ d₂`, `nsfSpecGen D g d₁ d₂ λ s`: the spectral right side of the Schatten trace
  generator for a general `C²` function with first and second derivative `d₁`, `d₂`;
  `nsf_nsgSpecGen_eq` (`nsgSpecGen` is the case `f = f_ε`).
* Polynomials vanishing at `0`, coefficient form `π(x) = Σ_{r<N} a_r x^{r+1}` (`nsfPolyFun`,
  `nsfPolyD1`, `nsfPolyD2`), the divided difference `nsf_divDiff_poly`
  (`DD π'(x,y) = Σ_r a_r (r+1) Σ_{l<r} x^l y^{r-1-l}`).
* `nsf_sum_pairs`, `nsf_sum_pairs_sym`: the counting identities behind the evaluation of
  `wordDrift` on clock words (pairs `i < j < r+1` by their gap `j - i`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Finset

/-!
## The spectral form for a general `C²` function
-/

/-- Divided difference of `d₁` (`= d₂` on the diagonal). -/
def nsfDivDiff (d₁ d₂ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x = y then d₂ x else (d₁ x - d₁ y) / (x - y)

/-- The spectral right side of the Schatten trace generator for a function with derivatives
`d₁ = f'`, `d₂ = f''`: `-(D/2) g Σ_i λ_i f'(λ_i) + (D/2) Σ_{i,j} λ_iλ_j s_j DD f'(λ_i,λ_j)`. -/
def nsfSpecGen {ι : Type*} [Fintype ι] (D g : ℝ) (d₁ d₂ : ℝ → ℝ) (lam s : ι → ℝ) : ℝ :=
  -(D / 2) * g * ∑ i, lam i * d₁ (lam i) +
    D / 2 * ∑ i, ∑ j, lam i * lam j * s j * nsfDivDiff d₁ d₂ (lam i) (lam j)

theorem nsf_nsgDivDiff_eq (p ε x y : ℝ) :
    nsgDivDiff p ε x y = nsfDivDiff (nsgDeriv p ε) (nsgDeriv2 p ε) x y := rfl

/-- `nsgSpecGen` is `nsfSpecGen` at `f = f_ε`. -/
theorem nsf_nsgSpecGen_eq {ι : Type*} [Fintype ι] (D p ε g : ℝ) (lam s : ι → ℝ) :
    nsgSpecGen D p ε g lam s = nsfSpecGen D g (nsgDeriv p ε) (nsgDeriv2 p ε) lam s := rfl

/-!
## Polynomials vanishing at `0`
-/

/-- `π(x) = Σ_{r<N} a_r x^{r+1}`. -/
def nsfPolyFun (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ := ∑ r ∈ range N, a r * x ^ (r + 1)

/-- `π'(x) = Σ_{r<N} a_r (r+1) x^r`. -/
def nsfPolyD1 (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ := ∑ r ∈ range N, a r * (r + 1) * x ^ r

/-- `π''(x) = Σ_{r<N} a_r (r+1) r x^{r-1}`. -/
def nsfPolyD2 (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ := ∑ r ∈ range N, a r * (r + 1) * r * x ^ (r - 1)

/-- The monomial divided difference `Σ_{l<r} x^l y^{r-1-l}`. -/
def nsfGeom (r : ℕ) (x y : ℝ) : ℝ := ∑ l ∈ range r, x ^ l * y ^ (r - 1 - l)

theorem nsf_geom_diag (r : ℕ) (x : ℝ) : nsfGeom r x x = r * x ^ (r - 1) := by
  unfold nsfGeom
  rw [Finset.sum_congr rfl fun l hl => (show x ^ l * x ^ (r - 1 - l) = x ^ (r - 1) by
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hl; omega)]
  rw [sum_const, card_range, nsmul_eq_mul]

theorem nsf_geom_offdiag (r : ℕ) {x y : ℝ} (h : x ≠ y) :
    nsfGeom r x y = (x ^ r - y ^ r) / (x - y) := by
  rw [eq_div_iff (sub_ne_zero.2 h)]
  exact geom_sum₂_mul x y r

/-- Divided difference of a polynomial derivative. -/
theorem nsf_divDiff_poly (a : ℕ → ℝ) (N : ℕ) (x y : ℝ) :
    nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y =
      ∑ r ∈ range N, a r * (r + 1) * nsfGeom r x y := by
  unfold nsfDivDiff
  split_ifs with h
  · subst h
    unfold nsfPolyD2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [nsf_geom_diag]; ring
  · unfold nsfPolyD1
    rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [nsf_geom_offdiag r h]; ring

/-!
## Counting pairs by their gap
-/

/-- `Σ_{i<r} Σ_{i<j<r} F(j-i) = Σ_{c<r} c F(r-c)`. -/
theorem nsf_sum_pairs (F : ℕ → ℂ) (r : ℕ) :
    ∑ i ∈ range r, ∑ j ∈ Ioo i r, F (j - i) = ∑ c ∈ range r, (c : ℂ) * F (r - c) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hI : ∀ i ∈ range r, ∑ j ∈ Ioo i (r + 1), F (j - i) =
        ∑ j ∈ Ioo i r, F (j - i) + F (r - i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hset : Ioo i (r + 1) = insert r (Ioo i r) := by
        ext j; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
      rw [hset, Finset.sum_insert (by simp), add_comm]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hI, Finset.sum_add_distrib, ih,
      show Ioo r (r + 1) = ∅ by ext j; simp,
      Finset.sum_empty, add_zero, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Nat.cast_zero, zero_mul, add_zero,
      Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      congr 2; omega
    · refine Finset.sum_congr rfl fun c hc => ?_
      congr 1; omega

/-- The symmetrized pair sum on `(QP)^{r+1}`: for the gap function
`F(c) = T(r+1-c)U(c) + U(r+1-c)T(c)`,
`Σ_{i<r+1} Σ_{i<j<r+1} F(j-i) = (r+1) Σ_{l<r} T(l+1)U(r-l)`. -/
theorem nsf_sum_pairs_sym (T U : ℕ → ℂ) (r : ℕ) :
    ∑ i ∈ range (r + 1), ∑ j ∈ Ioo i (r + 1),
        (T (r + 1 - (j - i)) * U (j - i) + U (r + 1 - (j - i)) * T (j - i)) =
      ((r : ℂ) + 1) * ∑ l ∈ range r, T (l + 1) * U (r - l) := by
  rw [nsf_sum_pairs (fun c => T (r + 1 - c) * U c + U (r + 1 - c) * T c), Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  have e1 : ∀ c ∈ range r, ((c : ℂ) + 1) *
      (T (r + 1 - (r + 1 - (c + 1))) * U (r + 1 - (c + 1)) +
        U (r + 1 - (r + 1 - (c + 1))) * T (r + 1 - (c + 1))) =
      ((c : ℂ) + 1) * (T (c + 1) * U (r - c)) + ((c : ℂ) + 1) * (U (c + 1) * T (r - c)) := by
    intro c hc
    have := Finset.mem_range.1 hc
    rw [show r + 1 - (r + 1 - (c + 1)) = c + 1 by omega, show r + 1 - (c + 1) = r - c by omega]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
  have e2 : ∑ c ∈ range r, ((c : ℂ) + 1) * (U (c + 1) * T (r - c)) =
      ∑ c ∈ range r, (((r - c : ℕ) : ℂ)) * (T (c + 1) * U (r - c)) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun c hc => ?_
    have := Finset.mem_range.1 hc
    rw [show r - 1 - c + 1 = r - c by omega, show r - (r - 1 - c) = c + 1 by omega,
      show ((r - 1 - c : ℕ) : ℂ) + 1 = ((r - c : ℕ) : ℂ) by
        rw [show r - c = (r - 1 - c) + 1 by omega]; push_cast; ring]
    ring
  rw [e2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have := Finset.mem_range.1 hc
  rw [show ((r - c : ℕ) : ℂ) = (r : ℂ) - c by rw [Nat.cast_sub this.le]]
  ring

/-!
## The spectral form at a polynomial
-/

/-- The spectral generator at a polynomial in moment form: with `T(m) = Σ_i λ_i^m` and
`U(m) = Σ_j λ_j^m s_j`,
`𝒢_π = Σ_r a_r [-(D/2) g (r+1) T(r+1) + (D/2)(r+1) Σ_{l<r} T(l+1) U(r-l)]`. -/
theorem nsf_specGen_poly {ι : Type*} [Fintype ι] (D g : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (lam s : ι → ℝ) :
    nsfSpecGen D g (nsfPolyD1 a N) (nsfPolyD2 a N) lam s =
      ∑ r ∈ range N, a r * (-(D / 2) * g * ((r : ℝ) + 1) * ∑ i, lam i ^ (r + 1) +
        D / 2 * ((r : ℝ) + 1) * ∑ l ∈ range r,
          (∑ i, lam i ^ (l + 1)) * ∑ j, lam j ^ (r - l) * s j) := by
  unfold nsfSpecGen
  simp only [nsf_divDiff_poly, nsfPolyD1, nsfGeom]
  have h1 : ∑ i, lam i * ∑ r ∈ range N, a r * ((r : ℝ) + 1) * lam i ^ r =
      ∑ r ∈ range N, a r * ((r : ℝ) + 1) * ∑ i, lam i ^ (r + 1) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : ∀ i j, lam i * lam j * s j * ∑ r ∈ range N, a r * ((r : ℝ) + 1) *
      ∑ l ∈ range r, lam i ^ l * lam j ^ (r - 1 - l) =
      ∑ r ∈ range N, ∑ l ∈ range r,
        a r * ((r : ℝ) + 1) * (lam i ^ (l + 1) * (lam j ^ (r - l) * s j)) := by
    intro i j
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l hl => ?_
    have := Finset.mem_range.1 hl
    rw [show r - l = (r - 1 - l) + 1 by omega]
    ring
  have h3 : ∑ i, ∑ j, ∑ r ∈ range N, ∑ l ∈ range r,
        a r * ((r : ℝ) + 1) * (lam i ^ (l + 1) * (lam j ^ (r - l) * s j)) =
      ∑ r ∈ range N, a r * ((r : ℝ) + 1) * ∑ l ∈ range r,
        (∑ i, lam i ^ (l + 1)) * ∑ j, lam j ^ (r - l) * s j := by
    conv_lhs => rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    conv_lhs => rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [h1, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h2 i j, h3,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

end BlockBand.Endpoints
