module

public import BlockBand.Endpoints.Response.NearSchattenFinitePoly

/-!
# Scalar inputs of the finite-width higher generator: `C²` approximation of `x ↦ (x+ε^p)^r`

* `rhfAnti`: an antiderivative of a real polynomial (`rhf_derivative_anti`, value `0` at `0`).
* `rhf_exists_poly_C2` (**C² Weierstrass on an interval containing `0`**): a function with a
  continuous second derivative on `[a, b] ∋ 0` is `δ`-approximated in `C²` by a real polynomial.
* `rhfH`, `rhfH1`, `rhfH2`, `rhfH3`: `h(y) = (y+e)^r` and its first three derivatives; on
  `rhfRange p ε K = [-ε^p/2, pε^{p-1}(K+1) + K + 1]` (the range of `Tr π(A)` for eigenvalues in
  `[0, K+1]`, `π` close to `f_ε`) the shift `e = ε^p` keeps `y + e ≥ ε^p/2 > 0`, so `h` is smooth
  for every real `r ≥ 1` (`rhf_exists_rpow_approx`), with explicit sup bound `rhfB`
  (`rhf_abs_H1_le`, `rhf_abs_H2_le`, `rhf_abs_H3_le`).
* `rhf_abs_mul_sub_le`: the product comparison used by the generator comparison.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Finset Set Polynomial

/-!
## Antiderivatives of real polynomials
-/

/-- `∫₀ˣ P`, as a polynomial. -/
def rhfAnti (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ range (P.natDegree + 1), C (P.coeff n / ((n : ℝ) + 1)) * X ^ (n + 1)

theorem rhf_derivative_anti (P : ℝ[X]) : derivative (rhfAnti P) = P := by
  unfold rhfAnti
  rw [derivative_sum]
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [derivative_C_mul_X_pow]
  congr 2
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem rhf_eval_anti_zero (P : ℝ[X]) : (rhfAnti P).eval 0 = 0 := by
  simp [rhfAnti, eval_finsetSum]

/-!
## `C²` approximation on an interval containing `0`
-/

/-- Lipschitz bound on `[a, b]` from a derivative bound. -/
theorem rhf_abs_sub_le_of_deriv {g g' : ℝ → ℝ} {a b C : ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hC : ∀ x ∈ Icc a b, |g' x| ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |g x - g y| ≤ C * |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hy hx (le_of_not_ge hxy)
  have hsub : Icc y x ⊆ Icc a b := Icc_subset_Icc hy.1 hx.2
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g') (C := C) (a := y)
    (b := x) (fun z hz => (hg z (hsub hz)).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact hC z (hsub (Ico_subset_Icc_self hz))) x
    ⟨hxy, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  rwa [abs_of_nonneg (sub_nonneg.2 hxy)]

theorem rhf_abs_le_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : |x| ≤ max (-a) b := by
  rw [abs_le]
  constructor
  · have := le_max_left (-a) b; linarith [hx.1]
  · exact hx.2.trans (le_max_right _ _)

/-- **`C²` polynomial approximation on `[a, b] ∋ 0`.** -/
theorem rhf_exists_poly_C2 {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) {h h1 h2 : ℝ → ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt h (h1 x) x) (hd1 : ∀ x ∈ Icc a b, HasDerivAt h1 (h2 x) x)
    (hc : ContinuousOn h2 (Icc a b)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : ℝ[X], ∀ x ∈ Icc a b, |G.eval x - h x| ≤ δ ∧
      |(derivative G).eval x - h1 x| ≤ δ ∧ |(derivative (derivative G)).eval x - h2 x| ≤ δ := by
  set M := max (-a) b with hM
  have hM0 : 0 ≤ M := (neg_nonneg.2 ha).trans (le_max_left _ _)
  set δ₀ := δ / (M ^ 2 + M + 1) with hδ₀
  have hden : 0 < M ^ 2 + M + 1 := by positivity
  have hδ₀pos : 0 < δ₀ := div_pos hδ hden
  have hδ₀le : δ₀ ≤ δ := div_le_self hδ.le (by nlinarith)
  have hδ₀M : δ₀ * M ≤ δ := by
    rw [hδ₀, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith
  have hδ₀M2 : δ₀ * M * M ≤ δ := by
    rw [hδ₀, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn a b h2 hc δ₀ hδ₀pos
  set G : ℝ[X] := C (h 0) + C (h1 0) * X + rhfAnti (rhfAnti P) with hG
  have hG1 : derivative G = C (h1 0) + rhfAnti P := by
    rw [hG, derivative_add, derivative_add, derivative_C, derivative_C_mul_X, rhf_derivative_anti,
      zero_add]
  have hG2 : derivative (derivative G) = P := by
    rw [hG1, derivative_add, derivative_C, rhf_derivative_anti, zero_add]
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨ha, hb⟩
  have hbd2 : ∀ x ∈ Icc a b, |(derivative (derivative G)).eval x - h2 x| ≤ δ₀ := fun x hx => by
    rw [hG2]; exact (hP x hx).le
  have hder1 : ∀ x ∈ Icc a b, HasDerivAt (fun y => (derivative G).eval y - h1 y)
      ((derivative (derivative G)).eval x - h2 x) x := fun x hx =>
    ((derivative G).hasDerivAt x).sub (hd1 x hx)
  have hbd1 : ∀ x ∈ Icc a b, |(derivative G).eval x - h1 x| ≤ δ₀ * M := by
    intro x hx
    have hh := rhf_abs_sub_le_of_deriv hder1 hbd2 hx h0
    have e0 : (derivative G).eval 0 - h1 0 = 0 := by
      rw [hG1]; simp [rhf_eval_anti_zero]
    rw [e0, sub_zero, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (rhf_abs_le_of_mem hx) hδ₀pos.le)
  have hder0 : ∀ x ∈ Icc a b, HasDerivAt (fun y => G.eval y - h y)
      ((derivative G).eval x - h1 x) x := fun x hx => (G.hasDerivAt x).sub (hd x hx)
  refine ⟨G, fun x hx => ⟨?_, (hbd1 x hx).trans hδ₀M, (hbd2 x hx).trans hδ₀le⟩⟩
  have hh := rhf_abs_sub_le_of_deriv hder0 hbd1 hx h0
  have e0 : G.eval 0 - h 0 = 0 := by
    rw [hG]; simp [rhf_eval_anti_zero]
  rw [e0, sub_zero, sub_zero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (rhf_abs_le_of_mem hx)
    (mul_nonneg hδ₀pos.le hM0)).trans hδ₀M2)

/-!
## The higher power `h(y) = (y + e)^r`
-/

/-- `h(y) = (y + e)^r`. -/
def rhfH (e r y : ℝ) : ℝ := (y + e) ^ r

/-- `h'(y) = r (y + e)^{r-1}`. -/
def rhfH1 (e r y : ℝ) : ℝ := r * (y + e) ^ (r - 1)

/-- `h''(y) = r(r-1) (y + e)^{r-2}`. -/
def rhfH2 (e r y : ℝ) : ℝ := r * (r - 1) * (y + e) ^ (r - 2)

/-- `h'''(y) = r(r-1)(r-2) (y + e)^{r-3}`. -/
def rhfH3 (e r y : ℝ) : ℝ := r * (r - 1) * (r - 2) * (y + e) ^ (r - 3)

theorem rhf_hasDerivAt_cpow (c s e : ℝ) {y : ℝ} (hy : 0 < y + e) :
    HasDerivAt (fun y => c * (y + e) ^ s) (c * s * (y + e) ^ (s - 1)) y := by
  have h := ((hasDerivAt_id' y).add_const e).rpow_const (p := s) (Or.inl hy.ne')
  have h' := h.const_mul c
  convert h' using 1
  ring

theorem rhf_hasDerivAt_H (e r : ℝ) {y : ℝ} (hy : 0 < y + e) :
    HasDerivAt (rhfH e r) (rhfH1 e r y) y := by
  have h := rhf_hasDerivAt_cpow 1 r e hy
  simp only [one_mul] at h
  exact h

theorem rhf_hasDerivAt_H1 (e r : ℝ) {y : ℝ} (hy : 0 < y + e) :
    HasDerivAt (rhfH1 e r) (rhfH2 e r y) y := by
  have h := rhf_hasDerivAt_cpow r (r - 1) e hy
  unfold rhfH2
  rw [show r - 2 = r - 1 - 1 by ring]
  exact h

theorem rhf_hasDerivAt_H2 (e r : ℝ) {y : ℝ} (hy : 0 < y + e) :
    HasDerivAt (rhfH2 e r) (rhfH3 e r y) y := by
  have h := rhf_hasDerivAt_cpow (r * (r - 1)) (r - 2) e hy
  unfold rhfH3
  rw [show r - 3 = r - 2 - 1 by ring]
  exact h

/-- The approximation range `[-ε^p/2, pε^{p-1}(K+1) + K + 1]` of `Tr π(A)`. -/
def rhfRange (p ε K : ℝ) : Set ℝ := Icc (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1)

/-- `max((lo+e)^s, (hi+e)^s)`, a bound of `(y+e)^s` on `[lo, hi]`. -/
def rhfPB (e s lo hi : ℝ) : ℝ := max ((lo + e) ^ s) ((hi + e) ^ s)

theorem rhf_rpow_le_PB {e s lo hi y : ℝ} (hlo : 0 < lo + e) (hy : y ∈ Icc lo hi) :
    (y + e) ^ s ≤ rhfPB e s lo hi := by
  rcases le_total 0 s with hs | hs
  · exact (Real.rpow_le_rpow (by linarith [hy.1]) (by linarith [hy.2]) hs).trans
      (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hlo (by linarith [hy.1]) hs).trans (le_max_left _ _)

theorem rhf_PB_nonneg {e s lo hi : ℝ} (hlo : 0 < lo + e) : 0 ≤ rhfPB e s lo hi :=
  (Real.rpow_nonneg hlo.le _).trans (le_max_left _ _)

/-- The sup bound of `|h'|, |h''|, |h'''|` on `rhfRange p ε K` (`e = ε^p`). -/
def rhfB (p r ε K : ℝ) : ℝ :=
  |r| * rhfPB (ε ^ p) (r - 1) (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1) +
    |r * (r - 1)| * rhfPB (ε ^ p) (r - 2) (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1) +
    |r * (r - 1) * (r - 2)| *
      rhfPB (ε ^ p) (r - 3) (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1)

theorem rhf_range_pos {p ε K y : ℝ} (hε : 0 < ε) (hy : y ∈ rhfRange p ε K) : 0 < y + ε ^ p := by
  have := Real.rpow_pos_of_pos hε p
  have := hy.1
  linarith

theorem rhf_lo_pos {p ε : ℝ} (hε : 0 < ε) : 0 < -(ε ^ p / 2) + ε ^ p := by
  have := Real.rpow_pos_of_pos hε p
  linarith

theorem rhf_B_terms_nonneg {p r ε K : ℝ} (hε : 0 < ε) :
    0 ≤ |r| * rhfPB (ε ^ p) (r - 1) (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1) ∧
    0 ≤ |r * (r - 1)| * rhfPB (ε ^ p) (r - 2) (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1) ∧
    0 ≤ |r * (r - 1) * (r - 2)| *
      rhfPB (ε ^ p) (r - 3) (-(ε ^ p / 2)) (p * ε ^ (p - 1) * (K + 1) + K + 1) :=
  ⟨mul_nonneg (abs_nonneg _) (rhf_PB_nonneg (rhf_lo_pos hε)),
    mul_nonneg (abs_nonneg _) (rhf_PB_nonneg (rhf_lo_pos hε)),
    mul_nonneg (abs_nonneg _) (rhf_PB_nonneg (rhf_lo_pos hε))⟩

theorem rhf_B_nonneg {p r ε K : ℝ} (hε : 0 < ε) : 0 ≤ rhfB p r ε K := by
  obtain ⟨h1, h2, h3⟩ := rhf_B_terms_nonneg (p := p) (r := r) (K := K) hε
  unfold rhfB; linarith

theorem rhf_abs_cpow_le {c s e lo hi y : ℝ} (hlo : 0 < lo + e) (hy : y ∈ Icc lo hi) :
    |c * (y + e) ^ s| ≤ |c| * rhfPB e s lo hi := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith [hy.1]) _)]
  exact mul_le_mul_of_nonneg_left (rhf_rpow_le_PB hlo hy) (abs_nonneg _)

theorem rhf_abs_H1_le {p r ε K y : ℝ} (hε : 0 < ε) (hy : y ∈ rhfRange p ε K) :
    |rhfH1 (ε ^ p) r y| ≤ rhfB p r ε K := by
  obtain ⟨-, h2, h3⟩ := rhf_B_terms_nonneg (p := p) (r := r) (K := K) hε
  have := rhf_abs_cpow_le (c := r) (s := r - 1) (rhf_lo_pos hε) hy
  unfold rhfH1 rhfB; linarith

theorem rhf_abs_H2_le {p r ε K y : ℝ} (hε : 0 < ε) (hy : y ∈ rhfRange p ε K) :
    |rhfH2 (ε ^ p) r y| ≤ rhfB p r ε K := by
  obtain ⟨h1, -, h3⟩ := rhf_B_terms_nonneg (p := p) (r := r) (K := K) hε
  have := rhf_abs_cpow_le (c := r * (r - 1)) (s := r - 2) (rhf_lo_pos hε) hy
  unfold rhfH2 rhfB; linarith

theorem rhf_abs_H3_le {p r ε K y : ℝ} (hε : 0 < ε) (hy : y ∈ rhfRange p ε K) :
    |rhfH3 (ε ^ p) r y| ≤ rhfB p r ε K := by
  obtain ⟨h1, h2, -⟩ := rhf_B_terms_nonneg (p := p) (r := r) (K := K) hε
  have := rhf_abs_cpow_le (c := r * (r - 1) * (r - 2)) (s := r - 3) (rhf_lo_pos hε) hy
  unfold rhfH3 rhfB; linarith

/-- Lipschitz bounds of `h` and `h'` on `rhfRange` with constant `rhfB`. -/
theorem rhf_abs_H_sub_le {p r ε K x y : ℝ} (hε : 0 < ε) (hx : x ∈ rhfRange p ε K)
    (hy : y ∈ rhfRange p ε K) :
    |rhfH (ε ^ p) r x - rhfH (ε ^ p) r y| ≤ rhfB p r ε K * |x - y| :=
  rhf_abs_sub_le_of_deriv (fun _ hz => rhf_hasDerivAt_H _ r (rhf_range_pos hε hz))
    (fun _ hz => rhf_abs_H1_le hε hz) hx hy

theorem rhf_abs_H1_sub_le {p r ε K x y : ℝ} (hε : 0 < ε) (hx : x ∈ rhfRange p ε K)
    (hy : y ∈ rhfRange p ε K) :
    |rhfH1 (ε ^ p) r x - rhfH1 (ε ^ p) r y| ≤ rhfB p r ε K * |x - y| :=
  rhf_abs_sub_le_of_deriv (fun _ hz => rhf_hasDerivAt_H1 _ r (rhf_range_pos hε hz))
    (fun _ hz => rhf_abs_H2_le hε hz) hx hy

theorem rhf_abs_H2_sub_le {p r ε K x y : ℝ} (hε : 0 < ε) (hx : x ∈ rhfRange p ε K)
    (hy : y ∈ rhfRange p ε K) :
    |rhfH2 (ε ^ p) r x - rhfH2 (ε ^ p) r y| ≤ rhfB p r ε K * |x - y| :=
  rhf_abs_sub_le_of_deriv (fun _ hz => rhf_hasDerivAt_H2 _ r (rhf_range_pos hε hz))
    (fun _ hz => rhf_abs_H3_le hε hz) hx hy

/-- **`C²` polynomial approximants of `y ↦ (y + ε^p)^r` on `rhfRange p ε K`** (`K ≥ 0`, any real
`r`): the shift keeps the range away from the singularity. -/
theorem rhf_exists_rpow_approx {p r ε K : ℝ} (hp : 0 ≤ p) (hε : 0 < ε) (hK : 0 ≤ K) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ G : ℝ[X], ∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ ∧
      |(derivative G).eval y - rhfH1 (ε ^ p) r y| ≤ δ ∧
      |(derivative (derivative G)).eval y - rhfH2 (ε ^ p) r y| ≤ δ := by
  have hεp := Real.rpow_pos_of_pos hε p
  have hεp1 := Real.rpow_nonneg hε.le (p - 1)
  refine rhf_exists_poly_C2 (by linarith) (by positivity)
    (fun y hy => rhf_hasDerivAt_H _ r (rhf_range_pos hε hy))
    (fun y hy => rhf_hasDerivAt_H1 _ r (rhf_range_pos hε hy)) ?_ hδ
  intro y hy
  have hpos := rhf_range_pos hε hy
  exact ((((continuous_id.add continuous_const).continuousAt.rpow_const
    (Or.inl hpos.ne')).const_mul (r * (r - 1)))).continuousWithinAt

/-!
## The product comparison
-/

/-- `|u'v' - uv| ≤ |u' - u| |v'| + |u| |v' - v|` in the form used by the generator comparison:
from `|u' - u| ≤ α`, `|v'| ≤ β`, `|u| ≤ γ`, `|v' - v| ≤ ζ`. -/
theorem rhf_abs_mul_sub_le {u u' v v' α β γ ζ : ℝ} (hu : |u' - u| ≤ α) (hv' : |v'| ≤ β)
    (hu0 : |u| ≤ γ) (hv : |v' - v| ≤ ζ) : |u' * v' - u * v| ≤ α * β + γ * ζ := by
  have e : u' * v' - u * v = (u' - u) * v' + u * (v' - v) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hα : 0 ≤ α := (abs_nonneg _).trans hu
  have hγ : 0 ≤ γ := (abs_nonneg _).trans hu0
  exact add_le_add (mul_le_mul hu hv' (abs_nonneg _) hα) (mul_le_mul hu0 hv (abs_nonneg _) hγ)

end BlockBand.Endpoints
