module

public import BlockBand.Transmission.FractionalBulk.Spectral

/-!
# The deterministic concavity gap of `Tr(Δ Z Δ)^p`

* `quad_inv_lower`: the variational bound `2Re x*y - x*Px ≤ y*P⁻¹y` for `P ⪰ 0`;
* `resolvent_gap`: for `s > 0`, with `R = (D+s)⁻¹`, `R' = (B+s)⁻¹`, `H = B - D`,
  `R - R' = RHR - RHR'HR` and `R' ⪰ R/N` give
  `n - s Re Tr R' ≤ Σ t_i/(t_i+s) + sΣ t_i(Re Z_ii - 1)/(t_i+s)² - (s/N)Σ_{ij} t_it_j|Z_ji-δ|²/((t_i+s)²(t_j+s))`;
* **`fracTrace_sand_le`**: integrating against `c_p s^{p-1}`,
  `Tr B^p ≤ Σ t_i^p + c_pJ_p Σ t_i^p(Re Z_ii - 1) - (c_p/27N) Σ_{t_i ≤ t_j} t_i^pt_j^p|Z_ji - δ_ji|²`.

Instead of a comparison along a segment via the Hessian, the proof uses the exact second-order
resolvent identity at the comparison point `A = T` (in its eigenbasis), so no derivative of
`Tr(·)^p` at a singular matrix is needed. The linear term has the explicit coefficient
`c_pJ_p t_i^p`; the quadratic term gives the gap.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Set Real Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawClauses
open scoped ComplexOrder ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Δ = diag(√t_i)`. -/
def sqDiag (t : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt (t i) : ℝ) : ℂ)

omit [Fintype ι] in
theorem sqDiag_conjTranspose (t : ι → ℝ) : (sqDiag t)ᴴ = sqDiag t := by
  rw [sqDiag, diagonal_conjTranspose]; congr 1; funext i; simp

theorem re_conj_mul (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul']; norm_cast

omit [DecidableEq ι] in
theorem re_star_dot_self (v : ι → ℂ) : (star v ⬝ᵥ v).re = ∑ k, ‖v k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [re_conj_mul]

theorem re_star_ofReal_mul (c : ℝ) (z : ℂ) : (star ((c : ℂ) * z) * z).re = c * ‖z‖ ^ 2 := by
  have : star (c : ℂ) = c := Complex.conj_ofReal c
  rw [star_mul', this, mul_assoc, Complex.re_ofReal_mul, re_conj_mul]

omit [DecidableEq ι] in
theorem re_star_dot_comm (x y : ι → ℂ) : (star y ⬝ᵥ x).re = (star x ⬝ᵥ y).re := by
  rw [← Complex.conj_re (star x ⬝ᵥ y)]
  congr 1
  simp only [dotProduct, map_sum, Pi.star_apply, map_mul, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem trace_diag_mul_diag (r : ι → ℂ) (M : Matrix ι ι ℂ) :
    (diagonal r * M * diagonal r).trace = ∑ i, r i * r i * M i i := by
  simp only [Matrix.trace, diag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Variational bound** `2 Re x*y - Re x*Px ≤ Re y*P⁻¹y` (`P ⪰ 0`, `PR' = 1`). -/
theorem quad_inv_lower {P R' : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (hPpos : ∀ w, 0 ≤ (star w ⬝ᵥ (P *ᵥ w)).re) (hPR : P * R' = 1) (x y : ι → ℂ) :
    2 * (star x ⬝ᵥ y).re - (star x ⬝ᵥ (P *ᵥ x)).re ≤ (star y ⬝ᵥ (R' *ᵥ y)).re := by
  obtain ⟨v, hv⟩ : ∃ v, v = R' *ᵥ y := ⟨_, rfl⟩
  have hPv : P *ᵥ v = y := by rw [hv, mulVec_mulVec, hPR, one_mulVec]
  have h := hPpos (x - v)
  have hsv : star v ᵥ* P = star y := by
    calc star v ᵥ* P = star v ᵥ* Pᴴ := by rw [hP.eq]
      _ = star (P *ᵥ v) := (star_mulVec P v).symm
      _ = star y := by rw [hPv]
  have e1 : star v ⬝ᵥ (P *ᵥ x) = star y ⬝ᵥ x := by rw [dotProduct_mulVec, hsv]
  have e3 : (star v ⬝ᵥ y).re = (star y ⬝ᵥ v).re := re_star_dot_comm y v
  rw [mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hPv, e1] at h
  simp only [Complex.sub_re] at h
  rw [← hv]
  linarith [re_star_dot_comm x y]

/-- The exact identity `R - R' = RHR - RHR'HR` for `P = H + K`, `R' = P⁻¹`, `R = K⁻¹`. -/
theorem resolvent_identity {R R' H P K : Matrix ι ι ℂ} (hPR : P * R' = 1) (hRP : R' * P = 1)
    (hRK : R * K = 1) (hKR : K * R = 1) (hP : P = H + K) :
    R - R' = R * H * R - R * H * R' * H * R := by
  have hH : H = P - K := by rw [hP]; abel
  have hA : R * H * R' = R - R' := by
    rw [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc R P R', hPR, Matrix.mul_one, hRK,
      Matrix.one_mul]
  have hB : R' * H * R = R - R' := by
    rw [hH, Matrix.mul_sub, Matrix.sub_mul, hRP, Matrix.one_mul, Matrix.mul_assoc R' K R, hKR,
      Matrix.mul_one]
  have : R * H * R' * H * R = R * H * (R' * H * R) := by simp only [Matrix.mul_assoc]
  rw [this, hB, Matrix.mul_sub, hA]
  abel

/-- **The resolvent gap at one `s > 0`.** -/
theorem resolvent_gap {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i) {Z : Matrix ι ι ℂ} (hZ : Z.PosSemidef)
    {N : ℝ} (hN : 1 ≤ N) (hZN : ∀ v : ι → ℂ, (star v ⬝ᵥ (Z *ᵥ v)).re ≤ N * ∑ k, ‖v k‖ ^ 2)
    {s : ℝ} (hs : 0 < s) :
    (Fintype.card ι : ℝ) - s * ((sqDiag t * Z * sqDiag t + (s : ℂ) • 1)⁻¹).trace.re ≤
      ∑ i, t i / (t i + s) + s * ∑ i, t i / (t i + s) ^ 2 * ((Z i i).re - 1) -
        s / N * ∑ i, ∑ j, t i * t j / ((t i + s) ^ 2 * (t j + s)) *
          ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 := by
  have hts : ∀ i, 0 < t i + s := fun i => by linarith [ht0 i]
  have hN0 : 0 < N := by linarith
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = sqDiag t := ⟨_, rfl⟩
  rw [← hΔdef]
  obtain ⟨B, hBdef⟩ : ∃ B, B = Δ * Z * Δ := ⟨_, rfl⟩
  rw [← hBdef]
  obtain ⟨P, hPdef⟩ : ∃ P, P = B + (s : ℂ) • (1 : Matrix ι ι ℂ) := ⟨_, rfl⟩
  rw [← hPdef]
  obtain ⟨R', hR'def⟩ : ∃ R', R' = P⁻¹ := ⟨_, rfl⟩
  rw [← hR'def]
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix ι ι ℂ, D = diagonal fun i => ((t i : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ι → ℂ, r = fun i => (((t i + s)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Matrix ι ι ℂ, R = diagonal r := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H, H = B - D := ⟨_, rfl⟩
  have hΔ : Δᴴ = Δ := by rw [hΔdef]; exact sqDiag_conjTranspose t
  have hB : B.PosSemidef := by
    have := hZ.conjTranspose_mul_mul_same Δ
    rwa [hΔ, ← hBdef] at this
  have hPd : P.PosDef := by
    rw [hPdef]
    exact Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hs))
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPd.isUnit
  have hPR : P * R' = 1 := by rw [hR'def]; exact Matrix.mul_nonsing_inv P hPu
  have hRP : R' * P = 1 := by rw [hR'def]; exact Matrix.nonsing_inv_mul P hPu
  have hDs : D + (s : ℂ) • (1 : Matrix ι ι ℂ) = diagonal fun i => ((t i + s : ℝ) : ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hDdef]
    · simp [hDdef, h]
  have hRD : R * (D + (s : ℂ) • (1 : Matrix ι ι ℂ)) = 1 := by
    rw [hDs, hRdef, hrdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hts i).ne', Complex.ofReal_one]
  have hDR : (D + (s : ℂ) • (1 : Matrix ι ι ℂ)) * R = 1 := by
    rw [hDs, hRdef, hrdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hts i).ne', Complex.ofReal_one]
  have hPH : P = H + (D + (s : ℂ) • (1 : Matrix ι ι ℂ)) := by
    rw [hPdef, hHdef]; abel
  have hid := resolvent_identity hPR hRP hRD hDR hPH
  have hHh : H.IsHermitian := by
    rw [hHdef, hDdef]
    exact hB.1.sub (isHermitian_diagonal_of_self_adjoint _ (by
      funext j; simp [Complex.conj_ofReal]))
  -- entries
  have hBij : ∀ i j, B i j = ((Real.sqrt (t i) * Real.sqrt (t j) : ℝ) : ℂ) * Z i j := by
    intro i j
    rw [hBdef, hΔdef, sqDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
    push_cast; ring
  have hHij : ∀ i j, H i j = ((Real.sqrt (t i) * Real.sqrt (t j) : ℝ) : ℂ) *
      (Z i j - (1 : Matrix ι ι ℂ) i j) := by
    intro i j
    rw [hHdef, Matrix.sub_apply, hBij, hDdef]
    by_cases h : i = j
    · subst h
      rw [Real.mul_self_sqrt (ht0 i)]
      simp only [diagonal_apply_eq, Matrix.one_apply_eq]
      ring
    · simp [h]
  have hHn : ∀ i j, ‖H i j‖ ^ 2 = t i * t j * ‖Z i j - (1 : Matrix ι ι ℂ) i j‖ ^ 2 := by
    intro i j
    rw [hHij, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
      mul_pow, Real.sq_sqrt (ht0 i), Real.sq_sqrt (ht0 j)]
  -- traces
  have hR_tr : (R.trace).re = ∑ i, (t i + s)⁻¹ := by
    rw [hRdef, hrdef, trace_diagonal, Complex.re_sum]; simp only [Complex.ofReal_re]
  have hcard : (Fintype.card ι : ℝ) - s * ∑ i, (t i + s)⁻¹ = ∑ i, t i / (t i + s) := by
    rw [Finset.mul_sum, show (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) by simp,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hts i).ne'
    field_simp; ring
  have hrr : ∀ i, r i * r i = (((t i + s)⁻¹ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [hrdef]; push_cast; ring
  have hRHR : ((R * H * R).trace).re = ∑ i, t i / (t i + s) ^ 2 * ((Z i i).re - 1) := by
    rw [hRdef, trace_diag_mul_diag, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrr, Complex.re_ofReal_mul, hHij, Matrix.one_apply_eq, Real.mul_self_sqrt (ht0 i),
      Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
    have := (hts i).ne'
    field_simp
  -- the quadratic term
  have hP : P.IsHermitian := hPd.1
  have hPpos : ∀ w, 0 ≤ (star w ⬝ᵥ (P *ᵥ w)).re := fun w =>
    hPd.posSemidef.re_dotProduct_nonneg w
  have hcol : ∀ i, N⁻¹ * ∑ k, (t k + s)⁻¹ * ‖H k i‖ ^ 2 ≤
      (star (fun k => H k i) ⬝ᵥ (R' *ᵥ fun k => H k i)).re := by
    intro i
    obtain ⟨y, hy⟩ : ∃ y : ι → ℂ, y = fun k => H k i := ⟨_, rfl⟩
    rw [← hy]
    have hyk : ∀ k, ‖H k i‖ = ‖y k‖ := fun k => by rw [hy]
    simp only [hyk]
    obtain ⟨x, hx⟩ : ∃ x : ι → ℂ, x = fun k => (((N⁻¹ * (t k + s)⁻¹) : ℝ) : ℂ) * y k :=
      ⟨_, rfl⟩
    have hlow := quad_inv_lower hP hPpos hPR x y
    have hxy : (star x ⬝ᵥ y).re = N⁻¹ * ∑ k, (t k + s)⁻¹ * ‖y k‖ ^ 2 := by
      rw [hx]
      simp only [dotProduct, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [re_star_ofReal_mul]
      ring
    have hxk : ∀ k, ‖x k‖ ^ 2 = (N⁻¹ * (t k + s)⁻¹) ^ 2 * ‖y k‖ ^ 2 := by
      intro k
      rw [hx, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
        have := hts k
        positivity), mul_pow]
    have hxPx : (star x ⬝ᵥ (P *ᵥ x)).re ≤ N⁻¹ * ∑ k, (t k + s)⁻¹ * ‖y k‖ ^ 2 := by
      have hsplit : star x ⬝ᵥ (P *ᵥ x) = star (Δ *ᵥ x) ⬝ᵥ (Z *ᵥ (Δ *ᵥ x)) +
          (s : ℂ) * (star x ⬝ᵥ x) := by
        rw [hPdef, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul,
          smul_eq_mul]
        congr 1
        rw [hBdef, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, hΔ,
          dotProduct_mulVec]
      have hZv := hZN (Δ *ᵥ x)
      have hΔx : ∀ k, ‖(Δ *ᵥ x) k‖ ^ 2 = t k * ‖x k‖ ^ 2 := by
        intro k
        rw [hΔdef, sqDiag, mulVec_diagonal, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (ht0 k)]
      rw [hsplit, Complex.add_re, Complex.re_ofReal_mul, re_star_dot_self]
      simp only [hΔx] at hZv
      calc (star (Δ *ᵥ x) ⬝ᵥ (Z *ᵥ (Δ *ᵥ x))).re + s * ∑ k, ‖x k‖ ^ 2
          ≤ N * ∑ k, t k * ‖x k‖ ^ 2 + N * (s * ∑ k, ‖x k‖ ^ 2) := by
            have : s * ∑ k, ‖x k‖ ^ 2 ≤ N * (s * ∑ k, ‖x k‖ ^ 2) :=
              le_mul_of_one_le_left (by positivity) hN
            linarith
        _ = ∑ k, N * (t k + s) * ‖x k‖ ^ 2 := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ = N⁻¹ * ∑ k, (t k + s)⁻¹ * ‖y k‖ ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hxk]
            have := (hts k).ne'
            field_simp
    rw [hxy] at hlow
    linarith
  have hquad : N⁻¹ * ∑ i, ∑ j, t i * t j / ((t i + s) ^ 2 * (t j + s)) *
      ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 ≤ ((R * H * R' * H * R).trace).re := by
    have htr : ((R * H * R' * H * R).trace).re =
        ∑ i, ((t i + s)⁻¹) ^ 2 * (star (fun k => H k i) ⬝ᵥ (R' *ᵥ fun k => H k i)).re := by
      have e0 : R * H * R' * H * R = R * (H * R' * H) * R := by simp only [Matrix.mul_assoc]
      rw [e0, hRdef, trace_diag_mul_diag, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : (H * R' * H) i i = star (fun k => H k i) ⬝ᵥ (R' *ᵥ fun k => H k i) := by
        simp only [Matrix.mul_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [← hHh.apply k i, star_star]
        ring
      rw [hrr, Complex.re_ofReal_mul, e]
    rw [htr, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hcol i
    have hi2 : 0 ≤ ((t i + s)⁻¹) ^ 2 := by positivity
    calc N⁻¹ * ∑ j, t i * t j / ((t i + s) ^ 2 * (t j + s)) * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2
        = ((t i + s)⁻¹) ^ 2 * (N⁻¹ * ∑ k, (t k + s)⁻¹ * ‖H k i‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hHn k i]
          generalize ‖Z k i - (1 : Matrix ι ι ℂ) k i‖ ^ 2 = w
          rw [div_eq_mul_inv, mul_inv, inv_pow]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hi2
  -- assemble
  have h1 : (R'.trace).re = (R.trace).re - ((R * H * R).trace).re +
      ((R * H * R' * H * R).trace).re := by
    have := congrArg (fun M => (M.trace).re) hid
    simp only [trace_sub, Complex.sub_re] at this
    linarith
  rw [h1, hRHR]
  rw [hRHR] at h1
  have hs' : s / N * ∑ i, ∑ j, t i * t j / ((t i + s) ^ 2 * (t j + s)) *
      ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 ≤ s * ((R * H * R' * H * R).trace).re := by
    rw [div_eq_mul_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left hquad hs.le
  have := hcard
  rw [← hR_tr] at this
  nlinarith

/-- **The integrated concavity gap.** For `0 ≤ t ≤ 1`, `Z ⪰ 0`, `Z ⪯ N` (`N ≥ 1`):
`Tr (ΔZΔ)^p ≤ Σ t_i^p + c_pJ_p Σ t_i^p (Re Z_ii - 1)
  - (c_p/(27N)) Σ_{i,j : t_i ≤ t_j} t_i^p t_j^p |Z_ji - δ_ji|²`. -/
theorem fracTrace_sand_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t : ι → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) {Z : Matrix ι ι ℂ} (hZ : Z.PosSemidef) {N : ℝ}
    (hN : 1 ≤ N) (hZN : ∀ v : ι → ℂ, (star v ⬝ᵥ (Z *ᵥ v)).re ≤ N * ∑ k, ‖v k‖ ^ 2) :
    fracTrace p (sqDiag t * Z * sqDiag t) ≤ ∑ i, t i ^ p +
      cP p * jP p * ∑ i, t i ^ p * ((Z i i).re - 1) -
      cP p / (27 * N) * ∑ i, ∑ j, (if t i ≤ t j then
        t i ^ p * t j ^ p * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 else 0) := by
  have hN0 : 0 < N := by linarith
  have hB : (sqDiag t * Z * sqDiag t).PosSemidef := by
    have := hZ.conjTranspose_mul_mul_same (sqDiag t)
    rwa [sqDiag_conjTranspose] at this
  rw [fracTrace_eq_integral_psd hB hp0 hp1]
  obtain ⟨w, hw⟩ : ∃ w : ι → ι → ℝ, w = fun i j => ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ι → ℝ, a = fun i => (Z i i).re - 1 := ⟨_, rfl⟩
  have hw0 : ∀ i j, 0 ≤ w i j := fun i j => by rw [hw]; positivity
  set f : ℝ → ℝ := fun s => s ^ (p - 1) * ((Fintype.card ι : ℝ) -
    s * ((sqDiag t * Z * sqDiag t + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) with hf
  set g1 : ℝ → ℝ := fun s => ∑ i, s ^ (p - 1) * (t i / (t i + s)) with hg1
  set g2 : ℝ → ℝ := fun s => ∑ i, s ^ p * (t i / (t i + s) ^ 2) * a i with hg2
  set g3 : ℝ → ℝ := fun s => ∑ i, ∑ j, gapIntegrand p (t i) (t j) s * w i j with hg3
  have hfi : IntegrableOn f (Ioi 0) := integrableOn_fracTrace_integrand_psd hB hp0 hp1
  have hi1 : IntegrableOn g1 (Ioi 0) :=
    integrable_finsetSum _ fun i _ => integrableOn_rpow_mul_div_add' hp0 hp1 (ht0 i)
  have hi2 : IntegrableOn g2 (Ioi 0) :=
    integrable_finsetSum _ fun i _ => (integrableOn_lin hp0 hp1 (ht0 i)).mul_const _
  have hi3 : IntegrableOn g3 (Ioi 0) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrableOn_gap hp0 hp1 (ht0 i) (ht0 j)).mul_const _
  have hpt : ∀ s ∈ Ioi (0 : ℝ), f s ≤ g1 s + g2 s - N⁻¹ * g3 s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have h := resolvent_gap ht0 hZ hN hZN hs0
    have hsp : 0 < s ^ (p - 1) := rpow_pos_of_pos hs0 _
    have hss : s ^ (p - 1) * s = s ^ p := by
      rw [← rpow_add_one hs0.ne']; ring_nf
    have p1 : s ^ (p - 1) * ∑ i, t i / (t i + s) = g1 s := by rw [hg1, Finset.mul_sum]
    have p2 : s ^ (p - 1) * (s * ∑ i, t i / (t i + s) ^ 2 * ((Z i i).re - 1)) = g2 s := by
      rw [hg2, ha, ← mul_assoc, hss, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have p3 : s ^ (p - 1) * (s / N * ∑ i, ∑ j, t i * t j / ((t i + s) ^ 2 * (t j + s)) *
        ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2) = N⁻¹ * g3 s := by
      rw [hg3, hw, div_eq_mul_inv, ← mul_assoc, ← mul_assoc, hss, mul_comm (s ^ p), mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [gapIntegrand]; ring
    have e : s ^ (p - 1) * (∑ i, t i / (t i + s) + s * ∑ i, t i / (t i + s) ^ 2 * ((Z i i).re - 1) -
        s / N * ∑ i, ∑ j, t i * t j / ((t i + s) ^ 2 * (t j + s)) *
          ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2) = g1 s + g2 s - N⁻¹ * g3 s := by
      rw [mul_sub, mul_add, p1, p2, p3]
    calc f s = s ^ (p - 1) * ((Fintype.card ι : ℝ) -
          s * ((sqDiag t * Z * sqDiag t + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹).trace.re) := rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left h hsp.le
      _ = _ := e
  have hmono : ∫ s in Ioi (0 : ℝ), f s ≤ ∫ s in Ioi (0 : ℝ), (g1 s + g2 s - N⁻¹ * g3 s) :=
    setIntegral_mono_on hfi ((hi1.add hi2).sub (hi3.const_mul _)) measurableSet_Ioi hpt
  have hsplit : ∫ s in Ioi (0 : ℝ), (g1 s + g2 s - N⁻¹ * g3 s) =
      (∫ s in Ioi (0 : ℝ), g1 s) + (∫ s in Ioi (0 : ℝ), g2 s) -
        N⁻¹ * ∫ s in Ioi (0 : ℝ), g3 s := by
    rw [integral_sub (f := fun s => g1 s + g2 s) (g := fun s => N⁻¹ * g3 s) (hi1.add hi2)
      (hi3.const_mul _), integral_add hi1 hi2, integral_const_mul]
  have hI1 : cP p * ∫ s in Ioi (0 : ℝ), g1 s = ∑ i, t i ^ p := by
    rw [hg1, integral_finsetSum _ fun i _ => integrableOn_rpow_mul_div_add' hp0 hp1 (ht0 i),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (rpow_eq_integral' hp0 hp1 (ht0 i)).symm
  have hI2 : ∫ s in Ioi (0 : ℝ), g2 s = jP p * ∑ i, t i ^ p * ((Z i i).re - 1) := by
    rw [hg2, integral_finsetSum _ fun i _ => (integrableOn_lin hp0 hp1 (ht0 i)).mul_const _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, integral_lin hp0 (ht0 i), ha]
    ring
  have hI3 : (∑ i, ∑ j, (if t i ≤ t j then
        t i ^ p * t j ^ p * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 else 0)) / 27 ≤
      ∫ s in Ioi (0 : ℝ), g3 s := by
    rw [hg3, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrableOn_gap hp0 hp1 (ht0 i) (ht0 j)).mul_const _, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (integrableOn_gap hp0 hp1 (ht0 i) (ht0 j)).mul_const _,
      Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [integral_mul_const]
    have hg0 : 0 ≤ ∫ s in Ioi (0 : ℝ), gapIntegrand p (t i) (t j) s :=
      setIntegral_nonneg measurableSet_Ioi fun s hs => gapIntegrand_nonneg (ht0 i) (ht0 j) hs
    split_ifs with hij
    · have := gap_lower hp0 hp1 (ht0 i) hij (ht1 j)
      rw [hw]
      have hwij : 0 ≤ ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 := by positivity
      calc t i ^ p * t j ^ p * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 / 27 =
          t i ^ p * t j ^ p / 27 * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hwij
    · rw [zero_div]; exact mul_nonneg hg0 (hw0 i j)
  have hcP := cP_pos hp0 hp1
  calc cP p * ∫ s in Ioi (0 : ℝ), f s ≤ cP p * ∫ s in Ioi (0 : ℝ), (g1 s + g2 s - N⁻¹ * g3 s) :=
        mul_le_mul_of_nonneg_left hmono hcP.le
    _ = cP p * (∫ s in Ioi (0 : ℝ), g1 s) + cP p * (∫ s in Ioi (0 : ℝ), g2 s) -
        cP p * N⁻¹ * ∫ s in Ioi (0 : ℝ), g3 s := by rw [hsplit]; ring
    _ ≤ _ := by
        rw [hI1, hI2]
        have : cP p / (27 * N) * (∑ i, ∑ j, (if t i ≤ t j then
            t i ^ p * t j ^ p * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 else 0)) ≤
            cP p * N⁻¹ * ∫ s in Ioi (0 : ℝ), g3 s := by
          calc cP p / (27 * N) * (∑ i, ∑ j, (if t i ≤ t j then
              t i ^ p * t j ^ p * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 else 0)) =
              cP p * N⁻¹ * ((∑ i, ∑ j, (if t i ≤ t j then
              t i ^ p * t j ^ p * ‖Z j i - (1 : Matrix ι ι ℂ) j i‖ ^ 2 else 0)) / 27) := by
                field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left hI3 (by positivity)
        linarith

end BlockBand.Transmission.FractionalBulk
