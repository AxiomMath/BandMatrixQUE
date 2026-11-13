module

public import BlockBand.Endpoints.Poisson.SingleCollarDilation

/-!
# The sandwich Schatten bound `Tr|AᴴKA|^q ≤ Tr(AᴴA)^q` for a contraction `K`

Proof (no Horn inequality is formalized; the tensor-power trick replaces it):
* `scw_schattenFrac_sandwich_le_two`: `Tr|AᴴKA|^q ≤ 2 Tr(AᴴA)^q`. The Hermitian dilation
  `H = [[0, X], [Xᴴ, 0]]` of `X = AᴴKA` has `Tr H₊^q = Tr|X|^q` (`scw_fracTrace_offDiag`), and
  `diag(AᴴA, AᴴA) - H = YᴴY + Eᴴ(1 - KᴴK)E ⪰ 0`, so Weyl monotonicity (`fracTrace_mono`) gives
  `Tr|X|^q ≤ 2 Tr(AᴴA)^q`.
* `scw_schattenFrac_kronecker`, `scw_fracTrace_kronecker`: both sides are multiplicative under
  `⊗ₖ` (`A ↦ A ⊗ A`, `K ↦ K ⊗ K` keeps `K` a contraction), so
  `(Tr|X|^q)^(2^N) ≤ 2 (Tr(AᴴA)^q)^(2^N)` for every `N`, hence `Tr|X|^q ≤ Tr(AᴴA)^q`
  (`scw_schattenFrac_sandwich_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace)
open BlockBand.Endpoints.PhaseFractional (schattenFrac fracTrace_diagonal)
open scoped ComplexOrder Kronecker

section Trace

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `Tr (diag(A, D))^p = Tr A^p + Tr D^p`. -/
theorem scw_fracTrace_fromBlocks_diag (p : ℝ) (A : Matrix n n ℂ) (D : Matrix m m ℂ) :
    fracTrace p (fromBlocks A 0 0 D) = fracTrace p A + fracTrace p D := by
  unfold fracTrace
  rw [charpoly_fromBlocks_zero₁₂, Polynomial.roots_mul
    (mul_ne_zero A.charpoly_monic.ne_zero D.charpoly_monic.ne_zero), Multiset.map_add,
    Multiset.sum_add]

/-- Spectral form `A = U diag(λ) U*` of a Hermitian matrix. -/
theorem scw_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  have := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  exact this

theorem scw_rpow_pos_part_add {x p : ℝ} (hp : 0 < p) :
    max x 0 ^ p + max (-x) 0 ^ p = max (x * x) 0 ^ (p / 2) := by
  have hsq : ∀ y : ℝ, 0 ≤ y → (y * y) ^ (p / 2) = y ^ p := fun y hy => by
    rw [← sq, ← Real.rpow_natCast, ← Real.rpow_mul hy]; congr 1; push_cast; ring
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith), Real.zero_rpow hp.ne', add_zero,
      max_eq_left (mul_nonneg hx hx), hsq x hx]
  · rw [max_eq_right hx, max_eq_left (by linarith), Real.zero_rpow hp.ne', zero_add,
      max_eq_left (mul_nonneg_of_nonpos_of_nonpos hx hx), ← neg_mul_neg, hsq (-x) (by linarith)]

/-- For Hermitian `H` and `p > 0`: `Tr H₊^p + Tr H₋^p = Tr (H*H)^(p/2)`. -/
theorem scw_fracTrace_add_neg {H : Matrix n n ℂ} (hH : H.IsHermitian) {p : ℝ} (hp : 0 < p) :
    fracTrace p H + fracTrace p (-H) = fracTrace (p / 2) (H * H) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hU : U ∈ unitaryGroup n ℂ := hH.eigenvectorUnitary.2
  have hUU : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hs := scw_spectral hH
  set d : n → ℂ := fun i => (hH.eigenvalues i : ℂ)
  have hs : H = U * diagonal d * star U := scw_spectral hH
  have h1 : -H = U * diagonal (fun i => -d i) * star U := by
    conv_lhs => rw [hs]
    rw [show (diagonal (fun i => -d i) : Matrix n n ℂ) = -diagonal d by
      ext i j; by_cases h : i = j <;> simp [h]]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  have h2 : H * H = U * diagonal (fun i => d i * d i) * star U := by
    conv_lhs => rw [hs]
    rw [← diagonal_mul_diagonal]
    calc U * diagonal d * star U * (U * diagonal d * star U)
        = U * diagonal d * (star U * U) * diagonal d * star U := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h1, h2]
  conv_lhs => rw [hs]
  rw [fracTrace_unitary_conj _ _ hU, fracTrace_unitary_conj _ _ hU, fracTrace_unitary_conj _ _ hU,
    fracTrace_diagonal, fracTrace_diagonal, fracTrace_diagonal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [d, Complex.neg_re, Complex.ofReal_re, ← Complex.ofReal_mul]
  exact scw_rpow_pos_part_add hp

/-- The Hermitian dilation `[[0, X], [Xᴴ, 0]]` has `Tr H₊^p = Tr |X|^p` (`p > 0`). -/
theorem scw_fracTrace_offDiag (X : Matrix n n ℂ) {p : ℝ} (hp : 0 < p) :
    fracTrace p (fromBlocks 0 X Xᴴ 0) = schattenFrac p X := by
  set H : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 0 X Xᴴ 0
  have hH : H.IsHermitian := by
    simp only [H, IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero,
      conjTranspose_conjTranspose]
  set J : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 1 0 0 (-1)
  have hJs : star J = J := by
    simp only [J, star_eq_conjTranspose, fromBlocks_conjTranspose, conjTranspose_zero,
      conjTranspose_one, conjTranspose_neg]
  have hJ : J ∈ unitaryGroup (n ⊕ n) ℂ := by
    rw [mem_unitaryGroup_iff', hJs]
    simp only [J, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.mul_neg, neg_neg, neg_zero, fromBlocks_one]
  have hneg : -H = J * H * star J := by
    rw [hJs]
    simp only [H, J, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_zero, fromBlocks_neg]
  have hsq : H * H = fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
    simp only [H, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have h := scw_fracTrace_add_neg hH hp
  rw [hneg, fracTrace_unitary_conj _ _ hJ, hsq, scw_fracTrace_fromBlocks_diag,
    fracTrace_mul_comm (p / 2) X Xᴴ] at h
  unfold schattenFrac
  linarith

/-- `Tr (P ⊗ P')^p = Tr P^p Tr P'^p` for PSD `P`, `P'`. -/
theorem scw_fracTrace_kronecker {P : Matrix n n ℂ} {P' : Matrix m m ℂ} (hP : P.PosSemidef)
    (hP' : P'.PosSemidef) (p : ℝ) :
    fracTrace p (P ⊗ₖ P') = fracTrace p P * fracTrace p P' := by
  set U : Matrix n n ℂ := (hP.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set U' : Matrix m m ℂ := (hP'.isHermitian.eigenvectorUnitary : Matrix m m ℂ)
  have hU : U ∈ unitaryGroup n ℂ := hP.isHermitian.eigenvectorUnitary.2
  have hU' : U' ∈ unitaryGroup m ℂ := hP'.isHermitian.eigenvectorUnitary.2
  set d : n → ℂ := fun i => (hP.isHermitian.eigenvalues i : ℂ)
  set d' : m → ℂ := fun i => (hP'.isHermitian.eigenvalues i : ℂ)
  have hs := scw_spectral hP.isHermitian
  have hs' := scw_spectral hP'.isHermitian
  have hstar : star (U ⊗ₖ U') = star U ⊗ₖ star U' := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker]
  have hUU : U ⊗ₖ U' ∈ unitaryGroup (n × m) ℂ := by
    rw [mem_unitaryGroup_iff', hstar, ← mul_kronecker_mul, mem_unitaryGroup_iff'.mp hU,
      mem_unitaryGroup_iff'.mp hU', one_kronecker_one]
  have hk : P ⊗ₖ P' = (U ⊗ₖ U') * diagonal (fun x => d x.1 * d' x.2) * star (U ⊗ₖ U') := by
    rw [hstar, ← diagonal_kronecker_diagonal, ← mul_kronecker_mul, ← mul_kronecker_mul]
    conv_lhs => rw [hs, hs']
  rw [hk, fracTrace_unitary_conj _ _ hUU, fracTrace_diagonal,
    fracTrace_eq_sum_eigenvalues_of_posSemidef hP, fracTrace_eq_sum_eigenvalues_of_posSemidef hP',
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi := hP.eigenvalues_nonneg i
  have hj := hP'.eigenvalues_nonneg j
  simp only [d, d', ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [max_eq_left (mul_nonneg hi hj), Real.mul_rpow hi hj]

/-- `Tr |X ⊗ Y|^p = Tr |X|^p Tr |Y|^p`. -/
theorem scw_schattenFrac_kronecker (X : Matrix n n ℂ) (Y : Matrix m m ℂ) (p : ℝ) :
    schattenFrac p (X ⊗ₖ Y) = schattenFrac p X * schattenFrac p Y := by
  unfold schattenFrac
  rw [conjTranspose_kronecker, ← mul_kronecker_mul]
  exact scw_fracTrace_kronecker (posSemidef_conjTranspose_mul_self X)
    (posSemidef_conjTranspose_mul_self Y) _

end Trace

section Sandwich

/-- **Constant-two sandwich bound.** For `A : ν × π`, `K` a contraction (`1 - KᴴK ⪰ 0`) and
`p > 0`: `Tr |AᴴKA|^p ≤ 2 Tr (AᴴA)^p`. -/
theorem scw_schattenFrac_sandwich_le_two {ν π : Type*} [Fintype ν] [DecidableEq ν] [Fintype π]
    [DecidableEq π] (A : Matrix ν π ℂ) {K : Matrix ν ν ℂ} (hK : (1 - Kᴴ * K).PosSemidef)
    {p : ℝ} (hp : 0 < p) :
    schattenFrac p (Aᴴ * K * A) ≤ 2 * fracTrace p (Aᴴ * A) := by
  set X := Aᴴ * K * A
  set Y : Matrix (ν ⊕ ν) (π ⊕ π) ℂ := fromBlocks A (-(K * A)) 0 0
  set E : Matrix ν (π ⊕ π) ℂ := Matrix.of fun k j => Sum.elim (fun _ => 0) (fun j => A k j) j
  have hY : Yᴴ * Y = fromBlocks (Aᴴ * A) (-X) (-Xᴴ) (Aᴴ * (Kᴴ * (K * A))) := by
    simp only [Y, X, fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      Matrix.mul_zero, add_zero, conjTranspose_neg, conjTranspose_mul, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, Matrix.mul_assoc, conjTranspose_conjTranspose]
  have hE : Eᴴ * (1 - Kᴴ * K) * E = fromBlocks 0 0 0 (Aᴴ * (1 - Kᴴ * K) * A) := by
    ext (i | i) (j | j) <;> simp [E, Matrix.mul_apply]
  have hdiff : fromBlocks (Aᴴ * A) 0 0 (Aᴴ * A) - fromBlocks 0 X Xᴴ 0 =
      Yᴴ * Y + Eᴴ * (1 - Kᴴ * K) * E := by
    rw [hY, hE]
    ext (i | i) (j | j) <;>
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hpsd : (fromBlocks (Aᴴ * A) 0 0 (Aᴴ * A) - fromBlocks 0 X Xᴴ 0).PosSemidef := by
    rw [hdiff]
    exact (posSemidef_conjTranspose_mul_self Y).add (hK.conjTranspose_mul_mul_same E)
  have hH : (fromBlocks 0 X Xᴴ 0 : Matrix (π ⊕ π) (π ⊕ π) ℂ).IsHermitian := by
    simp only [IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero,
      conjTranspose_conjTranspose]
  have hD : (fromBlocks (Aᴴ * A) 0 0 (Aᴴ * A)).IsHermitian := by
    have h := (posSemidef_conjTranspose_mul_self A).isHermitian
    simp only [IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero, h.eq]
  have hmono := fracTrace_mono hH hD hpsd hp.le
  rw [scw_fracTrace_offDiag X hp, scw_fracTrace_fromBlocks_diag] at hmono
  linarith

theorem scw_contraction_kronecker {ν ν' : Type*} [Fintype ν] [DecidableEq ν] [Fintype ν']
    [DecidableEq ν'] {K : Matrix ν ν ℂ} {K' : Matrix ν' ν' ℂ} (hK : (1 - Kᴴ * K).PosSemidef)
    (hK' : (1 - K'ᴴ * K').PosSemidef) : (1 - (K ⊗ₖ K')ᴴ * (K ⊗ₖ K')).PosSemidef := by
  have heq : 1 - (K ⊗ₖ K')ᴴ * (K ⊗ₖ K') =
      (1 - Kᴴ * K) ⊗ₖ (1 : Matrix ν' ν' ℂ) + (Kᴴ * K) ⊗ₖ (1 - K'ᴴ * K') := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← one_kronecker_one]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, kronecker_apply]
    ring
  rw [heq]
  exact (hK.kronecker PosSemidef.one).add
    ((posSemidef_conjTranspose_mul_self K).kronecker hK')

/-- The tensor-power iterate: `(Tr |AᴴKA|^p)^(2^N) ≤ 2 (Tr (AᴴA)^p)^(2^N)`. -/
theorem scw_sandwich_pow (N : ℕ) : ∀ {ν π : Type} [Fintype ν] [DecidableEq ν] [Fintype π]
    [DecidableEq π] (A : Matrix ν π ℂ) {K : Matrix ν ν ℂ}, (1 - Kᴴ * K).PosSemidef →
    ∀ {p : ℝ}, 0 < p →
      schattenFrac p (Aᴴ * K * A) ^ (2 ^ N) ≤ 2 * fracTrace p (Aᴴ * A) ^ (2 ^ N) := by
  induction N with
  | zero =>
    intro ν π _ _ _ _ A K hK p hp
    simpa using scw_schattenFrac_sandwich_le_two A hK hp
  | succ N ih =>
    intro ν π _ _ _ _ A K hK p hp
    have h := ih (A ⊗ₖ A) (scw_contraction_kronecker hK hK) hp
    have hX : (A ⊗ₖ A)ᴴ * (K ⊗ₖ K) * (A ⊗ₖ A) = (Aᴴ * K * A) ⊗ₖ (Aᴴ * K * A) := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
    have hA : (A ⊗ₖ A)ᴴ * (A ⊗ₖ A) = (Aᴴ * A) ⊗ₖ (Aᴴ * A) := by
      rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    rw [hX, hA, scw_schattenFrac_kronecker,
      scw_fracTrace_kronecker (posSemidef_conjTranspose_mul_self A)
        (posSemidef_conjTranspose_mul_self A)] at h
    rw [mul_pow, mul_pow] at h
    rw [pow_succ, pow_mul, pow_mul]
    simpa only [sq] using h

/-- **The sandwich Schatten bound.** For `A : ν × π`, a contraction `K` (`1 - KᴴK ⪰ 0`) and
`p > 0`: `Tr |AᴴKA|^p ≤ Tr (AᴴA)^p` (weak log-majorization of `s(AᴴKA)` by `λ(AᴴA)`, through
the tensor-power trick). -/
theorem scw_schattenFrac_sandwich_le {ν π : Type} [Fintype ν] [DecidableEq ν] [Fintype π]
    [DecidableEq π] (A : Matrix ν π ℂ) {K : Matrix ν ν ℂ} (hK : (1 - Kᴴ * K).PosSemidef)
    {p : ℝ} (hp : 0 < p) : schattenFrac p (Aᴴ * K * A) ≤ fracTrace p (Aᴴ * A) := by
  set s := schattenFrac p (Aᴴ * K * A)
  set f := fracTrace p (Aᴴ * A)
  have hs : 0 ≤ s := BlockBand.Endpoints.fracTrace_nonneg _ _
  have hf : 0 ≤ f := BlockBand.Endpoints.fracTrace_nonneg _ _
  have hN := fun N => scw_sandwich_pow N A hK hp
  by_contra hlt
  rw [not_le] at hlt
  rcases hf.eq_or_lt with hf0 | hf0
  · have h0 := hN 0
    simp only [pow_zero, pow_one] at h0
    change s ≤ 2 * f at h0
    rw [← hf0] at h0 hlt
    linarith
  · set a := s / f - 1
    have ha : 0 < a := by
      simp only [a, sub_pos]; rwa [one_lt_div hf0]
    obtain ⟨N, hN1⟩ := exists_nat_gt (1 / a)
    have hpow := hN (N)
    have hb : (s / f) ^ (2 ^ N) ≤ 2 := by
      rw [div_pow, div_le_iff₀ (pow_pos hf0 _)]; exact hpow
    have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ a by linarith) (2 ^ N)
    rw [show 1 + a = s / f by simp [a]] at hbern
    have h2N : (N : ℝ) < ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
    have h1 : 1 < (N : ℝ) * a := by rwa [div_lt_iff₀ ha] at hN1
    have h3 : (N : ℝ) * a < ((2 ^ N : ℕ) : ℝ) * a := mul_lt_mul_of_pos_right h2N ha
    linarith

end Sandwich

end BlockBand.Endpoints
