module

public import BlockBand.Prelude
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Trace-norm bounds by duality, Hilbert–Schmidt sums and accretive inverses

* `TraceBound D r` (`0 ≤ r` and `|Tr(C D)| ≤ ‖C‖ r` for every square `C`) is the statement
  `‖D‖₁ ≤ r` for the trace norm `‖·‖₁`, through the duality `‖D‖₁ = sup_{‖C‖ ≤ 1} |Tr(C D)|`. It
  is closed under sums, scalar multiples, adjoints and two-sided multiplication
  (`‖A D B‖₁ ≤ ‖A‖ ‖B‖ ‖D‖₁`), it dominates the operator norm (`TraceBound.norm_le`), and the
  Gram bound `‖N* X N‖₁ ≤ ‖X‖ Tr(N* N)` holds (`traceBound_gram`).
* `accretive_isUnit_norm_inv_le`: if `Re⟨v, A v⟩ ≥ c |v|²` with `c > 0`, then `A` is invertible
  and `‖A⁻¹‖ ≤ c⁻¹`. This gives the contraction of `(I + iκK_q/W²)⁻¹` (`-Im K_q ⪰ 0`) and the
  bound `‖(I - yT)⁻¹‖ ≤ (1-y)⁻¹` on `0 ⪯ T ⪯ I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

section VecNorm

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Squared Euclidean norm `Σ_i |v_i|²` of a complex vector. -/
def vecNormSq (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem vecNormSq_nonneg (v : n → ℂ) : 0 ≤ vecNormSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem vecNormSq_eq_norm_sq (v : n → ℂ) :
    vecNormSq v = ‖(EuclideanSpace.equiv n ℂ).symm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rfl

theorem vecNormSq_eq_zero {v : n → ℂ} (h : vecNormSq v = 0) : v = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖v j‖)).1 h i
    (Finset.mem_univ i)
  simpa using this

theorem vecNormSq_smul (a : ℂ) (v : n → ℂ) : vecNormSq (a • v) = ‖a‖ ^ 2 * vecNormSq v := by
  simp only [vecNormSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem star_dotProduct_self (v : n → ℂ) : star v ⬝ᵥ v = (vecNormSq v : ℂ) := by
  simp only [dotProduct, vecNormSq, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- Cauchy–Schwarz for `⟨u, w⟩ = star u ⬝ᵥ w`. -/
theorem norm_star_dotProduct_sq_le (u w : n → ℂ) :
    ‖star u ⬝ᵥ w‖ ^ 2 ≤ vecNormSq u * vecNormSq w := by
  have h1 : ‖star u ⬝ᵥ w‖ ≤ ∑ i, ‖u i‖ * ‖w i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  calc ‖star u ⬝ᵥ w‖ ^ 2 ≤ (∑ i, ‖u i‖ * ‖w i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem star_dotProduct_mulVec_eq (A : Matrix m n ℂ) (u : m → ℂ) (v : n → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = star (Aᴴ *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

theorem star_dotProduct_conjTranspose_mulVec (A : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (Aᴴ *ᵥ v) = star (star v ⬝ᵥ (A *ᵥ v)) := by
  rw [star_dotProduct_mulVec_eq, conjTranspose_conjTranspose, star_dotProduct]

theorem star_dotProduct_gram_mulVec (A : Matrix m n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((Aᴴ * A) *ᵥ v) = (vecNormSq (A *ᵥ v) : ℂ) := by
  rw [← mulVec_mulVec, star_dotProduct_mulVec_eq, conjTranspose_conjTranspose,
    star_dotProduct_self]

/-- Squared Hilbert–Schmidt norm `Σ_{i,j} |Y_ij|²`. -/
def hsSq {k l : Type*} [Fintype k] [Fintype l] (Y : Matrix k l ℂ) : ℝ := ∑ i, ∑ j, ‖Y i j‖ ^ 2

theorem hsSq_nonneg {k l : Type*} [Fintype k] [Fintype l] (Y : Matrix k l ℂ) : 0 ≤ hsSq Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem hsSq_conjTranspose {k l : Type*} [Fintype k] [Fintype l] (Y : Matrix k l ℂ) :
    hsSq Yᴴ = hsSq Y := by
  unfold hsSq
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

theorem trace_conjTranspose_mul_self_eq_hsSq (N : Matrix m n ℂ) :
    (Nᴴ * N).trace = ((hsSq N : ℝ) : ℂ) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, hsSq]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

theorem trace_conjTranspose_mul_self_re_eq_hsSq (N : Matrix m n ℂ) :
    (Nᴴ * N).trace.re = hsSq N := by
  rw [trace_conjTranspose_mul_self_eq_hsSq, Complex.ofReal_re]

/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing. -/
theorem norm_hsPairing_sq_le {k l : Type*} [Fintype k] [Fintype l] (N P : Matrix k l ℂ) :
    ‖∑ i, ∑ j, star (N i j) * P i j‖ ^ 2 ≤ hsSq N * hsSq P := by
  have h := norm_star_dotProduct_sq_le (fun x : k × l => N x.1 x.2) (fun x => P x.1 x.2)
  simpa only [dotProduct, vecNormSq, hsSq, Pi.star_apply, Fintype.sum_prod_type] using h

end VecNorm

section OpNorm

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem vecNormSq_mulVec_le (A : Matrix m n ℂ) (v : n → ℂ) :
    vecNormSq (A *ᵥ v) ≤ ‖A‖ ^ 2 * vecNormSq v := by
  have h := l2_opNorm_mulVec A ((EuclideanSpace.equiv n ℂ).symm v)
  rw [vecNormSq_eq_norm_sq, vecNormSq_eq_norm_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem l2_opNorm_le_of_vecNormSq {A : Matrix m n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, vecNormSq (A *ᵥ v) ≤ c ^ 2 * vecNormSq v) : ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have hx := h x.ofLp
  rw [vecNormSq_eq_norm_sq, vecNormSq_eq_norm_sq, ← mul_pow] at hx
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hx
  simpa [Matrix.toLpLin_apply] using this

theorem l2_opNorm_le_one_of_contraction {A : Matrix m n ℂ}
    (h : ∀ v, vecNormSq (A *ᵥ v) ≤ vecNormSq v) : ‖A‖ ≤ 1 :=
  l2_opNorm_le_of_vecNormSq zero_le_one fun v => by simpa using h v

theorem l2_opNorm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
  l2_opNorm_le_one_of_contraction fun v => by simp

/-- Hilbert–Schmidt bound `‖X Y‖_HS ≤ ‖X‖ ‖Y‖_HS`. -/
theorem hsSq_mul_le {l : Type*} [Fintype l] (X : Matrix m n ℂ) (Y : Matrix n l ℂ) :
    hsSq (X * Y) ≤ ‖X‖ ^ 2 * hsSq Y := by
  have hcol : ∀ j, ∑ i, ‖(X * Y) i j‖ ^ 2 = vecNormSq (X *ᵥ fun i => Y i j) := by
    intro j
    rfl
  unfold hsSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖Y i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [hcol]
  exact vecNormSq_mulVec_le X _

/-- Hilbert–Schmidt bound `‖Y C‖_HS ≤ ‖Y‖_HS ‖C‖`. -/
theorem hsSq_mul_le_right {l : Type*} [Fintype l] [DecidableEq l] (Y : Matrix m n ℂ)
    (C : Matrix n l ℂ) : hsSq (Y * C) ≤ hsSq Y * ‖C‖ ^ 2 := by
  rw [← hsSq_conjTranspose, conjTranspose_mul, ← hsSq_conjTranspose Y, mul_comm,
    ← l2_opNorm_conjTranspose C]
  exact hsSq_mul_le _ _

omit [DecidableEq n] in
/-- Accretive matrices: `Re⟨v, A v⟩ ≥ c|v|²`, `c > 0`, gives `|A v|² ≥ c² |v|²`. -/
theorem vecNormSq_le_of_accretive {A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * vecNormSq v ≤ (star v ⬝ᵥ (A *ᵥ v)).re) (v : n → ℂ) :
    c ^ 2 * vecNormSq v ≤ vecNormSq (A *ᵥ v) := by
  have h0 : 0 ≤ c * vecNormSq v := mul_nonneg hc.le (vecNormSq_nonneg v)
  have h1 : (c * vecNormSq v) ^ 2 ≤ vecNormSq v * vecNormSq (A *ᵥ v) :=
    (pow_le_pow_left₀ h0 ((h v).trans (Complex.re_le_norm _)) 2).trans
      (norm_star_dotProduct_sq_le v _)
  rcases (vecNormSq_nonneg v).lt_or_eq with hv | hv
  · have : vecNormSq v * (c ^ 2 * vecNormSq v) ≤ vecNormSq v * vecNormSq (A *ᵥ v) := by
      nlinarith
    exact le_of_mul_le_mul_left this hv
  · rw [← hv, mul_zero]
    exact vecNormSq_nonneg _

/-- **Accretive inverse.** If `Re⟨v, A v⟩ ≥ c |v|²` for all `v` with `c > 0`, then `A` is
invertible and `‖A⁻¹‖ ≤ c⁻¹` (`L²` operator norm).
-/
theorem accretive_isUnit_norm_inv_le {A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * vecNormSq v ≤ (star v ⬝ᵥ (A *ᵥ v)).re) : IsUnit A ∧ ‖A⁻¹‖ ≤ c⁻¹ := by
  have hlow := vecNormSq_le_of_accretive hc h
  have hinj : Function.Injective A.mulVec := by
    intro v w hvw
    have h0 : A *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
    have h1 := hlow (v - w)
    rw [h0] at h1
    have h2 : vecNormSq (0 : n → ℂ) = 0 := by simp [vecNormSq]
    rw [h2] at h1
    have h3 : vecNormSq (v - w) = 0 :=
      le_antisymm (by nlinarith [vecNormSq_nonneg (v - w), pow_pos hc 2]) (vecNormSq_nonneg _)
    exact sub_eq_zero.1 (vecNormSq_eq_zero h3)
  have hA : IsUnit A := mulVec_injective_iff_isUnit.1 hinj
  refine ⟨hA, l2_opNorm_le_of_vecNormSq (inv_nonneg.2 hc.le) fun u => ?_⟩
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have hu : A *ᵥ (A⁻¹ *ᵥ u) = u := by rw [mulVec_mulVec, mul_nonsing_inv A hd, one_mulVec]
  have := hlow (A⁻¹ *ᵥ u)
  rw [hu] at this
  rw [inv_pow]
  rw [le_inv_mul_iff₀ (by positivity)]
  exact this

end OpNorm

section TraceBound

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `TraceBound D r`:
`‖D‖₁ ≤ r` in trace norm, through the duality
`‖D‖₁ = sup_{‖C‖ ≤ 1} |Tr(C D)|` (`L²` operator norm on `C`).
-/
def TraceBound (D : Matrix n n ℂ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ C : Matrix n n ℂ, ‖(C * D).trace‖ ≤ ‖C‖ * r

theorem traceBound_zero : TraceBound (0 : Matrix n n ℂ) 0 :=
  ⟨le_rfl, fun C => by simp⟩

theorem TraceBound.nonneg {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) : 0 ≤ r := h.1

theorem TraceBound.trace_le {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) (C : Matrix n n ℂ) :
    ‖(C * D).trace‖ ≤ ‖C‖ * r := h.2 C

theorem TraceBound.mono {D : Matrix n n ℂ} {r r' : ℝ} (h : TraceBound D r) (hr : r ≤ r') :
    TraceBound D r' :=
  ⟨h.1.trans hr, fun C => (h.2 C).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg C))⟩

theorem TraceBound.add {D₁ D₂ : Matrix n n ℂ} {r₁ r₂ : ℝ} (h₁ : TraceBound D₁ r₁)
    (h₂ : TraceBound D₂ r₂) : TraceBound (D₁ + D₂) (r₁ + r₂) := by
  refine ⟨add_nonneg h₁.1 h₂.1, fun C => ?_⟩
  rw [mul_add, trace_add, mul_add]
  exact (norm_add_le _ _).trans (add_le_add (h₁.2 C) (h₂.2 C))

theorem TraceBound.smul {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) (a : ℂ) :
    TraceBound (a • D) (‖a‖ * r) := by
  refine ⟨mul_nonneg (norm_nonneg a) h.1, fun C => ?_⟩
  rw [mul_smul_comm, trace_smul, smul_eq_mul, norm_mul]
  calc ‖a‖ * ‖(C * D).trace‖ ≤ ‖a‖ * (‖C‖ * r) :=
        mul_le_mul_of_nonneg_left (h.2 C) (norm_nonneg a)
    _ = ‖C‖ * (‖a‖ * r) := by ring

theorem TraceBound.neg {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) :
    TraceBound (-D) r := by
  have := h.smul (-1)
  simpa using this

theorem TraceBound.sub {D₁ D₂ : Matrix n n ℂ} {r₁ r₂ : ℝ} (h₁ : TraceBound D₁ r₁)
    (h₂ : TraceBound D₂ r₂) : TraceBound (D₁ - D₂) (r₁ + r₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

/-- Two-sided multiplication: `‖A D B‖₁ ≤ ‖A‖ ‖B‖ ‖D‖₁` (rectangular `A`, `B`). -/
theorem TraceBound.mul_mul {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) (A : Matrix m n ℂ)
    (B : Matrix n m ℂ) : TraceBound (A * D * B) (‖A‖ * ‖B‖ * r) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h.1, fun C => ?_⟩
  have htr : (C * (A * D * B)).trace = ((B * C * A) * D).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc B C A]
  rw [htr]
  calc ‖((B * C * A) * D).trace‖ ≤ ‖B * C * A‖ * r := h.2 _
    _ ≤ (‖B‖ * ‖C‖ * ‖A‖) * r := by
        refine mul_le_mul_of_nonneg_right ?_ h.1
        calc ‖B * C * A‖ ≤ ‖B * C‖ * ‖A‖ := l2_opNorm_mul _ _
          _ ≤ ‖B‖ * ‖C‖ * ‖A‖ :=
            mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖C‖ * (‖A‖ * ‖B‖ * r) := by ring

theorem TraceBound.mul_left {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) (A : Matrix n n ℂ) :
    TraceBound (A * D) (‖A‖ * r) := by
  have := h.mul_mul A 1
  rw [Matrix.mul_one] at this
  exact this.mono (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg A) l2_opNorm_one_le) h.1)

theorem TraceBound.mul_right {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) (B : Matrix n n ℂ) :
    TraceBound (D * B) (‖B‖ * r) := by
  have := h.mul_mul 1 B
  rw [Matrix.one_mul] at this
  exact this.mono (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg B) l2_opNorm_one_le) h.1)

theorem TraceBound.conjTranspose {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) :
    TraceBound Dᴴ r := by
  refine ⟨h.1, fun C => ?_⟩
  have htr : (C * Dᴴ).trace = star ((Cᴴ * D).trace) := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, trace_mul_comm]
  rw [htr, norm_star, ← l2_opNorm_conjTranspose C]
  exact h.2 _

/-- Gram bound `‖N* X N‖₁ ≤ ‖X‖ Tr(N* N)`. -/
theorem traceBound_gram {k : Type*} [Fintype k] [DecidableEq k] (N : Matrix k n ℂ)
    (X : Matrix k k ℂ) : TraceBound (Nᴴ * X * N) (‖X‖ * (Nᴴ * N).trace.re) := by
  rw [trace_conjTranspose_mul_self_re_eq_hsSq]
  refine ⟨mul_nonneg (norm_nonneg _) (hsSq_nonneg _), fun C => ?_⟩
  set P := X * N * C
  have htr : (C * (Nᴴ * X * N)).trace = ∑ i, ∑ j, star (N i j) * P i j := by
    have : (C * (Nᴴ * X * N)).trace = (Nᴴ * P).trace := by
      rw [trace_mul_comm]
      simp only [P, Matrix.mul_assoc]
    rw [this]
    simp only [trace, diag, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
  have hP' : hsSq (X * (N * C)) ≤ ‖X‖ ^ 2 * (hsSq N * ‖C‖ ^ 2) :=
    (hsSq_mul_le X (N * C)).trans
      (mul_le_mul_of_nonneg_left (hsSq_mul_le_right N C) (sq_nonneg _))
  have hP : hsSq P ≤ ‖X‖ ^ 2 * (hsSq N * ‖C‖ ^ 2) := by
    simp only [P, Matrix.mul_assoc]
    exact hP'
  have hsq : ‖(C * (Nᴴ * X * N)).trace‖ ^ 2 ≤ (‖C‖ * (‖X‖ * hsSq N)) ^ 2 := by
    rw [htr]
    calc _ ≤ hsSq N * hsSq P := norm_hsPairing_sq_le N P
      _ ≤ hsSq N * (‖X‖ ^ 2 * (hsSq N * ‖C‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hP (hsSq_nonneg N)
      _ = (‖C‖ * (‖X‖ * hsSq N)) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (hsSq_nonneg _))) two_ne_zero).1 hsq

omit [DecidableEq n] in
theorem trace_vecMulVec_mul (v w : n → ℂ) (D : Matrix n n ℂ) :
    (vecMulVec v (star w) * D).trace = star w ⬝ᵥ (D *ᵥ v) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem l2_opNorm_vecMulVec_le (v w : n → ℂ) :
    ‖vecMulVec v (star w)‖ ≤ Real.sqrt (vecNormSq v * vecNormSq w) := by
  refine l2_opNorm_le_of_vecNormSq (Real.sqrt_nonneg _) fun z => ?_
  have hz : vecMulVec v (star w) *ᵥ z = (star w ⬝ᵥ z) • v := by
    funext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hz, vecNormSq_smul, Real.sq_sqrt (mul_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))]
  have := norm_star_dotProduct_sq_le w z
  have := vecNormSq_nonneg v
  nlinarith

/-- The trace norm dominates the operator norm: `‖D‖ ≤ ‖D‖₁`. -/
theorem TraceBound.norm_le {D : Matrix n n ℂ} {r : ℝ} (h : TraceBound D r) : ‖D‖ ≤ r := by
  refine l2_opNorm_le_of_vecNormSq h.1 fun v => ?_
  set w := D *ᵥ v
  have h1 : vecNormSq w ≤ Real.sqrt (vecNormSq v * vecNormSq w) * r := by
    have := h.2 (vecMulVec v (star w))
    rw [trace_vecMulVec_mul, star_dotProduct_self, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vecNormSq_nonneg _)] at this
    exact this.trans (mul_le_mul_of_nonneg_right (l2_opNorm_vecMulVec_le v w) h.1)
  have h2 : vecNormSq w ^ 2 ≤ vecNormSq v * vecNormSq w * r ^ 2 := by
    have h0 : 0 ≤ vecNormSq w := vecNormSq_nonneg _
    calc vecNormSq w ^ 2 ≤ (Real.sqrt (vecNormSq v * vecNormSq w) * r) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = vecNormSq v * vecNormSq w * r ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg (vecNormSq_nonneg _) h0)]
  rcases (vecNormSq_nonneg w).lt_or_eq with hw | hw
  · have : vecNormSq w * vecNormSq w ≤ vecNormSq w * (r ^ 2 * vecNormSq v) := by nlinarith
    exact le_of_mul_le_mul_left this hw
  · rw [← hw]
    exact mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)

end TraceBound

end BlockBand.Endpoints
