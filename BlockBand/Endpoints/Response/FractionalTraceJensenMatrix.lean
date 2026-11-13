module

public import BlockBand.Endpoints.Response.FractionalTraceJensenScalar

/-!
# Deterministic matrix inputs of the fractional trace Jensen gap

All statements are deterministic (finite index type `n`, complex matrices, Loewner order via
`PosSemidef`). Every matrix is handled through an explicit eigendecomposition
`ftj_spec U a = U diag(a) U*`, so no functional calculus or derivative is used.

* `ftj_trace_spec_spec`: `Tr(U diag a U* · W diag b W*) = Σ_{ij} a_i b_j |(U*W)_ij|²`;
* `ftj_trace_spec_sandwich`: `Tr(U diag a U* Δ W diag b W* Δ) = Σ_{ij} a_i b_j |(U*ΔW)_ij|²`;
* `ftj_klein`: Klein's inequality for `Tr(·)^p`, `0 ≤ p ≤ 1`, with the gradient
  `ftj_grad p U x = U diag(p x^{p-1}) U*`;
* `ftj_resolvent_sub_posSemidef`: `(X+s)⁻¹ - (Q+s)⁻¹ ⪰ 0` for `X ⪯ Q`, by the purely
  algebraic identity `R - P = P(Q-X)P + P(Q-X)R(Q-X)P`;
* `ftj_trace_mono_two`: monotonicity of `(A, B) ↦ Re Tr(AΔBΔ)` on PSD pairs;
* `ftj_grad_monotone`: the monotone-gradient gap
  `Re Tr((∇X - ∇Y)(Y - X)) ≥ (p/K_p) Σ_{kl} |(V*(Y-X)V)_kl|² ∫_0^∞ k_p(q_k, q_l)`
  for `X, Y ⪯ Q = V diag(q) V*`;
* `ftj_core_gap`: the pathwise second-order Jensen gap (two Klein steps through the midpoint
  plus the monotone-gradient gap), constant `p / (4 K_p)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `U diag(a) U*` for a real vector `a`. -/
def ftj_spec (U : Matrix n n ℂ) (a : n → ℝ) : Matrix n n ℂ :=
  U * diagonal (fun i => ((a i : ℝ) : ℂ)) * star U

/-- The gradient `p X^{p-1}` of `Tr X^p` in the eigenbasis `X = U diag(x) U*`. -/
def ftj_grad (p : ℝ) (U : Matrix n n ℂ) (x : n → ℝ) : Matrix n n ℂ :=
  ftj_spec U (fun i => p * x i ^ (p - 1))

/-!
## Unitary bookkeeping
-/

theorem ftj_star_mul_self {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) : star U * U = 1 :=
  mem_unitaryGroup_iff'.mp hU

theorem ftj_mul_star_self {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) : U * star U = 1 :=
  mem_unitaryGroup_iff.mp hU

theorem ftj_star_mul_mem {U W : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hW : W ∈ unitaryGroup n ℂ) : star U * W ∈ unitaryGroup n ℂ :=
  mul_mem (Unitary.star_mem hU) hW

/-- Rows of a unitary matrix are unit vectors. -/
theorem ftj_sum_row {Z : Matrix n n ℂ} (hZ : Z ∈ unitaryGroup n ℂ) (i : n) :
    ∑ j, ‖Z i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (ftj_mul_star_self hZ) i) i
  rw [mul_apply, one_apply_eq] at h
  have h' : ((∑ j, ‖Z i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]; push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_apply, Complex.star_def, Complex.mul_conj']
  exact_mod_cast h'

/-- Columns of a unitary matrix are unit vectors. -/
theorem ftj_sum_col {Z : Matrix n n ℂ} (hZ : Z ∈ unitaryGroup n ℂ) (j : n) :
    ∑ i, ‖Z i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (ftj_star_mul_self hZ) j) j
  rw [mul_apply, one_apply_eq] at h
  have h' : ((∑ i, ‖Z i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_apply, Complex.star_def, mul_comm, Complex.mul_conj']
  exact_mod_cast h'

/-!
## Trace formulas in two eigenbases
-/

theorem ftj_trace_diag_conj (a b : n → ℂ) (Z : Matrix n n ℂ) :
    (diagonal a * Z * diagonal b * star Z).trace =
      ∑ i, ∑ j, a i * b j * ((‖Z i j‖ ^ 2 : ℝ) : ℂ) := by
  unfold trace
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diag_apply]
  rw [mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, diagonal_mul, star_apply, Complex.star_def]
  push_cast
  rw [← Complex.mul_conj']
  ring

/-- `Tr(U diag a U* · W diag b W*) = Σ_{ij} a_i b_j |(U*W)_ij|²`. -/
theorem ftj_trace_spec_spec {U W : Matrix n n ℂ} (a b : n → ℝ) :
    (ftj_spec U a * ftj_spec W b).trace =
      ((∑ i, ∑ j, a i * b j * ‖(star U * W) i j‖ ^ 2 : ℝ) : ℂ) := by
  have h : (ftj_spec U a * ftj_spec W b).trace =
      (diagonal (fun i => ((a i : ℝ) : ℂ)) * (star U * W) * diagonal (fun i => ((b i : ℝ) : ℂ)) *
        star (star U * W)).trace := by
    unfold ftj_spec
    rw [star_mul, star_star]
    have := trace_mul_comm U (diagonal (fun i => ((a i : ℝ) : ℂ)) * star U *
      (W * diagonal (fun i => ((b i : ℝ) : ℂ)) * star W))
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  rw [h, ftj_trace_diag_conj]
  push_cast
  rfl

/-- Same eigenbasis: `Tr(U diag a U* · U diag b U*) = Σ_i a_i b_i`. -/
theorem ftj_trace_spec_same {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (a b : n → ℝ) :
    (ftj_spec U a * ftj_spec U b).trace = ((∑ i, a i * b i : ℝ) : ℂ) := by
  rw [ftj_trace_spec_spec, ftj_star_mul_self hU]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [one_apply_ne (Ne.symm hji)]
  · simp

/-- `Tr(U diag a U* Δ W diag b W* Δ) = Σ_{ij} a_i b_j |(U*ΔW)_ij|²` for Hermitian `Δ`. -/
theorem ftj_trace_spec_sandwich {U W Δ : Matrix n n ℂ} (hΔ : Δ.IsHermitian) (a b : n → ℝ) :
    (ftj_spec U a * Δ * ftj_spec W b * Δ).trace =
      ((∑ i, ∑ j, a i * b j * ‖(star U * Δ * W) i j‖ ^ 2 : ℝ) : ℂ) := by
  have hs : star (star U * Δ * W) = star W * Δ * U := by
    rw [star_mul, star_mul, star_star, Matrix.star_eq_conjTranspose Δ, hΔ.eq, Matrix.mul_assoc]
  have h : (ftj_spec U a * Δ * ftj_spec W b * Δ).trace =
      (diagonal (fun i => ((a i : ℝ) : ℂ)) * (star U * Δ * W) *
        diagonal (fun i => ((b i : ℝ) : ℂ)) * star (star U * Δ * W)).trace := by
    unfold ftj_spec
    rw [hs]
    have := trace_mul_comm U (diagonal (fun i => ((a i : ℝ) : ℂ)) * star U * Δ *
      (W * diagonal (fun i => ((b i : ℝ) : ℂ)) * star W) * Δ)
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  rw [h, ftj_trace_diag_conj]
  push_cast
  rfl

/-- `Re Tr(U diag a U* (W diag y W* - U diag x U*)) = Σ_{ij} |(U*W)_ij|² a_i (y_j - x_i)`. -/
theorem ftj_trace_left_sub {U W : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hW : W ∈ unitaryGroup n ℂ) (a x y : n → ℝ) :
    (ftj_spec U a * (ftj_spec W y - ftj_spec U x)).trace.re =
      ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (a i * (y j - x i)) := by
  rw [Matrix.mul_sub, trace_sub, ftj_trace_spec_spec, ftj_trace_spec_same hU, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_re]
  have hrow := ftj_sum_row (ftj_star_mul_mem hU hW)
  have : ∑ i, a i * x i = ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (a i * x i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Re Tr(W diag b W* (W diag y W* - U diag x U*)) = Σ_{ij} |(U*W)_ij|² b_j (y_j - x_i)`. -/
theorem ftj_trace_right_sub {U W : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hW : W ∈ unitaryGroup n ℂ) (b x y : n → ℝ) :
    (ftj_spec W b * (ftj_spec W y - ftj_spec U x)).trace.re =
      ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (b j * (y j - x i)) := by
  rw [Matrix.mul_sub, trace_sub, ftj_trace_spec_same hW, ftj_trace_spec_spec, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_re]
  have hcol := ftj_sum_col (ftj_star_mul_mem hU hW)
  have hsw : ∀ i j, ‖(star W * U) j i‖ = ‖(star U * W) i j‖ := by
    intro i j
    have : star W * U = star (star U * W) := by rw [star_mul, star_star]
    rw [this, star_apply, norm_star]
  have h1 : ∑ j, ∑ i, b j * x i * ‖(star W * U) j i‖ ^ 2 =
      ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (b j * x i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsw]; ring
  have h2 : ∑ j, b j * y j = ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (b j * y j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-!
## Klein's inequality
-/

/-- **Klein's inequality** for `Tr(·)^p`, `0 ≤ p ≤ 1`: for `X = U diag(x) U*` with `x > 0` and
`Y = W diag(y) W*` with `y ≥ 0`, `Σ_j y_j^p ≤ Σ_i x_i^p + Re Tr(∇X (Y - X))`. -/
theorem ftj_klein {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {U W : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hW : W ∈ unitaryGroup n ℂ) (x y : n → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 ≤ y j) :
    ∑ j, y j ^ p ≤
      ∑ i, x i ^ p + (ftj_grad p U x * (ftj_spec W y - ftj_spec U x)).trace.re := by
  unfold ftj_grad
  rw [ftj_trace_left_sub hU hW]
  have hrow := ftj_sum_row (ftj_star_mul_mem hU hW)
  have hcol := ftj_sum_col (ftj_star_mul_mem hU hW)
  have e1 : ∑ j, y j ^ p = ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * y j ^ p := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  have e2 : ∑ i, x i ^ p = ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * x i ^ p := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_add]
  have ht := ftj_rpow_tangent hp0 hp1 (hx i) (hy j)
  have hw : 0 ≤ ‖(star U * W) i j‖ ^ 2 := by positivity
  nlinarith

/-!
## Spectral bookkeeping for `ftj_spec`
-/

theorem ftj_spec_mul {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (a b : n → ℝ) :
    ftj_spec U a * ftj_spec U b = ftj_spec U (fun i => a i * b i) := by
  unfold ftj_spec
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, ftj_star_mul_self hU, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
  congr 3
  funext i
  push_cast; rfl

theorem ftj_spec_const {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (c : ℝ) :
    ftj_spec U (fun _ => c) = (c : ℂ) • (1 : Matrix n n ℂ) := by
  unfold ftj_spec
  rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ftj_mul_star_self hU]

theorem ftj_spec_add (U : Matrix n n ℂ) (a b : n → ℝ) :
    ftj_spec U (fun i => a i + b i) = ftj_spec U a + ftj_spec U b := by
  unfold ftj_spec
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 3
  funext i
  push_cast; rfl

theorem ftj_spec_add_const {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (a : n → ℝ) (c : ℝ) :
    ftj_spec U (fun i => a i + c) = ftj_spec U a + (c : ℂ) • (1 : Matrix n n ℂ) := by
  rw [ftj_spec_add U a (fun _ => c), ftj_spec_const hU]

theorem ftj_spec_isHermitian (U : Matrix n n ℂ) (a : n → ℝ) : (ftj_spec U a).IsHermitian := by
  unfold ftj_spec
  rw [Matrix.star_eq_conjTranspose]
  refine isHermitian_mul_mul_conjTranspose U ?_
  refine isHermitian_diagonal_iff.mpr fun i => ?_
  simp [isSelfAdjoint_iff, Complex.conj_ofReal]

theorem ftj_spec_posSemidef (U : Matrix n n ℂ) {a : n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (ftj_spec U a).PosSemidef := by
  unfold ftj_spec
  have hd : (diagonal (fun i => ((a i : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (ha i)
  have := hd.conjTranspose_mul_mul_same (star U)
  rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose] at this

theorem ftj_spec_posDef {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) {a : n → ℝ}
    (ha : ∀ i, 0 < a i) : (ftj_spec U a).PosDef := by
  unfold ftj_spec
  have hd : (diagonal (fun i => ((a i : ℝ) : ℂ))).PosDef :=
    PosDef.diagonal fun i => Complex.zero_lt_real.mpr (ha i)
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (Unitary.isUnit_coe (U := ⟨U, hU⟩))).mpr hd

/-- The canonical eigen-decomposition of a Hermitian matrix in `ftj_spec` form. -/
theorem ftj_spec_eigen {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = ftj_spec (hA.eigenvectorUnitary : Matrix n n ℂ) hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

/-- Resolvent identities: `U diag(1/(a+s)) U*` inverts `U diag(a+s) U*`. -/
theorem ftj_spec_resolvent {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (a : n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ftj_spec U (fun i => 1 / a i) * ftj_spec U a = 1 ∧
      ftj_spec U a * ftj_spec U (fun i => 1 / a i) = 1 := by
  rw [ftj_spec_mul hU, ftj_spec_mul hU]
  have h1 : (fun i => 1 / a i * a i) = fun _ => (1 : ℝ) := funext fun i => by field_simp [ha i]
  have h2 : (fun i => a i * (1 / a i)) = fun _ => (1 : ℝ) := funext fun i => by field_simp [ha i]
  rw [h1, h2, ftj_spec_const hU]
  simp

/-- `(X·Z)`-entries: `(U*(W diag y W* - U diag x U*)W)_ij = (U*W)_ij (y_j - x_i)`. -/
theorem ftj_entry_diff {U W : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hW : W ∈ unitaryGroup n ℂ) (x y : n → ℝ) (i j : n) :
    (star U * (ftj_spec W y - ftj_spec U x) * W) i j =
      (star U * W) i j * (((y j - x i : ℝ)) : ℂ) := by
  have e1 : star U * ftj_spec W y * W = star U * W * diagonal (fun j => ((y j : ℝ) : ℂ)) := by
    unfold ftj_spec
    simp only [Matrix.mul_assoc]
    rw [ftj_star_mul_self hW, Matrix.mul_one]
  have e2 : star U * ftj_spec U x * W = diagonal (fun i => ((x i : ℝ) : ℂ)) * (star U * W) := by
    unfold ftj_spec
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, ftj_star_mul_self hU, Matrix.one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, e1, e2, mul_diagonal, diagonal_mul]
  push_cast
  ring

/-!
## Loewner-order inputs
-/

omit [DecidableEq n] in
/-- Real trace pairing of two PSD matrices is nonnegative. -/
theorem ftj_re_trace_mul_nonneg {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace.re := by
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hQ
  obtain ⟨m, v, rfl⟩ := hQ
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _hj
  rw [dotProduct_comm]
  exact hP.re_dotProduct_nonneg (v j)

/-- **Resolvent antitonicity, algebraically**: if `R A = A R = 1`, `P B = B P = 1`, `B - A ⪰ 0`,
`P` Hermitian and `R ⪰ 0`, then `R - P = P(B-A)P + P(B-A)R(B-A)P ⪰ 0`. -/
theorem ftj_resolvent_sub_posSemidef {R P A B : Matrix n n ℂ} (hRA : R * A = 1) (hAR : A * R = 1)
    (hPB : P * B = 1) (hBP : B * P = 1) (hT : (B - A).PosSemidef) (hP : P.IsHermitian)
    (hR : R.PosSemidef) : (R - P).PosSemidef := by
  set T := B - A with hTdef
  have h1 : P * T * R = R - P := by
    rw [hTdef, Matrix.mul_sub, Matrix.sub_mul, hPB, Matrix.one_mul, Matrix.mul_assoc, hAR,
      Matrix.mul_one]
  have h2 : R * T * P = R - P := by
    rw [hTdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hBP, Matrix.mul_one, hRA,
      Matrix.one_mul]
  have hR' : R = P + R * T * P := by rw [h2]; abel
  have hid : R - P = P * T * P + P * T * R * T * P := by
    rw [← h1]
    conv_lhs => rw [hR']
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  have hPh : Pᴴ = P := hP.eq
  have hTh : Tᴴ = T := hT.isHermitian.eq
  have k1 : (P * T * P).PosSemidef := by
    have := hT.conjTranspose_mul_mul_same P
    rwa [hPh] at this
  have k2 : (P * T * R * T * P).PosSemidef := by
    have := hR.conjTranspose_mul_mul_same (T * P)
    rw [conjTranspose_mul, hPh, hTh] at this
    simpa only [Matrix.mul_assoc] using this
  rw [hid]
  exact k1.add k2

omit [DecidableEq n] in
/-- Monotonicity of `(A, B) ↦ Re Tr(AΔBΔ)`: if `A ⪰ A' ⪰ 0`, `B ⪰ B'` and `B ⪰ 0`, then
`Re Tr(A'ΔB'Δ) ≤ Re Tr(AΔBΔ)` for Hermitian `Δ`. -/
theorem ftj_trace_mono_two {A A' B B' Δ : Matrix n n ℂ} (hAA : (A - A').PosSemidef)
    (hBB : (B - B').PosSemidef) (hA' : A'.PosSemidef) (hB : B.PosSemidef) (hΔ : Δ.IsHermitian) :
    (A' * Δ * B' * Δ).trace.re ≤ (A * Δ * B * Δ).trace.re := by
  have hΔh : Δᴴ = Δ := hΔ.eq
  have p1 : (Δ * B * Δ).PosSemidef := by
    have := hB.conjTranspose_mul_mul_same Δ
    rwa [hΔh] at this
  have p2 : (Δ * A' * Δ).PosSemidef := by
    have := hA'.conjTranspose_mul_mul_same Δ
    rwa [hΔh] at this
  have q1 := ftj_re_trace_mul_nonneg hAA p1
  have q2 := ftj_re_trace_mul_nonneg hBB p2
  have c1 : ((B - B') * (Δ * A' * Δ)).trace = (A' * Δ * B * Δ).trace - (A' * Δ * B' * Δ).trace := by
    rw [Matrix.sub_mul, trace_sub]
    have e1 := trace_mul_comm (B * Δ) (A' * Δ)
    have e2 := trace_mul_comm (B' * Δ) (A' * Δ)
    simp only [Matrix.mul_assoc] at e1 e2 ⊢
    rw [e1, e2]
  have c2 : ((A - A') * (Δ * B * Δ)).trace = (A * Δ * B * Δ).trace - (A' * Δ * B * Δ).trace := by
    rw [Matrix.sub_mul, trace_sub]
    simp only [Matrix.mul_assoc]
  rw [c1, Complex.sub_re] at q2
  rw [c2, Complex.sub_re] at q1
  linarith

/-- **Pointwise resolvent comparison** (`s > 0`): for `X = U diag(x) U*`, `Y = W diag(y) W*`,
`Q = V diag(q) V*` with `x, y, q ≥ 0` and `X, Y ⪯ Q`,
`Σ_{kl} |(V*(Y-X)V)_kl|²/((q_k+s)(q_l+s)) ≤ Σ_{ij} |(U*W)_ij|² (y_j-x_i)²/((x_i+s)(y_j+s))`. -/
theorem ftj_pointwise {U W V : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hW : W ∈ unitaryGroup n ℂ) (hV : V ∈ unitaryGroup n ℂ) (x y q : n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (hq : ∀ k, 0 ≤ q k)
    (hXQ : (ftj_spec V q - ftj_spec U x).PosSemidef)
    (hYQ : (ftj_spec V q - ftj_spec W y).PosSemidef) {s : ℝ} (hs : 0 < s) :
    ∑ k, ∑ l, ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 / ((q k + s) * (q l + s)) ≤
      ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (y j - x i) ^ 2 / ((x i + s) * (y j + s)) := by
  set Δ := ftj_spec W y - ftj_spec U x with hΔdef
  have hΔ : Δ.IsHermitian := (ftj_spec_isHermitian W y).sub (ftj_spec_isHermitian U x)
  set RX := ftj_spec U (fun i => 1 / (x i + s))
  set RY := ftj_spec W (fun j => 1 / (y j + s))
  set P := ftj_spec V (fun k => 1 / (q k + s))
  have hxs : ∀ i, x i + s ≠ 0 := fun i => by linarith [hx i]
  have hys : ∀ j, y j + s ≠ 0 := fun j => by linarith [hy j]
  have hqs : ∀ k, q k + s ≠ 0 := fun k => by linarith [hq k]
  have hL : ∑ k, ∑ l, ‖(star V * Δ * V) k l‖ ^ 2 / ((q k + s) * (q l + s)) =
      (P * Δ * P * Δ).trace.re := by
    rw [ftj_trace_spec_sandwich hΔ, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hR : ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (y j - x i) ^ 2 / ((x i + s) * (y j + s)) =
      (RX * Δ * RY * Δ).trace.re := by
    rw [ftj_trace_spec_sandwich hΔ, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΔdef, ftj_entry_diff hU hW, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, div_eq_mul_inv, mul_inv]
    ring
  rw [hL, hR]
  have hPpsd : P.PosSemidef := ftj_spec_posSemidef V fun k => by
    have := hq k; positivity
  have hRYpsd : RY.PosSemidef := ftj_spec_posSemidef W fun j => by
    have := hy j; positivity
  have hRXpsd : RX.PosSemidef := ftj_spec_posSemidef U fun i => by
    have := hx i; positivity
  have hQs : ftj_spec V (fun k => q k + s) * P = 1 := (ftj_spec_resolvent hV _ hqs).2
  have hPQ : P * ftj_spec V (fun k => q k + s) = 1 := (ftj_spec_resolvent hV _ hqs).1
  have hsub : ∀ (Z : Matrix n n ℂ) (z : n → ℝ), Z ∈ unitaryGroup n ℂ →
      ftj_spec V (fun k => q k + s) - ftj_spec Z (fun i => z i + s) =
        ftj_spec V q - ftj_spec Z z := by
    intro Z z hZ
    rw [ftj_spec_add_const hV, ftj_spec_add_const hZ]
    abel
  have hX : (RX - P).PosSemidef :=
    ftj_resolvent_sub_posSemidef (ftj_spec_resolvent hU _ hxs).1 (ftj_spec_resolvent hU _ hxs).2
      hPQ hQs (by rw [hsub U x hU]; exact hXQ) (ftj_spec_isHermitian V _) hRXpsd
  have hY : (RY - P).PosSemidef :=
    ftj_resolvent_sub_posSemidef (ftj_spec_resolvent hW _ hys).1 (ftj_spec_resolvent hW _ hys).2
      hPQ hQs (by rw [hsub W y hW]; exact hYQ) (ftj_spec_isHermitian V _) hRYpsd
  exact ftj_trace_mono_two hX hY hPpsd hRYpsd hΔ

/-!
## The monotone-gradient gap and the pathwise Jensen gap
-/

/-- **Monotone-gradient gap.** For `X = U diag(x) U*`, `Y = W diag(y) W*` (`x, y > 0`) and
`Q = V diag(q) V*` (`q > 0`) with `X, Y ⪯ Q`, `0 < p < 1`:
`(p/K_p) Σ_{kl} |(V*(Y-X)V)_kl|² ∫_0^∞ k_p(q_k,q_l) ≤ Re Tr((∇X - ∇Y)(Y - X))`. -/
theorem ftj_grad_monotone {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {U W V : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hW : W ∈ unitaryGroup n ℂ) (hV : V ∈ unitaryGroup n ℂ)
    (x y q : n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j) (hq : ∀ k, 0 < q k)
    (hXQ : (ftj_spec V q - ftj_spec U x).PosSemidef)
    (hYQ : (ftj_spec V q - ftj_spec W y).PosSemidef) :
    p / ftj_resolventConst p * ∑ k, ∑ l,
        ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 *
          ∫ s in Ioi (0 : ℝ), concavityKernel p (q k) (q l) s ≤
      ((ftj_grad p U x - ftj_grad p W y) * (ftj_spec W y - ftj_spec U x)).trace.re := by
  have hK := ftj_resolventConst_pos hp0 hp1
  rw [Matrix.sub_mul, trace_sub, Complex.sub_re]
  unfold ftj_grad
  rw [ftj_trace_left_sub hU hW, ftj_trace_right_sub hU hW, ← Finset.sum_sub_distrib]
  have e : ∀ i j, ‖(star U * W) i j‖ ^ 2 * ((p * x i ^ (p - 1)) * (y j - x i)) -
      ‖(star U * W) i j‖ ^ 2 * ((p * y j ^ (p - 1)) * (y j - x i)) =
      p / ftj_resolventConst p * (‖(star U * W) i j‖ ^ 2 * ((y j - x i) ^ 2 *
        ∫ s in Ioi (0 : ℝ), concavityKernel p (x i) (y j) s)) := by
    intro i j
    rw [← mul_sub, ← sub_mul, ftj_divided_difference hp0 hp1 (hx i) (hy j)]
    ring
  have hrw : ∑ i, (∑ j, ‖(star U * W) i j‖ ^ 2 * ((p * x i ^ (p - 1)) * (y j - x i)) -
      ∑ j, ‖(star U * W) i j‖ ^ 2 * ((p * y j ^ (p - 1)) * (y j - x i))) =
      p / ftj_resolventConst p * ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * ((y j - x i) ^ 2 *
        ∫ s in Ioi (0 : ℝ), concavityKernel p (x i) (y j) s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => e i j
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hp0.le hK.le)
  -- both sides as one integral over `s`
  have hkint : ∀ a b : ℝ, 0 < a → 0 < b → IntegrableOn (concavityKernel p a b) (Ioi 0) :=
    fun a b ha hb => integrableOn_concavityKernel hp0 hp1 ha hb
  have hLHS : ∑ k, ∑ l, ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 *
        ∫ s in Ioi (0 : ℝ), concavityKernel p (q k) (q l) s =
      ∫ s in Ioi (0 : ℝ), ∑ k, ∑ l, ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 *
        concavityKernel p (q k) (q l) s := by
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hkint _ _ (hq k) (hq l)).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hkint _ _ (hq k) (hq l)).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
  have hRHS : ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * ((y j - x i) ^ 2 *
        ∫ s in Ioi (0 : ℝ), concavityKernel p (x i) (y j) s) =
      ∫ s in Ioi (0 : ℝ), ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (y j - x i) ^ 2 *
        concavityKernel p (x i) (y j) s := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hkint _ _ (hx i) (hy j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hkint _ _ (hx i) (hy j)).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  rw [hLHS, hRHS]
  refine setIntegral_mono_on
    (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hkint _ _ (hq k) (hq l)).const_mul _)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hkint _ _ (hx i) (hy j)).const_mul _)
    measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hpt := ftj_pointwise hU hW hV x y q (fun i => (hx i).le) (fun j => (hy j).le)
    (fun k => (hq k).le) hXQ hYQ hs0
  have f1 : ∑ k, ∑ l, ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 *
        concavityKernel p (q k) (q l) s =
      s ^ (p - 1) * ∑ k, ∑ l, ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 /
        ((q k + s) * (q l + s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold concavityKernel; ring
  have f2 : ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (y j - x i) ^ 2 *
        concavityKernel p (x i) (y j) s =
      s ^ (p - 1) * ∑ i, ∑ j, ‖(star U * W) i j‖ ^ 2 * (y j - x i) ^ 2 /
        ((x i + s) * (y j + s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold concavityKernel; ring
  rw [f1, f2]
  exact mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hs0.le _)

/-- **Pathwise second-order Jensen gap** (`0 < p < 1`). For `X = U diag(x) U*` with `x > 0`,
`Y = W diag(y) W*` with `y ≥ 0`, and `Q = V diag(q) V*` with `q > 0`, `X, Y ⪯ Q`:
`Σ_j y_j^p + (p/(4K_p)) Σ_{kl} |(V*(Y-X)V)_kl|² ∫_0^∞ k_p(q_k,q_l) ≤ Σ_i x_i^p + Re Tr(∇X (Y-X))`.
Proof: Klein's inequality from the midpoint `C = (X+Y)/2` to `Y` and from `X` to `C`, plus the
monotone-gradient gap between `X` and `C`. -/
theorem ftj_core_gap {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {U W V : Matrix n n ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hW : W ∈ unitaryGroup n ℂ) (hV : V ∈ unitaryGroup n ℂ)
    (x y q : n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 ≤ y j) (hq : ∀ k, 0 < q k)
    (hXQ : (ftj_spec V q - ftj_spec U x).PosSemidef)
    (hYQ : (ftj_spec V q - ftj_spec W y).PosSemidef) :
    ∑ j, y j ^ p + p / (4 * ftj_resolventConst p) * ∑ k, ∑ l,
        ‖(star V * (ftj_spec W y - ftj_spec U x) * V) k l‖ ^ 2 *
          ∫ s in Ioi (0 : ℝ), concavityKernel p (q k) (q l) s ≤
      ∑ i, x i ^ p + (ftj_grad p U x * (ftj_spec W y - ftj_spec U x)).trace.re := by
  set X := ftj_spec U x
  set Y := ftj_spec W y
  set Q := ftj_spec V q
  set Δ := Y - X with hΔ
  set C : Matrix n n ℂ := (1 / 2 : ℂ) • (X + Y) with hCdef
  have hhalf : (0 : ℂ) < 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_lt_real.mpr (by norm_num)
  have hXpd : X.PosDef := ftj_spec_posDef hU hx
  have hYpsd : Y.PosSemidef := ftj_spec_posSemidef W hy
  have hCpd : C.PosDef := (hXpd.add_posSemidef hYpsd).smul hhalf
  have hCh : C.IsHermitian := hCpd.isHermitian
  set Uc : Matrix n n ℂ := (hCh.eigenvectorUnitary : Matrix n n ℂ)
  have hUc : Uc ∈ unitaryGroup n ℂ := (hCh.eigenvectorUnitary).2
  set γ := hCh.eigenvalues
  have hCspec : ftj_spec Uc γ = C := (ftj_spec_eigen hCh).symm
  have hγ : ∀ k, 0 < γ k := fun k => hCpd.eigenvalues_pos k
  have hCQ : (Q - ftj_spec Uc γ).PosSemidef := by
    rw [hCspec]
    have e : Q - C = (1 / 2 : ℂ) • (Q - X) + (1 / 2 : ℂ) • (Q - Y) := by
      rw [hCdef]; module
    rw [e]
    exact (hXQ.smul hhalf.le).add (hYQ.smul hhalf.le)
  have hYC : Y - ftj_spec Uc γ = (1 / 2 : ℂ) • Δ := by rw [hCspec, hCdef, hΔ]; module
  have hCX : ftj_spec Uc γ - X = (1 / 2 : ℂ) • Δ := by rw [hCspec, hCdef, hΔ]; module
  have k1 := ftj_klein hp0.le hp1.le hUc hW γ y hγ hy
  have k2 := ftj_klein hp0.le hp1.le hU hUc x γ hx (fun k => (hγ k).le)
  have g := ftj_grad_monotone hp0 hp1 hU hUc hV x γ q hx hγ hq hXQ hCQ
  have half : ∀ G : Matrix n n ℂ, (G * ((1 / 2 : ℂ) • Δ)).trace.re = 1 / 2 * (G * Δ).trace.re := by
    intro G
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.mul_re]
    norm_num
  rw [hYC, half] at k1
  rw [hCX, half] at k2
  rw [hCX, Matrix.sub_mul, trace_sub, Complex.sub_re, half, half] at g
  have hnorm : ∀ k l, ‖(star V * ((1 / 2 : ℂ) • Δ) * V) k l‖ ^ 2 =
      1 / 4 * ‖(star V * Δ * V) k l‖ ^ 2 := by
    intro k l
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    norm_num
  simp_rw [hnorm] at g
  have hsum : ∑ k, ∑ l, 1 / 4 * ‖(star V * Δ * V) k l‖ ^ 2 *
      ∫ s in Ioi (0 : ℝ), concavityKernel p (q k) (q l) s =
      1 / 4 * ∑ k, ∑ l, ‖(star V * Δ * V) k l‖ ^ 2 *
        ∫ s in Ioi (0 : ℝ), concavityKernel p (q k) (q l) s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsum] at g
  have hK := ftj_resolventConst_pos hp0 hp1
  have hc : p / (4 * ftj_resolventConst p) = p / ftj_resolventConst p * (1 / 4) := by
    field_simp
  rw [hc]
  nlinarith

end BlockBand.Endpoints
