module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Pairing with `Q ⪰ 0` through an eigenbasis

For `Q ⪰ 0` with orthonormal eigenvectors `u_i` and eigenvalues `λ_i ≥ 0` (`Σλ_i = Tr Q`), and
`Z'_{ij} = u_i* Z u_j`:
* `Tr(QZ) = Σ_i λ_i Z'_{ii}` and `Tr(QZQZ*) = Σ_{ij} λ_iλ_j |Z'_{ij}|²`, so `hsSandwich Q` is a
  weighted `ℓ²` norm of the entries `Z'_{ij}`: `hsSandwich_add_le`, `hsSandwich_smul`,
  `hsSandwich_le_norm` (`≤ ‖Z‖ Tr Q`);
* `eLpNorm_trace_mul_le`: uniform bilinear `L^p` bounds `‖u*Zv‖_p ≤ B‖u‖‖v‖` give
  `‖Tr(QZ)‖_p ≤ B Tr Q` (Minkowski over `i`);
* `eLpNorm_hsSandwich_le` (`p ≥ 2`): the same for `‖‖Q^{1/2}ZQ^{1/2}‖_HS‖_p` (Minkowski in
  `L^{p/2}` on `Σ λ_iλ_j |Z'_{ij}|²`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## The eigenbasis
-/

/-- The eigenvectors of `Q ⪰ 0`. -/
def ts_vec {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (i : Fin W) : Fin W → ℂ :=
  ⇑(hQ.isHermitian.eigenvectorBasis i)

/-- The eigenvalues of `Q ⪰ 0`. -/
def ts_lam {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (i : Fin W) : ℝ :=
  hQ.isHermitian.eigenvalues i

/-- The entries `Z'_{ij} = u_i* Z u_j` in the eigenbasis. -/
def ts_ent {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ)
    (i j : Fin W) : ℂ :=
  bilinear (ts_vec hQ i) Z (ts_vec hQ j)

theorem ts_lam_nonneg {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (i : Fin W) :
    0 ≤ ts_lam hQ i := hQ.eigenvalues_nonneg i

theorem ts_sum_lam {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) :
    ∑ i, ts_lam hQ i = Q.trace.re := by
  rw [hQ.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp [ts_lam]

theorem ts_vecNorm {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (i : Fin W) :
    vecNorm (ts_vec hQ i) = 1 := by
  rw [vecNorm_eq, ts_vec]
  simp

theorem ts_norm_ent_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (Z : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) : ‖ts_ent hQ Z i j‖ ≤ ‖Z‖ := by
  have h := norm_bilinear_le (ts_vec hQ i) Z (ts_vec hQ j)
  rw [ts_vecNorm, ts_vecNorm, one_mul, mul_one] at h
  exact h

theorem ts_ent_add {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (A B : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    ts_ent hQ (A + B) i j = ts_ent hQ A i j + ts_ent hQ B i j := by
  simp [ts_ent, bilinear, Matrix.add_mulVec, dotProduct_add]

theorem ts_ent_smul {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (c : ℂ)
    (A : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    ts_ent hQ (c • A) i j = c * ts_ent hQ A i j := by
  simp [ts_ent, bilinear, Matrix.smul_mulVec, dotProduct_smul]

/-- The unitary `U` of the eigenbasis. -/
abbrev ts_U {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) : Matrix (Fin W) (Fin W) ℂ :=
  (hQ.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)

theorem ts_spectral {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) :
    Q = ts_U hQ * diagonal (fun i => (ts_lam hQ i : ℂ)) * star (ts_U hQ) := by
  have h := hQ.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

theorem ts_ent_eq {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (Z : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    ts_ent hQ Z i j = (star (ts_U hQ) * Z * ts_U hQ) i j := by
  simp only [ts_ent, bilinear, ts_vec, dotProduct, mulVec, Matrix.mul_apply, Matrix.star_apply,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  ring

theorem ts_trace_mul {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (Z : Matrix (Fin W) (Fin W) ℂ) :
    (Q * Z).trace = ∑ i, (ts_lam hQ i : ℂ) * ts_ent hQ Z i i := by
  conv_lhs => rw [ts_spectral hQ]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, ts_ent_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
  ring

theorem ts_trace_sandwich {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (Z : Matrix (Fin W) (Fin W) ℂ) :
    (Q * Z * Q * Zᴴ).trace =
      ((∑ i, ∑ j, ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ Z i j‖ ^ 2 : ℝ) : ℂ) := by
  have hZ' : star (ts_U hQ) * Zᴴ * ts_U hQ = (star (ts_U hQ) * Z * ts_U hQ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have e : (Q * Z * Q * Zᴴ).trace = (diagonal (fun i => (ts_lam hQ i : ℂ)) *
      (star (ts_U hQ) * Z * ts_U hQ) * diagonal (fun i => (ts_lam hQ i : ℂ)) *
      (star (ts_U hQ) * Z * ts_U hQ)ᴴ).trace := by
    rw [← hZ']
    conv_lhs => rw [ts_spectral hQ]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (ts_U hQ)]
    simp only [Matrix.mul_assoc]
  rw [e]
  push_cast
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, ts_ent_eq]
  rw [← Complex.mul_conj', Complex.star_def]
  ring

theorem ts_hs_eq {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (Z : Matrix (Fin W) (Fin W) ℂ) :
    hsSandwich Q Z =
      Real.sqrt (∑ i, ∑ j, ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ Z i j‖ ^ 2) := by
  rw [hsSandwich, ts_trace_sandwich hQ, Complex.ofReal_re]

/-!
## `hsSandwich` as a weighted `ℓ²` norm
-/

/-- The vector `(√(λ_iλ_j) Z'_{ij})_{ij}`, whose Euclidean norm is `hsSandwich Q Z`. -/
def ts_hsVec {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) :
    EuclideanSpace ℂ (Fin W × Fin W) :=
  WithLp.toLp 2 fun p => ((Real.sqrt (ts_lam hQ p.1 * ts_lam hQ p.2) : ℝ) : ℂ) * ts_ent hQ Z p.1 p.2

theorem ts_hs_eq_norm {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (Z : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q Z = ‖ts_hsVec hQ Z‖ := by
  rw [ts_hs_eq hQ, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h0 := mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)
  simp only [ts_hsVec, PiLp.toLp_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt h0]

theorem hsSandwich_add_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (A B : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q (A + B) ≤ hsSandwich Q A + hsSandwich Q B := by
  rw [ts_hs_eq_norm hQ, ts_hs_eq_norm hQ, ts_hs_eq_norm hQ]
  have e : ts_hsVec hQ (A + B) = ts_hsVec hQ A + ts_hsVec hQ B := by
    rw [ts_hsVec, ts_hsVec, ts_hsVec, ← WithLp.toLp_add]
    congr 1
    funext p
    simp only [ts_ent_add, Pi.add_apply, mul_add]
  rw [e]
  exact norm_add_le _ _

theorem hsSandwich_smul {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (c : ℂ)
    (A : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q (c • A) = ‖c‖ * hsSandwich Q A := by
  rw [ts_hs_eq_norm hQ, ts_hs_eq_norm hQ]
  have e : ts_hsVec hQ (c • A) = c • ts_hsVec hQ A := by
    rw [ts_hsVec, ts_hsVec, ← WithLp.toLp_smul]
    congr 1
    funext p
    simp only [ts_ent_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, norm_smul]

theorem hsSandwich_le_norm {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (A : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q A ≤ ‖A‖ * Q.trace.re := by
  rw [ts_hs_eq hQ, ← ts_sum_lam hQ]
  have h0 : 0 ≤ ‖A‖ * ∑ i, ts_lam hQ i :=
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => ts_lam_nonneg hQ i)
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  have e : (‖A‖ * ∑ i, ts_lam hQ i) ^ 2 = ∑ i, ∑ j, ts_lam hQ i * ts_lam hQ j * ‖A‖ ^ 2 := by
    rw [mul_pow, sq (∑ i, ts_lam hQ i), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h0 := mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)
  have h1 := ts_norm_ent_le hQ A i j
  have h2 : ‖ts_ent hQ A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact mul_le_mul_of_nonneg_left h2 h0

/-!
## `L^p` bounds from uniform bilinear bounds
-/

theorem ts_enorm_lam {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (i : Fin W) :
    ‖((ts_lam hQ i : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (ts_lam hQ i) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (ts_lam_nonneg hQ i)]

theorem ts_eLpNorm_ent_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) {Z : Ω → Matrix (Fin W) (Fin W) ℂ}
    {p : ℝ≥0∞} {B : ℝ}
    (hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v) p μ ≤
      ENNReal.ofReal (B * vecNorm u * vecNorm v)) (i j : Fin W) :
    eLpNorm (fun ω => ts_ent hQ (Z ω) i j) p μ ≤ ENNReal.ofReal B := by
  have h := hB (ts_vec hQ i) (ts_vec hQ j)
  rwa [ts_vecNorm, ts_vecNorm, mul_one, mul_one] at h

/-- `‖Tr(QZ)‖_p ≤ B Tr Q` from uniform bilinear bounds `‖u*Zv‖_p ≤ B‖u‖‖v‖`. -/
theorem eLpNorm_trace_mul_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) {Z : Ω → Matrix (Fin W) (Fin W) ℂ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v) p μ ≤
      ENNReal.ofReal (B * vecNorm u * vecNorm v)) :
    eLpNorm (fun ω => (Q * Z ω).trace) p μ ≤ ENNReal.ofReal (B * Q.trace.re) := by
  have hfun : (fun ω => (Q * Z ω).trace) =
      ∑ i, ((ts_lam hQ i : ℝ) : ℂ) • fun ω => ts_ent hQ (Z ω) i i := by
    funext ω
    rw [Finset.sum_apply, ts_trace_mul hQ]
    rfl
  rw [hfun]
  refine (eLpNorm_sum_le hp).trans ?_
  calc ∑ i, eLpNorm (((ts_lam hQ i : ℝ) : ℂ) • fun ω => ts_ent hQ (Z ω) i i) p μ
      ≤ ∑ i, ENNReal.ofReal (ts_lam hQ i * B) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [eLpNorm_const_smul, ts_enorm_lam, ENNReal.ofReal_mul (ts_lam_nonneg hQ i)]
        exact mul_le_mul_right (ts_eLpNorm_ent_le hQ hB i i) _
    _ = ENNReal.ofReal (B * Q.trace.re) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (ts_lam_nonneg hQ i) hB0,
          ← Finset.sum_mul, ts_sum_lam hQ, mul_comm]

theorem ts_measurable_ent {Ω : Type*} [MeasurableSpace Ω] {Q : Matrix (Fin W) (Fin W) ℂ}
    (hQ : Q.PosSemidef) {Z : Ω → Matrix (Fin W) (Fin W) ℂ} (hZ : Measurable Z) (i j : Fin W) :
    Measurable fun ω => ts_ent hQ (Z ω) i j := by
  have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => ts_ent hQ M i j := by
    unfold ts_ent bilinear; fun_prop
  exact hc.measurable.comp hZ

/-- `‖‖Q^{1/2}ZQ^{1/2}‖_HS‖_p ≤ B Tr Q` for `p ≥ 2` from the same bilinear bounds. -/
theorem eLpNorm_hsSandwich_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) {Z : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hZ : Measurable Z) {p : ℝ≥0∞} (hp : 2 ≤ p) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v) p μ ≤
      ENNReal.ofReal (B * vecNorm u * vecNorm v)) :
    eLpNorm (fun ω => hsSandwich Q (Z ω)) p μ ≤ ENNReal.ofReal (B * Q.trace.re) := by
  set S : Ω → ℝ := fun ω =>
    ∑ i, ∑ j, ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ (Z ω) i j‖ ^ 2 with hS
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)) (sq_nonneg _)
  have hg : (fun ω => hsSandwich Q (Z ω)) = fun ω => Real.sqrt (S ω) := by
    funext ω; rw [ts_hs_eq hQ]
  have hSm : Measurable S := Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((ts_measurable_ent hQ hZ i j).norm.pow_const 2)
  have hgm : AEStronglyMeasurable (fun ω => Real.sqrt (S ω)) μ :=
    (Real.continuous_sqrt.measurable.comp hSm).aestronglyMeasurable
  have hp2 : (1 : ℝ≥0∞) ≤ p / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), one_mul]
    exact hp
  have hpp : p / 2 * ENNReal.ofReal 2 = p := by
    rw [ENNReal.ofReal_ofNat, ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  -- `‖g‖_p² = ‖S‖_{p/2}`
  have hsq : eLpNorm (fun ω => Real.sqrt (S ω)) p μ ^ (2 : ℝ) = eLpNorm S (p / 2) μ := by
    have h := eLpNorm_norm_rpow (fun ω => Real.sqrt (S ω)) hgm (p := p / 2) two_pos
    rw [hpp] at h
    rw [← h]
    congr 1
    funext ω
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hS0 ω)]
  -- Minkowski in `L^{p/2}`
  have hterm : ∀ i j, eLpNorm (fun ω => ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ (Z ω) i j‖ ^ 2)
      (p / 2) μ ≤ ENNReal.ofReal (ts_lam hQ i * ts_lam hQ j * B ^ 2) := fun i j => by
    have h0 := mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)
    have e : (fun ω => ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ (Z ω) i j‖ ^ 2) =
        (ts_lam hQ i * ts_lam hQ j) • fun ω => ‖ts_ent hQ (Z ω) i j‖ ^ (2 : ℝ) := by
      funext ω; simp
    rw [e, eLpNorm_const_smul, eLpNorm_norm_rpow _ (ts_measurable_ent hQ hZ i j).aestronglyMeasurable
      two_pos, hpp, ← ofReal_norm, Real.norm_of_nonneg h0,
      ENNReal.ofReal_mul h0, ENNReal.ofReal_pow hB0, ← ENNReal.rpow_natCast]
    refine mul_le_mul_right ?_ _
    exact_mod_cast ENNReal.rpow_le_rpow (ts_eLpNorm_ent_le hQ hB i j) (by norm_num : (0 : ℝ) ≤ 2)
  have hSle : eLpNorm S (p / 2) μ ≤ ENNReal.ofReal (B * Q.trace.re) ^ (2 : ℝ) := by
    have hS' : S = ∑ i, ∑ j, fun ω => ts_lam hQ i * ts_lam hQ j * ‖ts_ent hQ (Z ω) i j‖ ^ 2 := by
      funext ω; simp [hS, Finset.sum_apply]
    rw [hS']
    refine (eLpNorm_sum_le hp2).trans ?_
    refine (Finset.sum_le_sum fun i _ => (eLpNorm_sum_le hp2).trans
      (Finset.sum_le_sum fun j _ => hterm i j)).trans ?_
    have hnn : ∀ i j, 0 ≤ ts_lam hQ i * ts_lam hQ j * B ^ 2 := fun i j =>
      mul_nonneg (mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)) (sq_nonneg _)
    simp_rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hnn _ j]
    have hT0 : 0 ≤ Q.trace.re := by
      rw [← ts_sum_lam hQ]; exact Finset.sum_nonneg fun i _ => ts_lam_nonneg hQ i
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hB0 hT0) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [← ts_sum_lam hQ, Real.rpow_two, mul_pow, sq (∑ i, ts_lam hQ i), Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hg]
  rw [← hsq] at hSle
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 hSle

end BlockBand.Transmission.SourceMixing
