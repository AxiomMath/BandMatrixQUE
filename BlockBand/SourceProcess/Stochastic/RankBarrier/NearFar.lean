module
public import BlockBand.SourceProcess.Stochastic.RankBarrier.Generator
public import BlockBand.SourceProcess.Stochastic.RankBarrier.RankOne
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.ItoTable
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The near and far linear equations

Along the finite source equation the near rows `L = PV` satisfy a
left-linear equation and the far rows `F = (1 − P)V` a right-linear one. Concretely, for the
noise coordinate `a = ((k₀,j),r)` with weight `w_r` and `E = E_{j k₀}`:

* `near_noise_eq`: `P σ_a(V) = w_r (P P')_{·j} ⊗ L_{k₀·}` (left multiplication of `L`);
* `far_noise_eq`: `(1−P) σ_a(V) = (F z) ⊗ L_{k₀·}`, `z = w_r (𝖣Vᴴ)_{·j}`, using
  `(1−P)P' = F𝖣Vᴴ` (right multiplication of `F`; needs `P² = P`);
* drift: `P b(V) = −(D₀Naux/4) L` and `(1−P) b(V) = 0`.

Hence every `k`-minor is affine along each noise line, with slope a combination
of `k`-minors whose coefficients are bounded on `‖V‖ ≤ R`. No constraint on `V` is used.
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

omit [DecidableEq ι] [Fintype c] in
theorem line_mul (Q : Matrix ι ι ℂ) (V H : Matrix ι c ℂ) (t : ℝ) :
    Q * (V + t • H) = Q * V + of fun l m => (t : ℂ) * (Q * H) l m := by
  rw [Matrix.mul_add, Matrix.mul_smul]
  ext l m
  simp [Complex.real_smul]

/-- `P σ_a(V) = w ⊗ (PV)_{k₀·}` with `w = w_r (PP')_{·j}`. -/
theorem near_noise_eq (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) :
    P * sourceDiffusion D0 P D a V = of fun l m =>
      (sourceWeight D0 a.2 * (P * gramProjection P V D) l a.1.2) * (P * V) a.1.1 m := by
  rw [sourceDiffusion_eq, sourceNoiseMatrix, Matrix.smul_mul, Matrix.mul_smul]
  have h : P * (gramProjection P V D * sourceUnit a * P * V) =
      P * gramProjection P V D * Matrix.single a.1.2 a.1.1 (1 : ℂ) * (P * V) := by
    simp only [sourceUnit, Matrix.mul_assoc]
  ext l m
  rw [Matrix.smul_apply, h, unit_entry, smul_eq_mul, of_apply, mul_assoc]

/-- `(1−P) σ_a(V) = (F z) ⊗ (PV)_{k₀·}` with `F = (1−P)V`, `z = w_r (𝖣Vᴴ)_{·j}`. -/
theorem far_noise_eq (D0 : ℝ) (P : Matrix ι ι ℂ) (hPP : P * P = P) (D : Matrix c c ℂ)
    (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    (1 - P) * sourceDiffusion D0 P D a V = of fun l m =>
      (((1 - P) * V) *ᵥ fun m' => sourceWeight D0 a.2 * (D * Vᴴ) m' a.1.2) l *
        (P * V) a.1.1 m := by
  rw [sourceDiffusion_eq, sourceNoiseMatrix, Matrix.smul_mul, Matrix.mul_smul]
  have hP' : (1 - P) * gramProjection P V D = (1 - P) * V * (D * Vᴴ) := by
    rw [gramProjection, Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self,
      zero_add]
    simp only [Matrix.mul_assoc]
  have h : (1 - P) * (gramProjection P V D * sourceUnit a * P * V) =
      (1 - P) * V * (D * Vᴴ) * Matrix.single a.1.2 a.1.1 (1 : ℂ) * (P * V) := by
    rw [← hP']
    simp only [sourceUnit, Matrix.mul_assoc]
  ext l m
  rw [Matrix.smul_apply, h, unit_entry, smul_eq_mul, of_apply, mul_apply]
  simp only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Slope of a minor under a row perturbation `w ⊗ L_{k₀·}`. -/
def rowSlope {k : ℕ} (L : Matrix ι c ℂ) (w : ι → ℂ) (k0 : ι)
    (p : (Fin k → ι) × (Fin k → c)) : ℂ :=
  ∑ i, w (p.1 i) * det (L.submatrix (Function.update p.1 i k0) p.2)

/-- Slope of a minor under a column perturbation `(F z) ⊗ y`. -/
def colSlope {k : ℕ} (F : Matrix ι c ℂ) (z y : c → ℂ) (p : (Fin k → ι) × (Fin k → c)) : ℂ :=
  ∑ i, y (p.2 i) * ∑ m, z m * det (F.submatrix p.1 (Function.update p.2 i m))

omit [DecidableEq ι] in
theorem norm_rowSlope_le {k : ℕ} (L : Matrix ι c ℂ) (w : ι → ℂ) (k0 : ι) {Bw : ℝ}
    (hw : ∀ l, ‖w l‖ ≤ Bw) (p : (Fin k → ι) × (Fin k → c)) :
    ‖rowSlope L w k0 p‖ ≤ (k * Bw) * ∑ q, ‖minorVec k L q‖ := by
  have hS : ∀ q0, ‖minorVec k L q0‖ ≤ ∑ q, ‖minorVec k L q‖ := fun q0 =>
    Finset.single_le_sum (f := fun q => ‖minorVec k L q‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ q0)
  calc ‖rowSlope L w k0 p‖ ≤ ∑ i, ‖w (p.1 i)‖ * ‖det (L.submatrix (Function.update p.1 i k0) p.2)‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
    _ ≤ ∑ _i : Fin k, Bw * ∑ q, ‖minorVec k L q‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hw _) (hS (Function.update p.1 i k0, p.2))
          (norm_nonneg _) ((norm_nonneg _).trans (hw (p.1 i)))
    _ = (k * Bw) * ∑ q, ‖minorVec k L q‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [DecidableEq ι] in
theorem norm_colSlope_le {k : ℕ} [DecidableEq c] (F : Matrix ι c ℂ) (z y : c → ℂ) {Bz By : ℝ}
    (hBz : 0 ≤ Bz) (hBy : 0 ≤ By) (hz : ∀ m, ‖z m‖ ≤ Bz) (hy : ∀ m, ‖y m‖ ≤ By)
    (p : (Fin k → ι) × (Fin k → c)) :
    ‖colSlope F z y p‖ ≤ (k * (By * (Fintype.card c * Bz))) * ∑ q, ‖minorVec k F q‖ := by
  set T := ∑ q, ‖minorVec k F q‖
  have hS : ∀ q0, ‖minorVec k F q0‖ ≤ T := fun q0 =>
    Finset.single_le_sum (f := fun q => ‖minorVec k F q‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ q0)
  have hin : ∀ i : Fin k, ‖∑ m, z m * det (F.submatrix p.1 (Function.update p.2 i m))‖ ≤
      Fintype.card c * Bz * T := by
    intro i
    calc ‖∑ m, z m * det (F.submatrix p.1 (Function.update p.2 i m))‖
        ≤ ∑ m, ‖z m‖ * ‖det (F.submatrix p.1 (Function.update p.2 i m))‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
      _ ≤ ∑ _m : c, Bz * T :=
          Finset.sum_le_sum fun m _ => mul_le_mul (hz m) (hS (p.1, Function.update p.2 i m))
            (norm_nonneg _) hBz
      _ = Fintype.card c * Bz * T := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc ‖colSlope F z y p‖ ≤ ∑ i, ‖y (p.2 i)‖ *
        ‖∑ m, z m * det (F.submatrix p.1 (Function.update p.2 i m))‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
    _ ≤ ∑ _i : Fin k, By * (Fintype.card c * Bz * T) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hy _) (hin i) (norm_nonneg _) hBy
    _ = (k * (By * (Fintype.card c * Bz))) * T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Near noise lines: minors of `P(V + t σ_a)` are affine with slope `rowSlope`. -/
theorem near_lin {k : ℕ} (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) (t : ℝ) (p : (Fin k → ι) × (Fin k → c)) :
    minorVec k (P * (V + t • sourceDiffusion D0 P D a V)) p = minorVec k (P * V) p +
      t * rowSlope (P * V) (fun l => sourceWeight D0 a.2 * (P * gramProjection P V D) l a.1.2)
        a.1.1 p := by
  have hM : P * (V + t • sourceDiffusion D0 P D a V) = P * V + of fun l m => (t : ℂ) *
      (sourceWeight D0 a.2 * (P * gramProjection P V D) l a.1.2) * (P * V) a.1.1 m := by
    rw [line_mul, near_noise_eq]
    ext l m
    simp only [Matrix.add_apply, of_apply]
    ring
  rw [minorVec, minorVec, hM, det_rowPerturb_submatrix]
  rfl

/-- Far noise lines: minors of `(1−P)(V + t σ_a)` are affine with slope `colSlope`. -/
theorem far_lin {k : ℕ} [DecidableEq c] (D0 : ℝ) (P : Matrix ι ι ℂ) (hPP : P * P = P)
    (D : Matrix c c ℂ) (a : SourceNoise ι) (V : Matrix ι c ℂ) (t : ℝ)
    (p : (Fin k → ι) × (Fin k → c)) :
    minorVec k ((1 - P) * (V + t • sourceDiffusion D0 P D a V)) p =
      minorVec k ((1 - P) * V) p + t * colSlope ((1 - P) * V)
        (fun m' => sourceWeight D0 a.2 * (D * Vᴴ) m' a.1.2) (fun m => (P * V) a.1.1 m) p := by
  have hM : (1 - P) * (V + t • sourceDiffusion D0 P D a V) = (1 - P) * V + of fun l m =>
      (t : ℂ) * (((1 - P) * V) *ᵥ fun m' => sourceWeight D0 a.2 * (D * Vᴴ) m' a.1.2) l *
        (P * V) a.1.1 m := by
    rw [line_mul, far_noise_eq D0 P hPP]
    ext l m
    simp only [Matrix.add_apply, of_apply]
    ring
  rw [minorVec, minorVec, hM, det_colPerturb_submatrix]
  rfl

omit [DecidableEq ι] in
theorem minorSq_smul (k : ℕ) (r : ℂ) (L : Matrix ι c ℂ) :
    minorSq k (r • L) = (‖r‖ ^ 2) ^ k * minorSq k L := by
  unfold minorSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : (r • L).submatrix p.1 p.2 = r • L.submatrix p.1 p.2 := rfl
  rw [h, det_smul, Fintype.card_fin, norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm k 2]

omit [DecidableEq ι] [Fintype c] in
/-- Near drift: `P(V + t b(V)) = (1 + tα) PV`, `α = −D₀Naux/4`. -/
theorem near_drift_line (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (hPP : P * P = P)
    (V : Matrix ι c ℂ) (t : ℝ) :
    P * (V + t • sourceDrift D0 Naux P V) =
      ((1 + t * (-(D0 * Naux / 4)) : ℝ) : ℂ) • (P * V) := by
  rw [sourceDrift, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hPP]
  ext l m
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

omit [Fintype c] in
/-- Far drift: `(1−P)(V + t b(V)) = (1−P)V`. -/
theorem far_drift_line (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ)
    (hPP : P * P = P) (V : Matrix ι c ℂ) (t : ℝ) :
    (1 - P) * (V + t • sourceDrift D0 Naux P V) = (1 - P) * V := by
  have h0 : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  rw [sourceDrift, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, h0,
    Matrix.zero_mul, smul_zero, smul_zero, add_zero]

omit [DecidableEq ι] in
theorem near_drift_deriv (k : ℕ) {D0 : ℝ} (hD0 : 0 ≤ D0) (Naux : ℕ) (P : Matrix ι ι ℂ)
    (hPP : P * P = P) (V : Matrix ι c ℂ) :
    ∃ d ≤ 0, HasDerivAt (fun t : ℝ =>
      minorSq k (P * (V + t • sourceDrift D0 Naux P V)) / (k.factorial : ℝ) ^ 2) d 0 := by
  set α : ℝ := -(D0 * Naux / 4)
  set C : ℝ := minorSq k (P * V) / (k.factorial : ℝ) ^ 2
  have hC : 0 ≤ C := div_nonneg (minorSq_nonneg _ _) (by positivity)
  have hα : α ≤ 0 := by
    have : 0 ≤ D0 * Naux / 4 := by positivity
    show -(D0 * Naux / 4) ≤ 0
    linarith
  have hfun : (fun t : ℝ =>
      minorSq k (P * (V + t • sourceDrift D0 Naux P V)) / (k.factorial : ℝ) ^ 2) =
      fun t => ((1 + t * α) ^ 2) ^ k * C := by
    funext t
    rw [near_drift_line D0 Naux P hPP, minorSq_smul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    ring
  have hu : HasDerivAt (fun t : ℝ => (1 + t * α) ^ 2) (2 * α) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const α).const_add 1).pow 2
    exact this.congr_deriv (by simp)
  refine ⟨k * 1 * (2 * α) * C, ?_, ?_⟩
  · have : (k : ℝ) * 1 * (2 * α) ≤ 0 := by
      have := Nat.cast_nonneg (α := ℝ) k
      nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg this hC
  · rw [hfun]
    have := (hu.pow k).mul_const C
    exact this.congr_deriv (by simp)

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
