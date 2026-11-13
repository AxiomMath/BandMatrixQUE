module

public import BlockBand.SourceProcess.Stochastic.SourceSDE.TraceBound

/-!
# Noise contractions of the finite-source SDE

* `sum_reInner_noise`: for the noise coefficients `w_r Q E_jk A` of the finite-source SDE,
  `∑_a Re Tr((w Q₁ E A₁)ᴴ (w Q₂ E A₂)) = (D₀/2) Re(Tr(Q₁ᴴQ₂) Tr(A₁ᴴA₂))`
  (`E|dZ|² = 2dt`, `∑_{jk} E_kj X E_jk = Tr X`); this is `dA₁ dA₂* = (D₀/2) Tr(P₁'P₂') P dt`.
* `sum_norm_sq_sourceDiffusion_mul`: on the constraint, `∑_a ‖σ_a(V) F‖² = (D₀/2) Naux ‖PVF‖²`.
* `sdeGenerator_normSq_mul_eq_zero`: on the constraint, the trace `‖VF‖²` of any right factor
  of a constrained frame has zero Itô drift (the trace martingale of each column group).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

omit [DecidableEq ι] in
theorem reInner_smul_smul (w : ℂ) (X Y : Matrix ι c ℂ) :
    reInner (w • X) (w • Y) = (star w * w * (Xᴴ * Y).trace).re := by
  simp only [reInner_apply, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
    smul_eq_mul]
  ring_nf

theorem sum_unit_trace (Q₁ Q₂ : Matrix ι ι ℂ) (A₁ A₂ : Matrix ι c ℂ) :
    ∑ e : ι × ι, ((Q₁ * Matrix.single e.2 e.1 (1 : ℂ) * A₁)ᴴ *
        (Q₂ * Matrix.single e.2 e.1 (1 : ℂ) * A₂)).trace =
      (Q₁ᴴ * Q₂).trace * (A₁ᴴ * A₂).trace := by
  have h : ∀ e : ι × ι, ((Q₁ * Matrix.single e.2 e.1 (1 : ℂ) * A₁)ᴴ *
      (Q₂ * Matrix.single e.2 e.1 (1 : ℂ) * A₂)).trace =
      (A₁ᴴ * (Matrix.single e.1 e.2 (1 : ℂ) * (Q₁ᴴ * Q₂) * Matrix.single e.2 e.1 (1 : ℂ)) *
        A₂).trace := fun e => by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_single, star_one]
    simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun e _ => h e, ← trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum,
    sum_unit_conj_mul_unit]
  simp [Matrix.mul_smul, Matrix.smul_mul, trace_smul]

/-- **The noise contraction.** -/
theorem sum_reInner_noise {D0 : ℝ} (hD0 : 0 ≤ D0) (Q₁ Q₂ : Matrix ι ι ℂ) (A₁ A₂ : Matrix ι c ℂ) :
    ∑ a : SourceNoise ι, reInner (sourceWeight D0 a.2 • (Q₁ * sourceUnit a * A₁))
        (sourceWeight D0 a.2 • (Q₂ * sourceUnit a * A₂)) =
      D0 / 2 * ((Q₁ᴴ * Q₂).trace * (A₁ᴴ * A₂).trace).re := by
  simp only [reInner_smul_smul]
  rw [Fintype.sum_prod_type]
  have h : ∀ e : ι × ι, ∑ r : Fin 2, (star (sourceWeight D0 r) * sourceWeight D0 r *
      ((Q₁ * sourceUnit (e, r) * A₁)ᴴ * (Q₂ * sourceUnit (e, r) * A₂)).trace).re =
      (((D0 / 2 : ℝ) : ℂ) * ((Q₁ * Matrix.single e.2 e.1 (1 : ℂ) * A₁)ᴴ *
        (Q₂ * Matrix.single e.2 e.1 (1 : ℂ) * A₂)).trace).re := fun e => by
    rw [← sum_star_weight_mul hD0, Finset.sum_mul, Complex.re_sum]
    rfl
  rw [Finset.sum_congr rfl fun e _ => h e, ← Complex.re_sum, ← Finset.mul_sum, sum_unit_trace,
    Complex.re_ofReal_mul]

theorem sourceDiffusion_eq' (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) :
    sourceDiffusion D0 P D a V =
      sourceWeight D0 a.2 • (gramProjection P V D * sourceUnit a * (P * V)) := by
  rw [sourceDiffusion_eq, sourceNoiseMatrix, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

theorem sourceDiffusion_mul (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) (F : Matrix c c ℂ) :
    sourceDiffusion D0 P D a V * F =
      sourceWeight D0 a.2 • (gramProjection P V D * sourceUnit a * (P * V * F)) := by
  rw [sourceDiffusion_eq', Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem sourceDrift_mul (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ)
    (F : Matrix c c ℂ) : sourceDrift D0 Naux P V * F = sourceDrift D0 Naux P (V * F) := by
  rw [sourceDrift, sourceDrift, Matrix.smul_mul, Matrix.mul_assoc]

/-- `∑_a ‖σ_a(V) F‖² = (D₀/2) Naux ‖PVF‖²` on the constraint. -/
theorem sum_norm_sq_sourceDiffusion_mul {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) (F : Matrix c c ℂ) :
    ∑ a, ‖sourceDiffusion D0 P D a V * F‖ ^ 2 = D0 / 2 * Naux * ‖P * V * F‖ ^ 2 := by
  simp_rw [← reInner_self, sourceDiffusion_mul]
  rw [sum_reInner_noise hD0, ← frob_sq_eq_trace, ← frob_sq_eq_trace,
    frob_sq_gramProjection hP hV, ← Complex.ofReal_mul,
    Complex.ofReal_re, reInner_self]
  ring

/-- **Zero trace drift of a right factor**: `𝓛‖·‖²(VF) = 0` for the coefficients of `V`
multiplied on the right by `F`, on the constraint. -/
theorem sdeGenerator_normSq_mul_eq_zero {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) (F : Matrix c c ℂ) :
    sdeGenerator (fun _ => sourceDrift D0 Naux P V * F)
      (fun a _ => sourceDiffusion D0 P D a V * F) (fun W : Matrix ι c ℂ => ‖W‖ ^ 2) (V * F) =
      0 := by
  rw [sdeGenerator_normSq, sourceDrift_mul, reInner_comm (V * F),
    reInner_sourceDrift hP.1 hP.2.1]
  simp only [reInner_self]
  rw [sum_norm_sq_sourceDiffusion_mul hD0 hP hV F, Matrix.mul_assoc]
  ring

end BlockBand.SourceProcess.RankFree
