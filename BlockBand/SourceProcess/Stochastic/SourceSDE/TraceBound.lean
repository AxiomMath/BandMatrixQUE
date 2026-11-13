module
public import BlockBand.SourceProcess.Stochastic.SourceSDE.DefectBridge
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The trace Lyapunov function `Tr M = ‖V‖²` for nonexplosion

In the finite Gram law, local strong uniqueness and the nonnegative trace martingale `Tr M` give
nonexplosion. Frobenius norm; `Φ(V) = ‖V‖²`.

* `sdeGenerator_normSq`: the generator of the finite source equation on `Φ` is
  `2 Re Tr(Vᴴ b) + ∑_a ‖σ_a‖²` (fderiv bridge, product-rule form; `reInner` order).
* `sdeGenerator_normSq_le`: on the constraint `TwoProjection P 𝖣 V` (and `0 ≤ D₀`,
  `IsNearProjection P Naux`), `𝓛Φ(V) ≤ C ‖V‖²` with the explicit uniform constant
  `C = card(SourceNoise ι) (√D₀/2 · Naux)²`. The drift term is `-(D₀Naux/2)‖PV‖² ≤ 0`; each noise
  coefficient obeys `‖σ_a(V)‖ ≤ (√D₀/2) Naux ‖V‖` because `‖P'‖²_F = ‖P‖²_F = Naux`
  (`frob_sq_gramProjection`). This is the Lyapunov hypothesis `𝓛Φ ≤ C(1 + Φ)` of
  `NonexplosionFor` (weaker than the paper's exact martingale identity, which is not needed).
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]
variable {κ : Type*} [Fintype κ]

omit [DecidableEq ι] in
theorem normSq_fun_eq : (fun V : Matrix ι c ℂ => ‖V‖ ^ 2) = fun V => reInner V V :=
  funext fun V => (reInner_self V).symm

omit [DecidableEq ι] in
theorem contDiff_normSq {k : WithTop ℕ∞} : ContDiff ℝ k (fun V : Matrix ι c ℂ => ‖V‖ ^ 2) := by
  rw [normSq_fun_eq]
  exact contDiff_bilin reInner contDiff_id contDiff_id

omit [DecidableEq ι] in
theorem sdeGenerator_normSq (b : Matrix ι c ℂ → Matrix ι c ℂ)
    (σ : κ → Matrix ι c ℂ → Matrix ι c ℂ) (V : Matrix ι c ℂ) :
    sdeGenerator b σ (fun V : Matrix ι c ℂ => ‖V‖ ^ 2) V =
      reInner V (b V) + reInner (b V) V + ∑ a, reInner (σ a V) (σ a V) := by
  rw [sdeGenerator_eq_vecGen]
  erw [normSq_fun_eq, vecGen_bilin b σ reInner contDiff_id contDiff_id, vecGen_id]
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id]

omit [DecidableEq ι] in
theorem reInner_sourceDrift {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) (V : Matrix ι c ℂ) :
    reInner V (sourceDrift D0 Naux P V) = -(D0 * Naux / 4) * ‖P * V‖ ^ 2 := by
  rw [reInner_apply, sourceDrift, Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    ← reInner_self, reInner_apply, conjTranspose_mul, hPH, Matrix.mul_assoc, ← Matrix.mul_assoc P,
    hPP]

theorem sourceDiffusion_norm_le {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux) (hV : TwoProjection P D V)
    (a : SourceNoise ι) :
    ‖sourceDiffusion D0 P D a V‖ ≤ Real.sqrt D0 / 2 * Naux * ‖V‖ := by
  have hPp : ‖gramProjection P V D‖ = Real.sqrt Naux := by
    rw [← frob_sq_gramProjection hP hV, Real.sqrt_sq (norm_nonneg _)]
  have hPn : ‖P‖ = Real.sqrt Naux := by
    rw [← frob_sq_nearProjection hP, Real.sqrt_sq (norm_nonneg _)]
  rw [sourceDiffusion_eq, sourceNoiseMatrix, Matrix.smul_mul, norm_smul, norm_sourceWeight]
  calc Real.sqrt D0 / 2 * ‖gramProjection P V D * sourceUnit a * P * V‖
      ≤ Real.sqrt D0 / 2 * (‖gramProjection P V D‖ * ‖sourceUnit a‖ * ‖P‖ * ‖V‖) := by
        gcongr; exact frob_mul4_le _ _ _ _
    _ = Real.sqrt D0 / 2 * Naux * ‖V‖ := by
        rw [hPp, hPn, sourceUnit, frob_single, mul_one, ← sq, Real.sq_sqrt (Nat.cast_nonneg _)]
        ring

/-- **Trace Lyapunov bound on the constraint.** -/
theorem sdeGenerator_normSq_le {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) {V : Matrix ι c ℂ}
    (hV : TwoProjection P D V) :
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (fun V : Matrix ι c ℂ => ‖V‖ ^ 2)
        V ≤ (Fintype.card (SourceNoise ι) * (Real.sqrt D0 / 2 * Naux) ^ 2) * ‖V‖ ^ 2 := by
  rw [sdeGenerator_normSq, reInner_comm V (sourceDrift D0 Naux P V),
    reInner_sourceDrift hP.1 hP.2.1]
  simp only [reInner_self]
  have h1 : -(D0 * Naux / 4) * ‖P * V‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by have : (0 : ℝ) ≤ Naux := Nat.cast_nonneg _; nlinarith)
      (sq_nonneg _)
  have h2 : ∑ a, ‖sourceDiffusion D0 P D a V‖ ^ 2 ≤
      ∑ _a : SourceNoise ι, (Real.sqrt D0 / 2 * Naux * ‖V‖) ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      pow_le_pow_left₀ (norm_nonneg _) (sourceDiffusion_norm_le hP hV a) 2
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  nlinarith [h1, h2]

end BlockBand.SourceProcess.Stochastic.SourceSDE
