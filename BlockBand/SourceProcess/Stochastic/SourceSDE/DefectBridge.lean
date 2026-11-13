module
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms
public import Mathlib.Analysis.Matrix.MeasurableSpace
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The fderiv bridge for the projection defect

Projection preservation in the finite Gram law. The source algebra computes the Itô drift of the
defect `Φ(V) = ‖P'² - P'‖² + |Tr P' - Tr P|²` in product-rule form (`defectGenerator`). Here
we identify it with the true generator of the finite source equation:

* `sdeGenerator_defectLyapunov`:
  `sdeGenerator (sourceDrift D₀ Naux P) (sourceDiffusion D₀ P 𝖣) Φ V = defectGenerator … V`
  for every frame `V` (no hypothesis at all);
* `contDiff_defectLyapunov`: `Φ` is `C^∞` (real coordinates, Frobenius norm);
* `defectLyapunov_eq_zero_iff`: under `Pᴴ = P`, `𝖣ᴴ = 𝖣`, `Φ(V) = 0 ↔ TwoProjection P 𝖣 V`.

Route: `P' = P + gramBil 𝖣 (V, V)`, `F = mulBil (P', P') - P'`, `τ = Tr P' - Tr P`,
`Φ = reInner (F, F) + reMul (τ, τ)`, and the generator calculus (`vecGen_bilin` etc.).
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]
variable {κ : Type*} [Fintype κ]

section General

variable (b : Matrix ι c ℂ → Matrix ι c ℂ) (σ : κ → Matrix ι c ℂ → Matrix ι c ℂ)
  (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)

omit [DecidableEq ι] in
theorem gramProjection_fun_eq :
    (fun V : Matrix ι c ℂ => gramProjection P V D) = fun V => P + gramBil D V V := rfl

omit [DecidableEq ι] in
theorem fderiv_gramProjection (V H : Matrix ι c ℂ) :
    fderiv ℝ (fun V => gramProjection P V D) V H = V * D * Hᴴ + H * D * Vᴴ := by
  erw [gramProjection_fun_eq, fderiv_const_add,
    fderiv_bilin_apply _ differentiableAt_id differentiableAt_id]
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id]
  rfl

omit [DecidableEq ι] in
theorem vecGen_gramProjection (V : Matrix ι c ℂ) :
    vecGen b σ (fun V => gramProjection P V D) V =
      V * D * (b V)ᴴ + b V * D * Vᴴ + ∑ a, σ a V * D * (σ a V)ᴴ := by
  erw [gramProjection_fun_eq, vecGen_add b σ contDiff_const
      (contDiff_bilin (gramBil D) contDiff_id contDiff_id), vecGen_const,
    vecGen_bilin b σ _ contDiff_id contDiff_id, vecGen_id]
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id, zero_add]
  rfl

omit [DecidableEq ι] in
theorem projDefect_fun_eq : (fun V : Matrix ι c ℂ => projDefect P D V) =
    fun V => mulBil (gramProjection P V D) (gramProjection P V D) - gramProjection P V D := rfl

omit [DecidableEq ι] in
theorem contDiff_projDefect {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => projDefect P D V) := by
  rw [projDefect_fun_eq]
  exact (contDiff_bilin mulBil (contDiff_gramProjection P D) (contDiff_gramProjection P D)).sub
    (contDiff_gramProjection P D)

omit [DecidableEq ι] in
theorem fderiv_projDefect (V H : Matrix ι c ℂ) :
    fderiv ℝ (fun V => projDefect P D V) V H =
      gramProjection P V D * fderiv ℝ (fun V => gramProjection P V D) V H +
        fderiv ℝ (fun V => gramProjection P V D) V H * gramProjection P V D -
        fderiv ℝ (fun V => gramProjection P V D) V H := by
  have hd : Differentiable ℝ (fun V : Matrix ι c ℂ => gramProjection P V D) :=
    (contDiff_gramProjection (k := 1) P D).differentiable (by norm_num)
  have hm : Differentiable ℝ (fun V : Matrix ι c ℂ =>
      mulBil (gramProjection P V D) (gramProjection P V D)) :=
    (contDiff_bilin (n := 1) mulBil (contDiff_gramProjection P D)
      (contDiff_gramProjection P D)).differentiable (by norm_num)
  erw [projDefect_fun_eq, fderiv_sub_apply' (hm V) (hd V), fderiv_bilin_apply _ (hd V) (hd V)]
  rfl

omit [DecidableEq ι] in
theorem vecGen_projDefect (V : Matrix ι c ℂ) :
    vecGen b σ (fun V => projDefect P D V) V =
      gramProjection P V D * vecGen b σ (fun V => gramProjection P V D) V +
        vecGen b σ (fun V => gramProjection P V D) V * gramProjection P V D +
        ∑ a, fderiv ℝ (fun V => gramProjection P V D) V (σ a V) *
          fderiv ℝ (fun V => gramProjection P V D) V (σ a V) -
        vecGen b σ (fun V => gramProjection P V D) V := by
  erw [projDefect_fun_eq, vecGen_sub b σ (contDiff_bilin mulBil (contDiff_gramProjection P D)
      (contDiff_gramProjection P D)) (contDiff_gramProjection P D),
    vecGen_bilin b σ _ (contDiff_gramProjection P D) (contDiff_gramProjection P D)]
  rfl

omit [DecidableEq ι] in
theorem rankDefect_fun_eq : (fun V : Matrix ι c ℂ => rankDefect P D V) =
    fun V => traceCLM (gramProjection P V D) - P.trace := rfl

omit [DecidableEq ι] in
theorem contDiff_rankDefect {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => rankDefect P D V) := by
  rw [rankDefect_fun_eq]
  exact (traceCLM.contDiff.comp (contDiff_gramProjection P D)).sub contDiff_const

omit [DecidableEq ι] in
theorem fderiv_rankDefect (V H : Matrix ι c ℂ) :
    fderiv ℝ (fun V => rankDefect P D V) V H =
      (fderiv ℝ (fun V => gramProjection P V D) V H).trace := by
  have hd : Differentiable ℝ (fun V : Matrix ι c ℂ => gramProjection P V D) :=
    (contDiff_gramProjection (k := 1) P D).differentiable (by norm_num)
  erw [rankDefect_fun_eq, fderiv_sub_const, fderiv_clm_apply' traceCLM (hd V), traceCLM_apply]
  rfl

omit [DecidableEq ι] in
theorem vecGen_rankDefect (V : Matrix ι c ℂ) :
    vecGen b σ (fun V => rankDefect P D V) V =
      (vecGen b σ (fun V => gramProjection P V D) V).trace := by
  have h : ContDiff ℝ 2 (fun V : Matrix ι c ℂ => traceCLM (gramProjection P V D)) :=
    traceCLM.contDiff.comp (contDiff_gramProjection P D)
  erw [rankDefect_fun_eq, vecGen_sub b σ h contDiff_const, vecGen_const, sub_zero]
  exact vecGen_clm b σ traceCLM (contDiff_gramProjection P D) V

omit [DecidableEq ι] in
theorem defectLyapunov_fun_eq : defectLyapunov P D = fun V : Matrix ι c ℂ =>
    reInner (projDefect P D V) (projDefect P D V) +
      reMul (rankDefect P D V) (rankDefect P D V) := by
  funext V
  rw [reInner_self, reMul_self]
  rfl

omit [DecidableEq ι] in
/-- `Φ` is `C^∞`. -/
theorem contDiff_defectLyapunov {k : WithTop ℕ∞} :
    ContDiff ℝ k (defectLyapunov (c := c) P D) := by
  rw [defectLyapunov_fun_eq]
  exact (contDiff_bilin reInner (contDiff_projDefect P D) (contDiff_projDefect P D)).add
    (contDiff_bilin reMul (contDiff_rankDefect P D) (contDiff_rankDefect P D))

omit [DecidableEq ι] in
theorem vecGen_defectLyapunov (V : Matrix ι c ℂ) :
    vecGen b σ (defectLyapunov P D) V =
      reInner (projDefect P D V) (vecGen b σ (fun V => projDefect P D V) V) +
          reInner (vecGen b σ (fun V => projDefect P D V) V) (projDefect P D V) +
        ∑ a, reInner (fderiv ℝ (fun V => projDefect P D V) V (σ a V))
          (fderiv ℝ (fun V => projDefect P D V) V (σ a V)) +
      (reMul (rankDefect P D V) (vecGen b σ (fun V => rankDefect P D V) V) +
          reMul (vecGen b σ (fun V => rankDefect P D V) V) (rankDefect P D V) +
        ∑ a, reMul (fderiv ℝ (fun V => rankDefect P D V) V (σ a V))
          (fderiv ℝ (fun V => rankDefect P D V) V (σ a V))) := by
  erw [defectLyapunov_fun_eq, vecGen_add b σ
      (contDiff_bilin reInner (contDiff_projDefect P D) (contDiff_projDefect P D))
      (contDiff_bilin reMul (contDiff_rankDefect P D) (contDiff_rankDefect P D)),
    vecGen_bilin b σ reInner (contDiff_projDefect P D) (contDiff_projDefect P D),
    vecGen_bilin b σ reMul (contDiff_rankDefect P D) (contDiff_rankDefect P D)]
  rfl

end General

/-!
### Specialization to the finite source equation
-/

theorem vecGen_gramProjection_source (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) :
    vecGen (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (fun V => gramProjection P V D) V =
      projDrift D0 Naux P D V := by
  rw [vecGen_gramProjection, projDrift, add_comm (V * D * _)]

theorem fderiv_gramProjection_source (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    fderiv ℝ (fun V => gramProjection P V D) V (sourceDiffusion D0 P D a V) =
      projNoise D0 P D a V := by
  rw [fderiv_gramProjection, projNoise, add_comm]

/-- **The fderiv bridge**: the generator of applied
to the projection defect `Φ` is the product-rule expression `defectGenerator`, for every `V`.
-/
theorem sdeGenerator_defectLyapunov (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) :
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (defectLyapunov P D) V =
      defectGenerator D0 Naux P D V := by
  rw [sdeGenerator_eq_vecGen, vecGen_defectLyapunov, vecGen_projDefect, vecGen_rankDefect,
    vecGen_gramProjection_source, reInner_comm (projDefect P D V), reMul_comm (rankDefect P D V)]
  simp only [fderiv_projDefect, fderiv_rankDefect, fderiv_gramProjection_source, reInner_self,
    reMul_self, defectGenerator, reInner_apply, reMul_apply]
  have e1 : gramProjection P V D * projDrift D0 Naux P D V +
      projDrift D0 Naux P D V * gramProjection P V D +
      ∑ a, projNoise D0 P D a V * projNoise D0 P D a V - projDrift D0 Naux P D V =
      defectDrift D0 Naux P D V := by
    rw [defectDrift]
    abel
  have e2 : ∀ a, gramProjection P V D * projNoise D0 P D a V +
      projNoise D0 P D a V * gramProjection P V D - projNoise D0 P D a V =
      defectNoise D0 P D a V := fun a => by
    rw [defectNoise]
    abel
  rw [e1]
  simp only [e2, rankNoise, rankDrift]
  ring

omit [DecidableEq ι] in
theorem defectLyapunov_nonneg (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    0 ≤ defectLyapunov P D V := by
  unfold defectLyapunov
  positivity

omit [DecidableEq ι] in
/-- The constraint is the zero set of `Φ` (Hermitian `P'` is automatic). -/
theorem defectLyapunov_eq_zero_iff {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hDH : Dᴴ = D) (V : Matrix ι c ℂ) : defectLyapunov P D V = 0 ↔ TwoProjection P D V := by
  unfold defectLyapunov
  rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity), sq_eq_zero_iff, sq_eq_zero_iff,
    norm_eq_zero, norm_eq_zero, projDefect, rankDefect, sub_eq_zero, sub_eq_zero]
  exact ⟨fun h => ⟨gramProjection_conjTranspose hPH hDH V, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

end BlockBand.SourceProcess.Stochastic.SourceSDE
