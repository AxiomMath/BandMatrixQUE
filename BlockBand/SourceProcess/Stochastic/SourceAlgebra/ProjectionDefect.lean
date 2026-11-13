module
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.GramBrackets
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Projection preservation: the defect equations are linear

In the proof of the finite Gram law, projection preservation is checked without a formal appeal
to covariance, through the two diagonal Itô equations for `(P')² = P'`. Here the check is made
*off* the constraint, as needed for a
Gronwall argument: for every frame `V` (no `TwoProjection` hypothesis) we compute, by the
product rule (`ItoProductRuleFor`), the Itô drift and diffusion of

* `P' = P + V𝖣Vᴴ` (`projDrift`, `projNoise`; bilinear map `(X,Y) ↦ X𝖣Yᴴ`),
* the projection defect `F = P'² - P'` (`defectDrift`, `defectNoise`; bilinear `(X,Y) ↦ XY`),
* the rank defect `τ = Tr P' - Tr P` (`rankDrift`, `rankNoise`),

and prove they are linear in `(F, τ)` with coefficients polynomial in `(V, P)`
(`defectNoise_eq`, `defectDrift_eq`, `rankNoise_eq`, `rankDrift_eq`). Only `Pᴴ = P`,
`P² = P`, `Tr P = Naux` and `𝖣ᴴ = 𝖣` are used (`𝖣³ = 𝖣` is not needed). The hypothesis
`Tr P = Naux` is required: otherwise `defectDrift` acquires the extra term
`(D₀/2)(Tr P - Naux) JPJ`, which does not vanish at `F = 0, τ = 0`.
Here `J = P' - P = V𝖣Vᴴ` is the adopted `fullCurrent`.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceAlgebra
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

/-- Diffusion of `P'` along `a`: `σ_a 𝖣 Vᴴ + V 𝖣 σ_aᴴ`. -/
def projNoise (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : Matrix ι ι ℂ :=
  sourceDiffusion D0 P D a V * D * Vᴴ + V * D * (sourceDiffusion D0 P D a V)ᴴ

/-- Itô drift of `P'`: `b 𝖣 Vᴴ + V 𝖣 bᴴ + ∑_a σ_a 𝖣 σ_aᴴ`. -/
def projDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) : Matrix ι ι ℂ :=
  sourceDrift D0 Naux P V * D * Vᴴ + V * D * (sourceDrift D0 Naux P V)ᴴ +
    ∑ a, sourceDiffusion D0 P D a V * D * (sourceDiffusion D0 P D a V)ᴴ

/-- Projection defect `F = P'² - P'`. -/
def projDefect (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) : Matrix ι ι ℂ :=
  gramProjection P V D * gramProjection P V D - gramProjection P V D

/-- Rank defect `τ = Tr P' - Tr P`. -/
def rankDefect (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) : ℂ :=
  (gramProjection P V D).trace - P.trace

/-- Diffusion of `F` along `a` (product rule): `N P' + P' N - N`. -/
def defectNoise (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : Matrix ι ι ℂ :=
  projNoise D0 P D a V * gramProjection P V D + gramProjection P V D * projNoise D0 P D a V -
    projNoise D0 P D a V

/-- Itô drift of `F` (product rule): `K P' + P' K + ∑_a N_a N_a - K`. -/
def defectDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) : Matrix ι ι ℂ :=
  projDrift D0 Naux P D V * gramProjection P V D + gramProjection P V D * projDrift D0 Naux P D V +
    ∑ a, projNoise D0 P D a V * projNoise D0 P D a V - projDrift D0 Naux P D V

/-- Diffusion of `τ` along `a`. -/
def rankNoise (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : ℂ := (projNoise D0 P D a V).trace

/-- Itô drift of `τ`. -/
def rankDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) : ℂ := (projDrift D0 Naux P D V).trace

omit [Fintype ι] [DecidableEq ι] in
theorem gramProjection_conjTranspose {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    (hPH : Pᴴ = P) (hDH : Dᴴ = D) (V : Matrix ι c ℂ) :
    (gramProjection P V D)ᴴ = gramProjection P V D := by
  simp [gramProjection, conjTranspose_add, conjTranspose_mul, hPH, hDH, Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem fullCurrent_gramProjection (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    fullCurrent P (gramProjection P V D) = V * D * Vᴴ := gram_current_eq P V D

/-- Closed form of the noise of `P'` (all `V`):
`N_a = w (P' E P J) + conj(w) (J P Eᴴ P')`. -/
theorem projNoise_eq (D0 : ℝ) {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hDH : Dᴴ = D) (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    projNoise D0 P D a V =
      sourceWeight D0 a.2 • (gramProjection P V D * Matrix.single a.1.2 a.1.1 (1 : ℂ) * P *
          fullCurrent P (gramProjection P V D)) +
        star (sourceWeight D0 a.2) • (fullCurrent P (gramProjection P V D) * P *
          Matrix.single a.1.1 a.1.2 (1 : ℂ) * gramProjection P V D) := by
  have hP' := gramProjection_conjTranspose hPH hDH V
  rw [projNoise, sourceDiffusion_eq, sourceNoiseMatrix, sourceUnit, fullCurrent_gramProjection]
  simp only [conjTranspose_mul, conjTranspose_smul, conjTranspose_single, star_one, hPH, hP',
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- Second-order contraction `∑_a N_a X N_aᴴ = (D₀/2) Tr(P X Pᴴ) P'P'ᴴ` for the coefficient
`N_a` of `dAᴴ` (all `V`). -/
theorem sum_noiseMatrix_mul_conj {D0 : ℝ} (hD0 : 0 ≤ D0) (P X : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    ∑ a, sourceNoiseMatrix D0 P D a V * X * (sourceNoiseMatrix D0 P D a V)ᴴ =
      ((D0 / 2 : ℝ) : ℂ) •
        ((P * X * Pᴴ).trace • (gramProjection P V D * (gramProjection P V D)ᴴ)) := by
  have h : ∀ a : SourceNoise ι,
      sourceNoiseMatrix D0 P D a V * X * (sourceNoiseMatrix D0 P D a V)ᴴ =
        (star (sourceWeight D0 a.2) * sourceWeight D0 a.2) •
          (gramProjection P V D * (Matrix.single a.1.2 a.1.1 (1 : ℂ) * (P * X * Pᴴ) *
            Matrix.single a.1.1 a.1.2 (1 : ℂ)) * (gramProjection P V D)ᴴ) := by
    intro a
    simp only [sourceNoiseMatrix, sourceUnit, conjTranspose_mul, conjTranspose_smul,
      conjTranspose_single, star_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc]
  simp_rw [h]
  refine (sum_sourceNoise_star_mul hD0 (fun e : ι × ι =>
    gramProjection P V D * (Matrix.single e.2 e.1 (1 : ℂ) * (P * X * Pᴴ) *
      Matrix.single e.1 e.2 (1 : ℂ)) * (gramProjection P V D)ᴴ)).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_unit_mul_unit_conj]
  simp

omit [DecidableEq ι] in
theorem trace_near_sandwich {P : Matrix ι ι ℂ} (hP : P * P = P) (X : Matrix ι ι ℂ) :
    (P * X * P).trace = (P * X).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP]

/-- Closed form of the drift of `P'` (all `V`):
`K = -(D₀Naux/4)(PJ + JP) + (D₀/2) Tr(PJ) P'²`. -/
theorem projDrift_eq {D0 : ℝ} (hD0 : 0 ≤ D0) (Naux : ℕ) {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hPH : Pᴴ = P) (hPP : P * P = P) (hDH : Dᴴ = D) (V : Matrix ι c ℂ) :
    projDrift D0 Naux P D V =
      ((-(D0 * Naux / 4) : ℝ) : ℂ) • (P * fullCurrent P (gramProjection P V D) +
          fullCurrent P (gramProjection P V D) * P) +
        ((D0 / 2 : ℝ) : ℂ) • ((P * fullCurrent P (gramProjection P V D)).trace •
          (gramProjection P V D * gramProjection P V D)) := by
  have h : ∑ a, sourceDiffusion D0 P D a V * D * (sourceDiffusion D0 P D a V)ᴴ =
      ∑ a, sourceNoiseMatrix D0 P D a V * (V * D * Vᴴ) * (sourceNoiseMatrix D0 P D a V)ᴴ := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sourceDiffusion_eq, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [projDrift, h, sum_noiseMatrix_mul_conj hD0, ← fullCurrent_gramProjection P D V, hPH,
    trace_near_sandwich hPP, gramProjection_conjTranspose hPH hDH, sourceDrift,
    fullCurrent_gramProjection]
  simp only [conjTranspose_smul, conjTranspose_mul, Complex.star_def, Complex.conj_ofReal, hPH,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_add]

/-- The second-order sum of the noise of `P'` (all `V`):
`∑_a N_a N_a = (D₀/2)[Tr(PJ²P) P'² + Tr(P'²) J P² J]`. -/
theorem sum_projNoise_mul {D0 : ℝ} (hD0 : 0 ≤ D0) {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    (hPH : Pᴴ = P) (hDH : Dᴴ = D) (V : Matrix ι c ℂ) :
    ∑ a, projNoise D0 P D a V * projNoise D0 P D a V =
      ((D0 / 2 : ℝ) : ℂ) •
        ((P * fullCurrent P (gramProjection P V D) * fullCurrent P (gramProjection P V D) *
            P).trace • (gramProjection P V D * gramProjection P V D) +
          (gramProjection P V D * gramProjection P V D).trace •
            (fullCurrent P (gramProjection P V D) * P * P * fullCurrent P (gramProjection P V D))) := by
  simp only [projNoise_eq D0 hPH hDH]
  set Pp := gramProjection P V D
  set J := fullCurrent P Pp
  refine (sum_sourceNoise_mul (A := Matrix ι ι ℂ) hD0
    (fun e : ι × ι => Pp * Matrix.single e.2 e.1 (1 : ℂ) * P * J)
    (fun e : ι × ι => J * P * Matrix.single e.1 e.2 (1 : ℂ) * Pp)
    (fun e : ι × ι => Pp * Matrix.single e.2 e.1 (1 : ℂ) * P * J)
    (fun e : ι × ι => J * P * Matrix.single e.1 e.2 (1 : ℂ) * Pp)).trans ?_
  congr 1
  have h1 : ∀ e : ι × ι, Pp * Matrix.single e.2 e.1 (1 : ℂ) * P * J *
      (J * P * Matrix.single e.1 e.2 (1 : ℂ) * Pp) =
      Pp * (Matrix.single e.2 e.1 (1 : ℂ) * (P * J * J * P) * Matrix.single e.1 e.2 (1 : ℂ)) * Pp := by
    intro e; simp only [Matrix.mul_assoc]
  have h2 : ∀ e : ι × ι, J * P * Matrix.single e.1 e.2 (1 : ℂ) * Pp *
      (Pp * Matrix.single e.2 e.1 (1 : ℂ) * P * J) =
      J * P * (Matrix.single e.1 e.2 (1 : ℂ) * (Pp * Pp) * Matrix.single e.2 e.1 (1 : ℂ)) *
        (P * J) := by
    intro e; simp only [Matrix.mul_assoc]
  rw [Finset.sum_add_distrib]
  simp only [h1, h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_unit_mul_unit_conj, sum_unit_conj_mul_unit]
  simp [Matrix.mul_assoc]

/-!
### Linearity of the defect equations
-/

/-- **Noise of the projection defect is linear in `F`** (all `V`):
`dF_a = w (P'EPF + FEPJ) + conj(w) (JPEᴴF + FPEᴴP')`. -/
theorem defectNoise_eq (D0 : ℝ) {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) (hDH : Dᴴ = D) (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    defectNoise D0 P D a V =
      sourceWeight D0 a.2 •
          (gramProjection P V D * Matrix.single a.1.2 a.1.1 (1 : ℂ) * P * projDefect P D V +
            projDefect P D V * Matrix.single a.1.2 a.1.1 (1 : ℂ) * P *
              fullCurrent P (gramProjection P V D)) +
        star (sourceWeight D0 a.2) •
          (fullCurrent P (gramProjection P V D) * P * Matrix.single a.1.1 a.1.2 (1 : ℂ) *
              projDefect P D V +
            projDefect P D V * P * Matrix.single a.1.1 a.1.2 (1 : ℂ) * gramProjection P V D) := by
  rw [defectNoise, projNoise_eq D0 hPH hDH, projDefect, fullCurrent]
  set Pp := gramProjection P V D
  simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc,
    hPP, smul_add, smul_sub]
  module

omit [DecidableEq ι] in
theorem trace_near_current {Naux : ℕ} {P : Matrix ι ι ℂ} (hP : IsNearProjection P Naux)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    (P * fullCurrent P (gramProjection P V D)).trace =
      (P * gramProjection P V D).trace - Naux := by
  rw [fullCurrent, mul_sub, trace_sub, hP.2.1, hP.2.2]

omit [DecidableEq ι] in
theorem trace_near_current_sq {Naux : ℕ} {P : Matrix ι ι ℂ} (hP : IsNearProjection P Naux)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    (P * fullCurrent P (gramProjection P V D) * fullCurrent P (gramProjection P V D) *
        P).trace =
      (P * projDefect P D V).trace + Naux - (P * gramProjection P V D).trace := by
  have hPP := hP.2.1
  set Pp := gramProjection P V D
  rw [Matrix.mul_assoc P, trace_near_sandwich hPP]
  have e : P * (fullCurrent P Pp * fullCurrent P Pp) = P * projDefect P D V - P * Pp * P + P := by
    have h2 : ∀ X : Matrix ι ι ℂ, P * (P * X) = P * X := fun X => by
      rw [← Matrix.mul_assoc, hPP]
    simp only [fullCurrent, projDefect, Pp, mul_sub, sub_mul, Matrix.mul_assoc, hPP, h2]
    abel
  rw [e, trace_add, trace_sub, trace_near_sandwich hPP, hP.2.2]
  ring

omit [DecidableEq ι] in
theorem trace_projection_sq {Naux : ℕ} {P : Matrix ι ι ℂ} (hP : IsNearProjection P Naux)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    (gramProjection P V D * gramProjection P V D).trace =
      (projDefect P D V).trace + rankDefect P D V + Naux := by
  rw [projDefect, rankDefect, trace_sub, hP.2.2]
  ring

/-- **Drift of the projection defect is linear in `(F, τ)`** (all `V`), with
`γ = Naux - Tr(PP')`:
`dF/dt = -(D₀Naux/4)(PF + FP) - D₀ γ P'F + (D₀/2)[Tr(PF) P'² + (Tr F + τ) JPJ]`. -/
theorem defectDrift_eq {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D) (V : Matrix ι c ℂ) :
    defectDrift D0 Naux P D V =
      ((-(D0 * Naux / 4) : ℝ) : ℂ) • (P * projDefect P D V + projDefect P D V * P) -
        ((D0 : ℂ) * ((Naux : ℂ) - (P * gramProjection P V D).trace)) •
          (gramProjection P V D * projDefect P D V) +
        ((D0 / 2 : ℝ) : ℂ) •
          ((P * projDefect P D V).trace • (gramProjection P V D * gramProjection P V D) +
            ((projDefect P D V).trace + rankDefect P D V) •
              (fullCurrent P (gramProjection P V D) * P * fullCurrent P (gramProjection P V D))) := by
  rw [defectDrift, sum_projNoise_mul hD0 hP.1 hDH, projDrift_eq hD0 Naux hP.1 hP.2.1 hDH,
    trace_near_current hP, trace_near_current_sq hP, trace_projection_sq hP]
  generalize (P * projDefect P D V).trace = u
  generalize (projDefect P D V).trace = f
  generalize rankDefect P D V = t
  generalize (P * gramProjection P V D).trace = s
  have hPP := hP.2.1
  rw [projDefect, fullCurrent]
  set Pp := gramProjection P V D
  push_cast
  simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc,
    hPP, smul_add, smul_sub]
  module

/-- **Noise of the rank defect is linear in `F`** (all `V`):
`dτ_a = w Tr(E P F) + conj(w) Tr(F P Eᴴ)`. -/
theorem rankNoise_eq (D0 : ℝ) {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) (hDH : Dᴴ = D) (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    rankNoise D0 P D a V =
      sourceWeight D0 a.2 * (Matrix.single a.1.2 a.1.1 (1 : ℂ) * (P * projDefect P D V)).trace +
        star (sourceWeight D0 a.2) *
          (projDefect P D V * P * Matrix.single a.1.1 a.1.2 (1 : ℂ)).trace := by
  rw [rankNoise, projNoise_eq D0 hPH hDH, trace_add, trace_smul, trace_smul, smul_eq_mul,
    smul_eq_mul]
  set Pp := gramProjection P V D
  congr 2
  · rw [show Pp * Matrix.single a.1.2 a.1.1 (1 : ℂ) * P * fullCurrent P Pp =
        Pp * (Matrix.single a.1.2 a.1.1 (1 : ℂ) * P * fullCurrent P Pp) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm Pp]
    congr 1
    simp only [projDefect, fullCurrent, Pp, mul_sub, sub_mul, Matrix.mul_assoc, hPP]
  · rw [Matrix.trace_mul_comm _ Pp]
    congr 1
    simp only [projDefect, fullCurrent, Pp, mul_sub, sub_mul, Matrix.mul_assoc, hPP]

/-- **Drift of the rank defect is linear in `(F, τ)`** (all `V`):
`dτ/dt = -(D₀/2)(Naux - Tr(PP'))(Tr F + τ)`. -/
theorem rankDrift_eq {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D) (V : Matrix ι c ℂ) :
    rankDrift D0 Naux P D V =
      -(((D0 / 2 : ℝ) : ℂ) * ((Naux : ℂ) - (P * gramProjection P V D).trace)) *
        ((projDefect P D V).trace + rankDefect P D V) := by
  rw [rankDrift, projDrift_eq hD0 Naux hP.1 hP.2.1 hDH, trace_add, trace_smul, trace_smul,
    trace_smul, trace_add, Matrix.trace_mul_comm (fullCurrent _ _) P, trace_near_current hP,
    trace_projection_sq hP]
  simp only [smul_eq_mul]
  push_cast
  ring

end BlockBand.SourceProcess.Stochastic.SourceAlgebra
