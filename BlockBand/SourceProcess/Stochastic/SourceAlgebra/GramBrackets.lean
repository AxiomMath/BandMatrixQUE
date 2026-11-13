module
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.ItoTable
public import BlockBand.SourceProcess.NoiseContraction
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram drift and brackets of the finite source equation

Deterministic content of the finite Gram law (the Gram drift and covariance) and of its proof:
for the exact coefficients `sourceDrift`/`sourceDiffusion`, the product-rule
(Itô) drift and the diffusion coefficients of the quadratic forms `VᴴQV`, in particular
`M = VᴴV` (`Q = 1`) and `B = VᴴPV` (`Q = P`).

For a real-bilinear `β(X,Y) = XᴴQY` the product rule (`ItoProductRuleFor`) gives drift
`β(b,V) + β(V,b) + ∑_a β(σ_a,σ_a)` and diffusion
`β(σ_a,V) + β(V,σ_a)`; these are `quadDrift` and `quadVariation … (sourceDiffusion …)`.

* `quad_bracket`: the complex-bilinear bracket of two such forms, valid for every `V`
  (no constraint, no Hermiticity);
* `gram_bracket_MM/MB/BB`: under `TwoProjection` these are exactly the `crossedBracket`
  patterns of `FiniteSourceGramCharacteristics` (via the adopted `crossed_coefficient_*`);
* `quadDrift_eq`, `gram_drift_M`, `gram_drift_B`: drift `0` and `-(D₀/2) g B`;
* `sum_dA_mul_dA_conj`, `sum_dA_P_mul_dA_conj`: `dA dAᴴ = (D₀Naux/2)P`,
  `dA P dAᴴ = (D₀(Naux-g)/2) P` (per unit time).
No inverse or rank assumption; `0 ≤ D₀` only for `(√D₀)² = D₀`.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceAlgebra
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

/-- First-order variation `HᴴQV + VᴴQH` of `V ↦ VᴴQV` along `H`. -/
def quadVariation (Q : Matrix ι ι ℂ) (V H : Matrix ι c ℂ) : Matrix c c ℂ :=
  Hᴴ * Q * V + Vᴴ * Q * H

/-- Variation `dM = dVᴴ V + Vᴴ dV` of `M = VᴴV`. -/
def gramVariation (V H : Matrix ι c ℂ) : Matrix c c ℂ := Hᴴ * V + Vᴴ * H

/-- Variation `dB = dVᴴ P V + Vᴴ P dV` of `B = VᴴPV`. -/
def nearVariation (P : Matrix ι ι ℂ) (V H : Matrix ι c ℂ) : Matrix c c ℂ :=
  Hᴴ * P * V + Vᴴ * P * H

omit [Fintype c] in
theorem gramVariation_eq_quad (V H : Matrix ι c ℂ) :
    gramVariation V H = quadVariation 1 V H := by
  simp [gramVariation, quadVariation]

omit [Fintype c] [DecidableEq ι] in
theorem nearVariation_eq_quad (P : Matrix ι ι ℂ) (V H : Matrix ι c ℂ) :
    nearVariation P V H = quadVariation P V H := rfl

/-- Itô drift of `VᴴQV`: first-order drift plus the second-order sum `∑_a σ_aᴴ Q σ_a`. -/
def quadDrift (D0 : ℝ) (Naux : ℕ) (P Q : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) : Matrix c c ℂ :=
  quadVariation Q V (sourceDrift D0 Naux P V) +
    ∑ a, (sourceDiffusion D0 P D a V)ᴴ * Q * sourceDiffusion D0 P D a V

/-- Gram diffusion coefficient `(dM, dB)` along the real noise coordinate `a`. -/
def gramNoise (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : Matrix c c ℂ × Matrix c c ℂ :=
  (gramVariation V (sourceDiffusion D0 P D a V), nearVariation P V (sourceDiffusion D0 P D a V))

/-- The variation along `σ_a` in `w X + conj(w) Y` form. -/
theorem quadVariation_sourceDiffusion (D0 : ℝ) (P Q : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    quadVariation Q V (sourceDiffusion D0 P D a V) =
      sourceWeight D0 a.2 • ((Vᴴ * Q * gramProjection P V D) *
          Matrix.single a.1.2 a.1.1 (1 : ℂ) * (P * V)) +
        star (sourceWeight D0 a.2) • ((Vᴴ * Pᴴ) * Matrix.single a.1.1 a.1.2 (1 : ℂ) *
          ((gramProjection P V D)ᴴ * Q * V)) := by
  rw [sourceDiffusion_eq, quadVariation, sourceNoiseMatrix, sourceUnit, add_comm]
  simp only [conjTranspose_mul, conjTranspose_smul, conjTranspose_single, star_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- **Raw bracket of two quadratic forms** (all `V`, no constraint): with `P' = P + V𝖣Vᴴ`,
`∑_a d(VᴴQV)_ij d(VᴴRV)_kl = (D₀/2)[(VᴴQP'P'ᴴRV)_il (VᴴPᴴPV)_kj
  + (VᴴRP'P'ᴴQV)_kj (VᴴPᴴPV)_il]`. -/
theorem quad_bracket {D0 : ℝ} (hD0 : 0 ≤ D0) (P Q R : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) (i j k l : c) :
    ∑ a, quadVariation Q V (sourceDiffusion D0 P D a V) i j *
        quadVariation R V (sourceDiffusion D0 P D a V) k l =
      ((D0 / 2 : ℝ) : ℂ) *
        ((Vᴴ * Q * gramProjection P V D * ((gramProjection P V D)ᴴ * R * V)) i l *
            (Vᴴ * Pᴴ * (P * V)) k j +
          (Vᴴ * R * gramProjection P V D * ((gramProjection P V D)ᴴ * Q * V)) k j *
            (Vᴴ * Pᴴ * (P * V)) i l) := by
  simp only [quadVariation_sourceDiffusion, Matrix.add_apply, Matrix.smul_apply]
  set P' := gramProjection P V D
  refine (sum_sourceNoise_mul (A := ℂ) hD0
    (fun e : ι × ι => ((Vᴴ * Q * P' * Matrix.single e.2 e.1 (1 : ℂ) * (P * V) :
      Matrix c c ℂ)) i j)
    (fun e : ι × ι => ((Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * (P'ᴴ * Q * V) :
      Matrix c c ℂ)) i j)
    (fun e : ι × ι => ((Vᴴ * R * P' * Matrix.single e.2 e.1 (1 : ℂ) * (P * V) :
      Matrix c c ℂ)) k l)
    (fun e : ι × ι => ((Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * (P'ᴴ * R * V) :
      Matrix c c ℂ)) k l)).trans ?_
  rw [smul_eq_mul, Finset.sum_add_distrib, sum_unit_entry_mul]
  congr 2
  rw [← sum_unit_entry_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

omit [DecidableEq ι] in
/-- Constraint consequences used below: `P'ᴴ = P'`, `P'P' = P'`. -/
theorem gram_frame_reduce {P Q R : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ}
    (hV : TwoProjection P D V) :
    Vᴴ * Q * gramProjection P V D * ((gramProjection P V D)ᴴ * R * V) =
      Vᴴ * Q * gramProjection P V D * R * V := by
  rw [hV.1]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (Vᴴ * Q) (gramProjection P V D) (gramProjection P V D), hV.2.1]

omit [DecidableEq ι] [Fintype c] in
theorem near_frame (P : Matrix ι ι ℂ) {Naux : ℕ} (hP : IsNearProjection P Naux)
    (V : Matrix ι c ℂ) : Vᴴ * Pᴴ * (P * V) = nearGram P V := by
  rw [hP.1, nearGram, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ P P, hP.2.1]

/-- **MM bracket.** Under the two-projection constraint,
`∑_a dM_ij dM_kl = (D₀/2)[B_il (C₀)_kj + (C₀)_il B_kj]`. -/
theorem gram_bracket_MM {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) (i j k l : c) :
    ∑ a, (gramNoise D0 P D a V).1 i j * (gramNoise D0 P D a V).1 k l =
      crossedBracket D0 (nearGram P V) (gramC0 (sourceGram V) (nearGram P V) D)
        (gramC0 (sourceGram V) (nearGram P V) D) i j k l := by
  simp only [gramNoise, gramVariation_eq_quad]
  rw [quad_bracket hD0]
  simp only [gram_frame_reduce hV]
  simp only [near_frame P hP, Matrix.mul_one, gram_sandwich_C0 P V D, crossedBracket]
  ring

/-- **MB bracket.** Under the constraint,
`∑_a dM_ij dB_kl = (D₀/2)[B_il (C₁ᴴ)_kj + (C₁)_il B_kj]`. -/
theorem gram_bracket_MB {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hD : IsSignature D) (hV : TwoProjection P D V) (i j k l : c) :
    ∑ a, (gramNoise D0 P D a V).1 i j * (gramNoise D0 P D a V).2 k l =
      crossedBracket D0 (nearGram P V) (gramC1 (sourceGram V) (nearGram P V) D)ᴴ
        (gramC1 (sourceGram V) (nearGram P V) D) i j k l := by
  simp only [gramNoise, gramVariation_eq_quad, nearVariation_eq_quad]
  rw [quad_bracket hD0]
  simp only [gram_frame_reduce hV]
  simp only [near_frame P hP, Matrix.mul_one, gram_sandwich_C1 P V D hP.2.1,
    gram_sandwich_C1_adjoint P V D hP.2.1 hP.1 hD.1, crossedBracket]
  ring

/-- **BB bracket.** Under the constraint,
`∑_a dB_ij dB_kl = (D₀/2)[B_il (C₂)_kj + (C₂)_il B_kj]`. -/
theorem gram_bracket_BB {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) (i j k l : c) :
    ∑ a, (gramNoise D0 P D a V).2 i j * (gramNoise D0 P D a V).2 k l =
      crossedBracket D0 (nearGram P V) (gramC2 (nearGram P V) D)
        (gramC2 (nearGram P V) D) i j k l := by
  simp only [gramNoise, nearVariation_eq_quad]
  rw [quad_bracket hD0]
  simp only [gram_frame_reduce hV]
  simp only [near_frame P hP, gram_sandwich_C2 P V D hP.2.1, crossedBracket]
  ring

/-- Second-order contraction (all `V`): `∑_a N_aᴴ Q N_a = (D₀/2) Tr(P'ᴴQP') PᴴP`, where
`N_a` is the coefficient of `dAᴴ`; i.e. `dA Q dAᴴ = (D₀/2) Tr(P'ᴴQP') PᴴP dt`. -/
theorem sum_noiseMatrix_conj_mul {D0 : ℝ} (hD0 : 0 ≤ D0) (P Q : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    ∑ a, (sourceNoiseMatrix D0 P D a V)ᴴ * Q * sourceNoiseMatrix D0 P D a V =
      ((D0 / 2 : ℝ) : ℂ) •
        (((gramProjection P V D)ᴴ * Q * gramProjection P V D).trace • (Pᴴ * P)) := by
  set X := (gramProjection P V D)ᴴ * Q * gramProjection P V D
  have h : ∀ a : SourceNoise ι,
      (sourceNoiseMatrix D0 P D a V)ᴴ * Q * sourceNoiseMatrix D0 P D a V =
        (star (sourceWeight D0 a.2) * sourceWeight D0 a.2) •
          (Pᴴ * (Matrix.single a.1.1 a.1.2 (1 : ℂ) * X * Matrix.single a.1.2 a.1.1 (1 : ℂ)) * P) := by
    intro a
    simp only [X, sourceNoiseMatrix, sourceUnit, conjTranspose_mul, conjTranspose_smul,
      conjTranspose_single, star_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc]
    rw [mul_comm (sourceWeight _ _)]
  simp_rw [h]
  refine (sum_sourceNoise_star_mul hD0 (fun e : ι × ι =>
    Pᴴ * (Matrix.single e.1 e.2 (1 : ℂ) * X * Matrix.single e.2 e.1 (1 : ℂ)) * P)).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_unit_conj_mul_unit]
  simp

/-- Closed form of the Itô drift of `VᴴQV` (all `V`). -/
theorem quadDrift_eq {D0 : ℝ} (hD0 : 0 ≤ D0) (Naux : ℕ) (P Q : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    quadDrift D0 Naux P Q D V =
      ((-(D0 * Naux / 4) : ℝ) : ℂ) • (Vᴴ * Pᴴ * Q * V + Vᴴ * Q * P * V) +
        ((D0 / 2 : ℝ) : ℂ) •
          (((gramProjection P V D)ᴴ * Q * gramProjection P V D).trace • (Vᴴ * Pᴴ * P * V)) := by
  have h : ∑ a, (sourceDiffusion D0 P D a V)ᴴ * Q * sourceDiffusion D0 P D a V =
      Vᴴ * (∑ a, (sourceNoiseMatrix D0 P D a V)ᴴ * Q * sourceNoiseMatrix D0 P D a V) * V := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sourceDiffusion_eq, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [quadDrift, h, sum_noiseMatrix_conj_mul hD0, quadVariation, sourceDrift]
  simp only [conjTranspose_smul, conjTranspose_mul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_add]

omit [DecidableEq ι] in
/-- The conductance of the pair `(P, P + V𝖣Vᴴ)` is `g = ½ Tr(𝖣M𝖣M)` (all `V`). -/
theorem currentConductance_gramProjection (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) :
    currentConductance P (gramProjection P V D) = gramScalar D (sourceGram V) := by
  simp only [currentConductance, fullCurrent, gramProjection, add_sub_cancel_left, gramScalar,
    sourceGram]
  have h : V * D * Vᴴ * (V * D * Vᴴ) = V * (D * Vᴴ * V * D * Vᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  ring

omit [DecidableEq ι] in
theorem trace_projection_sandwich {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ}
    (Q : Matrix ι ι ℂ) (hV : TwoProjection P D V) :
    ((gramProjection P V D)ᴴ * Q * gramProjection P V D).trace =
      (gramProjection P V D * Q).trace := by
  rw [hV.1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV.2.1]

/-- **`dA dAᴴ = (D₀ Naux/2) P dt`** under the constraint. -/
theorem sum_dA_mul_dA_conj {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    ∑ a, (sourceNoiseMatrix D0 P D a V)ᴴ * sourceNoiseMatrix D0 P D a V =
      ((D0 * Naux / 2 : ℝ) : ℂ) • P := by
  have h := sum_noiseMatrix_conj_mul hD0 P 1 D V
  simp only [Matrix.mul_one] at h
  rw [h, ← Matrix.mul_one (gramProjection P V D)ᴴ, trace_projection_sandwich 1 hV,
    Matrix.mul_one, hV.2.2, hP.2.2, hP.1, hP.2.1, smul_smul]
  push_cast
  ring_nf

/-- **`dA P dAᴴ = (D₀(Naux - g)/2) P dt`** under the constraint. -/
theorem sum_dA_P_mul_dA_conj {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    ∑ a, (sourceNoiseMatrix D0 P D a V)ᴴ * P * sourceNoiseMatrix D0 P D a V =
      (((D0 / 2 : ℝ) : ℂ) * ((Naux : ℂ) - gramScalar D (sourceGram V))) • P := by
  rw [sum_noiseMatrix_conj_mul hD0, trace_projection_sandwich P hV,
    near_projection_overlap P _ hP.2.1 hV.2.1 hV.2.2, currentConductance_gramProjection,
    hP.2.2, hP.1, hP.2.1, smul_smul]

/-- **Drift of `M` vanishes** (`E_t dM = 0`) under the constraint. -/
theorem gram_drift_M {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    quadDrift D0 Naux P 1 D V = 0 := by
  rw [quadDrift_eq hD0, trace_projection_sandwich 1 hV]
  simp only [Matrix.mul_one]
  have hB : Vᴴ * P * P * V = nearGram P V := by
    rw [Matrix.mul_assoc Vᴴ P P, hP.2.1]; rfl
  rw [hV.2.2, hP.2.2, hP.1, hB, show Vᴴ * P * V = nearGram P V from rfl, smul_add, smul_smul]
  convert gram_norm_drift_cancellation (D0 : ℂ) (Naux : ℂ) (nearGram P V) using 3 <;>
    push_cast <;> ring_nf

/-- **Drift of `B` is `-(D₀/2) g B`** under the constraint. -/
theorem gram_drift_B {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    quadDrift D0 Naux P P D V =
      (-(((D0 / 2 : ℝ) : ℂ) * gramScalar D (sourceGram V))) • nearGram P V := by
  rw [quadDrift_eq hD0, trace_projection_sandwich P hV,
    near_projection_overlap P _ hP.2.1 hV.2.1 hV.2.2, currentConductance_gramProjection, hP.2.2]
  have hB : Vᴴ * Pᴴ * P * V = nearGram P V := by
    rw [Matrix.mul_assoc _ P V, near_frame P hP]
  have hB' : Vᴴ * P * P * V = nearGram P V := by rw [← hB, hP.1]
  simp only [hB', hP.1, smul_add, smul_smul]
  have := gram_near_drift_cancellation (D0 : ℂ) (Naux : ℂ) (gramScalar D (sourceGram V))
    (nearGram P V)
  convert this using 3 <;> push_cast <;> ring_nf

end BlockBand.SourceProcess.Stochastic.SourceAlgebra
