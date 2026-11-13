module

public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartSigma

/-!
# The `𝒦` noise and its brackets with itself and with the Gram noise

In the ambient realization of the finite source SDE the noise coordinate `a = ((x, y), r)`
drives `dAᴴ = ∑_a w_a P' E_{yx} P dW_a` (`sourceNoiseMatrix`, `w_r = (1, -i)·√D₀/2`), so
`dA = ∑_a \bar w_a Pᴴ E_{xy} P'ᴴ dW_a`, and the complex source SDE `d𝒦 = -2iη Vᴴ dA V`
(probe block) has the coefficient
`kNoise D0 η P D a V = -2iη \bar w_a · Vᴴ Pᴴ E_{xy} (P'ᴴ V)` (`P' = gramProjection P V D`).

Raw brackets, for **every** frame `V` (no constraint), by the Itô table
`∑_r \bar w_r² = 0`, `∑_r \bar w_r w_r = D₀/2`:
* `sum_kNoise_mul`: `∑_a dK_ij dK_kl = 0`;
* `sum_kNoise_mul_star`: `∑_a dK_ij d\bar K_kl = 2η²D₀ (VᴴPᴴPV)_ik (VᴴP'P'ᴴV)_lj`;
* `sum_kNoise_mul_gram`: `∑_a dK_ij d(VᴴQV)_kl = -iηD₀ (VᴴPᴴPV)_il (VᴴQP'P'ᴴV)_kj`,
  `Q = 1` for `M`, `Q = P` for `B`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart

variable {c : Type*} [Fintype c] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `𝒦` noise coefficient** `-2iη \bar w_a Vᴴ Pᴴ E_{xy} P'ᴴ V`. -/
def kNoise (D0 η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : Matrix c c ℂ :=
  (((-2 * η : ℝ) : ℂ) * Complex.I * star (sourceWeight D0 a.2)) •
    (Vᴴ * Pᴴ * Matrix.single a.1.1 a.1.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * V))

/-- The `e`-part of the `𝒦` noise. -/
def kY (η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) (i j : c) (e : ι × ι) : ℂ :=
  ((-2 * η : ℝ) : ℂ) * Complex.I *
    (Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * V)) i j

theorem kNoise_apply (D0 η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) (i j : c) :
    kNoise D0 η P D a V i j = star (sourceWeight D0 a.2) * kY η P D V i j a.1 := by
  simp only [kNoise, kY, Matrix.smul_apply, smul_eq_mul]; ring

theorem sum_kNoise_mul (D0 η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ)
    (i j k l : c) : ∑ a, kNoise D0 η P D a V i j * kNoise D0 η P D a V k l = 0 := by
  simp only [kNoise_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun e _ => ?_
  have h : ∀ r : Fin 2, star (sourceWeight D0 r) * kY η P D V i j e *
      (star (sourceWeight D0 r) * kY η P D V k l e) =
        (star (sourceWeight D0 r) * star (sourceWeight D0 r)) *
          (kY η P D V i j e * kY η P D V k l e) := fun r => by ring
  simp only [h]
  rw [← Finset.sum_mul, sum_star_weight_mul_self, zero_mul]

theorem star_unit_entry {κ κ' : Type*} (A : Matrix κ ι ℂ) (B : Matrix ι κ' ℂ) (p q : ι)
    (i : κ) (j : κ') : star ((A * Matrix.single p q (1 : ℂ) * B) i j) =
      (Bᴴ * Matrix.single q p (1 : ℂ) * Aᴴ) j i := by
  rw [unit_entry, unit_entry, star_mul', conjTranspose_apply, conjTranspose_apply, mul_comm]

theorem sum_kNoise_mul_star {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) (i j k l : c) :
    ∑ a, kNoise D0 η P D a V i j * star (kNoise D0 η P D a V k l) =
      ((2 * η ^ 2 * D0 : ℝ) : ℂ) * (Vᴴ * Pᴴ * (P * V)) i k *
        (Vᴴ * gramProjection P V D * ((gramProjection P V D)ᴴ * V)) l j := by
  simp only [kNoise_apply, star_mul', star_star]
  rw [Fintype.sum_prod_type]
  have h : ∀ (e : ι × ι) (r : Fin 2), star (sourceWeight D0 r) * kY η P D V i j e *
      (sourceWeight D0 r * star (kY η P D V k l e)) =
        (star (sourceWeight D0 r) * sourceWeight D0 r) *
          (kY η P D V i j e * star (kY η P D V k l e)) := fun e r => by ring
  simp only [h, ← Finset.sum_mul, sum_star_weight_mul hD0]
  rw [← Finset.mul_sum]
  have h2 : ∀ e : ι × ι, kY η P D V i j e * star (kY η P D V k l e) = ((4 * η ^ 2 : ℝ) : ℂ) *
      ((Vᴴ * gramProjection P V D * Matrix.single e.2 e.1 (1 : ℂ) * (P * V)) l k *
        (Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * V)) i j) := by
    intro e
    simp only [kY, star_mul', star_unit_entry]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I, Matrix.mul_assoc]
    push_cast; ring_nf; simp only [Complex.I_sq]; ring
  simp only [h2, ← Finset.mul_sum, sum_unit_entry_mul]
  push_cast; ring

theorem sum_kNoise_mul_gram {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (V : Matrix ι c ℂ) (Q : Matrix ι ι ℂ) (i j k l : c) :
    ∑ a, kNoise D0 η P D a V i j * quadVariation Q V (sourceDiffusion D0 P D a V) k l =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * (Vᴴ * Pᴴ * (P * V)) i l *
        (Vᴴ * Q * gramProjection P V D * ((gramProjection P V D)ᴴ * V)) k j := by
  simp only [quadVariation_sourceDiffusion, kNoise_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Fintype.sum_prod_type]
  have h : ∀ (e : ι × ι) (r : Fin 2), star (sourceWeight D0 r) * kY η P D V i j e *
      (sourceWeight D0 r * (Vᴴ * Q * gramProjection P V D * Matrix.single e.2 e.1 (1 : ℂ) *
          (P * V)) k l + star (sourceWeight D0 r) * (Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) *
          ((gramProjection P V D)ᴴ * Q * V)) k l) =
        (star (sourceWeight D0 r) * sourceWeight D0 r) * (kY η P D V i j e *
          (Vᴴ * Q * gramProjection P V D * Matrix.single e.2 e.1 (1 : ℂ) * (P * V)) k l) +
        (star (sourceWeight D0 r) * star (sourceWeight D0 r)) * (kY η P D V i j e *
          (Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * Q * V)) k l) :=
    fun e r => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, sum_star_weight_mul hD0,
    sum_star_weight_mul_self, zero_mul, add_zero]
  rw [← Finset.mul_sum]
  simp only [kY]
  have h2 : ∀ e : ι × ι, ((-2 * η : ℝ) : ℂ) * Complex.I *
      (Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * V)) i j *
      (Vᴴ * Q * gramProjection P V D * Matrix.single e.2 e.1 (1 : ℂ) * (P * V)) k l =
        ((-2 * η : ℝ) : ℂ) * Complex.I *
          ((Vᴴ * Q * gramProjection P V D * Matrix.single e.2 e.1 (1 : ℂ) * (P * V)) k l *
            (Vᴴ * Pᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * V)) i j) :=
    fun e => by ring
  simp only [h2, ← Finset.mul_sum, sum_unit_entry_mul]
  push_cast; ring

end BlockBand.SourceProcess.ComplexUnique
