module

public import BlockBand.SourceProcess.ComplexUnique.Noise

/-!
# The raw `𝒦` brackets at any realization of a feasible Gram state

For a Hermitian idempotent `P` and a frame `V` (no two-projection constraint) with
`gramPair P V = G` and `G` feasible:
* `raw_B`: `VᴴPᴴPV = B`;
* `raw_C0`: `VᴴP'P'ᴴV = C₀ = B + M𝖣M`;
* `raw_C1`: `VᴴPP'P'ᴴV = C₁ᴴ = B + B𝖣M`.
The raw forms are polynomials in `(M, B)` (`GramChart.raw_expand`), so they can be evaluated at a
constrained realization (`exists_realization_of_feasible`), where `P'` is a projection.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart

variable {c : Type*} [Fintype c] {ι : Type*} [Fintype ι] {D : Matrix c c ℂ}
  {P : Matrix ι ι ℂ} {V : Matrix ι c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}

omit [Fintype c] in
theorem raw_B (hPH : Pᴴ = P) (hPP : P * P = P) (hV : gramPair P V = G) :
    Vᴴ * Pᴴ * (P * V) = G.2 := by
  rw [← hV, hPH, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ P P, hPP]; rfl

variable [DecidableEq ι]

theorem raw_poly (hD : Dᴴ = D) (hPH : Pᴴ = P) (hPP : P * P = P) {Q : Matrix ι ι ℂ}
    (hQ : Q * P = P) (hV : gramPair P V = G) {X : Matrix c c ℂ} (hQV : Vᴴ * Q * V = X) :
    Vᴴ * Q * gramProjection P V D * ((gramProjection P V D)ᴴ * V) =
      G.2 + G.2 * D * G.1 + X * D * G.2 + X * D * G.1 * D * G.1 := by
  have h := raw_expand hPH hPP hD hQ (mul_one P) V
  simp only [Matrix.mul_one] at h
  rw [h]
  have h1 : Vᴴ * V = G.1 := congrArg Prod.fst hV
  have h2 : Vᴴ * P * V = G.2 := congrArg Prod.snd hV
  rw [h1, h2, hQV]

theorem raw_C0 (hD : Dᴴ = D) (hPH : Pᴴ = P) (hPP : P * P = P) (hG : GramFeasible D G)
    (hV : gramPair P V = G) :
    Vᴴ * gramProjection P V D * ((gramProjection P V D)ᴴ * V) = gramC0 G.1 G.2 D := by
  obtain ⟨n, N, P', V', hP', hV', hGe⟩ := exists_realization_of_feasible hG
  have e1 := raw_poly hD hPH hPP (Q := 1) (one_mul P) hV (X := G.1) (by
    rw [Matrix.mul_one]; exact congrArg Prod.fst hV)
  have e2 := raw_poly hD hP'.1 hP'.2.1 (Q := 1) (one_mul P') hGe (X := G.1) (by
    rw [Matrix.mul_one]; exact congrArg Prod.fst hGe)
  simp only [Matrix.mul_one] at e1 e2
  have e3 := gram_frame_reduce (Q := 1) (R := 1) hV'
  simp only [Matrix.mul_one] at e3
  rw [e1, ← e2, e3, gram_sandwich_C0, ← hGe]; rfl

theorem raw_C1 (hD : Dᴴ = D) (hPH : Pᴴ = P) (hPP : P * P = P) (hG : GramFeasible D G)
    (hV : gramPair P V = G) :
    Vᴴ * P * gramProjection P V D * ((gramProjection P V D)ᴴ * V) = (gramC1 G.1 G.2 D)ᴴ := by
  obtain ⟨n, N, P', V', hP', hV', hGe⟩ := exists_realization_of_feasible hG
  have e1 := raw_poly hD hPH hPP (Q := P) hPP hV (congrArg Prod.snd hV)
  have e2 := raw_poly hD hP'.1 hP'.2.1 (Q := P') hP'.2.1 hGe (congrArg Prod.snd hGe)
  have e3 := gram_frame_reduce (Q := P') (R := 1) hV'
  simp only [Matrix.mul_one] at e3
  rw [e1, ← e2, e3, gram_sandwich_C1_adjoint P' V' D hP'.2.1 hP'.1 hD, ← hGe]; rfl

end BlockBand.SourceProcess.ComplexUnique
