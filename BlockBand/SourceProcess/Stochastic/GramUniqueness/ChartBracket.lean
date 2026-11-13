module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramGeneratorCoord
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealPath
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Gram noise brackets depend only on the Gram pair

For a frame `V` in an ambient space with a Hermitian idempotent `P` (no two-projection
constraint), the complex bilinear brackets `∑_a dG_e dG_e'` of the Gram noise
`gramNoise D0 P D a V` are polynomials in `(VᴴV, VᴴPV)`:
* `raw_expand`: `VᴴQP'P'ᴴRV = B + B𝖣(VᴴRV) + (VᴴQV)𝖣B + (VᴴQV)𝖣M𝖣(VᴴRV)` for
  `Q, R ∈ {1, P}` (`P' = P + V𝖣Vᴴ`, `𝖣ᴴ = 𝖣`);
* **`bracket_transfer`**: two frames with the same Gram pair have the same Gram noise brackets.
  So the brackets at any frame realizing a feasible `G` equal `gramCovEntry G`, the value at a
  constrained realization (`gramNoise_cov_entry`), even if the frame is not constrained.
* `sum_reIm_mul`: real covariances of Hermitian-valued noises in terms of the bilinear brackets
  `Γ_{e e'}` and `Γ_{e, swap e'}` (`realCovEntry`, as in `gramRealCov`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness

variable {c : Type*} [Fintype c] [DecidableEq c]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `1` for `M`-coordinates, `P` for `B`-coordinates. -/
def qOf (r : Fin 2) (P : Matrix ι ι ℂ) : Matrix ι ι ℂ := if r = 0 then 1 else P

omit [DecidableEq c] in
theorem gramEntry_gramNoise (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) (e : Fin 2 × c × c) :
    gramEntry e (gramNoise D0 P D a V) =
      quadVariation (qOf e.1 P) V (sourceDiffusion D0 P D a V) e.2.1 e.2.2 := by
  obtain ⟨r, i, j⟩ := e
  by_cases hr : r = 0
  · simp [gramEntry, gramNoise, qOf, hr, gramVariation_eq_quad]
  · simp [gramEntry, gramNoise, qOf, hr, nearVariation_eq_quad]

omit [DecidableEq c] [DecidableEq ι] in
theorem raw_expand {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P) {D : Matrix c c ℂ}
    (hD : Dᴴ = D) {Q R : Matrix ι ι ℂ} (hQ : Q * P = P) (hR : P * R = P) (V : Matrix ι c ℂ) :
    Vᴴ * Q * gramProjection P V D * ((gramProjection P V D)ᴴ * R * V) =
      Vᴴ * P * V + (Vᴴ * P * V) * D * (Vᴴ * R * V) + (Vᴴ * Q * V) * D * (Vᴴ * P * V) +
        (Vᴴ * Q * V) * D * (Vᴴ * V) * D * (Vᴴ * R * V) := by
  have hP' : (gramProjection P V D)ᴴ = gramProjection P V D := by
    simp only [gramProjection, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      hPH, hD, Matrix.mul_assoc]
  have hQ' : ∀ X : Matrix ι c ℂ, Q * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hQ]
  have hR' : ∀ X : Matrix ι c ℂ, P * (R * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hR]
  have hPP' : ∀ X : Matrix ι c ℂ, P * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hPP]
  rw [hP']
  simp only [gramProjection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hQ', hR', hPP']
  abel

theorem qOf_mul (r : Fin 2) {P : Matrix ι ι ℂ} (hPP : P * P = P) : qOf r P * P = P := by
  unfold qOf; split_ifs
  · exact Matrix.one_mul P
  · exact hPP

theorem mul_qOf (r : Fin 2) {P : Matrix ι ι ℂ} (hPP : P * P = P) : P * qOf r P = P := by
  unfold qOf; split_ifs
  · exact Matrix.mul_one P
  · exact hPP

omit [DecidableEq c] in
/-- **The Gram noise brackets depend only on the Gram pair.** -/
theorem bracket_transfer {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {D0 : ℝ} (hD0 : 0 ≤ D0)
    {D : Matrix c c ℂ} (hD : Dᴴ = D) {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    {P' : Matrix ι' ι' ℂ} (hPH' : P'ᴴ = P') (hPP' : P' * P' = P') {V : Matrix ι c ℂ}
    {V' : Matrix ι' c ℂ} (hG : gramPair P V = gramPair P' V') (e e' : Fin 2 × c × c) :
    ∑ a, gramEntry e (gramNoise D0 P D a V) * gramEntry e' (gramNoise D0 P D a V) =
      ∑ a, gramEntry e (gramNoise D0 P' D a V') * gramEntry e' (gramNoise D0 P' D a V') := by
  have hM : Vᴴ * V = V'ᴴ * V' := congrArg Prod.fst hG
  have hB : Vᴴ * P * V = V'ᴴ * P' * V' := congrArg Prod.snd hG
  have hq : ∀ r : Fin 2, Vᴴ * qOf r P * V = V'ᴴ * qOf r P' * V' := fun r => by
    unfold qOf; split_ifs
    · simpa using hM
    · exact hB
  have hn1 : Vᴴ * Pᴴ * (P * V) = Vᴴ * P * V := by
    rw [hPH, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ P P, hPP]
  have hn2 : V'ᴴ * P'ᴴ * (P' * V') = V'ᴴ * P' * V' := by
    rw [hPH', ← Matrix.mul_assoc, Matrix.mul_assoc V'ᴴ P' P', hPP']
  simp only [gramEntry_gramNoise]
  rw [quad_bracket hD0, quad_bracket hD0, hn1, hn2,
    raw_expand hPH hPP hD (qOf_mul _ hPP) (mul_qOf _ hPP),
    raw_expand hPH hPP hD (qOf_mul _ hPP) (mul_qOf _ hPP),
    raw_expand hPH' hPP' hD (qOf_mul _ hPP') (mul_qOf _ hPP'),
    raw_expand hPH' hPP' hD (qOf_mul _ hPP') (mul_qOf _ hPP'), hM, hB, hq, hq]

omit [Fintype c] [DecidableEq c] in
/-- Real covariances of Hermitian-valued Gram noises. -/
theorem sum_reIm_mul {κ : Type*} [Fintype κ] (N : κ → Matrix c c ℂ × Matrix c c ℂ)
    (hN : ∀ a, (N a).1ᴴ = (N a).1 ∧ (N a).2ᴴ = (N a).2) (q q' : gramRealIdx c) :
    ∑ a, reIm q.2 (gramEntry q.1 (N a)) * reIm q'.2 (gramEntry q'.1 (N a)) =
      realCovEntry q.2 q'.2 (∑ a, gramEntry q.1 (N a) * gramEntry q'.1 (N a))
        (∑ a, gramEntry q.1 (N a) * gramEntry (gramSwap q'.1) (N a)) := by
  simp only [reIm_mul_reIm]
  rw [Finset.sum_add_distrib, ← map_sum, ← map_sum, realCovEntry_eq]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_gramEntry_of_herm (hN a).1 (hN a).2]
  rfl

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
