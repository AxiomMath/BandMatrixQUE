module

public import BlockBand.SourceProcess.ClosedFeas.Algebra
public import BlockBand.SourceProcess.ClosedReduce.Start

/-!
# Far-port algebra of the time-`s` closing data

For a unitary two-port `𝕊` with far reflection `R = 𝕊_ff`, far transmission `T = 1 - RᴴR`,
`A_w = 1_{[0,h²]}(T)`, `G = g(T)` (`g = pairWeight h`), the embedded data are
`A = F A_w Fᴴ`, `Π = F G Rᴴ Fᴴ` (`F = farInj`). Proved:
* `pi_mul_eq`: `Π𝕊 = F G Fᴴ(1 - 𝕊ᴴP𝕊)`; hence `pi_mul_eigen`: `Π𝕊V = 0` for every frame with
  `AV = 0` and `𝕊ᴴP𝕊V = PV + VΛ`;
* `trace_cfc`: `Tr f(T) = Σ_i f(t_i)` over the eigenvalues of `T`, used for the retained
  transmission mass `Σ_i φ(t_i)`, `φ(t) = t·1_{t>h²}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.ClosedReduce

variable {W : ℕ}

/-- The retained transmission weight `φ(t) = t·1_{t>h²}`. -/
def retW (h t : ℝ) : ℝ := if h ^ 2 < t then t else 0

/-- **Trace of the functional calculus**: `Tr f(T) = Σ_i f(t_i)`. -/
theorem trace_cfc {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}
    (hT : T.IsHermitian) (f : ℝ → ℝ) : (cfc f T).trace = ∑ i, ((f (hT.eigenvalues i) : ℝ) : ℂ) := by
  rw [hT.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]
  rw [show (star (hT.eigenvectorUnitary : Matrix n n ℂ)) * (hT.eigenvectorUnitary : Matrix n n ℂ)
    = 1 from Unitary.coe_star_mul_self _, Matrix.one_mul, trace_diagonal]
  rfl

theorem farInj_conj_mul_farInj (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (farInj W)ᴴ * M * farInj W = portBlock M 1 1 := by
  ext a c
  simp only [mul_apply, conjTranspose_apply, farInj, of_apply, portBlock]
  rw [Finset.sum_eq_single (1, c) (fun y _ hy => by simp [hy]) (by simp)]
  rw [Finset.sum_eq_single (1, a) (fun y _ hy => by simp [hy]) (by simp)]
  simp

variable {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {h : ℝ}

/-- `T = 1 - RᴴR` for `R = 𝕊_ff`. -/
abbrev fT (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  1 - (portBlock S 1 1)ᴴ * portBlock S 1 1

theorem fT_isHermitian : (fT S).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)

theorem one_sub_fT : 1 - fT S = (portBlock S 1 1)ᴴ * portBlock S 1 1 := sub_sub_cancel _ _

theorem conjT_portBlock : (farInj W)ᴴ * Sᴴ * farInj W = (portBlock S 1 1)ᴴ := by
  rw [← farInj_conj_mul_farInj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

/-- The far compression of `𝕊ᴴP𝕊` is `T`. -/
theorem far_outProj (hS : Sᴴ * S = 1) :
    (farInj W)ᴴ * (Sᴴ * nearPortProj W * S) * farInj W = fT S := by
  have hP : nearPortProj W = 1 - farInj W * (farInj W)ᴴ := by rw [← one_sub_nearPortProj]; abel
  have e : (farInj W)ᴴ * (Sᴴ * (1 - farInj W * (farInj W)ᴴ) * S) * farInj W =
      (farInj W)ᴴ * (Sᴴ * S) * farInj W -
        ((farInj W)ᴴ * Sᴴ * farInj W) * ((farInj W)ᴴ * S * farInj W) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hP, e, hS, Matrix.mul_one, farInj_conj_mul_self, conjT_portBlock, farInj_conj_mul_farInj]

/-- **`Π𝕊 = F G Fᴴ (1 - 𝕊ᴴP𝕊)`**. -/
theorem pi_mul_eq (hS : Sᴴ * S = 1) (G : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed (G * (portBlock S 1 1)ᴴ) * S =
      farInj W * G * (farInj W)ᴴ * (1 - Sᴴ * nearPortProj W * S) := by
  have hQ : 1 - Sᴴ * nearPortProj W * S = Sᴴ * (farInj W * (farInj W)ᴴ) * S := by
    rw [← one_sub_nearPortProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS]
  rw [hQ, farEmbed_eq_farInj, ← conjT_portBlock]
  simp only [Matrix.mul_assoc]

/-- `Π𝕊F = F G (1 - T)`. -/
theorem pi_mul_far (G : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed (G * (portBlock S 1 1)ᴴ) * S * farInj W = farInj W * (G * (1 - fT S)) := by
  rw [one_sub_fT, farEmbed_eq_farInj, ← farInj_conj_mul_farInj S]
  simp only [Matrix.mul_assoc]

/-- **The pairing kills the retained frame**: `AV = 0`, `𝕊ᴴP𝕊V = PV + VΛ` give `Π𝕊V = 0`. -/
theorem pi_mul_eigen {κ : Type*} [Fintype κ] [DecidableEq κ] (hS : Sᴴ * S = 1) {V : Matrix (Fin 2 × Fin W) κ ℂ}
    {L : Matrix κ κ ℂ} (hAV : farEmbed (cfc (omitIndicator h) (fT S)) * V = 0)
    (hJ : Sᴴ * nearPortProj W * S * V = nearPortProj W * V + V * L) :
    farEmbed (cfc (pairWeight h) (fT S) * (portBlock S 1 1)ᴴ) * S * V = 0 := by
  have hG : cfc (pairWeight h) (fT S) = cfc (pairWeight h) (fT S) * cfc (omitIndicator h) (fT S) := by
    rw [← cfc_mul _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
    congr 1; funext t; unfold pairWeight omitIndicator; split_ifs <;> simp
  have hFA : cfc (omitIndicator h) (fT S) * ((farInj W)ᴴ * V) = 0 := by
    have := congrArg (fun X => (farInj W)ᴴ * X) hAV
    simp only [farEmbed_eq_farInj, Matrix.mul_zero] at this
    rw [← this]
    simp only [← Matrix.mul_assoc, farInj_conj_mul_self, Matrix.one_mul]
  have hQ : (farInj W)ᴴ * ((1 - Sᴴ * nearPortProj W * S) * V) = (farInj W)ᴴ * V * (1 - L) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hJ, Matrix.mul_sub, Matrix.mul_add,
      ← Matrix.mul_assoc _ (nearPortProj W), farInj_conj_mul_nearPortProj, Matrix.zero_mul,
      zero_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  calc farEmbed (cfc (pairWeight h) (fT S) * (portBlock S 1 1)ᴴ) * S * V
      = farInj W * cfc (pairWeight h) (fT S) *
          ((farInj W)ᴴ * ((1 - Sᴴ * nearPortProj W * S) * V)) := by
        rw [pi_mul_eq hS]; simp only [Matrix.mul_assoc]
    _ = farInj W * cfc (pairWeight h) (fT S) *
          (cfc (omitIndicator h) (fT S) * ((farInj W)ᴴ * V)) * (1 - L) := by
        rw [hQ]; conv_lhs => rw [hG]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hFA]; simp

end BlockBand.SourceProcess.ClosedFeas
