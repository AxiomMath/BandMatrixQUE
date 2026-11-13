module

public import BlockBand.SourceProcess.FullSourceStops.WordValue

/-!
# Separators of norm at most one, and one-letter current words

Right multiplication by a separator does not increase Hilbert–Schmidt norms, and the trace of the
current against any separator is bounded by the conductance.

* `hsNorm_mul_sepMat_le`: right multiplication by any of the six separators `I, P, P𝕊, 𝕊ᴴP, P𝕊P,
  P𝕊ᴴP` does not increase the Hilbert–Schmidt norm (`hsNorm_mul_ordSep_le` covers `I, P`).
* `norm_trace_current_sepMat_le`: `|Tr(JB)| ≤ ½‖J‖₂² = g` for every separator `B`. For `B = P𝕊`
  and `B = 𝕊ᴴP` the trace is `0`; for `B = P𝕊P` (and `P𝕊ᴴP`) we use `PJP = -GᴴG`,
  `G = (1-P)𝕊P`, so `Tr(J·P𝕊P) = -Tr(GᴴG·P𝕊)` and `‖G‖₂² = -Tr JP = ½Tr J²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge

variable {W : ℕ}

/-- The six separator matrices at a given scattering matrix `𝕊`. -/
def sepMat (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | .id => 1
  | .proj => nearProjection W
  | .projS => nearProjection W * S
  | .sStarProj => Sᴴ * nearProjection W
  | .projSProj => nearProjection W * S * nearProjection W
  | .projSStarProj => nearProjection W * Sᴴ * nearProjection W

theorem separatorMatrix_eq_sepMat (b E : ℝ) (j : ℕ) (ω : GrowthPath W) (σ : Separator) :
    separatorMatrix b E W j ω σ = sepMat (scatteringMatrix b E W j ω) σ := by
  cases σ <;> rfl

theorem hsNorm_mul_unitary {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (T : Matrix m n ℂ) (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) : hsNorm (T * U) = hsNorm T := by
  have h : ((hsNorm (T * U) ^ 2 : ℝ) : ℂ) = ((hsNorm T ^ 2 : ℝ) : ℂ) := by
    rw [← trace_conjTranspose_mul_self, ← trace_conjTranspose_mul_self, conjTranspose_mul,
      show Uᴴ * Tᴴ * (T * U) = Uᴴ * (Tᴴ * T * U) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm Uᴴ, Matrix.mul_assoc (Tᴴ * T) U Uᴴ, hU, Matrix.mul_one]
  exact (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp (by exact_mod_cast h)

variable (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hS : S * Sᴴ = 1)
include hS

theorem conjTranspose_unitary : Sᴴ * Sᴴᴴ = 1 := by
  rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hS

theorem hsNorm_mul_sepMat_le {m : Type*} [Fintype m] (σ : Separator)
    (T : Matrix m (Fin 2 × Fin W) ℂ) : hsNorm (T * sepMat S σ) ≤ hsNorm T := by
  have hP := fun (T : Matrix m (Fin 2 × Fin W) ℂ) => hsNorm_mul_nearProjection_le T
  have hU := fun (T : Matrix m (Fin 2 × Fin W) ℂ) => hsNorm_mul_unitary T S hS
  have hU' := fun (T : Matrix m (Fin 2 × Fin W) ℂ) =>
    hsNorm_mul_unitary T Sᴴ (conjTranspose_unitary S hS)
  cases σ
  · simp [sepMat]
  · exact hP T
  · rw [sepMat, ← Matrix.mul_assoc, hU]; exact hP T
  · rw [sepMat, ← Matrix.mul_assoc]; exact (hP _).trans (hU' T).le
  · rw [sepMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact (hP _).trans ((hU _).le.trans (hP T))
  · rw [sepMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact (hP _).trans ((hU' _).le.trans (hP T))

omit hS in
private theorem trace_PJP (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (nearProjection W * J * nearProjection W).trace = (J * nearProjection W).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, nearProjection_mul_self, Matrix.trace_mul_comm]

/-- `PJP = -GᴴG` with `G = (1-P)𝕊P`. -/
private theorem PJP_eq :
    let P := nearProjection W
    let G := (1 - P) * S * P
    P * (Sᴴ * P * S - P) * P = -(Gᴴ * G) := by
  intro P G
  have hSS : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  have hPP : P * P = P := nearProjection_mul_self
  have hPh : Pᴴ = P := nearProjection_conjTranspose
  have hSS' : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Sᴴ * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hSS, Matrix.one_mul]
  have hPP' : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, P * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hPP]
  simp only [G, conjTranspose_mul, hPh, conjTranspose_sub, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hSS', hPP', hPP]
  abel

/-- `|Tr(J·P𝕊P)|`-type bound: `|Tr(PJP·B)| ≤ ½‖J‖₂²` whenever `‖GB‖₂ ≤ ‖G‖₂`. -/
private theorem norm_trace_PJP_mul_le (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hB : ∀ T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, hsNorm (T * B) ≤ hsNorm T) :
    let P := nearProjection W
    ‖(P * (Sᴴ * P * S - P) * P * B).trace‖ ≤ hsNorm (Sᴴ * P * S - P) ^ 2 / 2 := by
  intro P
  set G := (1 - P) * S * P
  have hPh : Pᴴ = P := nearProjection_conjTranspose
  have hPP : P * P = P := nearProjection_mul_self
  rw [PJP_eq S hS, Matrix.neg_mul, Matrix.trace_neg, norm_neg]
  refine (norm_trace_gram_mul_le G B (hB G)).trans (le_of_eq ?_)
  have h1 := trace_conjTranspose_mul_self G
  rw [← neg_neg (Gᴴ * G), ← PJP_eq S hS, Matrix.trace_neg, trace_PJP,
    current_trace_mul_proj S P hS hPP, ← current_hsNorm_sq S P hPh] at h1
  have h2 : ((hsNorm G ^ 2 : ℝ) : ℂ) = ((hsNorm (Sᴴ * P * S - P) ^ 2 / 2 : ℝ) : ℂ) := by
    rw [← h1]; push_cast; ring
  exact_mod_cast h2

/-- **One-letter current words**: `|Tr(JB)| ≤ ½‖J‖₂²` for every separator `B`. -/
theorem norm_trace_current_sepMat_le (σ : Separator) :
    ‖((Sᴴ * nearProjection W * S - nearProjection W) * sepMat S σ).trace‖ ≤
      hsNorm (Sᴴ * nearProjection W * S - nearProjection W) ^ 2 / 2 := by
  set P := nearProjection W with hPdef
  have hPh : Pᴴ = P := nearProjection_conjTranspose
  have hPP : P * P = P := nearProjection_mul_self
  have h0 : (0 : ℝ) ≤ hsNorm (Sᴴ * P * S - P) ^ 2 / 2 := by positivity
  have hPJP : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      ((Sᴴ * P * S - P) * (P * X * P)).trace = (P * (Sᴴ * P * S - P) * P * (P * X)).trace := by
    intro X
    have e : P * (Sᴴ * P * S - P) * P * (P * X) = P * ((Sᴴ * P * S - P) * (P * X)) := by
      rw [Matrix.mul_assoc _ P, ← Matrix.mul_assoc P P X, hPP, Matrix.mul_assoc]
    rw [e, ← Matrix.mul_assoc (Sᴴ * P * S - P) (P * X) P,
      Matrix.trace_mul_comm ((Sᴴ * P * S - P) * (P * X)) P]
  cases σ
  · simpa [sepMat] using current_trace_mul_le S P hS hPh hPP 1 (Or.inl rfl)
  · exact current_trace_mul_le S P hS hPh hPP P (Or.inr rfl)
  · have e : ((Sᴴ * P * S - P) * (P * S)).trace = 0 := by
      have e1 : (Sᴴ * P * S * (P * S)).trace = (P * (P * S)).trace := by
        rw [show Sᴴ * P * S * (P * S) = Sᴴ * (P * S * P * S) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm Sᴴ,
          show P * S * P * S * Sᴴ = P * S * P * (S * Sᴴ) by simp only [Matrix.mul_assoc], hS,
          Matrix.mul_one, Matrix.trace_mul_comm (P * S) P]
      rw [Matrix.sub_mul, Matrix.trace_sub, e1, sub_self]
    simp only [sepMat, ← hPdef, e, norm_zero]; exact h0
  · have e : ((Sᴴ * P * S - P) * (Sᴴ * P)).trace = 0 := by
      have e1 : (Sᴴ * P * S * (Sᴴ * P)).trace = (Sᴴ * P * P).trace := by
        rw [show Sᴴ * P * S * (Sᴴ * P) = Sᴴ * P * (S * Sᴴ) * P by simp only [Matrix.mul_assoc], hS,
          Matrix.mul_one]
      rw [Matrix.sub_mul, Matrix.trace_sub, e1, Matrix.trace_mul_comm P (Sᴴ * P), sub_self]
    simp only [sepMat, ← hPdef, e, norm_zero]; exact h0
  · simp only [sepMat, ← hPdef]
    rw [hPJP S]
    refine norm_trace_PJP_mul_le S hS (P * S) fun T => ?_
    rw [← Matrix.mul_assoc, hsNorm_mul_unitary _ S hS]; exact hsNorm_mul_nearProjection_le T
  · simp only [sepMat, ← hPdef]
    rw [hPJP Sᴴ]
    refine norm_trace_PJP_mul_le S hS (P * Sᴴ) fun T => ?_
    rw [← Matrix.mul_assoc, hsNorm_mul_unitary _ Sᴴ (conjTranspose_unitary S hS)]
    exact hsNorm_mul_nearProjection_le T

end BlockBand.SourceProcess.ContractingWords
