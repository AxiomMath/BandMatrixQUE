module

public import BlockBand.SourceProcess.ClosedFeas.Trace

/-!
# The squared retained current has trace `2 Σ t_i 1_{t_i > h²}`

Notation as for `pi_mul_eq`: `fA h 𝕊 = F A_w Fᴴ`, `fPi h 𝕊 = F G Rᴴ Fᴴ`. Proved:
* the closing-data identities (`fA_*`, `fPi_*`): `A` a Hermitian projection, `AΠ = Π`,
  `ΠΠᴴ = A` (`h² < 1`), `PA = AP = ΠP = 0`;
* `trace_conj_sub_sq`: `Tr((𝕊ᴴE𝕊 - E')²) = Tr E + Tr E' - 2 Tr(𝕊ᴴE𝕊E')` for projections;
* **`trace_split_sq`**: `Tr(X²) = 2 Σ_i retW h t_i` for `X = splitCurrent 𝕊 P A Π`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.ClosedReduce

variable {W : ℕ} {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {h : ℝ}

/-- The embedded omitted far inputs `A = F A_w Fᴴ`. -/
abbrev fA (h : ℝ) (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  farEmbed (cfc (omitIndicator h) (fT S))

/-- The embedded pairing `Π = F G Rᴴ Fᴴ`. -/
abbrev fPi (h : ℝ) (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  farEmbed (cfc (pairWeight h) (fT S) * (portBlock S 1 1)ᴴ)

theorem cfc_mul' (f g : ℝ → ℝ) (T : Matrix (Fin W) (Fin W) ℂ) :
    cfc f T * cfc g T = cfc (fun t => f t * g t) T :=
  (cfc_mul _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)).symm

theorem fA_conj : (fA h S)ᴴ = fA h S := by rw [farEmbed_conjTranspose, cfc_conjTranspose]

theorem fA_mul_self : fA h S * fA h S = fA h S := by
  rw [farEmbed_mul, cfc_mul']; congr 2; funext t; unfold omitIndicator; split_ifs <;> simp

theorem fA_mul_fPi : fA h S * fPi h S = fPi h S := by
  rw [farEmbed_mul, ← Matrix.mul_assoc, cfc_mul']
  congr 3; funext t; unfold omitIndicator pairWeight; split_ifs <;> simp

theorem fPi_mul_conj (hh : h ^ 2 < 1) : fPi h S * (fPi h S)ᴴ = fA h S := by
  rw [farEmbed_conjTranspose, farEmbed_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    cfc_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc _ (portBlock S 1 1), ← one_sub_fT,
    show (1 - fT S) = cfc (fun x : ℝ => 1 - x) (fT S) by
      rw [cfc_sub _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
        cfc_const_one ℝ _ fT_isHermitian.isSelfAdjoint, cfc_id' ℝ _ fT_isHermitian.isSelfAdjoint],
    cfc_mul', cfc_mul']
  congr 2; funext t; exact pairWeight_mul h hh t

theorem nearPortProj_mul_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) :
    nearPortProj W * farEmbed X = 0 := by
  have := congrArg conjTranspose (farEmbed_mul_nearPortProj Xᴴ)
  rwa [conjTranspose_mul, farEmbed_conjTranspose, conjTranspose_conjTranspose,
    nearPortProj_conjTranspose, conjTranspose_zero] at this

/-- `Tr((𝕊ᴴE𝕊 - E')²) = Tr E + Tr E' - 2 Tr(𝕊ᴴE𝕊E')` for idempotents `E, E'`, `𝕊𝕊ᴴ = 1`. -/
theorem trace_conj_sub_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {S E E' : Matrix ι ι ℂ}
    (hS : S * Sᴴ = 1) (hE : E * E = E) (hE' : E' * E' = E') :
    ((Sᴴ * E * S - E') * (Sᴴ * E * S - E')).trace =
      E.trace + E'.trace - 2 * (Sᴴ * E * S * E').trace := by
  have h1 : Sᴴ * E * S * (Sᴴ * E * S) = Sᴴ * E * S := by
    calc Sᴴ * E * S * (Sᴴ * E * S) = Sᴴ * E * (S * Sᴴ) * E * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS, Matrix.mul_one, Matrix.mul_assoc Sᴴ E E, hE]
  have h2 : (Sᴴ * E * S).trace = E.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hS, Matrix.one_mul]
  have h3 : (E' * (Sᴴ * E * S)).trace = (Sᴴ * E * S * E').trace := Matrix.trace_mul_comm _ _
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, hE', trace_sub, trace_sub, trace_sub,
    h2, h3]
  ring

theorem trace_mul_farEmbed (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (X : Matrix (Fin W) (Fin W) ℂ) :
    (M * farEmbed X).trace = ((farInj W)ᴴ * M * farInj W * X).trace := by
  rw [farEmbed_eq_farInj, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

theorem trace_mul_nearPortProj (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (M * nearPortProj W).trace = M.trace - ((farInj W)ᴴ * M * farInj W).trace := by
  have hP : nearPortProj W = 1 - farInj W * (farInj W)ᴴ := by rw [← one_sub_nearPortProj]; abel
  rw [hP, Matrix.mul_sub, Matrix.mul_one, trace_sub, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]

/-- **The squared retained current**: `Tr X² = 2 Σ_i t_i 1_{t_i > h²}`. -/
theorem trace_split_sq (hS : Sᴴ * S = 1) (hS' : S * Sᴴ = 1) (hh : h ^ 2 < 1) :
    (splitCurrent S (nearPortProj W) (fA h S) (fPi h S) *
        splitCurrent S (nearPortProj W) (fA h S) (fPi h S)).trace =
      2 * ∑ i, ((retW h (fT_isHermitian (S := S).eigenvalues i) : ℝ) : ℂ) := by
  have hPA : nearPortProj W * fA h S = 0 := nearPortProj_mul_farEmbed _
  have hAP : fA h S * nearPortProj W = 0 := farEmbed_mul_nearPortProj _
  have hPiP : fPi h S * nearPortProj W = 0 := farEmbed_mul_nearPortProj _
  have hPPi : nearPortProj W * (fPi h S)ᴴ = 0 := by
    rw [farEmbed_conjTranspose]; exact nearPortProj_mul_farEmbed _
  have hBP : (fPi h S)ᴴ * fPi h S * nearPortProj W = 0 := by
    rw [Matrix.mul_assoc, hPiP, Matrix.mul_zero]
  have hPB : nearPortProj W * ((fPi h S)ᴴ * fPi h S) = 0 := by
    rw [← Matrix.mul_assoc, hPPi, Matrix.zero_mul]
  have hPiA : (fPi h S)ᴴ * fA h S = (fPi h S)ᴴ := by
    rw [← fA_conj, ← conjTranspose_mul, fA_mul_fPi]
  have hBB : (fPi h S)ᴴ * fPi h S * ((fPi h S)ᴴ * fPi h S) = (fPi h S)ᴴ * fPi h S := by
    calc (fPi h S)ᴴ * fPi h S * ((fPi h S)ᴴ * fPi h S)
        = (fPi h S)ᴴ * (fPi h S * (fPi h S)ᴴ) * fPi h S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [fPi_mul_conj hh, hPiA]
  have hE : (nearPortProj W + (fPi h S)ᴴ * fPi h S) * (nearPortProj W + (fPi h S)ᴴ * fPi h S) =
      nearPortProj W + (fPi h S)ᴴ * fPi h S := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, nearPortProj_mul_self, hPB, hBP, hBB]
    abel
  have hE' : (nearPortProj W + fA h S) * (nearPortProj W + fA h S) = nearPortProj W + fA h S := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, nearPortProj_mul_self, hPA, hAP,
      fA_mul_self]
    abel
  have htrB : ((fPi h S)ᴴ * fPi h S).trace = (fA h S).trace := by
    rw [Matrix.trace_mul_comm, fPi_mul_conj hh]
  have hK : (farInj W)ᴴ * (Sᴴ * ((fPi h S)ᴴ * fPi h S) * S) * farInj W =
      (cfc (pairWeight h) (fT S) * (1 - fT S))ᴴ * (cfc (pairWeight h) (fT S) * (1 - fT S)) := by
    calc (farInj W)ᴴ * (Sᴴ * ((fPi h S)ᴴ * fPi h S) * S) * farInj W
        = (fPi h S * S * farInj W)ᴴ * (fPi h S * S * farInj W) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (farInj W * (cfc (pairWeight h) (fT S) * (1 - fT S)))ᴴ *
          (farInj W * (cfc (pairWeight h) (fT S) * (1 - fT S))) := by rw [pi_mul_far]
      _ = _ := by
          rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (farInj W)ᴴ,
            farInj_conj_mul_self, Matrix.one_mul]
  have hKA : (cfc (pairWeight h) (fT S) * (1 - fT S))ᴴ * (cfc (pairWeight h) (fT S) * (1 - fT S)) *
      cfc (omitIndicator h) (fT S) =
      (cfc (pairWeight h) (fT S) * (1 - fT S))ᴴ * (cfc (pairWeight h) (fT S) * (1 - fT S)) := by
    have e1 : (1 - fT S) = cfc (fun x : ℝ => 1 - x) (fT S) := by
      rw [cfc_sub _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
        cfc_const_one ℝ _ fT_isHermitian.isSelfAdjoint, cfc_id' ℝ _ fT_isHermitian.isSelfAdjoint]
    rw [e1, conjTranspose_mul, cfc_conjTranspose, cfc_conjTranspose, cfc_mul', cfc_mul', cfc_mul',
      cfc_mul']
    congr 1; funext t; unfold omitIndicator pairWeight; split_ifs <;> simp
  have hX : (Sᴴ * (nearPortProj W + (fPi h S)ᴴ * fPi h S) * S * (nearPortProj W + fA h S)).trace =
      (nearPortProj W + (fPi h S)ᴴ * fPi h S).trace -
        (fT S + (cfc (pairWeight h) (fT S) * (1 - fT S))ᴴ *
          (cfc (pairWeight h) (fT S) * (1 - fT S))).trace +
        ((fT S + (cfc (pairWeight h) (fT S) * (1 - fT S))ᴴ *
          (cfc (pairWeight h) (fT S) * (1 - fT S))) * cfc (omitIndicator h) (fT S)).trace := by
    rw [Matrix.mul_add, trace_add, trace_mul_nearPortProj, trace_mul_farEmbed]
    have e : (farInj W)ᴴ * (Sᴴ * (nearPortProj W + (fPi h S)ᴴ * fPi h S) * S) * farInj W =
        fT S + (cfc (pairWeight h) (fT S) * (1 - fT S))ᴴ *
          (cfc (pairWeight h) (fT S) * (1 - fT S)) := by
      rw [← hK, ← far_outProj hS]; simp only [Matrix.mul_add, Matrix.add_mul]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hS', Matrix.one_mul]
  rw [splitCurrent, trace_conj_sub_sq hS' hE hE', hX, Matrix.add_mul, hKA, trace_add, trace_add,
    trace_add, trace_add, htrB]
  have hret : fT S - fT S * cfc (omitIndicator h) (fT S) = cfc (retW h) (fT S) := by
    calc fT S - fT S * cfc (omitIndicator h) (fT S) = cfc (fun x : ℝ => x) (fT S) -
          cfc (fun x : ℝ => x) (fT S) * cfc (omitIndicator h) (fT S) := by
          rw [cfc_id' ℝ (fT S) fT_isHermitian.isSelfAdjoint]
      _ = cfc (fun t : ℝ => t - t * omitIndicator h t) (fT S) := by
          rw [cfc_mul', ← cfc_sub _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
      _ = cfc (retW h) (fT S) := by
          congr 1; funext t; unfold retW omitIndicator
          split_ifs <;> first | ring1 | (exfalso; linarith)
  have htr := congrArg trace hret
  rw [trace_sub, trace_cfc fT_isHermitian] at htr
  rw [← htr]
  ring

end BlockBand.SourceProcess.ClosedFeas
