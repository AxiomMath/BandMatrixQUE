module

public import BlockBand.SourceProcess.PhysApprox.B3CurAlg
public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# The closed transported projection is a projection of the same trace

Pure finite-dimensional algebra on a finite index type `ι`. Hypotheses: `𝕊𝕊ᴴ = 1`, `P` and `A`
orthogonal projections, `ΠΠᴴ = A`, `PA = 0`, `PΠ = 0`, `ΠP = 0`, `|z| = 1` and `1 - zN`
invertible, with `C = C(z)` the closing map (`Closing.closingMap`). With `Q = ΠᴴΠ` and
`L = (1 - Q)𝕊C`:

* `AΠ = Π` and `Q` is a projection with `Tr Q = Tr A`;
* `(1 - A)C = 1 - A`, `CA = 0`; `LᴴL = 1 - A` (from `closed_omitted_current`, i.e. `|z| = 1`);
* `LLᴴ = 1 - Q` (a projection below `1 - Q` of the same trace);
* **`closed_proj`**: `P' = Cᴴ𝕊ᴴP𝕊C = LᴴPL` is Hermitian, idempotent, and `Tr P' = Tr P`;
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3Feas

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3Cur
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- A Hermitian idempotent of trace `0` vanishes. -/
theorem eq_zero_of_proj_trace {X : Matrix ι ι ℂ} (hXH : Xᴴ = X) (hXX : X * X = X)
    (htr : X.trace = 0) : X = 0 := by
  refine trace_conjTranspose_mul_self_eq_zero_iff.1 ?_
  rw [hXH, hXX, htr]

/-- A partial isometry `ΠΠᴴ = A` with `A` idempotent satisfies `AΠ = Π`. -/
theorem mul_self_of_mul_conj {A Pi : Matrix ι ι ℂ} (hAA : A * A = A) (hPi : Pi * Piᴴ = A) :
    A * Pi = Pi := by
  have h : (A * Pi - Pi) * (A * Pi - Pi)ᴴ = 0 := by
    have hAH : Aᴴ = A := by rw [← hPi, conjTranspose_mul, conjTranspose_conjTranspose]
    calc (A * Pi - Pi) * (A * Pi - Pi)ᴴ =
        A * (Pi * Piᴴ) * A - A * (Pi * Piᴴ) - (Pi * Piᴴ) * A + Pi * Piᴴ := by
          simp only [conjTranspose_sub, conjTranspose_mul, hAH, Matrix.sub_mul, Matrix.mul_sub,
            Matrix.mul_assoc]
          abel
      _ = 0 := by rw [hPi, hAA, hAA, sub_self, zero_sub, neg_add_cancel]
  exact sub_eq_zero.1 (self_mul_conjTranspose_eq_zero.1 h)

variable [DecidableEq ι] {S P A Pi : Matrix ι ι ℂ} {z : ℂ}

/-- **The closed transported projection.** `P' = C(z)ᴴ𝕊ᴴP𝕊C(z)` is Hermitian, idempotent, and
has the trace of `P`. -/
theorem closed_proj (hS : S * Sᴴ = 1) (hPH : Pᴴ = P) (hPP : P * P = P) (hAH : Aᴴ = A)
    (hAA : A * A = A) (hPi : Pi * Piᴴ = A) (hPPi' : Pi * P = 0)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : ‖z‖ = 1) :
    (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z =
        ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z)ᴴ ∧
      ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z) *
          ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z) =
        (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z ∧
      ((closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z).trace = P.trace := by
  set C := closingMap S A Pi z with hCdef
  have hAPi : A * Pi = Pi := mul_self_of_mul_conj hAA hPi
  have hSS : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  set Q := Piᴴ * Pi with hQdef
  have hQH : Qᴴ = Q := by
    rw [hQdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPiA : Piᴴ * A = Piᴴ := by rw [← hAH, ← conjTranspose_mul, hAPi]
  have hQQ : Q * Q = Q := by
    calc Q * Q = Piᴴ * (Pi * Piᴴ) * Pi := by simp only [hQdef, Matrix.mul_assoc]
      _ = Q := by rw [hPi, hPiA]
  have hPQ : P * Q = 0 := by
    have : P * Piᴴ = 0 := by
      rw [← hPH, ← conjTranspose_mul, hPPi', conjTranspose_zero]
    rw [hQdef, ← Matrix.mul_assoc, this, Matrix.zero_mul]
  -- `(1 - A)C = 1 - A` and `CA = 0`
  have hAC := A_mul_closingMap (S := S) (z := z) hAA hAPi
  have h1AC : (1 - A) * C = 1 - A := by
    rw [Matrix.sub_mul, Matrix.one_mul, hAC, hCdef, closingMap, add_sub_cancel_right]
  have hCA : C * A = 0 := by
    rw [hCdef, closingMap, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hAA, sub_self,
      zero_add, Matrix.mul_assoc, closingT, Matrix.smul_mul, Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.one_mul, hAA, sub_self, Matrix.mul_zero, smul_zero, Matrix.mul_zero]
  have h1AH : (1 - A)ᴴ = 1 - A := by rw [conjTranspose_sub, conjTranspose_one, hAH]
  have h1A1A : (1 - A) * (1 - A) = 1 - A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hAA, sub_self, sub_zero]
  -- `CᴴC = (1 - A) + CᴴAC`, and `CᴴAC = Cᴴ𝕊ᴴQ𝕊C`
  have hCC : Cᴴ * C = (1 - A) + Cᴴ * A * C := by
    have : Cᴴ * (1 - A) * C = 1 - A := by
      calc Cᴴ * (1 - A) * C = ((1 - A) * C)ᴴ * ((1 - A) * C) := by
            rw [conjTranspose_mul, h1AH, Matrix.mul_assoc, Matrix.mul_assoc,
              ← Matrix.mul_assoc (1 - A), h1A1A]
        _ = 1 - A := by rw [h1AC, h1AH, h1A1A]
    rw [← this, ← Matrix.add_mul, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
  have hom := closed_omitted_current (S := S) hAH hAA hAPi hU hz
  rw [← hCdef] at hom
  have hCAC : Cᴴ * A * C = Cᴴ * Sᴴ * Q * S * C := by
    have e : Cᴴ * ((Pi * S)ᴴ * (Pi * S)) * C = Cᴴ * Sᴴ * Q * S * C := by
      rw [conjTranspose_mul, hQdef]; simp only [Matrix.mul_assoc]
    rw [← e, ← sub_eq_zero, ← Matrix.sub_mul, ← Matrix.mul_sub, hom]
  -- `L = (1 - Q)𝕊C`, `LᴴL = 1 - A`
  set L := (1 - Q) * S * C with hLdef
  have h1QH : (1 - Q)ᴴ = 1 - Q := by rw [conjTranspose_sub, conjTranspose_one, hQH]
  have h1Q1Q : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hQQ, sub_self, sub_zero]
  have hLL : Lᴴ * L = 1 - A := by
    calc Lᴴ * L = Cᴴ * (Sᴴ * ((1 - Q) * (1 - Q)) * S) * C := by
          rw [hLdef, conjTranspose_mul, conjTranspose_mul, h1QH]; simp only [Matrix.mul_assoc]
      _ = Cᴴ * C - Cᴴ * Sᴴ * Q * S * C := by
          rw [h1Q1Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS, Matrix.mul_sub,
            Matrix.sub_mul, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 - A := by rw [hCC, ← hCAC, add_sub_cancel_right]
  have hLA : L * (1 - A) = L := by
    rw [Matrix.mul_sub, Matrix.mul_one, hLdef, Matrix.mul_assoc _ C A, hCA, Matrix.mul_zero,
      sub_zero]
  have hQL : (1 - Q) * L = L := by
    rw [hLdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1Q1Q, Matrix.mul_assoc]
  -- `F = LLᴴ = 1 - Q`
  have hF : L * Lᴴ = 1 - Q := by
    set F := L * Lᴴ with hFdef
    have hFH : Fᴴ = F := by rw [hFdef, conjTranspose_mul, conjTranspose_conjTranspose]
    have hFF : F * F = F := by
      rw [hFdef, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ, hLL, ← Matrix.mul_assoc, hLA]
    have hQF : (1 - Q) * F = F := by rw [hFdef, ← Matrix.mul_assoc, hQL]
    have hFQ : F * (1 - Q) = F := by
      rw [← hFH, ← h1QH, ← conjTranspose_mul, hQF]
    have htrQ : Q.trace = A.trace := by rw [hQdef, trace_mul_comm, hPi]
    have htrF : F.trace = (1 - A).trace := by rw [hFdef, trace_mul_comm, hLL]
    have hX := eq_zero_of_proj_trace (X := (1 - Q) - F)
      (by rw [conjTranspose_sub, h1QH, hFH])
      (by rw [Matrix.sub_mul, Matrix.mul_sub (1 - Q) (1 - Q) F, Matrix.mul_sub F (1 - Q) F, h1Q1Q,
        hQF, hFQ, hFF]; abel)
      (by rw [trace_sub, trace_sub, htrF, trace_sub, htrQ, sub_sub_sub_cancel_left, sub_self])
    exact (sub_eq_zero.1 hX).symm
  -- `P' = LᴴPL`
  have hP1Q : P * (1 - Q) = P := by rw [Matrix.mul_sub, Matrix.mul_one, hPQ, sub_zero]
  have hPL : P * S * C = P * L := by
    rw [hLdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1Q]
  have hP' : Cᴴ * Sᴴ * P * S * C = Lᴴ * P * L := by
    calc Cᴴ * Sᴴ * P * S * C = (P * S * C)ᴴ * (P * S * C) := by
          simp only [conjTranspose_mul, hPH, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc P P, hPP]
      _ = Lᴴ * P * L := by
          rw [hPL, conjTranspose_mul, hPH, Matrix.mul_assoc, ← Matrix.mul_assoc P P, hPP,
            Matrix.mul_assoc]
  rw [hP']
  refine ⟨?_, ?_, ?_⟩
  · have e : ∀ Y : Matrix ι ι ℂ, Yᴴ * P * Y = (Yᴴ * P * Y)ᴴ := fun Y => by
      rw [conjTranspose_mul, conjTranspose_mul, hPH, conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact e L
  · calc Lᴴ * P * L * (Lᴴ * P * L) = Lᴴ * (P * (L * Lᴴ) * P) * L := by
          simp only [Matrix.mul_assoc]
      _ = Lᴴ * P * L := by
          rw [hF, hP1Q, hPP, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hF, hP1Q]

/-- **The closed frame satisfies the two-projection constraint**: if the current of the closed
frame is the closed current, `V𝖣Vᴴ = C(z)ᴴ(𝕊ᴴP𝕊 - P)C(z)`, then `TwoProjection P 𝖣 V`. -/
theorem twoProjection_of_closed {c : Type*} [Fintype c] {D : Matrix c c ℂ} {V : Matrix ι c ℂ}
    (hS : S * Sᴴ = 1) (hPH : Pᴴ = P) (hPP : P * P = P) (hAH : Aᴴ = A) (hAA : A * A = A)
    (hPi : Pi * Piᴴ = A) (hPA : P * A = 0) (hPPi : P * Pi = 0) (hPPi' : Pi * P = 0)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : ‖z‖ = 1)
    (hV : V * D * Vᴴ = (closingMap S A Pi z)ᴴ * (Sᴴ * P * S - P) * closingMap S A Pi z) :
    TwoProjection P D V := by
  have hconj := closingMap_conj_near (S := S) (z := z) hPH hPP hPA hPPi
  have hG : gramProjection P V D = (closingMap S A Pi z)ᴴ * Sᴴ * P * S * closingMap S A Pi z := by
    rw [gramProjection, hV, Matrix.mul_sub, Matrix.sub_mul, hconj, add_sub_cancel]
    simp only [Matrix.mul_assoc]
  obtain ⟨h1, h2, h3⟩ := closed_proj hS hPH hPP hAH hAA hPi hPPi' hU hz
  exact ⟨by rw [hG, ← h1], by rw [hG, h2], by rw [hG, h3]⟩

end BlockBand.SourceProcess.PhysApprox.B3Feas
