module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWState
public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWStepAbs
public import BlockBand.SourceProcess.PhysApprox.B3GenMem

/-!
# One step of a test under the closed law

Closed law `μ = closedLaw b W np`, filtration `b3Sigma W j np`, Borel alive set
`A'_j = b3AliveM … R … j` (a.e. equal to `b3Alive`), at one step `j → j + 1` without a birth.

* `e1S`, `e2S`: the conditional drift and bracket errors of the basic increments; `pinE1`,
  `pinE2`: the summands of `ComplexClosedSummed` (`genDriftStep`, `genBrStep`, `genConjStep`)
  they equal (**`e1S_eq`, `e2S_eq`**; conjugate increments via `condExp_conj` and the Hermitian
  symmetry `conj dG_e = dG_{e*}`; every real second moment is covered).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal

variable {W np K : ℕ}

/-! ## Abstract a.e. lemmas for the errors -/

section AE

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem lint_congr_set {A A' : Set Ω} (hAA : A =ᵐ[μ] A') (X P : Ω → ℂ) :
    ∫⁻ y, ‖A.indicator (fun y => μ[A.indicator X | m] y - P y) y‖ₑ ∂μ =
      ∫⁻ y, ‖A'.indicator (fun y => μ[A'.indicator X | m] y - P y) y‖ₑ ∂μ := by
  have h1 : μ[A.indicator X | m] =ᵐ[μ] μ[A'.indicator X | m] :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hAA)
  have h2 : A.indicator (fun y => μ[A'.indicator X | m] y - P y) =ᵐ[μ]
      A'.indicator (fun y => μ[A'.indicator X | m] y - P y) := indicator_ae_eq_of_ae_eq_set hAA
  refine lintegral_congr_ae ?_
  filter_upwards [h1, h2] with y hy1 hy2
  rw [← hy2]
  by_cases hy : y ∈ A
  · simp [Set.indicator_of_mem hy, hy1]
  · simp [Set.indicator_of_notMem hy]

theorem enorm_conj' (z : ℂ) : ‖conj z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]

theorem lint_conj (A : Set Ω) (X P P' : Ω → ℂ) (hP : ∀ y, P' y = conj (P y)) :
    ∫⁻ y, ‖A.indicator (fun y => μ[A.indicator (fun y => conj (X y)) | m] y - P' y) y‖ₑ ∂μ =
      ∫⁻ y, ‖A.indicator (fun y => μ[A.indicator X | m] y - P y) y‖ₑ ∂μ := by
  have e : A.indicator (fun y => conj (X y)) = fun y => conj (A.indicator X y) := by
    funext y; by_cases hy : y ∈ A <;> simp [hy]
  rw [e]
  refine lintegral_congr_ae ((condExp_conj (m := m) (μ := μ) (f := A.indicator X)).mono
    fun y hy => ?_)
  dsimp only
  by_cases hA : y ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    rw [hy, hP, ← map_sub, enorm_conj']
  · simp [Set.indicator_of_notMem hA]

end AE

/-! ## The errors of the basic increments -/

section Errors

variable (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)

/-- The conditional drift error of the basic increment `i` at step `j` (Borel alive set). -/
def e1S (j : ℕ) (i : BI K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3AliveM b E s h τ m R W j Vs).indicator
        (fun y => betaS b E s h τ m W Vs j y i) | b3Sigma W j np] y -
      (W : ℂ)⁻¹ * dvec b E (b3ClosedGramAt b E s h τ m W j Vs y) i) y‖ₑ ∂closedLaw b W np

/-- The conditional bracket error of the basic increments `i, i'` at step `j`. -/
def e2S (j : ℕ) (i i' : BI K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3AliveM b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3AliveM b E s h τ m R W j Vs).indicator
        (fun y => betaS b E s h τ m W Vs j y i * betaS b E s h τ m W Vs j y i') |
          b3Sigma W j np] y -
      (W : ℂ)⁻¹ * Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y) i i') y‖ₑ ∂closedLaw b W np

/-- The coordinate of a basic increment. -/
def cOf : BI K np → CIdx K np
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl a) => Sum.inr a
  | Sum.inr (Sum.inr a) => Sum.inr a

/-- The summand of `ComplexClosedSummed` bounding `e1S`. -/
def pinE1 (j : ℕ) (i : BI K np) : ℝ≥0∞ := genDriftStep b E s h τ m R W j Vs (cOf i)

/-- The summand of `ComplexClosedSummed` bounding `e2S`. -/
def pinE2 (j : ℕ) : BI K np → BI K np → ℝ≥0∞
  | Sum.inl e, Sum.inl e' => genBrStep b E s h τ m R W j Vs (Sum.inl e) (Sum.inl e')
  | Sum.inl e, Sum.inr (Sum.inl a) => genBrStep b E s h τ m R W j Vs (Sum.inl e) (Sum.inr a)
  | Sum.inl e, Sum.inr (Sum.inr a) =>
      genBrStep b E s h τ m R W j Vs (Sum.inl (eStar e)) (Sum.inr a)
  | Sum.inr (Sum.inl a), Sum.inl e => genBrStep b E s h τ m R W j Vs (Sum.inr a) (Sum.inl e)
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inl a') =>
      genBrStep b E s h τ m R W j Vs (Sum.inr a) (Sum.inr a')
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inr a') => genConjStep b E s h τ m R W j Vs a a'
  | Sum.inr (Sum.inr a), Sum.inl e =>
      genBrStep b E s h τ m R W j Vs (Sum.inr a) (Sum.inl (eStar e))
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl a') => genConjStep b E s h τ m R W j Vs a a'
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr a') =>
      genBrStep b E s h τ m R W j Vs (Sum.inr a) (Sum.inr a')

variable {b E}

theorem e1S_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {j : ℕ} (hj : ¬ IsBirthStep τ W j)
    (i : BI K np) : e1S b E s h τ m R W Vs j i = pinE1 b E s h τ m R W Vs j i := by
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs (np := np)
  unfold e1S pinE1 genDriftStep
  rw [lint_congr_set hAA]
  rcases i with e | a | a
  · simp only [betaS_inl b E s h τ m W Vs hj, dvec, cOf, cDrift]; rfl
  · simp only [betaS_K b E s h τ m W Vs hj, dvec, cOf, cDrift]
  · simp only [betaS_Kc b E s h τ m W Vs hj, dvec, cOf, cDrift]
    exact lint_conj (m := b3Sigma W j np) (μ := closedLaw b W np)
      (b3AliveM b E s h τ m R W j Vs) (b3dX b E s h τ m W j Vs (Sum.inr a))
      (fun _ => (W : ℂ)⁻¹ * 0) (fun _ => (W : ℂ)⁻¹ * 0) (fun y => by simp)

theorem e2S_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {j : ℕ} (hj : ¬ IsBirthStep τ W j)
    (i i' : BI K np) : e2S b E s h τ m R W Vs j i i' = pinE2 b E s h τ m R W Vs j i i' := by
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs (np := np)
  have hc : ∀ e, (fun y => b3dX b E s h τ m W j Vs (Sum.inl e) y) =
      fun y => conj (b3dX b E s h τ m W j Vs (Sum.inl (eStar e)) y) := fun e => funext fun y => by
    rw [conj_b3dX_inl]; rfl
  unfold e2S
  rcases i with e | a | a <;> rcases i' with e' | a' | a'
  · simp only [betaS_inl b E s h τ m W Vs hj, Bmat, pinE2, genBrStep]
    rw [lint_congr_set hAA]; rfl
  · simp only [betaS_inl b E s h τ m W Vs hj, betaS_K b E s h τ m W Vs hj, Bmat, pinE2,
      genBrStep]
    rw [lint_congr_set hAA]; rfl
  · simp only [betaS_inl b E s h τ m W Vs hj, betaS_Kc b E s h τ m W Vs hj, Bmat, pinE2,
      genBrStep]
    rw [lint_congr_set hAA]
    have e1 : (fun y => b3dX b E s h τ m W j Vs (Sum.inl e) y *
        conj (b3dX b E s h τ m W j Vs (Sum.inr a') y)) = fun y =>
          conj (b3dX b E s h τ m W j Vs (Sum.inl (eStar e)) y *
            b3dX b E s h τ m W j Vs (Sum.inr a') y) := funext fun y => by
      rw [map_mul, ← congrFun (hc e) y]
    rw [e1]
    exact lint_conj (m := b3Sigma W j np) (μ := closedLaw b W np)
      (b3AliveM b E s h τ m R W j Vs) (fun y => b3dX b E s h τ m W j Vs (Sum.inl (eStar e)) y *
        b3dX b E s h τ m W j Vs (Sum.inr a') y)
      (fun y => (W : ℂ)⁻¹ * cCov b E (Sum.inl (eStar e)) (Sum.inr a')
        (b3ClosedGramAt b E s h τ m W j Vs y)) _ (fun y => by simp [cCov, kG])
  · simp only [betaS_inl b E s h τ m W Vs hj, betaS_K b E s h τ m W Vs hj, Bmat, pinE2,
      genBrStep]
    rw [lint_congr_set hAA]; rfl
  · simp only [betaS_K b E s h τ m W Vs hj, Bmat, pinE2, genBrStep]
    rw [lint_congr_set hAA]; rfl
  · simp only [betaS_K b E s h τ m W Vs hj, betaS_Kc b E s h τ m W Vs hj, Bmat, pinE2,
      genConjStep]
    rw [lint_congr_set hAA]; rfl
  · simp only [betaS_inl b E s h τ m W Vs hj, betaS_Kc b E s h τ m W Vs hj, Bmat, pinE2,
      genBrStep]
    rw [lint_congr_set hAA]
    have e1 : (fun y => conj (b3dX b E s h τ m W j Vs (Sum.inr a) y) *
        b3dX b E s h τ m W j Vs (Sum.inl e') y) = fun y =>
          conj (b3dX b E s h τ m W j Vs (Sum.inr a) y *
            b3dX b E s h τ m W j Vs (Sum.inl (eStar e')) y) := funext fun y => by
      rw [map_mul, ← congrFun (hc e') y]
    rw [e1]
    exact lint_conj (m := b3Sigma W j np) (μ := closedLaw b W np)
      (b3AliveM b E s h τ m R W j Vs) (fun y => b3dX b E s h τ m W j Vs (Sum.inr a) y *
        b3dX b E s h τ m W j Vs (Sum.inl (eStar e')) y)
      (fun y => (W : ℂ)⁻¹ * cCov b E (Sum.inr a) (Sum.inl (eStar e'))
        (b3ClosedGramAt b E s h τ m W j Vs y)) _ (fun y => by simp [cCov, kG])
  · simp only [betaS_K b E s h τ m W Vs hj, betaS_Kc b E s h τ m W Vs hj, Bmat, pinE2,
      genConjStep]
    rw [lint_congr_set hAA]
    have e1 : (fun y => conj (b3dX b E s h τ m W j Vs (Sum.inr a) y) *
        b3dX b E s h τ m W j Vs (Sum.inr a') y) = fun y =>
          conj (b3dX b E s h τ m W j Vs (Sum.inr a) y *
            conj (b3dX b E s h τ m W j Vs (Sum.inr a') y)) := funext fun y => by
      rw [map_mul, Complex.conj_conj]
    rw [e1]
    exact lint_conj (m := b3Sigma W j np) (μ := closedLaw b W np)
      (b3AliveM b E s h τ m R W j Vs) (fun y => b3dX b E s h τ m W j Vs (Sum.inr a) y *
        conj (b3dX b E s h τ m W j Vs (Sum.inr a') y))
      (fun y => (W : ℂ)⁻¹ * kConjCov b E a a' (b3ClosedGramAt b E s h τ m W j Vs y)) _
      (fun y => by simp [kC])
  · simp only [betaS_Kc b E s h τ m W Vs hj, Bmat, pinE2, genBrStep]
    rw [lint_congr_set hAA]
    have e1 : (fun y => conj (b3dX b E s h τ m W j Vs (Sum.inr a) y) *
        conj (b3dX b E s h τ m W j Vs (Sum.inr a') y)) = fun y =>
          conj (b3dX b E s h τ m W j Vs (Sum.inr a) y *
            b3dX b E s h τ m W j Vs (Sum.inr a') y) := funext fun y => by
      rw [map_mul]
    rw [e1]
    exact lint_conj (m := b3Sigma W j np) (μ := closedLaw b W np)
      (b3AliveM b E s h τ m R W j Vs) (fun y => b3dX b E s h τ m W j Vs (Sum.inr a) y *
        b3dX b E s h τ m W j Vs (Sum.inr a') y)
      (fun y => (W : ℂ)⁻¹ * cCov b E (Sum.inr a) (Sum.inr a')
        (b3ClosedGramAt b E s h τ m W j Vs y)) _ (fun y => by simp [cCov])

end Errors

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
