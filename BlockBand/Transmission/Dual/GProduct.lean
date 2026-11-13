module

public import BlockBand.Transmission.Dual.GProdTools

/-!
# Products of martingale-problem solutions

Two solutions `Y₁` (on `(Ω₁, 𝓖₁, Q₁)`, in `ℝ^{d₁}`, domain `U₁`) and `Y₂` (on `(Ω₂, 𝓖₂, Q₂)`, in
`ℝ^{d₂}`, domain `U₂`) of martingale problems with continuous coefficients give, on `Ω₁ × Ω₂`
with `Q₁ ⊗ Q₂` and the product filtration, the solution `prodPath Y₁ Y₂ = (Y₁, Y₂)` of the
**decoupled** problem: drift `(b₁, b₂)`, block diagonal covariance `diag(a₁, a₂)`, domain
`U₁ × U₂` (`isMPSolutionOn_prod`).

Proof: for an interior domain `W` of `U₁ × U₂`, the projections of `closure W` lie in interior
domains `W₁`, `W₂` of `U₁`, `U₂`, and the exit time from `W` is at most those of the factors.
The factor processes stopped at `W₁`, `W₂` lift to the product, cross brackets are products of
independent martingales (`hasMM_mul_lift`), and stopping again at the exit from `W`
(`hasMM_stop_congr`) gives the martingale-problem conditions. This gives the base process
`P⁰ = P⁰_pair ⊗ P⁰_rest` and the combined process of `Q^{(j)}` (after relabelling).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d₁ d₂ : ℕ}

/-- The first `d₁` coordinates. -/
def leftPart (y : Fin (d₁ + d₂) → ℝ) : Fin d₁ → ℝ := fun i => y (Fin.castAdd d₂ i)

/-- The last `d₂` coordinates. -/
def rightPart (y : Fin (d₁ + d₂) → ℝ) : Fin d₂ → ℝ := fun j => y (Fin.natAdd d₁ j)

theorem continuous_leftPart : Continuous (leftPart (d₁ := d₁) (d₂ := d₂)) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_rightPart : Continuous (rightPart (d₁ := d₁) (d₂ := d₂)) :=
  continuous_pi fun _ => continuous_apply _

/-- The decoupled drift `(b₁, b₂)`. -/
def prodDrift (b₁ : (Fin d₁ → ℝ) → Fin d₁ → ℝ) (b₂ : (Fin d₂ → ℝ) → Fin d₂ → ℝ)
    (y : Fin (d₁ + d₂) → ℝ) : Fin (d₁ + d₂) → ℝ :=
  Fin.append (b₁ (leftPart y)) (b₂ (rightPart y))

/-- The block diagonal covariance `diag(a₁, a₂)`. -/
def prodDiff (a₁ : (Fin d₁ → ℝ) → Matrix (Fin d₁) (Fin d₁) ℝ)
    (a₂ : (Fin d₂ → ℝ) → Matrix (Fin d₂) (Fin d₂) ℝ) (y : Fin (d₁ + d₂) → ℝ) :
    Matrix (Fin (d₁ + d₂)) (Fin (d₁ + d₂)) ℝ :=
  Matrix.of fun k l => Fin.addCases (fun i => Fin.addCases (fun j => a₁ (leftPart y) i j)
    (fun _ => 0) l) (fun i => Fin.addCases (fun _ => 0) (fun j => a₂ (rightPart y) i j) l) k

/-- The product domain `U₁ × U₂`. -/
def prodDomain (U₁ : Set (Fin d₁ → ℝ)) (U₂ : Set (Fin d₂ → ℝ)) : Set (Fin (d₁ + d₂) → ℝ) :=
  {y | leftPart y ∈ U₁ ∧ rightPart y ∈ U₂}

section Path

variable {Ω₁ Ω₂ : Type*}

/-- The combined path `(Y₁, Y₂)` on `Ω₁ × Ω₂`. -/
def prodPath (Y₁ : ℝ≥0 → Ω₁ → Fin d₁ → ℝ) (Y₂ : ℝ≥0 → Ω₂ → Fin d₂ → ℝ) :
    ℝ≥0 → Ω₁ × Ω₂ → Fin (d₁ + d₂) → ℝ :=
  fun t x => Fin.append (Y₁ t x.1) (Y₂ t x.2)

variable {Y₁ : ℝ≥0 → Ω₁ → Fin d₁ → ℝ} {Y₂ : ℝ≥0 → Ω₂ → Fin d₂ → ℝ}

@[simp] theorem leftPart_prodPath (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    leftPart (prodPath Y₁ Y₂ t x) = Y₁ t x.1 :=
  funext fun i => Fin.append_left _ _ i

@[simp] theorem rightPart_prodPath (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    rightPart (prodPath Y₁ Y₂ t x) = Y₂ t x.2 :=
  funext fun j => Fin.append_right _ _ j

variable {b₁ : (Fin d₁ → ℝ) → Fin d₁ → ℝ} {b₂ : (Fin d₂ → ℝ) → Fin d₂ → ℝ}
  {a₁ : (Fin d₁ → ℝ) → Matrix (Fin d₁) (Fin d₁) ℝ} {a₂ : (Fin d₂ → ℝ) → Matrix (Fin d₂) (Fin d₂) ℝ}

theorem mpCompensated_prod_castAdd (i : Fin d₁) (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    mpCompensated (prodDrift b₁ b₂) (prodPath Y₁ Y₂) (Fin.castAdd d₂ i) t x =
      mpCompensated b₁ Y₁ i t x.1 := by
  simp only [mpCompensated, prodDrift, leftPart_prodPath, rightPart_prodPath, Fin.append_left]
  simp only [prodPath, Fin.append_left]

theorem mpCompensated_prod_natAdd (j : Fin d₂) (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    mpCompensated (prodDrift b₁ b₂) (prodPath Y₁ Y₂) (Fin.natAdd d₁ j) t x =
      mpCompensated b₂ Y₂ j t x.2 := by
  simp only [mpCompensated, prodDrift, leftPart_prodPath, rightPart_prodPath, Fin.append_right]
  simp only [prodPath, Fin.append_right]

@[simp] theorem prodDiff_cc (y : Fin (d₁ + d₂) → ℝ) (i j : Fin d₁) :
    prodDiff a₁ a₂ y (Fin.castAdd d₂ i) (Fin.castAdd d₂ j) = a₁ (leftPart y) i j := by
  simp [prodDiff]

@[simp] theorem prodDiff_cn (y : Fin (d₁ + d₂) → ℝ) (i : Fin d₁) (j : Fin d₂) :
    prodDiff a₁ a₂ y (Fin.castAdd d₂ i) (Fin.natAdd d₁ j) = 0 := by
  simp [prodDiff]

@[simp] theorem prodDiff_nc (y : Fin (d₁ + d₂) → ℝ) (i : Fin d₂) (j : Fin d₁) :
    prodDiff a₁ a₂ y (Fin.natAdd d₁ i) (Fin.castAdd d₂ j) = 0 := by
  simp [prodDiff]

@[simp] theorem prodDiff_nn (y : Fin (d₁ + d₂) → ℝ) (i j : Fin d₂) :
    prodDiff a₁ a₂ y (Fin.natAdd d₁ i) (Fin.natAdd d₁ j) = a₂ (rightPart y) i j := by
  simp [prodDiff]

theorem exitTime_prod_le_fst {W : Set (Fin (d₁ + d₂) → ℝ)} {W₁ : Set (Fin d₁ → ℝ)}
    (hW : ∀ y ∈ W, leftPart y ∈ W₁) (x : Ω₁ × Ω₂) :
    exitTimeFrom W (prodPath Y₁ Y₂) x ≤ exitTimeFrom W₁ Y₁ x.1 :=
  le_iInf₂ fun t ht => iInf₂_le t fun hy => ht (by simpa using hW _ hy)

theorem exitTime_prod_le_snd {W : Set (Fin (d₁ + d₂) → ℝ)} {W₂ : Set (Fin d₂ → ℝ)}
    (hW : ∀ y ∈ W, rightPart y ∈ W₂) (x : Ω₁ × Ω₂) :
    exitTimeFrom W (prodPath Y₁ Y₂) x ≤ exitTimeFrom W₂ Y₂ x.2 :=
  le_iInf₂ fun t ht => iInf₂_le t fun hy => ht (by simpa using hW _ hy)

end Path

/-- The projections of an interior domain of `U₁ × U₂` lie in interior domains of the factors. -/
theorem exists_factor_domains {U₁ : Set (Fin d₁ → ℝ)} {U₂ : Set (Fin d₂ → ℝ)} (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂) {W : Set (Fin (d₁ + d₂) → ℝ)} (hW : IsInteriorDomain W (prodDomain U₁ U₂)) :
    (∃ W₁, IsInteriorDomain W₁ U₁ ∧ ∀ y ∈ W, leftPart y ∈ W₁) ∧
      ∃ W₂, IsInteriorDomain W₂ U₂ ∧ ∀ y ∈ W, rightPart y ∈ W₂ := by
  obtain ⟨W₁, h₁, hK₁⟩ := exists_interiorDomain_superset (hW.2.1.image continuous_leftPart) hU₁
    (by rintro _ ⟨y, hy, rfl⟩; exact (hW.2.2 hy).1)
  obtain ⟨W₂, h₂, hK₂⟩ := exists_interiorDomain_superset (hW.2.1.image continuous_rightPart) hU₂
    (by rintro _ ⟨y, hy, rfl⟩; exact (hW.2.2 hy).2)
  exact ⟨⟨W₁, h₁, fun y hy => hK₁ ⟨y, subset_closure hy, rfl⟩⟩,
    ⟨W₂, h₂, fun y hy => hK₂ ⟨y, subset_closure hy, rfl⟩⟩⟩

end BlockBand.Transmission.Dual.G
