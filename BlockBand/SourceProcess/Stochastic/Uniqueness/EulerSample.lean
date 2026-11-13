module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerLimit
public import BlockBand.SourceProcess.Stochastic.Uniqueness.BrownianLaw
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Euler scheme as a measurable functional of `(ξ, (B_q)_{q ∈ ℚ≥0})`

The laws of the Euler schemes depend only on the law of `initBrownian ξ B` (`BrownianLaw`).

* `wOf z`: the path read off a sample `z : Option ℚ≥0 → ℝ^d` (`z (some q)` at rational
  times, `0` elsewhere).
* `eulF c m z q = eulerX c m (z none) (wOf z) q`; **`measurable_eulF`**.
* **`eulX_eq_eulF`**: `X^m_q(ω) = eulF c m (initBrownian ξ B ω) q` for every rational `q`
  (pointwise, no null set).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory Set Matrix
open scoped NNReal

variable {d : ℕ}

/-- The path of a sample at rational times. -/
def wOf (z : Option ℚ≥0 → Fin d → ℝ) (s : ℝ≥0) : Fin d → ℝ :=
  open Classical in
  if h : ∃ q : ℚ≥0, (q : ℝ≥0) = s then z (some h.choose) else 0

theorem wOf_coe (z : Option ℚ≥0 → Fin d → ℝ) (q : ℚ≥0) : wOf z q = z (some q) := by
  have h : ∃ q' : ℚ≥0, (q' : ℝ≥0) = q := ⟨q, rfl⟩
  simp only [wOf, h, dite_true]
  congr 2
  exact NNRat.cast_injective h.choose_spec

/-- The rational grid point `j 2^{-m}`. -/
def gridQ (m j : ℕ) : ℚ≥0 := j / 2 ^ m

theorem coe_gridQ (m j : ℕ) : (gridQ m j : ℝ≥0) = gridT m j := by
  simp [gridQ, gridT]

/-- The Euler functional on samples. -/
def eulF (c : LipCoef d) (m : ℕ) (z : Option ℚ≥0 → Fin d → ℝ) (q : ℚ≥0) : Fin d → ℝ :=
  eulerX c m (z none) (wOf z) q

theorem measurable_eulerE_sample (c : LipCoef d) (m j : ℕ) :
    Measurable fun z : Option ℚ≥0 → Fin d → ℝ => eulerE c m (z none) (wOf z) j := by
  induction j with
  | zero => exact measurable_pi_apply none
  | succ j ih =>
    have hw : ∀ k, Measurable fun z : Option ℚ≥0 → Fin d → ℝ => wOf z (gridT m k) := fun k => by
      simp_rw [← coe_gridQ, wOf_coe]
      exact measurable_pi_apply _
    exact (continuous_eulStep c m).measurable.comp (ih.prodMk ((hw _).prodMk (hw _)))

theorem measurable_eulF (c : LipCoef d) (m : ℕ) :
    Measurable (eulF (d := d) c m) := by
  refine Measurable.of_eval fun q => ?_
  have hb := c.continuous_b
  have hσ := c.continuous_σ
  have hG : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
      p.1 + ((q : ℝ≥0) - gridT m (gridIdx m q) : ℝ) • c.b p.1 + c.σ p.1 *ᵥ (p.2.1 - p.2.2) := by
    have h1 : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
        c.σ p.1 *ᵥ (p.2.1 - p.2.2) := (hσ.comp continuous_fst).matrix_mulVec (by fun_prop)
    fun_prop
  have hw : Measurable fun z : Option ℚ≥0 → Fin d → ℝ => wOf z (gridT m (gridIdx m q)) := by
    simp_rw [← coe_gridQ, wOf_coe]; exact measurable_pi_apply _
  have hwq : Measurable fun z : Option ℚ≥0 → Fin d → ℝ => wOf z q := by
    simp_rw [wOf_coe]; exact measurable_pi_apply _
  exact hG.measurable.comp ((measurable_eulerE_sample c m _).prodMk (hwq.prodMk hw))

theorem eulX_eq_eulF {Ω : Type*} (c : LipCoef d) (m : ℕ) (ξ : Ω → Fin d → ℝ)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (q : ℚ≥0) (ω : Ω) :
    eulX c m ξ B q ω = eulF c m (initBrownian ξ B ω) q := by
  unfold eulX eulF
  refine eulerX_congr c m (ξ ω) (fun j => ?_) ?_
  · rw [← coe_gridQ, wOf_coe]; rfl
  · rw [wOf_coe]; rfl

end BlockBand.SourceProcess.Stochastic.Uniqueness
