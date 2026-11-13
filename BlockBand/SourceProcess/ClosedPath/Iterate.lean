module

public import BlockBand.SourceProcess.ClosedPath.FarStep

/-!
# The path closed at time `s`, grown to any later length

* `stepProd N j₀ m = N_{j₀} N_{j₀+1} ⋯ N_{j₀+m-1}` (ordered transport product).
* `conj_stepProd_iterate` (algebra): one-step relations `C_{j+1}ᴴN_jᴴ = M_jᴴC_jᴴ` iterate to
  `C_{j₀+m}ᴴ (stepProd N j₀ m)ᴴ = (stepProd M j₀ m)ᴴ C_{j₀}ᴴ`.
* **`ae_closedCurrent_iterate`** (physical): almost surely, if `n_s ≥ 1`, for every `m` and
  every phase `z` at which `1 - zN` is invertible at the lengths `n_s, …, n_s + m`, the retained
  current columns transported by the physical path to `n_s + m` and closed there with the
  closing map equal the time-`s` frame `V_s` transported by the **closed** transports
  `N^cl_j = (1-A)N_jC_{j+1}(z)`:
  `C_{n_s+m}(z)ᴴ (N_{n_s}⋯N_{n_s+m-1})ᴴ V_s = (N^cl_{n_s}⋯N^cl_{n_s+m-1})ᴴ V_s`.
  (`V_s` is not moved by `C_{n_s}(z)ᴴ`, `closedCurFrame_eq`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open MeasureTheory Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedLimit
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Bridge
open BlockBand.Internal.Contracts.TransmissionLaws

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordered product `N_{j₀} N_{j₀+1} ⋯ N_{j₀+m-1}`. -/
def stepProd (N : ℕ → Matrix ι ι ℂ) (j₀ : ℕ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | m + 1 => stepProd N j₀ m * N (j₀ + m)

/-- **Iterating the one-step closed transport.** -/
theorem conj_stepProd_iterate (C N M : ℕ → Matrix ι ι ℂ) (j₀ m : ℕ)
    (h : ∀ i, i < m → (C (j₀ + i + 1))ᴴ * (N (j₀ + i))ᴴ = (M (j₀ + i))ᴴ * (C (j₀ + i))ᴴ) :
    (C (j₀ + m))ᴴ * (stepProd N j₀ m)ᴴ = (stepProd M j₀ m)ᴴ * (C j₀)ᴴ := by
  induction m with
  | zero => simp [stepProd]
  | succ m ih =>
    have ih' := ih fun i hi => h i (by omega)
    simp only [stepProd, conjTranspose_mul]
    rw [show j₀ + (m + 1) = j₀ + m + 1 by omega, ← Matrix.mul_assoc, h m (by omega),
      Matrix.mul_assoc, ih', ← Matrix.mul_assoc]

variable {W : ℕ} {b E s h : ℝ} {K : ℕ}

/-- The closed transport `N^cl_j = (1-A)N_jC_{j+1}(z)` with the time-`s` closing data. -/
def closedTransport (b E s h : ℝ) (W : ℕ) (ω : GrowthPath W) (z : ℂ) (j : ℕ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) *
    (transportN b E W j ω * physClosingMapAt b E s h W (j + 1) ω z)

/-- **The closed current columns are the closed transports of the time-`s` frame.** -/
theorem ae_closedCurrent_iterate (π : Type*) (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hs : 1 ≤ closeLen s W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (m : ℕ) (z : ℂ), (∀ i, i ≤ m →
      IsUnit (1 - z • closingN (scatteringMatrix b E W (closeLen s W + i) ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) →
      (physClosingMapAt b E s h W (closeLen s W + m) ω z)ᴴ *
          (stepProd (fun j => transportN b E W j ω) (closeLen s W) m)ᴴ *
          physCurFrame b E s h K π W ω =
        (stepProd (closedTransport b E s h W ω z) (closeLen s W) m)ᴴ *
          physCurFrame b E s h K π W ω := by
  filter_upwards [ae_closedCol_transport (s := s) (h := h) hb hb2 hE1 hE2 hW] with ω hT m z hU
  have it := conj_stepProd_iterate (fun j => physClosingMapAt b E s h W j ω z)
    (fun j => transportN b E W j ω) (closedTransport b E s h W ω z) (closeLen s W) m
    (fun i hi => hT _ (by omega) z (hU i hi.le) (by
      have := hU (i + 1) (by omega); rwa [← add_assoc] at this))
  rw [it, Matrix.mul_assoc, closedCurFrame_eq]

end BlockBand.SourceProcess.ClosedPath
