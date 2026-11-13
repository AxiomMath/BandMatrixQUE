module

public import BlockBand.Internal.Contracts.CriticalEntire

/-!
# The canonical matrix Cauchy series `𝖢_r` on the closed upper half-plane

The limit object of the Herglotz tail lemma is the canonical matrix Cauchy series on `{Im z > 0}`
together with its real boundary values; `IsCanonicalCauchyAtZero` records only its value at `0`.

* `canonicalResidue g = π⁻¹ g g^*`: the residue attached to a decorated sine point.
* `cauchyTruncation r ξ R z`: the symmetric cutoff `π⁻¹ Σ_{|x_j| ≤ R} g_j g_j^*/(x_j - z)` of the
  canonical Cauchy series, at any `z : ℂ`.
* `IsCanonicalCauchy r P Ξ C`: `C : Ω → ℂ → Matrix` is `𝖢_r` built from the decorated sine
  process `Ξ`. The cutoffs converge locally uniformly in probability on compact subsets of
  `{Im z > 0}`. They converge in probability at every real point (boundary values). Every
  realization is continuous on the open half-plane.
* `cauchyTruncation_zero`, `IsCanonicalCauchy.atZero`: at `z = 0` this is
  `IsCanonicalCauchyAtZero`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate Matrix

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire

/-- The residue `π⁻¹ g g^*` of the canonical Cauchy series at a decorated point with mark `g ∈ ℂ^r`. -/
def canonicalResidue {r : ℕ} (g : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  ((Real.pi : ℂ)⁻¹) • Matrix.vecMulVec g (star g)

/-- The symmetric cutoff `π⁻¹ Σ_{|x_j| ≤ R} g_j g_j^* / (x_j - z)` of the canonical Cauchy series at `z : ℂ`. Entry `(i, j)` integrates `(π (x - z))⁻¹ g_i conj(g_j)` against the
decorated point measure over `{|x| ≤ R}` (Lean's `0⁻¹ = 0` at a real pole). -/
def cauchyTruncation (r : ℕ) (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (R : ℝ) (z : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ∫ p in {p : ℝ × (Fin r → ℂ) | |p.1| ≤ R},
    ((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (p.2 i * conj (p.2 j)) ∂ξ.measure

/-- At `z = 0` the cutoff is the `truncatedCauchyEntry`. -/
theorem cauchyTruncation_zero (r : ℕ) (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (R : ℝ)
    (i j : Fin r) : cauchyTruncation r ξ R 0 i j = truncatedCauchyEntry r ξ R i j := by
  unfold cauchyTruncation truncatedCauchyEntry
  congr 1
  funext p
  push_cast
  simp

/-- **`C = 𝖢_r` on the closed upper half-plane**, built
from one decorated sine process `Ξ` (`IsDecoratedSineProcess`: unit-intensity sine process
with independent standard circular Gaussian marks `g_j ∈ ℂ^r`).
Fields: measurability of every value.
Continuity of every realization on `{Im z > 0}`.
`locallyUniform`: for every compact `K ⊆ {Im z > 0}` and `ε > 0`, the outer probability that some
entry of the cutoff differs from `C` by at least `ε` somewhere on `K` tends to `0` as `R → ∞`.
`boundary`: at every real `x`, the cutoff converges in probability to `C · x`.
The order of limits is a single limit `R → ∞`.
-/
structure IsCanonicalCauchy (r : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))) (C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ) :
    Prop where
  decorated : IsDecoratedSineProcess r P Ξ
  measurable : ∀ z i j, Measurable fun ω => C ω z i j
  continuousOn : ∀ ω, ContinuousOn (C ω) {z : ℂ | 0 < z.im}
  locallyUniform : ∀ K : Set ℂ, IsCompact K → K ⊆ {z : ℂ | 0 < z.im} → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun R : ℝ => P {ω | ∃ z ∈ K, ∃ i j,
      ε ≤ ‖cauchyTruncation r (Ξ ω) R z i j - C ω z i j‖}) atTop (𝓝 0)
  boundary : ∀ (x : ℝ) (i j : Fin r),
    TendstoInMeasure P (fun R ω => cauchyTruncation r (Ξ ω) R x i j) atTop
      (fun ω => C ω x i j)

/-- The base value of a canonical realization is the `𝖢_r(0)` contract. -/
theorem IsCanonicalCauchy.atZero {r : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ}
    (h : IsCanonicalCauchy r P Ξ C) : IsCanonicalCauchyAtZero r P Ξ (fun ω => C ω 0) where
  decorated := h.decorated
  measurable i j := h.measurable 0 i j
  limit i j := by
    have := h.boundary 0 i j
    simp only [Complex.ofReal_zero] at this
    simpa only [cauchyTruncation_zero] using this

end BlockBand.Critical.Herglotz
