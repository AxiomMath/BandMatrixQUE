module

public import BlockBand.Critical.DecoratedSine.Existence
public import BlockBand.Critical.Herglotz.Existence

/-!
# Existence of a realization of `𝖢_r(0)`

`exists_isCanonicalCauchyAtZero`: for every `r` there are a probability space, a decorated sine
process `Ξ` with marks in `ℂ^r` and a random `r × r` matrix `C` such that
`IsCanonicalCauchyAtZero r P Ξ C` holds; `C` is the value at zero of the canonical Cauchy
transform of the decorated sine process.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.DecoratedSine

open MeasureTheory
open BlockBand.Internal.Contracts.CriticalEntire

/-- **A realization of `𝖢_r(0)` exists** (`IsCanonicalCauchyAtZero`), on a sample space
`Ω : Type`, for every `r`.
-/
theorem exists_isCanonicalCauchyAtZero (r : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))) (C : Ω → Matrix (Fin r) (Fin r) ℂ),
      IsCanonicalCauchyAtZero r P Ξ C := by
  obtain ⟨Ω, _, P, Ξ, hΞ⟩ := exists_isDecoratedSineProcess r
  obtain ⟨C, hC⟩ := BlockBand.Critical.Herglotz.exists_isCanonicalCauchy hΞ
  exact ⟨Ω, inferInstance, P, Ξ, fun ω => C ω 0, hC.atZero⟩

end BlockBand.Critical.DecoratedSine
