module

public import BlockBand.Critical.Herglotz.RealConstantMain

/-!
# The Herglotz tail lemma

`herglotzTail r : HerglotzTailStatement r`: random finite atomic Herglotz functions satisfying the
hypotheses of the lemma converge in law, jointly at finitely many real points and uniformly on
compacts of the upper half-plane, to the canonical matrix Cauchy series `𝖢_r`. It combines the
assembly `herglotzTail_of_farPartSmall` with the real-constant step
`HerglotzTailHypotheses.farPartSmall`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.Herglotz

/-- Law: for every `r`, random
finite atomic `r × r` Herglotz functions `F_N` on probability spaces `(Ω N, P N)` and every
realization `(Ω', P', Ξ, C)` of the canonical series `𝖢_r` (`IsCanonicalCauchy`;
`Ξ` the decorated sine process), hypotheses 1–3 (`HerglotzTailHypotheses`: vague convergence in
law of the marked poles and residues, `E Im F_N(iY) → I_r`, Cauchy(0, ‖v‖²) boundary laws)
imply `HerglotzTailConclusion`: for every `k`, real points `x : Fin k → ℝ` and compact
`K ⊆ {Im z > 0}`, `((F_N(x_a))_a, F_N|_K) ⇒ ((𝖢_r(x_a))_a, 𝖢_r|_K)` in
`(Fin k → Matrix) × C(K, Matrix)` (entrywise × compact-open topology, Borel σ-algebra).
No stationarity or tail independence is assumed.
Uniformity: none (a limit statement in `N` only).
Usable for a `IsCanonicalCauchyAtZero` value through `herglotzTail_of_atZero`.
Effective for `r ≥ 1`: at `r = 0` the
hypothesis `poles` cannot hold, so `herglotzTail 0` is vacuous; for
the matrix closing theorem at `r = 0` use `MatrixClosing.Poles.matrixClosingAt_zero`.
-/
theorem herglotzTail (r : ℕ) : HerglotzTailStatement r := by
  intro Ω _ P _ F Ω' _ P' _ Ξ C hC h
  exact herglotzTail_of_farPartSmall hC h (h.farPartSmall hC.decorated)

end BlockBand.Critical.Herglotz
