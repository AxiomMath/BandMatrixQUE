module
public import BlockBand.SourceProcess.Stochastic.Levy.Joint
public import BlockBand.SourceProcess.Stochastic.Levy.PredVersion
public import BlockBand.SourceProcess.Stochastic.Levy.Penrose
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Lévy's characterization and the Wiener extension: summary

Files (`Stochastic/Levy/`): `Exponential` (test functions, zero Itô drift), `Martingale`
(exponential martingales via the Itô formula), `CharFun` (conditional characteristic function),
`Brownian` (`IsFiltrationBrownian`, Lévy), `Product` (product filtrations, lifts),
`Wiener` (canonical Wiener extension), `BrownianIntegrator` (converse: Brownian motions are
`IsL2IntegratorVec` with identity brackets), `Extension` (product martingales, lifted
martingale-problem solutions, Lévy in integrator form), `Joint` (the joint integrator
`(N, B')`), `PredVersion` (predictable version for Borel integrands), `Penrose`
(pseudoinverse identities).

* `levy_characterization`: the conditional characteristic function and the Brownian property.
* `wienerExtension_spec`: the extension facts in one statement.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open scoped NNReal ENNReal

universe u

/-- **Lévy's characterization** (arbitrary filtered probability space, raw filtration,
modification form). If `M` is progressive, a.s. continuous, `M_0 = 0` a.s., and `M^i` and
`M^i M^j - δ_ij t` have `𝓖`-martingale modifications, then for all `u` and `s ≤ t`,
`E[exp(i⟨u, M_t - M_s⟩) | 𝓖_s] = exp(-|u|²(t-s)/2)` a.s., and `M` is a `𝓖`-Brownian motion
(increments independent of `𝓖_s` with law `N(0, (t-s) I)`). -/
theorem levy_characterization {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : ℝ≥0 → Ω → Fin d → ℝ} (hM : IsLevyMartingale Q 𝓖 M) :
    (∀ (u : Fin d → ℝ) (s t : ℝ≥0), s ≤ t →
      Q[fun ω => Complex.exp ((pairing u (M t ω - M s ω) : ℂ) * Complex.I) | 𝓖 s] =ᵐ[Q]
        fun _ => ((Real.exp (-(sqNorm u / 2 * ((t : ℝ) - s))) : ℝ) : ℂ)) ∧
      IsFiltrationBrownian Q 𝓖 M :=
  ⟨fun u _ _ hst => hM.condExp_cexp u hst, hM.isFiltrationBrownian⟩

/-- **The Wiener extension.** On `Ω × C(ℝ≥0,ℝ)^m` with `Q ⊗ Wiener` and the filtration
`𝓖_t ⊗ σ(B'_r, r ≤ t)`: `B'` is a Brownian motion for the extension filtration, independent
of the first factor; it is a vector integrator with identity brackets; martingales of the
first factor lift to martingales; and every vector integrator `N` of the first factor
extends jointly with `B'` to a vector integrator with bracket densities `diag(a, I)`. -/
theorem wienerExtension_spec {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (m : ℕ) :
    IsFiltrationBrownian (extMeasure Q m) (extFiltration 𝓖 m) (extB m) ∧
      IndepFun (Prod.fst : Ω × WienerSpace m → Ω) Prod.snd (extMeasure Q m) ∧
      IsL2IntegratorVec (extMeasure Q m) (extFiltration 𝓖 m) (fun k t x => extB m t x k)
        (fun k l _ _ => if k = l then 1 else 0) ∧
      (∀ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q →
        Martingale (fun t (x : Ω × WienerSpace m) => N t x.1) (extFiltration 𝓖 m)
          (extMeasure Q m)) ∧
      (∀ {ι : Type} [Fintype ι] (N : ι → ℝ≥0 → Ω → ℝ) (a : ι → ι → ℝ≥0 → Ω → ℝ),
        IsL2IntegratorVec Q 𝓖 N a →
        IsL2IntegratorVec (extMeasure Q m) (extFiltration 𝓖 m) (jointN N m) (jointA a m)) :=
  ⟨isFiltrationBrownian_extension m, indepFun_extension m,
    (isFiltrationBrownian_extension m).isL2IntegratorVec, fun _ hN => martingale_lift_fst hN,
    fun _ _ h => h.jointExtension m⟩

end BlockBand.SourceProcess.Stochastic.Levy
