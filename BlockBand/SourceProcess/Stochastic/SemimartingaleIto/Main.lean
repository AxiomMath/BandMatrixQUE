module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localizer
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Itô formula for continuous semimartingales

`semimartingaleItoFormula_holds d : SemimartingaleItoFormula d`.

Structure of the proof:
* measurability fields: `φ` Borel and the partial derivatives Borel (`measurable_fderiv`, no
  regularity), composed with the progressive `Y, β, α`;
* path continuity and the a.s. local integrability of `itoDrift`, `itoBracket`: continuity of the
  derivatives on `univ ×ˢ U` along continuous paths in `U`;
* localizing sequence `σ_m` (`exists_localizer`): hypothesis localizer, exits from an exhaustion of
  `U`, level crossings of `∫(|β| + |α|)`, the constant `m`, switched to `0` off `{Y_0 ∈ W_m}`;
* martingale modifications of the `σ_m`-stopped compensated process and of its square minus
  `∫ itoBracket` (`LocData.ito_local`): the integral-bound Taylor scheme
  (`IHyp.exists_martingale_schemeProc'`) on the augmented state `(t, a, y)` with test functions
  `φ(t, y) - a` and its square.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

/-- **Itô's formula** for continuous semimartingales with absolutely continuous
characteristics, time-dependent `C²` test functions on `ℝ × U`. -/
theorem semimartingaleItoFormula_holds (d : ℕ) : SemimartingaleItoFormula d := by
  intro Ω _ Q _ 𝓖 Y β α H U hU hYU φ hφm hφ
  obtain ⟨σ, hσ, hσlim, hloc⟩ := exists_localizer H hU hYU hφm hφ
  have hconst : Continuous fun x : ℝ => (fun _ : Fin 1 => x) :=
    continuous_pi fun _ => continuous_id
  refine ⟨fun t => ?_, fun i => ?_, ?_, fun i => ?_, fun i => ?_, ?_, ⟨σ, hσ, hσlim, fun m => ?_⟩⟩
  · exact hconst.comp_stronglyMeasurable
      ((isStronglyProgressive_phi hφm H.progressive).stronglyAdapted t)
  · exact hconst.comp_stronglyMeasurable (isStronglyProgressive_phi hφm H.progressive i)
  · filter_upwards [H.continuous, hYU] with ω hω hU'
    exact hconst.comp (hφ.continuousOn.comp_continuous (NNReal.continuous_coe.prodMk hω)
      fun t => ⟨mem_univ _, hU' t⟩)
  · exact hconst.comp_stronglyMeasurable (isStronglyProgressive_driftPath φ H.progressive
      H.drift_progressive H.cov_progressive i)
  · exact (continuous_matrix fun _ _ => continuous_id).comp_stronglyMeasurable
      (isStronglyProgressive_bracketPath φ H.progressive H.cov_progressive i)
  · filter_upwards [H.continuous, hYU, H.integrable] with ω hω hU' hi t
    exact ⟨fun _ => integrableOn_itoDrift_path hU hφ hω hU' t (hi t).1 (hi t).2,
      fun _ _ => integrableOn_itoBracket_path hU hφ hω hU' t (hi t).2⟩
  · obtain ⟨⟨W, T, c, ys, D⟩, hN, hB⟩ := hloc m
    obtain ⟨h1, h2⟩ := D.ito_local hN hB
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h1
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact h2

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
