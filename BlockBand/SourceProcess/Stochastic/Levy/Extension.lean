module
public import BlockBand.SourceProcess.Stochastic.Levy.Wiener
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Tools for the weak-solution representation of martingale-problem solutions

Inputs for representing a solution `Y` of the `(b, σσᵀ)` martingale problem as a weak SDE
solution on the Wiener extension `(Ω × C(ℝ≥0,ℝ)^m, 𝓖 ⊗ σ(B'), Q ⊗ Wiener)`:

* `martingale_mul_lift`: for martingales `N` of the first factor and `B` of the second, the
  product `N(x₁) B(x₂)` is a martingale of the product filtration (zero cross bracket between
  lifted martingales and the independent Brownian motion `B'`).
* `IsMPSolutionOn.lift_fst`: martingale-problem solutions lift to product extensions (same
  coefficients, same domain), with `extB` an independent Brownian motion
  (`isFiltrationBrownian_extension`).
* `IsL2IntegratorVec.isLevyMartingale`, `IsL2IntegratorVec.isFiltrationBrownian`: **Lévy in
  integrator form**: a progressive `d`-vector integrator with identity bracket densities and
  `N_0 = 0` a.s. is a Brownian motion. This is the step that identifies
  `W = ∫ σ⁺(Y) dN + ∫ (I - σ⁺σ)(Y) dB'` once its bracket density is shown to be `I`.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

universe u v

variable {Ω : Type u} {W : Type v} [mΩ : MeasurableSpace Ω] [mW : MeasurableSpace W]
  {𝓖 : Filtration ℝ≥0 mΩ} {𝓕 : Filtration ℝ≥0 mW}
  {Q : Measure Ω} [IsProbabilityMeasure Q] {ν : Measure W} [IsProbabilityMeasure ν]

/-- **Products of martingales of independent factors are martingales.** -/
theorem martingale_mul_lift {N : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → W → ℝ} (hN : Martingale N 𝓖 Q)
    (hB : Martingale B 𝓕 ν) :
    Martingale (fun t (x : Ω × W) => N t x.1 * B t x.2) (prodFiltration 𝓖 𝓕) (Q.prod ν) := by
  have hint : ∀ t, Integrable (fun x : Ω × W => N t x.1 * B t x.2) (Q.prod ν) := fun t =>
    (hN.integrable t).mul_prod (hB.integrable t)
  refine martingale_of_setIntegral_eq (fun t => ((hN.1 t).comp_measurable
    (measurable_fst_prodFiltration t)).mul ((hB.1 t).comp_measurable
      (measurable_snd_prodFiltration t))) hint fun s t hst S hS => ?_
  have h0 := setIntegral_eq_zero_of_rect (P := Q.prod ν)
    (D := fun x => N t x.1 * B t x.2 - N s x.1 * B s x.2) ((hint t).sub (hint s))
    (fun A C hA hC => ?_) hS
  · rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at h0
    linarith
  · rw [integral_sub (hint t).integrableOn (hint s).integrableOn,
      setIntegral_prod_mul (μ := Q) (ν := ν) (L := ℝ) (N t) (B t) A C,
      setIntegral_prod_mul (μ := Q) (ν := ν) (L := ℝ) (N s) (B s) A C,
      hN.setIntegral_eq hst hA, hB.setIntegral_eq hst hC, sub_self]

/-- **Martingale-problem solutions lift to product extensions.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsMPSolutionOn.lift_fst {d : ℕ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U : Set (Fin d → ℝ)}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hY : IsMPSolutionOn Q 𝓖 b a U Y) :
    IsMPSolutionOn (Q.prod ν) (prodFiltration 𝓖 𝓕) b a U (fun t x => Y t x.1) := by
  have hmp := measurePreserving_fst (μ := Q) (ν := ν)
  refine ⟨fun t => (hY.adapted t).comp_measurable (measurable_fst_prodFiltration t),
    hmp.quasiMeasurePreserving.ae hY.continuous, fun W' hW i => ?_, fun W' hW i j => ?_⟩
  · obtain ⟨N, hN, hNe⟩ := hY.drift W' hW i
    exact ⟨_, martingale_lift_fst hN, fun t => hmp.quasiMeasurePreserving.ae_eq_comp (hNe t)⟩
  · obtain ⟨N, hN, hNe⟩ := hY.bracket W' hW i j
    exact ⟨_, martingale_lift_fst hN, fun t => hmp.quasiMeasurePreserving.ae_eq_comp (hNe t)⟩

omit [IsProbabilityMeasure Q] in
/-- **Lévy in integrator form.** A progressive vector integrator with identity bracket
densities and `N_0 = 0` a.s. satisfies the hypotheses of Lévy's characterization. -/
theorem _root_.BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2IntegratorVec.isLevyMartingale {d : ℕ} {N : Fin d → ℝ≥0 → Ω → ℝ}
    {a : Fin d → Fin d → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓖 N a)
    (ha : ∀ i j t ω, a i j t ω = if i = j then 1 else 0)
    (hprog : IsStronglyProgressive 𝓖 fun t ω i => N i t ω) (h0 : ∀ᵐ ω ∂Q, ∀ i, N i 0 ω = 0) :
    IsLevyMartingale Q 𝓖 fun t ω i => N i t ω := by
  refine ⟨hprog, ?_, ?_, fun i => (h.coord i).martingale, fun i j => ?_⟩
  · filter_upwards [ae_all_iff.2 fun i => (h.coord i).continuous] with ω hω
    exact continuous_pi hω
  · filter_upwards [h0] with ω hω
    funext i; exact hω i
  · obtain ⟨K, hK, hKN⟩ := h.cross i j
    refine ⟨K, hK, fun t => (hKN t).mono fun ω hω => ?_⟩
    rw [hω]
    simp only [ha]
    split_ifs <;> simp

/-- **Lévy in integrator form, conclusion.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2IntegratorVec.isFiltrationBrownian {d : ℕ} {N : Fin d → ℝ≥0 → Ω → ℝ}
    {a : Fin d → Fin d → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓖 N a)
    (ha : ∀ i j t ω, a i j t ω = if i = j then 1 else 0)
    (hprog : IsStronglyProgressive 𝓖 fun t ω i => N i t ω) (h0 : ∀ᵐ ω ∂Q, ∀ i, N i 0 ω = 0) :
    IsFiltrationBrownian Q 𝓖 fun t ω i => N i t ω :=
  (h.isLevyMartingale ha hprog h0).isFiltrationBrownian

end BlockBand.SourceProcess.Stochastic.Levy
