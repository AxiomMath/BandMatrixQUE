module
public import BlockBand.SourceProcess.Stochastic.Levy.Extension
public import BlockBand.SourceProcess.Stochastic.Levy.BrownianIntegrator
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The joint integrator `(N, B')` on the Wiener extension

Given a vector integrator `N` (`IsL2IntegratorVec Q 𝓖 N a`, index `ι`) on `(Ω, 𝓖, Q)`, the
family `(N ∘ fst, B')` indexed by `ι ⊕ Fin m` is a vector integrator on the Wiener extension
`(Ω × C(ℝ≥0,ℝ)^m, 𝓖 ⊗ σ(B'), Q ⊗ Wiener)` with block-diagonal bracket densities
`diag(a, I_m)` (`IsL2IntegratorVec.jointExtension`). The off-diagonal cross brackets vanish
because products of martingales of the two independent factors are martingales
(`martingale_mul_lift`). This is the integrator for
`W = ∫ σ⁺(Y) dN + ∫ (I - σ⁺σ)(Y) dB'` in the general vector stochastic integral.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]

/-- The joint process `(N ∘ fst, B')`. -/
def jointN (N : ι → ℝ≥0 → Ω → ℝ) (m : ℕ) : ι ⊕ Fin m → ℝ≥0 → Ω × WienerSpace m → ℝ
  | .inl i => fun t x => N i t x.1
  | .inr k => fun t x => wienerB m t x.2 k

/-- The block-diagonal bracket densities `diag(a ∘ fst, I_m)`. -/
def jointA (a : ι → ι → ℝ≥0 → Ω → ℝ) (m : ℕ) :
    ι ⊕ Fin m → ι ⊕ Fin m → ℝ≥0 → Ω × WienerSpace m → ℝ
  | .inl i, .inl j => fun t x => a i j t x.1
  | .inr k, .inr l => fun _ _ => if k = l then 1 else 0
  | .inl _, .inr _ => fun _ _ => 0
  | .inr _, .inl _ => fun _ _ => 0

variable {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- Cross martingale between a factor martingale modification and the Wiener coordinate. -/
theorem cross_fst_wiener {X : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X) (m : ℕ)
    (k : Fin m) : ∃ K : ℝ≥0 → Ω × WienerSpace m → ℝ, Martingale K (extFiltration 𝓖 m)
      (extMeasure Q m) ∧ ∀ t, K t =ᵐ[extMeasure Q m] fun x => X t x.1 * wienerB m t x.2 k := by
  obtain ⟨M, hM, hMX⟩ := hX
  refine ⟨_, martingale_mul_lift hM ((isFiltrationBrownian_wienerB m).martingale_coord k),
    fun t => ?_⟩
  filter_upwards [(measurePreserving_fst (μ := Q)
    (ν := commonWienerLaw (Fin m))).quasiMeasurePreserving.ae_eq_comp (hMX t)] with x hx
  simp only [Function.comp_apply] at hx
  simp only [hx]

/-- **The joint integrator on the Wiener extension.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2IntegratorVec.jointExtension
    {N : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓖 N a) (m : ℕ) :
    IsL2IntegratorVec (extMeasure Q m) (extFiltration 𝓖 m) (jointN N m) (jointA a m) := by
  have hB := (isFiltrationBrownian_extension (Q := Q) (𝓖 := 𝓖) m).isL2IntegratorVec
  have hzero : ∀ t : ℝ≥0, ∫ r in Ioc (0 : ℝ) t, (0 : ℝ) = 0 := fun t => by simp
  refine ⟨fun i => ?_, fun t x v => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rcases i with i | k
    · exact (h.coord i).lift_fst
    · exact hB.coord k
  · simp only [Fintype.sum_sum_type, jointA]
    simp only [mul_zero, Finset.sum_const_zero, add_zero, zero_add]
    exact add_nonneg (h.psd t x.1 fun i => v (.inl i)) (hB.psd t x fun k => v (.inr k))
  · rcases i with i | k <;> rcases j with j | l
    · exact (h.measurable i j).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    all_goals exact measurable_const
  · rcases i with i | k <;> rcases j with j | l
    · exact (measurePreserving_fst (μ := Q)
        (ν := commonWienerLaw (Fin m))).quasiMeasurePreserving.ae (h.integrable i j)
    all_goals exact ae_of_all _ fun _ _ => integrableOn_const (by simp)
  · rcases i with i | k <;> rcases j with j | l
    · obtain ⟨K, hK, hKN⟩ := h.cross i j
      exact ⟨_, martingale_lift_fst hK, fun t => (measurePreserving_fst (μ := Q)
        (ν := commonWienerLaw (Fin m))).quasiMeasurePreserving.ae_eq_comp (hKN t)⟩
    · obtain ⟨K, hK, hKN⟩ := cross_fst_wiener (h.coord i).martingale m l
      exact ⟨K, hK, fun t => (hKN t).mono fun x hx => by simp [hx, jointN, jointA, hzero]⟩
    · obtain ⟨K, hK, hKN⟩ := cross_fst_wiener (h.coord j).martingale m k
      exact ⟨K, hK, fun t => (hKN t).mono fun x hx => by
        simp [hx, jointN, jointA, hzero, mul_comm]⟩
    · exact hB.cross k l

end BlockBand.SourceProcess.Stochastic.Levy
