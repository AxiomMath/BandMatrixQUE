module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Bracket
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The stochastic integral against a continuous `L²` integrator: summary

Setting: an arbitrary measurable space `(Ω, m₀)` with a finite measure `Q`, an arbitrary raw
filtration `𝓖 : Filtration ℝ≥0 m₀` (no completeness or usual conditions), and
`h : IsL2Integrator Q 𝓖 N α` (`N` a.s. continuous, `L²`, with a martingale modification;
`N² - ∫_0^· α` with a martingale modification; `α ≥ 0` jointly measurable, a.s. locally
integrable). Horizon `T`; integrands `H ∈ PredL2 𝓖 ν_T`, the predictable classes in
`L²(ν_T)`, `ν_T = α ds ⊗ Q` on `(0,T] × Ω`.

* `contIntegral_elem`: for a simple integrand the continuous integral is the elementary sum
  `∑ c_r 1_{A_r} (N_{s_r ∨ (t ∧ t_r)} - N_{s_r})`, a.s. at every time.
* `stochasticIntegral_exists`: the process `Z_t = ∫_0^t H dN` has a.s. continuous paths, is in
  `L²` at every time, has a martingale modification, satisfies `Z_T = stochIntegral h T H`
  a.s., `E Z_T² = ∫ H² dν_T`, is constant after `T`, and `Z² - ∫_0^{·∧T} H² α ds` has a
  martingale modification.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0)

/-- **Consistency with the elementary integral.** For a simple integrand `x`, the continuous
integral of `integrandLin h T x` is `elemProc N x`, a.s. at every time. -/
theorem contIntegral_elem (x : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    h.contIntegral T (h.integrandLin T x) t =ᵐ[Q] elemProc N x t := by
  set H := h.integrandLin T x
  have hm : AEStronglyMeasurable (fun ω => h.contIntegral T H t ω - elemProc N x t ω) Q :=
    (h.memLp_contIntegral T H t).aestronglyMeasurable.sub
      (elemProc_memLp h.memLp x t).aestronglyMeasurable
  have hb : ∀ k, eLpNorm (fun ω => h.contIntegral T H t ω - elemProc N x t ω) 2 Q ≤
      ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) + ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k) := by
    intro k
    have e1 : eLpNorm (fun ω => h.contIntegral T H t ω - h.approxProc T H k t ω) 2 Q ≤
        ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) := by
      have : (fun ω => h.contIntegral T H t ω - h.approxProc T H k t ω) =
          -(fun ω => h.approxProc T H k t ω - h.contIntegral T H t ω) := by funext ω; simp
      rw [this, eLpNorm_neg]; exact h.eLpNorm_approxProc_sub_contIntegral_le T H k t
    have e2 : eLpNorm (fun ω => h.approxProc T H k t ω - elemProc N x t ω) 2 Q ≤
        ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k) := by
      have : (fun ω => h.approxProc T H k t ω - elemProc N x t ω) =
          elemProc N (h.approx T H k - x) t := by
        funext ω; simp [approxProc, map_sub]
      rw [this, one_mul]
      refine (h.eLpNorm_elemProc_le T _ t).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [map_sub]; exact (h.approx_spec T H k).le
    calc _ = eLpNorm ((fun ω => h.contIntegral T H t ω - h.approxProc T H k t ω) +
          (fun ω => h.approxProc T H k t ω - elemProc N x t ω)) 2 Q := by
          congr 1; funext ω; simp
      _ ≤ _ := eLpNorm_add_le one_le_two
      _ ≤ _ := add_le_add e1 e2
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) +
      ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k)) atTop (𝓝 0) := by
    simpa using (tendsto_ofReal_geom 2).add (tendsto_ofReal_geom 1)
  have h0 := le_antisymm (ge_of_tendsto' ht hb) zero_le
  rw [eLpNorm_eq_zero_iff two_ne_zero] at h0
  filter_upwards [h0] with ω hω
  simpa [sub_eq_zero] using hω

/-- **The continuous stochastic integral and its bracket.** -/
theorem stochasticIntegral_exists (H : PredL2 𝓖 (bracketMeasure Q α T)) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂Q, Continuous fun t => Z t ω) ∧
      (∀ t, MemLp (Z t) 2 Q) ∧
      (∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] Z t) ∧
      Z T =ᵐ[Q] h.stochIntegral T H ∧
      ∫ ω, Z T ω ^ 2 ∂Q =
        ∫ p, ((H : Lp ℝ 2 (bracketMeasure Q α T)) p) ^ 2 ∂bracketMeasure Q α T ∧
      (∀ t, T ≤ t → Z t = Z T) ∧
      (∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] fun ω => Z t ω ^ 2 -
        ∫ r in Ioc (0 : ℝ) (min t T),
          ((H : Lp ℝ 2 (bracketMeasure Q α T)) (r, ω)) ^ 2 * α r.toNNReal ω) := by
  obtain ⟨hc, hL, hM, hT, hconst⟩ := h.contIntegral_spec T H
  refine ⟨h.contIntegral T H, hc, hL, hM, hT, ?_, hconst, h.bracket_martingale T H⟩
  rw [← h.integral_sq_stochIntegral T H]
  exact integral_congr_ae (hT.mono fun ω hω => by simp only [hω])

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
