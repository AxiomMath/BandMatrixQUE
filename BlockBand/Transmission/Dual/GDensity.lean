module

public import BlockBand.Transmission.Dual.GBayes
public import Mathlib.Probability.Martingale.Convergence

/-!
# The terminal density of a bounded martingale

`exists_isDensity`: a `P`-martingale `M` (time `ℝ≥0`, raw filtration) with `0 ≤ M_t ≤ K` a.s. has
a terminal density `g ≥ 0` with `M_t = E[g | 𝓖_t]` for **every** `t` (`IsDensity`). Proof: the
discrete martingale `M_n` is bounded, hence uniformly integrable, so it converges a.s. and in `L¹`
to `M_∞` with `M_n = E[M_∞ | 𝓖_n]` (Mathlib, `Martingale.ae_eq_condExp_limitProcess`); for real
`t ≤ n`, the tower property. `g = max(M_∞, 0)` (`= M_∞` a.s.). If `M_0 = 1` a.s., `tilt P g` is a
probability measure (`isProbabilityMeasure_tilt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {M : ℝ≥0 → Ω → ℝ}

/-- The discrete filtration `n ↦ 𝓖_n`. -/
def natFiltration (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
  ⟨fun n => 𝓖 n, fun _ _ h => 𝓖.mono (by exact_mod_cast h), fun n => 𝓖.le n⟩

/-- **The terminal density of a bounded martingale.** -/
theorem exists_isDensity (hM : Martingale M 𝓖 P) {K : ℝ}
    (hK : ∀ t, ∀ᵐ ω ∂P, 0 ≤ M t ω ∧ M t ω ≤ K) : ∃ g, IsDensity P 𝓖 M g := by
  set 𝓕 := natFiltration 𝓖
  set f : ℕ → Ω → ℝ := fun n => M n
  have hf : Martingale f 𝓕 P := ⟨fun n => hM.1 n, fun i j hij => hM.2 i j (by exact_mod_cast hij)⟩
  have hfm : ∀ n, AEStronglyMeasurable (f n) P := fun n =>
    ((hM.1 n).mono (𝓖.le n)).aestronglyMeasurable
  have hunif : UniformIntegrable f 1 P := by
    refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hfm fun ε _ => ⟨(max K 0 + 1).toNNReal,
      fun n => ?_⟩
    have h0 : {x | (max K 0 + 1).toNNReal ≤ ‖f n x‖₊}.indicator (f n) =ᵐ[P] 0 := by
      filter_upwards [hK n] with ω hω
      refine indicator_of_notMem (fun h => ?_) _
      have h' : max K 0 + 1 ≤ ‖f n ω‖ := by
        have := (Real.toNNReal_le_iff_le_coe).1 h; simpa using this
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1] at h'
      linarith [le_max_left K 0, hω.2]
    rw [eLpNorm_congr_ae h0, eLpNorm_zero]; exact zero_le
  set L := 𝓕.limitProcess f P
  have hLm : StronglyMeasurable L := Filtration.stronglyMeasurable_limit_process'
  have hce : ∀ n, f n =ᵐ[P] P[L | 𝓕 n] := hf.ae_eq_condExp_limitProcess hunif
  have hLi : Integrable L P := by
    obtain ⟨R, hR⟩ := hunif.2
    exact (Filtration.memLp_limitProcess_of_eLpNorm_bdd hfm hR).integrable le_rfl
  have hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω := by
    filter_upwards [hf.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hunif,
      ae_all_iff.2 fun n : ℕ => hK (n : ℝ≥0)] with ω hω hk
    exact ge_of_tendsto' hω fun n => (hk n).1
  set g : Ω → ℝ≥0 := fun ω => (L ω).toNNReal
  have hgL : (fun ω => (g ω : ℝ)) =ᵐ[P] L := by
    filter_upwards [hL0] with ω hω
    exact Real.coe_toNNReal _ hω
  refine ⟨g, ⟨hM, measurable_real_toNNReal.comp hLm.measurable,
    hLi.congr hgL.symm, fun t => ?_⟩⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, t ≤ n := ⟨⌈(t : ℝ)⌉₊, by
    rw [← NNReal.coe_le_coe]; push_cast; exact Nat.le_ceil _⟩
  have h1 : M t =ᵐ[P] P[M n | 𝓖 t] := (hM.2 t n hn).symm
  have h2 : P[M n | 𝓖 t] =ᵐ[P] P[P[L | 𝓖 n] | 𝓖 t] := condExp_congr_ae (hce n)
  have h3 : P[P[L | 𝓖 n] | 𝓖 t] =ᵐ[P] P[L | 𝓖 t] := condExp_condExp_of_le (𝓖.mono hn) (𝓖.le n)
  have h4 : P[L | 𝓖 t] =ᵐ[P] P[fun ω => (g ω : ℝ) | 𝓖 t] := condExp_congr_ae hgL.symm
  exact h1.trans (h2.trans (h3.trans h4))

/-- If moreover `M_0 = 1` a.s., the tilted measure is a probability measure. -/
theorem IsDensity.isProbabilityMeasure_tilt {g : Ω → ℝ≥0} (h : IsDensity P 𝓖 M g)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 1) : IsProbabilityMeasure (tilt P g) := by
  have := h.isFiniteMeasure
  refine ⟨?_⟩
  have e := h.setIntegral_tilt_eq (t := 0) (f := fun _ => (1 : ℝ)) stronglyMeasurable_const
    (C := 1) (Eventually.of_forall fun _ => by simp) MeasurableSet.univ
  have e1 : ∫ ω in univ, M 0 ω * 1 ∂P = 1 := by
    rw [setIntegral_univ, integral_congr_ae (g := fun _ => (1 : ℝ))
      (h0.mono fun ω hω => by simp [hω])]
    simp
  rw [e1, setIntegral_const, smul_eq_mul, mul_one] at e
  have : (tilt P g).real univ = 1 := by simpa using e
  rw [measureReal_def, ENNReal.toReal_eq_one_iff] at this
  exact this

end BlockBand.Transmission.Dual.G
