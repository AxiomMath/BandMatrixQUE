module

public import BlockBand.SourceProcess.FullSourceGenerator.Tight
public import BlockBand.SourceProcess.FullSourceGenerator.GenFixed
public import BlockBand.SourceProcess.FullSourceStops.Main

/-!
# Path inputs of the tested increment: moments, real parts, the `K`-free variance

Along the growth path (fixed `W`):
* `lintegral_polyValue_pow_le`: uniform moments `E|Ψ(Z_j)|ⁿ ≤ C` of an ordinary trace polynomial
  on `εW ≤ j ≤ TW`, all tag births (`FullSourceStops.lintegral_wordLoad_pow_le`; the four input
  hypotheses `MatchedTraces`, `GaussianAbsorption`, `GaussianLpGradient`, `ScalarRecursion`);
* `conjPoly`, `rePart`, `imPart`: `Φ̄ = rename conjWord (map conj Φ)` and the real/imaginary
  parts, ordinary, with `polyValue (rePart Φ) = Re Φ(Z_j)`, `polyValue (imPart Φ) = Im Φ(Z_j)`
  pointwise (`wordValue_conjWord`);
* `lintegral_sq_le_carre`: the `K`-free variance step, `E|1_A ΔR|² ≤ E‖carreErr‖ + W⁻¹E|Γ(R)|`
  for a real-valued `R` (the integrand of `EarlySummed`'s second clause).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal ComplexConjugate

variable {W nT nI : ℕ}

/-- **Uniform moments of ordinary trace polynomials** on `εW ≤ j ≤ TW`. -/
theorem lintegral_polyValue_pow_le (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) {ε T : ℝ}
    (hε : 0 < ε) (hεT : ε < T) {Ψ : TracePoly nT nI} (hΨ : Ψ ∈ ordPoly nT nI) (n : ℕ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ (k : Fin nT → ℕ) (j : ℕ), ε * W ≤ j →
      (j : ℝ) ≤ T * W → ∫⁻ ω, ‖polyValue b E k q W j ω Ψ‖ₑ ^ n ∂growthPathLaw W b ≤
        ENNReal.ofReal C := by
  obtain ⟨hκ, hEb⟩ := mem_bulk_self hE1 hE2
  obtain ⟨C', W₀, hC'top, hC'⟩ := lintegral_wordLoad_pow_le hMT hGA hLp hSR b hb0 hb _ hκ nT nI
    q hq ε T hε hεT (polyExp Ψ * n + 1) (Nat.le_add_left 1 _)
  have hc0 : 0 ≤ polyConst Ψ ^ n := pow_nonneg (polyConst_nonneg Ψ) n
  refine ⟨polyConst Ψ ^ n * C'.toReal, max W₀ 1, mul_nonneg hc0 ENNReal.toReal_nonneg,
    fun W hW k j hj hjT => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hpt : ∀ᵐ ω ∂growthPathLaw W b, ‖polyValue b E k q W j ω Ψ‖ₑ ^ n ≤
      ENNReal.ofReal (polyConst Ψ ^ n) *
        ENNReal.ofReal (wordLoad b E k q W j ω) ^ (polyExp Ψ * n + 1) := by
    filter_upwards [ae_norm_polyValue_ord_le (nT := nT) hb hE1 hE2 hW1 q hq,
      one_le_wordLoad_ae (nT := nT) hb hE1 hE2 hW1 q hq] with ω h1 h2
    have hL1 := h2 j k
    have hX := h1 j k Ψ hΨ
    have h4 : ‖polyValue b E k q W j ω Ψ‖ ^ n ≤
        polyConst Ψ ^ n * wordLoad b E k q W j ω ^ (polyExp Ψ * n + 1) := by
      have := pow_le_pow_left₀ (norm_nonneg _) hX n
      rw [mul_pow, ← pow_mul] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hc0)
      exact pow_le_pow_right₀ hL1 (Nat.le_succ _)
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (by linarith),
      ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal h4
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hc0,
    ENNReal.ofReal_toReal hC'top]
  exact mul_le_mul' le_rfl (hC' W (le_trans (le_max_left _ _) hW) E hEb k j hj hjT)

/-! ### Real and imaginary parts -/

/-- The conjugate polynomial `Φ̄`: conjugate coefficients, conjugate words. -/
def conjPoly (Φ : TracePoly nT nI) : TracePoly nT nI := rename conjWord (map (starRingEnd ℂ) Φ)

/-- `Re Φ = (Φ + Φ̄)/2`. -/
def rePart (Φ : TracePoly nT nI) : TracePoly nT nI := C (1 / 2 : ℂ) * (Φ + conjPoly Φ)

/-- `Im Φ = -(i/2)(Φ - Φ̄)`. -/
def imPart (Φ : TracePoly nT nI) : TracePoly nT nI := C (-(Complex.I / 2)) * (Φ - conjPoly Φ)

theorem conjPoly_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) :
    conjPoly Φ ∈ ordPoly nT nI := by
  refine mem_supported.mpr fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hw)
  exact conjWord_ordinary (hΦ v (vars_map _ _ hv))

theorem rePart_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) : rePart Φ ∈ ordPoly nT nI :=
  Subalgebra.mul_mem _ (C_mem_ordPoly _)
    (Subalgebra.add_mem _ (mem_ordPoly_of_isOrdinaryPoly hΦ) (conjPoly_mem hΦ))

theorem imPart_mem {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ) : imPart Φ ∈ ordPoly nT nI :=
  Subalgebra.mul_mem _ (C_mem_ordPoly _)
    (Subalgebra.sub_mem _ (mem_ordPoly_of_isOrdinaryPoly hΦ) (conjPoly_mem hΦ))

theorem isOrdinaryPoly_of_mem {Ψ : TracePoly nT nI} (h : Ψ ∈ ordPoly nT nI) : IsOrdinaryPoly Ψ :=
  fun _ hw => mem_supported.mp h hw

theorem polyValue_conjPoly (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) :
    polyValue b E k q W j ω (conjPoly Φ) = conj (polyValue b E k q W j ω Φ) := by
  simp only [polyValue, conjPoly, eval_rename, eval_map]
  rw [show conj (eval (wordValue b E k q W j ω) Φ) =
      (starRingEnd ℂ) (eval₂ (RingHom.id ℂ) (wordValue b E k q W j ω) Φ) from rfl,
    eval₂_comp_left]
  refine eval₂_congr _ _ _ fun {w} {c} hw hc => ?_
  have hwv : w ∈ Φ.vars := (mem_vars_iff_mem_support w).mpr ⟨c, mem_support_iff.mpr hc, hw⟩
  simp only [Function.comp_apply]
  exact wordValue_conjWord b E k q hq j ω (hΦ w hwv)

theorem polyValue_rePart (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) :
    polyValue b E k q W j ω (rePart Φ) = ((polyValue b E k q W j ω Φ).re : ℂ) := by
  have h := polyValue_conjPoly b E k q hq j ω hΦ
  simp only [polyValue] at h ⊢
  simp only [rePart, map_mul, map_add, eval_C, h, Complex.add_conj]
  push_cast; ring

theorem polyValue_imPart (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) :
    polyValue b E k q W j ω (imPart Φ) = ((polyValue b E k q W j ω Φ).im : ℂ) := by
  have h := polyValue_conjPoly b E k q hq j ω hΦ
  simp only [polyValue] at h ⊢
  simp only [imPart, map_mul, map_sub, eval_C, h, Complex.sub_conj]
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- `‖z‖² = (Re z)² + (Im z)²` for the stopped increments. -/
theorem enorm_sq_indicator_eq {Ω : Type*} (A : Set Ω) (f : Ω → ℂ) (ω : Ω) :
    ‖A.indicator f ω‖ₑ ^ 2 = ‖A.indicator (fun ω => ((f ω).re : ℂ)) ω‖ₑ ^ 2 +
      ‖A.indicator (fun ω => ((f ω).im : ℂ)) ω‖ₑ ^ 2 := by
  by_cases h : ω ∈ A
  · simp only [Set.indicator_of_mem h]
    rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, enorm_sq_eq_ofReal,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  · simp [Set.indicator_of_notMem h]

/-- **The `K`-free variance step**: for a real-valued increment,
`E|1_A Δ|² ≤ E‖1_A(E[1_A Δ²|m] - sP)‖ + s E|P|`. -/
theorem lintegral_sq_le_carre {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {A : Set Ω} (hA : MeasurableSet[m] A) {Δ P : Ω → ℂ}
    (hreal : ∀ ω, ((Δ ω).re : ℂ) = Δ ω) (hΔ : MemLp (A.indicator Δ) 2 μ)
    (hP : StronglyMeasurable[m0] P) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ ω, ‖A.indicator Δ ω‖ₑ ^ 2 ∂μ ≤
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator (fun ω => Δ ω ^ 2) | m] ω - (s : ℂ) * P ω) ω‖ₑ
        ∂μ + ENNReal.ofReal s * ∫⁻ ω, ‖P ω‖ₑ ∂μ := by
  set f : Ω → ℂ := A.indicator fun ω => Δ ω ^ 2
  have hf : ∀ ω, f ω = ((‖A.indicator Δ ω‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    by_cases h : ω ∈ A
    · simp only [f, Set.indicator_of_mem h]
      rw [← hreal ω, Complex.norm_real, Real.norm_eq_abs, sq_abs]; push_cast; ring
    · simp [f, Set.indicator_of_notMem h]
  have hfi : Integrable f μ := by
    have h2 := (memLp_two_iff_integrable_sq_norm hΔ.aestronglyMeasurable).mp hΔ
    refine (h2.ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun ω => (hf ω).symm)
  have hAf : A.indicator f = f := by
    funext ω; by_cases h : ω ∈ A <;> simp [f, h]
  have hce : μ[f | m] =ᵐ[μ] A.indicator (μ[f | m]) := by
    have := condExp_indicator (μ := μ) (m := m) hfi hA
    rwa [hAf] at this
  have hint : ∫ ω, f ω ∂μ = ∫ ω, A.indicator (μ[f | m]) ω ∂μ := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    rw [← integral_condExp hm (f := f)]; exact integral_congr_ae hce
  have hlhs : ∫⁻ ω, ‖A.indicator Δ ω‖ₑ ^ 2 ∂μ = ‖∫ ω, f ω ∂μ‖ₑ := by
    rw [lintegral_enorm_sq_eq hΔ]
    simp_rw [hf]
    rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => by positivity)]
  rw [hlhs, hint]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ ω, ‖A.indicator (μ[f | m]) ω‖ₑ ≤
      ‖A.indicator (fun ω => μ[f | m] ω - (s : ℂ) * P ω) ω‖ₑ + ENNReal.ofReal s * ‖P ω‖ₑ := by
    intro ω
    by_cases h : ω ∈ A
    · simp only [Set.indicator_of_mem h]
      calc ‖μ[f | m] ω‖ₑ = ‖(μ[f | m] ω - (s : ℂ) * P ω) + (s : ℂ) * P ω‖ₑ := by ring_nf
        _ ≤ ‖μ[f | m] ω - (s : ℂ) * P ω‖ₑ + ‖(s : ℂ) * P ω‖ₑ := enorm_add_le _ _
        _ = _ := by
          rw [enorm_mul, ← ofReal_norm (s : ℂ), Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hs]
    · simp [Set.indicator_of_notMem h]
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_add_right' _ (hP.measurable.enorm.const_mul _).aemeasurable,
    lintegral_const_mul _ hP.measurable.enorm]

end BlockBand.SourceProcess.FullSourceGenerator
