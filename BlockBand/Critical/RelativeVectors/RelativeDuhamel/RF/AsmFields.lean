module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.AsmDefs
public import BlockBand.Critical.RelativeVectors.AbstractFlow.Covariance

/-!
# The pathwise and law fields of the reference-flow witness

* `refM_self`, `refXi_self`: `𝓜_{s,s} = 1` and `Ξ_{s,s} = 0` (since `√(1 - 1) = 0`, or `N = 0`).
* `refM_contracts`: the contraction of the realization, unchanged by the phase conjugation.
* `phL_mul_conjTranspose`: `(P⁻¹ √(1 - KKᴴ))(P⁻¹ √(1 - KKᴴ))ᴴ = 1 - 𝓜𝓜ᴴ` for every sample (the
  realization contracts at rate `e^{−b₀N(u−s)/(2ℓ)} < 1` when `s < u`, `N > 0`).
* `refM_phase_covariant`: the torus shift `θ ↦ θ + α` preserves `auxLaw` and maps
  `(𝓜, Ξ)` to `(P_α⁻¹ 𝓜 P_α, P_α⁻¹ Ξ)` (`symPair_shift`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.ReferenceFlow
open BlockBand.Palm.MomentFlow (pathSigma)
open BlockBand.Palm.RelativeLocalization.StochasticBridge

variable {N r : ℕ}

/-!
## `initial`
-/

/-- `𝓜_{s,s} = 1`. -/
theorem refM_self (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N) (s : ℝ)
    (x : AuxSample N r) : refM F a c b₀ ℓ ω s s x = 1 := by
  simp only [refM, rawKernel, ↓reduceIte, phK, labelPhaseMatrix_one]

/-- `P_α 0 = 0`. -/
theorem labelPhase_zero_array (α : Fin N → ℝ) : labelPhase α (0 : Fin N → Fin r → ℂ) = 0 := by
  funext i
  simp only [labelPhase, Pi.zero_apply, smul_zero]

/-- `Ξ_{s,s} = 0`. -/
theorem refXi_self (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N) (s : ℝ)
    (x : AuxSample N r) : refXi F a c b₀ ℓ ω s s x = 0 := by
  simp only [refXi, rawKernel, ↓reduceIte, phL, arrayMul_rowPhase, arrayMul_sqrtOneSub_one,
    labelPhase_zero_array]

/-!
## `contraction`
-/

/-- **Contraction of `𝓜`**: `‖𝓜_{s,u} v‖₂ ≤ e^{−b₀N(u−s)/(2ℓ)} ‖v‖₂` for `a ≤ s ≤ u ≤ c`, every
path and every auxiliary sample. -/
theorem refM_contracts {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a < c)
    (b₀ : ℝ) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c) (ω : FlowSample N)
    (x : AuxSample N r) (v : Fin N → ℂ) :
    l2Norm (refM F a c b₀ ℓ ω s u x *ᵥ v) ≤ Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) * l2Norm v :=
  l2Norm_labelPhaseMatrix_mulVec_le (rawKernel_contracts hF hac b₀ ℓ has hsu huc ω x.1.1) v

/-!
## `covariance`
-/

/-- `√(1 - KKᴴ) √(1 - KKᴴ)ᴴ = 1 - KKᴴ` for `K = rawKernel … s u ω t`, `a ≤ s ≤ u ≤ c`. -/
theorem rawKernel_factor_cov {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a < c) {b₀ : ℝ} (hb₀ : 0 < b₀) {ℓ : ℕ} (hℓ : 0 < ℓ) {s u : ℝ} (has : a ≤ s)
    (hsu : s ≤ u) (huc : u ≤ c) (ω : FlowSample N) (t : unitInterval) :
    sqrtOneSub (rawKernel F a c b₀ ℓ s u ω t * (rawKernel F a c b₀ ℓ s u ω t)ᴴ) *
        (sqrtOneSub (rawKernel F a c b₀ ℓ s u ω t * (rawKernel F a c b₀ ℓ s u ω t)ᴴ))ᴴ =
      1 - rawKernel F a c b₀ ℓ s u ω t * (rawKernel F a c b₀ ℓ s u ω t)ᴴ := by
  by_cases h : s = u
  · simp only [rawKernel, h, ↓reduceIte]
    exact sqrtOneSub_one_mul
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact matrix_subsingleton_zero hN _ _
  have hq1 : Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) < 1 := by
    have h1 : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have h3 : 0 < u - s := sub_pos.2 (lt_of_le_of_ne hsu h)
    rw [Real.exp_lt_one_iff, neg_lt_zero]
    positivity
  exact sqrtOneSub_mul_conjTranspose_of_contracts (Real.exp_pos _).le hq1
    (rawKernel_contracts hF hac b₀ ℓ has hsu huc ω t)

/-- `(P⁻¹ √(1 - KKᴴ))(P⁻¹ √(1 - KKᴴ))ᴴ = 1 - (P⁻¹KP)(P⁻¹KP)ᴴ` when
`√(1 - KKᴴ) √(1 - KKᴴ)ᴴ = 1 - KKᴴ`. -/
theorem phL_mul_conjTranspose {K : Matrix (Fin N) (Fin N) ℂ} (θ : Torus N)
    (h : sqrtOneSub (K * Kᴴ) * (sqrtOneSub (K * Kᴴ))ᴴ = 1 - K * Kᴴ) :
    phL K θ * (phL K θ)ᴴ = 1 - phK K θ * (phK K θ)ᴴ := by
  rw [phL, phK, rowPhase_mul_conjTranspose, neg_neg, h, labelPhaseMatrix_sub, labelPhaseMatrix_one,
    labelPhaseMatrix_mul_conjTranspose]

/-- **The reference covariance identity for the witness** (`RFCovarianceStatement` on
`Ωd = unitInterval × Torus N` with `M = P⁻¹KP`, `L = P⁻¹ √(1 - KKᴴ)`), for `a ≤ s ≤ u ≤ c` and
every path. -/
theorem refM_covariance {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a < c) {b₀ : ℝ} (hb₀ : 0 < b₀) {ℓ : ℕ} (hℓ : 0 < ℓ) {s u : ℝ} (has : a ≤ s)
    (hsu : s ≤ u) (huc : u ≤ c) (ω : FlowSample N)
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hh : Measurable h) (hC : ∃ C, ∀ M, |h M| ≤ C)
    (w : Fin N → Fin r → ℂ) :
    ∫ ω', (h (refM F a c b₀ ℓ ω s u ω') : ℂ) * Complex.exp (Complex.I *
        (∑ i, ∑ q, (star (w i q) * refXi F a c b₀ ℓ ω s u ω' i q).re : ℝ)) ∂auxLaw N r =
      ∫ ω', (h (refM F a c b₀ ℓ ω s u ω') * Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
        (star (fun i => w i q) ⬝ᵥ ((1 - refM F a c b₀ ℓ ω s u ω' *
          (refM F a c b₀ ℓ ω s u ω')ᴴ) *ᵥ fun i => w i q)).re) : ℂ) ∂auxLaw N r := by
  set M : unitInterval × Torus N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => phK (rawKernel F a c b₀ ℓ s u ω y.1) y.2 with hMdef
  set L : unitInterval × Torus N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => phL (rawKernel F a c b₀ ℓ s u ω y.1) y.2 with hLdef
  have hK : Measurable fun y : unitInterval × Torus N => rawKernel F a c b₀ ℓ s u ω y.1 :=
    (measurable_rawKernel_left F a c b₀ ℓ s u ω).comp measurable_fst
  have hM : Measurable M := by
    have h' := measurable_phK.comp (hK.prodMk measurable_snd)
    exact h'
  have hL : Measurable L := by
    have h' := measurable_phL.comp (hK.prodMk measurable_snd)
    exact h'
  have hLL : ∀ᵐ y ∂((volume : Measure unitInterval).prod (torusHaar N)),
      L y * (L y)ᴴ = 1 - M y * (M y)ᴴ :=
    Eventually.of_forall fun y => phL_mul_conjTranspose y.2
      (rawKernel_factor_cov hF hac hb₀ hℓ has hsu huc ω y.1)
  exact AbstractFlow.rfCovariance_holds N r (unitInterval × Torus N)
    ((volume : Measure unitInterval).prod (torusHaar N)) M L hM hL hLL h hh hC w

/-!
## `phase_covariant`
-/

/-- `Ξ` in the `symNoise` form: `Ξ((t, θ), G) = P_θ'⁻¹ (√(1 - KKᴴ) G)`. -/
theorem refXi_eq_symNoise (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N)
    (s u : ℝ) (x : AuxSample N r) :
    refXi F a c b₀ ℓ ω s u x = symNoise (fun t : unitInterval => arrayMul
      (sqrtOneSub (rawKernel F a c b₀ ℓ s u ω t * (rawKernel F a c b₀ ℓ s u ω t)ᴴ)) x.2) x.1 := by
  rw [refXi, phL, arrayMul_rowPhase]
  rfl

/-- **Phase covariance of the witness.** For every `α`, the law of
`(P_α⁻¹ 𝓜_{s,u} P_α, P_α⁻¹ Ξ_{s,u})` under `auxLaw` is the law of `(𝓜_{s,u}, Ξ_{s,u})` (every
`s, u` and every path): the torus shift `θ ↦ θ + α` preserves `auxLaw`. -/
theorem refM_phase_covariant (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ)
    (ω : FlowSample N) (s u : ℝ) (α : Fin N → ℝ) :
    (auxLaw N r).map (fun ω' => (labelPhaseMatrix α (refM F a c b₀ ℓ ω s u ω'),
        labelPhase (fun i => -α i) (refXi F a c b₀ ℓ ω s u ω'))) =
      (auxLaw N r).map (fun ω' => (refM F a c b₀ ℓ ω s u ω', refXi F a c b₀ ℓ ω s u ω')) := by
  set T : AuxSample N r → AuxSample N r := Prod.map (Prod.map id (torusShift α)) id with hTdef
  have hT : MeasurePreserving T (auxLaw N r) (auxLaw N r) :=
    ((MeasurePreserving.id (volume : Measure unitInterval)).prod
      (measurePreserving_torusShift α)).prod (MeasurePreserving.id (matCircularLaw N r))
  have hF : Measurable fun ω' : AuxSample N r =>
      (refM F a c b₀ ℓ ω s u ω', refXi F a c b₀ ℓ ω s u ω') :=
    (measurable_refM F a c b₀ ℓ ω s u).prodMk (measurable_refXi F a c b₀ ℓ ω s u)
  have hpt : ∀ x : AuxSample N r, (labelPhaseMatrix α (refM F a c b₀ ℓ ω s u x),
      labelPhase (fun i => -α i) (refXi F a c b₀ ℓ ω s u x)) =
      (refM F a c b₀ ℓ ω s u (T x), refXi F a c b₀ ℓ ω s u (T x)) := by
    intro x
    have h := symPair_shift (rawKernel F a c b₀ ℓ s u ω) (fun t : unitInterval => arrayMul
      (sqrtOneSub (rawKernel F a c b₀ ℓ s u ω t * (rawKernel F a c b₀ ℓ s u ω t)ᴴ)) x.2) α x.1
    rw [refXi_eq_symNoise, refXi_eq_symNoise]
    exact h
  have e : (fun ω' : AuxSample N r => (labelPhaseMatrix α (refM F a c b₀ ℓ ω s u ω'),
      labelPhase (fun i => -α i) (refXi F a c b₀ ℓ ω s u ω'))) =
      (fun ω' => (refM F a c b₀ ℓ ω s u ω', refXi F a c b₀ ℓ ω s u ω')) ∘ T :=
    funext hpt
  rw [e, ← Measure.map_map hF hT.measurable, hT.map_eq]

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
