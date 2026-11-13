module

public import BlockBand.Native.ErdosRiabov.QV.Bracket
public import BlockBand.Native.ErdosRiabov.Prop.Bridge
public import BlockBand.Native.ErdosRiabov.VS.Tail
public import BlockBand.Native.ErdosRiabov.Flow.IntRules

/-!
# Quadratic variation: the propagated-martingale tail from a deterministic rate

An exponential tail bound for a propagated chain martingale whose bracket density is bounded by
a deterministic rate up to the stopping time.

* `qv_ringSlots_eq`: the slots `ringSlots 0 (zfam P.z σ α) s y` of the bracket of
  `VS.propagated_tail` are the resolvents `qvRes P s (ringMatrixFin p y) (σ j)` for `s ≤ 1`, so the
  bracket integrand of `VS.propagated_tail` is the chain bracket at `H = ringMatrixFin p y`
  (`= Evol.pathH p x s` for `y = vsNoise p s x`).
* `qv_int_rate`: integrability and the integration rules of `vsIntRules` for the rate
  `A L_s^{-γ} η_s⁻¹` on `(0, T]`, `T ≤ 1` (third rule for `γ > 0`, first for `γ = 0`).
* `qv_tail_of_rate`: if a.s., for every `s ∈ (0, T]` with `s ≤ τ`, the bracket density of
  `combMg 0 (zfam P.z σ) B K c` is `≤ A L_s^{-γ} η_s⁻¹`, then
  `P(∃ r ≤ T, r ≤ τ, λ ≤ |combMg r|) ≤ 4 exp(-λ²/(4y))`, `y = A · qvIntRule γ T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Chains (firstVar resSlots res)
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.CEH.Flow
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-!
## Identification of the slots
-/

theorem qv_ringSlots_eq {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im) {k : ℕ} {ι : Type*}
    (σ : Fin k → Bool) (α : ι) {s : ℝ} (hs : s ≤ 1) (y : Fin (ringDim p) → ℝ) :
    ringSlots 0 (Evol.zfam (ι := ι) P.z σ α) s y =
      fun j => qvRes P s (ringMatrixFin p y) (σ j) := by
  have hδ : 0 ≤ P.z.im / (2 * (semicircleM P.z).im) := by
    have := semicircleM_im_pos hz
    positivity
  funext j
  simp only [ringSlots, resSlots, res, zero_add, Evol.zfam]
  rw [← patZ_eq_vsPatternSpec P.z σ hs hδ j]
  rfl

theorem qv_combDir_eq {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im) {k : ℕ} {ι : Type*}
    [Fintype ι] (σ : Fin k → Bool) (B : ι → Fin k → RingMat p) (K : ι → RingMat p)
    (c : ι → ℝ → ℂ) {s : ℝ} (hs : s ≤ 1) (y : Fin (ringDim p) → ℝ) (X : RingMat p) :
    combDir 0 (Evol.zfam P.z σ) B K c s y X =
      ∑ α, c α s * Matrix.trace (K α * firstVar (B α)
        (fun j => qvRes P s (ringMatrixFin p y) (σ j)) X) := by
  rw [combDir_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [qv_ringSlots_eq hz σ α hs y]

/-!
## Integration of the rate
-/

/-- The integration rule for the rate `L_s^{-γ} η_s⁻¹` on `[0, T]`: `2/(γ c_m) L_T^{-γ}` for
`γ > 0`, `c_m⁻¹ log((C₀+1)N)` for `γ = 0`. -/
def qvIntRule (d : VSData) (P : PsiData (p.n * p.W)) (γ T : ℝ) : ℝ :=
  if γ = 0 then (imLower d.kappa d.C0)⁻¹ * Real.log ((d.C0 + 1) * (p.n * p.W : ℕ))
  else 2 / (γ * imLower d.kappa d.C0) * P.lEta T ^ (-γ)

section Rate

variable (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
include hPW hz

theorem qv_rate_continuousOn (γ : ℝ) :
    ContinuousOn (fun s => P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹) (Icc 0 1) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < vsHeight P.z s := fun s hs => vsHeight_pos hη hs.2
  have hL : ContinuousOn (fun s => P.lEta s) (Icc 0 1) := by
    unfold PsiData.lEta
    exact ((continuousOn_loc _ _).comp (continuous_vsHeight P.z).continuousOn
      (fun s hs => hpos s hs)).mul (continuous_vsHeight P.z).continuousOn
  have hLpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < P.lEta s := fun s hs =>
    P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη hs.2
  refine (hL.rpow_const fun s hs => Or.inl (hLpos s hs).ne').mul ?_
  exact ((continuous_vsHeight P.z).continuousOn).inv₀ fun s hs => (hpos s hs).ne'

theorem qv_rate_integrableOn (γ A : ℝ) {T : ℝ} (hT1 : T ≤ 1) :
    IntegrableOn (fun s => A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹) (Ioc 0 T) := by
  have h := (qv_rate_continuousOn d P hPW hz γ).integrableOn_Icc (μ := volume)
  have h2 : IntegrableOn (fun s => A * (P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹)) (Icc 0 1) :=
    h.const_mul A
  refine (h2.mono_set (fun s hs => ⟨hs.1.le, hs.2.trans hT1⟩)).congr_fun (fun s _ => ?_)
    measurableSet_Ioc
  ring

/-- **The integration rules for the rate.** For `0 ≤ T ≤ 1`, `A ≥ 0`, `γ ≥ 0`:
`∫_{(0,T]} A L_s^{-γ} η_s⁻¹ ds ≤ A · qvIntRule γ T`.
-/
theorem qv_int_rate {γ A T : ℝ} (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∫ s in Ioc 0 T, A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ ≤ A * qvIntRule d P γ T := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hrules := fun (γ' : ℝ) (hγ' : 0 < γ') => vsIntRules (N := p.n * p.W) (W := p.W) hN
    p.W_pos d.delta0_pos.le d.kappa_pos (by linarith [d.C0_ge_one]) hz hT0 hT1 hγ'
  have e : ∫ s in Ioc 0 T, A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ =
      A * ∫ s in (0 : ℝ)..T, P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ := by
    rw [intervalIntegral.integral_of_le hT0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hA
  unfold qvIntRule
  by_cases h0 : γ = 0
  · rw [qv_ite_pos h0]
    subst h0
    have h := (hrules 1 one_pos).1
    refine le_trans (le_of_eq ?_) h
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp
  · rw [qv_ite_neg h0]
    have h := (hrules γ (lt_of_le_of_ne hγ (Ne.symm h0))).2.2
    unfold PsiData.lEta
    rw [hPW]
    exact h

end Rate

/-!
## The tail from a rate
-/

/-- **The martingale tail bound.** Let `σ` be a pattern, `(B, K)` chain data, `c_α` `C²`
coefficients, `τ` a `driverAugmented` stopping time and `T ≤ 1`.
If a.s., for every `s ∈ (0, T]` with `s ≤ τ`, the
bracket density of the propagated martingale is at most the rate `A L_s^{-γ} η_s⁻¹`
(`A, γ ≥ 0`), then with `y = A · qvIntRule γ T > 0`, for `λ ≥ 0`:
`P(∃ r ≤ T, r ≤ τ, λ ≤ |combMg 0 (zfam P.z σ) B K c r|) ≤ 4 exp(-λ²/(4y))`.
-/
theorem qv_tail_of_rate (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
    {P : PsiData (p.n * p.W)} (hPW : P.W = p.W)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {k : ℕ} {ι : Type*} [Fintype ι]
    (σ : Fin k → Bool) (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ)
    (hc : ∀ α, ContDiff ℝ 2 (c α)) {τ : RingSample p → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ) (T : ℝ≥0)
    (hT1 : (T : ℝ) ≤ 1) {A γ : ℝ} (hA : 0 ≤ A) (hγ : 0 ≤ γ)
    (hy : 0 < A * qvIntRule d P γ T)
    (hb : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x →
        ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b *
          ‖combDir 0 (Evol.zfam P.z σ) B K c s (vsNoise p s.toNNReal x) (single a b 1)‖ ^ 2 ≤
        A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) B K c t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (A * qvIntRule d P γ T))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hη := hz.im_pos hN
  refine propagated_tail μ Matrix.isHermitian_zero (Evol.zfam_contDiff P.z σ)
    (Evol.zfam_im_ne_zero hη σ) B K c hc hτ T hy ?_ hlam
  filter_upwards [hb] with x hx t htT htτ
  have hGi := qv_rate_integrableOn d P hPW hz γ A (T := T) hT1
  have hint := qv_int_rate d P hPW hz hγ hA T.2 hT1
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := fun s hs => ⟨hs.1, hs.2.trans (by exact_mod_cast htT)⟩
  have hG0 : ∀ s ∈ Ioc (0 : ℝ) T, 0 ≤ A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ := by
    intro s hs
    have hpos := vsHeight_pos hη (hs.2.trans hT1)
    have := Real.rpow_nonneg (P.lEta_pos hN (by rw [hPW]; exact p.W_pos) hη
      (hs.2.trans hT1)).le (-γ)
    positivity
  have hle : ∀ s ∈ Ioc (0 : ℝ) t, ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b *
      ‖combDir 0 (Evol.zfam P.z σ) B K c (s.toNNReal : ℝ) (vsNoise p s.toNNReal x)
        (single a b 1)‖ ^ 2 ≤ A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ := by
    intro s hs
    have hs0 : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1.le
    rw [hs0]
    refine hx s (hsub hs) ?_
    refine le_trans ?_ htτ
    exact_mod_cast (Real.toNNReal_le_iff_le_coe.mpr hs.2)
  calc ∫ s in Ioc (0 : ℝ) t, ∑ a, ∑ b, shortRingProfile p.b p.n p.W a b *
        ‖combDir 0 (Evol.zfam P.z σ) B K c (s.toNNReal : ℝ) (vsNoise p s.toNNReal x)
          (single a b 1)‖ ^ 2
      ≤ ∫ s in Ioc (0 : ℝ) t, A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ := by
        refine integral_mono_of_nonneg ?_ (hGi.mono_set hsub) ?_
        · exact Filter.Eventually.of_forall fun s => Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun b _ => mul_nonneg
              (Adapters.ErdosRiabov.shortRingProfile_nonneg p.b_pos p.b_lt_half p.n p.W a b)
              (sq_nonneg _)
        · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hle)
    _ ≤ ∫ s in Ioc (0 : ℝ) T, A * P.lEta s ^ (-γ) * (vsHeight P.z s)⁻¹ :=
        setIntegral_mono_set hGi ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall hG0)) hsub.eventuallyLE
    _ ≤ _ := hint

end BlockBand.Native.ErdosRiabov.QV
