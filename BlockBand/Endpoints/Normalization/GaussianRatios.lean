module

public import BlockBand.Endpoints.Normalization.GaussianRatiosClocks

/-!
# The Gaussian-ratios theorem and the Palm part of the two-positive-clocks lemma

The theorems have the types `Clocks.GaussianRatiosContract` and
`Clocks.TwoPositiveClocksPalmContract`. They are proved from `CoareaPalm.FreshPalmContract` (the
fresh-Palm theorem) and the hypothesis `hZ : NormalizerLowerBound`:
`∀ A c₀ r₀ s₀ v₀, FreshConstants c₀ r₀ s₀ v₀ → ∃ c > 0, ∃ N₀, ∀ N ≥ N₀, ∀ F E,
FreshClass F A c₀ E r₀ s₀ v₀ → c N ≤ palmMass F c₀ E`, the lower bound `Z ≥ c₀N` of the
deterministic-normalizer corollary, which discharges it (`GaussianRatiosAssembly`).

**Proof.** The joint law of the clocks: `clock_weak_comparison` (relative Palm moments from
the fresh-Palm theorem averaged over `a ~ CN(0,Y)`, polarization, moment determinacy along
subsequences). The ratios (and the small-denominator estimate of the
Gaussian-ratios theorem): the test is cut off at `X₀ ≥ u` by a continuous cutoff; the
complement is controlled by the Gaussian small-ball bound `E e^{-sX̃₀} ≤ (1+s)⁻¹`
(`integral_cutDown_gauss_le`: `E[1{X̃₀ ≤ 2u}] ≤ 9u`) and, on the Palm side, by the joint
comparison applied to the cutoff itself. No inverse moment of the denominator is used.
For the Gaussian-ratios theorem the clocks are `X₀ = Nv*Dv/T`, `X₀ + X_j = Nv*(D+B_j)v/T`
(`D + B_j ⪰ 0`, `Tr Γ(D+B_j) ≤ 2T`); for the two-positive-clocks lemma they are `Nv*Dv/T`,
`Nv*Cv/T` with `Tr ΓC ≤ KT`, no Loewner domination.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix Filter Topology BoundedContinuousFunction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder Matrix

/-!
## Continuous cutoffs
-/

/-- `0` for `y ≤ u`, `1` for `y ≥ 2u`. -/
def cutUp (u y : ℝ) : ℝ := min 1 (max 0 (y / u - 1))

/-- `1` for `y ≤ 2u`, `0` for `y ≥ 3u`. -/
def cutDown (u y : ℝ) : ℝ := min 1 (max 0 (3 - y / u))

theorem continuous_cutUp (u : ℝ) : Continuous (cutUp u) := by unfold cutUp; fun_prop

theorem continuous_cutDown (u : ℝ) : Continuous (cutDown u) := by unfold cutDown; fun_prop

theorem cutUp_mem (u y : ℝ) : 0 ≤ cutUp u y ∧ cutUp u y ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem cutDown_mem (u y : ℝ) : 0 ≤ cutDown u y ∧ cutDown u y ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem cutUp_eq_one {u y : ℝ} (hu : 0 < u) (hy : 2 * u ≤ y) : cutUp u y = 1 := by
  unfold cutUp
  have : 1 ≤ y / u - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hu]; linarith
  rw [max_eq_right (by linarith), min_eq_left this]

theorem cutDown_eq_one {u y : ℝ} (hu : 0 < u) (hy : y ≤ 2 * u) : cutDown u y = 1 := by
  unfold cutDown
  have : 1 ≤ 3 - y / u := by
    have : y / u ≤ 2 := by rw [div_le_iff₀ hu]; linarith
    linarith
  rw [max_eq_right (by linarith), min_eq_left this]

theorem cutDown_le_exp {u y : ℝ} (hu : 0 < u) :
    cutDown u y ≤ Real.exp 1 * Real.exp (-(3 * u)⁻¹ * y) := by
  rw [← Real.exp_add]
  rcases le_or_gt (3 * u) y with h | h
  · have : cutDown u y = 0 := by
      unfold cutDown
      have : 3 - y / u ≤ 0 := by
        have : 3 ≤ y / u := by rw [le_div_iff₀ hu]; linarith
        linarith
      rw [max_eq_left this, min_eq_right zero_le_one]
    rw [this]; exact (Real.exp_pos _).le
  · refine (cutDown_mem u y).2.trans (Real.one_le_exp ?_)
    have : (3 * u)⁻¹ * y ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity)]; linarith
    linarith

theorem abs_cutUp_mul_le {u y z B : ℝ} (hz : |z| ≤ B) : |cutUp u y * z| ≤ B := by
  rw [abs_mul, abs_of_nonneg (cutUp_mem u y).1]
  calc cutUp u y * |z| ≤ 1 * |z| := mul_le_mul_of_nonneg_right (cutUp_mem u y).2 (abs_nonneg _)
    _ ≤ B := by rw [one_mul]; exact hz

/-- The cutoff estimate: if `φ = H` on `{y ≥ 2u}` and `|φ|, |H| ≤ B`, then
`|φ - H| ≤ 2B cutDown_u(y)`. -/
theorem abs_sub_le_cutDown {u y φ H B : ℝ} (hu : 0 < u) (hφ : |φ| ≤ B) (hH : |H| ≤ B)
    (heq : 2 * u ≤ y → φ = H) : |φ - H| ≤ 2 * B * cutDown u y := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hφ
  rcases le_or_gt (2 * u) y with h | h
  · rw [heq h, sub_self, abs_zero]
    exact mul_nonneg (by linarith) (cutDown_mem u y).1
  · rw [cutDown_eq_one hu h.le, mul_one]
    exact (abs_sub _ _).trans (by linarith)

theorem abs_integral_sub_le {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    {φ H w : X → ℝ} (hφ : Integrable φ ρ) (hH : Integrable H ρ) (hw : Integrable w ρ) {B : ℝ}
    (hpt : ∀ x, |φ x - H x| ≤ 2 * B * w x) :
    |∫ x, φ x ∂ρ - ∫ x, H x ∂ρ| ≤ 2 * B * ∫ x, w x ∂ρ := by
  rw [← integral_sub hφ hH, ← integral_const_mul]
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hφ.sub hH).abs (hw.const_mul _) hpt)

theorem integrable_of_abs_le {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    [IsFiniteMeasure ρ] {φ : X → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    Integrable φ ρ :=
  (integrable_const B).mono' hφ.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

/-!
## The Gaussian small-ball bound
-/

variable {N : ℕ}

/-- **Small denominators, Gaussian side**: `E[cutDown_u(g*M*DMg/T)] ≤ 9u` when `MM* = Γ` and
`T = Tr(ΓD) > 0` (from `E e^{-sX̃₀} ≤ (1+s)⁻¹`, `s = 1/(3u)`). -/
theorem integral_cutDown_gauss_le {D M Γ : Matrix (Fin N) (Fin N) ℂ} (hD : D.PosSemidef)
    (hM : M * Mᴴ = Γ) (hT : 0 < traceAgainst Γ D) {u : ℝ} (hu : 0 < u) :
    ∫ g, cutDown u (quadForm D (M *ᵥ g) / traceAgainst Γ D) ∂circularVectorLaw (Fin N) ≤
      9 * u := by
  set T := traceAgainst Γ D
  have hQ : (Mᴴ * D * M).PosSemidef := hD.conjTranspose_mul_mul_same M
  have htr : (Mᴴ * D * M).trace.re = T := trace_conj_eq_traceAgainst D M Γ hM
  set s : ℝ := (3 * u)⁻¹ * T⁻¹
  have hs : 0 ≤ s := by positivity
  have hpt : ∀ g : Fin N → ℂ, cutDown u (quadForm D (M *ᵥ g) / T) ≤
      Real.exp 1 * Real.exp (-s * quadForm (Mᴴ * D * M) g) := by
    intro g
    rw [quadForm_conjTranspose_mul_mul]
    refine (cutDown_le_exp hu).trans (le_of_eq ?_)
    congr 2
    rw [div_eq_mul_inv]; ring
  have hexpint : Integrable (fun g => Real.exp (-s * quadForm (Mᴴ * D * M) g))
      (circularVectorLaw (Fin N)) := by
    refine integrable_of_abs_le (Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_quadForm _))) (B := 1) fun g => ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := quadForm_nonneg_of_posSemidef hQ g
    nlinarith
  have hcutint : Integrable (fun g => cutDown u (quadForm D (M *ᵥ g) / T))
      (circularVectorLaw (Fin N)) := by
    refine integrable_of_abs_le ((continuous_cutDown u).measurable.comp
      (((continuous_quadForm' D).comp
        (Matrix.toLin' M).continuous_of_finiteDimensional).measurable.div_const T)) (B := 1)
      fun g => ?_
    rw [abs_of_nonneg (cutDown_mem _ _).1]; exact (cutDown_mem _ _).2
  calc ∫ g, cutDown u (quadForm D (M *ᵥ g) / T) ∂circularVectorLaw (Fin N)
      ≤ ∫ g, Real.exp 1 * Real.exp (-s * quadForm (Mᴴ * D * M) g) ∂circularVectorLaw (Fin N) :=
        integral_mono hcutint (hexpint.const_mul _) hpt
    _ = Real.exp 1 * ∫ g, Real.exp (-s * quadForm (Mᴴ * D * M) g) ∂circularVectorLaw (Fin N) :=
        integral_const_mul _ _
    _ ≤ Real.exp 1 * (1 + s * T)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := integral_exp_neg_quadForm_le hQ hs
        rwa [htr] at this
    _ ≤ 9 * u := by
        have hsT : s * T = (3 * u)⁻¹ := by
          simp only [s]; field_simp
        rw [hsT]
        have he : Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
        have h1 : (1 + (3 * u)⁻¹)⁻¹ ≤ 3 * u := by
          rw [inv_le_comm₀ (by positivity) (by positivity)]
          linarith [le_add_of_nonneg_left (zero_le_one' ℝ) (a := (3 * u)⁻¹)]
        nlinarith [inv_pos.mpr (show (0 : ℝ) < 1 + (3 * u)⁻¹ by positivity)]

/-!
## Ratio algebra
-/

theorem palm_ratio_eq {N : ℕ} {a b T : ℝ} (hT : 0 < T) (h : 0 < (N : ℝ) * b / T) :
    ((N : ℝ) * a / T) / ((N : ℝ) * b / T) = a / b := by
  have hN : (N : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul, zero_div] at h; exact lt_irrefl _ h
  have hb : b ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_div] at h; exact lt_irrefl _ h
  field_simp

theorem pos_of_palm_clock {N : ℕ} {b T : ℝ} (h : 0 < (N : ℝ) * b / T) : b ≠ 0 := by
  intro h0; rw [h0, mul_zero, zero_div] at h; exact lt_irrefl _ h

theorem continuous_projIci_zero' : Continuous (Set.projIci (0 : ℝ)) :=
  (continuous_const.max continuous_id).subtype_mk _

/-!
## the two-positive-clocks lemma, Palm part
-/

/-- The two clock matrices `(D, C)`. -/
def twoClocks (D C : Matrix (Fin N) (Fin N) ℂ) : Fin 2 → Matrix (Fin N) (Fin N) ℂ := ![D, C]

theorem twoClocks_psd {D C : Matrix (Fin N) (Fin N) ℂ} (hD : D.PosSemidef) (hC : C.PosSemidef) :
    ∀ i, (twoClocks D C i).PosSemidef := by
  intro i; fin_cases i
  · exact hD
  · exact hC

theorem twoClocks_trace {Γ D C : Matrix (Fin N) (Fin N) ℂ} {K : ℝ} (hT : 0 < traceAgainst Γ D)
    (hK : traceAgainst Γ C ≤ K * traceAgainst Γ D) :
    ∀ i, traceAgainst Γ (twoClocks D C i) ≤ max 1 K * traceAgainst Γ D := by
  intro i; fin_cases i
  · simp only [twoClocks, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    nlinarith [le_max_left 1 K]
  · simp only [twoClocks, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [le_max_right 1 K]

/-- The joint test `y ↦ ψ(clockPair y₀ y₁)`. -/
def pairTest (ψ : (Set.Ici (0 : ℝ) × Set.Ici (0 : ℝ)) →ᵇ ℝ) : (Fin 2 → ℝ) →ᵇ ℝ :=
  ψ.compContinuous ⟨fun y => clockPair (y 0) (y 1),
    (continuous_projIci_zero'.comp (continuous_apply 0)).prodMk
      (continuous_projIci_zero'.comp (continuous_apply 1))⟩

/-- **Two-positive-clocks lemma, Palm part**, from `FreshPalmContract` and the normalizer lower
bound `NormalizerLowerBound`. -/
theorem twoPositiveClocksPalm_of (hP : FreshPalmContract) (hZ : NormalizerLowerBound) :
    TwoPositiveClocksPalmContract := by
  refine ⟨?_, ?_⟩
  · -- joint
    intro A c₀ r₀ s₀ v₀ hc K ψ ε hε
    obtain ⟨N₀, hN₀⟩ := clock_weak_comparison hP hZ (A := A) hc (ι := Fin 2) (max 1 K)
      (le_trans zero_le_one (le_max_left 1 K)) (pairTest ψ) ε hε
    refine ⟨N₀, fun N hN _ F E hF D C hD hC hT hK M hM => ?_⟩
    have := (hN₀ N hN F E hF (twoClocks D C) (twoClocks_psd hD hC) _ hT
      (twoClocks_trace hT hK) M hM).2
    exact this
  · -- ratio
    intro A c₀ r₀ s₀ v₀ hc K Φ ε hε
    set B := ‖Φ‖ with hBdef
    have hB0 : 0 ≤ B := norm_nonneg _
    have hΦB : ∀ x, |Φ x| ≤ B := fun x => by
      simpa [Real.norm_eq_abs] using Φ.norm_coe_le_norm x
    set u : ℝ := ε / (200 * (B + 1)) with hudef
    have hu : 0 < u := by positivity
    set R : ℝ := max 1 K
    have hR0 : 0 ≤ R := le_trans zero_le_one (le_max_left 1 K)
    -- the cut test and the cutoff
    have hHc : Continuous (fun y : Fin 2 → ℝ =>
        cutUp u (y 0) * Φ (Set.projIci 0 (y 1 / max (y 0) u))) := by
      refine ((continuous_cutUp u).comp (continuous_apply 0)).mul
        (Φ.continuous.comp (continuous_projIci_zero'.comp ?_))
      exact (continuous_apply 1).div ((continuous_apply 0).max continuous_const)
        fun y => (lt_of_lt_of_le hu (le_max_right _ _)).ne'
    let H : (Fin 2 → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup _ hHc B
      (fun y => by rw [Real.norm_eq_abs]; exact abs_cutUp_mul_le (hΦB _))
    let W : (Fin 2 → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun y => cutDown u (y 0)) ((continuous_cutDown u).comp (continuous_apply 0)) 1
      (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (cutDown_mem _ _).1]; exact (cutDown_mem _ _).2)
    set ε' : ℝ := ε / (16 * (B + 1)) with hε'def
    obtain ⟨N₁, hN₁⟩ := clock_weak_comparison hP hZ (A := A) hc (ι := Fin 2) R hR0 H (ε / 2)
      (by positivity)
    obtain ⟨N₂, hN₂⟩ := clock_weak_comparison hP hZ (A := A) hc (ι := Fin 2) R hR0 W ε'
      (by positivity)
    refine ⟨max N₁ N₂, fun N hN _ F E hF D C hD hC hT hK M hM d hd => ?_⟩
    set T := traceAgainst (freshGamma F c₀ E) D with hTdef
    set P := twoClocks D C
    have hPsd := twoClocks_psd hD hC
    have hPtr := twoClocks_trace (K := K) hT hK
    obtain ⟨hZpos, hHcmp⟩ := hN₁ N (le_of_max_le_left hN) F E hF P hPsd T hT hPtr M hM
    have hWcmp := (hN₂ N (le_of_max_le_right hN) F E hF P hPsd T hT hPtr M hM).2
    -- the observables
    set φ : (Fin N → ℂ) → ℝ := fun v => Φ (ratioHalfLine C D d v) with hφdef
    have hφm : Measurable φ := by
      refine Φ.continuous.measurable.comp (continuous_projIci_zero'.measurable.comp ?_)
      exact Measurable.ite (measurableSet_eq_fun (measurable_quadForm D) measurable_const) hd
        ((measurable_quadForm C).div (measurable_quadForm D))
    have hφB : ∀ v, |φ v| ≤ B := fun v => hΦB _
    have hHB : ∀ y, |H y| ≤ B := fun y => abs_cutUp_mul_le (hΦB _)
    have hW1 : ∀ y, |W y| ≤ 1 := fun y => by
      show |cutDown u (y 0)| ≤ 1
      rw [abs_of_nonneg (cutDown_mem _ _).1]; exact (cutDown_mem _ _).2
    -- pointwise cutoff bounds
    have hptP : ∀ v, |φ v - H (palmClocks N P T v)| ≤ 2 * B * W (palmClocks N P T v) := by
      intro v
      refine abs_sub_le_cutDown hu (hφB v) (hHB _) fun hy' => ?_
      have hy : 2 * u ≤ (N : ℝ) * quadForm D v / T := hy'
      have hy0 : 0 < (N : ℝ) * quadForm D v / T := lt_of_lt_of_le (by positivity) hy
      have hD0 : quadForm D v ≠ 0 :=
        pos_of_palm_clock hy0
      show Φ (ratioHalfLine C D d v) = cutUp u ((N : ℝ) * quadForm D v / T) *
        Φ (Set.projIci 0 (((N : ℝ) * quadForm C v / T) / max ((N : ℝ) * quadForm D v / T) u))
      rw [cutUp_eq_one hu hy, one_mul, max_eq_left (by linarith), palm_ratio_eq hT hy0]
      unfold ratioHalfLine
      rw [ite_eq_right hD0]
    have hptG : ∀ g : Fin N → ℂ, |φ (M *ᵥ g) - H (gaussClocks P T (M *ᵥ g))| ≤
        2 * B * W (gaussClocks P T (M *ᵥ g)) := by
      intro g
      refine abs_sub_le_cutDown hu (hφB _) (hHB _) fun hy' => ?_
      have hy : 2 * u ≤ quadForm D (M *ᵥ g) / T := hy'
      have hy0 : 0 < quadForm D (M *ᵥ g) / T := lt_of_lt_of_le (by positivity) hy
      have hD0 : quadForm D (M *ᵥ g) ≠ 0 := by
        intro h0; rw [h0, zero_div] at hy0; exact lt_irrefl _ hy0
      show Φ (ratioHalfLine C D d (M *ᵥ g)) = cutUp u (quadForm D (M *ᵥ g) / T) *
        Φ (Set.projIci 0 ((quadForm C (M *ᵥ g) / T) / max (quadForm D (M *ᵥ g) / T) u))
      rw [cutUp_eq_one hu hy, one_mul, max_eq_left (by linarith), div_div_div_cancel_right₀ hT.ne']
      unfold ratioHalfLine
      rw [ite_eq_right hD0]
    -- Palm side as integrals
    have hpc := continuous_palmClocks N P T
    have hgc : Continuous fun g : Fin N → ℂ => gaussClocks P T (M *ᵥ g) :=
      (continuous_gaussClocks P T).comp (Matrix.toLin' M).continuous_of_finiteDimensional
    have hprob := isProbabilityMeasure_palmMeasure F c₀ E hZpos
    have hP1 : |palmExpect F c₀ E φ - palmExpect F c₀ E (fun v => H (palmClocks N P T v))| ≤
        2 * B * palmExpect F c₀ E (fun v => W (palmClocks N P T v)) := by
      rw [palmExpect_eq_integral F c₀ E hφm (fun v _ => hφB v),
        palmExpect_eq_integral_of_continuous F c₀ E
          (φ := fun v => H (palmClocks N P T v)) (H.continuous.comp hpc),
        palmExpect_eq_integral_of_continuous F c₀ E
          (φ := fun v => W (palmClocks N P T v)) (W.continuous.comp hpc)]
      exact abs_integral_sub_le (integrable_palmMeasure F c₀ E hφm (fun v _ => hφB v))
        (integrable_palmMeasure_of_continuous F c₀ E (H.continuous.comp hpc))
        (integrable_palmMeasure_of_continuous F c₀ E (W.continuous.comp hpc)) hptP
    have hG1 : |∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N) -
        ∫ g, H (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤
        2 * B * ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) :=
      abs_integral_sub_le
        (integrable_of_abs_le (hφm.comp (measurable_mulVec M)) fun g => hφB _)
        (integrable_of_abs_le (H.continuous.comp hgc).measurable fun g => hHB _)
        (integrable_of_abs_le (W.continuous.comp hgc).measurable fun g => hW1 _) hptG
    have hGW : ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) ≤ 9 * u :=
      integral_cutDown_gauss_le hD hM hT hu
    have hPW : palmExpect F c₀ E (fun v => W (palmClocks N P T v)) ≤ 9 * u + ε' := by
      have := le_abs_self (palmExpect F c₀ E (fun v => W (palmClocks N P T v)) -
        ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N))
      linarith
    show |palmExpect F c₀ E φ - ∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N)| ≤ ε
    have htri : |palmExpect F c₀ E φ - ∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N)| ≤
        2 * B * palmExpect F c₀ E (fun v => W (palmClocks N P T v)) + ε / 2 +
          2 * B * ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) := by
      have e := abs_sub_le (palmExpect F c₀ E φ)
        (palmExpect F c₀ E (fun v => H (palmClocks N P T v)))
        (∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N))
      have e2 := abs_sub_le (palmExpect F c₀ E (fun v => H (palmClocks N P T v)))
        (∫ g, H (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N))
        (∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N))
      rw [abs_sub_comm (∫ g, H (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N))] at e2
      linarith
    have hb1 : 2 * B * (9 * u + ε') ≤ 2 * B * (9 * u) + ε / 8 := by
      have : 2 * B * ε' ≤ ε / 8 := by
        rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hb2 : 2 * B * (9 * u) ≤ ε / 10 := by
      rw [hudef, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have := mul_le_mul_of_nonneg_left hPW (by positivity : (0 : ℝ) ≤ 2 * B)
    have := mul_le_mul_of_nonneg_left hGW (by positivity : (0 : ℝ) ≤ 2 * B)
    linarith

/-!
## the Gaussian-ratios theorem
-/

/-- The positive clocks `(D, D + B_1, …, D + B_k)`. -/
def ratioClocks {k : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    Fin (k + 1) → Matrix (Fin N) (Fin N) ℂ :=
  Fin.cons D fun j => D + B j

theorem ratioClocks_psd {k : ℕ} {D : Matrix (Fin N) (Fin N) ℂ}
    {B : Fin k → Matrix (Fin N) (Fin N) ℂ} (hD : D.PosSemidef) (hB : ∀ j, IsSandwiched (B j) D) :
    ∀ i, (ratioClocks D B i).PosSemidef := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [ratioClocks] using hD
  · simpa [ratioClocks] using (hB j).2.2

theorem traceAgainst_sub (Γ A B : Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ (A - B) = traceAgainst Γ A - traceAgainst Γ B := by
  unfold traceAgainst; rw [Matrix.mul_sub, trace_sub, Complex.sub_re]

theorem ratioClocks_trace {k : ℕ} {Γ D : Matrix (Fin N) (Fin N) ℂ}
    {B : Fin k → Matrix (Fin N) (Fin N) ℂ} (hΓ : Γ.PosSemidef) (hB : ∀ j, IsSandwiched (B j) D)
    (hT : 0 < traceAgainst Γ D) :
    ∀ i, traceAgainst Γ (ratioClocks D B i) ≤ 2 * traceAgainst Γ D := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [ratioClocks, Fin.cons_zero]; linarith
  · simp only [ratioClocks, Fin.cons_succ]
    rw [traceAgainst_add]
    have h := BlockBand.Endpoints.Clock.traceAgainst_nonneg hΓ (hB j).2.1
    rw [traceAgainst_sub] at h
    linarith

theorem continuous_projIcc_one : Continuous (Set.projIcc (-1 : ℝ) 1 (by norm_num)) :=
  continuous_projIcc

/-- **The Gaussian-ratios theorem** (`GaussianRatiosContract`), from `FreshPalmContract` and the
normalizer lower bound `NormalizerLowerBound`. -/
theorem gaussianRatios_of (hP : FreshPalmContract) (hZ : NormalizerLowerBound) :
    GaussianRatiosContract := by
  intro A c₀ r₀ s₀ v₀ hc k Φ ε hε
  set Bd := ‖Φ‖ with hBdef
  have hB0 : 0 ≤ Bd := norm_nonneg _
  have hΦB : ∀ x, |Φ x| ≤ Bd := fun x => by
    have := Φ.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  set u : ℝ := ε / (200 * (Bd + 1)) with hudef
  have hu : 0 < u := by positivity
  -- the clamped ratio vector of the clocks, cut off at `y₀ ≥ u`
  set clampVec : (Fin (k + 1) → ℝ) → Fin k → Set.Icc (-1 : ℝ) 1 := fun y j =>
    Set.projIcc (-1 : ℝ) 1 (by norm_num) ((y j.succ - y 0) / max (y 0) u) with hclamp
  have hclampc : Continuous clampVec := by
    refine continuous_pi fun j => continuous_projIcc_one.comp ?_
    refine Continuous.div ((continuous_apply _).sub (continuous_apply 0))
      ((continuous_apply 0).max continuous_const) ?_
    intro y
    exact (lt_of_lt_of_le hu (le_max_right (y 0) u)).ne'
  have hHc : Continuous (fun y : Fin (k + 1) → ℝ => cutUp u (y 0) * Φ (clampVec y)) :=
    ((continuous_cutUp u).comp (continuous_apply 0)).mul (Φ.continuous.comp hclampc)
  let H : (Fin (k + 1) → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup _ hHc Bd
    (fun y => by rw [Real.norm_eq_abs]; exact abs_cutUp_mul_le (hΦB _))
  let W : (Fin (k + 1) → ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => cutDown u (y 0)) ((continuous_cutDown u).comp (continuous_apply 0)) 1
    (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (cutDown_mem _ _).1]; exact (cutDown_mem _ _).2)
  set ε' : ℝ := ε / (16 * (Bd + 1)) with hε'def
  obtain ⟨N₁, hN₁⟩ := clock_weak_comparison hP hZ (A := A) hc (ι := Fin (k + 1)) 2
    (by norm_num) H (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := clock_weak_comparison hP hZ (A := A) hc (ι := Fin (k + 1)) 2
    (by norm_num) W ε' (by positivity)
  refine ⟨max N₁ N₂, fun N hN _ F E hF D B hD hB hT d hd M hM => ?_⟩
  set Γ := freshGamma F c₀ E
  set T := traceAgainst Γ D with hTdef
  set P := ratioClocks D B
  have hΓ : Γ.PosSemidef := BlockBand.Endpoints.Clock.freshGamma_posSemidef F hc.1.le E
  have hPsd := ratioClocks_psd hD hB
  have hPtr := ratioClocks_trace hΓ hB hT
  obtain ⟨hZpos, hHcmp⟩ := hN₁ N (le_of_max_le_left hN) F E hF P hPsd T hT hPtr M hM
  have hWcmp := (hN₂ N (le_of_max_le_right hN) F E hF P hPsd T hT hPtr M hM).2
  set φ : (Fin N → ℂ) → ℝ := fun v => Φ (ratioCube B D d v) with hφdef
  have hφm : Measurable φ := by
    refine Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun j => ?_)
    refine continuous_projIcc_one.measurable.comp ?_
    exact Measurable.ite (measurableSet_eq_fun (measurable_quadForm D) measurable_const)
      ((measurable_pi_apply j).comp hd) ((measurable_quadForm (B j)).div (measurable_quadForm D))
  have hφB : ∀ v, |φ v| ≤ Bd := fun v => hΦB _
  have hHB : ∀ y, |H y| ≤ Bd := fun y => abs_cutUp_mul_le (hΦB _)
  have hW1 : ∀ y, |W y| ≤ 1 := fun y => by
    show |cutDown u (y 0)| ≤ 1
    rw [abs_of_nonneg (cutDown_mem _ _).1]; exact (cutDown_mem _ _).2
  have hP0 : P 0 = D := rfl
  have hPs : ∀ j, P j.succ = D + B j := fun _ => rfl
  have hptP : ∀ v, |φ v - H (palmClocks N P T v)| ≤ 2 * Bd * W (palmClocks N P T v) := by
    intro v
    refine abs_sub_le_cutDown hu (hφB v) (hHB _) fun hy' => ?_
    have hy : 2 * u ≤ (N : ℝ) * quadForm D v / T := hy'
    have hy0 : 0 < (N : ℝ) * quadForm D v / T := lt_of_lt_of_le (by positivity) hy
    have hD0 : quadForm D v ≠ 0 := pos_of_palm_clock hy0
    show Φ (ratioCube B D d v) = cutUp u ((N : ℝ) * quadForm D v / T) *
      Φ (clampVec (palmClocks N P T v))
    rw [cutUp_eq_one hu hy, one_mul]
    congr 1
    funext j
    simp only [hclamp, palmClocks]
    rw [hPs j, hP0, quadForm_add, max_eq_left (by linarith)]
    have : ((N : ℝ) * (quadForm D v + quadForm (B j) v) / T - (N : ℝ) * quadForm D v / T) =
        (N : ℝ) * quadForm (B j) v / T := by ring
    rw [this, palm_ratio_eq hT hy0]
    unfold ratioCube
    rw [ite_eq_right hD0]
  have hptG : ∀ g : Fin N → ℂ, |φ (M *ᵥ g) - H (gaussClocks P T (M *ᵥ g))| ≤
      2 * Bd * W (gaussClocks P T (M *ᵥ g)) := by
    intro g
    refine abs_sub_le_cutDown hu (hφB _) (hHB _) fun hy' => ?_
    have hy : 2 * u ≤ quadForm D (M *ᵥ g) / T := hy'
    have hy0 : 0 < quadForm D (M *ᵥ g) / T := lt_of_lt_of_le (by positivity) hy
    have hD0 : quadForm D (M *ᵥ g) ≠ 0 := by
      intro h0; rw [h0, zero_div] at hy0; exact lt_irrefl _ hy0
    show Φ (ratioCube B D d (M *ᵥ g)) = cutUp u (quadForm D (M *ᵥ g) / T) *
      Φ (clampVec (gaussClocks P T (M *ᵥ g)))
    rw [cutUp_eq_one hu hy, one_mul]
    congr 1
    funext j
    simp only [hclamp, gaussClocks]
    rw [hPs j, hP0, quadForm_add, max_eq_left (by linarith)]
    have : ((quadForm D (M *ᵥ g) + quadForm (B j) (M *ᵥ g)) / T - quadForm D (M *ᵥ g) / T) =
        quadForm (B j) (M *ᵥ g) / T := by ring
    rw [this, div_div_div_cancel_right₀ hT.ne']
    unfold ratioCube
    rw [ite_eq_right hD0]
  have hpc := continuous_palmClocks N P T
  have hgc : Continuous fun g : Fin N → ℂ => gaussClocks P T (M *ᵥ g) :=
    (continuous_gaussClocks P T).comp (Matrix.toLin' M).continuous_of_finiteDimensional
  have hprob := isProbabilityMeasure_palmMeasure F c₀ E hZpos
  have hP1 : |palmExpect F c₀ E φ - palmExpect F c₀ E (fun v => H (palmClocks N P T v))| ≤
      2 * Bd * palmExpect F c₀ E (fun v => W (palmClocks N P T v)) := by
    rw [palmExpect_eq_integral F c₀ E hφm (fun v _ => hφB v),
      palmExpect_eq_integral_of_continuous F c₀ E
        (φ := fun v => H (palmClocks N P T v)) (H.continuous.comp hpc),
      palmExpect_eq_integral_of_continuous F c₀ E
        (φ := fun v => W (palmClocks N P T v)) (W.continuous.comp hpc)]
    exact abs_integral_sub_le (integrable_palmMeasure F c₀ E hφm (fun v _ => hφB v))
      (integrable_palmMeasure_of_continuous F c₀ E (H.continuous.comp hpc))
      (integrable_palmMeasure_of_continuous F c₀ E (W.continuous.comp hpc)) hptP
  have hG1 : |∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N) -
      ∫ g, H (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤
      2 * Bd * ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) :=
    abs_integral_sub_le
      (integrable_of_abs_le (hφm.comp (measurable_mulVec M)) fun g => hφB _)
      (integrable_of_abs_le (H.continuous.comp hgc).measurable fun g => hHB _)
      (integrable_of_abs_le (W.continuous.comp hgc).measurable fun g => hW1 _) hptG
  have hGW : ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) ≤ 9 * u :=
    integral_cutDown_gauss_le hD hM hT hu
  have hPW : palmExpect F c₀ E (fun v => W (palmClocks N P T v)) ≤ 9 * u + ε' := by
    have := le_abs_self (palmExpect F c₀ E (fun v => W (palmClocks N P T v)) -
      ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N))
    linarith
  show |palmExpect F c₀ E φ - ∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N)| ≤ ε
  have htri : |palmExpect F c₀ E φ - ∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N)| ≤
      2 * Bd * palmExpect F c₀ E (fun v => W (palmClocks N P T v)) + ε / 2 +
        2 * Bd * ∫ g, W (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N) := by
    have e := abs_sub_le (palmExpect F c₀ E φ)
      (palmExpect F c₀ E (fun v => H (palmClocks N P T v)))
      (∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N))
    have e2 := abs_sub_le (palmExpect F c₀ E (fun v => H (palmClocks N P T v)))
      (∫ g, H (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N))
      (∫ g, φ (M *ᵥ g) ∂circularVectorLaw (Fin N))
    rw [abs_sub_comm (∫ g, H (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N))] at e2
    linarith
  have hb1 : 2 * Bd * ε' ≤ ε / 8 := by
    rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb2 : 2 * Bd * (9 * u) ≤ ε / 10 := by
    rw [hudef, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := mul_le_mul_of_nonneg_left hPW (by positivity : (0 : ℝ) ≤ 2 * Bd)
  have := mul_le_mul_of_nonneg_left hGW (by positivity : (0 : ℝ) ≤ 2 * Bd)
  nlinarith

end BlockBand.Endpoints.Normalization
