module
public import BlockBand.Diffusion.PathSpace.AdapterDrift
public import BlockBand.Diffusion.PathSpace.ProductMart
public import BlockBand.Diffusion.PathSpace.BracketCalc
public import BlockBand.SourceProcess.Stochastic.Representation.Basic
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularAugment
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Pathwise
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Adapter, part 2: the bracket field and `IsMPSolutionOn`

Setting as in `AdapterDrift`: raw filtration, `U` open, `b, a` continuous on `U`, and in
addition `a` **symmetric** on `U` (the test-function martingale problem only sees the
symmetric part of `a`, while `IsMPSolutionOn.bracket` is required for all ordered pairs
`(i, j)`; without symmetry the conclusion is false).

**Headline (`IsTestMPSolution.isMPSolutionOn`).** A solution of the raw test-function
martingale problem (`C_c^∞` tests supported in `U`, raw martingales, a.s. continuous paths,
arbitrary filtration) solves the localized martingale problem `IsMPSolutionOn Q 𝓖 b a U Z`.
No completion or right-continuity of `𝓖` is needed.

Proof of the bracket field, for an interior domain `W` and `i, j`: with a bump `χ = 1` near
`closure W`, the stopped compensated `y_i y_j`-process `P`, the drift martingales `M^i, M^j`,
the `𝓖_0`-multiples `1{Z_0 ∈ W} Z^i_0 M^j`, and the processes
`K^{ij} = M^i ∫_0^· β_j - ∫_0^· β_j Ñ^i` of `hasMartingaleModification_mul_integral` (with
`β_j = 1{0 < u ≤ ρ} 1{Z_0 ∈ W} 𝓛(χ y_j)(Ẑ_u)`, `Ẑ` the progressive `predVersion`, `ρ` the raw
exit time, and `Ñ^i` the progressive compensated coordinate), the deterministic
`bracket_identity` gives, on every continuous path,
`M^i M^j - ∫ a_ij = P - Z^i_0 M^j - Z^j_0 M^i - K^{ij} - K^{ji}` at the stopped time.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ} {Ω : Type*}

/-!
### Deterministic helpers
-/

theorem coe_toNNReal_le_iff {τ : WithTop ℝ≥0} {t : ℝ≥0} {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) t) :
    ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ↔ u ≤ (stopTime τ t : ℝ) := by
  have hut : u.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hu.2
  induction τ with
  | top => simp only [le_top, stopTime_top, true_iff]; exact hu.2
  | coe s₀ =>
    rw [stopTime_coe, WithTop.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le,
      NNReal.coe_min]
    constructor
    · intro h; exact le_min hu.2 h
    · intro h; exact h.trans (min_le_right _ _)

/-- Integrating a switched-off integrand over `(0, t]` is integrating over `(0, t ∧ τ]`. -/
theorem setIntegral_switch (τ : WithTop ℝ≥0) (t : ℝ≥0) (φ : ℝ → ℝ) :
    ∫ u in Ioc (0 : ℝ) t, (if ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ then φ u else 0) =
      ∫ u in Ioc (0 : ℝ) (stopTime τ t), φ u := by
  have hsub : Ioc (0 : ℝ) (stopTime τ t) ⊆ Ioc (0 : ℝ) t :=
    Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (stopTime_le τ t))
  rw [← inter_eq_right.2 hsub, ← setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  by_cases h : ((u.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ
  · simp only [h, ↓reduceIte]
    rw [indicator_of_mem]
    exact ⟨hu.1, (coe_toNNReal_le_iff hu).1 h⟩
  · simp only [h, ↓reduceIte]
    rw [indicator_of_notMem]
    exact fun h' => h ((coe_toNNReal_le_iff hu).2 h'.2)

theorem stopTime_eq_of_le {τ : WithTop ℝ≥0} {u : ℝ≥0} (h : (u : WithTop ℝ≥0) ≤ τ) :
    stopTime τ u = u := by
  induction τ with
  | top => exact stopTime_top u
  | coe s₀ => rw [stopTime_coe]; exact min_eq_left (WithTop.coe_le_coe.1 h)

theorem setIntegral_Ioc_eq_prim {φ : ℝ → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ u in Ioc (0 : ℝ) σ, φ u = prim φ σ :=
  (intervalIntegral.integral_of_le hσ).symm

/-!
### Martingale tools
-/

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [IsProbabilityMeasure Q] in
/-- A martingale times a bounded `𝓖_0`-measurable variable is a martingale. -/
theorem martingale_mul_left_of_zero {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 Q) {g : Ω → ℝ}
    (hg : StronglyMeasurable[𝓖 0] g) {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) :
    Martingale (fun t ω => g ω * N t ω) 𝓖 Q := by
  have hgt : ∀ t, StronglyMeasurable[𝓖 t] g := fun t => hg.mono (𝓖.mono zero_le)
  have hint : ∀ t, Integrable (fun ω => g ω * N t ω) Q := fun t =>
    (hN.integrable t).bdd_mul (c := C) ((hgt t).mono (𝓖.le t)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgC ω)
  refine ⟨fun t => (hgt t).mul (hN.1 t), fun s t hst => ?_⟩
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓖 s) (μ := Q) (hgt s) (hint t)
    (hN.integrable t)
  filter_upwards [h1, hN.condExp_ae_eq hst] with ω e1 e2
  rw [show (fun ω => g ω * N t ω) = g * N t from rfl, e1, Pi.mul_apply, e2]

/-!
### The bracket field
-/

variable {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}

/-- The progressive version of `Z`, as a process. -/
def pv (Z : ℝ≥0 → Ω → Fin d → ℝ) (u : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  Levy.predVersion Z ((u : ℝ), ω)

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem pv_eq {ω : Ω} (hZ : Continuous fun t => Z t ω) {u : ℝ≥0} (hu : 0 < u) :
    pv Z u ω = Z u ω := by
  rw [pv, Levy.predVersion_eq (p := ((u : ℝ), ω)) hZ (by exact_mod_cast hu), Real.toNNReal_coe]

/-- On `closure W`, the generator of the localized product `χ y_i y_j`. -/
theorem mpGenerator_bump_coordMul {χ : (Fin d → ℝ) → ℝ} {V W : Set (Fin d → ℝ)}
    (hV : IsOpen V) (hWV : closure W ⊆ V) (hχ : ∀ y ∈ V, χ y = 1) (i j : Fin d)
    (hsym : ∀ y ∈ closure W, a y i j = a y j i) :
    ∀ y ∈ closure W, mpGenerator b a (fun y => χ y * (y i * y j)) y =
      b y i * y j + b y j * y i + a y i j := fun y hy => by
  rw [mpGenerator_congr (eventuallyEq_mul_of_eq_one hV hχ (hWV hy)), mpGenerator_coordMul,
    hsym y hy]
  ring

/-- **The bracket field of `IsMPSolutionOn`** (for symmetric `a`). -/
theorem IsTestMPSolution.bracket (h : IsTestMPSolution Q 𝓖 b a U Z) (hU : IsOpen U)
    (hb : ContinuousOn b U) (ha : ContinuousOn a U) (hsym : ∀ y ∈ U, ∀ i j, a y i j = a y j i)
    {W : Set (Fin d → ℝ)} (hW : IsInteriorDomain W U) (i j : Fin d) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t,
      N t =ᵐ[Q] stoppedProcess (fun t ω => mpCompensated b Z i t ω * mpCompensated b Z j t ω -
        ∫ s in Ioc (0 : ℝ) t, a (Z s.toNNReal ω) i j) (exitTimeFrom W Z) t := by
  obtain ⟨χ, V, hχ, hVo, hWV, hχ1⟩ := exists_bump hU hW
  have hfi := hχ.mul_left (p := fun y => y i) (contDiff_apply ℝ ℝ i)
  have hfj := hχ.mul_left (p := fun y => y j) (contDiff_apply ℝ ℝ j)
  have hfij := hχ.mul_left (p := fun y => y i * y j)
    ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ j))
  set bi := mpGenerator b a (fun y => χ y * y i) with hbi
  set bj := mpGenerator b a (fun y => χ y * y j) with hbj
  set Lij := mpGenerator b a (fun y => χ y * (y i * y j)) with hLij
  have cbi : Continuous bi := continuous_mpGenerator hU hb ha hfi
  have cbj : Continuous bj := continuous_mpGenerator hU hb ha hfj
  have cLij : Continuous Lij := continuous_mpGenerator hU hb ha hfij
  obtain ⟨Ci, -, hCi⟩ := exists_bound_mpGenerator hU hb ha hfi
  obtain ⟨Cj, -, hCj⟩ := exists_bound_mpGenerator hU hb ha hfj
  set ψ : (Fin d → ℝ) → ℝ := fun y => Lij y - (bi y * y j + bj y * y i) with hψ
  have cψ : Continuous ψ := cLij.sub ((cbi.mul (continuous_apply j)).add
    (cbj.mul (continuous_apply i)))
  have hWU : closure W ⊆ U := hW.2.2
  have ebi : ∀ y ∈ closure W, bi y = b y i := mpGenerator_bump_coord hVo hWV hχ1 i
  have ebj : ∀ y ∈ closure W, bj y = b y j := mpGenerator_bump_coord hVo hWV hχ1 j
  have eψ : ∀ y ∈ closure W, ψ y = a y i j := fun y hy => by
    simp only [hψ, ebi y hy, ebj y hy]
    rw [hLij, mpGenerator_bump_coordMul hVo hWV hχ1 i j (fun y hy => hsym y (hWU hy) i j) y hy]
    ring
  -- martingales from the test functions
  obtain ⟨Mi, hMi, hMie⟩ := h.drift hU hb ha hW i
  obtain ⟨Mj, hMj, hMje⟩ := h.drift hU hb ha hW j
  obtain ⟨P, hP, hPe⟩ := h.exists_martingale_stopped hU hb ha hfij hW.1
  -- the raw stopping time and the start set
  set ρ : Ω → WithTop ℝ≥0 := rawHit Wᶜ Z with hρdef
  have hρ : IsStoppingTime 𝓖 ρ := isStoppingTime_rawHit h.adapted
  have hρe : ∀ ω, Continuous (fun t => Z t ω) → ρ ω = exitTimeFrom W Z ω := fun ω hω =>
    rawHit_compl_eq_exitTimeFrom hW.1 hω
  set G0 : Set Ω := {ω | Z 0 ω ∈ W} with hG0def
  have hG0 : MeasurableSet[𝓖 0] G0 := h.adapted 0 hW.1.measurableSet
  -- bounds on `closure W`
  obtain ⟨R, hR⟩ := hW.2.1.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨Bb, hBb⟩ := hW.2.1.exists_bound_of_continuousOn (hb.mono hWU)
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  have hB0 : 0 ≤ max Bb 0 := le_max_right _ _
  have hRW : ∀ y ∈ closure W, ‖y‖ ≤ max R 0 := fun y hy => (hR y hy).trans (le_max_left _ _)
  have hBW : ∀ y ∈ closure W, ‖b y‖ ≤ max Bb 0 := fun y hy =>
    (hBb y hy).trans (le_max_left _ _)
  -- `𝓖_0` multipliers
  set gi : Ω → ℝ := G0.indicator fun ω => Z 0 ω i
  set gj : Ω → ℝ := G0.indicator fun ω => Z 0 ω j
  have bg : ∀ k : Fin d, ∀ ω, |G0.indicator (fun ω => Z 0 ω k) ω| ≤ max R 0 := fun k ω => by
    by_cases hω : ω ∈ G0
    · rw [indicator_of_mem hω, ← Real.norm_eq_abs]
      exact (norm_le_pi_norm (Z 0 ω) k).trans (hRW _ (subset_closure hω))
    · rw [indicator_of_notMem hω, abs_zero]; exact hR0
  have mg : ∀ k : Fin d, StronglyMeasurable[𝓖 0] (G0.indicator fun ω => Z 0 ω k) := fun k =>
    (((continuous_apply k).measurable.comp (h.adapted 0)).stronglyMeasurable).indicator hG0
  have hgiMj := martingale_mul_left_of_zero hMj (mg i) (bg i)
  have hgjMi := martingale_mul_left_of_zero hMi (mg j) (bg j)
  -- progressive integrands
  have hZsm : ∀ t, StronglyMeasurable[𝓖 t] (Z t) := fun t => (h.adapted t).stronglyMeasurable
  have hpv : IsStronglyProgressive 𝓖 (pv Z) :=
    Representation.isStronglyProgressive_predVersion 𝓖 hZsm
  have pvc : ∀ {g : (Fin d → ℝ) → ℝ}, Continuous g →
      IsStronglyProgressive 𝓖 fun u ω => g (pv Z u ω) := fun hg t =>
    (hg.measurable.comp (hpv t).measurable).stronglyMeasurable
  have c0 : IsStronglyProgressive 𝓖 fun (u : ℝ≥0) (_ : Ω) => if 0 < u then (1 : ℝ) else 0 :=
    fun t => (Measurable.ite (measurableSet_lt measurable_const
      (measurable_subtype_coe.comp measurable_fst)) measurable_const
        measurable_const).stronglyMeasurable
  set β : ((Fin d → ℝ) → ℝ) → ℝ≥0 → Ω → ℝ := fun g => switchAfter ρ fun u ω =>
    (if 0 < u then (1 : ℝ) else 0) * g (pv Z u ω) with hβdef
  have hβ : ∀ {g : (Fin d → ℝ) → ℝ}, Continuous g → IsStronglyProgressive 𝓖 (β g) :=
    fun hg => isStronglyProgressive_switchAfter (c0.mul (pvc hg)) hρ
  have hβC : ∀ {g : (Fin d → ℝ) → ℝ} {C : ℝ}, (∀ y, |g y| ≤ C) → ∀ u ω, |β g u ω| ≤ C := by
    intro g C hg u ω
    have hC : 0 ≤ C := (abs_nonneg _).trans (hg 0)
    simp only [hβdef, switchAfter]
    split_ifs
    · simp [hg]
    · simp [hC]
    · simp [hC]
  set Ñ : ((Fin d → ℝ) → ℝ) → Fin d → ℝ≥0 → Ω → ℝ := fun g k u ω =>
    pv Z u ω k - Z 0 ω k - ∫ r in Ioc (0 : ℝ) u, g (pv Z r.toNNReal ω) with hÑdef
  have hÑ : ∀ {g : (Fin d → ℝ) → ℝ}, Continuous g → ∀ k, IsStronglyProgressive 𝓖 (Ñ g k) := by
    intro g hg k
    have h1 : IsStronglyProgressive 𝓖 fun u ω => pv Z u ω k := pvc (continuous_apply k)
    have h2 : IsStronglyProgressive 𝓖 fun (_ : ℝ≥0) ω => Z 0 ω k := fun t =>
      ((((continuous_apply k).measurable.comp (h.adapted 0)).mono (𝓖.mono zero_le)
        le_rfl).stronglyMeasurable).comp_measurable measurable_snd
    have h3 := Dyson.Angular.isStronglyProgressive_integral (pvc hg)
    exact (h1.sub h2).sub h3
  -- the drift martingales are locally bounded
  have hMb : ∀ {k : Fin d} {Mk : ℝ≥0 → Ω → ℝ},
      (∀ t, Mk t =ᵐ[Q] stoppedProcess (mpCompensated b Z k) (exitTimeFrom W Z) t) →
      ∀ T, ∃ C', ∀ u ≤ T, ∀ᵐ ω ∂Q, |Mk u ω| ≤ C' := fun {k} {Mk} hMke T =>
    ⟨2 * max R 0 + max Bb 0 * T, fun u hu => by
      filter_upwards [hMke u, h.continuous] with ω e hω
      rw [e]
      exact abs_smCompensated_stop_le hW.1 hω hR0 hB0 hRW hBW hu k⟩
  -- `β_l Ñ^k = β_l M^k` where `β_l ≠ 0`
  have hÑM : ∀ {k : Fin d} {gk gl : (Fin d → ℝ) → ℝ} {Mk : ℝ≥0 → Ω → ℝ},
      (∀ y ∈ closure W, gk y = b y k) →
      (∀ t, Mk t =ᵐ[Q] stoppedProcess (mpCompensated b Z k) (exitTimeFrom W Z) t) →
      ∀ u, (fun ω => β gl u ω * Ñ gk k u ω) =ᵐ[Q] fun ω => β gl u ω * Mk u ω := by
    intro k gk gl Mk hgk hMke u
    filter_upwards [hMke u, h.continuous] with ω e hω
    rw [e]
    simp only [hβdef, switchAfter]
    by_cases hu : (u : WithTop ℝ≥0) ≤ ρ ω
    · by_cases hu0 : 0 < u
      · simp only [hu, hu0, ↓reduceIte, one_mul]
        congr 1
        rw [hρe ω hω] at hu
        rw [stoppedProcess_eq_stopTime, stopTime_eq_of_le hu]
        simp only [hÑdef, mpCompensated, pv_eq hω hu0]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        have hr0 : 0 < r.toNNReal := Real.toNNReal_pos.2 hr.1
        rw [pv_eq hω hr0]
        refine hgk _ ((stopped_path_mem_closure hW.1 hω u).1 r ?_)
        rw [stopTime_eq_of_le hu]; exact hr
      · simp only [hu0, ↓reduceIte, zero_mul]
        split_ifs; simp
    · simp only [mul_eq_mul_left_iff]
      right; split_ifs; rfl
  -- the two product martingales
  obtain ⟨Kij, hKij, hKije⟩ := hasMartingaleModification_mul_integral hMi (hMb hMie) (hβ cbj)
    (hβC hCj) (hÑ cbi i) (hÑM ebi hMie)
  obtain ⟨Kji, hKji, hKjie⟩ := hasMartingaleModification_mul_integral hMj (hMb hMje) (hβ cbi)
    (hβC hCi) (hÑ cbj j) (hÑM ebj hMje)
  refine ⟨fun t ω => P t ω - gi ω * Mj t ω - gj ω * Mi t ω - Kij t ω - Kji t ω,
    (((hP.sub hgiMj).sub hgjMi).sub hKij).sub hKji, fun t => ?_⟩
  filter_upwards [hPe t, hMie t, hMje t, hKije t, hKjie t, h.continuous] with ω e1 e2 e3 e4 e5 hω
  show P t ω - gi ω * Mj t ω - gj ω * Mi t ω - Kij t ω - Kji t ω = _
  rw [e4, e5, e1, e2, e3]
  simp only [stoppedProcess_eq_stopTime]
  obtain ⟨σ, hσ⟩ : ∃ σ, stopTime (exitTimeFrom W Z ω) t = σ := ⟨_, rfl⟩
  rw [hσ]
  have hρω : ρ ω = exitTimeFrom W Z ω := hρe ω hω
  have hmem : ∀ u ∈ Ioc (0 : ℝ) σ, Z u.toNNReal ω ∈ closure W := fun u hu =>
    (stopped_path_mem_closure hW.1 hω t).1 u (hσ ▸ hu)
  have hσ0 : (0 : ℝ) ≤ σ := σ.2
  obtain ⟨zi, hzi⟩ : ∃ f : ℝ → ℝ, f = fun u => Z u.toNNReal ω i := ⟨_, rfl⟩
  obtain ⟨zj, hzj⟩ : ∃ f : ℝ → ℝ, f = fun u => Z u.toNNReal ω j := ⟨_, rfl⟩
  obtain ⟨φi, hφi⟩ : ∃ f : ℝ → ℝ, f = fun u => bi (Z u.toNNReal ω) := ⟨_, rfl⟩
  obtain ⟨φj, hφj⟩ : ∃ f : ℝ → ℝ, f = fun u => bj (Z u.toNNReal ω) := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'⟩ : ∃ f : ℝ → ℝ, f = fun u => ψ (Z u.toNNReal ω) := ⟨_, rfl⟩
  have cpath : Continuous fun u : ℝ => Z u.toNNReal ω := hω.comp continuous_real_toNNReal
  have czi : Continuous zi := hzi ▸ (continuous_apply i).comp cpath
  have czj : Continuous zj := hzj ▸ (continuous_apply j).comp cpath
  have cφi : Continuous φi := hφi ▸ cbi.comp cpath
  have cφj : Continuous φj := hφj ▸ cbj.comp cpath
  have cψ' : Continuous ψ' := hψ' ▸ cψ.comp cpath
  have hZσ : ∀ k, Z σ ω k = Z (σ : ℝ).toNNReal ω k := fun k => by rw [Real.toNNReal_coe]
  have hZ0 : ∀ k, Z 0 ω k = Z (0 : ℝ).toNNReal ω k := fun k => by rw [Real.toNNReal_zero]
  have hIoc : ∀ (φ : ℝ → ℝ), ∫ u in Ioc (0 : ℝ) σ, φ u = ∫ u in (0 : ℝ)..σ, φ u := fun φ =>
    (intervalIntegral.integral_of_le hσ0).symm
  -- the compensated coordinates
  have hA : ∀ (k : Fin d) (gk : (Fin d → ℝ) → ℝ), (∀ y ∈ closure W, gk y = b y k) →
      mpCompensated b Z k σ ω = Z (σ : ℝ).toNNReal ω k - Z (0 : ℝ).toNNReal ω k -
        prim (fun u => gk (Z u.toNNReal ω)) σ := fun k gk hgk => by
    rw [mpCompensated, hZσ, hZ0, prim, ← intervalIntegral.integral_of_le hσ0 |>.symm]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc fun u hu => (hgk _ (hmem u hu)).symm
  have hAi : mpCompensated b Z i σ ω = zi σ - zi 0 - prim φi σ := by
    rw [hA i bi ebi, hzi, hφi]
  have hAj : mpCompensated b Z j σ ω = zj σ - zj 0 - prim φj σ := by
    rw [hA j bj ebj, hzj, hφj]
  have hB : ∫ s in Ioc (0 : ℝ) σ, a (Z s.toNNReal ω) i j = ∫ u in (0 : ℝ)..σ, ψ' u := by
    rw [← hIoc, hψ']
    exact setIntegral_congr_fun measurableSet_Ioc fun u hu => (eψ _ (hmem u hu)).symm
  have hC : testCompensated (fun y => χ y * (y i * y j)) Lij Z σ ω =
      zi σ * zj σ - zi 0 * zj 0 - ∫ u in (0 : ℝ)..σ, (φi u * zj u + φj u * zi u + ψ' u) := by
    have h1 : χ (Z σ ω) * (Z σ ω i * Z σ ω j) - χ (Z 0 ω) * (Z 0 ω i * Z 0 ω j) =
        Z σ ω i * Z σ ω j - Z 0 ω i * Z 0 ω j := by
      rcases (stopped_path_mem_closure hW.1 hω t).2 with he | ⟨h1, h2⟩
      · rw [hσ] at he; rw [he]; ring
      · rw [hσ] at h1
        rw [hχ1 _ (hWV h1), hχ1 _ (hWV h2)]; ring
    rw [testCompensated, h1, hIoc, hzi, hzj, hφi, hφj, hψ']
    simp only [← hZσ, ← hZ0]
    congr 2
    funext u
    simp only [hψ]
    ring
  -- the integral terms
  have hD : ∀ (g : (Fin d → ℝ) → ℝ), ∫ u in Ioc (0 : ℝ) t, β g u.toNNReal ω =
      prim (fun u => g (Z u.toNNReal ω)) σ := fun g => by
    simp only [hβdef, switchAfter]
    rw [hρω, setIntegral_switch, hσ, prim, ← hIoc]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
    simp only [hu0, ↓reduceIte, one_mul, pv_eq hω hu0]
  have hE : ∀ (g g' : (Fin d → ℝ) → ℝ) (k : Fin d),
      ∫ u in Ioc (0 : ℝ) t, β g u.toNNReal ω * Ñ g' k u.toNNReal ω =
        ∫ u in (0 : ℝ)..σ, g (Z u.toNNReal ω) * (Z u.toNNReal ω k - Z (0 : ℝ).toNNReal ω k -
          prim (fun r => g' (Z r.toNNReal ω)) u) := fun g g' k => by
    simp only [hβdef, switchAfter, ite_mul, zero_mul]
    rw [hρω, setIntegral_switch, hσ, ← hIoc]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
    simp only [hu0, ↓reduceIte, one_mul, pv_eq hω hu0, hÑdef]
    rw [Real.coe_toNNReal _ hu.1.le, ← hZ0, prim, intervalIntegral.integral_of_le hu.1.le]
    congr 2
    exact setIntegral_congr_fun measurableSet_Ioc fun r hr => by
      rw [pv_eq hω (Real.toNNReal_pos.2 hr.1)]
  have hDi : ∫ u in Ioc (0 : ℝ) t, β bi u.toNNReal ω = prim φi σ := by rw [hD, hφi]
  have hDj : ∫ u in Ioc (0 : ℝ) t, β bj u.toNNReal ω = prim φj σ := by rw [hD, hφj]
  have hEij : ∫ u in Ioc (0 : ℝ) t, β bj u.toNNReal ω * Ñ bi i u.toNNReal ω =
      ∫ u in (0 : ℝ)..σ, φj u * (zi u - zi 0 - prim φi u) := by
    rw [hE, hφj, hzi, hφi]
  have hEji : ∫ u in Ioc (0 : ℝ) t, β bi u.toNNReal ω * Ñ bj j u.toNNReal ω =
      ∫ u in (0 : ℝ)..σ, φi u * (zj u - zj 0 - prim φj u) := by
    rw [hE, hφi, hzj, hφj]
  -- the `𝓖_0` multipliers
  have hzero : ω ∉ G0 → σ = 0 := fun hω0 => by
    have he : exitTimeFrom W Z ω = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      le_antisymm (iInf₂_le 0 hω0) bot_le
    rw [he, stopTime_coe] at hσ
    rw [← hσ]; exact min_eq_right zero_le
  have hgi : gi ω * (zj σ - zj 0 - prim φj σ) = zi 0 * (zj σ - zj 0 - prim φj σ) := by
    by_cases hω0 : ω ∈ G0
    · simp only [gi, indicator_of_mem hω0, hzi, Real.toNNReal_zero]
    · rw [hzero hω0]; simp [prim_zero]
  have hgj : gj ω * (zi σ - zi 0 - prim φi σ) = zj 0 * (zi σ - zi 0 - prim φi σ) := by
    by_cases hω0 : ω ∈ G0
    · simp only [gj, indicator_of_mem hω0, hzj, Real.toNNReal_zero]
    · rw [hzero hω0]; simp [prim_zero]
  rw [hAi, hAj, hB, hC, hDi, hDj, hEij, hEji, hgi, hgj]
  have key := bracket_identity czi czj cφi cφj cψ' σ
  simp only at key
  linarith [key]

end BlockBand.Diffusion

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory BlockBand.SourceProcess.Stochastic
open scoped NNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}

/-- **Adapter.** A solution of the raw test-function martingale problem
(`IsTestMPSolution`: adapted, a.s. continuous paths, `f(Z_t) - ∫_0^t 𝓛f(Z_u) du` a raw
`𝓖`-martingale for every `C^∞` test `f` with compact support in `U`), with `U` open, `b, a`
continuous on `U` and `a` symmetric on `U`, solves the localized martingale problem
`IsMPSolutionOn Q 𝓖 b a U Z`, on the same raw filtration. -/
theorem IsTestMPSolution.isMPSolutionOn (h : IsTestMPSolution Q 𝓖 b a U Z) (hU : IsOpen U)
    (hb : ContinuousOn b U) (ha : ContinuousOn a U)
    (hsym : ∀ y ∈ U, ∀ i j, a y i j = a y j i) : IsMPSolutionOn Q 𝓖 b a U Z where
  adapted t := (h.adapted t).stronglyMeasurable
  continuous := h.continuous
  drift _ hW i := h.drift hU hb ha hW i
  bracket _ hW i j := h.bracket hU hb ha hsym hW i j

end BlockBand.Diffusion
