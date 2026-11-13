module

public import BlockBand.Palm.MomentFlow.MultiFlowGen
public import BlockBand.Palm.MomentFlow.MultiAux
public import BlockBand.Palm.MomentFlow.StartShift

/-!
# The expectation bound from every start `s ≥ a` (restart transport)

The stopped Gronwall expectation bound for a generic weighted mass, first for a positive start
time and then, through the restart map of the flow, from every start `s ≥ a`
(`gen_mf_expectation_any`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N : ℕ}

/-- The adapted mass depends on the sample only through the coefficient path and the datum. -/
theorem adaptedMass_congr {Ω Ω' : Type*} {M : ℕ} {Lc : ℝ≥0 → Ω → Fin M → Fin M → ℝ}
    {Lc' : ℝ≥0 → Ω' → Fin M → Fin M → ℝ} {v₀ : Ω → Fin M → ℝ} {v₀' : Ω' → Fin M → ℝ}
    {ω : Ω} {ω' : Ω'} (hL : ∀ t, Lc t ω = Lc' t ω') (hv : v₀ ω = v₀' ω') (x : ℝ) :
    adaptedMass Lc v₀ x ω = adaptedMass Lc' v₀' x ω' := by
  unfold adaptedMass adaptedIter realCoeff
  simp only [hL, hv]

/-- The stopped weighted mass from start `sL`, with data functions of the start eigenvalues. -/
def stoppedMass (F : Matrix (Fin N) (Fin N) ℂ) (sL : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (C : (Fin N → ℝ) → Fin r → ℝ) (V : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ)
    (E r₀ c₁ C₁ K : ℝ) (w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ) (T : ℝ≥0)
    (ω : FlowSample N) : ℝ :=
  stoppedProcess (fun (u : ℝ≥0) ω => gTilted K w ((u : ℝ),
      gState F sL ℓ g r (fun ω => C (flowLam F sL ω)) (fun ω => V (flowLam F sL ω)) u ω))
    (flowStop F sL ℓ E r₀ c₁ C₁ g) T ω

/-- The initial weighted mass. -/
def initMass (F : Matrix (Fin N) (Fin N) ℂ) (sL : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (C : (Fin N → ℝ) → Fin r → ℝ) (V : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ) (K : ℝ)
    (w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ) (ω : FlowSample N) : ℝ :=
  gTilted K w (0, gState F sL ℓ g r (fun ω => C (flowLam F sL ω)) (fun ω => V (flowLam F sL ω))
    0 ω)

/-- Two samples with the same eigenvalue path after their starts have the same stopped mass. -/
theorem stoppedMass_congr {F : Matrix (Fin N) (Fin N) ℂ} {sL sL' : ℝ≥0} {ℓ : ℕ} {g : ℝ} {r : ℕ}
    {C : (Fin N → ℝ) → Fin r → ℝ} {V : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ}
    {E r₀ c₁ C₁ K : ℝ} {w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ} {T : ℝ≥0}
    {ω ω' : FlowSample N} (hP : ∀ x : ℝ≥0, flowLam F (sL + x) ω = flowLam F (sL' + x) ω') :
    stoppedMass F sL ℓ g r C V E r₀ c₁ C₁ K w T ω =
        stoppedMass F sL' ℓ g r C V E r₀ c₁ C₁ K w T ω' ∧
      initMass F sL ℓ g r C V K w ω = initMass F sL' ℓ g r C V K w ω' := by
  have h0 : flowLam F sL ω = flowLam F sL' ω' := by simpa using hP 0
  have hρ : flowStop F sL ℓ E r₀ c₁ C₁ g ω = flowStop F sL' ℓ E r₀ c₁ C₁ g ω' := by
    unfold flowStop hitTime
    simp only [hP]
  have hcoef : ∀ t, mfCoeff F sL ℓ g r t ω = mfCoeff F sL' ℓ g r t ω' := fun t => by
    simp only [mfCoeff, hP]
  have hm : ∀ x : ℝ≥0, mfMass F sL ℓ g r (fun ω => V (flowLam F sL ω)) x ω =
      mfMass F sL' ℓ g r (fun ω => V (flowLam F sL' ω)) x ω' := fun x =>
    adaptedMass_congr hcoef (by simp only [h0]) x
  have hs : ∀ x : ℝ≥0, gState F sL ℓ g r (fun ω => C (flowLam F sL ω))
      (fun ω => V (flowLam F sL ω)) x ω = gState F sL' ℓ g r (fun ω => C (flowLam F sL' ω))
      (fun ω => V (flowLam F sL' ω)) x ω' := fun x => by
    simp only [gState, hP x, h0, hm x]
  refine ⟨?_, ?_⟩
  · unfold stoppedMass stoppedProcess
    rw [hρ]
    dsimp only
    rw [hs]
  · unfold initMass
    rw [hs]

/-- The path identity through the restart map (`ω.1` Hermitian). -/
theorem flowLam_restart {F : Matrix (Fin N) (Fin N) ℂ} {a' a : ℝ} (ha' : a' ≤ a)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (x : ℝ≥0) :
    flowLam F (Real.toNNReal (a - a') + x) ω = flowLam F (0 + x) (restartMap a' a ω) := by
  have hH' : (restartMap (N := N) a' a ω).1.IsHermitian :=
    hω.add (hermitianBrownian_isHermitian' _ _)
  rw [flowLam_add_eq_eig F a' hω, flowLam_add_eq_eig F a hH', zero_add]
  funext k
  rw [flowEigenvalue_restartMap F ha' (by have := x.2; linarith)]
  congr 1
  push_cast
  rw [Real.coe_toNNReal _ (by linarith)]
  ring

theorem measurable_stoppedMass {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (sL : ℝ≥0) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (r : ℕ) {C : (Fin N → ℝ) → Fin r → ℝ}
    (hC : Measurable C) {V : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ} (hV : Measurable V)
    (E r₀ c₁ C₁ K : ℝ) {w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ}
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2)) (T : ℝ≥0) :
    StronglyMeasurable (stoppedMass F sL ℓ g r C V E r₀ c₁ C₁ K w T) ∧
      StronglyMeasurable (initMass F sL ℓ g r C V K w) := by
  set 𝓖 := shiftFiltration (flowFiltration N) sL
  have hle0 : flowFiltration N sL ≤ 𝓖 0 := (flowFiltration N).mono (le_of_eq (add_zero sL).symm)
  have hc₀m : Measurable[𝓖 0] (fun ω => C (flowLam F sL ω)) :=
    (hC.comp (flowLam_adapted F sL)).mono hle0 le_rfl
  have hv₀m : Measurable[𝓖 0] (fun ω => V (flowLam F sL ω)) :=
    (hV.comp (flowLam_adapted F sL)).mono hle0 le_rfl
  have hYc : ∀ ω, Continuous fun xx : ℝ≥0 => gState F sL ℓ g r (fun ω => C (flowLam F sL ω))
      (fun ω => V (flowLam F sL ω)) xx ω := fun ω =>
    continuous_sumVec.comp (((flowLam_continuous hF ω).comp
      (continuous_const.add continuous_id)).prodMk (continuous_sumVec.comp
        (continuous_const.prodMk (adaptedMass_continuous (mfCoeff_continuous hN hF sL ℓ hg r)
          _ ω))))
  have hYa : ∀ xx, Measurable[𝓖 xx] (fun ω => gState F sL ℓ g r (fun ω => C (flowLam F sL ω))
      (fun ω => V (flowLam F sL ω)) xx ω) := by
    intro xx
    have h1 := flowLam_adapted F (sL + xx)
    have h2 := adaptedMass_measurable 𝓖 (mfCoeff_adapted hN F sL ℓ hg r)
      (mfCoeff_continuous hN hF sL ℓ hg r) hv₀m xx
    have h3 : Measurable[𝓖 xx] (fun ω => C (flowLam F sL ω)) :=
      hc₀m.mono (𝓖.mono (zero_le (a := xx))) le_rfl
    exact continuous_sumVec.measurable.comp (h1.prodMk
      (continuous_sumVec.measurable.comp (h3.prodMk h2)))
  have hΦcont : Continuous (gTilted (N := N) (r := r) (M := sectorCard N r) K w) :=
    (gTilted_contDiff hw).continuous
  have hXa : ∀ xx, StronglyMeasurable[𝓖 xx] (fun ω => gTilted K w ((xx : ℝ),
      gState F sL ℓ g r (fun ω => C (flowLam F sL ω)) (fun ω => V (flowLam F sL ω)) xx ω)) :=
    fun xx => (hΦcont.measurable.comp (measurable_const.prodMk (hYa xx))).stronglyMeasurable
  have hXc : ∀ ω, Continuous fun xx : ℝ≥0 => gTilted K w ((xx : ℝ),
      gState F sL ℓ g r (fun ω => C (flowLam F sL ω)) (fun ω => V (flowLam F sL ω)) xx ω) :=
    fun ω => hΦcont.comp (NNReal.continuous_coe.prodMk (hYc ω))
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous hXa hXc
  refine ⟨?_, ?_⟩
  · have hm := hprog.stronglyMeasurable_stoppedProcess (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g) T
    exact hm
  · exact (((hΦcont.measurable.comp (measurable_const.prodMk (hYa 0))).mono (𝓖.le 0)
      le_rfl).stronglyMeasurable)

/-- Data of the expectation bound, positive start. -/
theorem gen_mf_expectation_pos (r : ℕ) (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (sL : ℝ≥0) (hs : 0 < sL)
    (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {E r₀ c₁ C₁ : ℝ}
    {C : (Fin N → ℝ) → Fin r → ℝ} (hC : Measurable C)
    {V : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ} (hV : Measurable V)
    (hV01 : ∀ lam q, 0 ≤ V lam q ∧ V lam q ≤ 1)
    {w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ}
    {d1 d2 : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → Fin N → ℝ}
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => d1 q (fun m => lam m + if m = i then s else 0) c i) (d2 q lam c i) 0)
    {Wm K : ℝ} (hWm0 : 0 ≤ Wm) (hw0 : ∀ q lam c, 0 ≤ w q lam c) (hwM : ∀ q lam c, w q lam c ≤ Wm)
    (hK0 : 0 ≤ K)
    (hdet : ∀ lam lam0 : Fin N → ℝ, lam ∉ stopSet N ℓ E r₀ c₁ C₁ g →
      ∀ v : Fin (sectorCard N r) → ℝ, (∀ q, 0 ≤ v q) →
      ∑ q, w q lam (C lam0) * ∑ q', cfgMat (cfgRate N lam ℓ g) r q q' * v q' +
        ∑ q, v q * ∑ i, (dysonDrift N lam i * d1 q lam (C lam0) i +
          d2 q lam (C lam0) i / (2 * N)) ≤
      K * ∑ q, w q lam (C lam0) * v q)
    (T : ℝ≥0) :
    ∫ ω, stoppedMass F sL ℓ g r C V E r₀ c₁ C₁ K w T ω ∂flowLaw N a ≤
      ∫ ω, initMass F sL ℓ g r C V K w ω ∂flowLaw N a := by
  have hle0 : flowFiltration N sL ≤ shiftFiltration (flowFiltration N) sL 0 :=
    (flowFiltration N).mono (le_of_eq (add_zero sL).symm)
  exact gen_mf_expectation_le r hIto hStop hDBM hN hF a sL hs ℓ hg
    ((hV.comp (flowLam_adapted F sL)).mono hle0 le_rfl) (fun ω q => hV01 _ q)
    ((hC.comp (flowLam_adapted F sL)).mono hle0 le_rfl) hw hd1 hd2 hWm0 hw0 hwM hK0
    (flowStop F sL ℓ E r₀ c₁ C₁ g) (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g)
    (fun ω u hu v hv => hdet _ _ (notMem_of_lt_hitTime hu) v hv) T

/-- **The expectation bound from every start `sL ≥ 0`** (base `a > 0`). -/
theorem gen_mf_expectation_any (r : ℕ) (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (sL : ℝ≥0)
    (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {E r₀ c₁ C₁ : ℝ}
    {C : (Fin N → ℝ) → Fin r → ℝ} (hC : Measurable C)
    {V : (Fin N → ℝ) → Fin (sectorCard N r) → ℝ} (hV : Measurable V)
    (hV01 : ∀ lam q, 0 ≤ V lam q ∧ V lam q ≤ 1)
    {w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ}
    {d1 d2 : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → Fin N → ℝ}
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => d1 q (fun m => lam m + if m = i then s else 0) c i) (d2 q lam c i) 0)
    {Wm K : ℝ} (hWm0 : 0 ≤ Wm) (hw0 : ∀ q lam c, 0 ≤ w q lam c) (hwM : ∀ q lam c, w q lam c ≤ Wm)
    (hK0 : 0 ≤ K)
    (hdet : ∀ lam lam0 : Fin N → ℝ, lam ∉ stopSet N ℓ E r₀ c₁ C₁ g →
      ∀ v : Fin (sectorCard N r) → ℝ, (∀ q, 0 ≤ v q) →
      ∑ q, w q lam (C lam0) * ∑ q', cfgMat (cfgRate N lam ℓ g) r q q' * v q' +
        ∑ q, v q * ∑ i, (dysonDrift N lam i * d1 q lam (C lam0) i +
          d2 q lam (C lam0) i / (2 * N)) ≤
      K * ∑ q, w q lam (C lam0) * v q)
    (T : ℝ≥0) :
    ∫ ω, stoppedMass F sL ℓ g r C V E r₀ c₁ C₁ K w T ω ∂flowLaw N a ≤
      ∫ ω, initMass F sL ℓ g r C V K w ω ∂flowLaw N a := by
  rcases eq_or_lt_of_le (zero_le (a := sL)) with h0 | hpos
  swap
  · exact gen_mf_expectation_pos r hIto hStop hDBM hN hF a sL hpos ℓ hg hC hV hV01 hw hd1 hd2
      hWm0 hw0 hwM hK0 hdet T
  subst h0
  set a' := a / 2 with ha'def
  have ha'0 : 0 ≤ a' := by positivity
  have ha'a : a' ≤ a := by linarith
  set sL' : ℝ≥0 := Real.toNNReal (a - a') with hsL'
  have hsL'pos : 0 < sL' := Real.toNNReal_pos.mpr (by linarith)
  have hmp := measurePreserving_restartMap (N := N) ha'0 ha'a
  obtain ⟨hXm, hIm⟩ := measurable_stoppedMass hF hN 0 ℓ hg r hC hV E r₀ c₁ C₁ K hw T
  have hae : ∀ᵐ ω ∂flowLaw N a', (stoppedMass F sL' ℓ g r C V E r₀ c₁ C₁ K w T ω =
      stoppedMass F 0 ℓ g r C V E r₀ c₁ C₁ K w T (restartMap a' a ω)) ∧
      (initMass F sL' ℓ g r C V K w ω = initMass F 0 ℓ g r C V K w (restartMap a' a ω)) := by
    filter_upwards [ae_fst_isHermitian (N := N) a'] with ω hω
    exact stoppedMass_congr (flowLam_restart ha'a hω)
  have hpos := gen_mf_expectation_pos r hIto hStop hDBM hN hF a' sL' hsL'pos ℓ hg hC hV hV01 hw
    hd1 hd2 hWm0 hw0 hwM hK0 hdet T
  have e1 : ∫ ω, stoppedMass F 0 ℓ g r C V E r₀ c₁ C₁ K w T ω ∂flowLaw N a =
      ∫ ω, stoppedMass F sL' ℓ g r C V E r₀ c₁ C₁ K w T ω ∂flowLaw N a' := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hXm.aestronglyMeasurable]
    exact integral_congr_ae (hae.mono fun ω h => h.1.symm)
  have e2 : ∫ ω, initMass F 0 ℓ g r C V K w ω ∂flowLaw N a =
      ∫ ω, initMass F sL' ℓ g r C V K w ω ∂flowLaw N a' := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hIm.aestronglyMeasurable]
    exact integral_congr_ae (hae.mono fun ω h => h.2.symm)
  rw [e1, e2]
  exact hpos

end BlockBand.Palm.MomentFlow
