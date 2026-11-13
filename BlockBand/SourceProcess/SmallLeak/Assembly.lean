module

public import BlockBand.SourceProcess.SmallLeak.Interface
public import BlockBand.SourceProcess.Closing.Routes

/-!
# Small channel leakage from the three steps

`SmallChannelLeakage` follows from `OmittedFluxStart`, `OmittedFluxGrowth` and `LeakRecursion`.
The order of limits is: the trace stop `K = max 1 (3C/ε)` is fixed first, then `h` is taken small
(so that the flux bound `x(h) → 0`), then `W` is taken large.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing

/-- The flux bound `x(h) = C_G⁺ C_S⁺ h + h`. -/
def fluxBound (CG CS h : ℝ) : ℝ := max CG 0 * (max CS 0 * h) + h

theorem eventually_small_bound (CG CS a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < 1 ∧
      a * (Real.sqrt (fluxBound CG CS h) + fluxBound CG CS h) < ε := by
  have hc : Continuous fun h : ℝ => a * (Real.sqrt (fluxBound CG CS h) + fluxBound CG CS h) := by
    unfold fluxBound; fun_prop
  have h0 : (fun h : ℝ => a * (Real.sqrt (fluxBound CG CS h) + fluxBound CG CS h)) 0 = 0 := by
    simp [fluxBound]
  have ht : Tendsto (fun h : ℝ => a * (Real.sqrt (fluxBound CG CS h) + fluxBound CG CS h))
      (𝓝 0) (𝓝 0) := by
    have := hc.tendsto 0
    have h0' : a * (Real.sqrt (fluxBound CG CS 0) + fluxBound CG CS 0) = 0 := h0
    rwa [h0'] at this
  have h1 : ∀ᶠ h in 𝓝 (0 : ℝ), a * (Real.sqrt (fluxBound CG CS h) + fluxBound CG CS h) < ε :=
    ht.eventually (gt_mem_nhds hε)
  have h2 : ∀ᶠ h in 𝓝 (0 : ℝ), h < 1 := gt_mem_nhds one_pos
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2]
    with h hpos hsmall hlt
  exact ⟨hpos, hlt, hsmall⟩

/-- **`SmallChannelLeakage` from the three steps.** -/
theorem smallChannelLeakage_of (hS : OmittedFluxStart) (hG : OmittedFluxGrowth)
    (hL : LeakRecursion) : SmallChannelLeakage := by
  intro b hb0 hb E hE1 hE2 s T hs hsT q hq ε hε
  obtain ⟨CS, hCS⟩ := hS b hb0 hb E hE1 hE2 s hs
  obtain ⟨CG, hCG⟩ := hG b hb0 hb E hE1 hE2 s T hs hsT
  obtain ⟨CL, hCL⟩ := hL b hb0 hb E hE1 hE2 s T hs hsT q hq
  set K := max 1 (3 * CL / ε)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hCLK : CL / K ≤ ε / 3 := by
    rcases le_or_gt CL 0 with h | h
    · have : CL / K ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hK0.le
      linarith
    · rw [div_le_iff₀ hK0]
      have : 3 * CL / ε ≤ K := le_max_right _ _
      rw [div_le_iff₀ hε] at this
      linarith
  filter_upwards [eventually_small_bound CG CS (max CL 0 * K) (by positivity : 0 < ε / 3)]
    with h ⟨h0, h1, hsmall⟩
  filter_upwards [hCS h h0 h1, hCG h h0 h1 h h0, hCL K hK1 h h0 h1 (ε / 3) (by positivity)]
    with W hSW hGW hLW
  set x := fluxBound CG CS h
  have hx : 0 ≤ x := by unfold x fluxBound; positivity
  have hI0 : 0 ≤ ∫ ω, omittedFlux b E h s W ⌊(W : ℝ) * s⌋₊ ω ∂growthPathLaw W b :=
    integral_nonneg fun ω => omittedFlux_nonneg b E h s W _ ω
  have hflux : ∀ j : ℕ, ⌊(W : ℝ) * s⌋₊ ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
      ∫ ω, omittedFlux b E h s W j ω ∂growthPathLaw W b ≤ x := by
    intro j hj1 hj2
    refine (hGW j hj1 hj2).trans ?_
    have h1 : CG * ∫ ω, omittedFlux b E h s W ⌊(W : ℝ) * s⌋₊ ω ∂growthPathLaw W b ≤
        max CG 0 * (max CS 0 * h) := by
      refine (mul_le_mul_of_nonneg_right (le_max_left CG 0) hI0).trans
        (mul_le_mul_of_nonneg_left (hSW.trans ?_) (le_max_right _ _))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h0.le
    simp only [x, fluxBound]; linarith
  have hfin := hLW x hx hflux
  have hsx : 0 ≤ Real.sqrt x + x := by positivity
  have hmain : CL * K * (Real.sqrt x + x) ≤ max CL 0 * K * (Real.sqrt x + x) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hK0.le) hsx
  change ∫ ω, omittedLeak b E h s q W ⌊(W : ℝ) * T⌋₊ ω ∂growthPathLaw W b ≤ ε
  linarith

end BlockBand.SourceProcess.SmallLeak
