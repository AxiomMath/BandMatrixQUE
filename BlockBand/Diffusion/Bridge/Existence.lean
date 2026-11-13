module

public import BlockBand.Diffusion.Bridge.ExistenceStatement
public import BlockBand.Diffusion.Bridge.Moments

/-!
# Existence of the base bridges: `BrLbkBridgeExistence`

`D₀ > 0`; Lebesgue measure on `ℝ × ℝ` and its finite powers; `S = exBaseStrip`.

* `bridgeFddDensity_brKernel`: for a start `z ∈ S`, the generic bridge density of the adapter
  `q′ = brKernel D0` equals, **pointwise**, the bridge density `brBridgeFddDensity` of
  `exKernel D0`: if all nodes lie in `S` the factors agree; otherwise the factor whose
  target is the first node off `S` vanishes on both sides.
* `isBrBaseBridge_of_isBridgeProcess`: the generic `IsBridgeProcess P volume q′ z (0,0) t Z`
  gives `IsBrBaseBridge P (exKernel D0) z t Z` field by field.
* **`brLbkBridgeExistence : ∀ D0 > 0, BrLbkBridgeExistence D0`** (the local copy
  `BrLbkBridgeExistence` of `LbkBridgeExistence`), on the canonical space `Ω = Ioo 0 t → ℝ × ℝ` (in `Type`), from the
  generic `exists_isBridgeProcess` with the Chapman–Kolmogorov identity
  `brKernel_chapmanKolmogorov`, the moment bound `brKernel_bridgeMomentBound` (`p = 4`, `γ = 2`)
  and corner positivity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The generic bridge density of the adapter is the bridge density `brBridgeFddDensity` of
`exKernel`, for starts in the strip. -/
theorem bridgeFddDensity_brKernel {D0 : ℝ} {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) (e : ℝ × ℝ)
    (t : ℝ) {k : ℕ} (ts : Fin k → ℝ) (zs : Fin k → ℝ × ℝ) :
    bridgeFddDensity (brKernel D0) z e t ts zs = brBridgeFddDensity (exKernel D0) z e t ts zs := by
  unfold bridgeFddDensity brBridgeFddDensity
  rw [brKernel_of_mem hz]
  by_cases hall : ∀ i, zs i ∈ exBaseStrip
  · have hc : ∀ j : Fin (k + 1), (Fin.cons z zs : Fin (k + 1) → ℝ × ℝ) j ∈ exBaseStrip := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa using hz
      · simpa using hall i
    rw [brKernel_of_mem (hc _)]
    congr 2
    exact Finset.prod_congr rfl fun i _ => brKernel_of_mem (hc _) _
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_univ j) ?_,
      Finset.prod_eq_zero (i := j) (Finset.mem_univ j) ?_]
    · simp
    · exact (congrArg ENNReal.ofReal (exKernel_of_notMem_right _ hj)).trans ENNReal.ofReal_zero
    · exact brKernel_of_notMem_right _ hj

/-- **Conversion** `IsBridgeProcess → IsBrBaseBridge` (field by field). -/
theorem isBrBaseBridge_of_isBridgeProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D0 t : ℝ} {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {Z : ℝ → Ω → ℝ × ℝ}
    (h : IsBridgeProcess P volume (brKernel D0) z (0, 0) t Z) :
    IsBrBaseBridge P (exKernel D0) z t Z where
  prob := h.prob
  meas := h.meas
  paths := h.paths
  fdd k ts hts hbd F hF := by
    rw [h.fdd k ts hts hbd F hF, volume_pi]
    simp_rw [bridgeFddDensity_brKernel hz]

/-- **Existence of the continuous base bridges** (the local copy `BrLbkBridgeExistence` of
`LbkBridgeExistence`): for every
`D₀ > 0`, every boundary start `(x, y)` and every `t > 0` there is a probability space carrying a
process with paths continuous on `[0, t]`, `Z₀ = (x, y)`, `Z_t = (0, 0)` a.s., and the
base-bridge finite-dimensional laws of `exKernel D0`. -/
theorem brLbkBridgeExistence : ∀ D0 : ℝ, 0 < D0 → BrLbkBridgeExistence D0 := by
  intro D0 hD0 x y hxy t ht
  have hz : (x, y) ∈ exBaseStrip := by
    have h1 := hxy.2.2.1 0
    have h2 := hxy.2.2.2.1 0
    simp only [Matrix.cons_val_zero] at h1 h2
    exact ⟨h1, h2.1, h2.2⟩
  obtain ⟨M, hM, hB⟩ := brKernel_bridgeMomentBound hD0 hz ht
  obtain ⟨P, Z, hPZ, -⟩ := exists_isBridgeProcess (ν := volume) (measurable_brKernel hD0)
    (brKernel_chapmanKolmogorov hD0) (brKernel_corner_pos hD0 ht hz) (brKernel_ne_top D0 t _ _)
    ht (by norm_num : (0 : ℝ) < 4) (by norm_num : (1 : ℝ) < 2) hM hB
  exact ⟨Ioo (0 : ℝ) t → ℝ × ℝ, inferInstance, P, Z, isBrBaseBridge_of_isBridgeProcess hz hPZ⟩

end BlockBand.Diffusion
