module

public import BlockBand.Endpoints.Response.BridgeOccupationProofVitali
public import BlockBand.Endpoints.Response.LifetimeBridgeParts

/-!
# `BridgeOccupationStatement` is false as formalized

`BridgeOccupationStatement` (the bridge occupation lemma as formalized) quantifies over **every**
`p` with `IsBaseDensity D₀ p`. `IsBaseDensity` constrains `p_t(z, ·)` off the closed strip only
through `∫⁻_B ofReal (p_t(z, ·)) = P(Z_t ∈ B)`, and `p_t(z', ·)` for `z'` off the strip not at
all. The occupation `bridgeMeanTotal` integrates
`ofReal(x'+y') p_s(z, z') p_{T-s}(z', 0) / p_T(z, 0)` over **all** `z' ∈ ℝ²`. For a
non-measurable `p` the first factor can be strictly positive off the strip while having zero
Lebesgue integral over every set (`bopPhi`), and the second factor can be its reciprocal. The
product is then `1` off the strip, and the occupation is `⊤`, contradicting the first conclusion
`bridgeOccupation … ≠ ⊤`.

**Proved here.**
* `bop_isBaseDensity_bad`: from any `IsBaseDensity D₀ q`, the modified version
  `bopBadVersion q` (equal to `q` on strip × strip, `bopPhi z'` for `z` in and `z'` off the strip,
  `(bopPhi z)⁻¹` for `z` off the strip) again satisfies `IsBaseDensity D₀`.
* `bop_bad_occupation_top`: its bridge occupation from any strip point is `⊤`.
* `not_bridgeOccupationStatement_of_isBaseDensity`: `IsBaseDensity D₀ q` for one `D₀ > 0` refutes
  `BridgeOccupationStatement`; in particular `not_bridgeOccupationStatement_of_lifetimeBridge`
  (`LifetimeBridgeStatement → ¬ BridgeOccupationStatement`), so the hypothesis pair `(hLB, hOcc)` of
  `nonzeroResponse` is inconsistent, and `not_bridgeOccupationStatement_of_lbk`
  (from `LbkSphereKernelPos`, `LbkBaseExistence`, `LbkBaseTransitionLaw` at one `D₀ > 0`).

The defect is the formal encoding (the statement "off the strip `ofReal p = 0` a.e." needs
measurability of `p_t(z, ·)`), not the lemma of the paper. A repaired statement with a
measurability hypothesis is in `BridgeOccupationProofDefs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

theorem bop_baseStrip_measurable : MeasurableSet baseStrip :=
  measurableSet_Ici.prod measurableSet_Icc

theorem bop_corner_mem : ((0 : ℝ), (0 : ℝ)) ∈ baseStrip :=
  ⟨le_refl (0 : ℝ), le_refl (0 : ℝ), zero_le_one⟩

theorem bop_bridgeStart_mem (r₀ : ℝ) : bridgeStart r₀ ∈ baseStrip := by
  refine ⟨?_, le_refl (0 : ℝ), zero_le_one⟩
  have := Real.one_le_cosh r₀
  show (0 : ℝ) ≤ (Real.cosh r₀ - 1) / 2
  linarith

/-- The one-time bridge density. -/
theorem bop_bridgeFdd_one {α : Type*} (p : ℝ → α → α → ℝ) (z e : α) (T s : ℝ)
    (zs : Fin 1 → α) :
    bridgeFddDensity p z e T ![s] zs =
      ENNReal.ofReal (p s z (zs 0)) * ENNReal.ofReal (p (T - s) (zs 0) e) /
        ENNReal.ofReal (p T z e) := by
  simp only [bridgeFddDensity, Fin.prod_univ_one, Fin.castSucc_zero, Fin.cons_zero,
    Matrix.cons_val_zero, sub_zero]
  rfl

open scoped Classical in
/-- **The bad version** of a base density: unchanged on strip × strip, `bopPhi z'` for `z` in the
strip and `z'` off it, and `(bopPhi z)⁻¹` for `z` off the strip. -/
def bopBadVersion (q : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (t : ℝ) (z z' : ℝ × ℝ) : ℝ :=
  if z ∈ baseStrip then (if z' ∈ baseStrip then q t z z' else bopPhi z') else (bopPhi z)⁻¹

/-- Off the strip, every base density has zero mass (the base diffusion stays in the strip). -/
theorem bop_lintegral_off_strip {D0 : ℝ} {q : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hq : IsBaseDensity D0 q)
    {t : NNReal} (ht : 0 < t) {z : ℝ × ℝ} (hz : z ∈ baseStrip) {B : Set (ℝ × ℝ)}
    (hB : MeasurableSet B) : ∫⁻ z' in B \ baseStrip, ENNReal.ofReal (q t z z') = 0 := by
  obtain ⟨Ω, m, 𝓖, P, Z, hZ⟩ := hq.exists_ z hz
  rw [← hq.law t ht z hz Ω m 𝓖 P Z hZ _ (hB.diff bop_baseStrip_measurable)]
  refine measure_mono_null (fun ω (hω : ω ∈ Z t ⁻¹' (B \ baseStrip)) => ?_) (ae_iff.1 hZ.paths)
  exact fun h => hω.2 (h.2 t)

theorem bop_isBaseDensity_bad {D0 : ℝ} {q : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hq : IsBaseDensity D0 q) :
    IsBaseDensity D0 (bopBadVersion q) where
  exists_ := hq.exists_
  nonneg := fun t ht z hz z' hz' => by
    simp only [bopBadVersion, hz, hz', ↓reduceIte]
    exact hq.nonneg t ht z hz z' hz'
  cont := fun t ht z hz => (hq.cont t ht z hz).congr fun z' hz' => by
    simp only [bopBadVersion, hz, hz', ↓reduceIte]
  law := by
    intro t ht z hz Ω m 𝓖 P Z hZ B hB
    rw [hq.law t ht z hz Ω m 𝓖 P Z hZ B hB,
      ← lintegral_inter_add_sdiff (fun z' => ENNReal.ofReal (q t z z')) B bop_baseStrip_measurable,
      ← lintegral_inter_add_sdiff (fun z' => ENNReal.ofReal (bopBadVersion q t z z')) B
        bop_baseStrip_measurable, bop_lintegral_off_strip hq ht hz hB]
    congr 1
    · refine setLIntegral_congr_fun (hB.inter bop_baseStrip_measurable) fun z' hz' => ?_
      simp only [bopBadVersion, hz, hz'.2, ↓reduceIte]
    · rw [setLIntegral_congr_fun (g := fun z' => ENNReal.ofReal (bopPhi z'))
        (hB.diff bop_baseStrip_measurable) fun z' hz' => by
          simp only [bopBadVersion, hz, hz'.2, ↓reduceIte]]
      exact (bop_setLIntegral_phi _).symm

/-- **The occupation density of the bad version is `⊤`** at every time. -/
theorem bop_bad_meanTotal_top (q : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) {z : ℝ × ℝ} (hz : z ∈ baseStrip)
    (T s : ℝ) : bridgeMeanTotal (bopBadVersion q) z T s = ⊤ := by
  set c : ℝ≥0∞ := ENNReal.ofReal (bopBadVersion q T z (0, 0)) with hc
  have hc0 : (1 : ℝ≥0∞) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨one_ne_zero, ENNReal.ofReal_ne_top⟩
  set U : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 1 with hU
  have hUm : MeasurableSet U := measurableSet_Ioi.prod measurableSet_Ioi
  have hle : ∀ zs : Fin 1 → ℝ × ℝ, U.indicator (fun _ => 1 / c) (zs 0) ≤
      ENNReal.ofReal ((zs 0).1 + (zs 0).2) * bridgeFddDensity (bopBadVersion q) z (0, 0) T ![s] zs := by
    intro zs
    by_cases hzU : zs 0 ∈ U
    · rw [indicator_of_mem hzU, bop_bridgeFdd_one]
      have hx : 0 < (zs 0).1 := hzU.1
      have hy : 1 < (zs 0).2 := hzU.2
      have hnS : zs 0 ∉ baseStrip := fun h => by linarith [h.2.2]
      have hnum : ENNReal.ofReal (bopBadVersion q s z (zs 0)) *
          ENNReal.ofReal (bopBadVersion q (T - s) (zs 0) (0, 0)) = 1 := by
        simp only [bopBadVersion, hz, hnS, ↓reduceIte]
        rw [← ENNReal.ofReal_mul (bop_phi_pos _).le, mul_inv_cancel₀ (bop_phi_pos _).ne',
          ENNReal.ofReal_one]
      rw [hnum, ← hc]
      have h1 : 1 ≤ ENNReal.ofReal ((zs 0).1 + (zs 0).2) := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
      calc 1 / c = 1 * (1 / c) := (one_mul _).symm
        _ ≤ ENNReal.ofReal ((zs 0).1 + (zs 0).2) * (1 / c) := by gcongr
    · rw [indicator_of_notMem hzU]
      exact zero_le
  have hvol : volume ((fun zs : Fin 1 → ℝ × ℝ => zs 0) ⁻¹' U) = ⊤ := by
    have := (volume_preserving_funUnique (Fin 1) (ℝ × ℝ)).measure_preimage hUm.nullMeasurableSet
    refine this.trans ?_
    rw [hU, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioi, Real.volume_Ioi,
      ENNReal.top_mul_top]
  have hpre : MeasurableSet ((fun zs : Fin 1 → ℝ × ℝ => zs 0) ⁻¹' U) :=
    hUm.preimage (measurable_pi_apply 0)
  unfold bridgeMeanTotal
  refine eq_top_iff.2 ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ zs : Fin 1 → ℝ × ℝ,
        ((fun zs : Fin 1 → ℝ × ℝ => zs 0) ⁻¹' U).indicator (fun _ => 1 / c) zs := by
        rw [lintegral_indicator_const hpre, hvol, ENNReal.mul_top hc0]
    _ ≤ _ := lintegral_mono fun zs => by
        rw [show ((fun zs : Fin 1 → ℝ × ℝ => zs 0) ⁻¹' U).indicator (fun _ => 1 / c) zs =
          U.indicator (fun _ => 1 / c) (zs 0) from rfl]
        exact hle zs

/-- **The bridge occupation of the bad version is `⊤`** on every nondegenerate interval. -/
theorem bop_bad_occupation_top (q : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) {z : ℝ × ℝ} (hz : z ∈ baseStrip)
    {T a b : ℝ} (hab : a < b) : bridgeOccupation (bopBadVersion q) z T a b = ⊤ := by
  unfold bridgeOccupation
  simp_rw [bop_bad_meanTotal_top q hz T]
  rw [setLIntegral_const, Real.volume_Ioo, ENNReal.top_mul]
  exact (ENNReal.ofReal_pos.2 (by linarith)).ne'

/-- **`BridgeOccupationStatement` is refuted by any base density**, at any one `D₀ > 0`. -/
theorem not_bridgeOccupationStatement_of_isBaseDensity {D0 : ℝ} (hD0 : 0 < D0)
    {q : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ} (hq : IsBaseDensity D0 q) : ¬ BridgeOccupationStatement := by
  intro h
  obtain ⟨c, -, C, -, r₁, H⟩ := h (D0 * 1) (by linarith)
  exact (H D0 1 hD0 one_pos rfl _ (bop_isBaseDensity_bad hq) r₁ le_rfl 1
    ⟨one_pos, le_rfl⟩).1 (bop_bad_occupation_top q (bop_bridgeStart_mem r₁) one_pos)

/-- **`LifetimeBridgeStatement → ¬ BridgeOccupationStatement`**: the two diffusion statements
assumed together by `nonzeroResponse` are jointly inconsistent. -/
theorem not_bridgeOccupationStatement_of_lifetimeBridge (hLB : LifetimeBridgeStatement) :
    ¬ BridgeOccupationStatement := by
  obtain ⟨p, hp, -⟩ := hLB 1 one_pos
  exact not_bridgeOccupationStatement_of_isBaseDensity one_pos hp

/-- The explicit kernel is a base density, given (i), (ii) and sphere positivity. -/
theorem bop_isBaseDensity_lbk {D0 : ℝ} (hD0 : 0 < D0) (hpos : LbkSphereKernelPos D0)
    (hex : LbkBaseExistence D0) (hlaw : LbkBaseTransitionLaw D0) :
    IsBaseDensity D0 (lbkKernel D0) :=
  ⟨hex, fun _ _ _ _ _ _ => lbk_kernel_nonneg hD0 hpos _ _ _,
    fun _ ht _ hz => lbk_kernel_continuousOn hD0 ht hz, hlaw⟩

/-- The refutation from the lifetime-bridge parts (i), (ii) and sphere positivity at one
`D₀ > 0`. -/
theorem not_bridgeOccupationStatement_of_lbk {D0 : ℝ} (hD0 : 0 < D0)
    (hpos : LbkSphereKernelPos D0) (hex : LbkBaseExistence D0) (hlaw : LbkBaseTransitionLaw D0) :
    ¬ BridgeOccupationStatement :=
  not_bridgeOccupationStatement_of_isBaseDensity hD0 (bop_isBaseDensity_lbk hD0 hpos hex hlaw)

end BlockBand.Endpoints
