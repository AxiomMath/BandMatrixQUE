module

public import BlockBand.Endpoints.Response.LifetimeBridgeSplitLifetime

/-!
# The H-transform law from the corner heat identity, the Doob killed law and the Markov property

## Main results

* `lbkHTransformLaw_of_split (hD0) (h1) (h2) (h3) : LbkHTransformLaw D0` from
  `LbkCornerHeatIdentity`, `LbkDoobKilledLaw` and `LbkLifetimeMarkov`: the Markov step with the
  lifetime functional supplied by `lbk_lifetime_law_of_split` (from the first two), the killed law
  applied to `F(zs) Λ(z_k)`, and the telescoping `(D₀/2)H(z_k)⁻¹ · (x+y)H(z_k) = (D₀/2)(x+y)` off
  the Lebesgue-null set `{z_k = (0,0)}` (off the strip the kernel string vanishes);
* `lbkParts_of_split`, `lifetimeBridge_of_split : (∀ D₀ > 0, LbkSplitParts D₀) →
  LifetimeBridgeStatement`, as in `lifetimeBridge_of_parts`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### Support of the kernel string
-/

theorem lbk_kernel_ne_zero_mem {D0 t : ℝ} {w w' : ℝ × ℝ} (h : lbkKernel D0 t w w' ≠ 0) :
    w' ∈ baseStrip := by
  by_contra hw'
  apply h
  simp only [baseStrip, mem_prod, mem_Ici, not_and_or] at hw'
  rcases hw' with hx | hy
  · simp [lbkKernel, lbkKernelX, hx]
  · simp [lbkKernel, lbkKernelY, hy]

/-- If the string of transition densities does not vanish, its last point lies in the strip. -/
theorem lbk_lastPoint_mem_of_fddProd_ne_zero {D0 : ℝ} {z : ℝ × ℝ} (hz : z ∈ baseStrip) {k : ℕ}
    {ts : Fin k → ℝ} {zs : Fin k → ℝ × ℝ} (h : lbkFddProd (lbkKernel D0) z ts zs ≠ 0) :
    lbkLastPoint z zs ∈ baseStrip := by
  cases k with
  | zero => simpa [lbkLastPoint] using hz
  | succ m =>
    simp only [lbkLastPoint, ← Fin.succ_last, Fin.cons_succ]
    have := (Finset.prod_ne_zero_iff.1 h) (Fin.last m) (Finset.mem_univ _)
    exact lbk_kernel_ne_zero_mem (ENNReal.ofReal_ne_zero_iff.1 this).ne'

/-- The last point avoids the corner for a.e. `zs`. -/
theorem lbk_ae_lastPoint_ne {z : ℝ × ℝ} (hz : z ≠ (0, 0)) {k : ℕ} :
    ∀ᵐ zs ∂(volume : Measure (Fin k → ℝ × ℝ)), lbkLastPoint z zs ≠ (0, 0) := by
  cases k with
  | zero => exact ae_of_all _ fun zs => by simpa [lbkLastPoint] using hz
  | succ m =>
    rw [ae_iff]
    have hnull : (volume : Measure (Fin (m + 1) → ℝ × ℝ))
        (Function.eval (Fin.last m) ⁻¹' {((0, 0) : ℝ × ℝ)}) = 0 := by
      rw [MeasureTheory.volume_pi]
      exact Measure.pi_eval_preimage_null _ (measure_singleton _)
    refine measure_mono_null (fun zs hzs => ?_) hnull
    simp only [mem_ofPred_eq, not_not, lbkLastPoint, ← Fin.succ_last, Fin.cons_succ] at hzs
    simpa using hzs

/-- The event `{t_i < σ₀ ∀ i}` is `{t_k < σ₀}` once `σ₀ > 0`. -/
theorem lbk_forall_lt_iff_last {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) {σ : ℝ≥0∞}
    (hσ : 0 < σ) : (∀ i, ENNReal.ofReal (ts i) < σ) ↔ ENNReal.ofReal (lbkLastTime ts) < σ := by
  cases k with
  | zero => simp [lbkLastTime, hσ]
  | succ m =>
    simp only [lbkLastTime, ← Fin.succ_last, Fin.cons_succ]
    exact ⟨fun h => h _, fun h i =>
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hts.monotone (Fin.le_last i))) h⟩

/-!
### The assembly
-/

/-- The remaining-lifetime functional `Λ(w) = ∫_{(0,∞)} g(T + s) (D₀/2)(w₁ + w₂) p_s(w, 0) ds`
(the lifetime law from `w` applied to `g(T + ·)`). -/
def lbkRemainingLifetime (D0 : ℝ) (g : ℝ → ℝ≥0∞) (T : ℝ) (w : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, g (T + s) * ENNReal.ofReal (D0 / 2 * (w.1 + w.2) * lbkKernel D0 s w (0, 0))

theorem lbk_remainingLifetime_measurable {D0 : ℝ} (hD0 : 0 < D0) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (T : ℝ) : Measurable (lbkRemainingLifetime D0 g T) := by
  have hk : Measurable fun q : (ℝ × ℝ) × ℝ => lbkKernel D0 q.2 q.1 (0, 0) :=
    (lbk_kernel_measurable hD0).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.2, q.1, ((0, 0) : ℝ × ℝ)))
      (measurable_snd.prodMk (measurable_fst.prodMk measurable_const))
  have hf : Measurable fun q : (ℝ × ℝ) × ℝ =>
      g (T + q.2) * ENNReal.ofReal (D0 / 2 * (q.1.1 + q.1.2) * lbkKernel D0 q.2 q.1 (0, 0)) :=
    (hg.comp (measurable_const.add measurable_snd)).mul
      ((measurable_const.mul (measurable_fst.fst.add measurable_fst.snd)).mul hk).ennreal_ofReal
  exact hf.lintegral_prod_right'

/-- The telescoping `Λ(w) · (x + y)H(w) = (D₀/2)(x + y) ∫ g(T + s) p_s(w, 0) ds` for `w` in the
strip off the corner. -/
theorem lbk_remainingLifetime_telescope {D0 : ℝ} (hD0 : 0 < D0) (g : ℝ → ℝ≥0∞) (T : ℝ)
    {x y : ℝ} (hs : 0 < x + y) {w : ℝ × ℝ} (hw : 0 < w.1 + w.2) :
    lbkRemainingLifetime D0 g T w * ENNReal.ofReal ((x + y) * lbkHarm w) =
      ENNReal.ofReal (D0 / 2 * (x + y)) *
        ∫⁻ s in Ioi 0, g (T + s) * ENNReal.ofReal (lbkKernel D0 s w (0, 0)) := by
  have hc : 0 ≤ D0 / 2 * (w.1 + w.2) := by positivity
  have hΛ : lbkRemainingLifetime D0 g T w = ENNReal.ofReal (D0 / 2 * (w.1 + w.2)) *
      ∫⁻ s in Ioi 0, g (T + s) * ENNReal.ofReal (lbkKernel D0 s w (0, 0)) := by
    rw [lbkRemainingLifetime, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [ENNReal.ofReal_mul hc]
    ring
  have hk : ENNReal.ofReal (D0 / 2 * (w.1 + w.2)) * ENNReal.ofReal ((x + y) * lbkHarm w) =
      ENNReal.ofReal (D0 / 2 * (x + y)) := by
    rw [← ENNReal.ofReal_mul hc, lbkHarm]
    congr 1
    field_simp
  rw [hΛ, mul_right_comm, hk]

/-- The corner heat identity, the Doob killed law and the Markov property at `t_k` imply
`LbkHTransformLaw`. -/
theorem lbkHTransformLaw_of_split {D0 : ℝ} (hD0 : 0 < D0) (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) (h3 : LbkLifetimeMarkov D0) : LbkHTransformLaw D0 := by
  classical
  intro x y hxy Ω m 𝓖 P N X Y hP k ts hts htp g hg F hF
  obtain ⟨hz, hz0, hs⟩ := lbk_isDualStart_strip hxy
  set T := lbkLastTime ts with hT
  set Λ := lbkRemainingLifetime D0 g T with hΛdef
  have hpos := lbk_extinction_pos_ae h2 hxy hP
  have hgT : Measurable fun s => g (T + s) := hg.comp (measurable_const.add measurable_id)
  -- the event `{t_i < σ₀ ∀ i}` is `{t_k < σ₀}` a.s., and `g(σ₀) = g(T + (σ₀ - T))`
  have hstep1 : ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < dualExtinction N ω
        then g (dualExtinction N ω).toReal * F (fun i => dualPoint X Y (ts i) ω) else 0) ∂P =
      ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ENNReal.ofReal T < dualExtinction N ω
        then F (fun i => dualPoint X Y (ts i) ω) * g (T + ((dualExtinction N ω).toReal - T))
        else 0) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hpos] with ω hω
    have he := lbk_forall_lt_iff_last hts hω
    by_cases hc : dualExtinction N ω < ⊤ ∧ ENNReal.ofReal T < dualExtinction N ω
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hc.1, he.2 hc.2⟩),
        ite_eq_left_of_eq_true _ _ (eq_true hc),
        add_sub_cancel, mul_comm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hc ⟨h.1, he.1 h.2⟩),
        ite_eq_right_of_eq_false _ _ (eq_false hc)]
  -- the Markov property at `t_k`, with the lifetime law from every start
  have hΛ : ∀ a b : ℝ, IsDualStart ![a] ![b] →
      ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (P' : Measure Ω')
        (N' : ℝ≥0 → Ω' → ℕ) (X' Y' : ℝ≥0 → Ω' → ℕ → ℝ),
        IsBoundaryDualProcess P' 𝓖' D0 ![a] ![b] N' X' Y' →
        ∫⁻ ω', (if dualExtinction N' ω' < ⊤ then g (T + (dualExtinction N' ω').toReal) else 0)
          ∂P' = Λ (a, b) := fun a b hab Ω' m' 𝓖' P' N' X' Y' hP' =>
    lbk_lifetime_law_of_split hD0 h1 h2 hab hP' hgT
  have hstep2 := h3 x y hxy Ω m 𝓖 P N X Y hP k ts hts htp (fun s => g (T + s)) hgT Λ hΛ F hF
  -- the killed law applied to `F(zs) Λ(z_k)`
  have hFΛ : Measurable fun zs : Fin k → ℝ × ℝ => F zs * Λ (lbkLastPoint (x, y) zs) :=
    hF.mul ((lbk_remainingLifetime_measurable hD0 hg T).comp (lbk_measurable_cons _ _))
  have hstep3 := h2 x y hxy Ω m 𝓖 P N X Y hP k ts hts htp _ hFΛ
  rw [hstep1, hstep2, hstep3, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the telescoping, off the null set `{z_k = (0,0)}`
  refine lintegral_congr_ae ?_
  filter_upwards [lbk_ae_lastPoint_ne (k := k) hz0] with zs hzs
  by_cases hPi : lbkFddProd (lbkKernel D0) (x, y) ts zs = 0
  · simp [hPi]
  have hw := lbk_lastPoint_mem_of_fddProd_ne_zero hz hPi
  have hw0 : 0 < (lbkLastPoint (x, y) zs).1 + (lbkLastPoint (x, y) zs).2 := by
    have ha : 0 ≤ (lbkLastPoint (x, y) zs).1 := hw.1
    have hb : 0 ≤ (lbkLastPoint (x, y) zs).2 := hw.2.1
    rcases (add_nonneg ha hb).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hzs
      exact Prod.ext (by linarith) (by linarith)
  have htel := lbk_remainingLifetime_telescope hD0 g T hs hw0
  calc F zs * Λ (lbkLastPoint (x, y) zs) * lbkFddProd (lbkKernel D0) (x, y) ts zs *
        ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs))
      = F zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
          (Λ (lbkLastPoint (x, y) zs) *
            ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs))) := by ring
    _ = _ := by rw [hΛdef, htel]; ring

/-- `LbkParts` from the split parts. -/
theorem lbkParts_of_split {D0 : ℝ} (hD0 : 0 < D0) (h : LbkSplitParts D0) : LbkParts D0 :=
  ⟨h.spherePos, h.existence, h.transition,
    lbkHTransformLaw_of_split hD0 h.cornerHeat h.doob h.markov, h.bridge⟩

/-- The lifetime-bridge lemma from the split parts, as in `lifetimeBridge_of_parts`:
`LbkHTransformLaw` is replaced by the corner heat identity (analytic, about `lbkKernel`), the Doob
killed law and the Markov property at `t_k`. -/
theorem lifetimeBridge_of_split (h : ∀ D0 : ℝ, 0 < D0 → LbkSplitParts D0) :
    LifetimeBridgeStatement :=
  lifetimeBridge_of_parts fun D0 hD0 => lbkParts_of_split hD0 (h D0 hD0)

end BlockBand.Endpoints
