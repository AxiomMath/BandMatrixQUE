module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Increment
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Elementary stochastic integral processes

Setting: `(Ω, m₀, Q)`, raw filtration `𝓖`, horizon `T`, an arbitrary process `X` (applied to
the continuous integrator `N` for path properties and to its martingale modification `M` for
moments). Simple predictable integrands are formal combinations `x : Rect 𝓖 T →₀ ℝ` of
rectangles `r = (s,t] × A`.

* `rectProc X r u = 1_A (X_{s ∨ (u ∧ t)} - X_s)`, the integral of `1_r` against `X` on
  `(0,u]`; `elemProc X x` is its linear extension.
* `elemProc_continuous`: continuous in `u` wherever `X` has a continuous path.
* `elemProc_ae`: modifications of `X` give modifications.
* `elemProc_martingale`: for a martingale `X`, `elemProc X x` is a martingale.
* `Rect.restrict r q₁ q₂ C` (`q₁ ≤ q₂ ≤ T`, `C ∈ 𝓖_{q₁}`) is the rectangle
  `r ∩ ((q₁,q₂] × C)`; `elemProc_restrict`: the terminal value of the restricted integrand is
  `1_C (elemProc X x q₂ - elemProc X x q₁)`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 mΩ} {T : ℝ≥0}

/-- The clamped time `s ∨ (u ∧ t)`. -/
def Rect.clamp (r : Rect 𝓖 T) (u : ℝ≥0) : ℝ≥0 := max r.s (min u r.t)

theorem Rect.clamp_T (r : Rect 𝓖 T) : r.clamp T = r.t := by
  simp [Rect.clamp, min_eq_right r.htT, r.hst]

theorem Rect.continuous_clamp (r : Rect 𝓖 T) : Continuous r.clamp :=
  continuous_const.max (continuous_id.min continuous_const)

theorem Rect.clamp_mono (r : Rect 𝓖 T) : Monotone r.clamp :=
  fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

/-- Integral of the rectangle `r` against `X` on `(0,u]`. -/
def rectProc (X : ℝ≥0 → Ω → ℝ) (r : Rect 𝓖 T) (u : ℝ≥0) (ω : Ω) : ℝ :=
  r.A.indicator (fun ω => X (r.clamp u) ω - X r.s ω) ω

/-- Integral of the simple predictable integrand `x` against `X` on `(0,u]`. -/
def elemProc (X : ℝ≥0 → Ω → ℝ) : (Rect 𝓖 T →₀ ℝ) →ₗ[ℝ] (ℝ≥0 → Ω → ℝ) :=
  Finsupp.linearCombination ℝ (rectProc X)

theorem elemProc_apply (X : ℝ≥0 → Ω → ℝ) (x : Rect 𝓖 T →₀ ℝ) (u : ℝ≥0) (ω : Ω) :
    elemProc X x u ω = x.sum fun r c => c * rectProc X r u ω := by
  simp [elemProc, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]

@[simp] theorem elemProc_single (X : ℝ≥0 → Ω → ℝ) (r : Rect 𝓖 T) (c : ℝ) :
    elemProc X (Finsupp.single r c) = c • rectProc X r := by
  simp [elemProc]

theorem rectProc_T (X : ℝ≥0 → Ω → ℝ) (r : Rect 𝓖 T) :
    rectProc X r T = r.A.indicator fun ω => X r.t ω - X r.s ω := by
  funext ω; simp [rectProc, Rect.clamp_T]

theorem Rect.clamp_of_le (r : Rect 𝓖 T) {u : ℝ≥0} (hu : T ≤ u) : r.clamp u = r.t := by
  simp [Rect.clamp, min_eq_right (r.htT.trans hu), r.hst]

/-- Elementary integrals are constant after the horizon `T`. -/
theorem elemProc_of_le (X : ℝ≥0 → Ω → ℝ) (x : Rect 𝓖 T →₀ ℝ) {u : ℝ≥0} (hu : T ≤ u) :
    elemProc X x u = elemProc X x T := by
  funext ω
  simp only [elemProc_apply, rectProc, Rect.clamp_of_le _ hu, Rect.clamp_T]

theorem rectProc_continuous {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : Continuous fun t => X t ω)
    (r : Rect 𝓖 T) : Continuous fun u => rectProc X r u ω := by
  by_cases hA : ω ∈ r.A
  · simp only [rectProc, indicator_of_mem hA]
    exact (hω.comp r.continuous_clamp).sub continuous_const
  · simp only [rectProc, indicator_of_notMem hA]
    exact continuous_const

theorem elemProc_continuous {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : Continuous fun t => X t ω)
    (x : Rect 𝓖 T →₀ ℝ) : Continuous fun u => elemProc X x u ω := by
  simp only [elemProc_apply, Finsupp.sum]
  exact continuous_finsetSum _ fun r _ => continuous_const.mul (rectProc_continuous hω r)

theorem rectProc_ae {X Y : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} (hXY : ∀ t, X t =ᵐ[Q] Y t)
    (r : Rect 𝓖 T) (u : ℝ≥0) : rectProc X r u =ᵐ[Q] rectProc Y r u := by
  filter_upwards [hXY (r.clamp u), hXY r.s] with ω h1 h2
  by_cases hA : ω ∈ r.A <;> simp [rectProc, hA, h1, h2]

theorem elemProc_ae {X Y : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} (hXY : ∀ t, X t =ᵐ[Q] Y t)
    (x : Rect 𝓖 T →₀ ℝ) (u : ℝ≥0) : elemProc X x u =ᵐ[Q] elemProc Y x u := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply]
      exact hx.add hy
  | single r c =>
      simp only [elemProc_single, Pi.smul_apply]
      exact (rectProc_ae hXY r u).const_smul c

/-- A martingale criterion from set integrals (adapted, integrable, `∫_B X_v = ∫_B X_u`). -/
theorem martingale_of_setIntegral {Q : Measure Ω} [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    (hadp : ∀ t, StronglyMeasurable[𝓖 t] (X t)) (hint : ∀ t, Integrable (X t) Q)
    (hset : ∀ u v, u ≤ v → ∀ B, MeasurableSet[𝓖 u] B →
      ∫ ω in B, X v ω ∂Q = ∫ ω in B, X u ω ∂Q) : Martingale X 𝓖 Q :=
  ⟨hadp, fun i j hij => (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) (fun s hs _ => (hset i j hij s hs).symm)
    (hadp i).aestronglyMeasurable).symm⟩

theorem rectProc_martingale {Q : Measure Ω} [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓖 Q) (r : Rect 𝓖 T) : Martingale (rectProc X r) 𝓖 Q := by
  refine martingale_of_setIntegral (fun u => ?_) (fun u => ?_) ?_
  · by_cases hu : r.s ≤ u
    · have hc : r.clamp u ≤ u := max_le hu (min_le_left _ _)
      exact (((hX.stronglyMeasurable _).mono (𝓖.mono hc)).sub
        ((hX.stronglyMeasurable _).mono (𝓖.mono hu))).indicator (𝓖.mono hu _ r.hA)
    · have hc : r.clamp u = r.s := max_eq_left ((min_le_left _ _).trans (le_of_not_ge hu))
      have : rectProc X r u = fun _ => 0 := by funext ω; simp [rectProc, hc]
      rw [this]; exact stronglyMeasurable_const
  · exact ((hX.integrable _).sub (hX.integrable _)).indicator (𝓖.le _ _ r.hA)
  · intro u v huv B hB
    have hAm : MeasurableSet r.A := 𝓖.le _ _ r.hA
    have hBm : MeasurableSet B := 𝓖.le _ _ hB
    have key : ∫ ω in B ∩ r.A, X (r.clamp v) ω ∂Q = ∫ ω in B ∩ r.A, X (r.clamp u) ω ∂Q := by
      by_cases hut : u ≤ r.t
      · have hcu : r.clamp u = max r.s u := by simp [Rect.clamp, min_eq_left hut]
        have hmeas : MeasurableSet[𝓖 (r.clamp u)] (B ∩ r.A) := by
          rw [hcu]
          exact (𝓖.mono (le_max_right _ _) _ hB).inter (𝓖.mono (le_max_left _ _) _ r.hA)
        exact (hX.setIntegral_eq (r.clamp_mono huv) hmeas).symm
      · have h1 : r.clamp u = r.t := by
          simp only [Rect.clamp, min_eq_right (not_le.1 hut).le, max_eq_right r.hst]
        have h2 : r.clamp v = r.t := by
          simp only [Rect.clamp, min_eq_right ((not_le.1 hut).le.trans huv), max_eq_right r.hst]
        rw [h1, h2]
    simp only [rectProc]
    rw [setIntegral_indicator hAm, setIntegral_indicator hAm,
      integral_sub (hX.integrable _).integrableOn (hX.integrable _).integrableOn,
      integral_sub (hX.integrable _).integrableOn (hX.integrable _).integrableOn, key]

theorem elemProc_martingale {Q : Measure Ω} [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓖 Q) (x : Rect 𝓖 T →₀ ℝ) : Martingale (elemProc X x) 𝓖 Q := by
  induction x using Finsupp.induction_linear with
  | zero => simpa using martingale_zero (E := ℝ) 𝓖 Q
  | add x y hx hy => simpa using hx.add hy
  | single r c => simpa using (rectProc_martingale hX r).smul c

theorem rectProc_memLp {Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 Q)
    (r : Rect 𝓖 T) (u : ℝ≥0) : MemLp (rectProc X r u) 2 Q :=
  ((hX _).sub (hX _)).indicator (𝓖.le _ _ r.hA).nullMeasurableSet

theorem elemProc_memLp {Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, MemLp (X t) 2 Q)
    (x : Rect 𝓖 T →₀ ℝ) (u : ℝ≥0) : MemLp (elemProc X x u) 2 Q := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using hx.add hy
  | single r c => simpa using (rectProc_memLp hX r u).const_smul c

/-!
### Restriction of rectangles to `(q₁, q₂] × C`
-/

/-- The rectangle `r ∩ ((q₁,q₂] × C)`, for `q₁ ≤ q₂ ≤ T` and `C ∈ 𝓖_{q₁}`. -/
def Rect.restrict (r : Rect 𝓖 T) {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T) {C : Set Ω}
    (hC : MeasurableSet[𝓖 q₁] C) : Rect 𝓖 T where
  s := max r.s q₁
  t := max (max r.s q₁) (min r.t q₂)
  A := r.A ∩ C
  hst := le_max_left _ _
  htT := max_le (max_le (r.hst.trans r.htT) (hq.trans hqT)) ((min_le_right _ _).trans hqT)
  hA := (𝓖.mono (le_max_left _ _) _ r.hA).inter (𝓖.mono (le_max_right _ _) _ hC)

theorem Rect.restrict_set (r : Rect 𝓖 T) {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T)
    {C : Set Ω} (hC : MeasurableSet[𝓖 q₁] C) :
    (r.restrict hq hqT hC).set = r.set ∩ (Ioc (q₁ : ℝ) q₂ ×ˢ C) := by
  simp only [Rect.set, Rect.restrict, prod_inter_prod, Ioc_inter_Ioc]
  congr 1
  ext x
  simp only [mem_Ioc, NNReal.coe_max, NNReal.coe_min]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases le_max_iff.1 h2 with h | h
    · exact absurd h (not_le.2 h1)
    · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_max_of_le_right h2⟩

theorem rectProc_restrict (X : ℝ≥0 → Ω → ℝ) (r : Rect 𝓖 T) {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂)
    (hqT : q₂ ≤ T) {C : Set Ω} (hC : MeasurableSet[𝓖 q₁] C) (ω : Ω) :
    rectProc X (r.restrict hq hqT hC) T ω =
      C.indicator (fun ω => rectProc X r q₂ ω - rectProc X r q₁ ω) ω := by
  rw [rectProc_T]
  by_cases hω : ω ∈ r.A ∩ C
  · have hA : ω ∈ r.A := hω.1
    have hCω : ω ∈ C := hω.2
    change (r.A ∩ C).indicator _ ω = _
    rw [indicator_of_mem hω, indicator_of_mem hCω]
    simp only [rectProc, indicator_of_mem hA, Rect.restrict, Rect.clamp]
    by_cases h1 : q₁ ≤ r.t
    · rw [min_eq_left h1]
      have : max (max r.s q₁) (min r.t q₂) = max r.s (min q₂ r.t) := by
        rw [min_comm]
        rcases le_total q₂ r.t with h | h
        · rw [min_eq_left h, max_assoc, max_eq_right hq]
        · rw [min_eq_right h, max_eq_right (max_le r.hst h1), max_eq_right r.hst]
      rw [this]; ring
    · have h1' : r.t ≤ q₁ := (not_le.1 h1).le
      rw [min_eq_right h1', min_eq_right (h1'.trans hq),
        max_eq_left (h1'.trans (le_max_right _ _) |>.trans' (min_le_left _ _))]
      ring
  · change (r.A ∩ C).indicator _ ω = _
    rw [indicator_of_notMem hω]
    by_cases hCω : ω ∈ C
    · have hA : ω ∉ r.A := fun h => hω ⟨h, hCω⟩
      simp [rectProc, indicator_of_mem hCω, indicator_of_notMem hA]
    · simp [indicator_of_notMem hCω]

/-- Linear restriction of simple integrands to `(q₁, q₂] × C`. -/
def restrictLin {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T) {C : Set Ω}
    (hC : MeasurableSet[𝓖 q₁] C) : (Rect 𝓖 T →₀ ℝ) →ₗ[ℝ] (Rect 𝓖 T →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ fun r => r.restrict hq hqT hC

theorem elemProc_restrict (X : ℝ≥0 → Ω → ℝ) {q₁ q₂ : ℝ≥0} (hq : q₁ ≤ q₂) (hqT : q₂ ≤ T)
    {C : Set Ω} (hC : MeasurableSet[𝓖 q₁] C) (x : Rect 𝓖 T →₀ ℝ) :
    elemProc X (restrictLin hq hqT hC x) T =
      C.indicator fun ω => elemProc X x q₂ ω - elemProc X x q₁ ω := by
  induction x using Finsupp.induction_linear with
  | zero => funext ω; simp
  | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, hx, hy]
      funext ω
      by_cases hω : ω ∈ C <;> simp [hω]; ring
  | single r c =>
      funext ω
      simp only [restrictLin, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        elemProc_single, Pi.smul_apply, smul_eq_mul, rectProc_restrict]
      by_cases hω : ω ∈ C <;> simp [hω]; ring

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
