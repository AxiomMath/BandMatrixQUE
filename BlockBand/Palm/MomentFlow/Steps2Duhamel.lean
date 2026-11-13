module

public import BlockBand.Palm.MomentFlow.MultiMat
public import BlockBand.Palm.RelativeLocalizationExist
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The propagator by duality, and the localized Duhamel bound

Instead of a two-parameter propagator, the row `ζ ↦ U_{v,u}(ξ, ζ)` is realised as a **backward
solution** `w(v, ·)` of the moment flow with `w(u, ·) = δ_ξ` (`IsBackwardMomentFlow`). Since the
moment generator is symmetric for the counting measure (`sum_mul_momentGenerator_symm`),
`v ↦ Σ_ζ w(v,ζ)Φ(v,ζ)` has derivative `Σ_ζ w(v,ζ)h(v,ζ)` along every forward solution of
`∂Φ = 𝓑Φ + h`. This gives:

* `backward_pairing` (**Duhamel by duality**): `Σ w(u)Φ(u) - Σ w(s)Φ(s) = ∫_s^u Σ_ζ w(v,ζ)h(v,ζ) dv`.
* `exists_backward` (existence for rates continuous on `[s,u]`, by time reversal of
  `forwardMass_exists` on the enumerated sector `cfgMat`).
* `IsBackwardMomentFlow.reverse`, `.nonneg`, `.mass_eq`, `.represent`: positivity, conservation
  of `Σ_ζ w(v,ζ)` (so `w(v,·)` is a probability vector when `w(u,·) = δ_ξ`), and
  `Σ_ζ w(v,ζ)f(ζ) = Φ_f(u,ξ)` for the forward solution `Φ_f` started at time `v` from `f`
  (the tails of `w` are identified with the finite-speed quantities by `tail_eq_forward`).
* **`duhamel_localized`**: if `F` solves the full flow, `g` the short flow with `g(s) = F(s)`,
  `|(𝓑 - 𝓢)F| ≤ e` on a set `W` of configurations and `≤ K` on the sector, then
  `|F(u,ξ) - g(u,ξ)| ≤ e(u - s) + K ∫_s^u Σ_{ζ ∉ W} w(v,ζ) dv`.
* `continuousOn_momentGenerator`: `(𝓑_{c(v)}F(v))(ξ)` is continuous on `[s,u]` when `c` and the
  sector values of `F` are.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory intervalIntegral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.RelativeLocalization

variable {N : ℕ}

/-- `w` solves the backward moment flow `∂_v w = -𝓑_{c(v)} w` on `[s,u]` (sector `r`). -/
def IsBackwardMomentFlow (c : ℝ → Fin N → Fin N → ℝ) (r : ℕ) (s u : ℝ)
    (w : ℝ → Occ N → ℝ) : Prop :=
  ∀ ξ ∈ sector N r, ContinuousOn (fun v => w v ξ) (Icc s u) ∧
    ∀ v ∈ Ioo s u, HasDerivAt (fun v => w v ξ) (-momentGenerator (c v) (w v) ξ) v

theorem IsBackwardMomentFlow.mono {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u s' : ℝ}
    {w : ℝ → Occ N → ℝ} (hw : IsBackwardMomentFlow c r s u w) (hs : s ≤ s') :
    IsBackwardMomentFlow c r s' u w := fun ξ hξ =>
  ⟨(hw ξ hξ).1.mono (Icc_subset_Icc_left hs),
    fun v hv => (hw ξ hξ).2 v ⟨lt_of_le_of_lt hs hv.1, hv.2⟩⟩

theorem IsMomentFlowSolution.mono_right {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u u' : ℝ}
    {Φ : ℝ → Occ N → ℝ} (hΦ : IsMomentFlowSolution c r s u Φ) (hu : u' ≤ u) :
    IsMomentFlowSolution c r s u' Φ := fun ξ hξ =>
  ⟨(hΦ ξ hξ).1.mono (Icc_subset_Icc_right hu),
    fun v hv => (hΦ ξ hξ).2 v ⟨hv.1, lt_of_lt_of_le hv.2 hu⟩⟩

theorem IsMomentFlowSolution.mono_left {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u s' : ℝ}
    {Φ : ℝ → Occ N → ℝ} (hΦ : IsMomentFlowSolution c r s u Φ) (hs : s ≤ s') :
    IsMomentFlowSolution c r s' u Φ := fun ξ hξ =>
  ⟨(hΦ ξ hξ).1.mono (Icc_subset_Icc_left hs),
    fun v hv => (hΦ ξ hξ).2 v ⟨lt_of_le_of_lt hs hv.1, hv.2⟩⟩

/-- **Duhamel by duality.** -/
theorem backward_pairing {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ} (hsu : s ≤ u)
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {Φ w h : ℝ → Occ N → ℝ}
    (hΦc : ∀ ξ ∈ sector N r, ContinuousOn (fun v => Φ v ξ) (Icc s u))
    (hΦd : ∀ ξ ∈ sector N r, ∀ v ∈ Ioo s u,
      HasDerivAt (fun v => Φ v ξ) (momentGenerator (c v) (Φ v) ξ + h v ξ) v)
    (hw : IsBackwardMomentFlow c r s u w)
    (hh : ∀ ξ ∈ sector N r, ContinuousOn (fun v => h v ξ) (Icc s u)) :
    ∑ ξ ∈ sector N r, w u ξ * Φ u ξ - ∑ ξ ∈ sector N r, w s ξ * Φ s ξ =
      ∫ v in s..u, ∑ ξ ∈ sector N r, w v ξ * h v ξ := by
  symm
  refine integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v => ∑ ξ ∈ sector N r, w v ξ * Φ v ξ) hsu ?_ (fun v hv => ?_) ?_
  · exact continuousOn_finsetSum _ fun ξ hξ => ((hw ξ hξ).1.mul (hΦc ξ hξ))
  · have hd : HasDerivAt (fun v => ∑ ξ ∈ sector N r, w v ξ * Φ v ξ)
        (∑ ξ ∈ sector N r, ((-momentGenerator (c v) (w v) ξ) * Φ v ξ +
          w v ξ * (momentGenerator (c v) (Φ v) ξ + h v ξ))) v :=
      HasDerivAt.fun_sum fun ξ hξ => ((hw ξ hξ).2 v hv).mul (hΦd ξ hξ v hv)
    convert hd using 1
    have hD5 := sum_mul_momentGenerator_symm (hsym v hv) r (Φ v) (w v)
    simp only [neg_mul, mul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hD5]
    have : ∑ ξ ∈ sector N r, momentGenerator (c v) (w v) ξ * Φ v ξ =
        ∑ ξ ∈ sector N r, Φ v ξ * momentGenerator (c v) (w v) ξ :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [this]; ring
  · exact (continuousOn_finsetSum _ fun ξ hξ => ((hw ξ hξ).1.mul (hh ξ hξ))).intervalIntegrable_of_Icc
      hsu

theorem continuousOn_cfgMat {c : ℝ → Fin N → Fin N → ℝ} {S : Set ℝ} (hc : ContinuousOn c S)
    (r : ℕ) : ContinuousOn (fun x => cfgMat (c x) r) S :=
  (continuous_cfgMat_comp continuous_id r).comp_continuousOn hc

/-- **Existence of backward solutions** for rates continuous on `[s,u]`. -/
theorem exists_backward {c : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} (hsu : s ≤ u)
    (hc : ContinuousOn c (Icc s u)) (r : ℕ) (f : Occ N → ℝ) :
    ∃ w : ℝ → Occ N → ℝ, IsBackwardMomentFlow c r s u w ∧ ∀ ξ ∈ sector N r, w u ξ = f ξ := by
  set ρ : ℝ → ℝ := fun t => s + u - t
  have hρc : Continuous ρ := by fun_prop
  have hρmaps : MapsTo ρ (Icc s u) (Icc s u) := fun t ht => ⟨by simp only [ρ]; linarith [ht.2],
    by simp only [ρ]; linarith [ht.1]⟩
  have hL : ContinuousOn (fun t => cfgMat (c (ρ t)) r) (Icc s u) :=
    continuousOn_cfgMat (hc.comp hρc.continuousOn hρmaps) r
  obtain ⟨V, hV0, hVc, hVd⟩ := forwardMass_exists hsu hL (fun p => f (sectorEnum N r p))
  refine ⟨fun v => cfgExt r (V (ρ v)), fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · have hfun : (fun v => cfgExt r (V (ρ v)) ξ) = fun v => V (ρ v) (sectorIndex hξ) :=
      funext fun v => cfgExt_of_mem _ hξ
    refine ⟨?_, fun v hv => ?_⟩
    · rw [hfun]
      exact ((continuousOn_pi.1 hVc) _).comp hρc.continuousOn hρmaps
    · rw [hfun]
      have hvt : ρ v ∈ Ioo s u := ⟨by simp only [ρ]; linarith [hv.2], by simp only [ρ]; linarith [hv.1]⟩
      have h1 := hasDerivAt_pi.1 (hVd (ρ v) hvt) (sectorIndex hξ)
      have hρd : HasDerivAt ρ (-1) v := by
        simpa using ((hasDerivAt_id v).const_sub (s + u))
      have h2 := h1.scomp v hρd
      have hρρ : ρ (ρ v) = v := by simp only [ρ]; ring
      have e := cfgMat_act (c v) r (cfgExt r (V (ρ v))) (sectorIndex hξ)
      rw [sectorEnum_index hξ] at e
      simp only [cfgExt_enum] at e
      beta_reduce at h2
      rw [hρρ, e] at h2
      convert h2 using 1 <;> first | rfl | simp
  · show cfgExt r (V (ρ u)) ξ = f ξ
    have : ρ u = s := by simp only [ρ]; ring
    rw [this, cfgExt_of_mem _ hξ, hV0]
    show f (sectorEnum N r (sectorIndex hξ)) = f ξ
    rw [sectorEnum_index hξ]

/-- Reversal: a backward solution is a forward solution for the reversed rates. -/
theorem IsBackwardMomentFlow.reverse {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    {w : ℝ → Occ N → ℝ} (hw : IsBackwardMomentFlow c r s u w) :
    IsMomentFlowSolution (fun t => c (s + u - t)) r s u (fun t => w (s + u - t)) := by
  intro ξ hξ
  have hρc : Continuous fun t : ℝ => s + u - t := by fun_prop
  have hρmaps : MapsTo (fun t : ℝ => s + u - t) (Icc s u) (Icc s u) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨(hw ξ hξ).1.comp hρc.continuousOn hρmaps, fun t ht => ?_⟩
  have hvt : s + u - t ∈ Ioo s u := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h1 := (hw ξ hξ).2 _ hvt
  have hρd : HasDerivAt (fun t : ℝ => s + u - t) (-1) t := by
    simpa using ((hasDerivAt_id t).const_sub (s + u))
  have h2 := h1.scomp t hρd
  convert h2 using 1 <;> first | rfl | simp

/-- **Positivity** of backward solutions. -/
theorem IsBackwardMomentFlow.nonneg {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    (hc : ∀ v ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c v i j) {w : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) (h0 : ∀ ξ ∈ sector N r, 0 ≤ w u ξ) :
    ∀ v ∈ Icc s u, ∀ ξ ∈ sector N r, 0 ≤ w v ξ := by
  intro v hv ξ hξ
  have hrev := hw.reverse
  have hc' : ∀ t ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c (s + u - t) i j := fun t ht =>
    hc _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have := hrev.ge_of_initial_ge hc' (m := 0) (fun ζ hζ => by
    simp only [show s + u - s = u by ring]; exact h0 ζ hζ) (s + u - v)
    ⟨by linarith [hv.2], by linarith [hv.1]⟩ ξ hξ
  simpa [show s + u - (s + u - v) = v by ring] using this

/-- Constants are forward solutions. -/
theorem const_forward (c : ℝ → Fin N → Fin N → ℝ) (r : ℕ) (s u k : ℝ) :
    ∀ ξ ∈ sector N r, ∀ v ∈ Ioo s u, HasDerivAt (fun _ : ℝ => k)
      (momentGenerator (c v) (fun _ => k) ξ + (fun (_ : ℝ) (_ : Occ N) => (0 : ℝ)) v ξ) v := by
  intro ξ _ v _
  simpa [momentGenerator_const] using hasDerivAt_const v k

/-- **Representation**: pairing with a forward solution without source. -/
theorem IsBackwardMomentFlow.represent {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    (hsu : s ≤ u) (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {w Φ : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) (hΦ : IsMomentFlowSolution c r s u Φ) :
    ∑ ξ ∈ sector N r, w s ξ * Φ s ξ = ∑ ξ ∈ sector N r, w u ξ * Φ u ξ := by
  have h := backward_pairing (h := fun _ _ => 0) hsu hsym (fun ξ hξ => (hΦ ξ hξ).1)
    (fun ξ hξ v hv => by simpa using (hΦ ξ hξ).2 v hv) hw (fun _ _ => continuousOn_const)
  simp only [mul_zero, Finset.sum_const_zero, intervalIntegral.integral_zero] at h
  linarith

/-- **Conservation** of `Σ_ζ w(v, ζ)`. -/
theorem IsBackwardMomentFlow.mass_eq {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {w : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) :
    ∀ v ∈ Icc s u, ∑ ξ ∈ sector N r, w v ξ = ∑ ξ ∈ sector N r, w u ξ := by
  intro v hv
  have h := (hw.mono hv.1).represent hv.2 (fun x hx => hsym x ⟨lt_of_le_of_lt hv.1 hx.1, hx.2⟩)
    (isMomentFlowSolution_const c r v u 1)
  simpa using h

/-- The indicator of `ξ`. -/
def deltaCfg (ξ : Occ N) (ζ : Occ N) : ℝ := by
  classical
  exact if ζ = ξ then 1 else 0

theorem sum_deltaCfg_mul {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) (f : Occ N → ℝ) :
    ∑ ζ ∈ sector N r, deltaCfg ξ ζ * f ζ = f ξ := by
  classical
  rw [Finset.sum_eq_single ξ (fun ζ _ hζ => by simp [deltaCfg, hζ]) (fun h => absurd hξ h)]
  simp [deltaCfg]

/-- `(𝓑_{c(v)}F(v))(ξ)` is continuous on `S` when `c` and the sector values of `F` are. -/
theorem continuousOn_momentGenerator {c : ℝ → Fin N → Fin N → ℝ} {S : Set ℝ} (hc : ContinuousOn c S)
    {r : ℕ} {F : ℝ → Occ N → ℝ} (hF : ∀ ζ ∈ sector N r, ContinuousOn (fun v => F v ζ) S)
    {ξ : Occ N} (hξ : ξ ∈ sector N r) :
    ContinuousOn (fun v => momentGenerator (c v) (F v) ξ) S := by
  unfold momentGenerator
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j hj => ?_
  have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
  have hcij : ContinuousOn (fun v => c v i j) S :=
    continuousOn_pi.1 (continuousOn_pi.1 hc i) j
  rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
  · have : (fun v => c v i j * jumpCoeff ξ i j * (F v (move ξ i j) - F v ξ)) = fun _ => 0 := by
      funext v; rw [jumpCoeff_eq_zero_of_eq_zero ξ j hi]; ring
    rw [this]; exact continuousOn_const
  · exact (hcij.mul continuousOn_const).mul
      ((hF _ (move_mem_sector hξ hij hi)).sub (hF ξ hξ))

/-- **Localized Duhamel bound** (the deterministic core of the long-versus-short moment
comparison). -/
theorem duhamel_localized {c c' : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u e K : ℝ} (hsu : s ≤ u)
    (he : 0 ≤ e)
    (hc' : ∀ v ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c' v i j)
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c' v i j = c' v j i)
    {F g w : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r s u F)
    (hg : IsMomentFlowSolution c' r s u g) (h0 : ∀ ζ ∈ sector N r, F s ζ = g s ζ)
    (hh : ∀ ζ ∈ sector N r, ContinuousOn
      (fun v => momentGenerator (c v) (F v) ζ - momentGenerator (c' v) (F v) ζ) (Icc s u))
    (W : Finset (Occ N))
    (hloc : ∀ v ∈ Icc s u, ∀ ζ ∈ sector N r, ζ ∈ W →
      |momentGenerator (c v) (F v) ζ - momentGenerator (c' v) (F v) ζ| ≤ e)
    (hglob : ∀ v ∈ Icc s u, ∀ ζ ∈ sector N r,
      |momentGenerator (c v) (F v) ζ - momentGenerator (c' v) (F v) ζ| ≤ K)
    {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hw : IsBackwardMomentFlow c' r s u w) (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) :
    |F u ξ - g u ξ| ≤ e * (u - s) + K * ∫ v in s..u, ∑ ζ ∈ sector N r \ W, w v ζ := by
  set h : ℝ → Occ N → ℝ := fun v ζ =>
    momentGenerator (c v) (F v) ζ - momentGenerator (c' v) (F v) ζ
  set G : ℝ → Occ N → ℝ := fun v ζ => F v ζ - g v ζ
  have hGd : ∀ ζ ∈ sector N r, ∀ v ∈ Ioo s u,
      HasDerivAt (fun v => G v ζ) (momentGenerator (c' v) (G v) ζ + h v ζ) v := by
    intro ζ hζ v hv
    have h1 := ((hF ζ hζ).2 v hv).sub ((hg ζ hζ).2 v hv)
    convert h1 using 1
    have : G v = F v - g v := rfl
    rw [this, momentGenerator_sub]
    simp only [h]; ring
  have hpair := backward_pairing (Φ := G) (h := h) hsu hsym (fun ζ hζ => ((hF ζ hζ).1.sub (hg ζ hζ).1)) hGd hw hh
  have hG0 : ∑ ζ ∈ sector N r, w s ζ * G s ζ = 0 :=
    Finset.sum_eq_zero fun ζ hζ => by simp only [G, h0 ζ hζ, sub_self, mul_zero]
  have hGu : ∑ ζ ∈ sector N r, w u ζ * G u ζ = G u ξ := by
    rw [Finset.sum_congr rfl fun ζ hζ => by rw [hwu ζ hζ]]
    exact sum_deltaCfg_mul hξ _
  rw [hG0, sub_zero, hGu] at hpair
  have hwnn := hw.nonneg hc' (fun ζ hζ => by
    rw [hwu ζ hζ]; unfold deltaCfg; split_ifs <;> norm_num)
  have hmass : ∀ v ∈ Icc s u, ∑ ζ ∈ sector N r, w v ζ = 1 := by
    intro v hv
    rw [hw.mass_eq hsym v hv, Finset.sum_congr rfl fun ζ hζ => hwu ζ hζ]
    simpa using sum_deltaCfg_mul hξ (fun _ => 1)
  have hTc : ContinuousOn (fun v => ∑ ζ ∈ sector N r \ W, w v ζ) (Icc s u) :=
    continuousOn_finsetSum _ fun ζ hζ => (hw ζ (Finset.mem_sdiff.1 hζ).1).1
  have hbound : ∀ v ∈ Icc s u, ‖∑ ζ ∈ sector N r, w v ζ * h v ζ‖ ≤
      e + K * ∑ ζ ∈ sector N r \ W, w v ζ := by
    intro v hv
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hglob v hv ξ hξ)
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsplit := Finset.sum_filter_add_sum_filter_not (sector N r) (fun ζ => ζ ∈ W)
      (fun ζ => |w v ζ * h v ζ|)
    rw [← hsplit]
    have hsd : (sector N r).filter (fun ζ => ζ ∉ W) = sector N r \ W := by
      ext ζ; simp [Finset.mem_sdiff]
    have hA : ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), |w v ζ * h v ζ| ≤ e := by
      calc ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), |w v ζ * h v ζ|
          ≤ ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), w v ζ * e := by
            refine Finset.sum_le_sum fun ζ hζ => ?_
            obtain ⟨hζs, hζW⟩ := Finset.mem_filter.1 hζ
            rw [abs_mul, abs_of_nonneg (hwnn v hv ζ hζs)]
            exact mul_le_mul_of_nonneg_left (hloc v hv ζ hζs hζW) (hwnn v hv ζ hζs)
        _ = e * ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∈ W), w v ζ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ ≤ e * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ he
            rw [← hmass v hv]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun ζ hζ _ => hwnn v hv ζ hζ
        _ = e := mul_one e
    have hB : ∑ ζ ∈ (sector N r).filter (fun ζ => ζ ∉ W), |w v ζ * h v ζ| ≤
        K * ∑ ζ ∈ sector N r \ W, w v ζ := by
      rw [hsd, Finset.mul_sum]
      refine Finset.sum_le_sum fun ζ hζ => ?_
      have hζs := (Finset.mem_sdiff.1 hζ).1
      rw [abs_mul, abs_of_nonneg (hwnn v hv ζ hζs), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hglob v hv ζ hζs) (hwnn v hv ζ hζs)
    linarith
  show |G u ξ| ≤ _
  rw [hpair]
  have hint : IntervalIntegrable (fun v => e + K * ∑ ζ ∈ sector N r \ W, w v ζ) volume s u :=
    (continuousOn_const.add (continuousOn_const.mul hTc)).intervalIntegrable_of_Icc hsu
  have hle := intervalIntegral.norm_integral_le_of_norm_le hsu
    (Filter.Eventually.of_forall fun v hv => hbound v (Ioc_subset_Icc_self hv)) hint
  rw [Real.norm_eq_abs] at hle
  refine hle.trans (le_of_eq ?_)
  have hTi : IntervalIntegrable (fun v => K * ∑ ζ ∈ sector N r \ W, w v ζ) volume s u :=
    (continuousOn_const.mul hTc).intervalIntegrable_of_Icc hsu
  rw [intervalIntegral.integral_add intervalIntegrable_const hTi, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

end BlockBand.Palm.MomentFlow
