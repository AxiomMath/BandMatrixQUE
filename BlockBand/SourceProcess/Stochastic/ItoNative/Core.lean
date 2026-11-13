module
public import BlockBand.SourceProcess.Stochastic.ItoNative.IntegralProcess
public import BlockBand.SourceProcess.Stochastic.ItoNative.Contracts
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The core identity of the Itô formula

Sample space `DriverSample S κ`, law `P = driverLaw μ`, augmented filtration `G = F_t ∨ N`.
Let `Z` be a coordinate representation (`CoordRep μ Z β h`) in `ℝ^d` and
`ψ : ℝ × ℝ^d → ℝ` be `C²`. Write `H_a(s) = Dψ(s, Z_s)[(0, h_a(s))]` (the candidate diffusion)
and `A(s) = itoDrift ψ (Z_s) s β_s (∑_a h_a h_aᵀ)` (the Itô drift).

**`CoordRep.ito_identity`.** For every augmented stopping time `τ` and horizon `T` such that
`H 1{s ≤ τ}` is an integrand on `(0, T]`, and every `t ≤ T`:
`ψ(t∧τ, Z_{t∧τ}) − ψ(0, Z_0) − ∫_0^{t∧τ} A ds = I_T(H 1{s ≤ t ∧ τ})` a.s.

Proof. With `ρ = τ ∧ T`, `g = H 1{s ≤ ρ}` and `W` the integral process of `g`
(`exists_integralProcess`), the concatenation `Z' = (Z, W)` is a `CoordRep`, hence a continuous
semimartingale with covariance `∑_a h'_a h'_aᵀ`, `h'_a = (h_a, g_a)`. Apply the Itô formula to
`Ψ(s, z, w) = ψ(s, z) − w`: its drift is `A` (the `w` direction has no drift and `Ψ` is affine in
`w`) and its bracket density is `∑_a (H_a − g_a)²`, which vanishes on `{s ≤ ρ}`. Stopping at `ρ`
(`stoppedSemimartingale_holds`) gives a semimartingale with identically zero bracket, whose
martingale part is then `0` a.s. (`smCompensated_ae_eq_zero_of_bracket`). Finally
`W_{t∧τ} = I_T(g 1{s ≤ t∧τ})` and `g 1{s ≤ t∧τ} = H 1{s ≤ t∧τ}` for `t ≤ T`.
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.Internal.Contracts.Transmission

section Prog
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀}

/-- A continuous function of `(t, Y_t)` for a progressive `Y` is progressive. -/
theorem isStronglyProgressive_timeComp {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace.PseudoMetrizableSpace B] {Y : ℝ≥0 → Ω → A}
    (hY : IsStronglyProgressive 𝓖 Y) {Φ : ℝ × A → B} (hΦ : Continuous Φ) :
    IsStronglyProgressive 𝓖 fun t x => Φ ((t : ℝ), Y t x) := fun i =>
  hΦ.comp_stronglyMeasurable
    (((measurable_coe_nnreal_real.comp (measurable_time_coord i)).stronglyMeasurable).prodMk
      (hY i))

end Prog

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {d : ℕ}

/-- The candidate diffusion integrand `(s, x) ↦ Dψ(s, Z_s)[(0, h_a(s))]` (time via `toNNReal`). -/
def itoIntegrand (ψ : ℝ × (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → DriverSample S κ → Fin d → ℝ)
    (h : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ) : κ → ℝ × DriverSample S κ → ℝ :=
  fun a p => fderiv ℝ ψ ((p.1.toNNReal : ℝ), Z p.1.toNNReal p.2) ((0 : ℝ), h a p.1.toNNReal p.2)

/-- The Itô drift process `s ↦ itoDrift ψ (Z_s) s β_s (∑_a h_a h_aᵀ)`. -/
def itoDriftProc (ψ : ℝ × (Fin d → ℝ) → ℝ) (Z β : ℝ≥0 → DriverSample S κ → Fin d → ℝ)
    (h : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ) : ℝ≥0 → DriverSample S κ → ℝ :=
  fun s x => itoDrift ψ (Z s x) s (β s x) (covOf fun a => h a s x)

/-- First block `z ↦ (z_{castAdd i})_i` of `ℝ^{d+1}`, with the time coordinate kept. -/
def blockL (d : ℕ) : ℝ × (Fin (d + 1) → ℝ) →L[ℝ] ℝ × (Fin d → ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin (d + 1) → ℝ)).prod
    ((ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) (Fin.castAdd 1 i)).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin (d + 1) → ℝ)))

/-- Minus the last coordinate of `ℝ^{d+1}`. -/
def lastL (d : ℕ) : ℝ × (Fin (d + 1) → ℝ) →L[ℝ] ℝ :=
  -((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ)
    (Fin.natAdd d (0 : Fin 1))).comp (ContinuousLinearMap.snd ℝ ℝ (Fin (d + 1) → ℝ)))

theorem blockL_concat (r : ℝ) (u : Fin d → ℝ) (v : Fin 1 → ℝ) :
    blockL d (r, concatCoord u v) = (r, u) := by
  ext i
  · rfl
  · simp [blockL]

theorem lastL_concat (r : ℝ) (u : Fin d → ℝ) (v : Fin 1 → ℝ) :
    lastL d (r, concatCoord u v) = -v 0 := by
  simp [lastL]

theorem blockL_one_zero : blockL d ((1 : ℝ), (0 : Fin (d + 1) → ℝ)) = (1, 0) := by
  ext i <;> simp [blockL]

theorem lastL_one_zero : lastL d ((1 : ℝ), (0 : Fin (d + 1) → ℝ)) = 0 := by
  simp [lastL]

/-- `stopTime (τ ∧ T) t = stopTime τ t` for `t ≤ T`. -/
theorem stopTime_min_of_le {t T : ℝ≥0} (ht : t ≤ T) (r : WithTop ℝ≥0) :
    stopTime (min r (T : WithTop ℝ≥0)) t = stopTime r t := by
  unfold stopTime
  congr 1
  rw [min_comm r, ← min_assoc, min_eq_left (WithTop.coe_le_coe.2 ht)]

/-- **Core identity of the Itô formula.** See the module docstring. -/
theorem CoordRep.ito_identity {Z β : ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {h : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ} (H : CoordRep μ Z β h)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    {T : ℝ≥0} (hG : NativeIntegrand μ T (stopIntegrand τ (itoIntegrand ψ Z h)))
    {t : ℝ≥0} (ht : t ≤ T) :
    ∃ hs : NativeIntegrand μ T
        (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) (itoIntegrand ψ Z h)),
      (fun x => stoppedProcess (fun (s : ℝ≥0) x => ψ ((s : ℝ), Z s x)) τ t x -
          ψ (((0 : ℝ≥0) : ℝ), Z 0 x) - stoppedDrift τ (itoDriftProc ψ Z β h) t x)
        =ᵐ[driverLaw (κ := κ) μ] (nativeIntegralOf hs : DriverSample S κ → ℝ) := by
  classical
  set I := itoIntegrand ψ Z h with hIdef
  set ρ : DriverSample S κ → WithTop ℝ≥0 := fun x => min (τ x) (T : WithTop ℝ≥0) with hρdef
  have hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ := hτ.min (isStoppingTime_const _ T)
  set g := stopIntegrand ρ I with hgdef
  have hg : NativeIntegrand μ T g := by
    rw [hgdef, hρdef, ← stopIntegrand_stopIntegrand]
    exact stopIntegrand_nativeIntegrand hG (isStoppingTime_const _ T)
  have hsupp : ∀ c p, (T : ℝ) < p.1 → g c p = 0 := by
    intro c p hp
    have hn : ¬ ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ p.2 := by
      intro hle
      have h2 : p.1.toNNReal ≤ T := WithTop.coe_le_coe.1 (hle.trans (min_le_right _ _))
      exact absurd (Real.toNNReal_le_iff_le_coe.1 h2) (not_le.2 hp)
    simp only [hgdef, stopIntegrand]
    exact ite_eq_right hn
  have htoNN : ∀ c (p : ℝ × DriverSample S κ), g c ((p.1.toNNReal : ℝ), p.2) = g c p := by
    intro c p
    simp only [hgdef, hIdef, stopIntegrand, itoIntegrand, Real.toNNReal_coe]
  have hDc : Continuous fun q : ℝ × (Fin d → ℝ) × (Fin d → ℝ) =>
      fderiv ℝ ψ (q.1, q.2.1) ((0 : ℝ), q.2.2) :=
    ((hψ.continuous_fderiv (by norm_num)).comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).clm_apply
      (continuous_const.prodMk (continuous_snd.comp continuous_snd))
  have hprog : ∀ c, IsStronglyProgressive (driverAugmented (κ := κ) μ)
      (fun t x => g c ((t : ℝ), x)) := by
    intro c
    have hin : IsStronglyProgressive (driverAugmented (κ := κ) μ)
        (fun t x => fderiv ℝ ψ ((t : ℝ), Z t x) ((0 : ℝ), h c t x)) :=
      isStronglyProgressive_timeComp (Y := fun t x => (Z t x, h c t x))
        (fun i => (H.progressive i).prodMk (H.diffusion_progressive c i)) hDc
    have e : (fun (t : ℝ≥0) x => g c ((t : ℝ), x)) = switchAfter ρ
        (fun t x => fderiv ℝ ψ ((t : ℝ), Z t x) ((0 : ℝ), h c t x)) := by
      funext t x
      simp only [hgdef, hIdef, stopIntegrand, itoIntegrand, switchAfter, Real.toNNReal_coe]
    rw [e]
    exact isStronglyProgressive_switchAfter hin hρ
  obtain ⟨W, HW, hW0, hWid⟩ := exists_integralProcess hg hsupp htoNN hprog
  have HS := (H.concat HW).isContinuousSemimartingale
  set Ψ := affineComp (ContinuousLinearMap.id ℝ ℝ) ψ (blockL d) (lastL d) with hΨdef
  have hΨ : ContDiff ℝ 2 Ψ := contDiff_affineComp hψ _ _ _
  have H1 := isContinuousSemimartingale_ito HS hΨ.continuous.measurable hΨ
  have H2 := isContinuousSemimartingale_stopped H1 hρ
  have hzero := smCompensated_ae_eq_zero_of_bracket H2 (fun s ω => by
    simp only [switchAfter]
    split_ifs with hs
    · simp only [Matrix.of_apply]
      rw [itoBracket_covOf]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hΨdef, fderiv_affineComp hψ, blockL_concat, blockL_concat, lastL_concat]
      simp only [hgdef, hIdef, stopIntegrand, itoIntegrand, Real.toNNReal_coe,
        ContinuousLinearMap.id_apply]
      split_ifs
      ring
    · rfl) t
  have P1 : ∀ (s : ℝ≥0) ω, Ψ ((s : ℝ), concatCoord (Z s ω) (fun _ : Fin 1 => W s ω)) =
      ψ ((s : ℝ), Z s ω) - W s ω := by
    intro s ω
    simp only [hΨdef, affineComp, blockL_concat, lastL_concat, ContinuousLinearMap.id_apply]
    ring
  have P2 : ∀ (s : ℝ≥0) ω, itoDrift Ψ (concatCoord (Z s ω) (fun _ : Fin 1 => W s ω)) s
      (concatCoord (β s ω) (fun _ : Fin 1 => 0))
      (covOf fun a => concatCoord (h a s ω) (fun _ : Fin 1 => g a ((s : ℝ), ω))) =
      itoDriftProc ψ Z β h s ω := by
    intro s ω
    rw [itoDriftProc, itoDrift_covOf, itoDrift_covOf]
    simp only [hΨdef, fderiv_affineComp hψ, fderiv_fderiv_affineComp hψ, blockL_concat,
      lastL_concat, blockL_one_zero, lastL_one_zero, ContinuousLinearMap.id_apply, neg_zero,
      add_zero]
  obtain ⟨hs0, hWae⟩ := hWid τ hτ t
  have e : stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) g =
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) I := by
    rw [hgdef, stopIntegrand_stopIntegrand]
    congr 1
    funext x
    exact min_eq_right (le_min (min_le_right _ _)
      ((min_le_left _ _).trans (WithTop.coe_le_coe.2 ht)))
  have hs : NativeIntegrand μ T (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) I) :=
    e ▸ hs0
  refine ⟨hs, ?_⟩
  rw [← Bridges.nativeIntegralOf_congr e hs0 hs]
  filter_upwards [hzero, hWae] with ω h1 h2
  rw [smCompensated_stopped] at h1
  simp only [smCompensated, P1, P2, hρdef, stopTime_min_of_le ht] at h1
  rw [stoppedProcess_eq_stopTime] at h2
  rw [stoppedProcess_eq_stopTime, stoppedDrift,
    setIntegral_switch (fun v => itoDriftProc ψ Z β h v.toNNReal ω) (τ ω) t]
  rw [hW0] at h1
  linarith

end BlockBand.SourceProcess.Stochastic.ItoNative
