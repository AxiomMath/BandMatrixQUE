module

public import BlockBand.Diffusion.Doob.Path
public import BlockBand.Diffusion.Doob.KilledDuality
public import BlockBand.Diffusion.Duality.Shift

/-!
# The one-pair dual solves the martingale problem of the `H` transform

In `Fin 2` coordinates (`y = (y₀, y₁) = (x, y)`), the open chamber `dkDualChamber 1` is the
open strip `openStripFin`, and the dual generator `dkDualGenerator D0` at `q = 1` is
`mpGenerator` with
* drift `dkHDrift D0 y = (D₀/2)(β^x, β^y)`, `β^x = 1 + 2x - 2x(1+x)/(x+y)`,
  `β^y = 1 - 2y - 2y(1-y)/(x+y)` (`dkHDrift_apply`), continuous on the open strip;
* covariance `baseCov D0 y = diag(D₀ x(1+x), D₀ y(1-y))`
(`dkDualGenerator_comp`). This is `H⁻¹𝒟₀(H ·)`, `H = (x+y)⁻¹`; only the form above is used.

## Main results

For every realization of the one-pair boundary dual
`IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y`:
* `IsDkBoundaryDualProcess.isTestMPSolution`: the killed point `dkZ = finProd.symm ∘ dkPt`
  (the dual point while the level is `1` and `N₀ = 1`, the corner after) solves the raw
  test-function martingale problem `IsTestMPSolution P 𝓖 (dkHDrift D0) (baseCov D0)
  openStripFin` (on the `𝓖₀`-set `{N₀ = 1}` the compensated test process is
  `dkDualMartingale` plus the `𝓖₀`-measurable entrance value; off it, it vanishes);
* `IsDkBoundaryDualProcess.isTestMPSolution_flat`: so does its progressive version `dkZf`
  (`predVersion`, equal to `dkZ` on continuous paths), all of whose paths are measurable in
  time;
* `IsDkBoundaryDualProcess.isTestMPSolution_shift`: hence, for every `q`, the restarted
  `shiftProc (dkZf) q` solves the raw problem for `shiftFiltration 𝓖 q` (the restart needs the
  splitting of the time integral on every path, hence the progressive version).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission (shiftFiltration)
open scoped ENNReal NNReal

/-!
### Coordinates and the generator
-/

/-- `DkDualCoord 1 ≃ ℝ²`, `(x, y) ↦ (x₀, y₀)`. -/
def dkFinLinear : DkDualCoord 1 ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.1 0, z.2 0]
  invFun y := (fun _ => y 0, fun _ => y 1)
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl
  left_inv z := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> rfl
  right_inv y := by ext i; fin_cases i <;> rfl

/-- The continuous linear equivalence `DkDualCoord 1 ≃L ℝ²`. -/
def dkFin : DkDualCoord 1 ≃L[ℝ] (Fin 2 → ℝ) := dkFinLinear.toContinuousLinearEquiv

@[simp] theorem dkFin_apply (z : DkDualCoord 1) : dkFin z = ![z.1 0, z.2 0] := rfl

@[simp] theorem dkFin_symm_apply (y : Fin 2 → ℝ) :
    dkFin.symm y = (fun _ => y 0, fun _ => y 1) := rfl

/-- The drift of the `H` transform in `Fin 2` coordinates. -/
def dkHDrift (D0 : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![D0 / 2 * dkDualDriftX (dkFin.symm y) 0, D0 / 2 * dkDualDriftY (dkFin.symm y) 0]

theorem dkHDrift_apply (D0 : ℝ) (y : Fin 2 → ℝ) :
    dkHDrift D0 y = ![D0 / 2 * (1 + 2 * y 0 - 2 * y 0 * (1 + y 0) * (1 / (y 0 + y 1))),
      D0 / 2 * (1 - 2 * y 1 - 2 * y 1 * (1 - y 1) * (1 / (y 0 + y 1)))] := by
  have hx : dkDualDriftX (dkFin.symm y) 0 =
      1 + 2 * y 0 - 2 * y 0 * (1 + y 0) * (1 / (y 0 + y 1)) := by
    simp only [dkDualDriftX, dkFin_symm_apply, Finset.univ_unique, Fin.default_eq_zero,
      Finset.erase_singleton, Finset.sum_empty, Finset.sum_singleton]
    ring
  have hy : dkDualDriftY (dkFin.symm y) 0 =
      1 - 2 * y 1 - 2 * y 1 * (1 - y 1) * (1 / (y 0 + y 1)) := by
    simp only [dkDualDriftY, dkFin_symm_apply, Finset.univ_unique, Fin.default_eq_zero,
      Finset.erase_singleton, Finset.sum_empty, Finset.sum_singleton]
    ring
  rw [dkHDrift, hx, hy]

theorem continuousOn_dkHDrift (D0 : ℝ) : ContinuousOn (dkHDrift D0) openStripFin := by
  have hne : ∀ y ∈ openStripFin, y 0 + y 1 ≠ 0 := fun y hy => by
    have := hy.1; have := hy.2.1; positivity
  have h0 : ContinuousOn (fun y : Fin 2 → ℝ => 1 / (y 0 + y 1)) openStripFin :=
    continuousOn_const.div (by fun_prop) hne
  have hc : ∀ (A B : (Fin 2 → ℝ) → ℝ), Continuous A → Continuous B →
      ContinuousOn (fun y => D0 / 2 * (A y - B y * (1 / (y 0 + y 1)))) openStripFin :=
    fun A B hA hB => continuousOn_const.mul (hA.continuousOn.sub (hB.continuousOn.mul h0))
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · refine (hc (fun y => 1 + 2 * y 0) (fun y => 2 * y 0 * (1 + y 0)) (by fun_prop)
      (by fun_prop)).congr fun y _ => ?_
    simp [dkHDrift_apply]
  · refine (hc (fun y => 1 - 2 * y 1) (fun y => 2 * y 1 * (1 - y 1)) (by fun_prop)
      (by fun_prop)).congr fun y _ => ?_
    simp [dkHDrift_apply]

theorem fderiv_comp_dkFin (f : (Fin 2 → ℝ) → ℝ) (z v : DkDualCoord 1) :
    fderiv ℝ (f ∘ dkFin) z v = fderiv ℝ f (dkFin z) (dkFin v) := by
  rw [dkFin.comp_right_fderiv]; rfl

theorem fderiv_fderiv_comp_dkFin {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (z v w : DkDualCoord 1) :
    fderiv ℝ (fun u => fderiv ℝ (f ∘ dkFin) u w) z v =
      fderiv ℝ (fderiv ℝ f) (dkFin z) (dkFin v) (dkFin w) := by
  have e : (fun u => fderiv ℝ (f ∘ dkFin) u w) = (fun y => fderiv ℝ f y (dkFin w)) ∘ dkFin := by
    funext u; simp only [Function.comp, fderiv_comp_dkFin]
  rw [e, fderiv_comp_dkFin]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) (dkFin z) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem dkFin_dirX : dkFin (dkDirX (0 : Fin 1)) = Pi.single 0 1 := by
  ext i; fin_cases i <;> simp [dkDirX]

theorem dkFin_dirY : dkFin (dkDirY (0 : Fin 1)) = Pi.single 1 1 := by
  ext i; fin_cases i <;> simp [dkDirY]

/-- **Generator transport**: the dual generator `dkDualGenerator` at `q = 1` is `mpGenerator` of
`(dkHDrift D0, baseCov D0)`. -/
theorem dkDualGenerator_comp (D0 : ℝ) {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (z : DkDualCoord 1) :
    dkDualGenerator D0 (f ∘ dkFin) z = mpGenerator (dkHDrift D0) (baseCov D0) f (dkFin z) := by
  have hb : dkHDrift D0 (dkFin z) = ![D0 / 2 * dkDualDriftX z 0, D0 / 2 * dkDualDriftY z 0] := by
    simp only [dkHDrift, ContinuousLinearEquiv.symm_apply_apply]
  simp only [dkDualGenerator, Fin.sum_univ_one]
  rw [fderiv_fderiv_comp_dkFin hf, fderiv_fderiv_comp_dkFin hf, fderiv_comp_dkFin,
    fderiv_comp_dkFin, dkFin_dirX, dkFin_dirY]
  simp only [mpGenerator, Fin.sum_univ_two, hb]
  simp [baseCov]
  ring

/-!
### Tests
-/

theorem dkFin_preimage_openStrip_subset :
    dkFin ⁻¹' openStripFin ⊆ dkDualChamber 1 := fun z hz => by
  obtain ⟨h0, h1, h2⟩ := hz
  simp only [dkFin_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  refine ⟨fun i j hij => absurd hij (by simp [Subsingleton.elim i j]),
    fun i j hij => absurd hij (by simp [Subsingleton.elim i j]), fun i => ?_, fun i => ?_⟩
  · rw [Subsingleton.elim i 0]; exact h0
  · rw [Subsingleton.elim i 0]; exact ⟨h1, h2⟩

theorem IsMPTest.comp_dkFin {f : (Fin 2 → ℝ) → ℝ} (hf : IsMPTest openStripFin f) :
    ContDiff ℝ (⊤ : ℕ∞) (f ∘ dkFin) ∧ HasCompactSupport (f ∘ dkFin) ∧
      tsupport (f ∘ dkFin) ⊆ dkDualChamber 1 := by
  refine ⟨hf.1.comp dkFin.contDiff, hf.2.1.comp_homeomorph dkFin.toHomeomorph, ?_⟩
  rw [show f ∘ dkFin = f ∘ dkFin.toHomeomorph from rfl, tsupport_comp_eq_preimage]
  exact (preimage_mono hf.2.2).trans dkFin_preimage_openStrip_subset

theorem zero_notMem_openStripFin : (0 : Fin 2 → ℝ) ∉ openStripFin := fun h => by
  have := h.1; simp at this

theorem IsMPTest.apply_zero {f : (Fin 2 → ℝ) → ℝ} (hf : IsMPTest openStripFin f) : f 0 = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => zero_notMem_openStripFin (hf.2.2 h)

theorem IsMPTest.mpGenerator_zero {f : (Fin 2 → ℝ) → ℝ} (hf : IsMPTest openStripFin f)
    (b : (Fin 2 → ℝ) → Fin 2 → ℝ) (a : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) :
    mpGenerator b a f 0 = 0 :=
  mpGenerator_eq_zero_of_notMem fun h => zero_notMem_openStripFin (hf.2.2 h)

/-!
### The killed point in `Fin 2` coordinates
-/

variable {Ω : Type*}

/-- The killed point in `Fin 2` coordinates. -/
def dkZ (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : Fin 2 → ℝ :=
  finProd.symm (dkPt N X Y t ω)

theorem dkZ_eq (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) :
    dkZ N X Y t ω = if N 0 ω = 1 ∧ N t ω = 1 then dkFin (dkDualCoordOf 1 (X t ω) (Y t ω))
      else 0 := by
  unfold dkZ dkPt
  split_ifs
  · ext i; fin_cases i <;> rfl
  · ext i; fin_cases i <;> rfl

/-- The progressive version of the killed point (`dkZ` on continuous paths). -/
def dkZf (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : Fin 2 → ℝ :=
  if t = 0 then dkZ N X Y 0 ω else pv (dkZ N X Y) t ω

theorem dkZf_eq_of_continuous {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (hc : Continuous fun t => dkZ N X Y t ω) (t : ℝ≥0) : dkZf N X Y t ω = dkZ N X Y t ω := by
  unfold dkZf
  split_ifs with h
  · rw [h]
  · exact pv_eq hc (pos_iff_ne_zero.2 h)

/-!
### The martingale problem
-/

section MP

variable [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 x y : ℝ} {N : ℝ≥0 → Ω → ℕ}
  {X Y : ℝ≥0 → Ω → ℕ → ℝ}

omit [MeasurableSpace Ω] in
theorem dkDualEntrance_eq_zero {ω : Ω} (h0 : N 0 ω = 1) : dkDualEntrance N 1 ω = 0 :=
  le_antisymm (csInf_le (OrderBot.bddBelow _) (by simp [h0])) zero_le

theorem stronglyMeasurable_dkZ (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (t : ℝ≥0) : StronglyMeasurable[𝓖 t] (dkZ N X Y t) := by
  have hN0 : Measurable[𝓖 t] (N 0) := ((hP.adapted 0).1).mono (𝓖.mono zero_le) le_rfl
  have hNt : Measurable[𝓖 t] (N t) := (hP.adapted t).1
  have hS : MeasurableSet[𝓖 t] {ω | N 0 ω = 1 ∧ N t ω = 1} :=
    (hN0 (measurableSet_singleton 1)).inter (hNt (measurableSet_singleton 1))
  have hX : Measurable[𝓖 t] fun ω => X t ω 0 := (measurable_pi_apply 0).comp (hP.adapted t).2.1
  have hY : Measurable[𝓖 t] fun ω => Y t ω 0 := (measurable_pi_apply 0).comp (hP.adapted t).2.2
  have hpt : Measurable[𝓖 t] (dkPt N X Y t) := by
    classical
    unfold dkPt
    exact Measurable.ite hS (hX.prodMk hY) measurable_const
  exact (finProd.symm.continuous.measurable.comp hpt).stronglyMeasurable

/-- The a.s. pathwise facts. -/
theorem IsDkBoundaryDualProcess.ae_good
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, (N 0 ω = 1 ∧ X 0 ω 0 = x ∧ Y 0 ω 0 = y) ∧
      IsDkBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω) := by
  filter_upwards [hP.start, hP.paths] with ω h1 h2
  exact ⟨⟨by simpa using h1.1, by simpa using (h1.2 0).1, by simpa using (h1.2 0).2⟩, h2⟩

theorem IsDkBoundaryDualProcess.continuous_dkZ
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, Continuous fun t => dkZ N X Y t ω := by
  filter_upwards [hP.ae_good] with ω h
  exact finProd.symm.continuous.comp (dk_continuous_pt h.2 h.1.1)

/-- **The killed point solves the raw test-function martingale problem of the `H` transform.** -/
theorem IsDkBoundaryDualProcess.isTestMPSolution
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    IsTestMPSolution P 𝓖 (dkHDrift D0) (baseCov D0) openStripFin (dkZ N X Y) where
  adapted t := (stronglyMeasurable_dkZ hP t).measurable
  continuous := hP.continuous_dkZ
  martingale f hf := by
    have := hP.prob
    obtain ⟨hg1, hg2, hg3⟩ := hf.comp_dkFin
    have hM := hP.martingale 1 le_rfl (by simp) (f ∘ dkFin) hg1 hg2 hg3
    set G₀ : Set Ω := {ω | N 0 ω = 1} with hG₀
    have hG₀m : MeasurableSet[𝓖 0] G₀ := (hP.adapted 0).1 (measurableSet_singleton 1)
    set g : Ω → ℝ := G₀.indicator 1 with hgdef
    have hgm : StronglyMeasurable[𝓖 0] g :=
      (stronglyMeasurable_const.indicator hG₀m)
    have hgb : ∀ ω, |g ω| ≤ 1 := fun ω => by
      by_cases hω : ω ∈ G₀ <;> simp [hgdef, hω]
    have hM1 := martingale_mul_left_of_zero hM hgm hgb
    have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by norm_cast)
    obtain ⟨Cf, hCf⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
    have hc0 : StronglyMeasurable[𝓖 ⊥] fun ω => g ω * f (dkZ N X Y 0 ω) := by
      have : (𝓖 ⊥ : MeasurableSpace Ω) = 𝓖 0 := rfl
      rw [this]
      exact hgm.mul (hf.1.continuous.comp_stronglyMeasurable (stronglyMeasurable_dkZ hP 0))
    have hci : Integrable (fun ω => g ω * f (dkZ N X Y 0 ω)) P := by
      refine Integrable.of_bound ((hc0.mono (𝓖.le _)).aestronglyMeasurable) Cf
        (ae_of_all _ fun ω => ?_)
      rw [norm_mul]
      calc ‖g ω‖ * ‖f (dkZ N X Y 0 ω)‖ ≤ 1 * Cf :=
            mul_le_mul (by rw [Real.norm_eq_abs]; exact hgb ω) (hCf _) (norm_nonneg _)
              zero_le_one
        _ = Cf := one_mul _
    have hM2 := hM1.add (martingale_const_fun 𝓖 P hc0 hci)
    convert hM2 using 1
    funext t ω
    simp only [Pi.add_apply]
    by_cases hω : ω ∈ G₀
    · have h0 : N 0 ω = 1 := hω
      have hgω : g ω = 1 := by simp [hgdef, hω]
      rw [hgω, one_mul, one_mul]
      have hlift : ∀ r : ℝ≥0, dkDualLift (f ∘ dkFin) (N r ω) (X r ω) (Y r ω) =
          f (dkZ N X Y r ω) := fun r => by
        rw [dkZ_eq]
        by_cases hr : N r ω = 1
        · simp [dkDualLift, hr, h0]
        · simp [dkDualLift, hr, hf.apply_zero]
      have hgen : ∀ r : ℝ≥0, dkDualLift (dkDualGenerator D0 (f ∘ dkFin)) (N r ω) (X r ω)
          (Y r ω) = mpGenerator (dkHDrift D0) (baseCov D0) f (dkZ N X Y r ω) := fun r => by
        rw [dkZ_eq]
        by_cases hr : N r ω = 1
        · simp only [dkDualLift, hr, h0, and_self, ↓reduceIte]
          exact dkDualGenerator_comp D0 hf2 _
        · simp [dkDualLift, hr, hf.mpGenerator_zero]
      have hent : dkDualEntranceValue (f ∘ dkFin) N X Y t ω = f (dkZ N X Y 0 ω) := by
        have hex : ∃ u ≤ t, N u ω ≤ 1 := ⟨0, zero_le, h0.le⟩
        simp only [dkDualEntranceValue, hex, ↓reduceIte, dkDualEntrance_eq_zero h0]
        exact hlift 0
      simp only [dkDualMartingale, hlift, hgen, hent]
      ring
    · have h0 : ¬ N 0 ω = 1 := hω
      have hgω : g ω = 0 := by simp [hgdef, hω]
      have hz : ∀ r, dkZ N X Y r ω = 0 := fun r => by rw [dkZ_eq]; simp [h0]
      simp only [hgω, zero_mul, add_zero, hz, hf.apply_zero, hf.mpGenerator_zero,
        integral_zero, sub_zero]

/-- The progressive version is adapted. -/
theorem stronglyMeasurable_dkZf (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (t : ℝ≥0) : StronglyMeasurable[𝓖 t] (dkZf N X Y t) := by
  have hpv : IsStronglyProgressive 𝓖 (pv (dkZ N X Y)) :=
    Representation.isStronglyProgressive_predVersion 𝓖 (stronglyMeasurable_dkZ hP)
  by_cases ht : t = 0
  · subst ht
    have e : dkZf N X Y 0 = dkZ N X Y 0 := funext fun ω => by simp [dkZf]
    rw [e]; exact stronglyMeasurable_dkZ hP 0
  · have e : dkZf N X Y t = pv (dkZ N X Y) t := funext fun ω => by simp [dkZf, ht]
    rw [e]; exact hpv.stronglyAdapted t

/-- Every path of the progressive version is measurable in time. -/
theorem measurable_dkZf_path (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (ω : Ω) :
    Measurable fun u : ℝ => dkZf N X Y u.toNNReal ω := by
  classical
  have hpv : Measurable (Levy.predVersion (dkZ N X Y)) :=
    ((Levy.stronglyMeasurable_predVersion 𝓖 (stronglyMeasurable_dkZ hP)).measurable.mono
      (BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto.predictableSpace_le _)
      le_rfl)
  have h1 : Measurable fun u : ℝ => Levy.predVersion (dkZ N X Y) (((u.toNNReal : ℝ≥0) : ℝ), ω) :=
    hpv.comp ((measurable_subtype_coe.comp measurable_real_toNNReal).prodMk measurable_const)
  have e : (fun u : ℝ => dkZf N X Y u.toNNReal ω) = fun u =>
      if u.toNNReal = 0 then dkZ N X Y 0 ω
      else Levy.predVersion (dkZ N X Y) (((u.toNNReal : ℝ≥0) : ℝ), ω) := by
    funext u; simp only [dkZf, pv]
  rw [e]
  exact Measurable.ite (measurableSet_eq_fun measurable_real_toNNReal measurable_const)
    measurable_const h1

theorem IsDkBoundaryDualProcess.ae_dkZf_eq
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, ∀ t, dkZf N X Y t ω = dkZ N X Y t ω := by
  filter_upwards [hP.continuous_dkZ] with ω h t using dkZf_eq_of_continuous h t

/-- **The progressive version solves the raw test-function martingale problem.** -/
theorem IsDkBoundaryDualProcess.isTestMPSolution_flat
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    IsTestMPSolution P 𝓖 (dkHDrift D0) (baseCov D0) openStripFin (dkZf N X Y) where
  adapted t := (stronglyMeasurable_dkZf hP t).measurable
  continuous := by
    filter_upwards [hP.continuous_dkZ] with ω h
    have e : (fun t => dkZf N X Y t ω) = fun t => dkZ N X Y t ω :=
      funext fun t => dkZf_eq_of_continuous h t
    rw [e]; exact h
  martingale f hf := by
    have hT := hP.isTestMPSolution
    refine martingale_of_ae_eq (hT.martingale f hf) (fun t => ?_) (fun t => ?_)
    · have hgc : Continuous (mpGenerator (dkHDrift D0) (baseCov D0) f) :=
        continuous_mpGenerator isOpen_openStripFin (continuousOn_dkHDrift D0)
          (continuous_baseCov D0).continuousOn hf
      have hpv : IsStronglyProgressive 𝓖 (pv (dkZ N X Y)) :=
        Representation.isStronglyProgressive_predVersion 𝓖 (stronglyMeasurable_dkZ hP)
      have hprog : IsStronglyProgressive 𝓖
          fun u ω => mpGenerator (dkHDrift D0) (baseCov D0) f (pv (dkZ N X Y) u ω) := fun T =>
        (hgc.measurable.comp (hpv T).measurable).stronglyMeasurable
      have hI := (Dyson.Angular.isStronglyProgressive_integral hprog).stronglyAdapted t
      have e : (fun ω => ∫ u in Ioc (0 : ℝ) t,
          mpGenerator (dkHDrift D0) (baseCov D0) f (dkZf N X Y u.toNNReal ω)) =
          fun ω => ∫ u in Ioc (0 : ℝ) t,
            mpGenerator (dkHDrift D0) (baseCov D0) f (pv (dkZ N X Y) u.toNNReal ω) :=
        funext fun ω => setIntegral_congr_fun measurableSet_Ioc fun u hu => by
          have : u.toNNReal ≠ 0 := by
            rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hu.1
          simp [dkZf, this]
      refine (hf.1.continuous.comp_stronglyMeasurable (stronglyMeasurable_dkZf hP t)).sub ?_
      rw [e]; exact hI
    · filter_upwards [hP.ae_dkZf_eq] with ω h
      simp only [h]

/-- The time-shift identity, on every path of the progressive version. -/
theorem integral_shift_dkZf (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    {g : (Fin 2 → ℝ) → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) (q r : ℝ≥0)
    (ω : Ω) :
    (∫ u in Ioc (0 : ℝ) (q + r : ℝ≥0), g (dkZf N X Y u.toNNReal ω)) -
        ∫ u in Ioc (0 : ℝ) q, g (dkZf N X Y u.toNNReal ω) =
      ∫ u in Ioc (0 : ℝ) r, g (dkZf N X Y (q + u.toNNReal) ω) := by
  set G : ℝ → ℝ := fun u => g (dkZf N X Y u.toNNReal ω) with hG
  have hGm : Measurable G := hg.measurable.comp (measurable_dkZf_path hP ω)
  have hii : ∀ a b : ℝ, IntervalIntegrable G volume a b := fun a b =>
    ⟨Measure.integrableOn_of_bounded (M := B) measure_Ioc_lt_top.ne
      hGm.aestronglyMeasurable (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hB _),
    Measure.integrableOn_of_bounded (M := B) measure_Ioc_lt_top.ne
      hGm.aestronglyMeasurable (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hB _)⟩
  rw [← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hii 0 (q : ℝ))
    (hii (q : ℝ) ((q + r : ℝ≥0) : ℝ))
  have e : ∫ u in (0 : ℝ)..r, g (dkZf N X Y (q + u.toNNReal) ω) = ∫ u in (0 : ℝ)..r, G (u + q) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg r)] at hu
    have hu0 : (0 : ℝ) ≤ u := hu.1
    have : (u + q).toNNReal = q + u.toNNReal := by
      rw [Real.toNNReal_add hu0 (NNReal.coe_nonneg q), Real.toNNReal_coe, add_comm]
    simp only [hG, this]
  have e2 := intervalIntegral.integral_comp_add_right G (q : ℝ) (a := 0) (b := r)
  rw [e, e2, zero_add, ← hadd, NNReal.coe_add, add_comm (r : ℝ)]
  ring

/-- **The restarted progressive version solves the raw test-function martingale problem for the
shifted filtration.** -/
theorem IsDkBoundaryDualProcess.isTestMPSolution_shift
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (q : ℝ≥0) :
    IsTestMPSolution P (shiftFiltration 𝓖 q) (dkHDrift D0) (baseCov D0) openStripFin
      (shiftProc (dkZf N X Y) q) where
  adapted r := (stronglyMeasurable_dkZf hP (q + r)).measurable
  continuous := hP.isTestMPSolution_flat.continuous.mono fun ω h => continuous_shiftProc h q
  martingale f hf := by
    have := hP.prob
    have hT := hP.isTestMPSolution_flat
    set g := mpGenerator (dkHDrift D0) (baseCov D0) f with hgdef
    have hgc : Continuous g := continuous_mpGenerator isOpen_openStripFin
      (continuousOn_dkHDrift D0) (continuous_baseCov D0).continuousOn hf
    obtain ⟨B, -, hB⟩ := exists_bound_mpGenerator isOpen_openStripFin
      (continuousOn_dkHDrift D0) (continuous_baseCov D0).continuousOn hf
    have hM := hT.martingale f hf
    set A : ℝ≥0 → Ω → ℝ := fun t ω => f (dkZf N X Y t ω) -
      ∫ u in Ioc (0 : ℝ) t, g (dkZf N X Y u.toNNReal ω) with hAdef
    have hc : StronglyMeasurable[shiftFiltration 𝓖 q ⊥]
        fun ω => A q ω - f (dkZf N X Y q ω) := by
      have : (shiftFiltration 𝓖 q ⊥ : MeasurableSpace Ω) = 𝓖 q := by simp
      rw [this]
      exact (hM.1 q).sub (hf.1.continuous.comp_stronglyMeasurable (stronglyMeasurable_dkZf hP q))
    obtain ⟨Cf, hCf⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
    have hci : Integrable (fun ω => A q ω - f (dkZf N X Y q ω)) P :=
      (hM.integrable q).sub (Integrable.of_bound
        ((hf.1.continuous.comp_stronglyMeasurable (stronglyMeasurable_dkZf hP q)).mono
          (𝓖.le q)).aestronglyMeasurable Cf (ae_of_all _ fun ω => hCf _))
    have hM2 := (martingale_shift hM q).sub (martingale_const_fun _ P hc hci)
    convert hM2 using 1
    funext r ω
    simp only [Pi.sub_apply, hAdef, shiftProc_apply]
    have := integral_shift_dkZf hP hgc hB q r ω
    linarith

end MP

end BlockBand.Diffusion
