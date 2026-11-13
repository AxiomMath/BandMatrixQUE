module
public import BlockBand.SourceProcess.Stochastic.Levy.Exponential
public import BlockBand.SourceProcess.Stochastic.Assembly.ItoUniverse
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Lévy's characterization: the exponential martingales

Setting: an arbitrary filtered probability space `(Ω, 𝓖, Q)` (raw filtration, no usual
conditions), `Ω : Type u`.

* `IsLevyMartingale Q 𝓖 M`: the hypotheses of Lévy's characterization in modification form
  (`M` progressive, a.s. continuous, `M_0 = 0` a.s., and `M^i`, `M^i M^j - δ_ij t` have
  `𝓖`-martingale modifications).
* `hasMartingaleModification_levyPhi`: for a continuous semimartingale with characteristics
  `(0, I)`, `e^{|u|²t/2} cos(⟨u, M_t⟩ - θ) - (same at 0)` has a martingale modification. Proof:
  the Itô formula (`semimartingaleItoFormulaU_holds`) with zero Itô drift
  (`itoDrift_levyPhi`), then removal of the localization by domination
  (`hasMartingaleModification_of_localized`; the process is bounded by `2 e^{|u|²t/2}` on `[0,t]`).
* `integral_mul_levyProc`: hence `∫ g · φ(t, M_t) = ∫ g · φ(s, M_s)` for `s ≤ t` and every
  `𝓖_s`-measurable `g` with `|g| ≤ 1`.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

universe u

variable {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Hypotheses of Lévy's characterization** (modification form, raw filtration): `M` is
progressively measurable, has a.s. continuous paths, `M_0 = 0` a.s., and each coordinate
`M^i` and each `M^i M^j - δ_ij t` has a `𝓖`-martingale modification. -/
structure IsLevyMartingale (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  progressive : IsStronglyProgressive 𝓖 M
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => M t ω
  zero : ∀ᵐ ω ∂Q, M 0 ω = 0
  mart : ∀ i, HasMartingaleModification Q 𝓖 fun t ω => M t ω i
  bracket : ∀ i j, HasMartingaleModification Q 𝓖 fun t ω =>
    M t ω i * M t ω j - if i = j then (t : ℝ) else 0

/-- With every path continuous, adaptedness suffices for progressive measurability. -/
theorem IsLevyMartingale.of_forall_continuous {M : ℝ≥0 → Ω → Fin d → ℝ}
    (hadapt : ∀ t, StronglyMeasurable[𝓖 t] (M t)) (hc : ∀ ω, Continuous fun t => M t ω)
    (h0 : ∀ᵐ ω ∂Q, M 0 ω = 0) (hmart : ∀ i, HasMartingaleModification Q 𝓖 fun t ω => M t ω i)
    (hbr : ∀ i j, HasMartingaleModification Q 𝓖 fun t ω =>
      M t ω i * M t ω j - if i = j then (t : ℝ) else 0) : IsLevyMartingale Q 𝓖 M :=
  ⟨StronglyAdapted.isStronglyProgressive_of_continuous hadapt hc, ae_of_all _ hc, h0, hmart, hbr⟩

/-- A Lévy martingale is a continuous semimartingale with characteristics `(0, I)`. -/
theorem IsLevyMartingale.isContinuousSemimartingale {M : ℝ≥0 → Ω → Fin d → ℝ}
    (hM : IsLevyMartingale Q 𝓖 M) :
    IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1) := by
  have hcomp : ∀ᵐ ω ∂Q, ∀ i t, smCompensated M (fun _ _ => 0) i t ω = M t ω i := by
    filter_upwards [hM.zero] with ω hω i t
    simp [smCompensated, hω]
  have hint : ∀ (c : ℝ) (t : ℝ≥0), ∫ s in Ioc (0 : ℝ) t, c = (t : ℝ) * c := fun c t => by
    simp
  refine ⟨hM.progressive.stronglyAdapted, hM.progressive, hM.continuous,
    isStronglyProgressive_const _ _, isStronglyProgressive_const _ _,
    ae_of_all _ fun ω t => ⟨fun i => by simp, fun i j => integrableOn_const (by simp)⟩,
    ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top_const, ae_of_all _ fun _ => tendsto_const_nhds,
      fun _ => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · refine hasMartingaleModification_congr (hM.mart i) fun t => ?_
    filter_upwards [hcomp] with ω hω
    simp only [stoppedProcess_eq_stopTime, stopTime_top, hω]
  · refine hasMartingaleModification_congr (hM.bracket i j) fun t => ?_
    filter_upwards [hcomp] with ω hω
    simp only [stoppedProcess_eq_stopTime, stopTime_top, hω, hint, Matrix.one_apply]
    split_ifs <;> simp

/-- The real exponential process `φ(t, M_t) = e^{|u|²t/2} cos(⟨u, M_t⟩ - θ)`. -/
def levyProc (u : Fin d → ℝ) (θ : ℝ) (M : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  levyPhi u θ ((t : ℝ), M t ω)

theorem sqNorm_nonneg (u : Fin d → ℝ) : 0 ≤ sqNorm u :=
  Finset.sum_nonneg fun i _ => sq_nonneg (u i)

omit [MeasurableSpace Ω] in
theorem abs_levyProc_le (u : Fin d → ℝ) (θ : ℝ) (M : ℝ≥0 → Ω → Fin d → ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (ω : Ω) : |levyProc u θ M s ω| ≤ Real.exp (sqNorm u / 2 * t) :=
  (levyPhi_abs_le u θ _).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
    (NNReal.coe_le_coe.2 hst) (div_nonneg (sqNorm_nonneg u) zero_le_two)))

variable [IsProbabilityMeasure Q]

/-- **The exponential martingales.** -/
theorem hasMartingaleModification_levyPhi {M : ℝ≥0 → Ω → Fin d → ℝ}
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1)) (u : Fin d → ℝ)
    (θ : ℝ) : HasMartingaleModification Q 𝓖
      fun t ω => levyProc u θ M t ω - levyProc u θ M 0 ω := by
  have H := semimartingaleItoFormulaU_holds.{u} d Ω Q 𝓖 M _ _ hM univ isOpen_univ
    (ae_of_all _ fun _ _ => mem_univ _) (levyPhi u θ) (continuous_levyPhi u θ).measurable
    (contDiff_levyPhi u θ).contDiffOn
  obtain ⟨τ, -, hτ, hloc⟩ := H.localizing
  refine hasMartingaleModification_of_localized hτ (fun n => ?_) fun t =>
    ⟨2 * Real.exp (sqNorm u / 2 * t), ae_of_all _ fun ω s hs => ?_⟩
  · have e : smCompensated (fun t ω (_ : Fin 1) => levyPhi u θ ((t : ℝ), M t ω))
        (fun t ω (_ : Fin 1) => itoDrift (levyPhi u θ) (M t ω) t 0 1) 0 =
        fun t ω => levyProc u θ M t ω - levyProc u θ M 0 ω := by
      funext t ω
      simp [smCompensated, itoDrift_levyPhi, levyProc]
    have := (hloc n).1 0
    rwa [e] at this
  · calc |levyProc u θ M s ω - levyProc u θ M 0 ω|
        ≤ |levyProc u θ M s ω| + |levyProc u θ M 0 ω| := abs_sub _ _
      _ ≤ Real.exp (sqNorm u / 2 * t) + Real.exp (sqNorm u / 2 * t) :=
        add_le_add (abs_levyProc_le u θ M hs ω) (abs_levyProc_le u θ M zero_le ω)
      _ = _ := by ring

theorem measurable_levyProc {M : ℝ≥0 → Ω → Fin d → ℝ} (hM : ∀ t, StronglyMeasurable[𝓖 t] (M t))
    (u : Fin d → ℝ) (θ : ℝ) (t : ℝ≥0) : StronglyMeasurable[𝓖 t] (levyProc u θ M t) :=
  ((continuous_levyPhi u θ).comp (Continuous.prodMk_right (t : ℝ))).comp_stronglyMeasurable
    (hM t)

/-- **Weighted martingale identity.** For `s ≤ t` and `𝓖_s`-measurable `g` with `|g| ≤ 1`,
`∫ g φ(t, M_t) dQ = ∫ g φ(s, M_s) dQ`. -/
theorem integral_mul_levyProc {M : ℝ≥0 → Ω → Fin d → ℝ}
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1)) (u : Fin d → ℝ)
    (θ : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {g : Ω → ℝ} (hg : StronglyMeasurable[𝓖 s] g)
    (hgb : ∀ ω, |g ω| ≤ 1) :
    ∫ ω, g ω * levyProc u θ M t ω ∂Q = ∫ ω, g ω * levyProc u θ M s ω ∂Q := by
  obtain ⟨N, hN, hNX⟩ := hasMartingaleModification_levyPhi hM u θ
  have hgm : StronglyMeasurable g := hg.mono (𝓖.le s)
  have hint : ∀ r, Integrable (fun ω => g ω * levyProc u θ M r ω) Q := fun r => by
    refine Integrable.of_bound (hgm.mul ((measurable_levyProc hM.adapted u θ r).mono
      (𝓖.le r))).aestronglyMeasurable (Real.exp (sqNorm u / 2 * r)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hgb ω) |>.trans (abs_levyProc_le u θ M le_rfl ω)
  have hN' : ∫ ω, g ω * N t ω ∂Q = ∫ ω, g ω * N s ω ∂Q := by
    have hgN : ∀ r, Integrable (g * N r) Q := fun r =>
      ((hN.integrable r).bdd_mul (c := 1) hgm.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω))
    calc ∫ ω, g ω * N t ω ∂Q = ∫ ω, (Q[g * N t | 𝓖 s]) ω ∂Q :=
          (integral_condExp (𝓖.le s)).symm
      _ = ∫ ω, (g * Q[N t | 𝓖 s]) ω ∂Q :=
          integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg (hgN t) (hN.integrable t))
      _ = ∫ ω, g ω * N s ω ∂Q := integral_congr_ae
          ((hN.condExp_ae_eq hst).mono fun ω hω => by simp only [Pi.mul_apply, hω])
  have hrep : ∀ r, ∫ ω, g ω * N r ω ∂Q =
      ∫ ω, g ω * levyProc u θ M r ω ∂Q - ∫ ω, g ω * levyProc u θ M 0 ω ∂Q := fun r => by
    rw [← integral_sub (hint r) (hint 0)]
    exact integral_congr_ae ((hNX r).mono fun ω hω => by simp only [hω]; ring)
  have := hN'
  rw [hrep, hrep] at this
  linarith

end BlockBand.SourceProcess.Stochastic.Levy
