module

public import BlockBand.Critical.JointRecovery.DerivativeEvaluation
public import BlockBand.Critical.JointRecovery.Hurwitz
public import BlockBand.Critical.FiniteReadback

/-!
# The energy axis of a random entire function

The energy axis of `F : EntireFunction (m + 1)` is `w ↦ F(w, 0, …, 0)` (`axis`). This file shows
that `EntireFunction m` is metrizable, that locally uniform convergence restricts to the energy
axis, and that evaluation of holomorphic partial derivatives `(F, z) ↦ ∂_a F(z)` is jointly
continuous.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction

/-- The compact-open state space `EntireFunction m` is regular (subspace of the uniform space
`C(ℂ^m, ℂ)`); with second countability and `T2` it is metrizable. -/
instance regularSpace_entireFunction (m : ℕ) : RegularSpace (EntireFunction m) :=
  inferInstanceAs (RegularSpace {F : C(Fin m → ℂ, ℂ) // Differentiable ℂ ⇑F})

/-- `EntireFunction m` is metrizable (Urysohn: regular, second countable, Hausdorff). -/
instance metrizableSpace_entireFunction (m : ℕ) :
    TopologicalSpace.MetrizableSpace (EntireFunction m) := inferInstance

/-- The energy axis `w ↦ F(w, 0, …, 0)` (`energySource w = Pi.single 0 w`). -/
def axis {m : ℕ} (F : EntireFunction (m + 1)) : ℂ → ℂ :=
  fun w => F (BlockBand.Critical.energySource w)

theorem energySource_eq_smul {m : ℕ} (w : ℂ) :
    (BlockBand.Critical.energySource w : Fin (m + 1) → ℂ) = w • Pi.single 0 1 := by
  funext a
  by_cases ha : a = 0
  · subst ha; simp [BlockBand.Critical.energySource]
  · simp [BlockBand.Critical.energySource, ha]

theorem continuous_energySource {m : ℕ} :
    Continuous (BlockBand.Critical.energySource : ℂ → Fin (m + 1) → ℂ) := by
  have : (BlockBand.Critical.energySource : ℂ → Fin (m + 1) → ℂ) =
      fun w => w • (Pi.single 0 1 : Fin (m + 1) → ℂ) := funext energySource_eq_smul
  rw [this]
  fun_prop

theorem energySource_zero {m : ℕ} :
    (BlockBand.Critical.energySource (0 : ℂ) : Fin (m + 1) → ℂ) = 0 := by
  rw [energySource_eq_smul, zero_smul]

theorem axis_apply {m : ℕ} (F : EntireFunction (m + 1)) (w : ℂ) :
    axis F w = F (BlockBand.Critical.energySource w) := rfl

theorem axis_zero {m : ℕ} (F : EntireFunction (m + 1)) : axis F 0 = F 0 := by
  rw [axis_apply, energySource_zero]

theorem differentiable_axis {m : ℕ} (F : EntireFunction (m + 1)) : Differentiable ℂ (axis F) := by
  have : axis F = fun w => F (w • (Pi.single 0 1 : Fin (m + 1) → ℂ)) := by
    funext w; rw [axis_apply, energySource_eq_smul]
  rw [this]
  exact F.differentiable.comp (differentiable_id.smul_const _)

/-- `D_0'(x) = ∂_{z_0} D(x, 0, …, 0)`. -/
theorem deriv_axis {m : ℕ} (F : EntireFunction (m + 1)) (x : ℂ) :
    deriv (axis F) x = partialDerivValue 0 F (BlockBand.Critical.energySource x) := by
  have hline : HasDerivAt (fun w : ℂ => w • (Pi.single 0 1 : Fin (m + 1) → ℂ))
      (Pi.single 0 1) x := by
    simpa using (hasDerivAt_id x).smul_const (Pi.single 0 1 : Fin (m + 1) → ℂ)
  have hcomp := (F.differentiable (x • (Pi.single 0 1 : Fin (m + 1) → ℂ))).hasFDerivAt.comp_hasDerivAt
    x hline
  have : axis F = fun w => F (w • (Pi.single 0 1 : Fin (m + 1) → ℂ)) := by
    funext w; rw [axis_apply, energySource_eq_smul]
  rw [this]
  change deriv (⇑F ∘ fun w => w • (Pi.single 0 1 : Fin (m + 1) → ℂ)) x = _
  rw [hcomp.deriv, partialDerivValue, energySource_eq_smul]

/-- Locally uniform convergence of entire functions restricts to the energy axis. -/
theorem tendstoLocallyUniformly_axis {m : ℕ} {ι : Type*} {l : Filter ι}
    {F : ι → EntireFunction (m + 1)} {G : EntireFunction (m + 1)} (h : Tendsto F l (𝓝 G)) :
    TendstoLocallyUniformly (fun i => axis (F i)) (axis G) l :=
  (tendsto_iff_tendstoLocallyUniformly.mp h).comp _ continuous_energySource

/-- The coordinate line through `z` in direction `a`, as a continuous map. -/
def lineCM {m : ℕ} (a : Fin m) (z : Fin m → ℂ) : C(ℂ, Fin m → ℂ) :=
  ⟨EntireFunction.coordinateLine a z, EntireFunction.continuous_coordinateLine a z⟩

theorem continuous_lineCM {m : ℕ} (a : Fin m) : Continuous (lineCM a) := by
  have hc : Continuous fun p : (Fin m → ℂ) × ℂ => EntireFunction.coordinateLine a p.1 p.2 := by
    unfold EntireFunction.coordinateLine; fun_prop
  exact (ContinuousMap.curry ⟨_, hc⟩).continuous

/-- **Joint continuity of derivative evaluation**: if `F i → G` locally uniformly and
`z i → z₀`, then `∂_a F i (z i) → ∂_a G (z₀)`. Arbitrary filter. -/
theorem tendsto_partialDerivValue {m : ℕ} {ι : Type*} {l : Filter ι}
    {F : ι → EntireFunction m} {G : EntireFunction m} {z : ι → Fin m → ℂ} {z₀ : Fin m → ℂ}
    (hF : Tendsto F l (𝓝 G)) (hz : Tendsto z l (𝓝 z₀)) (a : Fin m) :
    Tendsto (fun i => partialDerivValue a (F i) (z i)) l (𝓝 (partialDerivValue a G z₀)) := by
  let S : EntireFunction m × (Fin m → ℂ) → C(ℂ, ℂ) := fun p =>
    (toContinuousMap p.1).comp (lineCM a p.2)
  have hS : Continuous S := by
    have h1 : Continuous fun p : EntireFunction m × (Fin m → ℂ) =>
        (lineCM a p.2, toContinuousMap p.1) :=
      ((continuous_lineCM a).comp continuous_snd).prodMk
        (isEmbedding_toContinuousMap.continuous.comp continuous_fst)
    exact ContinuousMap.continuous_comp'.comp h1
  have hlim : Tendsto (fun i => S (F i, z i)) l (𝓝 (S (G, z₀))) :=
    (hS.tendsto _).comp (hF.prodMk_nhds hz)
  have hloc := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  have hd := (tendstoLocallyUniformlyOn_univ.mpr (tendstoLocallyUniformly_deriv hloc (fun i =>
    EntireFunction.differentiable_coordinateSlice a (z i) (F i)))).tendsto_at (mem_univ 0)
  have h2 : Tendsto (fun i => deriv (fun w => F i (EntireFunction.coordinateLine a (z i) w)) 0)
      l (𝓝 (deriv (fun w => G (EntireFunction.coordinateLine a z₀ w)) 0)) := hd
  simpa only [EntireFunction.deriv_coordinateSlice_zero] using h2

/-- `(F, z) ↦ ∂_a F(z)` is jointly continuous on `EntireFunction m × ℂ^m`. -/
theorem continuous_partialDerivValue {m : ℕ} (a : Fin m) :
    Continuous fun p : EntireFunction m × (Fin m → ℂ) => partialDerivValue a p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_partialDerivValue (continuous_fst.tendsto p) (continuous_snd.tendsto p) a

end BlockBand.Critical.JointRecovery
