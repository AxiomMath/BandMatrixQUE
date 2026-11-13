module

public import BlockBand.Endpoints.Poisson.SequentialCollarsComponents
public import BlockBand.Endpoints.Poisson.SingleCollarAssemblyAux

/-!
# The length marginal of the grown path and the law of a component's interval source

The first `r` blocks of the grown path form a path of length `r`, so the interval source of a
component can be read off the grown path.

* `scp_growthPathLaw_map_pathAt`: for `r ≥ 1`,
  `(growthPathLaw W b).map (pathAt W r) = pathLaw W r b`. (For `r = 0` both port bonds of
  `pathAt W 0` are `B_0`, so the identity fails when `W ≥ 1`.)
* `scpLift r`: a measurable section of `pathAt W r` (`scp_pathAt_lift`, `r ≥ 1`); the interval
  source only depends on `pathAt` (`scp_intervalSource_congr`), so it factors through the lift
  (`scp_intervalSource_lift_pathAt`).
* `scp_map_intervalSource_lift`: if `ρ` has law `pathLaw W r b` under `μ`, then
  `μ.map (intervalSource ∘ scpLift r ∘ ρ) = growthPathLaw.map (intervalSource …)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath (intervalSource growthPathLaw GrowthPath pathAt
  tagResponse boundaryToInterior fullInverse fullPathMatrix)
open BlockBand.Internal.Contracts.Layers (PathSample pathLaw ginibreMeasure)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure)

section Marginal

variable {W : ℕ}

/-- The bond indices read by `pathAt W r`: internal bond `i ↦ r-1-i`, ports `r` and `0`. -/
def scpBondIdx (r : ℕ) : Fin (r - 1) ⊕ Fin 2 → ℕ
  | Sum.inl i => r - 1 - i.val
  | Sum.inr c => if c = 0 then r else 0

theorem scp_bondIdx_injective {r : ℕ} (hr : 1 ≤ r) : Function.Injective (scpBondIdx r) := by
  rintro (i | c) (i' | c') h <;> simp only [scpBondIdx] at h
  · have := i.isLt; have := i'.isLt
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have := i.isLt
    split_ifs at h <;> omega
  · have := i'.isLt
    split_ifs at h <;> omega
  · congr 1
    split_ifs at h with h1 h2 h2
    · rw [h1, h2]
    · omega
    · omega
    · exact (Fin.eq_one_of_ne_zero c h1).trans (Fin.eq_one_of_ne_zero c' h2).symm

/-- The block readout of `pathAt W r`. -/
def scpBlockRead (r : ℕ) (g : ℕ → Matrix (Fin W) (Fin W) ℂ) : Fin r → Matrix (Fin W) (Fin W) ℂ :=
  fun i => g (r - 1 - i.val)

/-- The bond readout of `pathAt W r`. -/
def scpBondRead (r : ℕ) (h : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    (Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) × (Fin 2 → Matrix (Fin W) (Fin W) ℂ) :=
  (fun i => (h (r - 1 - i.val))ᴴ, ![h r, h 0])

theorem scp_measurable_blockRead (r : ℕ) : Measurable (scpBlockRead (W := W) r) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem scp_measurable_bondRead (r : ℕ) : Measurable (scpBondRead (W := W) r) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun i => measurable_conjTranspose'.comp (measurable_pi_apply _)
  · refine measurable_pi_iff.mpr fun c => ?_
    fin_cases c
    · exact measurable_pi_apply _
    · exact measurable_pi_apply _

theorem scp_measurable_pathAt (r : ℕ) : Measurable (pathAt (W := W) r) := by
  have h : pathAt (W := W) r = fun ω => (scpBlockRead r ω.1, scpBondRead r ω.2) := rfl
  rw [h]
  exact ((scp_measurable_blockRead r).comp measurable_fst).prodMk
    ((scp_measurable_bondRead r).comp measurable_snd)

/-- For `r ≥ 1`, `(growthPathLaw W b).map (pathAt W r) = pathLaw W r b`. -/
theorem scp_growthPathLaw_map_pathAt (b : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    (growthPathLaw W b).map (pathAt W r) = pathLaw W r b := by
  set μA := Measure.infinitePi fun _ : ℕ => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := Measure.infinitePi fun _ : ℕ =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have : IsProbabilityMeasure (gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) :=
    isProbabilityMeasure_gue' _ _
  have : IsProbabilityMeasure (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
    isProbabilityMeasure_gin' _ _ _
  have hAm := scp_measurable_blockRead (W := W) r
  have hBm := scp_measurable_bondRead (W := W) r
  -- the blocks
  have hA : μA.map (scpBlockRead (W := W) r) =
      Measure.pi fun _ : Fin r => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
    have hinj : Function.Injective (fun i : Fin r => r - 1 - i.val) := by
      intro i i' h; have := i.isLt; have := i'.isLt
      exact Fin.ext (by simp only at h; omega)
    have h := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) hinj
    exact h.trans (Measure.infinitePi_eq_pi _)
  -- the bonds
  have hB : μB.map (scpBondRead (W := W) r) =
      (Measure.pi fun _ : Fin (r - 1) => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod
        (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := by
    have h1 := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
      (scp_bondIdx_injective hr)
    replace h1 := h1.trans (Measure.infinitePi_eq_pi _)
    have e1 := measurePreserving_sumPiEquivProdPi
      (fun _ : Fin (r - 1) ⊕ Fin 2 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
    have e2 : MeasurePreserving
        (fun v : (Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) => fun i => (v i)ᴴ)
        (Measure.pi fun _ : Fin (r - 1) => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
        (Measure.pi fun _ : Fin (r - 1) => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
      measurePreserving_pi _ _ fun _ =>
        ⟨measurable_conjTranspose', ginibre_map_conjTranspose W _⟩
    have e3 := (e2.prod (MeasurePreserving.id
      (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))))).comp e1
    have hfac : scpBondRead (W := W) r =
        (Prod.map (fun v : (Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) => fun i => (v i)ᴴ) id ∘
          MeasurableEquiv.sumPiEquivProdPi _) ∘ (fun h j => h (scpBondIdx r j)) := by
      funext h
      simp only [scpBondRead, Function.comp_apply, Prod.map]
      refine Prod.ext rfl ?_
      funext c
      fin_cases c
      · simp [scpBondIdx, MeasurableEquiv.sumPiEquivProdPi]
      · simp [scpBondIdx, MeasurableEquiv.sumPiEquivProdPi]
    rw [hfac, ← Measure.map_map e3.measurable (by fun_prop), h1, e3.map_eq]
  -- assemble
  have hfun : pathAt W r = Prod.map (scpBlockRead (W := W) r) (scpBondRead (W := W) r) := by
    funext ω; rfl
  unfold growthPathLaw
  rw [hfun, ← Measure.map_prod_map _ _ hAm hBm, hA, hB]
  rfl

end Marginal

section Lift

variable {W : ℕ}

/-- A section of `pathAt W r`: the grown path whose first `r` blocks and `r+1` bonds are those of
a given path sample (other coordinates `0`). -/
def scpLift (r : ℕ) (x : PathSample W r) : GrowthPath W :=
  (fun k => if h : k < r then x.1 ⟨r - 1 - k, by omega⟩ else 0,
    fun k => if h0 : k = 0 then x.2.2 1 else if k = r then x.2.2 0 else
      if h : k < r then (x.2.1 ⟨r - 1 - k, by omega⟩)ᴴ else 0)

theorem scp_pathAt_lift {r : ℕ} (hr : 1 ≤ r) (x : PathSample W r) :
    pathAt W r (scpLift r x) = x := by
  obtain ⟨A, B, C⟩ := x
  simp only [pathAt, scpLift]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    have hi := i.isLt
    simp only [show r - 1 - i.val < r by omega, dite_true]
    congr 1; ext; simp; omega
  · funext i
    have hi := i.isLt
    simp only [show ¬ (r - 1 - i.val = 0) by omega, dite_false,
      show ¬ (r - 1 - i.val = r) by omega, ite_false, show r - 1 - i.val < r by omega, dite_true,
      conjTranspose_conjTranspose]
    congr 1; ext; simp; omega
  · funext c
    fin_cases c
    · simp [show ¬ r = 0 by omega]
    · simp

theorem scp_measurable_lift (r : ℕ) : Measurable (scpLift (W := W) r) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun k => ?_
    split_ifs
    · exact (measurable_pi_apply _).comp measurable_fst
    · exact measurable_const
  · refine measurable_pi_iff.mpr fun k => ?_
    split_ifs
    · exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    · exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    · exact measurable_conjTranspose'.comp
        ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))
    · exact measurable_const

/-- The interval source depends on the grown path only through `pathAt`. -/
theorem scp_intervalSource_congr (b E : ℝ) (r : ℕ) (q : ℝ → ℝ) {ω ω' : GrowthPath W}
    (h : pathAt W r ω = pathAt W r ω') :
    intervalSource b E W r q ω = intervalSource b E W r q ω' := by
  simp only [intervalSource, tagResponse, boundaryToInterior, fullInverse, fullPathMatrix, h]

theorem scp_intervalSource_lift_pathAt (b E : ℝ) {r : ℕ} (hr : 1 ≤ r) (q : ℝ → ℝ)
    (ω : GrowthPath W) :
    intervalSource b E W r q (scpLift r (pathAt W r ω)) = intervalSource b E W r q ω :=
  scp_intervalSource_congr b E r q (scp_pathAt_lift hr _)

/-- **Law of an interval source read through a path sample.** -/
theorem scp_map_intervalSource_lift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r : ℕ}
    {ρ : Ω → PathSample W r} (b E : ℝ) (hr : 1 ≤ r) (q : ℝ → ℝ)
    (hρ : HasLaw ρ (pathLaw W r b) μ) :
    μ.map (fun x => intervalSource b E W r q (scpLift r (ρ x))) =
      (growthPathLaw W b).map (intervalSource b E W r q) := by
  have hg : Measurable fun x : PathSample W r => intervalSource b E W r q (scpLift r x) :=
    (sca2_measurable_intervalSource b E W r q).comp (scp_measurable_lift r)
  have h1 : μ.map (fun x => intervalSource b E W r q (scpLift r (ρ x))) =
      (μ.map ρ).map (fun x => intervalSource b E W r q (scpLift r x)) :=
    (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hρ.aemeasurable).symm
  rw [h1, hρ.map_eq, ← scp_growthPathLaw_map_pathAt b hr,
    Measure.map_map hg (scp_measurable_pathAt r)]
  congr 1
  funext ω
  exact scp_intervalSource_lift_pathAt b E hr q ω

end Lift

end BlockBand.Endpoints
