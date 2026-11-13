module

public import BlockBand.Palm.MomentFlow.BridgeBrownian
public import Mathlib.MeasureTheory.Constructions.Projective

/-!
# The Markov restart of the matrix flow

For `0 ≤ a' ≤ a` with `d = a - a'`, the **restart map**
`restartMap a' a (G, B) = (G + B(d), B(d + ·) - B(d))` (`shiftPath` on every Wiener coordinate)
* preserves the laws: `(flowLaw N a').map (restartMap a' a) = flowLaw N a` (`map_restartMap`);
* intertwines the flows after time `a`: `flowMatrix F a (restartMap a' a ω) σ = flowMatrix F a' ω σ`
  for every sample and every `σ ≥ a` (`flowMatrix_restartMap`), hence the same eigenvalue paths,
  overlaps and rates (`flowEigenvalue_restartMap`, `flowOverlap_restartMap`, `flowRate_restartMap`).

Ingredients proved here: uniqueness of a finite measure on `C(ℝ≥0, ℝ)` with given
finite-dimensional marginals (`continuousPath_measure_ext`, from Mathlib's
`borel_eq_iSup_comap_eval` and `IsProjectiveLimit.unique`), invariance of the constructed Wiener
law under the shift (`map_shiftPath_canonicalWienerLaw`, via Mathlib's `IsPreBrownianReal.shift`),
and independence of `(G_{a'}, B|_{[0,d]})` from the shifted future
(`commonWienerFuture_independent_old_past`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal

variable {N : ℕ}

/-!
## Measures on continuous paths are determined by their finite-dimensional marginals
-/

theorem measurableSpace_continuousPath_eq :
    (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.comap (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) MeasurableSpace.pi := by
  change borel C(ℝ≥0, ℝ) = _
  rw [ContinuousMap.borel_eq_iSup_comap_eval, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  congr 1

theorem measurable_coeFn_continuousPath :
    Measurable (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) :=
  Measurable.of_eval fun t => ContinuousMap.measurable_eval t

/-- Measurability into `C(ℝ≥0, ℝ)` from measurability of the evaluations (any σ-algebra). -/
theorem measurable_continuousPath_of_eval {Z : Type*} {m : MeasurableSpace Z}
    {g : Z → C(ℝ≥0, ℝ)} (h : ∀ t, Measurable fun z => g z t) : Measurable g :=
  ContinuousMap.measurable_iff_eval.2 h

/-- `Measurable.of_eval` for an arbitrary σ-algebra on the domain. -/
theorem measurable_pi_of_eval' {Z ι : Type*} {m : MeasurableSpace Z} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {g : Z → ∀ i, β i} (h : ∀ i, Measurable fun z => g z i) :
    Measurable g :=
  Measurable.of_eval h

/-- Two finite measures on `C(ℝ≥0, ℝ)` with the same finite-dimensional marginals are equal. -/
theorem continuousPath_measure_ext {μ ν : Measure C(ℝ≥0, ℝ)} [IsFiniteMeasure μ]
    (h : ∀ I : Finset ℝ≥0, μ.map (fun f : C(ℝ≥0, ℝ) => I.restrict (f : ℝ≥0 → ℝ)) =
      ν.map (fun f : C(ℝ≥0, ℝ) => I.restrict (f : ℝ≥0 → ℝ))) : μ = ν := by
  have hres : ∀ I : Finset ℝ≥0, Measurable (I.restrict (π := fun _ : ℝ≥0 => ℝ)) := fun I =>
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hcomp : ∀ (ρ : Measure C(ℝ≥0, ℝ)) (I : Finset ℝ≥0),
      (ρ.map (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ))).map I.restrict =
        ρ.map (fun f : C(ℝ≥0, ℝ) => I.restrict (f : ℝ≥0 → ℝ)) := fun ρ I => by
    rw [Measure.map_map (hres I) measurable_coeFn_continuousPath]; rfl
  have hμ : IsProjectiveLimit (μ.map (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)))
      (fun I => μ.map (fun f : C(ℝ≥0, ℝ) => I.restrict (f : ℝ≥0 → ℝ))) := fun I => hcomp μ I
  have hν : IsProjectiveLimit (ν.map (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)))
      (fun I => μ.map (fun f : C(ℝ≥0, ℝ) => I.restrict (f : ℝ≥0 → ℝ))) := fun I =>
    (hcomp ν I).trans (h I).symm
  have heq := hμ.unique hν
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ))
      MeasurableSpace.pi] A := by
    rw [← measurableSpace_continuousPath_eq]; exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [← Measure.map_apply measurable_coeFn_continuousPath hB,
    ← Measure.map_apply measurable_coeFn_continuousPath hB, heq]

/-!
## The shift of a continuous path
-/

/-- `f ↦ f(d + ·) - f(d)`. -/
def shiftPath (d : ℝ≥0) (f : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun t := f (d + t) - f d
  continuous_toFun := (f.continuous.comp (continuous_const.add continuous_id)).sub continuous_const

theorem shiftPath_apply (d : ℝ≥0) (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    shiftPath d f t = f (d + t) - f d := rfl

theorem measurable_shiftPath (d : ℝ≥0) : Measurable (shiftPath d) := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  exact (ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _)

/-- The constructed Wiener law is invariant under the shift. -/
theorem map_shiftPath_canonicalWienerLaw (d : ℝ≥0) :
    canonicalWienerLaw.map (shiftPath d) = canonicalWienerLaw := by
  refine continuousPath_measure_ext fun I => ?_
  have hres : Measurable (fun f : C(ℝ≥0, ℝ) => I.restrict (f : ℝ≥0 → ℝ)) :=
    (Measurable.of_eval fun _ => measurable_pi_apply _).comp measurable_coeFn_continuousPath
  rw [Measure.map_map hres (measurable_shiftPath d)]
  have h1 := (canonicalWiener_isBrownian.toIsPreBrownianReal.shift d).hasLaw I
  have h2 := canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw I
  rw [h2.map_eq]
  exact h1.map_eq

/-!
## The restart map
-/

/-- Shift every Wiener coordinate. -/
def shiftNoise (d : ℝ≥0) (B : FlowNoise N) : FlowNoise N := fun q => shiftPath d (B q)

theorem measurable_shiftNoise (d : ℝ≥0) : Measurable (shiftNoise (N := N) d) :=
  Measurable.of_eval fun q => (measurable_shiftPath d).comp (measurable_pi_apply q)

/-- The restart map `(G, B) ↦ (G + B(a - a'), B(a - a' + ·) - B(a - a'))`. -/
def restartMap (a' a : ℝ) (ω : FlowSample N) : FlowSample N :=
  (ω.1 + hermitianBrownian ω.2 (a - a'), shiftNoise (Real.toNNReal (a - a')) ω.2)

theorem measurable_restartMap (a' a : ℝ) : Measurable (restartMap (N := N) a' a) :=
  (measurable_matrix_add.comp (measurable_fst.prodMk
    ((measurable_hermitianBrownian _).comp measurable_snd))).prodMk
    ((measurable_shiftNoise _).comp measurable_snd)

theorem brownianOfCoords_sub (r r' : ((Fin N × Fin N) × Fin 2) → ℝ) :
    brownianOfCoords N (r - r') = brownianOfCoords N r - brownianOfCoords N r' := by
  ext i j
  simp only [brownianOfCoords, circularBrownianCoordinates, Matrix.of_apply, Matrix.sub_apply,
    Pi.sub_apply, Complex.ofReal_sub, map_sub, map_div₀, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- **Intertwining**: after time `a` the restarted flow is the original flow, for every sample. -/
theorem flowMatrix_restartMap (F : Matrix (Fin N) (Fin N) ℂ) {a' a σ : ℝ} (ha : a' ≤ a)
    (hσ : a ≤ σ) (ω : FlowSample N) :
    flowMatrix F a (restartMap a' a ω) σ = flowMatrix F a' ω σ := by
  have hshift : hermitianBrownian (shiftNoise (Real.toNNReal (a - a')) ω.2) (σ - a) =
      hermitianBrownian ω.2 (σ - a') - hermitianBrownian ω.2 (a - a') := by
    rw [hermitianBrownian_eq_coords, hermitianBrownian_eq_coords, hermitianBrownian_eq_coords,
      ← brownianOfCoords_sub]
    congr 1
    funext q
    simp only [shiftNoise, shiftPath_apply, Pi.sub_apply]
    congr 2
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left (sub_nonneg.2 ha),
      max_eq_left (sub_nonneg.2 hσ), max_eq_left (by linarith : (0 : ℝ) ≤ σ - a')]
    ring
  simp only [flowMatrix, restartMap, hshift]
  abel

theorem flowEigenvalue_restartMap (F : Matrix (Fin N) (Fin N) ℂ) {a' a σ : ℝ} (ha : a' ≤ a)
    (hσ : a ≤ σ) (ω : FlowSample N) (k : Fin N) :
    flowEigenvalue F a (restartMap a' a ω) σ k = flowEigenvalue F a' ω σ k := by
  simp only [flowEigenvalue, flowMatrix_restartMap F ha hσ]

theorem flowOverlap_restartMap (F : Matrix (Fin N) (Fin N) ℂ) {a' a σ : ℝ} (ha : a' ≤ a)
    (hσ : a ≤ σ) (q : Fin N → ℂ) (k : Fin N) (ω : FlowSample N) :
    flowOverlap F a q σ k (restartMap a' a ω) = flowOverlap F a' q σ k ω := by
  simp only [flowOverlap, flowMatrix_restartMap F ha hσ]

theorem flowRate_restartMap (F : Matrix (Fin N) (Fin N) ℂ) {a' a σ : ℝ} (ha : a' ≤ a)
    (hσ : a ≤ σ) (ω : FlowSample N) :
    flowRate F a (restartMap a' a ω) σ = flowRate F a' ω σ := by
  funext k l
  simp only [flowRate, flowEigenvalue_restartMap F ha hσ]

/-!
## The restart map preserves the law
-/

/-- **Restart map preserves the law.** For `0 ≤ a' ≤ a`, the restart map pushes `flowLaw N a'` to
`flowLaw N a`. -/
theorem map_restartMap {a' a : ℝ} (ha' : 0 ≤ a') (ha : a' ≤ a) :
    (flowLaw N a').map (restartMap a' a) = flowLaw N a := by
  set d : ℝ≥0 := Real.toNNReal (a - a')
  set X : FlowSample N → Matrix (Fin N) (Fin N) ℂ := fun ω => ω.1 + hermitianBrownian ω.2 (a - a')
  set Y : FlowSample N → FlowNoise N := fun ω => shiftNoise d ω.2
  have hX : Measurable X := measurable_matrix_add.comp (measurable_fst.prodMk
    ((measurable_hermitianBrownian _).comp measurable_snd))
  have hY : Measurable Y := (measurable_shiftNoise _).comp measurable_snd
  -- law of `X`
  have hlawX : (flowLaw N a').map X = gueMeasure (Fin N) (Real.toNNReal (a / N)) := by
    have h := map_flowMatrix_sub (N := N) 0 ha' ha
    have e : (fun ω : FlowSample N => flowMatrix 0 a' ω a - 0) = X := by
      funext ω; simp [flowMatrix, X]
    rwa [e] at h
  -- law of `Y`
  have hlawY : (flowLaw N a').map Y = commonWienerLaw ((Fin N × Fin N) × Fin 2) := by
    have e : Y = shiftNoise d ∘ Prod.snd := rfl
    rw [e, ← Measure.map_map (measurable_shiftNoise d) measurable_snd]
    unfold flowLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul, commonWienerLaw,
      show shiftNoise (N := N) d = fun B q => shiftPath d (B q) from rfl,
      Measure.pi_map_pi (fun _ => (measurable_shiftPath d).aemeasurable)]
    congr 1
    funext _
    exact map_shiftPath_canonicalWienerLaw d
  -- independence of `X` and `Y`
  have hind : IndepFun X Y (flowLaw N a') := by
    have h := commonWienerFuture_independent_old_past (κ := (Fin N × Fin N) × Fin 2)
      (gueMeasure (Fin N) (Real.toNNReal (a' / N))) d
    rw [IndepFun_iff_Indep] at h ⊢
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h.symm ?_) ?_
    · -- `σ(X) ≤ σ(old state, past)`
      refine Measurable.comap_le ?_
      have : X = (fun z : Matrix (Fin N) (Fin N) ℂ × (((Fin N × Fin N) × Fin 2) → Set.Iic d → ℝ) =>
          z.1 + brownianOfCoords N (fun q => z.2 q ⟨d, le_rfl⟩)) ∘
          (fun x : FlowSample N => (x.1, commonWienerPast d x.2)) := by
        funext ω
        simp only [X, Function.comp_apply, hermitianBrownian_eq_coords, commonWienerPast]
        rfl
      rw [this]
      refine Measurable.comp ?_ (comap_measurable _)
      exact measurable_matrix_add.comp (measurable_fst.prodMk (measurable_brownianOfCoords.comp
        (Measurable.of_eval fun q => (measurable_pi_apply _).comp
          ((measurable_pi_apply q).comp measurable_snd))))
    · -- `σ(Y) ≤ σ(future)`
      refine Measurable.comap_le ?_
      refine measurable_pi_of_eval' fun q => measurable_continuousPath_of_eval fun t => ?_
      have : (fun ω : FlowSample N => (Y ω q) t) =
          (fun g : ((Fin N × Fin N) × Fin 2) → ℝ≥0 → ℝ => g q t) ∘
            (fun x : FlowSample N => commonWienerFuture d x.2) := rfl
      rw [this]
      exact ((measurable_pi_apply t).comp (measurable_pi_apply q)).comp (comap_measurable _)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have e : restartMap (N := N) a' a = fun ω => (X ω, Y ω) := rfl
  rw [e, hprod, hlawX, hlawY]
  rfl

theorem measurePreserving_restartMap {a' a : ℝ} (ha' : 0 ≤ a') (ha : a' ≤ a) :
    MeasurePreserving (restartMap (N := N) a' a) (flowLaw N a') (flowLaw N a) :=
  ⟨measurable_restartMap a' a, map_restartMap ha' ha⟩

end BlockBand.Palm.MomentFlow
