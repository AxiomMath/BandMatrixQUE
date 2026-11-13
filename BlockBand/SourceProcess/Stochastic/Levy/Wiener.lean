module
public import BlockBand.SourceProcess.Stochastic.Levy.Product
public import BlockBand.SourceProcess.CommonMatrixBrownian
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Wiener extension of a filtered probability space

The canonical Wiener factor is `(C(ℝ≥0, ℝ))^m` with the constructed product Wiener law
`commonWienerLaw (Fin m)` (no Brownian input is assumed) and its natural filtration
`wienerFiltration m t = σ(B'_r, r ≤ t)`
(`comap (commonWienerPast t)`), with coordinate process `wienerB m t ω i = ω i t`.

* `isFiltrationBrownian_wienerB`: `wienerB m` is an `m`-dimensional Brownian motion for its
  natural filtration (from the weak Markov property `commonWienerFuture_independent_past`).
* `extMeasure`, `extFiltration`, `extB`: for any `(Ω, 𝓖, Q)`, the product `Ω × (C(ℝ≥0,ℝ))^m` with
  `Q ⊗ Wiener` and the filtration `𝓖_t ⊗ σ(B'_r, r ≤ t)`; `isFiltrationBrownian_extension`:
  `B'` is a Brownian motion for the product filtration, `indepFun_extension`: the Wiener paths
  are independent of the first factor (hence of `𝓖_∞`). Martingales, martingale modifications,
  `IsL2Integrator` and `IsL2IntegratorVec` lift by `martingale_lift_fst`,
  `hasMartingaleModification_lift_fst`, `IsL2Integrator.lift_fst`, `IsL2IntegratorVec.lift_fst`.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess
open scoped NNReal ENNReal

universe u

/-- The Wiener path space `C(ℝ≥0, ℝ)^m`. -/
abbrev WienerSpace (m : ℕ) : Type := Fin m → CanonicalWienerPath

/-- The coordinate Brownian motion `B'_t(ω) = (ω_i(t))_i`. -/
def wienerB (m : ℕ) (t : ℝ≥0) (ω : WienerSpace m) : Fin m → ℝ := fun i => ω i t

/-- The natural filtration `σ(B'_r, r ≤ t)`. -/
def wienerFiltration (m : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (WienerSpace m)) where
  seq t := MeasurableSpace.comap (commonWienerPast (κ := Fin m) t) inferInstance
  mono' := by
    intro s t hst
    let restrict : (Fin m → Set.Iic t → ℝ) → (Fin m → Set.Iic s → ℝ) :=
      fun z a v => z a ⟨v.1, v.2.trans hst⟩
    have hr : Measurable restrict := Measurable.of_eval fun a => Measurable.of_eval fun v =>
      (measurable_pi_apply (⟨v.1, v.2.trans hst⟩ : Set.Iic t)).comp (measurable_pi_apply a)
    exact (hr.comp (comap_measurable (commonWienerPast (κ := Fin m) t))).comap_le
  le' t := (measurable_commonWienerPast (κ := Fin m) t).comap_le

theorem measurable_wienerB_adapted (m : ℕ) (t : ℝ≥0) :
    Measurable[wienerFiltration m t] (wienerB m t) := by
  have hev : Measurable (fun z : Fin m → Set.Iic t → ℝ => fun a => z a ⟨t, le_rfl⟩) :=
    Measurable.of_eval fun a => (measurable_pi_apply (⟨t, le_rfl⟩ : Set.Iic t)).comp
      (measurable_pi_apply a)
  exact hev.comp (comap_measurable _)

theorem measurable_wienerB (m : ℕ) (t : ℝ≥0) : Measurable (wienerB m t) :=
  (measurable_wienerB_adapted m t).mono ((wienerFiltration m).le t) le_rfl

theorem nndist_coe_eq_sub {s t : ℝ≥0} (hst : s ≤ t) : nndist (t : ℝ) (s : ℝ) = t - s :=
  NNReal.eq (by rw [coe_nndist, Real.dist_eq, NNReal.coe_sub hst,
    abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))])

/-- **The coordinate process is a Brownian motion for its natural filtration.** -/
theorem isFiltrationBrownian_wienerB (m : ℕ) :
    IsFiltrationBrownian (commonWienerLaw (Fin m)) (wienerFiltration m) (wienerB m) := by
  refine ⟨fun t => (measurable_wienerB_adapted m t).stronglyMeasurable,
    ae_of_all _ fun ω => continuous_pi fun i => (ω i).continuous, ?_, fun s t hst => ?_,
    fun s t hst => ?_⟩
  · have h := fun i : Fin m => (measurePreserving_eval (fun _ : Fin m => canonicalWienerLaw)
      i).quasiMeasurePreserving.ae canonicalWiener_isBrownian.eval_zero_ae_eq_zero
    filter_upwards [ae_all_iff.2 h] with ω hω
    funext i; exact hω i
  · have hind := (IndepFun_iff_Indep _ _ _).1 (commonWienerFuture_independent_past (κ := Fin m) s)
    refine indep_of_indep_of_le_left hind ?_
    have e : (fun ω => wienerB m t ω - wienerB m s ω) =
        (fun z : Fin m → ℝ≥0 → ℝ => fun a => z a (t - s)) ∘ commonWienerFuture s := by
      funext ω a
      simp [wienerB, commonWienerFuture, add_tsub_cancel_of_le hst]
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_eval fun a =>
      (measurable_pi_apply (t - s)).comp (measurable_pi_apply a)).comap_le
  · have hlaw : HasLaw (fun ω : CanonicalWienerPath => ω t - ω s) (gaussianReal 0 (t - s))
        canonicalWienerLaw := by
      have := canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw_sub t s
      convert this using 2
      exact (nndist_coe_eq_sub hst).symm
    refine ⟨((measurable_wienerB m t).sub (measurable_wienerB m s)).aemeasurable, ?_⟩
    have e : (fun ω => wienerB m t ω - wienerB m s ω) =
        fun (x : WienerSpace m) (i : Fin m) => (fun ω : CanonicalWienerPath => ω t - ω s) (x i) := by
      funext ω i; simp [wienerB]
    rw [e, commonWienerLaw, Measure.pi_map_pi (fun _ => hlaw.aemeasurable), gaussPi]
    congr 1; funext i; exact hlaw.map_eq

/-!
### The extension
-/

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The extension filtration `𝓖_t ⊗ σ(B'_r, r ≤ t)` on `Ω × C(ℝ≥0,ℝ)^m`. -/
abbrev extFiltration (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (m : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × WienerSpace m)) :=
  prodFiltration 𝓖 (wienerFiltration m)

/-- The extension measure `Q ⊗ Wiener^m`. -/
abbrev extMeasure (Q : Measure Ω) (m : ℕ) : Measure (Ω × WienerSpace m) :=
  Q.prod (commonWienerLaw (Fin m))

/-- The extension Brownian motion `B'_t(ω, w) = w(t)`. -/
abbrev extB (m : ℕ) (t : ℝ≥0) (x : Ω × WienerSpace m) : Fin m → ℝ := wienerB m t x.2

variable {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **`B'` is a Brownian motion for the extension filtration.** -/
theorem isFiltrationBrownian_extension (m : ℕ) :
    IsFiltrationBrownian (extMeasure Q m) (extFiltration 𝓖 m) (extB m) :=
  isFiltrationBrownian_lift_snd (isFiltrationBrownian_wienerB m)

/-- **The Wiener factor is independent of the first factor** (so `B'` is independent of
`𝓖_∞` and of every random variable of the original space). -/
theorem indepFun_extension (m : ℕ) :
    IndepFun (Prod.fst : Ω × WienerSpace m → Ω) Prod.snd (extMeasure Q m) :=
  indepFun_fst_snd

omit [MeasurableSpace Ω] in
/-- Every path of `B'` is continuous. -/
theorem continuous_extB (m : ℕ) (x : Ω × WienerSpace m) : Continuous fun t => extB m t x :=
  continuous_pi fun i => (x.2 i).continuous

end BlockBand.SourceProcess.Stochastic.Levy
