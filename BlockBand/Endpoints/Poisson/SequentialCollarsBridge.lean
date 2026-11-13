module

public import BlockBand.Endpoints.Poisson.SequentialCollarsPhysical

/-!
# Sequential collar removal: the law of the fresh collar

Under the original prior, the fresh collar, read through `toCriticalCollar`, has exactly the
collar law `BlockBand.Internal.Contracts.Critical.collarLaw W b` (`hasLaw_toCriticalCollar`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.SourceProcess (circularBrownianCoordinates commonCircularIncrementLaw)
open scoped NNReal

/-- `GUE` is invariant under relabelling the index set by an equivalence. -/
theorem gueMeasure_map_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (t : ℝ≥0) :
    (gueMeasure ι t).map (fun A => A.submatrix e e) = gueMeasure κ t := by
  set σ : (κ × κ) × Fin 2 ≃ (ι × ι) × Fin 2 := (e.prodCongr e).prodCongr (Equiv.refl _)
  have hT := (measurePreserving_piCongrLeft (fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0))
    σ).symm
  have hsub : Measurable fun A : Matrix ι ι ℂ => A.submatrix e e :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hcomm : (fun A : Matrix ι ι ℂ => A.submatrix e e) ∘
      (gueSample t ∘ circularBrownianCoordinates) =
      (gueSample t ∘ circularBrownianCoordinates) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : (ι × ι) × Fin 2 => ℝ) σ).symm := by
    have happ : ∀ (r : (ι × ι) × Fin 2 → ℝ) (i : (κ × κ) × Fin 2),
        (MeasurableEquiv.piCongrLeft (fun _ : (ι × ι) × Fin 2 => ℝ) σ).symm r i = r (σ i) :=
      fun r i => Equiv.piCongrLeft_symm_apply (fun _ => ℝ) σ r i
    funext r
    ext x y
    simp only [Function.comp_apply, submatrix_apply, gueSample, circularBrownianCoordinates,
      Matrix.of_apply, happ]
    rfl
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample t) measurable_circ,
    Measure.map_map hsub ((measurable_gueSample t).comp measurable_circ), hcomm,
    ← Measure.map_map ((measurable_gueSample t).comp measurable_circ) hT.measurable, hT.map_eq,
    Measure.map_map (measurable_gueSample t) measurable_circ]

/-- **Law of the fresh collar.** Under the original prior, the fresh collar written as a `Critical.CollarSample`
(`toCriticalCollar`) has the law `Critical.collarLaw W b` of the collar kernel theorem (`CollarKernelContract`). -/
theorem hasLaw_toCriticalCollar {m n W : ℕ} [NeZero n] {L : Fin m → ℕ} {s : ZMod n}
    (hL : IsCollarLayout n L) (k : Fin m) (b : ℝ) :
    HasLaw (toCriticalCollar ∘ freshCollar (W := W) L s k)
      (BlockBand.Internal.Contracts.Critical.collarLaw W b) (ringCoordLaw n W b) := by
  set P := ringCoordLaw n W b
  set X : Fin 3 ⊕ Fin 2 → RingCoords n W → Matrix (Fin W) (Fin W) ℂ :=
    fun j => ringCoord (collarIdx L s k j)
  obtain ⟨hI, hm⟩ := iIndepFun_ringCoord (n := n) (W := W) b
  have hX : iIndepFun X P := hI.precomp (collarIdx_injective hL k)
  have hXm : ∀ j, HasLaw (X j) (ringCoordMarginal W b (collarIdx L s k j)) P := fun j => hm _
  have hmeas : ∀ j, Measurable (X j) := fun j => measurable_ringCoord _
  -- the two end diagonals
  let j₀ : Fin 2 → Fin 3 ⊕ Fin 2 := fun i => Sum.inl (if i = 0 then 0 else 2)
  have hj₀ : Function.Injective j₀ := by
    intro i i' h
    fin_cases i <;> fin_cases i' <;> simp_all [j₀]
  set U : RingCoords n W → Fin 2 → Matrix (Fin W) (Fin W) ℂ := fun ω i => X (j₀ i) ω
  have hU : HasLaw U (Measure.pi fun _ : Fin 2 => gueBlockLaw W b) P :=
    (hX.precomp hj₀).hasLaw_pi fun i => hXm _
  -- the two bonds to the middle block, `(B_left, B_rightᴴ)` on the common port
  let g : Fin 2 → Matrix (Fin W) (Fin W) ℂ → Fin 1 → Matrix (Fin W) (Fin W) ℂ :=
    fun a M _ => if a = 0 then M else Mᴴ
  have hg : ∀ a, MeasurePreserving (g a) (ginBondLaw W b)
      (Measure.pi fun _ : Fin 1 => ginBondLaw W b) := by
    intro a
    have h1 := (measurePreserving_funUnique (ginBondLaw W b) (Fin 1)).symm
    have h2 : MeasurePreserving (fun M : Matrix (Fin W) (Fin W) ℂ => if a = 0 then M else Mᴴ)
        (ginBondLaw W b) (ginBondLaw W b) := by
      by_cases ha : a = 0
      · simp only [ha, ite_true]; exact MeasurePreserving.id _
      · simp only [ha, ite_false]
        exact ⟨measurable_conjTranspose', ginibre_map_conjTranspose W _⟩
    exact h1.comp h2
  set V : RingCoords n W → Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ :=
    fun ω a => g a (X (Sum.inr a) ω)
  have hV : HasLaw V (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 1 => ginBondLaw W b) P :=
    ((hX.precomp Sum.inr_injective).comp g fun a => (hg a).measurable).hasLaw_pi
      fun a => (hg a).comp_hasLaw (hXm _)
  -- the middle block on the port index
  set Y : RingCoords n W → Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
    fun ω => (X (Sum.inl 1) ω).submatrix Prod.snd Prod.snd
  have hY : HasLaw Y (gueMeasure (Fin 1 × Fin W) (Real.toNNReal ((1 - 2 * b) / W))) P := by
    have hmp : MeasurePreserving (fun A : Matrix (Fin W) (Fin W) ℂ => A.submatrix
        (Equiv.uniqueProd (Fin W) (Fin 1)) (Equiv.uniqueProd (Fin W) (Fin 1)))
        (gueBlockLaw W b) (gueMeasure (Fin 1 × Fin W) (Real.toNNReal ((1 - 2 * b) / W))) :=
      ⟨Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply,
        gueMeasure_map_submatrix _ _⟩
    exact hmp.comp_hasLaw (hXm (Sum.inl 1))
  -- independence of the three groups
  have hUV : IndepFun U V P := by
    have h := hX.indepFun_finset {Sum.inl 0, Sum.inl 2} {Sum.inr 0, Sum.inr 1} (by decide) hmeas
    have hF1 : Measurable fun t : ({Sum.inl 0, Sum.inl 2} : Finset (Fin 3 ⊕ Fin 2)) →
        Matrix (Fin W) (Fin W) ℂ => fun i : Fin 2 =>
          t ⟨j₀ i, by fin_cases i <;> simp [j₀]⟩ :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    have hF2 : Measurable fun t : ({Sum.inr 0, Sum.inr 1} : Finset (Fin 3 ⊕ Fin 2)) →
        Matrix (Fin W) (Fin W) ℂ => fun a : Fin 2 =>
          g a (t ⟨Sum.inr a, by fin_cases a <;> simp⟩) :=
      Measurable.of_eval fun a => (hg a).measurable.comp (measurable_pi_apply _)
    exact h.comp hF1 hF2
  have hUVY : IndepFun (fun ω => (U ω, V ω)) Y P := by
    have h := hX.indepFun_finset {Sum.inl 0, Sum.inl 2, Sum.inr 0, Sum.inr 1} {Sum.inl 1}
      (by decide) hmeas
    have hF1 : Measurable fun t : ({Sum.inl 0, Sum.inl 2, Sum.inr 0, Sum.inr 1} :
        Finset (Fin 3 ⊕ Fin 2)) → Matrix (Fin W) (Fin W) ℂ =>
          ((fun i : Fin 2 => t ⟨j₀ i, by fin_cases i <;> simp [j₀]⟩),
            (fun a : Fin 2 => g a (t ⟨Sum.inr a, by fin_cases a <;> simp⟩))) :=
      (Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
        (Measurable.of_eval fun a => (hg a).measurable.comp (measurable_pi_apply _))
    have hF2 : Measurable fun t : ({Sum.inl 1} : Finset (Fin 3 ⊕ Fin 2)) →
        Matrix (Fin W) (Fin W) ℂ => (t ⟨Sum.inl 1, by simp⟩).submatrix
          (Prod.snd : Fin 1 × Fin W → Fin W) Prod.snd :=
      Measurable.of_eval_matrix _ fun (x y : Fin 1 × Fin W) =>
        (Matrix.measurable_apply (m := Fin W) (n := Fin W) (α := ℂ) (i := x.2) (j := y.2)).comp
          (measurable_pi_apply _)
    exact h.comp hF1 hF2
  have hlaw := (indepFun_iff_hasLaw_prodMk_prod
    ((indepFun_iff_hasLaw_prodMk_prod hU hV).mp hUV) hY).mp hUVY
  have heq : toCriticalCollar ∘ freshCollar (W := W) L s k = fun ω => ((U ω, V ω), Y ω) := by
    funext ω
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · funext i; fin_cases i <;> rfl
    · funext a c; fin_cases a <;> rfl
  rw [heq]
  exact hlaw

end BlockBand.Endpoints
