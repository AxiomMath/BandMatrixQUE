module

public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateCases

/-!
# Item (ii): measurability, the law of the grown path, a.s. invertibility of the paths

Item (ii) of the sequential collars lemma.

* Measurability of the matrix inverse, `pathMatrix`, `pathSchur`, `matchedDistance` and
  `nearConductance`.
* `hasLaw_pathAt`: the near-end-grown path at length `r` has the law `pathLaw`;
  `pathConductance_eq`: the conductance `g_r` is `nearConductance` of its Schur matrix.
* `ae_isUnit_det_runPath`: `(H_path - e)⁻¹` exists almost surely for every run ("the inverse
  defining that reaction exists almost surely, by the Schur formulas for a finite path").
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathLaw pathMatrix pathPortCoupling pathSchur
  pathPortResolvent boundaryZ matchedA matchedDistance blockTrace ginibreMeasure)
open BlockBand.Internal.Contracts.TransmissionPath (GrowthPath growthPathLaw pathAt
  absorbedPathSchur layerAbsorption absorptionDiag pathNearSchur pathTransmission)
open BlockBand.Internal.Contracts.TransmissionStatements (pathConductance)
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure)

section Measurability

theorem measurable_mat_mul {α l m o : Type*} [MeasurableSpace α] [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => hf.eval_matrix.mul hg.eval_matrix

theorem measurable_mat_sub {α l m : Type*} [MeasurableSpace α]
    {f g : α → Matrix l m ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x - g x :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.sub_apply]
    exact hf.eval_matrix.sub hg.eval_matrix

theorem measurable_mat_add {α l m : Type*} [MeasurableSpace α]
    {f g : α → Matrix l m ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x + g x :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.add_apply]
    exact hf.eval_matrix.add hg.eval_matrix

theorem measurable_matrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  have hdet : Measurable (fun A : Matrix ι ι ℂ => A.det) := (continuous_id.matrix_det).measurable
  have hadj : Measurable (fun A : Matrix ι ι ℂ => A.adjugate) :=
    (continuous_id.matrix_adjugate).measurable
  have : (fun A : Matrix ι ι ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (hdet.inv).smul hadj

theorem measurable_pathMatrix {W r : ℕ} : Measurable (pathMatrix (W := W) (r := r)) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pathMatrix]
  split_ifs
  · exact (Matrix.measurable_apply).comp ((measurable_pi_apply _).comp measurable_fst)
  · exact (Matrix.measurable_apply).comp
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))
  · exact continuous_star.measurable.comp ((Matrix.measurable_apply).comp
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
  · exact measurable_const

theorem measurable_pathPortCoupling {W r : ℕ} :
    Measurable (pathPortCoupling (W := W) (r := r)) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pathPortCoupling]
  split_ifs
  · exact (Matrix.measurable_apply).comp
      ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))
  · exact measurable_const

theorem measurable_conjTranspose'' {α β : Type*} : Measurable (fun M : Matrix α β ℂ => Mᴴ) :=
  Measurable.of_eval_matrix _ fun x y =>
    continuous_star.measurable.comp (Matrix.measurable_apply (i := y) (j := x))

theorem measurable_pathSchur {W r : ℕ} (E : ℝ) :
    Measurable (pathSchur (W := W) (r := r) E) := by
  have h1 := measurable_mat_sub (measurable_pathMatrix (W := W) (r := r))
    (measurable_const (a := ((E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ))))
  have h2 := measurable_matrix_inv.comp h1
  have hC := measurable_pathPortCoupling (W := W) (r := r)
  exact measurable_mat_mul (measurable_mat_mul (measurable_conjTranspose''.comp hC) h2) hC

theorem measurable_matchedDistance (b e : ℝ) {W : ℕ} :
    Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => matchedDistance b e X) := by
  have hR : Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (boundaryZ b e • 1 - X)⁻¹ :=
    measurable_matrix_inv.comp (measurable_mat_sub measurable_const measurable_id)
  have hbt : ∀ j : Fin 2, Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      ‖blockTrace ((boundaryZ b e • 1 - X)⁻¹) j - matchedA e‖ := by
    intro j
    refine (Measurable.norm (Measurable.sub_const ?_ _))
    simp only [blockTrace]
    exact measurable_const.mul (Finset.measurable_sum _ fun a _ => hR.eval_matrix)
  exact (hbt 0).max (hbt 1)

theorem measurable_portBlock {W : ℕ} (i j : Fin 2) :
    Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      BlockBand.Internal.Contracts.TransmissionPath.portBlock X i j) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply

theorem measurable_nearConductance (b e : ℝ) {W : ℕ} :
    Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => nearConductance b e X) := by
  have hN : Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      BlockBand.Internal.Contracts.TransmissionPath.nearSchur (boundaryZ b e) X := by
    unfold BlockBand.Internal.Contracts.TransmissionPath.nearSchur
    exact measurable_mat_add (measurable_portBlock 0 0) (measurable_mat_mul (measurable_mat_mul
      (measurable_portBlock 0 1) (measurable_matrix_inv.comp
        (measurable_mat_sub measurable_const (measurable_portBlock 1 1))))
      (measurable_portBlock 1 0))
  unfold nearConductance BlockBand.Internal.Contracts.TransmissionPath.conductanceOf
    BlockBand.Internal.Contracts.TransmissionPath.passiveTransmission
    BlockBand.Internal.Contracts.TransmissionPath.passiveQ
    BlockBand.Internal.Contracts.TransmissionPath.passiveY
    BlockBand.Internal.Contracts.TransmissionPath.passiveResolvent
    BlockBand.Transmission.matrixImaginaryPart
  have hR := measurable_matrix_inv.comp (measurable_mat_sub
    (measurable_const (a := boundaryZ b e • (1 : Matrix (Fin W) (Fin W) ℂ))) hN)
  have hY : Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      -((-Complex.I / 2) •
        (BlockBand.Internal.Contracts.TransmissionPath.nearSchur (boundaryZ b e) X -
        (BlockBand.Internal.Contracts.TransmissionPath.nearSchur (boundaryZ b e) X)ᴴ)) :=
    Measurable.of_eval_matrix _ fun x y => by
      simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, conjTranspose_apply,
        smul_eq_mul]
      exact (measurable_const.mul (hN.eval_matrix.sub
        (continuous_star.measurable.comp hN.eval_matrix))).neg
  have hT := measurable_mat_mul (measurable_mat_mul (measurable_conjTranspose''.comp hR) hY) hR
  refine Complex.measurable_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul hT.eval_matrix

end Measurability

section GrowthLaw

/-- With zero absorption the absorbed Schur matrix is the unabsorbed one. -/
theorem absorbedPathSchur_zero {W r : ℕ} (E : ℝ) (ω : PathSample W r) :
    absorbedPathSchur E (layerAbsorption W (fun _ => 0) r) ω = pathSchur E ω := by
  have h : absorptionDiag (r := r) W (layerAbsorption W (fun _ => 0) r) = 0 := by
    ext x y; simp [absorptionDiag, layerAbsorption, diagonal_apply]
  simp [absorbedPathSchur, pathSchur, h]

/-- The conductance `g_r` of the grown path is the near conductance of its two-port Schur
matrix. -/
theorem pathConductance_eq (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    pathConductance b E W r ω = nearConductance b E (pathSchur E (pathAt W r ω)) := by
  simp [pathConductance, pathTransmission, pathNearSchur, absorbedPathSchur_zero, nearConductance]

/-- The `r`-marginal of the near-end-grown path is the path law `pathLaw`. -/
theorem hasLaw_pathAt (W r : ℕ) (b : ℝ) (hr : 1 ≤ r) :
    HasLaw (pathAt W r) (pathLaw W r b) (growthPathLaw W b) := by
  -- blocks
  set F₁ : (ℕ → Matrix (Fin W) (Fin W) ℂ) → Fin r → Matrix (Fin W) (Fin W) ℂ :=
    fun f i => f (r - 1 - i.val)
  have hinj₁ : Function.Injective (fun i : Fin r => r - 1 - i.val) := by
    intro i j h; apply Fin.ext; have := i.isLt; have := j.isLt; simp only at h; omega
  have hI₁ := (iIndepFun_infinitePi (P := fun _ : ℕ => gueBlockLaw W b)
    (X := fun _ => id) (fun _ => measurable_id)).precomp hinj₁
  have hF₁ : HasLaw F₁ (Measure.pi fun _ : Fin r => gueBlockLaw W b)
      (Measure.infinitePi fun _ : ℕ => gueBlockLaw W b) :=
    hI₁.hasLaw_pi fun i =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gueBlockLaw W b) (r - 1 - i.val)).hasLaw
  have hF₁m : Measurable F₁ := Measurable.of_eval fun i => measurable_pi_apply _
  -- bonds
  let ι : Fin (r - 1) ⊕ Fin 2 → ℕ
    | Sum.inl i => r - 1 - i.val
    | Sum.inr c => if c = 0 then r else 0
  have hinj₂ : Function.Injective ι := by
    rintro (i | c) (i' | c') h <;> simp only [ι] at h
    · apply congrArg Sum.inl; apply Fin.ext; have := i.isLt; have := i'.isLt; omega
    · exfalso; have := i.isLt; split_ifs at h <;> omega
    · exfalso; have := i'.isLt; split_ifs at h <;> omega
    · apply congrArg Sum.inr
      fin_cases c <;> fin_cases c' <;> (simp_all; try omega)
  have hI₂ := (iIndepFun_infinitePi (P := fun _ : ℕ => ginBondLaw W b)
    (X := fun _ => id) (fun _ => measurable_id)).precomp hinj₂
  have hv : HasLaw (fun (g : ℕ → Matrix (Fin W) (Fin W) ℂ) j => g (ι j))
      (Measure.pi fun _ : Fin (r - 1) ⊕ Fin 2 => ginBondLaw W b)
      (Measure.infinitePi fun _ : ℕ => ginBondLaw W b) :=
    hI₂.hasLaw_pi fun j =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => ginBondLaw W b) (ι j)).hasLaw
  have e1 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (r - 1) ⊕ Fin 2 => ginBondLaw W b)
  have e2 : MeasurePreserving (fun v : Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ => fun i => (v i)ᴴ)
      (Measure.pi fun _ : Fin (r - 1) => ginBondLaw W b)
      (Measure.pi fun _ : Fin (r - 1) => ginBondLaw W b) :=
    measurePreserving_pi _ _ fun _ => ⟨measurable_conjTranspose', ginibre_map_conjTranspose W _⟩
  have hF₂ := ((e2.prod (MeasurePreserving.id _)).comp e1).comp_hasLaw hv
  have hF₂m : Measurable (fun (g : ℕ → Matrix (Fin W) (Fin W) ℂ) j => g (ι j)) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  have hmp := (hF₁.measurePreserving hF₁m).prod
    (hF₂.measurePreserving (((e2.prod (MeasurePreserving.id _)).comp e1).measurable.comp hF₂m))
  have heq : pathAt W r = Prod.map F₁ ((Prod.map (fun v : Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ =>
      fun i => (v i)ᴴ) id ∘ MeasurableEquiv.sumPiEquivProdPi _) ∘
        fun (g : ℕ → Matrix (Fin W) (Fin W) ℂ) j => g (ι j)) := by
    funext ω
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      rfl
    · funext c
      fin_cases c <;> rfl
  rw [heq]
  exact hmp.hasLaw

end GrowthLaw

section RunInvertible

variable (p : Parameters)

theorem IsActivePoly.dite {c : Prop} {inst : Decidable c} {f : c → p.SiteMatrix → ℂ}
    {g : ¬ c → p.SiteMatrix → ℂ} (hf : ∀ h, IsActivePoly p (f h)) (hg : ∀ h, IsActivePoly p (g h)) :
    IsActivePoly p (fun H => @dite ℂ c inst (fun h => f h H) (fun h => g h H)) := by
  by_cases h : c
  · simpa [h] using hf h
  · simpa [h] using hg h

/-- The path matrix of a run is almost surely invertible at every real `e` (the
`(H_path - e)⁻¹` of the Schur formulas for a finite path). -/
theorem ae_isUnit_det_runPath (p₀ : ZMod p.n) (r : ℕ) (e : ℝ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      IsUnit (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1).det := by
  have hX := (hasLaw_ringCoordsOf p p.constructGaussianRingModel).1
  have hm : Measurable fun ω : RingCoords p.n p.W => pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1 :=
    measurable_mat_sub (measurable_pathMatrix.comp (measurable_runSample p₀ r)) measurable_const
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_isUnit_det hm)]
  have hpoly : IsActivePoly p
      (fun H => (pathMatrix (runSample p₀ r (ringCoordsOf H)) - (e : ℂ) • 1).det) := by
    refine IsActivePoly.det fun x y => ?_
    simp only [pathMatrix, runSample, ringCoordsOf, Matrix.of_apply, Matrix.sub_apply,
      Matrix.smul_apply, one_apply, smul_eq_mul]
    repeat' (first
      | exact IsActivePoly.const _
      | exact IsActivePoly.entry _ _
      | refine IsActivePoly.ite ?_ ?_
      | refine IsActivePoly.dite (fun _ => ?_) (fun _ => ?_)
      | refine IsActivePoly.add ?_ ?_
      | refine IsActivePoly.sub ?_ ?_
      | refine IsActivePoly.mul ?_ ?_
      | refine IsActivePoly.star ?_)
  have hne : ∀ q : ZMod p.n, q ≠ q + 1 := fun q h => succ_ne_self p q h.symm
  have h0 : (pathMatrix (runSample p₀ r (ringCoordsOf (scalarWitness p e))) - (e : ℂ) • 1).det ≠
      0 := by
    have : pathMatrix (runSample p₀ r (ringCoordsOf (scalarWitness p e))) - (e : ℂ) • 1 = 1 := by
      ext ⟨i, a⟩ ⟨j, c⟩
      by_cases hij : i = j
      · subst hij
        by_cases hac : a = c
        · subst hac; simp [pathMatrix, runSample, ringCoordsOf, scalarWitness, one_apply]
        · simp [pathMatrix, runSample, ringCoordsOf, scalarWitness, one_apply, hac]
      · have hne' : ∀ q : ZMod p.n, ∀ a c : Fin p.W, (q, a) ≠ (q + 1, c) :=
          fun q a c h => hne q (congrArg Prod.fst h)
        simp [pathMatrix, runSample, ringCoordsOf, scalarWitness, one_apply, hij, diagonal_apply,
          hne']
    rw [this, det_one]; exact one_ne_zero
  filter_upwards [hpoly.ae_ne_zero p.constructGaussianRingModel
    (z₀ := p.gaussianActiveExtraction (scalarWitness p e))
    (by rw [activeReconstruction_scalarWitness]; exact h0)] with H hH
  exact isUnit_iff_ne_zero.mpr hH

end RunInvertible

end BlockBand.Endpoints
