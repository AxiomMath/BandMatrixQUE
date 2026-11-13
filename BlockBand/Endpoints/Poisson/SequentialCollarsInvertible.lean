module

public import BlockBand.Endpoints.Poisson.SequentialCollarsPhysical
public import BlockBand.Model.Construction.GaussianSimpleSpectrum

/-!
# Sequential collar removal: almost-sure invertibility of the real inverses

* `IsActivePoly`: complex polynomial in the active real Gaussian coordinates of `H`
  (`Parameters.gaussianActiveReconstruction`); closed under `+ - *`, `star`, `ite`, finite sums
  and products, and `det` of a matrix of active polynomials. `IsActivePoly.ae_ne_zero`: nonzero
  at one point ⇒ nonzero `model.law`-a.s. (`ae_activePolynomial_ne_zero`, i.e.
  `GaussianPolynomialNull`).
* Witness `scalarWitness p e = (e+1) I`: there `M_κ` is diagonal with entries `1 + i(...)` or
  `ξ + iη`, `η > 0`, and `G - e = I`.
* `ae_isUnit_det_oldInterior`, `ae_isUnit_det_collarMid` (under `ringCoordLaw`) and their
  versions; `stageMatrix_factorization_ae(_locked)`: item (iii) almost surely, with no
  invertibility side condition, for each fixed `κ ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix

section Poly

variable (p : Parameters)

/-- `f(H)` is a complex polynomial in the active real Gaussian coordinates of `H` on the range of
the active reconstruction. -/
def IsActivePoly (f : p.SiteMatrix → ℂ) : Prop :=
  ∃ P : MvPolynomial p.GaussianActiveCoordinate ℂ, ∀ z : p.GaussianActiveCoordinate → ℝ,
    f (p.gaussianActiveReconstruction z) = MvPolynomial.eval (fun i => (z i : ℂ)) P

variable {p}

/-- Constants. -/
theorem IsActivePoly.const (c : ℂ) : IsActivePoly p (fun _ => c) :=
  ⟨MvPolynomial.C c, fun z => by simp⟩

/-- Matrix entries (`gaussianUniversalMatrix`). -/
theorem IsActivePoly.entry (x y : p.Site) : IsActivePoly p (fun H => H x y) :=
  ⟨p.gaussianUniversalMatrix x y, fun z => by
    rw [← p.gaussianUniversalMatrix_map_eval z]; rfl⟩

theorem IsActivePoly.add {f g : p.SiteMatrix → ℂ} (hf : IsActivePoly p f) (hg : IsActivePoly p g) :
    IsActivePoly p (fun H => f H + g H) := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun z => by simp [hP, hQ]⟩

theorem IsActivePoly.mul {f g : p.SiteMatrix → ℂ} (hf : IsActivePoly p f) (hg : IsActivePoly p g) :
    IsActivePoly p (fun H => f H * g H) := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun z => by simp [hP, hQ]⟩

theorem IsActivePoly.sub {f g : p.SiteMatrix → ℂ} (hf : IsActivePoly p f) (hg : IsActivePoly p g) :
    IsActivePoly p (fun H => f H - g H) := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  exact ⟨P - Q, fun z => by simp [hP, hQ]⟩

theorem IsActivePoly.star {f : p.SiteMatrix → ℂ} (hf : IsActivePoly p f) :
    IsActivePoly p (fun H => Star.star (f H)) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨MvPolynomial.map (starRingEnd ℂ) P, fun z => ?_⟩
  show Star.star (f (p.gaussianActiveReconstruction z)) = _
  rw [hP, MvPolynomial.eval_map]
  have h := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (RingHom.id ℂ) (fun i => (z i : ℂ)) P
  have hg : (starRingEnd ℂ) ∘ (fun i => (z i : ℂ)) = fun i => (z i : ℂ) := by
    funext i; simp
  rw [RingHom.comp_id, hg] at h
  exact h

theorem IsActivePoly.sum {ι : Type*} (s : Finset ι) {f : ι → p.SiteMatrix → ℂ}
    (hf : ∀ i, IsActivePoly p (f i)) : IsActivePoly p (fun H => ∑ i ∈ s, f i H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsActivePoly.const (p := p) 0
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a).add ih

theorem IsActivePoly.prod {ι : Type*} (s : Finset ι) {f : ι → p.SiteMatrix → ℂ}
    (hf : ∀ i, IsActivePoly p (f i)) : IsActivePoly p (fun H => ∏ i ∈ s, f i H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsActivePoly.const (p := p) 1
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (hf a).mul ih

/-- Determinants of matrices of active polynomials. -/
theorem IsActivePoly.det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : p.SiteMatrix → Matrix ι ι ℂ} (hA : ∀ i j, IsActivePoly p (fun H => A H i j)) :
    IsActivePoly p (fun H => (A H).det) := by
  simp_rw [det_apply']
  exact IsActivePoly.sum _ fun σ => (IsActivePoly.const _).mul (IsActivePoly.prod _ fun i => hA _ _)

/-- An active polynomial function which is nonzero at one point of the reconstruction range is
nonzero almost surely under the law of every realization. -/
theorem IsActivePoly.ae_ne_zero {f : p.SiteMatrix → ℂ} (hf : IsActivePoly p f)
    (model : p.GaussianRingModel) {z₀ : p.GaussianActiveCoordinate → ℝ}
    (h₀ : f (p.gaussianActiveReconstruction z₀) ≠ 0) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), f H ≠ 0 := by
  obtain ⟨P, hP⟩ := hf
  rw [hP] at h₀
  filter_upwards [model.ae_activePolynomial_ne_zero P z₀ h₀,
    model.ae_gaussianActiveReconstruction_eq] with H hH hrec
  rw [← hrec, hP]
  exact hH

theorem IsActivePoly.ite {c : Prop} {inst : Decidable c} {f g : p.SiteMatrix → ℂ}
    (hf : IsActivePoly p f) (hg : IsActivePoly p g) :
    IsActivePoly p (fun H => @ite ℂ c inst (f H) (g H)) := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using hg

end Poly

section Witness

variable (p : Parameters)

/-- The real scalar witness `H₀ = (e+1) I`. -/
def scalarWitness (e : ℝ) : p.SiteMatrix := Matrix.diagonal fun _ => ((e + 1 : ℝ) : ℂ)

/-- The witness lies in the active reconstruction range. -/
theorem activeReconstruction_scalarWitness (e : ℝ) :
    p.gaussianActiveReconstruction (p.gaussianActiveExtraction (scalarWitness p e)) =
      scalarWitness p e := by
  classical
  have hcoord : p.gaussianActiveValue (p.gaussianActiveExtraction (scalarWitness p e)) =
      p.gaussianExtraction (scalarWitness p e) := by
    funext i
    unfold Parameters.gaussianActiveValue Parameters.gaussianActiveExtraction
    split_ifs with hi
    · rfl
    · cases i with
      | inl x => exact False.elim (hi (p.gaussianCoordinateVariance_diagonal_ne_zero x))
      | inr xy =>
          rcases xy with ⟨x, y, b⟩
          by_cases hxy : x = y
          · subst y
            simp [Parameters.gaussianExtraction]
          · simp [Parameters.gaussianExtraction, scalarWitness, Matrix.diagonal_apply_ne _ hxy]
  rw [Parameters.gaussianActiveReconstruction, hcoord]
  apply p.gaussianReconstruction_gaussianExtraction
  rw [scalarWitness, Matrix.isHermitian_diagonal_iff]
  intro x
  simp [IsSelfAdjoint, Complex.conj_ofReal]

end Witness

section Stage

variable (p : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)

/-- Every entry of the stage matrix built from `ringCoordsOf H` is an active polynomial in `H`. -/
theorem isActivePoly_stageFull (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (x y : p.Site) :
    IsActivePoly p (fun H => stageFull L s π S e z buf κ (ringCoordsOf H) x y) := by
  simp only [stageFull, stageHerm, ringCoordsOf, Matrix.add_apply, Matrix.of_apply,
    diagonal_apply]
  repeat' (first
    | exact IsActivePoly.const _
    | exact IsActivePoly.entry _ _
    | refine IsActivePoly.ite ?_ ?_
    | refine IsActivePoly.add ?_ ?_
    | refine IsActivePoly.sub ?_ ?_
    | refine IsActivePoly.star ?_)

open Classical in
/-- At the witness `(e+1) I` the stage matrix is diagonal with nonzero entries. -/
theorem stageFull_scalarWitness (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (x y : p.Site) :
    stageFull L s π S e z buf κ (ringCoordsOf (scalarWitness p e)) x y =
      if x = y then
        ((if IsMatched L s S x.1 then (z.re : ℂ) else 1) +
          ((stageAbsorption L s S buf κ z.im p.W x.1 : ℝ) : ℂ) * Complex.I) else 0 := by
  have h1 : (1 : ZMod p.n) ≠ 0 := zmod_one_ne_zero p
  obtain ⟨q, a⟩ := x
  obtain ⟨q', b⟩ := y
  by_cases hq : q = q'
  · subst hq
    by_cases hab : a = b
    · subst hab
      by_cases hm : IsMatched L s S q
      · simp [stageFull, stageHerm, ringCoordsOf, scalarWitness, diagonal_apply, hm, h1]
      · simp [stageFull, stageHerm, ringCoordsOf, scalarWitness, diagonal_apply, hm, h1]
    · simp [stageFull, stageHerm, ringCoordsOf, scalarWitness, diagonal_apply, hab, h1]
  · simp [stageFull, stageHerm, ringCoordsOf, scalarWitness, diagonal_apply, hq, h1]

open Classical in
/-- `det M_κ ≠ 0` at the witness. -/
theorem det_oldInterior_scalarWitness_ne_zero (π : Pairing) (S : Finset (Fin m)) (k : Fin m)
    (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ) (κ : ℝ) :
    (oldInterior L s π S k e z buf κ (ringCoordsOf (scalarWitness p e))).det ≠ 0 := by
  set g : OldSite L s S k p.W → ℂ := fun x =>
    (if IsMatched L s S x.1.1 then (z.re : ℂ) else 1) +
      ((stageAbsorption L s S buf κ z.im p.W x.1.1 : ℝ) : ℂ) * Complex.I
  have hdiag : oldInterior L s π S k e z buf κ (ringCoordsOf (scalarWitness p e)) = diagonal g := by
    ext x y
    simp only [oldInterior, submatrix_apply, stageFull_scalarWitness, diagonal_apply,
      Subtype.ext_iff, g]
  rw [hdiag, det_diagonal, Finset.prod_ne_zero_iff]
  intro x _
  simp only [g]
  by_cases hm : IsMatched L s S x.1.1
  · simp only [hm, ite_true, stageAbsorption]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  · simp only [hm, ite_false]
    intro h
    have := congrArg Complex.re h
    simp at this

/-- `M_κ⁻¹` exists almost surely under the law, for each fixed `κ` and real `e`
(any `z` with `Im z > 0`). -/
theorem ae_isUnit_det_oldInterior_locked (model : p.GaussianRingModel) (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m) (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ) (κ : ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      IsUnit (oldInterior L s π S k e z buf κ (ringCoordsOf H)).det := by
  have hpoly : IsActivePoly p
      (fun H => (oldInterior L s π S k e z buf κ (ringCoordsOf H)).det) :=
    IsActivePoly.det fun x y => isActivePoly_stageFull p L s π S e z buf κ x.1 y.1
  filter_upwards [hpoly.ae_ne_zero model (z₀ := p.gaussianActiveExtraction (scalarWitness p e))
    (by rw [activeReconstruction_scalarWitness]
        exact det_oldInterior_scalarWitness_ne_zero p L s π S k e hz buf κ)] with H hH
  exact isUnit_iff_ne_zero.mpr hH

/-- `(G-e)⁻¹` exists almost surely under the law, at every deterministic real `e`. -/
theorem ae_isUnit_det_collarMid_locked (model : p.GaussianRingModel) (k : Fin m) (e : ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      IsUnit (collarMidBlock e (freshCollar L s k (ringCoordsOf H))).det := by
  have hpoly : IsActivePoly p
      (fun H => (collarMidBlock e (freshCollar L s k (ringCoordsOf H))).det) := by
    refine IsActivePoly.det fun a b => ?_
    simp only [collarMidBlock, freshCollar, ringCoordsOf, Matrix.sub_apply, Matrix.of_apply,
      Matrix.smul_apply, one_apply, smul_eq_mul]
    exact (IsActivePoly.entry _ _).sub (IsActivePoly.const _)
  have h0 : (collarMidBlock e (freshCollar L s k (ringCoordsOf (scalarWitness p e)))).det ≠ 0 := by
    have : collarMidBlock e (freshCollar L s k (ringCoordsOf (scalarWitness p e))) = 1 := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [collarMidBlock, freshCollar, ringCoordsOf, scalarWitness]
      · simp [collarMidBlock, freshCollar, ringCoordsOf, scalarWitness, hab, one_apply]
    rw [this, det_one]; exact one_ne_zero
  filter_upwards [hpoly.ae_ne_zero model (z₀ := p.gaussianActiveExtraction (scalarWitness p e))
    (by rw [activeReconstruction_scalarWitness]; exact h0)] with H hH
  exact isUnit_iff_ne_zero.mpr hH

/-- `{x | det M x is a unit}` is measurable for measurable `M`. -/
theorem measurableSet_isUnit_det {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    {M : α → Matrix ι ι ℂ} (hM : Measurable M) : MeasurableSet {x | IsUnit (M x).det} := by
  have hd : Measurable fun x => (M x).det := (continuous_id.matrix_det).measurable.comp hM
  have : {x | IsUnit (M x).det} = (fun x => (M x).det) ⁻¹' {0}ᶜ := by
    ext x; simp [isUnit_iff_ne_zero]
  rw [this]
  exact hd (measurableSet_singleton 0).compl

/-- **First inverse.** Under the original prior `ringCoordLaw` (any admissible
`p`), for every pairing and stage, every fixed source strength `κ`, deterministic real energy
`e` and `Im z > 0`, the old interior `M_κ` is almost surely invertible. -/
theorem ae_isUnit_det_oldInterior (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (e : ℝ)
    {z : ℂ} (hz : 0 < z.im) (buf : ℕ) (κ : ℝ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      IsUnit (oldInterior L s π S k e z buf κ ω).det := by
  have hX := (hasLaw_ringCoordsOf p p.constructGaussianRingModel).1
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_isUnit_det
    (measurable_oldNetwork L s π S k e z buf κ).fst)]
  exact ae_isUnit_det_oldInterior_locked p L s _ π S k e hz buf κ

/-- **Second inverse.** `(G - e)⁻¹` exists almost surely at every deterministic
real `e`. -/
theorem ae_isUnit_det_collarMid (k : Fin m) (e : ℝ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      IsUnit (collarMidBlock e (freshCollar L s k ω)).det := by
  have hX := (hasLaw_ringCoordsOf p p.constructGaussianRingModel).1
  have hm : Measurable fun ω : RingCoords p.n p.W => collarMidBlock e (freshCollar L s k ω) :=
    Measurable.of_eval_matrix _ fun a b => by
      simp only [collarMidBlock, freshCollar, Matrix.sub_apply]
      exact ((Matrix.measurable_apply).comp ((measurable_pi_apply _).comp measurable_fst)).sub
        measurable_const
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_isUnit_det hm)]
  exact ae_isUnit_det_collarMid_locked p L s _ k e

/-- **Item (iii) without invertibility side conditions.** For every admissible `p`, collar
layout, pairing, stage `S`, selected `k ∉ S`, real energy `e`, `Im z > 0` and each fixed `κ ≥ 0`:
almost surely under the original prior,
`det H^before_κ / det H^after_κ = det(G-e)·det(K_c+iη)/(2iη)^{2W} · det(I - U r_κ)`. -/
theorem stageMatrix_factorization_ae (hL : IsCollarLayout p.n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      (stageMatrix L s π S e z buf κ ω).det / (stageMatrix L s π (insert k S) e z buf κ ω).det =
        collarPrefactor e z (freshCollar L s k ω) *
          (1 - collarU z.im (collarKc e z.re (freshCollar L s k ω)) *
            oldResponse z (oldSchur (oldInterior L s π S k e z buf κ ω)
              (oldCoupling L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)ᴴ)).det := by
  have hfac := ((sequentialCollars (W := p.W) (s := s) hL p.b buf e z hz).1 π S k hk).2.2.2
  filter_upwards [hfac, ae_isUnit_det_oldInterior p L s π S k e hz buf κ,
    ae_isUnit_det_collarMid p L s k e] with ω h hM hG
  exact h κ hκ hM hG

/-- The same, under the law `model.law` of any realization, at `ω = ringCoordsOf H`. -/
theorem stageMatrix_factorization_ae_locked (model : p.GaussianRingModel)
    (hL : IsCollarLayout p.n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) (π : Pairing)
    (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      (stageMatrix L s π S e z buf κ (ringCoordsOf H)).det /
          (stageMatrix L s π (insert k S) e z buf κ (ringCoordsOf H)).det =
        collarPrefactor e z (freshCollar L s k (ringCoordsOf H)) *
          (1 - collarU z.im (collarKc e z.re (freshCollar L s k (ringCoordsOf H))) *
            oldResponse z (oldSchur (oldInterior L s π S k e z buf κ (ringCoordsOf H))
              (oldCoupling L s π S k e z buf κ (ringCoordsOf H))
              (oldCoupling L s π S k e z buf κ (ringCoordsOf H))ᴴ)).det := by
  have hX := (hasLaw_ringCoordsOf p model).1
  have h := stageMatrix_factorization_ae p L s hL hk π e hz buf hκ
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

end Stage

end BlockBand.Endpoints
