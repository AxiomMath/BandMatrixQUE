module

public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificate
public import BlockBand.Endpoints.Poisson.SequentialCollarsBridge

/-!
# The sequential-collars lemma under the physical law

We assemble items (i), (ii) and (iii) of the sequential-collars lemma under the law of every
realization of the physical ring (`sequentialCollars_full`).

* `ae_isUnit_det_after`: `det H^after_κ ≠ 0` almost surely (each fixed `κ ≥ 0`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathLaw pathSchur boundaryZ matchedDistance
  MatchedTracesContract bulkInterval)
open BlockBand.Internal.Contracts.Critical (conductance)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open scoped ENNReal

section Full

/-- Under the physical law `model.law`, the fresh collar has the collar law `Critical.collarLaw`. -/
theorem hasLaw_toCriticalCollar_locked (p : Parameters) (model : p.GaussianRingModel) {m : ℕ}
    {L : Fin m → ℕ} {s : ZMod p.n} (hL : IsCollarLayout p.n L) (k : Fin m) :
    HasLaw (toCriticalCollar ∘ freshCollar L s k ∘ ringCoordsOf)
      (BlockBand.Internal.Contracts.Critical.collarLaw p.W p.b)
      (model.law : Measure p.SiteMatrix) :=
  (hasLaw_toCriticalCollar hL k p.b).comp (hasLaw_ringCoordsOf p model).1

/-- `det H^after_κ ≠ 0` almost surely under the original prior, for each fixed `κ ≥ 0`, real `e`,
`Im z > 0`. -/
theorem ae_isUnit_det_after (p : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)
    (hL : IsCollarLayout p.n L) (π : Pairing) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      IsUnit (stageMatrix L s π (insert k S) e z buf κ ω).det := by
  filter_upwards [ringCoordLaw_ae_isHermitian (n := p.n) (W := p.W) p.b,
    ae_isUnit_det_oldInterior p L s π S k e hz buf κ] with ω hA hM
  have hIm := oldInterior_numRange (L := L) (s := s) π S k e z buf ω hA hκ hz.le
  exact (outerResolvent_eq hL hk π e z buf κ ω hM
    (isUnit_det_sub_oldSchur _ _ hM hIm hz)).2

theorem measurable_conductance_oldX0 (p : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)
    (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (b e : ℝ) (buf : ℕ) :
    Measurable fun ω : RingCoords p.n p.W =>
      conductance (oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω)) := by
  have hN := measurable_oldNetwork (W := p.W) L s π S k e (boundaryZ b e) buf 0
  have hM := hN.fst
  have hC := hN.snd
  have hX : Measurable fun ω : RingCoords p.n p.W => oldX0 L s π S k b e buf ω :=
    measurable_mat_mul (measurable_mat_mul (measurable_conjTranspose''.comp hC)
      (measurable_matrix_inv.comp hM)) hC
  have hR := measurable_matrix_inv.comp (measurable_mat_sub
    (measurable_const (a := boundaryZ b e • (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)))
    hX)
  have hr : Measurable fun ω : RingCoords p.n p.W =>
      oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω) := by
    unfold oldResponse
    refine measurable_mat_sub measurable_const (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.mul hR.eval_matrix
  unfold conductance
  have h1 := measurable_mat_sub
    (measurable_const (a := (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)))
    (measurable_mat_mul (measurable_conjTranspose''.comp hr) hr)
  refine Complex.measurable_re.comp ?_
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun i _ => h1.eval_matrix

/-- **The sequential-collars lemma, items (i), (ii) and (iii)**, under the law `model.law` of
every realization `model : p.GaussianRingModel` (the original prior; `ω = ringCoordsOf H` are its Gaussian block/bond coordinates), every collar
layout of its `p.n` blocks, either pairing and every stage `(S, k ∉ S)` of every deterministic
removal order.

  - **certificate**: for every threshold `δ > 0` (in particular `d_*/2` of
    the collar-kernel theorem), every `D` and total-length ratio `T`, eventually in `W` (uniformly in
    `p` with `n ≤ TW`, the layout, pairing, stage and energy)
    `P(d(X₀) > δ) ≤ W^{-D}`;
  - **defect moment**: for every `ε > 0` (complementary paths of `≥ εW` blocks; in the
    application `ε = 4R`)
    there is `C`, chosen before `T`, with `E g₀² ≤ C` for `W ≥ W₀(T)`, where
    `g₀ = Tr(I - r₀*r₀)` and `r₀ = Critical.oldScattering b e X₀`. -/
theorem sequentialCollars_full (hMT : MatchedTracesContract)
    (hTU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κI : ℝ}
    (hκI : 0 < κI) :
    -- items (i) and (iii)
    (∀ (p : Parameters) (model : p.GaussianRingModel) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)
        (hL : IsCollarLayout p.n L) (buf : ℕ) (e : ℝ) (z : ℂ), 0 < z.im →
      (HasLaw ringCoordsOf (ringCoordLaw p.n p.W p.b) (model.law : Measure p.SiteMatrix) ∧
      (∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ringMatrix (ringCoordsOf H) = H) ∧
      ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S →
        HasLaw (freshCollar L s k ∘ ringCoordsOf) (collarLaw p.W p.b)
          (model.law : Measure p.SiteMatrix) ∧
        IndepFun (freshCollar L s k ∘ ringCoordsOf) (oldCoords L s k ∘ ringCoordsOf)
          (model.law : Measure p.SiteMatrix) ∧
        (∀ κ : ℝ, IndepFun (freshCollar L s k ∘ ringCoordsOf)
          ((fun ω : RingCoords p.n p.W =>
            (oldInterior L s π S k e z buf κ ω, oldCoupling L s π S k e z buf κ ω)) ∘ ringCoordsOf)
          (model.law : Measure p.SiteMatrix)) ∧
        (∃ (pR : ZMod p.n) (rR : ℕ) (pL : ZMod p.n) (rL : ℕ),
          IsActualGaussianPath (W := p.W) L s π S k e z buf p.b pR rR ∧
          IsActualGaussianPath (W := p.W) L s π S k e z buf p.b pL rL ∧
          HasLaw (runSample pR rR ∘ ringCoordsOf) (pathLaw p.W rR p.b)
            (model.law : Measure p.SiteMatrix) ∧
          HasLaw (runSample pL rL ∘ ringCoordsOf) (pathLaw p.W rL p.b)
            (model.law : Measure p.SiteMatrix) ∧
          IndepFun (freshCollar L s k ∘ ringCoordsOf) (runSample pR rR ∘ ringCoordsOf)
            (model.law : Measure p.SiteMatrix) ∧
          IndepFun (freshCollar L s k ∘ ringCoordsOf) (runSample pL rL ∘ ringCoordsOf)
            (model.law : Measure p.SiteMatrix)) ∧
        (∀ κ : ℝ, 0 ≤ κ → ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
          (stageMatrix L s π S e z buf κ (ringCoordsOf H)).det /
              (stageMatrix L s π (insert k S) e z buf κ (ringCoordsOf H)).det =
            collarPrefactor e z (freshCollar L s k (ringCoordsOf H)) *
              (1 - collarU z.im (collarKc e z.re (freshCollar L s k (ringCoordsOf H))) *
                oldResponse z (oldSchur (oldInterior L s π S k e z buf κ (ringCoordsOf H))
                  (oldCoupling L s π S k e z buf κ (ringCoordsOf H))
                  (oldCoupling L s π S k e z buf κ (ringCoordsOf H))ᴴ)).det)) ∧
      (∀ (κ : ℝ) (ω : RingCoords p.n p.W),
        stageMatrix L s .box Finset.univ e z buf κ ω =
          (stageMatrix L s .cyclic Finset.univ e z buf κ ω).submatrix (finalSitePerm L s hL)
            (finalSitePerm L s hL))) ∧
    -- item (ii): the scalar certificate
    (∀ δ : ℝ, 0 < δ → ∀ (D : ℕ) (T : ℝ), ∃ W₀ : ℕ, ∀ p : Parameters, p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) {m : ℕ} (L : Fin m → ℕ)
        (s : ZMod p.n) (_hL : IsCollarLayout p.n L) (π : Pairing) (S : Finset (Fin m))
        (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ), e ∈ bulkInterval κI →
        (model.law : Measure p.SiteMatrix)
            {H | δ < matchedDistance b e (oldX0 L s π S k b e buf (ringCoordsOf H))} ≤
          ENNReal.ofReal ((p.W : ℝ) ^ (-(D : ℝ)))) ∧
    -- item (ii): the defect moment, uniformly in the total length
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ p : Parameters, p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) {m : ℕ} (L : Fin m → ℕ)
        (s : ZMod p.n) (_hL : IsCollarLayout p.n L), (∀ j, ε * p.W ≤ L j) →
        ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ),
        e ∈ bulkInterval κI →
        ∫⁻ H, ‖conductance (BlockBand.Internal.Contracts.Critical.oldScattering b e
            (oldX0 L s π S k b e buf (ringCoordsOf H)))‖ₑ ^ (2 : ℝ)
          ∂(model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal C) := by
  have hbridge : ∀ {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e : ℝ),
      BlockBand.Internal.Contracts.Critical.oldScattering b e X = oldResponse (boundaryZ b e) X :=
    fun {W} X e => ((collarKc_eq_collarReaction (W := W) b e (fun _ => 0, fun _ => 0)).2.2 X).symm
  refine ⟨fun p model m L s hL buf e z hz => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := sequentialCollars_locked p s model hL buf e z hz
    refine ⟨⟨h1, h2, fun π S k hk => ?_⟩, fun κ ω => final_models_agree hL e z buf κ ω⟩
    obtain ⟨a1, a2, a3, a4, -⟩ := h3 π S k hk
    exact ⟨a1, a2, a3, a4, fun κ hκ =>
      stageMatrix_factorization_ae_locked p L s model hL hk π e hz buf hκ⟩
  · intro δ hδ D T
    obtain ⟨W₀, hW₀⟩ := sequentialCollars_certificate hMT hb0 hb1 hκI hδ D T
    refine ⟨W₀, fun p hpb hW hn model m L s hL π S k hk buf e he => ?_⟩
    have hX := (hasLaw_ringCoordsOf p model).1
    refine (Measure.le_map_apply hX.aemeasurable
      {ω | δ < matchedDistance b e (oldX0 L s π S k b e buf ω)}).trans ?_
    rw [hX.map_eq]
    exact hW₀ p hpb hW hn L s hL π S k hk buf e he
  · intro ε hε
    obtain ⟨C, hC⟩ := sequentialCollars_conductance hTU hb0 hb1 hκI hε
    refine ⟨C, fun T => ?_⟩
    obtain ⟨W₀, hW₀⟩ := hC T
    refine ⟨W₀, fun p hpb hW hn model m L s hL hεL π S k hk buf e he => ?_⟩
    have hX := (hasLaw_ringCoordsOf p model).1
    simp_rw [hbridge]
    rw [hX.lintegral_comp (f := fun ω => ‖conductance (oldResponse (boundaryZ b e)
      (oldX0 L s π S k b e buf ω))‖ₑ ^ (2 : ℝ))
      ((measurable_conductance_oldX0 p L s π S k b e buf).enorm.pow_const _).aemeasurable]
    exact hW₀ p hpb hW hn L s hL hεL π S k hk buf e he

end Full

end BlockBand.Endpoints
