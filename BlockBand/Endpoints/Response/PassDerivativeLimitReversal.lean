module

public import BlockBand.Endpoints.Response.PassDerivativeLimitPort

/-!
# Path reversal preserves the near-end-grown path law

The reversal `revPath n` reverses the order of the first `n` blocks and takes adjoints of the
internal bond matrices. Since the square Ginibre law is invariant under the adjoint, the reversal
maps `growthPathLaw W b` to itself (`growthPathLaw_map_revPath`), and integrals are invariant
(`integral_revPath`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

/-!
### Ginibre invariance under the adjoint
-/

/-- The coordinate map of the adjoint on the real Gaussian coordinates of a square Ginibre
matrix: `(x, y, 0) ↦ r(y, x, 0)`, `(x, y, 1) ↦ -r(y, x, 1)`. -/
def adjCoord (ι : Type*) (r : ι × ι × Fin 2 → ℝ) : ι × ι × Fin 2 → ℝ :=
  fun c => if c.2.2 = 0 then r (c.2.1, c.1, c.2.2) else -r (c.2.1, c.1, c.2.2)

/-- The swap `(x, y, j) ↦ (y, x, j)`. -/
def swapCoord (ι : Type*) : ι × ι × Fin 2 ≃ ι × ι × Fin 2 where
  toFun c := (c.2.1, c.1, c.2.2)
  invFun c := (c.2.1, c.1, c.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem ginibreMeasure_map_conjTranspose (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    (ginibreMeasure ι ι t).map (fun B : Matrix ι ι ℂ => Bᴴ) = ginibreMeasure ι ι t := by
  classical
  set g : ℝ → ℝ := fun _ => 0
  set P := Measure.pi fun _ : ι × ι × Fin 2 => gaussianReal 0 (t / 2)
  set Φ : (ι × ι × Fin 2 → ℝ) → Matrix ι ι ℂ :=
    fun r => Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I
  have hΦ : Measurable Φ := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
      ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul_const _)
  have hct : Measurable (fun B : Matrix ι ι ℂ => Bᴴ) :=
    (continuous_id.matrix_conjTranspose).measurable
  -- `ᴴ ∘ Φ = Φ ∘ adjCoord`
  have hcomp : (fun B : Matrix ι ι ℂ => Bᴴ) ∘ Φ = Φ ∘ adjCoord ι := by
    funext r
    ext x y
    simp only [Function.comp_apply, conjTranspose_apply, Φ, of_apply, adjCoord]
    simp
  -- `adjCoord` preserves the product Gaussian law
  set s : ι × ι × Fin 2 → ℝ → ℝ := fun c => if c.2.2 = 0 then id else fun u => -u
  have hs : ∀ c, Measurable (s c) := fun c => by
    simp only [s]; split_ifs
    · exact measurable_id
    · exact measurable_neg
  have hadj : adjCoord ι = (fun r c => s c (r c)) ∘ (MeasurableEquiv.piCongrLeft
      (fun _ : ι × ι × Fin 2 => ℝ) (swapCoord ι)) := by
    funext r c
    simp only [adjCoord, Function.comp_apply, s, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply]
    split_ifs <;> rfl
  have hF : Measurable (fun (r : ι × ι × Fin 2 → ℝ) c => s c (r c)) :=
    measurable_pi_iff.2 fun c => (hs c).comp (measurable_pi_apply c)
  have hP : P.map (adjCoord ι) = P := by
    rw [hadj, ← Measure.map_map hF (MeasurableEquiv.measurable _)]
    have h1 := (measurePreserving_piCongrLeft (fun _ : ι × ι × Fin 2 => gaussianReal 0 (t / 2))
      (swapCoord ι)).map_eq
    rw [h1, Measure.pi_map_pi (fun c => (hs c).aemeasurable)]
    congr 1
    funext c
    simp only [s]
    split_ifs
    · exact Measure.map_id
    · rw [gaussianReal_map_neg, neg_zero]
  have hadjm : Measurable (adjCoord ι) := by
    rw [hadj]
    exact hF.comp (MeasurableEquiv.measurable _)
  unfold ginibreMeasure
  change (P.map Φ).map _ = P.map Φ
  rw [Measure.map_map hct hΦ, hcomp, ← Measure.map_map hΦ hadjm, hP]

/-!
### The reversal as a product map
-/

theorem piCongrLeft_const_apply {X : Type*} (e : ℕ ≃ ℕ) (a : ℕ → X) (k : ℕ) :
    Equiv.piCongrLeft (fun _ => X) e a k = a (e.symm k) := by
  rw [Equiv.piCongrLeft_apply]
  exact eq_rec_constant _ _

theorem revIdx_involutive (n : ℕ) : Function.Involutive (revIdx n) := by
  intro k
  unfold revIdx
  by_cases hk : k < n
  · rw [ite_pos' hk, ite_pos' (by omega)]; omega
  · rw [ite_neg' hk, ite_neg' hk]

/-- `k ↦ n - k` on `[0, n]`, identity beyond. -/
def revBond (n k : ℕ) : ℕ := if k ≤ n then n - k else k

theorem revBond_involutive (n : ℕ) : Function.Involutive (revBond n) := by
  intro k
  unfold revBond
  by_cases hk : k ≤ n
  · rw [ite_pos' hk, ite_pos' (by omega)]; omega
  · rw [ite_neg' hk, ite_neg' hk]

/-- The adjoint on the internal bond coordinates of the reversed sample. -/
def bondAdj (n k : ℕ) {W : ℕ} (B : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  if 0 < k ∧ k < n then Bᴴ else B

theorem revPath_eq (n : ℕ) {W : ℕ} (ω : GrowthPath W) :
    revPath n ω = Prod.map
      (fun a : ℕ → Matrix (Fin W) (Fin W) ℂ =>
        Equiv.piCongrLeft (fun _ => Matrix (Fin W) (Fin W) ℂ)
          (revIdx_involutive n).toPerm a)
      (fun c : ℕ → Matrix (Fin W) (Fin W) ℂ => fun k => bondAdj n k
        (Equiv.piCongrLeft (fun _ => Matrix (Fin W) (Fin W) ℂ)
          (revBond_involutive n).toPerm c k)) ω := by
  simp only [revPath, Prod.map]
  congr 1
  · funext k
    rw [piCongrLeft_const_apply, Function.Involutive.toPerm_symm, Function.Involutive.coe_toPerm]
  · funext k
    simp only [bondAdj, piCongrLeft_const_apply, Function.Involutive.toPerm_symm,
      Function.Involutive.coe_toPerm]
    by_cases h0 : k = 0
    · subst h0; simp [revBond]
    · by_cases hk : k < n
      · simp [h0, hk, revBond, hk.le, Nat.pos_of_ne_zero h0]
      · by_cases hkn : k = n
        · subst hkn; simp [h0, revBond]
        · have : ¬ k ≤ n := by omega
          simp [h0, hk, hkn, revBond, this]

theorem growthPathLaw_map_revPath (W : ℕ) (b : ℝ) (n : ℕ) :
    (growthPathLaw W b).map (revPath n) = growthPathLaw W b := by
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have iA : IsProbabilityMeasure μA := passDeriv_isProbabilityMeasure_gue _ _
  have iB : IsProbabilityMeasure μB := passDeriv_isProbabilityMeasure_ginibre _ _ _
  set eA := (revIdx_involutive n).toPerm
  set eB := (revBond_involutive n).toPerm
  set f : (ℕ → Matrix (Fin W) (Fin W) ℂ) → (ℕ → Matrix (Fin W) (Fin W) ℂ) :=
    fun a => Equiv.piCongrLeft (fun _ => Matrix (Fin W) (Fin W) ℂ) eA a
  set gp : (ℕ → Matrix (Fin W) (Fin W) ℂ) → (ℕ → Matrix (Fin W) (Fin W) ℂ) :=
    fun c => Equiv.piCongrLeft (fun _ => Matrix (Fin W) (Fin W) ℂ) eB c
  set gh : (ℕ → Matrix (Fin W) (Fin W) ℂ) → (ℕ → Matrix (Fin W) (Fin W) ℂ) :=
    fun d k => bondAdj n k (d k)
  have hrev : revPath n = Prod.map f (gh ∘ gp) := by
    funext ω; rw [revPath_eq]; rfl
  have hfm : Measurable f := (MeasurableEquiv.piCongrLeft _ eA).measurable
  have hgpm : Measurable gp := (MeasurableEquiv.piCongrLeft _ eB).measurable
  have hbm : ∀ k, Measurable (fun B : Matrix (Fin W) (Fin W) ℂ => bondAdj n k B) := by
    intro k
    unfold bondAdj
    split_ifs
    · exact (continuous_id.matrix_conjTranspose).measurable
    · exact measurable_id
  have hghm : Measurable gh := measurable_pi_iff.2 fun k => (hbm k).comp (measurable_pi_apply k)
  have hA : (Measure.infinitePi fun _ : ℕ => μA).map f = Measure.infinitePi fun _ : ℕ => μA := by
    have := Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μA) eA
    simpa [MeasurableEquiv.coe_piCongrLeft] using this
  have hB1 : (Measure.infinitePi fun _ : ℕ => μB).map gp = Measure.infinitePi fun _ : ℕ => μB := by
    have := Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μB) eB
    simpa [MeasurableEquiv.coe_piCongrLeft] using this
  have hB2 : (Measure.infinitePi fun _ : ℕ => μB).map gh = Measure.infinitePi fun _ : ℕ => μB := by
    rw [Measure.infinitePi_map_pi _ (fun k => hbm k)]
    congr 1
    funext k
    unfold bondAdj
    split_ifs
    · exact ginibreMeasure_map_conjTranspose _ _
    · exact Measure.map_id
  have hB : (Measure.infinitePi fun _ : ℕ => μB).map (gh ∘ gp) =
      Measure.infinitePi fun _ : ℕ => μB := by
    rw [← Measure.map_map hghm hgpm, hB1, hB2]
  unfold growthPathLaw
  rw [hrev, ← Measure.map_prod_map _ _ hfm (hghm.comp hgpm), hA, hB]

theorem measurable_revPath (n W : ℕ) : Measurable (fun ω : GrowthPath W => revPath n ω) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.2 fun k => (measurable_pi_apply _).comp measurable_fst
  · refine measurable_pi_iff.2 fun k => ?_
    show Measurable fun ω : GrowthPath W => if k = 0 then ω.2 n else if k < n then (ω.2 (n - k))ᴴ
      else if k = n then ω.2 0 else ω.2 k
    split_ifs
    · exact (measurable_pi_apply _).comp measurable_snd
    · exact (continuous_id.matrix_conjTranspose).measurable.comp
        ((measurable_pi_apply _).comp measurable_snd)
    · exact (measurable_pi_apply _).comp measurable_snd
    · exact (measurable_pi_apply _).comp measurable_snd

/-- Integrals are invariant under the reversal. -/
theorem integral_revPath (W : ℕ) (b : ℝ) (n : ℕ) {f : GrowthPath W → ℝ} (hf : Measurable f) :
    ∫ ω, f (revPath n ω) ∂growthPathLaw W b = ∫ ω, f ω ∂growthPathLaw W b := by
  rw [← integral_map (measurable_revPath n W).aemeasurable hf.aestronglyMeasurable,
    growthPathLaw_map_revPath]

end BlockBand.Endpoints
