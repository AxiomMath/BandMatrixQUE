module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Coarea.GUELaw
public import BlockBand.Coarea.ContractClauses
public import BlockBand.Palm.MomentFlow.LocalScaling

/-!
# The compressed pair `GUE` law

The compression `Uᴴ G U` of `G ~ GUE_{2W}(s/(2W))` by an isometry onto `2W - 1` columns has
the law `GUE_{2W-1}(s/(2W))`, the rescaled source GUE law.

*Measure.* `gueMeasure (PairSite p i) (pairTime p s) = GUE_{2W}(s/(2W))` and
`gueSourceLaw (2W - 1) = GUE_{2W-1}(1/(2W-1))` on `CEH.SourceHermitian (2W - 1)`. *Domain:* every
parameter set `p` (so `W ≥ 1` by `BlockBand.Parameters.W_pos`, hence `2W - 1 ≥ 1` with no truncation in the
natural subtraction), pair `i`, `s > 0`, and every isometry
`U : Matrix (PairSite p i) (Fin (2W - 1)) ℂ` (`Uᴴ U = 1`). Exact identity of measures at fixed
finite size; no norm, limit or uniformity statement.

## Main results

* `pi_map_comp_injective`: a product measure `∏_β ν` maps, under restriction `r ↦ r ∘ g` along an
  injective `g : α → β`, to `∏_α ν` (independence of the coordinates, `iIndepFun.precomp`).
* `gueMeasure_map_submatrix`: principal-block restriction, `(GUE_ι(t)).map (G ↦ G.submatrix f f) =
  GUE_κ(t)` for injective `f : κ → ι`.
* `gueMeasure_map_isometry_conj_of_equiv`: `(GUE_ι(t)).map (G ↦ Vᴴ G V) = GUE_κ(t)` for an isometry
  `V : Matrix ι κ ℂ` between index types of equal cardinality (from `gueMeasure_map_unitary_conj`
  and `gueMeasure_map_reindex`, `BlockBand.Coarea.GUELaw`).
* `exists_unit_mem_ker_conjTranspose`, `extendCol`, `extendCol_isometry`: an isometry with one
  fewer column than rows extends to a unitary `[U | v]`, `v` a unit vector in `ker Uᴴ`
  (rank–nullity).
* `gueMeasure_map_isometry_compress`: `(GUE_ι(t)).map (G ↦ Uᴴ G U) = GUE_κ(t)` whenever
  `|ι| = |κ| + 1` and `Uᴴ U = 1`.
* **`compressedGUELawBridge_holds : CompressedGUELawBridgeStatement`**, unconditional. Proof:
  compression gives `GUE_{2W-1}(s/(2W))`; `map_gueSourceLaw_smul` gives
  `(gueSourceLaw (2W-1)).map (√σ • ·.1) = GUE_{2W-1}(σ/(2W-1))` with `σ = s(1 - 1/(2W))`, and
  `σ/(2W-1) = s/(2W)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.LawBridge

open MeasureTheory Matrix BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs BlockBand.External

/-- **The compressed pair `GUE` law bridge**: for every parameter
set, pair, `s > 0` and isometry `U:
Fin (2W - 1) → PairSite` (`U* U = 1`), the compression
`U* G U` of `G ~ GUE_{2W}(s/2W)` has the law of `√(s(1 - 1/(2W))) W`, `W ~ gueSourceLaw (2W - 1)`.
-/
def CompressedGUELawBridgeStatement : Prop :=
  ∀ (p : Parameters) (i : ZMod p.n) (s : ℝ), 0 < s →
    ∀ U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ, Uᴴ * U = 1 →
      (gueMeasure (PairSite p i) (pairTime p s)).map (fun G => Uᴴ * G * U) =
        (gueSourceLaw (2 * p.W - 1)).map
          (fun W => (((Real.sqrt (s * (1 - 1 / (2 * (p.W : ℝ))))) : ℝ) : ℂ) • W.1)

open ProbabilityTheory BlockBand.SourceProcess BlockBand.Coarea.GUELaw
open scoped NNReal

/-!
## Gaussian restriction and compression lemmas
-/

section Compression

variable {ι κ : Type*}

/-- Restriction of an i.i.d. product measure along an injective map of index sets:
`(∏_β ν).map (r ↦ r ∘ g) = ∏_α ν` for injective `g : α → β` and a probability measure `ν`. -/
theorem pi_map_comp_injective {α β : Type*} [Fintype α] [Fintype β] {g : α → β}
    (hg : Function.Injective g) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : β => ν).map (fun r a => r (g a)) = Measure.pi fun _ : α => ν := by
  have h0 : iIndepFun (fun q (r : β → ℝ) => r q) (Measure.pi fun _ => ν) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h1 := h0.precomp hg
  rw [h1.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)]
  congr 1
  funext a
  exact (measurePreserving_eval (fun _ : β => ν) (g a)).map_eq

/-- The flat circular law restricts along an injective map `f : κ → ι` of matrix indices. -/
theorem commonCircularIncrementLaw_map_comp_injective [Fintype ι] [Fintype κ] {f : κ → ι}
    (hf : Function.Injective f) :
    (commonCircularIncrementLaw ι 1).map
        (fun X : ι × ι → ℂ => fun u : κ × κ => X (f u.1, f u.2)) =
      commonCircularIncrementLaw κ 1 := by
  set g : RealIndex κ → RealIndex ι := fun q => ((f q.1.1, f q.1.2), q.2) with hg_def
  have hg : Function.Injective g := by
    rintro ⟨⟨a, b⟩, j⟩ ⟨⟨a', b'⟩, j'⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [hf h1, hf h2, h3]
  have hX : Measurable (fun X : ι × ι → ℂ => fun u : κ × κ => X (f u.1, f u.2)) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hG : Measurable (fun r : RealIndex ι → ℝ => fun q => r (g q)) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hfun : (fun X : ι × ι → ℂ => fun u : κ × κ => X (f u.1, f u.2)) ∘
      circularBrownianCoordinates =
      circularBrownianCoordinates ∘ (fun r : RealIndex ι → ℝ => fun q => r (g q)) := by
    funext r u
    rfl
  unfold commonCircularIncrementLaw
  rw [Measure.map_map hX measurable_circularBrownianCoordinates, hfun,
    ← Measure.map_map measurable_circularBrownianCoordinates hG, pi_map_comp_injective hg]

/-- **Principal-block restriction of `GUE`**: for an
injective `f : κ → ι`, `(gueMeasure ι t).map (G ↦ G.submatrix f f) = gueMeasure κ t`. -/
theorem gueMeasure_map_submatrix [Fintype ι] [Fintype κ] {f : κ → ι}
    (hf : Function.Injective f) (t : ℝ≥0) :
    (gueMeasure ι t).map (fun G => G.submatrix f f) = gueMeasure κ t := by
  have hS : Measurable (fun G : Matrix ι ι ℂ => G.submatrix f f) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hX : Measurable (fun X : ι × ι → ℂ => fun u : κ × κ => X (f u.1, f u.2)) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hcomp : (fun G : Matrix ι ι ℂ => G.submatrix f f) ∘ gueSample t =
      gueSample t ∘ (fun X : ι × ι → ℂ => fun u : κ × κ => X (f u.1, f u.2)) := by
    funext X
    ext a b
    rfl
  unfold gueMeasure
  rw [Measure.map_map hS (measurable_gueSample t), hcomp,
    ← Measure.map_map (measurable_gueSample t) hX,
    commonCircularIncrementLaw_map_comp_injective hf]

/-- The compression map `G ↦ Vᴴ G V` is measurable. -/
theorem measurable_isometry_conj [Fintype ι] [Fintype κ] (V : Matrix ι κ ℂ) :
    Measurable (fun G : Matrix ι ι ℂ => Vᴴ * G * V) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable

/-- Unitary invariance of `GUE` for a square isometry between index types of equal
cardinality: `(gueMeasure ι t).map (G ↦ Vᴴ G V) = gueMeasure κ t` when `Vᴴ V = 1`. -/
theorem gueMeasure_map_isometry_conj_of_equiv [Fintype ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (t : ℝ≥0) {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) :
    (gueMeasure ι t).map (fun G => Vᴴ * G * V) = gueMeasure κ t := by
  classical
  set V' : Matrix ι ι ℂ := V.submatrix id e.symm with hV'_def
  have hV' : V' ∈ Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have h : star V' * V' = (Vᴴ * V).submatrix e.symm e.symm := by
      ext a b
      simp [V', Matrix.mul_apply, Matrix.star_apply, Matrix.conjTranspose_apply]
    rw [h, hV, Matrix.submatrix_one_equiv]
  have hW : star V' ∈ Matrix.unitaryGroup ι ℂ := Unitary.star_mem hV'
  have hR : Measurable (Matrix.reindex e.symm e.symm : Matrix ι ι ℂ → Matrix κ κ ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hC : Measurable (fun G : Matrix ι ι ℂ => star V' * G * star (star V')) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hcomp : (fun G : Matrix ι ι ℂ => Vᴴ * G * V) =
      (Matrix.reindex e.symm e.symm : Matrix ι ι ℂ → Matrix κ κ ℂ) ∘
        (fun G => star V' * G * star (star V')) := by
    funext G
    ext k l
    simp [V', Matrix.mul_apply, Matrix.star_apply, Matrix.conjTranspose_apply]
  rw [hcomp, ← Measure.map_map hR hC, gueMeasure_map_unitary_conj t hW, gueMeasure_map_reindex]

/-- `x* x = ∑ |x_a|²`. -/
theorem star_dotProduct_self_eq [Fintype ι] (x : ι → ℂ) :
    star x ⬝ᵥ x = (((∑ a, ‖x a‖ ^ 2 : ℝ)) : ℂ) := by
  simp [dotProduct, Complex.conj_mul']

/-- If `|κ| < |ι|`, then `ker Uᴴ` contains a unit vector (rank–nullity). -/
theorem exists_unit_mem_ker_conjTranspose [Fintype ι] [Fintype κ] (U : Matrix ι κ ℂ)
    (hcard : Fintype.card κ < Fintype.card ι) :
    ∃ v : ι → ℂ, Uᴴ *ᵥ v = 0 ∧ star v ⬝ᵥ v = 1 := by
  classical
  have hker : LinearMap.ker (Uᴴ.mulVecLin) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hcard)
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hw' : Uᴴ *ᵥ w = 0 := by simpa using hw
  obtain ⟨a₀, ha₀⟩ : ∃ a, w a ≠ 0 := Function.ne_iff.mp hw0
  set r : ℝ := ∑ a, ‖w a‖ ^ 2 with hr_def
  have hr : 0 < r :=
    Finset.sum_pos' (fun a _ => by positivity) ⟨a₀, Finset.mem_univ _, by positivity⟩
  set c : ℝ := (Real.sqrt r)⁻¹ with hc_def
  have hc : c ^ 2 * r = 1 := by
    rw [hc_def, inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne']
  refine ⟨(c : ℂ) • w, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hw', smul_zero]
  · rw [star_dotProduct_self_eq]
    have : ∑ a, ‖((c : ℂ) • w) a‖ ^ 2 = c ^ 2 * r := by
      rw [hr_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs,
        sq_abs]
    rw [this, hc, Complex.ofReal_one]

/-- The extension `[U | v] : Matrix ι (κ ⊕ Unit) ℂ` of `U` by one column `v`. -/
def extendCol [Fintype ι] (U : Matrix ι κ ℂ) (v : ι → ℂ) : Matrix ι (κ ⊕ Unit) ℂ :=
  Matrix.of fun a k => Sum.elim (fun l => U a l) (fun _ => v a) k

/-- If `Uᴴ U = 1`, `Uᴴ v = 0` and `v* v = 1`, then `[U | v]` is an isometry. -/
theorem extendCol_isometry [Fintype ι] [Fintype κ] [DecidableEq κ] {U : Matrix ι κ ℂ}
    (hU : Uᴴ * U = 1) {v : ι → ℂ} (hv : Uᴴ *ᵥ v = 0) (hvv : star v ⬝ᵥ v = 1) :
    (extendCol U v)ᴴ * extendCol U v = 1 := by
  have hU' : ∀ k l, ∑ a, star (U a k) * U a l = (1 : Matrix κ κ ℂ) k l := fun k l => by
    rw [← hU]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hv' : ∀ k, ∑ a, star (U a k) * v a = 0 := fun k => by
    have := congrFun hv k
    simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] using this
  have hv'' : ∀ k, ∑ a, star (v a) * U a k = 0 := fun k => by
    have := congrArg star (hv' k)
    simpa [star_sum, mul_comm] using this
  have hvv' : ∑ a, star (v a) * v a = 1 := by simpa [dotProduct] using hvv
  ext (k | k) (l | l)
  · simpa [extendCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hU' k l
  · simpa [extendCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hv' k
  · simpa [extendCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hv'' l
  · simpa [extendCol, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hvv'

/-- **Compression of `GUE` by an isometry of corank one**: if `|ι| = |κ| + 1` and `Uᴴ U = 1`, then
`(gueMeasure ι t).map (G ↦ Uᴴ G U) = gueMeasure κ t`. Proof: extend `U` to the unitary
`[U | v]`, use unitary invariance, and restrict to the principal `κ`-block. -/
theorem gueMeasure_map_isometry_compress [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hcard : Fintype.card ι = Fintype.card κ + 1) (t : ℝ≥0) {U : Matrix ι κ ℂ}
    (hU : Uᴴ * U = 1) :
    (gueMeasure ι t).map (fun G => Uᴴ * G * U) = gueMeasure κ t := by
  obtain ⟨v, hv, hvv⟩ := exists_unit_mem_ker_conjTranspose U (by omega)
  obtain ⟨e⟩ : Nonempty (κ ⊕ Unit ≃ ι) :=
    Fintype.card_eq.mp (by rw [Fintype.card_sum, Fintype.card_unit, hcard])
  have hS : Measurable (fun M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℂ => M.submatrix Sum.inl Sum.inl) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hcomp : (fun G : Matrix ι ι ℂ => Uᴴ * G * U) =
      (fun M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℂ => M.submatrix Sum.inl Sum.inl) ∘
        (fun G => (extendCol U v)ᴴ * G * extendCol U v) := by
    funext G
    ext k l
    simp [extendCol, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hcomp, ← Measure.map_map hS (measurable_isometry_conj _),
    gueMeasure_map_isometry_conj_of_equiv e t (extendCol_isometry hU hv hvv),
    gueMeasure_map_submatrix Sum.inl_injective]

end Compression

/-!
## The compressed law
-/

/-- **The compressed pair `GUE` law bridge** `CompressedGUELawBridgeStatement`, with no
hypothesis. -/
theorem compressedGUELawBridge_holds : CompressedGUELawBridgeStatement := by
  intro p i s hs U hU
  have hW := p.W_pos
  have hcard : Fintype.card (PairSite p i) = Fintype.card (Fin (2 * p.W - 1)) + 1 := by
    rw [BlockBand.Coarea.ContractClauses.card_pairSite, Fintype.card_fin]
    omega
  have hWr : (1 : ℝ) ≤ p.W := by exact_mod_cast hW
  have hσ : 0 ≤ s * (1 - 1 / (2 * (p.W : ℝ))) := by
    apply mul_nonneg hs.le
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  rw [gueMeasure_map_isometry_compress hcard _ hU,
    BlockBand.Palm.MomentFlow.map_gueSourceLaw_smul hσ]
  unfold pairTime
  congr 2
  have h1 : 1 ≤ 2 * p.W := by omega
  rw [Nat.cast_sub h1]
  push_cast
  have h2 : (2 * (p.W : ℝ) - 1) ≠ 0 := by linarith
  have h3 : (p.W : ℝ) ≠ 0 := by positivity
  field_simp

end BlockBand.Coarea.LawBridge
