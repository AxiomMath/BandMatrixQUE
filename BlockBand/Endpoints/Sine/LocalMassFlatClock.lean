module

public import BlockBand.Endpoints.Sine.LocalMassFlatDefs
public import BlockBand.Endpoints.Response.PassDerivative

/-!
# The matched-lead clocks are the tagged clocks of the two-input path

The interior coordinates of the matched-lead response `Uh` are those of the two-input response
`𝒰_r h` (`lmf_leadResponse_mulVec_inl`). Hence the matched-lead tag clock is the tagged response
clock, `Z_{r;K} = W⁻¹h*Y_{r;r-1-K}h` (`lmf_tagClock_eq`), and the mean clock is
`M_r = (rW)⁻¹ h*Yh` with `Y = 𝒰_r*𝒰_r` (`lmf_meanClock_eq`). The file also proves joint
measurability in the energy, the path and the probe.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm

/-!
## Quadratic forms of Gram matrices
-/

/-- `Re(h*(A*DA)h) = Σ_x Re(d_x)‖(Ah)_x‖²` for a diagonal `D = diag(d)` with real entries. -/
theorem lmf_quadForm_conj_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ ι ℂ) (d : κ → ℝ) (h : ι → ℂ) :
    quadForm (Aᴴ * Matrix.diagonal (fun x => (d x : ℂ)) * A) h =
      ∑ x, d x * ‖(A *ᵥ h) x‖ ^ 2 := by
  unfold quadForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  set z := (A *ᵥ h) x
  rw [mul_comm (((d x : ℝ) : ℂ)), ← mul_assoc, mul_comm (star _),
    show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

/-- `Re(h*(A*A)h) = Σ_x ‖(Ah)_x‖²`. -/
theorem lmf_quadForm_conj_self {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ ι ℂ) (h : ι → ℂ) :
    quadForm (Aᴴ * A) h = ∑ x, ‖(A *ᵥ h) x‖ ^ 2 := by
  have h1 := lmf_quadForm_conj_diagonal A (fun _ => 1) h
  simp only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, one_mul] at h1
  exact h1

/-!
## The matched-lead response is the interior response
-/

/-- The interior coordinates of `Uh` are those of `𝒰_r h`. -/
theorem lmf_leadResponse_mulVec_inl (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (y : Fin r × Fin W) :
    (leadResponse b e W r ω *ᵥ h) (Sum.inl y) = (boundaryToInterior b e W r ω *ᵥ h) y := by
  rfl

/-- `‖P_KUh‖² = Σ_a ‖(𝒰_r h)_{(K,a)}‖²`. -/
theorem lmf_leadPositionMass_inl (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (K : Fin r) :
    leadPositionMass b e W r ω h (Sum.inl K) =
      ∑ a : Fin W, ‖(boundaryToInterior b e W r ω *ᵥ h) (K, a)‖ ^ 2 := by
  rfl

/-- `h*Y_{r;k}h = Σ_a ‖(𝒰_r h)_{(K,a)}‖²` at birth index `k = r - 1 - K`. -/
theorem lmf_quadForm_tagResponse (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (K : Fin r) :
    quadForm (tagResponse b e W r (r - 1 - K.val) ω) h =
      ∑ a : Fin W, ‖(boundaryToInterior b e W r ω *ᵥ h) (K, a)‖ ^ 2 := by
  classical
  have hP : tagProjection W r (r - 1 - K.val) =
      Matrix.diagonal (fun x : Fin r × Fin W => ((if x.1 = K then 1 else 0 : ℝ) : ℂ)) := by
    unfold tagProjection
    congr 1
    funext x
    have hK := K.isLt
    by_cases hx : x.1 = K
    · have h1 : r - 1 - K.val < r ∧ x.1.val = r - 1 - (r - 1 - K.val) := by
        rw [hx]; exact ⟨by omega, by omega⟩
      rw [ite_eq_left h1, ite_eq_left hx, Complex.ofReal_one]
    · have h1 : ¬ (r - 1 - K.val < r ∧ x.1.val = r - 1 - (r - 1 - K.val)) := by
        rintro ⟨-, h2⟩
        exact hx (Fin.ext (by omega))
      rw [ite_eq_right h1, ite_eq_right hx, Complex.ofReal_zero]
  unfold tagResponse
  rw [hP, lmf_quadForm_conj_diagonal]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single K]
  · simp
  · intro K' _ hK'
    simp [hK']
  · simp

/-- `Z_{r;K} = W⁻¹h*Y_{r;r-1-K}h`: the matched-lead tag clock is the tagged response clock. -/
theorem lmf_tagClock_eq (b e : ℝ) (W r : ℕ) (K : Fin r)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    lmf_tagClock b e W r K x = lmf_tagResponseClock b e W r (r - 1 - K.val) x := by
  unfold lmf_tagClock lmf_tagResponseClock
  rw [lmf_quadForm_tagResponse, lmf_leadPositionMass_inl]

/-- `h*Y^{int}h = h*Yh`, `Y = 𝒰_r*𝒰_r` the full two-input interior clock. -/
theorem lmf_interiorLeadMass_eq (b e : ℝ) (W r : ℕ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    lmf_interiorLeadMass b e W r x = quadForm (fullClock b e W r x.1) x.2 := by
  unfold lmf_interiorLeadMass fullClock
  rw [lmf_quadForm_conj_self, Fintype.sum_prod_type]
  rfl

/-- `M_r = (rW)⁻¹ h*Yh`. -/
theorem lmf_meanClock_eq (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    lmf_meanClock b e W r x = ((r : ℝ) * W)⁻¹ * quadForm (fullClock b e W r x.1) x.2 := by
  unfold lmf_meanClock
  rw [lmf_interiorLeadMass_eq]

/-- Along a clock sequence, `M_r` is the `rescaledClock` `M_W = h*Yh/(nW)`. -/
theorem lmf_meanClock_eq_rescaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (x : GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ)) :
    lmf_meanClock b (s.energy j) (s.W j) (s.n j) x = rescaledClock b s j x := by
  rw [lmf_meanClock_eq]
  unfold rescaledClock
  rw [div_eq_inv_mul]

theorem lmf_tagClock_nonneg (b e : ℝ) (W r : ℕ) (K : Fin r)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : 0 ≤ lmf_tagClock b e W r K x := by
  unfold lmf_tagClock leadPositionMass
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem lmf_meanClock_nonneg (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ lmf_meanClock b e W r x := by
  unfold lmf_meanClock lmf_interiorLeadMass leadPositionMass
  exact mul_nonneg (inv_nonneg.2 (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-!
## Measurability in the energy, the path and the probe
-/

theorem lmf_continuous_matchedA : Continuous matchedA := by
  have : matchedA = fun e : ℝ => ((-e / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - e ^ 2) / 2 : ℝ) : ℂ) *
      Complex.I := by
    funext e; rw [matchedA, Complex.mk_eq_add_mul_I]
  rw [this]; fun_prop

theorem lmf_measurable_boundaryZ (b : ℝ) : Measurable (fun e : ℝ => boundaryZ b e) := by
  unfold boundaryZ
  exact (lmf_continuous_matchedA.measurable.inv).add
    (measurable_const.mul lmf_continuous_matchedA.measurable)

theorem lmf_measurable_fullPathMatrix_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {E : α → ℝ} {Ω : α → GrowthPath W} (hE : Measurable E) (hΩ : Measurable Ω) :
    Measurable (fun a => fullPathMatrix b (E a) W r (Ω a)) := by
  have hP : Measurable (fun ω : PathSample W r => pathMatrix ω) := by
    unfold pathMatrix; fun_prop
  have hC : Measurable (fun ω : PathSample W r => pathPortCoupling ω) := by
    unfold pathPortCoupling; fun_prop
  have ha : Measurable (fun a => pathAt W r (Ω a)) := (measurable_pathAt W r).comp hΩ
  have hsub : Measurable (fun a =>
      pathMatrix (pathAt W r (Ω a)) -
        (E a : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    have h1 : Measurable (fun a => pathMatrix (pathAt W r (Ω a)) x y) :=
      (measurable_pi_apply y).comp ((measurable_pi_apply x).comp (hP.comp ha))
    have h2 : Measurable (fun a =>
        (E a : ℂ) * (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ) x y) :=
      (Complex.measurable_ofReal.comp hE).mul_const _
    exact h1.sub h2
  have hz : Measurable (fun a =>
      (boundaryZ b (E a) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact ((lmf_measurable_boundaryZ b).comp hE).mul_const _
  unfold fullPathMatrix
  exact measurable_fromBlocks hsub (hC.comp ha)
    ((continuous_id.matrix_conjTranspose).measurable.comp (hC.comp ha)) hz

/-- The entries of `𝒰_r h` are jointly measurable in `(e, ω, h)` (parametrized form). -/
theorem lmf_measurable_interiorResponse_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) (y : Fin r × Fin W) :
    Measurable (fun a => (boundaryToInterior b (e a) W r (x a).1 *ᵥ (x a).2) y) := by
  have hF : Measurable (fun a => fullInverse b (e a) W r (x a).1) :=
    passDeriv_measurable_inv.comp
      (lmf_measurable_fullPathMatrix_of b W r he (measurable_fst.comp hx))
  have hG : ∀ x' z, Measurable (fun a => fullInverse b (e a) W r (x a).1 x' z) := fun x' z =>
    measurable_pi_iff.1 (measurable_pi_iff.1 hF x') z
  have hh : ∀ z, Measurable (fun a => (x a).2 z) :=
    fun z => (measurable_pi_apply z).comp (measurable_snd.comp hx)
  simp only [mulVec, dotProduct, boundaryToInterior, Matrix.toBlocks₁₂]
  exact Finset.measurable_sum _ fun z _ => (hG (Sum.inl y) (Sum.inr z)).mul (hh z)

theorem lmf_measurable_tagClock_of (b : ℝ) (W r : ℕ) (K : Fin r) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)}
    (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => lmf_tagClock b (e a) W r K (x a)) := by
  unfold lmf_tagClock
  simp_rw [lmf_leadPositionMass_inl]
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ =>
    (continuous_norm.measurable.comp
      (lmf_measurable_interiorResponse_of b W r he hx (K, a))).pow_const 2)

theorem lmf_measurable_meanClock_of (b : ℝ) (W r : ℕ) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)}
    (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => lmf_meanClock b (e a) W r (x a)) := by
  unfold lmf_meanClock lmf_interiorLeadMass
  simp_rw [lmf_leadPositionMass_inl]
  exact measurable_const.mul (Finset.measurable_sum _ fun K _ =>
    Finset.measurable_sum _ fun a _ => (continuous_norm.measurable.comp
      (lmf_measurable_interiorResponse_of b W r he hx (K, a))).pow_const 2)

theorem lmf_measurable_tagResponseClock (b e : ℝ) (W r k : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      lmf_tagResponseClock b e W r k x) := by
  classical
  by_cases hk : k < r
  · have h := lmf_measurable_tagClock_of b W r ⟨r - 1 - k, by omega⟩
      (measurable_const (a := e)) measurable_id
    convert h using 1
    funext x
    rw [lmf_tagClock_eq]
    congr 1
    simp only
    omega
  · have : (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => lmf_tagResponseClock b e W r k x) =
        fun _ => 0 := by
      funext x
      unfold lmf_tagResponseClock tagResponse tagProjection
      have : (Matrix.diagonal fun x : Fin r × Fin W =>
          if k < r ∧ x.1.val = r - 1 - k then (1 : ℂ) else 0) = 0 := by
        ext y z
        simp [Matrix.diagonal_apply, hk]
      rw [this]
      simp [quadForm]
    rw [this]
    exact measurable_const

theorem lmf_measurable_quadForm_fullClock (b e : ℝ) (W r : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      quadForm (fullClock b e W r x.1) x.2) := by
  have h := lmf_measurable_interiorResponse_of b W r (measurable_const (a := e))
    (measurable_id (α := GrowthPath W × (Fin 2 × Fin W → ℂ)))
  have e' : (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      quadForm (fullClock b e W r x.1) x.2) =
      fun x => ∑ y, ‖(boundaryToInterior b e W r x.1 *ᵥ x.2) y‖ ^ 2 := by
    funext x
    unfold fullClock
    rw [lmf_quadForm_conj_self]
  rw [e']
  exact Finset.measurable_sum _ fun y _ => (continuous_norm.measurable.comp (h y)).pow_const 2

theorem lmf_measurable_scaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    Measurable (scaledClock b s j) :=
  (lmf_measurable_quadForm_fullClock b (s.energy j) (s.W j) (s.n j)).div_const _

theorem lmf_measurable_rescaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    Measurable (rescaledClock b s j) :=
  (lmf_measurable_quadForm_fullClock b (s.energy j) (s.W j) (s.n j)).div_const _

end BlockBand.Endpoints
