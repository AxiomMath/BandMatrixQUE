module

public import BlockBand.Palm.ReferenceFlowBackwardGen
public import BlockBand.Palm.ReferenceFlowAssembly
public import BlockBand.Critical.RelativeVectors.AngularFields
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Phase covariance by Haar symmetrization

The reference flow is symmetrized by an independent Haar phase: `𝓜 = P_θ⁻¹ K P_θ`,
`Ξ = P_θ⁻¹ L G`, `θ` uniform on the torus `(ℝ/2πℤ)^N`, independent of `(K, L, G)`, with
`P_θ = diag(e^{iθ'_k})` (`θ'` the representative in `[0, 2π)^N`). Conventions:
`labelPhaseMatrix α M = P_α⁻¹ M P_α`, `labelPhase α z = (e^{iα_k} z_k)_k`.

1. **Torus.** `torusHaar N` (product of `haarAddCircle` on `AddCircle (2π)`) is a probability
   measure; `torusShift α` (`θ ↦ θ + α`, `α : Fin N → ℝ`) preserves it
   (`measurePreserving_torusShift`); `torusRep` and `torusPhase` are measurable.
2. **Phase covariance** (`phase_covariant_sym`): on `(Ω₀ × Torus N, P₀ ⊗ Haar)`, with
   `symKernel K (ω₀, θ) = labelPhaseMatrix θ' (K ω₀)` and
   `symNoise Λ (ω₀, θ) = labelPhase (-θ') (Λ ω₀)`, the law of
   `(labelPhaseMatrix α 𝓜, labelPhase (-α) Ξ)` is the law of `(𝓜, Ξ)` for every `α` (the shape of
   `IsReferenceFlow.phase_covariant`). Composition: `labelPhaseMatrix_labelPhaseMatrix`.
3. **Generator equivariance** (`refGenerator_comp_labelPhase`):
   `refGenerator ρ κ s (h ∘ labelPhase θ) z = refGenerator ρ κ s h (labelPhase θ z)` for every
   `h` (no smoothness: `labelPhase θ` is a linear isomorphism), every `θ` and all coefficients.
   `P_θ X_ij P_θ⁻¹ = cos φ X_ij + sin φ Y_ij` (`labelPhase_lmul_rotX`, `φ = θ_j - θ_i`), and the
   rotation invariance of `Q(a, a) + Q(b, b)` (`bilin_rot`) handles the pair and the
   Ornstein–Uhlenbeck parts.
4. **Symmetrized backward equation.** `symBackward μ K L f s z =
   ∫ θ, refSemigroup μ K L (f ∘ labelPhase (-θ')) s (labelPhase θ' z) dHaar`;
   `symBackward_eq_integral`: it equals `E f(𝓜 z + Ξ)` on `(driverLaw μ ⊗ matCircularLaw) ⊗ Haar`;
   `symBackward_static`: `C²` with `D`, `D²` the `θ`-averages; `hasDerivAt_symBackward`:
   `∂_s symBackward s z = -refGenerator ρ κ s (symBackward s) z` on `(a, c)`.

The backward equation 4 uses two hypotheses beyond `IsReferenceFlow`: `IsProbabilityMeasure μ`
(for the integral bounds), and coefficients bounded on `[a, c]`
(`∃ B, ∀ s ∈ Icc a c, ‖ρ s‖ ≤ B ∧ ‖κ s‖ ≤ B`; `hasDerivAt_symBackward_of_continuousOn` derives it
from continuity, which holds for `shortRate`/`refDamping` on simple-spectrum paths).
The bound is the domination needed to differentiate `∫ θ` in `s`: the `backward` field gives
each `θ`-integrand's `s`-derivative pointwise, with size `|ρ s| + |κ s|` times derivative
bounds, and `IsReferenceFlow` itself does not bound `ρ`, `κ`. The bound on the kernel entries is
derived from `covariance` (`ae_kernel_entry_le`), not assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
open MeasureTheory Set Filter Topology Real
open BlockBand.Palm.ReferenceFlow BlockBand.Palm.ReferenceFlow.Backward
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {N p : ℕ}

/-- `0 < 2π`. -/
local instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The circle `ℝ/2πℤ`. -/
abbrev Circ := AddCircle (2 * π)
/-- The phase torus `(ℝ/2πℤ)^N`. -/
abbrev Torus (N : ℕ) := Fin N → Circ

/-- Normalized Haar measure on the torus: the product of the normalized Haar measures
`haarAddCircle` of the circles. -/
def torusHaar (N : ℕ) : Measure (Torus N) := Measure.pi fun _ => AddCircle.haarAddCircle

/-- **Item 1.** The Haar measure on the torus is a probability measure. -/
instance isProbabilityMeasure_torusHaar : IsProbabilityMeasure (torusHaar N) := by
  unfold torusHaar; infer_instance

/-- The real representative in `[0, 2π)` of a point of the circle. -/
def angleRep (x : Circ) : ℝ := (AddCircle.equivIco (2 * π) 0 x : ℝ)

/-- The real representative `θ' ∈ [0, 2π)^N` of a torus point `θ`. -/
def torusRep (θ : Torus N) : Fin N → ℝ := fun i => angleRep (θ i)

/-- The shift `θ ↦ θ + α` of the torus by a real vector `α` (reduced mod `2π`). -/
def torusShift (α : Fin N → ℝ) (θ : Torus N) : Torus N := θ + fun i => (α i : Circ)

/-- **Item 1.** The shift `θ ↦ θ + α` preserves the Haar measure, for every `α : Fin N → ℝ`. -/
theorem measurePreserving_torusShift (α : Fin N → ℝ) :
    MeasurePreserving (torusShift α) (torusHaar N) (torusHaar N) := by
  have h := measurePreserving_add_left
    (Measure.pi fun _ : Fin N => (AddCircle.haarAddCircle : Measure Circ)) (fun i => (α i : Circ))
  have he : torusShift α = fun θ => (fun i => (α i : Circ)) + θ := by
    funext θ; exact add_comm _ _
  rw [he]
  exact h

/-- The representative map of the circle is measurable. -/
theorem measurable_angleRep : Measurable angleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2 * π) 0).measurable

/-- **Item 1.** The real representative `θ ↦ θ'` is measurable. -/
theorem measurable_torusRep : Measurable (torusRep (N := N)) :=
  measurable_pi_iff.2 fun i => measurable_angleRep.comp (measurable_pi_apply i)

/-- The phase map `θ ↦ (e^{iθ'_k})_k` (the diagonal of `P_{θ'}`). -/
def torusPhase (θ : Torus N) (k : Fin N) : ℂ := Complex.exp ((torusRep θ k : ℂ) * Complex.I)

/-- **Item 1.** The phase map is measurable. -/
theorem measurable_torusPhase : Measurable (torusPhase (N := N)) :=
  measurable_pi_iff.2 fun k => Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp ((measurable_pi_apply k).comp measurable_torusRep)).mul_const _)

/-- The representative projects back to the point. -/
theorem coe_angleRep (x : Circ) : ((angleRep x : ℝ) : Circ) = x :=
  (AddCircle.equivIco (2 * π) 0).symm_apply_apply x

/-- `e^{i(t + 2πn)} = e^{it}`. -/
theorem exp_ofReal_add_int_mul (t : ℝ) (n : ℤ) :
    Complex.exp (((t + n * (2 * π) : ℝ) : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I) := by
  have h : (((t + n * (2 * π) : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The representative of `x + t` and `t + x'` differ by a multiple of `2π`, so they have the same
phase. -/
theorem exp_angleRep_add (x : Circ) (t : ℝ) :
    Complex.exp ((angleRep (x + t) : ℂ) * Complex.I) =
      Complex.exp (((t + angleRep x : ℝ) : ℂ) * Complex.I) := by
  have h0 : ((angleRep (x + t) - (t + angleRep x) : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, coe_angleRep, coe_angleRep, add_comm (x : Circ),
      sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * π)).1 h0
  have : angleRep (x + t) = (t + angleRep x) + n * (2 * π) := by
    rw [zsmul_eq_mul] at hn; linarith
  rw [this, exp_ofReal_add_int_mul]

/-- `(α, z) ↦ labelPhase α z` is jointly continuous. -/
theorem continuous_labelPhase_joint :
    Continuous fun q : (Fin N → ℝ) × RefState N p => labelPhase q.1 q.2 := by
  unfold labelPhase; fun_prop

/-- `(α, M) ↦ labelPhaseMatrix α M` is jointly continuous. -/
theorem continuous_labelPhaseMatrix_joint :
    Continuous fun q : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℂ => labelPhaseMatrix q.1 q.2 := by
  refine continuous_matrix fun i j => ?_
  unfold labelPhaseMatrix
  simp only [Matrix.of_apply]
  fun_prop

/-!
## label phase algebra
-/

/-- **Composition of phase conjugations**: `labelPhaseMatrix α ∘ labelPhaseMatrix β =
labelPhaseMatrix (α + β)`. -/
theorem labelPhaseMatrix_labelPhaseMatrix (α β : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    labelPhaseMatrix α (labelPhaseMatrix β M) = labelPhaseMatrix (α + β) M := by
  ext i j
  simp only [labelPhaseMatrix, Matrix.of_apply, Pi.add_apply, Complex.ofReal_add, add_mul, neg_add,
    Complex.exp_add]
  ring

/-- `labelPhase α ∘ labelPhase β = labelPhase (α + β)`. -/
theorem labelPhase_labelPhase (α β : Fin N → ℝ) (z : RefState N p) :
    labelPhase α (labelPhase β z) = labelPhase (α + β) z := by
  funext i
  simp only [labelPhase, Pi.add_apply, Complex.ofReal_add, add_mul, Complex.exp_add, smul_smul]

/-- `labelPhase 0 = id`. -/
theorem labelPhase_zero (z : RefState N p) : labelPhase 0 z = z := by
  funext i
  simp only [labelPhase, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]

/-- `labelPhase (-α) ∘ labelPhase α = id`. -/
theorem labelPhase_neg_labelPhase (α : Fin N → ℝ) (z : RefState N p) :
    labelPhase (-α) (labelPhase α z) = z := by
  rw [labelPhase_labelPhase, neg_add_cancel, labelPhase_zero]

/-- `labelPhase α ∘ labelPhase (-α) = id`. -/
theorem labelPhase_labelPhase_neg (α : Fin N → ℝ) (z : RefState N p) :
    labelPhase α (labelPhase (-α) z) = z := by
  rw [labelPhase_labelPhase, add_neg_cancel, labelPhase_zero]

/-- `labelPhaseMatrix α` depends on `α` only through the phases `e^{iα_k}`. -/
theorem labelPhaseMatrix_congr {α β : Fin N → ℝ}
    (h : ∀ i, Complex.exp ((α i : ℂ) * Complex.I) = Complex.exp ((β i : ℂ) * Complex.I)) :
    labelPhaseMatrix α = labelPhaseMatrix β := by
  funext M
  ext i j
  simp only [labelPhaseMatrix, Matrix.of_apply, Complex.exp_neg, h]

/-- `labelPhase α` depends on `α` only through the phases `e^{iα_k}`. -/
theorem labelPhase_congr {α β : Fin N → ℝ}
    (h : ∀ i, Complex.exp ((α i : ℂ) * Complex.I) = Complex.exp ((β i : ℂ) * Complex.I)) :
    (labelPhase α : RefState N p → RefState N p) = labelPhase β := by
  funext z i
  simp only [labelPhase, h]

/-- `labelPhase (-α)` depends on `α` only through the phases `e^{iα_k}`. -/
theorem labelPhase_neg_congr {α β : Fin N → ℝ}
    (h : ∀ i, Complex.exp ((α i : ℂ) * Complex.I) = Complex.exp ((β i : ℂ) * Complex.I)) :
    (labelPhase (-α) : RefState N p → RefState N p) = labelPhase (-β) := by
  funext z i
  simp only [labelPhase, Pi.neg_apply, Complex.ofReal_neg, neg_mul, Complex.exp_neg, h]

/-- `labelPhase α` is additive. -/
theorem labelPhase_add (α : Fin N → ℝ) (z w : RefState N p) :
    labelPhase α (z + w) = labelPhase α z + labelPhase α w := by
  funext i
  simp only [labelPhase, Pi.add_apply, smul_add]

/-- `P_β (M z) = (P_β M P_β⁻¹) (P_β z)`, where `P_β M P_β⁻¹ = labelPhaseMatrix (-β) M`. -/
theorem labelPhase_lmul (β : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    labelPhase β (lmul M z) = lmul (labelPhaseMatrix (-β) M) (labelPhase β z) := by
  funext i q
  simp only [labelPhase, lmul, labelPhaseMatrix, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply, Complex.ofReal_neg, neg_mul, neg_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Complex.exp (-((β j : ℂ) * Complex.I)) * Complex.exp ((β j : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (-(Complex.exp ((β i : ℂ) * Complex.I) * M i j * z j q)) * h1

/-- Label phases preserve the (sup) norm of arrays. -/
theorem norm_labelPhase (α : Fin N → ℝ) (z : RefState N p) : ‖labelPhase α z‖ = ‖z‖ := by
  have hle : ∀ (β : Fin N → ℝ) (w : RefState N p), ‖labelPhase β w‖ ≤ ‖w‖ := by
    intro β w
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simp only [labelPhase, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_le_pi_norm w i
  refine le_antisymm (hle α z) ?_
  calc ‖z‖ = ‖labelPhase (-α) (labelPhase α z)‖ := by rw [labelPhase_neg_labelPhase]
    _ ≤ _ := hle _ _

/-- `labelPhase α` as a real continuous linear equivalence. -/
def phaseL (α : Fin N → ℝ) : RefState N p ≃L[ℝ] RefState N p :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := labelPhase α
      invFun := labelPhase (-α)
      map_add' := labelPhase_add α
      map_smul' := fun t z => by
        funext i q
        simp only [labelPhase, Pi.smul_apply, smul_eq_mul, Complex.real_smul, RingHom.id_apply]
        ring
      left_inv := labelPhase_neg_labelPhase α
      right_inv := labelPhase_labelPhase_neg α }

@[simp] theorem phaseL_apply (α : Fin N → ℝ) (z : RefState N p) : phaseL α z = labelPhase α z := rfl

/-- `‖P_α‖ ≤ 1` as an operator. -/
theorem norm_phaseL_le (α : Fin N → ℝ) :
    ‖(phaseL (p := p) α : RefState N p →L[ℝ] RefState N p)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    simp only [ContinuousLinearEquiv.coe_coe, phaseL_apply, norm_labelPhase, one_mul, le_refl]

/-- `P_α⁻¹ = P_{-α}`. -/
theorem phaseL_symm (α : Fin N → ℝ) : (phaseL α : RefState N p ≃L[ℝ] RefState N p).symm = phaseL (-α) := by
  refine ContinuousLinearEquiv.ext (funext fun z => ?_)
  rw [ContinuousLinearEquiv.symm_apply_eq, phaseL_apply, phaseL_apply, labelPhase_labelPhase_neg]

/-!
## equivariance
-/

local notation "tX" => BlockBand.Internal.Contracts.TransmissionFlow.rotX
local notation "tY" => BlockBand.Internal.Contracts.TransmissionFlow.rotY

/-- Sum of a single-entry indicator. -/
theorem sum_ite_and_eq {M : Type*} [AddCommMonoid M] (a k b : Fin N) (f : Fin N → M) :
    ∑ x, (if a = k ∧ b = x then f x else 0) = if a = k then f b else 0 := by
  by_cases h : a = k
  · simp only [h, true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · simp only [h, false_and, ↓reduceIte, Finset.sum_const_zero]

/-- Entries of `X_ij z` for the matrix `rotX`. -/
theorem lmul_rotX_apply (i j : Fin N) (w : RefState N p) (k : Fin N) (q : Fin p) :
    lmul (tX i j) w k q = (if k = j then w i q else 0) - (if k = i then w j q else 0) := by
  simp only [lmul, BlockBand.Internal.Contracts.TransmissionFlow.rotX, Matrix.sub_apply,
    Matrix.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [sum_ite_and_eq, sum_ite_and_eq]
  congr 1 <;> exact if_congr eq_comm rfl rfl

/-- Entries of `Y_ij z` for the matrix `rotY`. -/
theorem lmul_rotY_apply (i j : Fin N) (w : RefState N p) (k : Fin N) (q : Fin p) :
    lmul (tY i j) w k q =
      (if k = j then Complex.I * w i q else 0) + (if k = i then Complex.I * w j q else 0) := by
  simp only [lmul, BlockBand.Internal.Contracts.TransmissionFlow.rotY, Matrix.smul_apply,
    Matrix.add_apply, Matrix.single_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [sum_ite_and_eq, sum_ite_and_eq]
  congr 1 <;> exact if_congr eq_comm rfl rfl

/-- `e^{iθ_j} = (cos φ + i sin φ) e^{iθ_i}` with `φ = θ_j - θ_i`. -/
theorem exp_pair (θ : Fin N → ℝ) (i j : Fin N) :
    Complex.exp ((θ j : ℂ) * Complex.I) =
      ((Real.cos (θ j - θ i) : ℂ) + (Real.sin (θ j - θ i) : ℂ) * Complex.I) *
        Complex.exp ((θ i : ℂ) * Complex.I) := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `cos² φ + sin² φ = 1` in `ℂ`. -/
theorem cos_sq_add_sin_sq_complex (φ : ℝ) :
    ((Real.cos φ : ℂ)) ^ 2 + ((Real.sin φ : ℂ)) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq φ

/-- **Pair rotation.** For `i ≠ j`, `P_θ X_ij z = cos φ X_ij (P_θ z) + sin φ Y_ij (P_θ z)`,
`φ = θ_j - θ_i`. -/
theorem labelPhase_lmul_rotX {i j : Fin N} (hij : i ≠ j) (θ : Fin N → ℝ) (z : RefState N p) :
    labelPhase θ (lmul (tX i j) z) =
      Real.cos (θ j - θ i) • lmul (tX i j) (labelPhase θ z) +
        Real.sin (θ j - θ i) • lmul (tY i j) (labelPhase θ z) := by
  funext k q
  have hu := exp_pair θ i j
  have hcs := cos_sq_add_sin_sq_complex (θ j - θ i)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  rw [show labelPhase θ (lmul (tX i j) z) k q =
    Complex.exp ((θ k : ℂ) * Complex.I) * lmul (tX i j) z k q from rfl,
    lmul_rotX_apply, lmul_rotX_apply, lmul_rotY_apply]
  simp only [labelPhase, Pi.smul_apply, smul_eq_mul]
  by_cases hkj : k = j
  · subst hkj
    simp only [ite_true, Ne.symm hij, ite_false, sub_zero, add_zero]
    rw [hu]; ring
  · by_cases hki : k = i
    · subst hki
      simp only [ite_true, hkj, ite_false, zero_sub, zero_add]
      rw [hu]
      linear_combination (Complex.exp ((θ k : ℂ) * Complex.I) * z j q) * hcs -
        (((Real.sin (θ j - θ k) : ℂ)) ^ 2 * Complex.exp ((θ k : ℂ) * Complex.I) * z j q) * hI
    · simp only [hkj, ↓reduceIte, hki, sub_self, mul_zero, Complex.ofReal_cos, Complex.ofReal_sub,
        Complex.ofReal_sin, add_zero]

/-- For `i ≠ j`, `P_θ Y_ij z = -sin φ X_ij (P_θ z) + cos φ Y_ij (P_θ z)`, `φ = θ_j - θ_i`. -/
theorem labelPhase_lmul_rotY {i j : Fin N} (hij : i ≠ j) (θ : Fin N → ℝ) (z : RefState N p) :
    labelPhase θ (lmul (tY i j) z) =
      (-Real.sin (θ j - θ i)) • lmul (tX i j) (labelPhase θ z) +
        Real.cos (θ j - θ i) • lmul (tY i j) (labelPhase θ z) := by
  funext k q
  have hu := exp_pair θ i j
  have hcs := cos_sq_add_sin_sq_complex (θ j - θ i)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  rw [show labelPhase θ (lmul (tY i j) z) k q =
    Complex.exp ((θ k : ℂ) * Complex.I) * lmul (tY i j) z k q from rfl,
    lmul_rotY_apply, lmul_rotX_apply, lmul_rotY_apply]
  simp only [labelPhase, Pi.smul_apply, smul_eq_mul]
  by_cases hkj : k = j
  · subst hkj
    simp only [ite_true, Ne.symm hij, ite_false, sub_zero, add_zero]
    rw [hu, Complex.ofReal_neg]
    linear_combination
      ((Real.sin (θ k - θ i) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * z i q) * hI
  · by_cases hki : k = i
    · subst hki
      simp only [ite_true, hkj, ite_false, zero_sub, zero_add]
      rw [hu, Complex.ofReal_neg]
      linear_combination (-(Complex.I * Complex.exp ((θ k : ℂ) * Complex.I) * z j q)) * hcs -
        ((Real.sin (θ j - θ k) : ℂ) * (Real.cos (θ j - θ k) : ℂ) *
          Complex.exp ((θ k : ℂ) * Complex.I) * z j q) * hI
    · simp only [hkj, ↓reduceIte, hki, add_zero, mul_zero, Complex.ofReal_neg, Complex.ofReal_sin,
        Complex.ofReal_sub, sub_self, Complex.ofReal_cos]

/-- `P_θ (X X z) + P_θ (Y Y z) = X X (P_θ z) + Y Y (P_θ z)` for `X = X_ij`, `Y = Y_ij`, `i ≠ j`. -/
theorem labelPhase_rot_sq {i j : Fin N} (hij : i ≠ j) (θ : Fin N → ℝ) (z : RefState N p) :
    labelPhase θ (lmul (tX i j) (lmul (tX i j) z)) + labelPhase θ (lmul (tY i j) (lmul (tY i j) z)) =
      lmul (tX i j) (lmul (tX i j) (labelPhase θ z)) +
        lmul (tY i j) (lmul (tY i j) (labelPhase θ z)) := by
  rw [labelPhase_lmul_rotX hij, labelPhase_lmul_rotY hij, labelPhase_lmul_rotX hij,
    labelPhase_lmul_rotY hij]
  have hcs : Real.cos (θ j - θ i) ^ 2 + Real.sin (θ j - θ i) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  simp only [← lmulL_apply, map_add, map_smul]
  linear_combination (norm := module)
    hcs • (lmulL (p := p) (tX i j) (lmulL (tX i j) (labelPhase θ z))) +
      hcs • (lmulL (p := p) (tY i j) (lmulL (tY i j) (labelPhase θ z)))

/-- Label phases commute with the row projections. -/
theorem labelPhase_rowProj (θ : Fin N → ℝ) (i : Fin N) (z : RefState N p) :
    labelPhase θ (rowProj i z) = rowProj i (labelPhase θ z) := by
  funext k q
  simp only [labelPhase, rowProj, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp only [mul_zero]

/-- `P_θ e_{iα} = cos θ_i e_{iα} + sin θ_i (i e_{iα})`. -/
theorem labelPhase_unitEntry (θ : Fin N → ℝ) (i : Fin N) (α : Fin p) :
    labelPhase θ (unitEntry i α) =
      Real.cos (θ i) • unitEntry i α + Real.sin (θ i) • (Complex.I • unitEntry i α) := by
  funext k q
  simp only [labelPhase, unitEntry, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  by_cases h : k = i ∧ q = α
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one]
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
  · simp only [h, ite_false, mul_zero, add_zero]

/-- `P_θ (i e_{iα}) = -sin θ_i e_{iα} + cos θ_i (i e_{iα})`. -/
theorem labelPhase_I_unitEntry (θ : Fin N → ℝ) (i : Fin N) (α : Fin p) :
    labelPhase θ (Complex.I • unitEntry i α) =
      (-Real.sin (θ i)) • unitEntry i α + Real.cos (θ i) • (Complex.I • unitEntry i α) := by
  funext k q
  simp only [labelPhase, unitEntry, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  by_cases h : k = i ∧ q = α
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one, Complex.ofReal_neg]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination (Real.sin (θ k) : ℂ) * Complex.I_mul_I
  · simp only [h, ite_false, mul_zero, add_zero]

/-- `Q(ca + sb, ca + sb) + Q(-sa + cb, -sa + cb) = Q(a, a) + Q(b, b)` when `c² + s² = 1`. -/
theorem bilin_rot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : E →L[ℝ] E →L[ℝ] ℝ)
    (a b : E) {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    Q (c • a + s • b) (c • a + s • b) + Q ((-s) • a + c • b) ((-s) • a + c • b) =
      Q a a + Q b b := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul]
  linear_combination (Q a a + Q b b) * h

/-- The first-order part of the generator is equivariant: `genL z (L ∘ P_θ) = genL (P_θ z) L`. -/
theorem genL_phase (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (θ : Fin N → ℝ) (z : RefState N p)
    (L : RefState N p →L[ℝ] ℝ) :
    genL ρ κ z (L.comp (phaseL (p := p) θ : RefState N p →L[ℝ] RefState N p)) =
      genL ρ κ (labelPhase θ z) L := by
  rw [genL_apply, genL_apply]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
        Function.comp_apply, phaseL_apply]
      rw [← map_add, labelPhase_rot_sq (ne_of_lt hij), map_add]
    · rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
        Function.comp_apply, phaseL_apply, labelPhase_rowProj]

/-- The second-order part is equivariant: if `Q'(u, v) = Q(P_θ u, P_θ v)` then
`genQ z Q' = genQ (P_θ z) Q`. -/
theorem genQ_phase (ρ : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) (θ : Fin N → ℝ) (z : RefState N p)
    (Q Q' : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (hQ : ∀ u v, Q' u v = Q (labelPhase θ u) (labelPhase θ v)) :
    genQ ρ κ z Q' = genQ ρ κ (labelPhase θ z) Q := by
  rw [genQ_apply, genQ_apply]
  simp only [hQ]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · rw [labelPhase_lmul_rotX (ne_of_lt hij), labelPhase_lmul_rotY (ne_of_lt hij),
        bilin_rot Q _ _ (Real.cos_sq_add_sin_sq _)]
    · rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [labelPhase_unitEntry, labelPhase_I_unitEntry, bilin_rot Q _ _ (Real.cos_sq_add_sin_sq _)]

/-- `D(h ∘ P_θ)(z) = Dh(P_θ z) ∘ P_θ`, for any `h`. -/
theorem fderiv_comp_labelPhase (h : RefState N p → ℝ) (θ : Fin N → ℝ) (z : RefState N p) :
    fderiv ℝ (h ∘ labelPhase θ) z =
      (fderiv ℝ h (labelPhase θ z)).comp (phaseL (p := p) θ : RefState N p →L[ℝ] RefState N p) :=
  (phaseL θ).comp_right_fderiv (f := h)

/-- `D²(h ∘ P_θ)(z)(u, v) = D²h(P_θ z)(P_θ u, P_θ v)`, for any `h` (`P_θ` is a linear
isomorphism). -/
theorem fderiv_fderiv_comp_labelPhase (h : RefState N p → ℝ) (θ : Fin N → ℝ)
    (z u v : RefState N p) :
    fderiv ℝ (fderiv ℝ (h ∘ labelPhase θ)) z u v =
      fderiv ℝ (fderiv ℝ h) (labelPhase θ z) (labelPhase θ u) (labelPhase θ v) := by
  set e : RefState N p ≃L[ℝ] RefState N p := phaseL θ
  set A : (RefState N p →L[ℝ] ℝ) ≃L[ℝ] (RefState N p →L[ℝ] ℝ) :=
    e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have h1 : fderiv ℝ (h ∘ labelPhase θ) = A ∘ (fderiv ℝ h ∘ e) := by
    funext x
    rw [fderiv_comp_labelPhase]
    ext w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, phaseL_apply,
      Function.comp_apply, ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply, A, e]
  rw [h1, A.comp_fderiv, e.comp_right_fderiv]
  simp only [phaseL_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.refl_apply, A, e]

/-- **Equivariance of the reference generator under label phases** (any `h`, any coefficients). -/
theorem refGenerator_comp_labelPhase (ρ : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (s : ℝ)
    (h : RefState N p → ℝ) (θ : Fin N → ℝ) (z : RefState N p) :
    refGenerator ρ κ s (h ∘ labelPhase θ) z = refGenerator ρ κ s h (labelPhase θ z) := by
  rw [refGenerator_eq_gen, refGenerator_eq_gen, fderiv_comp_labelPhase, genL_phase,
    genQ_phase _ _ θ z _ _ (fderiv_fderiv_comp_labelPhase h θ z)]

/-!
## symmetrized pair
-/

/-- Phases of the shifted representative: `e^{i (θ + α)'_k} = e^{i (α_k + θ'_k)}`. -/
theorem exp_torusRep_shift (α : Fin N → ℝ) (θ : Torus N) (i : Fin N) :
    Complex.exp ((torusRep (torusShift α θ) i : ℂ) * Complex.I) =
      Complex.exp (((α + torusRep θ) i : ℂ) * Complex.I) :=
  exp_angleRep_add (θ i) (α i)

attribute [local instance] matrix_secondCountable

section Pair

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- Symmetrized kernel `𝓜(ω₀, θ) = P_{θ'}⁻¹ K(ω₀) P_{θ'}` on `Ω₀ × Torus N`. -/
def symKernel (Kf : Ω₀ → Matrix (Fin N) (Fin N) ℂ) (x : Ω₀ × Torus N) :
    Matrix (Fin N) (Fin N) ℂ :=
  labelPhaseMatrix (torusRep x.2) (Kf x.1)

/-- Symmetrized noise `Ξ(ω₀, θ) = P_{θ'}⁻¹ Λ(ω₀)` on `Ω₀ × Torus N`. -/
def symNoise (Λ : Ω₀ → RefState N p) (x : Ω₀ × Torus N) : RefState N p :=
  labelPhase (-torusRep x.2) (Λ x.1)

/-- The symmetrized kernel is measurable. -/
theorem measurable_symKernel {Kf : Ω₀ → Matrix (Fin N) (Fin N) ℂ} (hK : Measurable Kf) :
    Measurable (symKernel Kf) := by
  have h1 : Measurable fun x : Ω₀ × Torus N => (torusRep x.2, Kf x.1) :=
    (measurable_torusRep.comp measurable_snd).prodMk (hK.comp measurable_fst)
  have h2 : Measurable fun q : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℂ => labelPhaseMatrix q.1 q.2 :=
    continuous_labelPhaseMatrix_joint.measurable
  have he : symKernel Kf = (fun q : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℂ =>
      labelPhaseMatrix q.1 q.2) ∘ (fun x : Ω₀ × Torus N => (torusRep x.2, Kf x.1)) := rfl
  rw [he]
  exact h2.comp h1

/-- The symmetrized noise is measurable. -/
theorem measurable_symNoise {Λ : Ω₀ → RefState N p} (hΛ : Measurable Λ) :
    Measurable (symNoise Λ) := by
  have h1 : Measurable fun x : Ω₀ × Torus N => (-torusRep x.2, Λ x.1) :=
    (measurable_torusRep.comp measurable_snd).neg.prodMk (hΛ.comp measurable_fst)
  have h2 : Measurable fun q : (Fin N → ℝ) × RefState N p => labelPhase q.1 q.2 :=
    continuous_labelPhase_joint.measurable
  have he : symNoise Λ = (fun q : (Fin N → ℝ) × RefState N p => labelPhase q.1 q.2) ∘
      (fun x : Ω₀ × Torus N => (-torusRep x.2, Λ x.1)) := rfl
  rw [he]
  exact h2.comp h1

omit [MeasurableSpace Ω₀] in
/-- Phase conjugation of `(𝓜, Ξ)` by `α` is `(𝓜, Ξ)` at the shifted torus point. -/
theorem symPair_shift (Kf : Ω₀ → Matrix (Fin N) (Fin N) ℂ) (Λ : Ω₀ → RefState N p)
    (α : Fin N → ℝ) (x : Ω₀ × Torus N) :
    (labelPhaseMatrix α (symKernel Kf x), labelPhase (fun i => -α i) (symNoise Λ x)) =
      (symKernel Kf (Prod.map id (torusShift α) x), symNoise Λ (Prod.map id (torusShift α) x)) := by
  have h := exp_torusRep_shift α x.2
  simp only [symKernel, symNoise, Prod.map_fst, Prod.map_snd, id]
  rw [labelPhaseMatrix_labelPhaseMatrix, labelPhaseMatrix_congr h,
    show (fun i => -α i) = -α from rfl, labelPhase_labelPhase, ← neg_add,
    labelPhase_neg_congr h]

/-- **Phase covariance.** On `(Ω₀ × Torus N, P₀ ⊗ Haar)`, for every `α : Fin N → ℝ`, the law of
`(P_α⁻¹ 𝓜 P_α, P_α⁻¹ Ξ)` is the law of `(𝓜, Ξ)`. This is the shape of the `phase_covariant`
field of `IsReferenceFlow`. -/
theorem phase_covariant_sym (P₀ : Measure Ω₀) [SFinite P₀] {Kf : Ω₀ → Matrix (Fin N) (Fin N) ℂ}
    {Λ : Ω₀ → RefState N p} (hK : Measurable Kf) (hΛ : Measurable Λ) (α : Fin N → ℝ) :
    (P₀.prod (torusHaar N)).map
        (fun x => (labelPhaseMatrix α (symKernel Kf x), labelPhase (fun i => -α i) (symNoise Λ x))) =
      (P₀.prod (torusHaar N)).map (fun x => (symKernel Kf x, symNoise Λ x)) := by
  have hT : MeasurePreserving (Prod.map id (torusShift α)) (P₀.prod (torusHaar N))
      (P₀.prod (torusHaar N)) :=
    (MeasurePreserving.id P₀).prod (measurePreserving_torusShift α)
  have hF : Measurable fun x : Ω₀ × Torus N => (symKernel Kf x, symNoise Λ x) :=
    (measurable_symKernel hK).prodMk (measurable_symNoise hΛ)
  rw [show (fun x => (labelPhaseMatrix α (symKernel Kf x), labelPhase (fun i => -α i) (symNoise Λ x)))
      = (fun x : Ω₀ × Torus N => (symKernel Kf x, symNoise Λ x)) ∘ Prod.map id (torusShift α) from
      funext (symPair_shift Kf Λ α), ← Measure.map_map hF hT.measurable, hT.map_eq]

end Pair

/-!
## backward
-/

/-- `f ∘ P_α` has the same bounded-`C²` constant as `f`. -/
theorem isC2BoundedBy_comp_labelPhase {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (α : Fin N → ℝ) : IsC2BoundedBy C (f ∘ labelPhase α) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  have he : f ∘ labelPhase α = f ∘ ⇑(phaseL (p := p) α : RefState N p →L[ℝ] RefState N p) := rfl
  refine ⟨?_, fun z => hf.bound _, fun z => ?_, fun z => ?_⟩
  · rw [he]; exact hf.contDiff.comp (ContinuousLinearMap.contDiff _)
  · rw [fderiv_comp_labelPhase]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ f (labelPhase α z)‖ * ‖(phaseL (p := p) α : RefState N p →L[ℝ] RefState N p)‖
        ≤ C * 1 := mul_le_mul (hf.deriv_bound _) (norm_phaseL_le α) (norm_nonneg _) hC
      _ = C := mul_one C
  · rw [he, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf.contDiff _ (by norm_num)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc ‖iteratedFDeriv ℝ 2 f ((phaseL (p := p) α : RefState N p →L[ℝ] RefState N p) z)‖ *
          ∏ _i : Fin 2, ‖(phaseL (p := p) α : RefState N p →L[ℝ] RefState N p)‖
        ≤ C * 1 := by
          refine mul_le_mul (hf.hessian_bound _) ?_ (by positivity) hC
          rw [Fin.prod_univ_two]
          calc ‖(phaseL (p := p) α : RefState N p →L[ℝ] RefState N p)‖ *
                ‖(phaseL (p := p) α : RefState N p →L[ℝ] RefState N p)‖ ≤ 1 * 1 :=
              mul_le_mul (norm_phaseL_le α) (norm_phaseL_le α) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = C := mul_one C

/-- `‖M w‖ ≤ N ‖w‖` when all entries of `M` have modulus at most `1`. -/
theorem norm_lmul_le {M : Matrix (Fin N) (Fin N) ℂ} (hM : ∀ i j, ‖M i j‖ ≤ 1) (w : RefState N p) :
    ‖lmul M w‖ ≤ N * ‖w‖ :=
  ((lmulL M : RefState N p →L[ℝ] RefState N p).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (norm_lmulL_le hM) (norm_nonneg _))

/-- `arrayMul` is `lmul`. -/
theorem arrayMul_eq_lmul (M : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    arrayMul M z = lmul M z := rfl

section Backward

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ρ : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}
  {K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

omit [IsProbabilityMeasure μ] in
/-- From `covariance` (`L Lᴴ = 1 - K Kᴴ`): a.s., all entries of `K_s`, `s ∈ [a, c]`, have
modulus at most `1`. -/
theorem ae_kernel_entry_le (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, ∀ i j, ‖K s y i j‖ ≤ 1 := by
  filter_upwards [hRF.covariance] with y hy s hs i j
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => (M i i).re) (hy s hs)
  simp only [Matrix.sub_apply, Complex.sub_re, Matrix.one_apply_eq, Complex.one_re] at h
  rw [re_mul_conjTranspose_diag, re_mul_conjTranspose_diag] at h
  have h0 : 0 ≤ ∑ k, ‖L s y i k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ‖K s y i j‖ ^ 2 ≤ ∑ k, ‖K s y i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖K s y i k‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  nlinarith [norm_nonneg (K s y i j)]

/-- Bound for the double average `E_aux E_G`. -/
theorem abs_iint_le {F : DriverSample S (RotIdx N) → RefState N p → ℝ} {B : ℝ}
    (h : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ G, |F y G| ≤ B) :
    |∫ y, ∫ G, F y G ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ| ≤ B := by
  have h1 : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ‖∫ G, F y G ∂matCircularLaw N p‖ ≤ B := by
    filter_upwards [h] with y hy
    have := norm_integral_le_of_norm_le_const (μ := matCircularLaw N p) (f := F y) (C := B)
      (Eventually.of_forall fun G => by simpa only [Real.norm_eq_abs] using hy G)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using this
  have := norm_integral_le_of_norm_le_const h1
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using this

/-- Measurability in `θ` of the double average of a continuous function of
`(θ', (K_s, L_s), G)`. -/
theorem aesm_phase_iint {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s))
    (Φ : (Fin N → ℝ) × ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p) → ℝ)
    (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun θ : Torus N => ∫ y, ∫ G, Φ (torusRep θ, ((K s y, L s y), G))
      ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ) (torusHaar N) := by
  have hg : Measurable fun q : (Torus N × DriverSample S (RotIdx N)) × RefState N p =>
      (torusRep q.1.1, ((K s q.1.2, L s q.1.2), q.2)) :=
    (measurable_torusRep.comp (measurable_fst.comp measurable_fst)).prodMk
      (((hK.comp (measurable_snd.comp measurable_fst)).prodMk
        (hL.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  have hm : Measurable (Φ ∘ fun q : (Torus N × DriverSample S (RotIdx N)) × RefState N p =>
      (torusRep q.1.1, ((K s q.1.2, L s q.1.2), q.2))) := hΦ.measurable.comp hg
  have h1 := hm.stronglyMeasurable.integral_prod_right' (ν := matCircularLaw N p)
  have h2 := h1.integral_prod_right' (ν := driverLaw (κ := RotIdx N) μ)
  exact h2.aestronglyMeasurable

/-- The affine map inside the symmetrized backward function, as a function of
`(α, (M, M'), G)`. -/
def phaseAff (z : RefState N p)
    (q : (Fin N → ℝ) × ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p)) :
    RefState N p :=
  labelPhase (-q.1) (lmul q.2.1.1 (labelPhase q.1 z) + lmul q.2.1.2 q.2.2)

/-- The linear part. -/
def phaseLin (u : RefState N p)
    (q : (Fin N → ℝ) × ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p)) :
    RefState N p :=
  labelPhase (-q.1) (lmul q.2.1.1 (labelPhase q.1 u))

/-- `phaseAff z` is continuous. -/
theorem continuous_phaseAff (z : RefState N p) : Continuous (phaseAff (N := N) z) := by
  unfold phaseAff
  have h1 : Continuous fun q : (Fin N → ℝ) ×
      ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p) =>
      labelPhase q.1 z :=
    continuous_labelPhase_joint.comp (continuous_fst.prodMk continuous_const)
  exact continuous_labelPhase_joint.comp (continuous_fst.neg.prodMk
    ((continuous_lmul_joint.comp ((continuous_snd.fst.fst).prodMk h1)).add
      (continuous_lmul_joint.comp ((continuous_snd.fst.snd).prodMk continuous_snd.snd))))

/-- `phaseLin u` is continuous. -/
theorem continuous_phaseLin (u : RefState N p) : Continuous (phaseLin (N := N) u) := by
  unfold phaseLin
  have h1 : Continuous fun q : (Fin N → ℝ) ×
      ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p) =>
      labelPhase q.1 u :=
    continuous_labelPhase_joint.comp (continuous_fst.prodMk continuous_const)
  exact continuous_labelPhase_joint.comp (continuous_fst.neg.prodMk
    (continuous_lmul_joint.comp ((continuous_snd.fst.fst).prodMk h1)))

/-- `genL ρ κ z L` is jointly continuous in `((ρ, κ), L)`. -/
theorem continuous_genL_joint (z : RefState N p) :
    Continuous fun q : ((Fin N → Fin N → ℝ) × (Fin N → ℝ)) × (RefState N p →L[ℝ] ℝ) =>
      genL q.1.1 q.1.2 z q.2 := by
  simp only [genL_apply]
  refine (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)).add (continuous_finsetSum _ fun i _ => ?_)
  · split_ifs
    · have hρ : Continuous fun q : ((Fin N → Fin N → ℝ) × (Fin N → ℝ)) ×
          (RefState N p →L[ℝ] ℝ) => q.1.1 i j := by fun_prop
      exact hρ.mul
        ((continuous_snd.clm_apply continuous_const).add (continuous_snd.clm_apply continuous_const))
    · exact continuous_const
  · exact (((continuous_apply i).comp continuous_fst.snd).mul continuous_const).mul
      (continuous_snd.clm_apply continuous_const)

/-- `genL` is bounded on bounded sets of coefficients and first derivatives. -/
theorem exists_genL_bound (z : RefState N p) (B R : ℝ) :
    ∃ M, ∀ (ρ' : Fin N → Fin N → ℝ) (κ' : Fin N → ℝ) (D : RefState N p →L[ℝ] ℝ),
      ‖ρ'‖ ≤ B → ‖κ'‖ ≤ B → ‖D‖ ≤ R → |genL ρ' κ' z D| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall
    (0 : ((Fin N → Fin N → ℝ) × (Fin N → ℝ)) × (RefState N p →L[ℝ] ℝ)) (max B R)).exists_bound_of_continuousOn
    (continuous_genL_joint z).continuousOn
  refine ⟨M, fun ρ' κ' D h1 h2 h3 => ?_⟩
  have hq : (((ρ', κ'), D) : ((Fin N → Fin N → ℝ) × (Fin N → ℝ)) × (RefState N p →L[ℝ] ℝ)) ∈
      Metric.closedBall 0 (max B R) := by
    rw [mem_closedBall_zero_iff]
    exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨h1.trans (le_max_left _ _),
      h2.trans (le_max_left _ _)⟩, h3.trans (le_max_right _ _)⟩
  simpa only [Real.norm_eq_abs] using hM _ hq

/-- `genQ` is bounded on bounded sets of coefficients and second derivatives. -/
theorem exists_genQ_bound (z : RefState N p) (B R : ℝ) :
    ∃ M, ∀ (ρ' : Fin N → Fin N → ℝ) (κ' : Fin N → ℝ)
      (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ),
      ‖ρ'‖ ≤ B → ‖κ'‖ ≤ B → ‖Q‖ ≤ R → |genQ ρ' κ' z Q| ≤ M := by
  refine ⟨(1 / 4 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
      B * (R * ‖lmul (tX i j) z‖ * ‖lmul (tX i j) z‖ + R * ‖lmul (tY i j) z‖ * ‖lmul (tY i j) z‖) +
    ∑ i : Fin N, (B * (1 / 4 : ℝ)) * ∑ α : Fin p,
      (R * ‖unitEntry (N := N) i α‖ * ‖unitEntry (N := N) i α‖ +
        R * ‖Complex.I • unitEntry (N := N) (p := p) i α‖ * ‖Complex.I • unitEntry (N := N) (p := p) i α‖),
    fun ρ' κ' Q h1 h2 h3 => ?_⟩
  have hB : 0 ≤ B := (norm_nonneg _).trans h1
  have hR : 0 ≤ R := (ContinuousLinearMap.opNorm_nonneg Q).trans h3
  have hQb : ∀ u v : RefState N p, |Q u v| ≤ R * ‖u‖ * ‖v‖ := fun u v => by
    rw [← Real.norm_eq_abs]
    refine (Q.le_opNorm₂ u v).trans ?_
    gcongr
  have hρ : ∀ i j, |ρ' i j| ≤ B := fun i j => by
    rw [← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (ρ' i) j).trans (norm_le_pi_norm ρ' i)).trans h1
  have hκ : ∀ i, |κ' i * (1 / 4 : ℝ)| ≤ B * (1 / 4 : ℝ) := fun i => by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm κ' i).trans h2) (by norm_num)
  rw [genQ_apply]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hρ i j) ((abs_add_le _ _).trans (add_le_add (hQb _ _) (hQb _ _)))
        (abs_nonneg _) hB
    · rw [abs_zero]; positivity
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul (hκ i) ?_ (abs_nonneg _) (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    exact (abs_add_le _ _).trans (add_le_add (hQb _ _) (hQb _ _))

/-- The symmetrized backward function. -/
def symBackward (μ : Measure S) (K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ)
    (f : RefState N p → ℝ) (s : ℝ) (z : RefState N p) : ℝ :=
  ∫ θ, refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s (labelPhase (torusRep θ) z)
    ∂torusHaar N

/-- The `θ`-integrand. -/
def symIntegrand (μ : Measure S) (K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ)
    (f : RefState N p → ℝ) (s : ℝ) (θ : Torus N) : RefState N p → ℝ :=
  refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s ∘ labelPhase (torusRep θ)

omit [IsProbabilityMeasure μ] in
/-- `symBackward s` is the `θ`-average of the `symIntegrand`s. -/
theorem symBackward_eq (f : RefState N p → ℝ) (s : ℝ) :
    symBackward μ K L f s = fun z => ∫ θ, symIntegrand μ K L f s θ z ∂torusHaar N := rfl

variable {C : ℝ} {f : RefState N p → ℝ}

omit [IsProbabilityMeasure μ] in
/-- Each `θ`-integrand is `C²` for `s ∈ [a, c]`. -/
theorem contDiff_symIntegrand (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (θ : Torus N) :
    ContDiff ℝ 2 (symIntegrand μ K L f s θ) :=
  ((hRF.backward p C _ (isC2BoundedBy_comp_labelPhase hf _)).2.2.1 s hs).comp
    (phaseL (p := p) (torusRep θ) : RefState N p →L[ℝ] RefState N p).contDiff

omit [IsProbabilityMeasure μ] in
/-- Representation of `D H_θ` for `s ∈ [a, c]` (from the `backward` field of `f ∘ P_{-θ'}`). -/
theorem fderiv_symIntegrand (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (θ : Torus N) (z u : RefState N p) :
    fderiv ℝ (symIntegrand μ K L f s θ) z u =
      ∫ y, ∫ G, fderiv ℝ f (phaseAff z (torusRep θ, ((K s y, L s y), G)))
        (phaseLin u (torusRep θ, ((K s y, L s y), G)))
        ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ := by
  unfold symIntegrand
  rw [fderiv_comp_labelPhase]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    phaseL_apply]
  rw [(hRF.backward p C _ (isC2BoundedBy_comp_labelPhase hf _)).2.2.2.1 s hs]
  congr 1; funext y; congr 1; funext G
  rw [fderiv_comp_labelPhase]
  rfl

omit [IsProbabilityMeasure μ] in
/-- Representation of `D² H_θ` for `s ∈ [a, c]`. -/
theorem fderiv_fderiv_symIntegrand
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (θ : Torus N) (z u v : RefState N p) :
    fderiv ℝ (fderiv ℝ (symIntegrand μ K L f s θ)) z u v =
      ∫ y, ∫ G, fderiv ℝ (fderiv ℝ f) (phaseAff z (torusRep θ, ((K s y, L s y), G)))
        (phaseLin u (torusRep θ, ((K s y, L s y), G))) (phaseLin v (torusRep θ, ((K s y, L s y), G)))
        ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ := by
  unfold symIntegrand
  rw [fderiv_fderiv_comp_labelPhase]
  have h5 := (hRF.backward p C _ (isC2BoundedBy_comp_labelPhase hf (-torusRep θ))).2.2.2.2.1 s hs
    (labelPhase (torusRep θ) z) (labelPhase (torusRep θ) u) (labelPhase (torusRep θ) v)
  unfold D2 at h5
  rw [h5]
  congr 1; funext y; congr 1; funext G
  rw [fderiv_fderiv_comp_labelPhase]
  rfl

/-- `|H_θ| ≤ C`. -/
theorem abs_symIntegrand_le (hf : IsC2BoundedBy C f) (s : ℝ) (θ : Torus N) (z : RefState N p) :
    |symIntegrand μ K L f s θ z| ≤ C :=
  abs_iint_le (Eventually.of_forall fun _ _ => hf.bound _)

/-- `‖D H_θ(z)‖ ≤ C N` for `s ∈ [a, c]`, uniformly in `θ` and `z`. -/
theorem norm_fderiv_symIntegrand_le
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (θ : Torus N) (z : RefState N p) :
    ‖fderiv ℝ (symIntegrand μ K L f s θ) z‖ ≤ C * N := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  rw [Real.norm_eq_abs, fderiv_symIntegrand hRF hf hs]
  refine abs_iint_le ?_
  filter_upwards [ae_kernel_entry_le hRF] with y hy G
  refine (abs_fderiv_apply_le hf _ _).trans ?_
  simp only [phaseLin, norm_labelPhase]
  calc C * ‖lmul (K s y) (labelPhase (torusRep θ) u)‖
      ≤ C * (N * ‖labelPhase (torusRep θ) u‖) :=
        mul_le_mul_of_nonneg_left (norm_lmul_le (hy s hs) _) hC
    _ = C * N * ‖u‖ := by rw [norm_labelPhase]; ring

/-- `‖D² H_θ(z)‖ ≤ C N²` for `s ∈ [a, c]`, uniformly in `θ` and `z`. -/
theorem norm_fderiv_fderiv_symIntegrand_le
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (θ : Torus N) (z : RefState N p) :
    ‖fderiv ℝ (fderiv ℝ (symIntegrand μ K L f s θ)) z‖ ≤ C * N * N := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u v => ?_
  rw [Real.norm_eq_abs, fderiv_fderiv_symIntegrand hRF hf hs]
  refine abs_iint_le ?_
  filter_upwards [ae_kernel_entry_le hRF] with y hy G
  refine (abs_D2_le hf _ _ _).trans ?_
  simp only [phaseLin, norm_labelPhase]
  have h1 := norm_lmul_le (hy s hs) (labelPhase (torusRep θ) u)
  have h2 := norm_lmul_le (hy s hs) (labelPhase (torusRep θ) v)
  rw [norm_labelPhase] at h1 h2
  calc C * ‖lmul (K s y) (labelPhase (torusRep θ) u)‖ * ‖lmul (K s y) (labelPhase (torusRep θ) v)‖
      ≤ C * (N * ‖u‖) * (N * ‖v‖) := by gcongr
    _ = C * N * N * ‖u‖ * ‖v‖ := by ring

/-- `θ ↦ H_θ(z)` is measurable. -/
theorem aesm_symIntegrand (hK : ∀ s, Measurable (K s)) (hL : ∀ s, Measurable (L s))
    (hf : IsC2BoundedBy C f) (s : ℝ) (z : RefState N p) :
    AEStronglyMeasurable (fun θ => symIntegrand μ K L f s θ z) (torusHaar N) :=
  aesm_phase_iint (hK s) (hL s) _ (hf.contDiff.continuous.comp (continuous_phaseAff z))

/-- `θ ↦ H_θ(z)` is integrable. -/
theorem integrable_symIntegrand (hK : ∀ s, Measurable (K s)) (hL : ∀ s, Measurable (L s))
    (hf : IsC2BoundedBy C f) (s : ℝ) (z : RefState N p) :
    Integrable (fun θ => symIntegrand μ K L f s θ z) (torusHaar N) :=
  Integrable.of_bound (aesm_symIntegrand hK hL hf s z) C
    (Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs]; exact abs_symIntegrand_le hf s θ z)

/-- `θ ↦ D H_θ(z)` is measurable for `s ∈ [a, c]`. -/
theorem aesm_fderiv_symIntegrand
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (z : RefState N p) :
    AEStronglyMeasurable (fun θ => fderiv ℝ (symIntegrand μ K L f s θ) z) (torusHaar N) := by
  refine aestronglyMeasurable_clm_of_apply fun u => ?_
  have hc : Continuous fun q : (Fin N → ℝ) ×
      ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p) =>
      fderiv ℝ f (phaseAff z q) (phaseLin u q) :=
    ((hf.contDiff.continuous_fderiv (by norm_num)).comp (continuous_phaseAff z)).clm_apply
      (continuous_phaseLin u)
  exact (aesm_phase_iint (hRF.measurable_kernel s) (hRF.measurable_factor s) _ hc).congr
    (Eventually.of_forall fun θ => (fderiv_symIntegrand hRF hf hs θ z u).symm)

/-- `θ ↦ D² H_θ(z)` is measurable for `s ∈ [a, c]`. -/
theorem aesm_fderiv_fderiv_symIntegrand
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (z : RefState N p) :
    AEStronglyMeasurable (fun θ => fderiv ℝ (fderiv ℝ (symIntegrand μ K L f s θ)) z)
      (torusHaar N) := by
  refine aestronglyMeasurable_clm_of_apply fun u => aestronglyMeasurable_clm_of_apply fun v => ?_
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hc : Continuous fun q : (Fin N → ℝ) ×
      ((Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) × RefState N p) =>
      fderiv ℝ (fderiv ℝ f) (phaseAff z q) (phaseLin u q) (phaseLin v q) :=
    ((hf2c.comp (continuous_phaseAff z)).clm_apply (continuous_phaseLin u)).clm_apply
      (continuous_phaseLin v)
  exact (aesm_phase_iint (hRF.measurable_kernel s) (hRF.measurable_factor s) _ hc).congr
    (Eventually.of_forall fun θ => (fderiv_fderiv_symIntegrand hRF hf hs θ z u v).symm)

/-- For `s ∈ [a, c]`, `symBackward s` is `C²`, and its first and second derivatives are the
`θ`-averages of those of the integrands. -/
theorem symBackward_static (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) :
    ContDiff ℝ 2 (symBackward μ K L f s) ∧
      (∀ z, fderiv ℝ (symBackward μ K L f s) z =
        ∫ θ, fderiv ℝ (symIntegrand μ K L f s θ) z ∂torusHaar N) ∧
      (∀ z, fderiv ℝ (fderiv ℝ (symBackward μ K L f s)) z =
        ∫ θ, fderiv ℝ (fderiv ℝ (symIntegrand μ K L f s θ)) z ∂torusHaar N) := by
  rw [symBackward_eq]
  exact integral_contDiff_two (Eventually.of_forall fun θ => contDiff_symIntegrand hRF hf hs θ)
    (Eventually.of_forall fun θ z => norm_fderiv_symIntegrand_le hRF hf hs θ z)
    (Eventually.of_forall fun θ z => norm_fderiv_fderiv_symIntegrand_le hRF hf hs θ z)
    (aesm_symIntegrand hRF.measurable_kernel hRF.measurable_factor hf s)
    (integrable_symIntegrand hRF.measurable_kernel hRF.measurable_factor hf s)
    (aesm_fderiv_symIntegrand hRF hf hs) (aesm_fderiv_fderiv_symIntegrand hRF hf hs)

/-- The reference generator commutes with the `θ`-average (using the equivariance
`refGenerator_comp_labelPhase`). -/
theorem refGenerator_symBackward
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hf : IsC2BoundedBy C f) {s : ℝ} (hs : s ∈ Icc a c) (z : RefState N p) :
    refGenerator ρ κ s (symBackward μ K L f s) z =
      ∫ θ, refGenerator ρ κ s (refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s)
        (labelPhase (torusRep θ) z) ∂torusHaar N := by
  obtain ⟨-, hd1, hd2⟩ := symBackward_static hRF hf hs
  rw [symBackward_eq] at hd1 hd2 ⊢
  rw [← integral_refGenerator ρ κ s z (aesm_fderiv_symIntegrand hRF hf hs z)
    (aesm_fderiv_fderiv_symIntegrand hRF hf hs z)
    (Eventually.of_forall fun θ => norm_fderiv_symIntegrand_le hRF hf hs θ z)
    (Eventually.of_forall fun θ => norm_fderiv_fderiv_symIntegrand_le hRF hf hs θ z)
    (hd1 z) (hd2 z)]
  congr 1
  funext θ
  exact refGenerator_comp_labelPhase ρ κ s _ (torusRep θ) z

/-- **Symmetrized backward equation.** If `(K, L)` is a reference flow
(`Palm.ReferenceFlow.IsReferenceFlow`) for `(ρ, κ)` on `[a, c]` whose coefficients are bounded on
`[a, c]`, then for every bounded-`C²` test `f`,
`∂_s symBackward s z = -refGenerator ρ κ s (symBackward s) z` on `(a, c)`. -/
theorem hasDerivAt_symBackward (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hB : ∃ B, ∀ s ∈ Icc a c, ‖ρ s‖ ≤ B ∧ ‖κ s‖ ≤ B) (hf : IsC2BoundedBy C f) :
    ∀ s ∈ Ioo a c, ∀ z : RefState N p, HasDerivAt (fun s' => symBackward μ K L f s' z)
      (-refGenerator ρ κ s (symBackward μ K L f s) z) s := by
  intro s₀ hs₀ z
  obtain ⟨B, hB⟩ := hB
  obtain ⟨M₁, hM₁⟩ := exists_genL_bound z B (C * N)
  obtain ⟨M₂, hM₂⟩ := exists_genQ_bound z B (C * N * N)
  have hIcc : ∀ s ∈ Ioo a c, s ∈ Icc a c := fun s hs => Ioo_subset_Icc_self hs
  have key : ∀ s θ, refGenerator ρ κ s (refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s)
      (labelPhase (torusRep θ) z) =
      genL (ρ s) (κ s) z (fderiv ℝ (symIntegrand μ K L f s θ) z) +
        genQ (ρ s) (κ s) z (fderiv ℝ (fderiv ℝ (symIntegrand μ K L f s θ)) z) := by
    intro s θ
    rw [← refGenerator_comp_labelPhase, ← refGenerator_eq_gen]
    rfl
  have hF'm : AEStronglyMeasurable (fun θ => -refGenerator ρ κ s₀
      (refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s₀) (labelPhase (torusRep θ) z))
      (torusHaar N) := by
    simp only [key]
    exact (((genL (ρ s₀) (κ s₀) z).continuous.comp_aestronglyMeasurable
      (aesm_fderiv_symIntegrand hRF hf (hIcc s₀ hs₀) z)).add
      ((genQ (ρ s₀) (κ s₀) z).continuous.comp_aestronglyMeasurable
      (aesm_fderiv_fderiv_symIntegrand hRF hf (hIcc s₀ hs₀) z))).neg
  have hbound : ∀ᵐ θ ∂torusHaar N, ∀ s ∈ Ioo a c, ‖-refGenerator ρ κ s
      (refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s) (labelPhase (torusRep θ) z)‖ ≤
      M₁ + M₂ := by
    refine Eventually.of_forall fun θ s hs => ?_
    rw [norm_neg, key, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add
      (hM₁ _ _ _ (hB s (hIcc s hs)).1 (hB s (hIcc s hs)).2
        (norm_fderiv_symIntegrand_le hRF hf (hIcc s hs) θ z))
      (hM₂ _ _ _ (hB s (hIcc s hs)).1 (hB s (hIcc s hs)).2
        (norm_fderiv_fderiv_symIntegrand_le hRF hf (hIcc s hs) θ z)))
  have hdiff : ∀ᵐ θ ∂torusHaar N, ∀ s ∈ Ioo a c,
      HasDerivAt (fun s' => symIntegrand μ K L f s' θ z) (-refGenerator ρ κ s
        (refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s) (labelPhase (torusRep θ) z)) s :=
    Eventually.of_forall fun θ s hs =>
      (hRF.backward p C _ (isC2BoundedBy_comp_labelPhase hf _)).2.2.2.2.2 s hs _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := torusHaar N)
    (F := fun s θ => symIntegrand μ K L f s θ z) (x₀ := s₀) (Ioo_mem_nhds hs₀.1 hs₀.2)
    (Eventually.of_forall fun s => aesm_symIntegrand hRF.measurable_kernel hRF.measurable_factor hf s z)
    (integrable_symIntegrand hRF.measurable_kernel hRF.measurable_factor hf s₀ z) hF'm hbound
    (integrable_const (M₁ + M₂)) hdiff
  have hval : ∫ θ, -refGenerator ρ κ s₀ (refSemigroup μ K L (f ∘ labelPhase (-torusRep θ)) s₀)
      (labelPhase (torusRep θ) z) ∂torusHaar N =
      -refGenerator ρ κ s₀ (symBackward μ K L f s₀) z := by
    rw [integral_neg, refGenerator_symBackward hRF hf (hIcc s₀ hs₀)]
  rw [← hval]
  exact h.2

/-- `hasDerivAt_symBackward` for coefficients continuous on `[a, c]`. -/
theorem hasDerivAt_symBackward_of_continuousOn
    (hRF : BlockBand.Palm.ReferenceFlow.IsReferenceFlow μ ρ κ a c K L)
    (hρ : ContinuousOn ρ (Icc a c)) (hκ : ContinuousOn κ (Icc a c)) (hf : IsC2BoundedBy C f) :
    ∀ s ∈ Ioo a c, ∀ z : RefState N p, HasDerivAt (fun s' => symBackward μ K L f s' z)
      (-refGenerator ρ κ s (symBackward μ K L f s) z) s := by
  obtain ⟨B₁, h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hρ
  obtain ⟨B₂, h₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hκ
  exact hasDerivAt_symBackward hRF ⟨max B₁ B₂, fun s hs =>
    ⟨(h₁ s hs).trans (le_max_left _ _), (h₂ s hs).trans (le_max_right _ _)⟩⟩ hf

/-- **Item 4 (Fubini identity).** `symBackward s z = E f(𝓜 z + Ξ)` with
`𝓜 = P_{θ'}⁻¹ K_s P_{θ'}` and `Ξ = P_{θ'}⁻¹ L_s G` on `(DriverSample × RefState) × Torus N` with
`(driverLaw μ ⊗ matCircularLaw) ⊗ Haar`. -/
theorem symBackward_eq_integral {s : ℝ} (hK : Measurable (K s)) (hL : Measurable (L s))
    (hf : IsC2BoundedBy C f) (z : RefState N p) :
    symBackward μ K L f s z =
      ∫ x, f (arrayMul (symKernel (fun ω : DriverSample S (RotIdx N) × RefState N p => K s ω.1) x) z +
          symNoise (fun ω : DriverSample S (RotIdx N) × RefState N p => lmul (L s ω.1) ω.2) x)
        ∂(prodLaw μ N p).prod (torusHaar N) := by
  have hK₀ : Measurable fun ω : DriverSample S (RotIdx N) × RefState N p => K s ω.1 :=
    hK.comp measurable_fst
  have hΛ : Measurable fun ω : DriverSample S (RotIdx N) × RefState N p => lmul (L s ω.1) ω.2 :=
    (continuous_lmul_joint.measurable).comp ((hL.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable fun x : (DriverSample S (RotIdx N) × RefState N p) × Torus N =>
      f (arrayMul (symKernel (fun ω : DriverSample S (RotIdx N) × RefState N p => K s ω.1) x) z +
        symNoise (fun ω : DriverSample S (RotIdx N) × RefState N p => lmul (L s ω.1) ω.2) x) := by
    have hc : Continuous fun q : Matrix (Fin N) (Fin N) ℂ × RefState N p => f (lmul q.1 z + q.2) :=
      hf.contDiff.continuous.comp
        ((continuous_lmul_joint.comp (continuous_fst.prodMk continuous_const)).add continuous_snd)
    have he : (fun x : (DriverSample S (RotIdx N) × RefState N p) × Torus N =>
        f (arrayMul (symKernel (fun ω : DriverSample S (RotIdx N) × RefState N p => K s ω.1) x) z +
          symNoise (fun ω : DriverSample S (RotIdx N) × RefState N p => lmul (L s ω.1) ω.2) x)) =
        (fun q : Matrix (Fin N) (Fin N) ℂ × RefState N p => f (lmul q.1 z + q.2)) ∘
          (fun x => (symKernel (fun ω : DriverSample S (RotIdx N) × RefState N p => K s ω.1) x,
            symNoise (fun ω : DriverSample S (RotIdx N) × RefState N p => lmul (L s ω.1) ω.2) x)) :=
      rfl
    rw [he]
    exact hc.measurable.comp ((measurable_symKernel hK₀).prodMk (measurable_symNoise hΛ))
  have hint : Integrable (fun x : (DriverSample S (RotIdx N) × RefState N p) × Torus N =>
      f (arrayMul (symKernel (fun ω : DriverSample S (RotIdx N) × RefState N p => K s ω.1) x) z +
        symNoise (fun ω : DriverSample S (RotIdx N) × RefState N p => lmul (L s ω.1) ω.2) x))
      ((prodLaw μ N p).prod (torusHaar N)) :=
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hf.bound _)
  rw [integral_prod_symm _ hint]
  unfold symBackward
  congr 1
  funext θ
  rw [refSemigroup_eq_prod hK hL (isC2BoundedBy_comp_labelPhase hf _)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Function.comp_apply, lmulL_apply, symKernel, symNoise]
  rw [labelPhase_add, labelPhase_lmul, neg_neg, labelPhase_neg_labelPhase]
  rfl

end Backward

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
