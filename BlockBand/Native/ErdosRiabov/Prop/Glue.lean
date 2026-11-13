module

public import BlockBand.Native.ErdosRiabov.Kernel.VSKernelExtra
public import BlockBand.Native.ErdosRiabov.Flow.Duhamel

/-!
# Glue Kernel → Duhamel: operator-valued propagators and tensor propagators

Deterministic: no measure occurs.

* `propOp M : (ι → ℂ) →L[ℝ] (ι → ℂ)`, `(propOp M f)(a) = Σ_b M_{ab} f(b)`, for a matrix `M` over a
  finite index type `ι`; `propOp_mul`, `propOp_one`, and `hasDerivAt_propOp` (entrywise
  derivatives give the operator-valued derivative).
* One variable: `hasDerivAt_propOp_vsPropagator_left` (`∂_s U(s,t) = -U(s,t) ∘ L_s` with
  `U(s,t) = propOp P̂_{s,t}`, `L_s = propOp A_s`), `hasDerivAt_propOp_vsPropagator` (forward),
  `propOp_vsPropagator_self`, and `vsPropagator_duhamel` (`duhamel_det` instantiated).
* Several sites: `tensorMat M` (`(⊗_j M_j)_{xy} = Π_j (M_j)_{x_j y_j}`, `x, y : Fin k → Fin N`),
  `tensorMat_mul`, `tensorMat_one`, the generator
  `vsTensorGen S μ μ' s = Σ_i I⊗…⊗A_i(s)⊗…⊗I` (`A_i = vsKernel S (μ i) (μ' i)`) with its action
  `(⊕_i A_i)[f](x) = Σ_i Σ_c (A_i)_{x_i c} f(x[i ↦ c])` (`propOp_vsTensorGen_apply`), the
  propagator `vsTensorProp S μ μ' s t = ⊗_j P̂_j(s,t)`, the product rule
  `hasDerivAt_tensorMat`, `hasDerivAt_propOp_vsTensorProp_left` (`∂_s U = -U ∘ ⊕_j A_j(s)`),
  the forward derivative `hasDerivAt_propOp_vsTensorProp` (`∂_t U = (⊕_j A_j(t)) ∘ U`) and
  `vsTensorProp_duhamel`. A factor `I` is the case `μ j = 0` (`P̂ = I`, `A = 0`); a conjugate
  factor `conj Q̂` is the case `(conj μ j, conj μ' j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open Matrix MeasureTheory Set
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open scoped BigOperators

/-!
## Matrices as continuous `ℝ`-linear operators
-/

section Op

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ℝ`-linear action `f ↦ (a ↦ Σ_b M_{ab} f(b))` of a matrix (as a Pi function). -/
def propOpLin (M : ι → ι → ℂ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) where
  toFun f a := ∑ b, M a b * f b
  map_add' f g := by
    ext a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext a
    simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring

/-- Matrices (as Pi functions) to continuous operators, as a continuous `ℝ`-linear map. -/
def propOpCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → ι → ℂ) →L[ℝ] ((ι → ℂ) →L[ℝ] (ι → ℂ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap (propOpLin M)
      map_add' := fun M M' => by
        ext f a
        simp [propOpLin, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c M => by
        ext f a
        simp only [LinearMap.coe_toContinuousLinearMap', propOpLin, LinearMap.coe_mk,
          AddHom.coe_mk, Pi.smul_apply, Complex.real_smul, RingHom.id_apply,
          FunLike.coe_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring }

/-- The operator `f ↦ M f` of a matrix `M`, as a continuous `ℝ`-linear map on `ι → ℂ`. -/
def propOp (M : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) := propOpCLM ι (fun a b => M a b)

theorem propOp_apply (M : Matrix ι ι ℂ) (f : ι → ℂ) (a : ι) :
    propOp M f a = ∑ b, M a b * f b := rfl

theorem propOp_mul (M M' : Matrix ι ι ℂ) : propOp (M * M') = (propOp M).comp (propOp M') := by
  ext f a
  simp only [propOp_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem propOp_one : propOp (1 : Matrix ι ι ℂ) = ContinuousLinearMap.id ℝ (ι → ℂ) := by
  ext f a
  simp [propOp_apply, Matrix.one_apply]

theorem propOp_neg (M : Matrix ι ι ℂ) : propOp (-M) = -propOp M := by
  ext f a
  simp [propOp_apply]

theorem propOp_sum {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ) :
    propOp (∑ i ∈ s, M i) = ∑ i ∈ s, propOp (M i) := by
  ext f a
  simp [propOp_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Entrywise derivatives give the operator-valued derivative. -/
theorem hasDerivAt_propOp {M : ℝ → Matrix ι ι ℂ} {M' : Matrix ι ι ℂ} {x : ℝ}
    (h : ∀ a b, HasDerivAt (fun r => M r a b) (M' a b) x) :
    HasDerivAt (fun r => propOp (M r)) (propOp M') x := by
  have hpi : HasDerivAt (fun r => (fun a b => M r a b : ι → ι → ℂ)) (fun a b => M' a b) x :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b
  exact (propOpCLM ι).hasFDerivAt.comp_hasDerivAt x hpi

/-- Duhamel for operator families given by matrices: if `∂_s U(s,t) = -U(s,t) L_s` entrywise on
`[t₀,t]`, `U(t,t) = I` and `X' = L_s X + F_s`, then `X_t = U(t₀,t) X_{t₀} + ∫ U(s,t) F_s`. -/
theorem propOp_duhamel {U : ℝ → ℝ → Matrix ι ι ℂ} {L : ℝ → Matrix ι ι ℂ} {X F : ℝ → ι → ℂ}
    {t₀ t : ℝ}
    (hU : ∀ s ∈ uIcc t₀ t, ∀ a b, HasDerivAt (fun r => U r t a b) ((-(U s t * L s)) a b) s)
    (hUt : U t t = 1)
    (hX : ∀ s ∈ uIcc t₀ t, HasDerivAt X (propOp (L s) (X s) + F s) s)
    (hint : IntervalIntegrable (fun s => propOp (U s t) (F s)) volume t₀ t) :
    X t = propOp (U t₀ t) (X t₀) + ∫ s in t₀..t, propOp (U s t) (F s) := by
  refine duhamel_det (U := fun r t' => propOp (U r t')) (L := fun s => propOp (L s))
    (fun s hs => ?_) (by rw [hUt, propOp_one]) hX hint
  have h := hasDerivAt_propOp (M' := -(U s t * L s)) (hU s hs)
  rwa [propOp_neg, propOp_mul] at h

end Op

/-!
## One variable
-/

section One

variable {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}

/-- **Backward derivative of the propagator**:
`∂_s propOp P̂_{s,t} = -(propOp P̂_{s,t}) ∘ (propOp A_s)` (operator-valued),
for a stochastic symmetric `S`, `|μ|, |μ'| < 1`, `s, t ∈ [0,1]`.
-/
theorem hasDerivAt_propOp_vsPropagator_left (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (fun r => propOp (vsPropagator S μ μ' r t))
      (-((propOp (vsPropagator S μ μ' s t)).comp (propOp (vsKernel S μ μ' s)))) s := by
  have h := hasDerivAt_propOp (M' := -(vsPropagator S μ μ' s t * vsKernel S μ μ' s))
    (hasDerivAt_vsPropagator_left hS hμ hμ' hs0 hs1 ht0 ht1)
  rwa [propOp_neg, propOp_mul] at h

/-- Forward form: `∂_t propOp P̂_{s,t} = (propOp A_t) ∘ (propOp P̂_{s,t})`. -/
theorem hasDerivAt_propOp_vsPropagator (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) (s : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (fun r => propOp (vsPropagator S μ μ' s r))
      ((propOp (vsKernel S μ μ' t)).comp (propOp (vsPropagator S μ μ' s t))) t := by
  have h := hasDerivAt_propOp (M' := vsKernel S μ μ' t * vsPropagator S μ μ' s t)
    (hasDerivAt_vsPropagator hS s (norm_smul_lt_one hμ hμ' ht0 ht1))
  rwa [propOp_mul] at h

/-- `propOp P̂_{t,t} = id`. -/
theorem propOp_vsPropagator_self (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    propOp (vsPropagator S μ μ' t t) = ContinuousLinearMap.id ℝ (Fin N → ℂ) := by
  rw [vsPropagator_self hS (norm_smul_lt_one hμ hμ' ht0 ht1), propOp_one]

/-- **Duhamel formula for the propagator** (`duhamel_det` with `U(s,t) = propOp P̂_{s,t}`,
`L_s = propOp A_s`): for `t₀, t ∈ [0,1]`, if `X' = A_s X + F_s` on `[t₀,t]` then
`X_t = P̂_{t₀,t} X_{t₀} + ∫_{t₀}^t P̂_{s,t} F_s ds`.
-/
theorem vsPropagator_duhamel (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) {t₀ t : ℝ} (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {X F : ℝ → Fin N → ℂ}
    (hX : ∀ s ∈ uIcc t₀ t, HasDerivAt X (propOp (vsKernel S μ μ' s) (X s) + F s) s)
    (hint : IntervalIntegrable (fun s => propOp (vsPropagator S μ μ' s t) (F s)) volume t₀ t) :
    X t = propOp (vsPropagator S μ μ' t₀ t) (X t₀) +
      ∫ s in t₀..t, propOp (vsPropagator S μ μ' s t) (F s) := by
  refine propOp_duhamel (U := vsPropagator S μ μ') (L := vsKernel S μ μ')
    (fun s hs a b => ?_) (vsPropagator_self hS (norm_smul_lt_one hμ hμ' ht0 ht1)) hX hint
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    rcases le_total t₀ t with h | h
    · rw [uIcc_of_le h] at hs
      exact ⟨ht₀0.trans hs.1, hs.2.trans ht1⟩
    · rw [uIcc_of_ge h] at hs
      exact ⟨ht0.trans hs.1, hs.2.trans ht₀1⟩
  exact hasDerivAt_vsPropagator_left hS hμ hμ' hs.1 hs.2 ht0 ht1 a b

end One

/-!
## Tensor propagators on functions of `k` sites
-/

section Tensor

variable {k N : ℕ}

/-- `(⊗_j M_j)_{xy} = Π_j (M_j)_{x_j y_j}` on multi-indices `x, y : Fin k → Fin N`. -/
def tensorMat (M : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  fun x y => ∏ j, M j (x j) (y j)

theorem tensorMat_mul (M B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    tensorMat (fun j => M j * B j) = tensorMat M * tensorMat B := by
  ext x y
  simp only [tensorMat, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib

theorem tensorMat_one : tensorMat (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) =
    (1 : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) := by
  ext x y
  simp only [tensorMat, Matrix.one_apply]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

private theorem tensorMat_update_entry (M : Fin k → Matrix (Fin N) (Fin N) ℂ) (i : Fin k)
    (X : Matrix (Fin N) (Fin N) ℂ) (x y : Fin k → Fin N) :
    tensorMat (Function.update M i X) x y =
      X (x i) (y i) * ∏ j ∈ Finset.univ \ {i}, M j (x j) (y j) := by
  simp only [tensorMat]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by simpa using hj
  rw [Function.update_of_ne hji]

theorem tensorMat_update_neg (M : Fin k → Matrix (Fin N) (Fin N) ℂ) (i : Fin k)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    tensorMat (Function.update M i (-X)) = -tensorMat (Function.update M i X) := by
  ext x y
  rw [Matrix.neg_apply, tensorMat_update_entry, tensorMat_update_entry, Matrix.neg_apply,
    neg_mul]

theorem tensorMat_update_mul_right (M : Fin k → Matrix (Fin N) (Fin N) ℂ) (i : Fin k)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    tensorMat (Function.update M i (M i * B)) =
      tensorMat M * tensorMat (Function.update (fun _ => 1) i B) := by
  rw [← tensorMat_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem tensorMat_update_mul_left (M : Fin k → Matrix (Fin N) (Fin N) ℂ) (i : Fin k)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    tensorMat (Function.update M i (B * M i)) =
      tensorMat (Function.update (fun _ => 1) i B) * tensorMat M := by
  rw [← tensorMat_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- **Product rule** for the tensor product: if each factor `M_j(r)` has entrywise derivative
`M'_j` at `x`, then `⊗_j M_j(r)` has entrywise derivative `Σ_i ⊗_j (M_j(x) with M'_i at i)`. -/
theorem hasDerivAt_tensorMat {M : Fin k → ℝ → Matrix (Fin N) (Fin N) ℂ}
    {M' : Fin k → Matrix (Fin N) (Fin N) ℂ} {x : ℝ}
    (h : ∀ j a b, HasDerivAt (fun r => M j r a b) (M' j a b) x) (a b : Fin k → Fin N) :
    HasDerivAt (fun r => tensorMat (fun j => M j r) a b)
      ((∑ i, tensorMat (Function.update (fun j => M j x) i (M' i))) a b) x := by
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := x)
    (f := fun j r => M j r (a j) (b j)) (f' := fun j => M' j (a j) (b j))
    (fun j _ => h j (a j) (b j))
  rw [Matrix.sum_apply]
  refine hp.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  rw [tensorMat_update_entry, smul_eq_mul, mul_comm, Finset.sdiff_singleton_eq_erase]

/-- The `k`-site generator `⊕_i A_i(s) = Σ_i I⊗…⊗A_i(s)⊗…⊗I`, `A_i = vsKernel S (μ i) (μ' i)`. -/
def vsTensorGen (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : Fin k → ℂ) (s : ℝ) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  ∑ i, tensorMat (Function.update (fun _ => 1) i (vsKernel S (μ i) (μ' i) s))

/-- The `k`-site propagator `⊗_j P̂_j(s,t)`, `P̂_j = vsPropagator S (μ j) (μ' j)`. -/
def vsTensorProp (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : Fin k → ℂ) (s t : ℝ) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  tensorMat (fun j => vsPropagator S (μ j) (μ' j) s t)

/-- Entries of a one-slot tensor: `(I⊗…⊗A⊗…⊗I)_{xy} = A_{x_i y_i}` if `y = x[i ↦ y_i]`,
else `0`. -/
theorem tensorMat_update_one_apply (i : Fin k) (A : Matrix (Fin N) (Fin N) ℂ)
    (x y : Fin k → Fin N) :
    tensorMat (Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) i A) x y =
      if y = Function.update x i (y i) then A (x i) (y i) else 0 := by
  rw [tensorMat_update_entry]
  split_ifs with h
  · have hrest : ∏ j ∈ Finset.univ \ {i},
        (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) j (x j) (y j) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hji : j ≠ i := by simpa using hj
      have : y j = x j := by rw [h, Function.update_of_ne hji]
      show (1 : Matrix (Fin N) (Fin N) ℂ) (x j) (y j) = 1
      rw [this, Matrix.one_apply_eq]
    rw [hrest, mul_one]
  · have : ∃ j, j ≠ i ∧ y j ≠ x j := by
      by_contra hc
      push Not at hc
      exact h (Function.eq_update_iff.mpr ⟨rfl, hc⟩)
    obtain ⟨j, hji, hj⟩ := this
    have hmem : j ∈ Finset.univ \ {i} := by simpa using hji
    have hxy : x j ≠ y j := fun e => hj e.symm
    have hz : (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) j (x j) (y j) = 0 :=
      Matrix.one_apply_ne hxy
    rw [Finset.prod_eq_zero hmem hz, mul_zero]

/-- **Action of the generator** on a function of `k` sites:
`(⊕_i A_i)[f](x) = Σ_i Σ_c (A_i)_{x_i c} f(x[i ↦ c])`. -/
theorem propOp_vsTensorGen_apply (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : Fin k → ℂ) (s : ℝ)
    (f : (Fin k → Fin N) → ℂ) (x : Fin k → Fin N) :
    propOp (vsTensorGen S μ μ' s) f x =
      ∑ i, ∑ c, vsKernel S (μ i) (μ' i) s (x i) c * f (Function.update x i c) := by
  rw [vsTensorGen, propOp_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [propOp_apply]
  simp_rw [tensorMat_update_one_apply, ite_mul, zero_mul]
  have hinj : Set.InjOn (fun c : Fin N => Function.update x i c) (Finset.univ : Finset (Fin N)) :=
    fun c _ c' _ hcc => by simpa using congrFun hcc i
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun y : Fin k → Fin N => y = Function.update x i (y i)) =
      Finset.univ.image (fun c : Fin N => Function.update x i c) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      exact ⟨y i, hy.symm⟩
    · rintro ⟨c, rfl⟩
      simp
  rw [hfil, Finset.sum_image hinj]
  simp

/-- `U(t,t) = I` for the tensor propagator. -/
theorem vsTensorProp_self {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : vsTensorProp S μ μ' t t = 1 := by
  rw [vsTensorProp]
  simp_rw [vsPropagator_self hS (norm_smul_lt_one (hμ _) (hμ' _) ht0 ht1)]
  exact tensorMat_one

/-- Entrywise backward derivative `∂_s U(s,t) = -U(s,t) (⊕_j A_j(s))`. -/
theorem hasDerivAt_vsTensorProp_left {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a b : Fin k → Fin N) :
    HasDerivAt (fun r => vsTensorProp S μ μ' r t a b)
      ((-(vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s)) a b) s := by
  have h := hasDerivAt_tensorMat (M := fun j r => vsPropagator S (μ j) (μ' j) r t)
    (M' := fun j => -(vsPropagator S (μ j) (μ' j) s t * vsKernel S (μ j) (μ' j) s))
    (fun j a b => hasDerivAt_vsPropagator_left hS (hμ j) (hμ' j) hs0 hs1 ht0 ht1 a b) a b
  refine h.congr_deriv ?_
  have he : (∑ i, tensorMat (Function.update
      (fun j => vsPropagator S (μ j) (μ' j) s t) i
      (-(vsPropagator S (μ i) (μ' i) s t * vsKernel S (μ i) (μ' i) s)))) =
      -(vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s) := by
    rw [vsTensorGen, Matrix.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensorMat_update_neg, tensorMat_update_mul_right]
    rfl
  rw [he]

/-- **Backward derivative of the `k`-site propagator** (operator-valued),
`∂_s propOp U(s,t) = -(propOp U(s,t)) ∘ (propOp ⊕_j A_j(s))`, `U = ⊗_j P̂_j`, for
`|μ j|, |μ' j| < 1`, `s, t ∈ [0,1]`.
-/
theorem hasDerivAt_propOp_vsTensorProp_left {S : Matrix (Fin N) (Fin N) ℝ}
    (hS : StochasticSymm S) {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (fun r => propOp (vsTensorProp S μ μ' r t))
      (-((propOp (vsTensorProp S μ μ' s t)).comp (propOp (vsTensorGen S μ μ' s)))) s := by
  have h := hasDerivAt_propOp (M' := -(vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s))
    (hasDerivAt_vsTensorProp_left hS hμ hμ' hs0 hs1 ht0 ht1)
  rwa [propOp_neg, propOp_mul] at h

/-- **Forward derivative of the `k`-site propagator**:
`∂_t propOp U(s,t) = (propOp ⊕_j A_j(t)) ∘ (propOp U(s,t))`.
-/
theorem hasDerivAt_propOp_vsTensorProp {S : Matrix (Fin N) (Fin N) ℝ}
    (hS : StochasticSymm S) {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1)
    (s : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasDerivAt (fun r => propOp (vsTensorProp S μ μ' s r))
      ((propOp (vsTensorGen S μ μ' t)).comp (propOp (vsTensorProp S μ μ' s t))) t := by
  have h := hasDerivAt_tensorMat (M := fun j r => vsPropagator S (μ j) (μ' j) s r)
    (M' := fun j => vsKernel S (μ j) (μ' j) t * vsPropagator S (μ j) (μ' j) s t)
    (fun j a b => hasDerivAt_vsPropagator hS s (norm_smul_lt_one (hμ j) (hμ' j) ht0 ht1) a b)
  have h2 := hasDerivAt_propOp (M' := ∑ i, tensorMat (Function.update
    (fun j => vsPropagator S (μ j) (μ' j) s t) i
    (vsKernel S (μ i) (μ' i) t * vsPropagator S (μ i) (μ' i) s t))) h
  have he : (∑ i, tensorMat (Function.update (fun j => vsPropagator S (μ j) (μ' j) s t) i
      (vsKernel S (μ i) (μ' i) t * vsPropagator S (μ i) (μ' i) s t))) =
      vsTensorGen S μ μ' t * vsTensorProp S μ μ' s t := by
    rw [vsTensorGen, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact tensorMat_update_mul_left (fun j => vsPropagator S (μ j) (μ' j) s t) i _
  rw [he, propOp_mul] at h2
  exact h2

/-- **Duhamel formula for the `k`-site propagator** (`duhamel_det` with
`U(s,t) = propOp ⊗_j P̂_j(s,t)`, `L_s = propOp ⊕_j A_j(s)`), `t₀, t ∈ [0,1]`.
-/
theorem vsTensorProp_duhamel {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {t₀ t : ℝ}
    (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {X F : ℝ → (Fin k → Fin N) → ℂ}
    (hX : ∀ s ∈ uIcc t₀ t, HasDerivAt X (propOp (vsTensorGen S μ μ' s) (X s) + F s) s)
    (hint : IntervalIntegrable (fun s => propOp (vsTensorProp S μ μ' s t) (F s)) volume t₀ t) :
    X t = propOp (vsTensorProp S μ μ' t₀ t) (X t₀) +
      ∫ s in t₀..t, propOp (vsTensorProp S μ μ' s t) (F s) := by
  refine propOp_duhamel (U := vsTensorProp S μ μ') (L := vsTensorGen S μ μ')
    (fun s hs a b => ?_) (vsTensorProp_self hS hμ hμ' ht0 ht1) hX hint
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    rcases le_total t₀ t with h | h
    · rw [uIcc_of_le h] at hs
      exact ⟨ht₀0.trans hs.1, hs.2.trans ht1⟩
    · rw [uIcc_of_ge h] at hs
      exact ⟨ht0.trans hs.1, hs.2.trans ht₀1⟩
  exact hasDerivAt_vsTensorProp_left hS hμ hμ' hs.1 hs.2 ht0 ht1 a b

end Tensor

end BlockBand.Native.ErdosRiabov.Propagator
