module

public import BlockBand.SourceProcess.Stochastic.Dyson.FirstDeriv
public import BlockBand.SourceProcess.Stochastic.Dyson.OverlapBracket
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Dyson Brownian motion: diagonal second derivatives of eigenvalues and overlaps

For `y ∈ simpleSet N`, `V = H(v)`, `μ_j = λ_j(y)`, `P_j = P_j(y)`:
* `fderiv2_lam`: `D²λ_i(y)[v, v] = Re tr(dP_i[V] V)`;
* `fderiv2_ovl`: `D²X_i(y)[v, v] = N Re q* d²P_i[V] q` with `d²P_i = SpecFamily.d2Proj`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix Filter Topology
open scoped Matrix ContDiff Matrix.Norms.Operator
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- First-variation map at the point `y`. -/
def dProjAt (N : ℕ) (y : Fin (N * N) → ℝ) (i : Fin N) (V : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  SpecFamily.dProj (fun j => proj N j y) (fun j => ((lam N j y : ℝ) : ℂ)) i V

theorem fderiv_proj_eq {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (v : Fin (N * N) → ℝ) : fderiv ℝ (proj N i) y v = dProjAt N y i (vecHerm N v) :=
  (fderiv_lam_proj hy i v).2

theorem fderiv_lam_eq {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (v : Fin (N * N) → ℝ) :
    fderiv ℝ (lam N i) y v = (trace (proj N i y * vecHerm N v)).re := by
  rw [← (fderiv_lam_proj hy i v).1, Complex.ofReal_re]

/-- The real-linear functional `M ↦ Re tr(M W)` as a continuous linear map. -/
def reTraceMul (W : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (trace (M * W)).re
      map_add' := fun A B => by simp [Matrix.add_mul, trace_add]
      map_smul' := fun c A => by
        simp [trace_smul, Complex.real_smul] }

theorem reTraceMul_apply (W M : Matrix (Fin N) (Fin N) ℂ) :
    reTraceMul W M = (trace (M * W)).re := rfl

/-- The real-linear functional `M ↦ N Re q* M q`. -/
def overlapForm (N : ℕ) (q : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (N : ℝ) * (qf q M).re
      map_add' := fun A B => by simp [qf_add, mul_add]
      map_smul' := fun c A => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [show c • A = (c : ℂ) • A from (Complex.coe_smul c A).symm, qf_smul,
          Complex.re_ofReal_mul]
        ring }

theorem overlapForm_apply (q : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    overlapForm N q M = (N : ℝ) * (qf q M).re := rfl

/-- `fderiv (fderiv f) y v v = fderiv (y' ↦ fderiv f y' v) y v`. -/
theorem fderiv_fderiv_apply_diag {f : (Fin (N * N) → ℝ) → ℝ} {y : Fin (N * N) → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (v : Fin (N * N) → ℝ) :
    fderiv ℝ (fderiv ℝ f) y v v = fderiv ℝ (fun y' => fderiv ℝ f y' v) y v := by
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

/-- **Second variation of eigenvalues** (diagonal): `D²λ_i[v,v] = Re tr(dP_i[V] V)`. -/
theorem fderiv2_lam {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (v : Fin (N * N) → ℝ) :
    fderiv ℝ (fderiv ℝ (lam N i)) y v v =
      (trace (dProjAt N y i (vecHerm N v) * vecHerm N v)).re := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (lam N i)) y :=
    ((contDiffAt_eigenvalue (n := 2) hy i).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  rw [fderiv_fderiv_apply_diag hd]
  have hev : (fun y' => fderiv ℝ (lam N i) y' v) =ᶠ[𝓝 y]
      fun y' => reTraceMul (vecHerm N v) (proj N i y') := by
    filter_upwards [eventually_simpleSet hy] with y' hy'
    rw [fderiv_lam_eq hy' i v, reTraceMul_apply]
  have hc : HasFDerivAt (fun y' => reTraceMul (vecHerm N v) (proj N i y'))
      ((reTraceMul (vecHerm N v)).comp (fderiv ℝ (proj N i) y)) y :=
    (reTraceMul (vecHerm N v)).hasFDerivAt.comp y (hasFDerivAt_proj hy i)
  rw [hev.fderiv_eq, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, reTraceMul_apply, fderiv_proj_eq hy i v]

/-- Inverse eigenvalue gap in coordinates. -/
def invGap (N : ℕ) (i j : Fin N) (y : Fin (N * N) → ℝ) : ℝ := (lam N i y - lam N j y)⁻¹

theorem hasFDerivAt_invGap {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) {i j : Fin N}
    (hij : j ≠ i) :
    HasFDerivAt (invGap N i j) ((ContinuousLinearMap.toSpanSingleton ℝ
      (-((lam N i y - lam N j y) ^ 2)⁻¹)).comp
        (fderiv ℝ (lam N i) y - fderiv ℝ (lam N j) y)) y := by
  have hne : lam N i y - lam N j y ≠ 0 := sub_ne_zero.mpr (HasSimpleSpectrum.ne hy hij.symm)
  exact (hasFDerivAt_inv hne).comp y ((hasFDerivAt_lam hy i).sub (hasFDerivAt_lam hy j))

theorem dProjAt_eq (y : Fin (N * N) → ℝ) (i : Fin N) (W : Matrix (Fin N) (Fin N) ℂ) :
    dProjAt N y i W = ∑ j ∈ Finset.univ.erase i, ((invGap N i j y : ℝ) : ℂ) •
      (proj N j y * W * proj N i y + proj N i y * W * proj N j y) := by
  unfold dProjAt SpecFamily.dProj invGap
  push_cast; rfl

/-- Derivative of one term of `dProjAt`. -/
theorem fderiv_dProj_term {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) {i j : Fin N}
    (hij : j ≠ i) (W : Matrix (Fin N) (Fin N) ℂ) (v : Fin (N * N) → ℝ) :
    HasFDerivAt (fun y' => ((invGap N i j y' : ℝ) : ℂ) •
      (proj N j y' * W * proj N i y' + proj N i y' * W * proj N j y'))
      (fderiv ℝ (fun y' => ((invGap N i j y' : ℝ) : ℂ) •
        (proj N j y' * W * proj N i y' + proj N i y' * W * proj N j y')) y) y ∧
    fderiv ℝ (fun y' => ((invGap N i j y' : ℝ) : ℂ) •
        (proj N j y' * W * proj N i y' + proj N i y' * W * proj N j y')) y v =
      ((invGap N i j y : ℝ) : ℂ) •
        (fderiv ℝ (proj N j) y v * W * proj N i y + proj N j y * W * fderiv ℝ (proj N i) y v +
          (fderiv ℝ (proj N i) y v * W * proj N j y + proj N i y * W * fderiv ℝ (proj N j) y v)) +
      ((((fderiv ℝ (lam N i) y v - fderiv ℝ (lam N j) y v) *
        (-((lam N i y - lam N j y) ^ 2)⁻¹) : ℝ)) : ℂ) •
        (proj N j y * W * proj N i y + proj N i y * W * proj N j y) := by
  have hPi := hasFDerivAt_proj hy i
  have hPj := hasFDerivAt_proj hy j
  have hW := hasFDerivAt_const (𝕜 := ℝ) W y
  have hc := Complex.ofRealCLM.hasFDerivAt.comp y (hasFDerivAt_invGap hy hij)
  have h0 := hc.fun_smul ((((hPj.fun_mul' hW).fun_mul' hPi)).add ((hPi.fun_mul' hW).fun_mul' hPj))
  have h : HasFDerivAt (fun y' => ((invGap N i j y' : ℝ) : ℂ) •
      (proj N j y' * W * proj N i y' + proj N i y' * W * proj N j y')) _ y := h0
  refine ⟨h.differentiableAt.hasFDerivAt, ?_⟩
  rw [h.fderiv]
  change ((invGap N i j y : ℝ) : ℂ) • ((proj N j y * W * fderiv ℝ (proj N i) y v +
      (proj N j y * 0 + fderiv ℝ (proj N j) y v * W) * proj N i y) +
      (proj N i y * W * fderiv ℝ (proj N j) y v +
      (proj N i y * 0 + fderiv ℝ (proj N i) y v * W) * proj N j y)) +
    (((fderiv ℝ (lam N i) y v - fderiv ℝ (lam N j) y v) *
      (-((lam N i y - lam N j y) ^ 2)⁻¹) : ℝ) : ℂ) •
      (proj N j y * W * proj N i y + proj N i y * W * proj N j y) = _
  simp only [Matrix.mul_zero, zero_add]
  congr 2
  abel

theorem hasFDerivAt_dProjAt {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (W : Matrix (Fin N) (Fin N) ℂ) :
    HasFDerivAt (fun y' => dProjAt N y' i W) (∑ j ∈ Finset.univ.erase i,
      fderiv ℝ (fun y' => ((invGap N i j y' : ℝ) : ℂ) •
        (proj N j y' * W * proj N i y' + proj N i y' * W * proj N j y')) y) y := by
  simp_rw [dProjAt_eq]
  exact HasFDerivAt.fun_sum fun j hj => (fderiv_dProj_term hy (Finset.ne_of_mem_erase hj) W 0).1

/-- The diagonal second variation of `P_i` along `V = H(v)`. -/
theorem fderiv_dProjAt_self {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (v : Fin (N * N) → ℝ) :
    fderiv ℝ (fun y' => dProjAt N y' i (vecHerm N v)) y v =
      SpecFamily.d2Proj (fun j => proj N j y) (fun j => ((lam N j y : ℝ) : ℂ)) i (vecHerm N v) := by
  rw [(hasFDerivAt_dProjAt hy i (vecHerm N v)).fderiv, _root_.sum_apply]
  unfold SpecFamily.d2Proj
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [(fderiv_dProj_term hy hji (vecHerm N v) v).2, fderiv_proj_eq hy i, fderiv_proj_eq hy j]
  have hLi := (fderiv_lam_proj hy i v).1
  have hLj := (fderiv_lam_proj hy j v).1
  have e1 : ((invGap N i j y : ℝ) : ℂ) = (((lam N i y : ℝ) : ℂ) - ((lam N j y : ℝ) : ℂ))⁻¹ := by
    unfold invGap; push_cast; rfl
  have e2 : ((((fderiv ℝ (lam N i) y v - fderiv ℝ (lam N j) y v) *
      (-((lam N i y - lam N j y) ^ 2)⁻¹) : ℝ)) : ℂ) =
      -((((lam N i y : ℝ) : ℂ) - ((lam N j y : ℝ) : ℂ))⁻¹ ^ 2 *
        (trace (proj N i y * vecHerm N v) - trace (proj N j y * vecHerm N v))) := by
    rw [← hLi, ← hLj]; push_cast; rw [inv_pow]; ring
  rw [e1, e2, neg_smul, ← sub_eq_add_neg]
  unfold dProjAt
  congr 1
  rw [add_assoc (_ + _)]

/-- The overlap in coordinates, `X_i(y) = N Re q* P_i(y) q`. -/
def ovl (N : ℕ) (q : Fin N → ℂ) (i : Fin N) (y : Fin (N * N) → ℝ) : ℝ :=
  dysonOverlap N q (vecHerm N y) i

theorem ovl_eq (q : Fin N → ℂ) (i : Fin N) :
    ovl N q i = fun y => overlapForm N q (proj N i y) := rfl

theorem contDiffAt_ovl {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (q : Fin N → ℂ) (i : Fin N) : ContDiffAt ℝ n (ovl N q i) y := by
  rw [ovl_eq]
  exact (overlapForm N q).contDiff.contDiffAt.comp y (contDiffAt_proj hy i)

theorem fderiv_ovl_eq {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ) (i : Fin N)
    (v : Fin (N * N) → ℝ) :
    fderiv ℝ (ovl N q i) y v = overlapForm N q (dProjAt N y i (vecHerm N v)) := by
  have hc := (overlapForm N q).hasFDerivAt.comp y (hasFDerivAt_proj hy i)
  rw [ovl_eq, show (fun y => overlapForm N q (proj N i y)) = (overlapForm N q) ∘ proj N i from rfl,
    hc.fderiv, ← fderiv_proj_eq hy i]
  rfl

/-- **Second variation of overlaps** (diagonal): `D²X_i[v,v] = N Re q* d²P_i[V] q`. -/
theorem fderiv2_ovl {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ) (i : Fin N)
    (v : Fin (N * N) → ℝ) :
    fderiv ℝ (fderiv ℝ (ovl N q i)) y v v = overlapForm N q
      (SpecFamily.d2Proj (fun j => proj N j y) (fun j => ((lam N j y : ℝ) : ℂ)) i (vecHerm N v)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (ovl N q i)) y :=
    ((contDiffAt_ovl (n := 2) hy q i).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  rw [fderiv_fderiv_apply_diag hd]
  have hev : (fun y' => fderiv ℝ (ovl N q i) y' v) =ᶠ[𝓝 y]
      fun y' => overlapForm N q (dProjAt N y' i (vecHerm N v)) := by
    filter_upwards [eventually_simpleSet hy] with y' hy'
    exact fderiv_ovl_eq hy' q i v
  have hc := (overlapForm N q).hasFDerivAt.comp y (hasFDerivAt_dProjAt hy i (vecHerm N v))
  rw [hev.fderiv_eq]
  change fderiv ℝ ((overlapForm N q) ∘ fun y' => dProjAt N y' i (vecHerm N v)) y v = _
  have key := fderiv_dProjAt_self hy i v
  rw [(hasFDerivAt_dProjAt hy i (vecHerm N v)).fderiv] at key
  rw [hc.fderiv, ← key]
  rfl

end BlockBand.SourceProcess.Stochastic.Dyson
