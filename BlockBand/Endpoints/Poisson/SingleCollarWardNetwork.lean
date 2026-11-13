module

public import BlockBand.Endpoints.Poisson.SingleCollarStage
public import BlockBand.Endpoints.Poisson.SingleCollarWardCore

/-!
# The old network of one stage as an absorbing network with complete ports

* Sites: the old interior `OldSite` (non-deleted sites outside collar `k`) and the two outer
  coordinates of collar `k`. Ports `ScwPorts = (Fin 2 × Fin W) ⊕ ScwMatched`: the collar ports and
  the matched sites (outer blocks of removed collars, diagonal `z_b`); interior `ScwInner`: the
  unmatched old sites. `scwEquiv` reorders `OldSite ⊕ (Fin 2 × Fin W)`.
* `scwFull t ω`: `collarAfter M_t C Cᴴ z_b` (the old network `[[M_t, C], [Cᴴ, z_b]]`) in the
  port/interior order. `scw_full_eq`: it is `scwNet H η (t/W²) D` with the Hermitian part
  `scwHerm` (Hermitian for Hermitian diagonal samples, `scw_herm_isHermitian`), `η = Im z_b`, and
  the source projection `D = 1_C` (`scwSrc`).
* `scw_isUnit_full`, `scw_scat_block`: if `M_t` and `z_b - X_t` are invertible, so is `scwFull t`,
  and the collar block of its complete scattering matrix is `oldScattering b e X_t`, the `r_t` of
  `scsResponse`.
* `scw_measurable_full`: measurability.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace)
open BlockBand.Internal.Contracts.Layers (boundaryZ)
open BlockBand.Internal.Contracts.Critical (oldScattering)
open scoped ComplexOrder

open Classical

section Network

variable {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (s : ZMod n) (π : Pairing) (S : Finset (Fin m))
  (k : Fin m)

/-- The matched old sites (outer blocks of removed collars): input ports of the old network. -/
abbrev ScwMatched : Type := {x : OldSite L s S k W // IsMatched L s S x.1.1}

/-- The unmatched old sites: the interior of the old network. -/
abbrev ScwInner : Type := {x : OldSite L s S k W // ¬ IsMatched L s S x.1.1}

/-- All input ports: the collar ports and the matched sites. -/
abbrev ScwPorts : Type := (Fin 2 × Fin W) ⊕ ScwMatched (W := W) L s S k

instance scw_instFintypeMatched : Fintype (ScwMatched (W := W) L s S k) := Subtype.fintype _

instance scw_instFintypeInner : Fintype (ScwInner (W := W) L s S k) := Subtype.fintype _

instance scw_instDecEqMatched : DecidableEq (ScwMatched (W := W) L s S k) :=
  Subtype.instDecidableEq

instance scw_instDecEqInner : DecidableEq (ScwInner (W := W) L s S k) := Subtype.instDecidableEq

instance scw_instFintypePorts : Fintype (ScwPorts (W := W) L s S k) := instFintypeSum _ _

instance scw_instDecEqPorts : DecidableEq (ScwPorts (W := W) L s S k) := instDecidableEqSum

/-- Reordering of the old network's sites into ports and interior. -/
def scwEquiv : ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k ≃
    OldSite L s S k W ⊕ (Fin 2 × Fin W) :=
  (Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _)
    (Equiv.sumCompl fun x : OldSite L s S k W => IsMatched L s S x.1.1)).trans (Equiv.sumComm _ _))

/-- The source projection `D = 1_C` on the interior. -/
def scwSrc (buf : ℕ) : Matrix (ScwInner (W := W) L s S k) (ScwInner (W := W) L s S k) ℂ :=
  diagonal fun u => if InSource L s buf u.1.1.1 then 1 else 0

/-- The old network with its collar ports, `[[M_t, C], [Cᴴ, z_b]]`, in port/interior order. -/
def scwFull (b e : ℝ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W) :
    Matrix (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k)
      (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k) ℂ :=
  (collarAfter (oldInterior L s π S k e (boundaryZ b e) buf t ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf t ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf t ω)ᴴ (boundaryZ b e)).submatrix
      (scwEquiv L s S k) (scwEquiv L s S k)

/-- The Hermitian part of the old network. -/
def scwHerm (b e : ℝ) (buf : ℕ) (ω : RingCoords n W) :
    Matrix (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k)
      (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k) ℂ :=
  (fromBlocks ((stageHerm L s π S e (boundaryZ b e).re ω).submatrix Subtype.val Subtype.val)
    (oldCoupling L s π S k e (boundaryZ b e) buf 0 ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf 0 ω)ᴴ
    (((boundaryZ b e).re : ℂ) • 1)).submatrix (scwEquiv L s S k) (scwEquiv L s S k)

variable {L s π S k}

omit [NeZero n] in
theorem scw_src_conjTranspose (buf : ℕ) :
    (scwSrc (W := W) L s S k buf)ᴴ = scwSrc (W := W) L s S k buf := by
  simp only [scwSrc, diagonal_conjTranspose]
  congr 1; funext u; by_cases h : InSource L s buf u.1.1.1 <;> simp [h]

theorem scw_src_mul_self (buf : ℕ) :
    scwSrc (W := W) L s S k buf * scwSrc (W := W) L s S k buf = scwSrc (W := W) L s S k buf := by
  simp only [scwSrc, diagonal_mul_diagonal]
  congr 1; funext u; by_cases h : InSource L s buf u.1.1.1 <;> simp [h]

omit [NeZero n] in
theorem scw_herm_isHermitian (b e : ℝ) (buf : ℕ) {ω : RingCoords n W}
    (hA : ∀ p, (ω.1 p).IsHermitian) : (scwHerm L s π S k b e buf ω).IsHermitian := by
  refine IsHermitian.submatrix ?_ _
  refine IsHermitian.fromBlocks ((stageHerm_isHermitian π S e _ ω hA).submatrix _) rfl ?_
  simp [IsHermitian, conjTranspose_smul]

omit [NeZero n] in
theorem scw_oldCoupling_eq (e : ℝ) (z : ℂ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W) :
    oldCoupling L s π S k e z buf t ω = oldCoupling L s π S k e z buf 0 ω := by
  ext x c
  have hne : x.1 ≠ outerSite L s k c := fun h => x.2.2 (h ▸ outerPos_inCollar k c.1)
  simp only [oldCoupling, stageFull, submatrix_apply, Matrix.add_apply, diagonal_apply, hne,
    ite_false]

omit [NeZero n] in
theorem scw_oldInterior_eq (e : ℝ) (z : ℂ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W) :
    oldInterior L s π S k e z buf t ω =
      (stageHerm L s π S e z.re ω).submatrix Subtype.val Subtype.val +
        diagonal fun x : OldSite L s S k W =>
          ((stageAbsorption L s S buf t z.im W x.1.1 : ℝ) : ℂ) * Complex.I := by
  ext x y
  simp only [oldInterior, stageFull, submatrix_apply, Matrix.add_apply, diagonal_apply,
    Subtype.ext_iff]

omit [NeZero n] in
theorem scw_abs_submatrix (b e : ℝ) (buf : ℕ) (t : ℝ) :
    (Complex.I • scwAbs (boundaryZ b e).im (t / (W : ℝ) ^ 2) (scwSrc (W := W) L s S k buf)).submatrix
        (scwEquiv L s S k).symm (scwEquiv L s S k).symm =
      fromBlocks (diagonal fun x : OldSite L s S k W =>
          ((stageAbsorption L s S buf t (boundaryZ b e).im W x.1.1 : ℝ) : ℂ) * Complex.I) 0 0
        ((((boundaryZ b e).im : ℂ) * Complex.I) • 1) := by
  ext (x | x) (y | y)
  · by_cases hx : IsMatched L s S x.1.1 <;> by_cases hy : IsMatched L s S y.1.1 <;>
      by_cases hxy : x = y <;>
      simp [scwEquiv, scwAbs, scwSrc, stageAbsorption, hx, hy, hxy, Equiv.sumCompl,
        Subtype.ext_iff, mul_comm]
    all_goals (split_ifs <;> simp)
  · by_cases hx : IsMatched L s S x.1.1 <;> simp [scwEquiv, scwAbs, hx, Equiv.sumCompl]
  · by_cases hy : IsMatched L s S y.1.1 <;> simp [scwEquiv, scwAbs, hy, Equiv.sumCompl]
  · by_cases hxy : x = y <;> simp [scwEquiv, scwAbs, hxy, mul_comm]

omit [NeZero n] in
/-- **The old network is an absorbing network**: `scwFull t = scwNet H η (t/W²) D`. -/
theorem scw_full_eq (b e : ℝ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W) :
    scwFull L s π S k b e buf t ω =
      scwNet (scwHerm L s π S k b e buf ω) (boundaryZ b e).im (t / (W : ℝ) ^ 2)
        (scwSrc L s S k buf) := by
  have hinj : ∀ A B : Matrix (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k)
      (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k) ℂ,
      A.submatrix (scwEquiv L s S k).symm (scwEquiv L s S k).symm =
        B.submatrix (scwEquiv L s S k).symm (scwEquiv L s S k).symm → A = B := by
    intro A B h
    have := congrArg (fun M => M.submatrix (scwEquiv L s S k) (scwEquiv L s S k)) h
    simpa [submatrix_submatrix] using this
  apply hinj
  rw [scwNet, show ∀ A B : Matrix (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k)
      (ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k) ℂ,
      (A + B).submatrix (scwEquiv L s S k).symm (scwEquiv L s S k).symm =
        A.submatrix (scwEquiv L s S k).symm (scwEquiv L s S k).symm +
          B.submatrix (scwEquiv L s S k).symm (scwEquiv L s S k).symm from fun _ _ => rfl,
    scw_abs_submatrix]
  simp only [scwFull, scwHerm, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id,
    collarAfter, fromBlocks_add, add_zero]
  rw [scw_oldInterior_eq, scw_oldCoupling_eq]
  congr 1
  conv_lhs => rw [← Complex.re_add_im (boundaryZ b e)]
  rw [add_smul]

theorem scw_isUnit_full (b e : ℝ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W)
    (hM : IsUnit (oldInterior L s π S k e (boundaryZ b e) buf t ω).det)
    (hX : IsUnit (boundaryZ b e • 1 - oldSchur (oldInterior L s π S k e (boundaryZ b e) buf t ω)
      (oldCoupling L s π S k e (boundaryZ b e) buf t ω)
      (oldCoupling L s π S k e (boundaryZ b e) buf t ω)ᴴ).det) :
    IsUnit (scwFull L s π S k b e buf t ω).det := by
  rw [scwFull, det_submatrix_equiv_self, det_collarAfter _ _ _ _ hM]
  exact hM.mul hX

/-- **The collar block of the complete scattering matrix is `r_t`.** -/
theorem scw_scat_block (b e : ℝ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W)
    (hM : IsUnit (oldInterior L s π S k e (boundaryZ b e) buf t ω).det)
    (hX : IsUnit (boundaryZ b e • 1 - oldSchur (oldInterior L s π S k e (boundaryZ b e) buf t ω)
      (oldCoupling L s π S k e (boundaryZ b e) buf t ω)
      (oldCoupling L s π S k e (boundaryZ b e) buf t ω)ᴴ).det) :
    (scwScat (boundaryZ b e).im (scwFull (W := W) L s π S k b e buf t ω)⁻¹).toBlocks₁₁ =
      oldScattering b e (oldSchur (oldInterior L s π S k e (boundaryZ b e) buf t ω)
        (oldCoupling L s π S k e (boundaryZ b e) buf t ω)
        (oldCoupling L s π S k e (boundaryZ b e) buf t ω)ᴴ) := by
  have h22 := inv_fromBlocks_toBlocks₂₂ (oldInterior L s π S k e (boundaryZ b e) buf t ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf t ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf t ω)ᴴ (boundaryZ b e • 1) hM hX
  have hinv : (scwFull (W := W) L s π S k b e buf t ω)⁻¹ =
      (collarAfter (oldInterior L s π S k e (boundaryZ b e) buf t ω)
        (oldCoupling L s π S k e (boundaryZ b e) buf t ω)
        (oldCoupling L s π S k e (boundaryZ b e) buf t ω)ᴴ (boundaryZ b e))⁻¹.submatrix
          (scwEquiv L s S k) (scwEquiv L s S k) := by
    rw [scwFull, inv_submatrix_equiv]
  ext c c'
  have hcc := congrFun (congrFun h22 c) c'
  simp only [collarAfter] at hinv
  simp only [scwScat, oldScattering, toBlocks₁₁, Matrix.sub_apply, Matrix.smul_apply, of_apply,
    hinv, submatrix_apply, Matrix.one_apply, Sum.inl.injEq, oldSchur]
  rw [← hcc]
  rfl

theorem scw_measurable_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun N : Matrix ι ι ℂ => N⁻¹) := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).mul
    ((continuous_apply_apply i j).comp continuous_id.matrix_adjugate).measurable

theorem scw_measurable_full (b e : ℝ) (buf : ℕ) (t : ℝ) :
    Measurable (scwFull (W := W) L s π S k b e buf t) := by
  have h1 := (measurable_oldNetwork L s π S k e (boundaryZ b e) buf t (W := W)).fst
  have h2 := (measurable_oldNetwork L s π S k e (boundaryZ b e) buf t (W := W)).snd
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [scwFull, submatrix_apply, collarAfter]
  generalize scwEquiv L s S k x = x'
  generalize scwEquiv L s S k y = y'
  rcases x' with x' | x' <;> rcases y' with y' | y'
  · exact h1.eval_matrix
  · exact h2.eval_matrix
  · simp only [fromBlocks_apply₂₁, conjTranspose_apply]
    exact continuous_star.measurable.comp h2.eval_matrix
  · exact measurable_const

end Network

end BlockBand.Endpoints
