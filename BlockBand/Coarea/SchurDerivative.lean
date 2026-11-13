module

public import Mathlib

/-!
# Physical Schur derivative at every nonpole energy

The exterior and retained index types are arbitrary finite types. The real
energy is outside the exterior spectrum; the exterior matrix is Hermitian.
`F(E)=V-Cᴴ(H_R-E)⁻¹C`, `T(E)=(H_R-E)⁻¹C`, `D(E)=I+TᴴT` preserve
exact signs and constants. The derivative is over real scalars on finite
complex matrices with their standard matrix norm. There is no measure,
asymptotic limit, uniform estimate, or Gaussian hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace BlockBand.Coarea

open Matrix Filter Topology

/-- Totalized exterior resolvent; off poles this is the ordinary inverse. -/
def physicalCoareaResolvent {α : Type*} [Fintype α] [DecidableEq α]
    (H_R : Matrix α α ℂ) (E : ℝ) : Matrix α α ℂ :=
  (H_R - (E : ℂ) • 1)⁻¹

/-- Exterior-to-retained Schur transfer with the `(H_R-E)⁻¹` sign. -/
def physicalCoareaT {α β : Type*} [Fintype α] [DecidableEq α]
    (H_R : Matrix α α ℂ) (C : Matrix α β ℂ) (E : ℝ) : Matrix α β ℂ :=
  physicalCoareaResolvent H_R E * C

/-- Retained compression with its exact energy dependence. -/
def physicalCoareaF {α β : Type*} [Fintype α] [DecidableEq α]
    (H_R : Matrix α α ℂ) (C : Matrix α β ℂ) (V : Matrix β β ℂ)
    (E : ℝ) : Matrix β β ℂ :=
  V - Cᴴ * physicalCoareaResolvent H_R E * C

/-- Positive Schur clock; the identity contribution has coefficient one. -/
def schurClock {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (T : Matrix α β ℂ) : Matrix β β ℂ := 1 + Tᴴ * T

/-- Energy-dependent clock for the exterior Schur transfer. -/
def physicalCoareaD {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H_R : Matrix α α ℂ)
    (C : Matrix α β ℂ) (E : ℝ) : Matrix β β ℂ :=
  schurClock (physicalCoareaT H_R C E)

/-- Resolvent identity: `R(s) - R(E) = (s - E) R(s) R(E)` off the poles. -/
theorem physicalCoareaResolvent_sub {α : Type*} [Fintype α] [DecidableEq α] (H_R : Matrix (α) (α) ℂ) (s E : ℝ)
    (hs : (H_R - (s : ℂ) • 1).det ≠ 0) (hE : (H_R - (E : ℂ) • 1).det ≠ 0) :
    physicalCoareaResolvent H_R s - physicalCoareaResolvent H_R E =
      ((s : ℂ) - E) • (physicalCoareaResolvent H_R s * physicalCoareaResolvent H_R E) := by
  unfold physicalCoareaResolvent
  set A := H_R - (s : ℂ) • 1
  set B := H_R - (E : ℂ) • 1
  have h1 : A⁻¹ * A = 1 := nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hs)
  have h2 : B * B⁻¹ = 1 := mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hE)
  have hBA : B - A = ((s : ℂ) - E) • 1 := by
    simp only [A, B, sub_smul]; abel
  have : A⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, h1, Matrix.mul_one, Matrix.one_mul]
  rw [← this, hBA]
  simp

/-- The physical compression `F(E) = V - Cᴴ (H_R - E)⁻¹ C` has energy
derivative `-T(E)ᴴ T(E)` off the exterior poles (`H_R` Hermitian). -/
theorem hasDerivAt_physicalCoareaF {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (H_R : Matrix (α) (α) ℂ) (hH : H_R.IsHermitian)
    (C : Matrix (α) (β) ℂ)
    (V : Matrix (β) (β) ℂ)
    (E : ℝ) (hE : (H_R - (E : ℂ) • 1).det ≠ 0) :
    HasDerivAt (physicalCoareaF H_R C V)
      (-((physicalCoareaT H_R C E)ᴴ * physicalCoareaT H_R C E)) E := by
  set R := physicalCoareaResolvent H_R
  have hdetc : Continuous fun s : ℝ => (H_R - (s:ℂ) • 1).det := by fun_prop
  have hev : ∀ᶠ s : ℝ in 𝓝 E, (H_R - (s:ℂ) • 1).det ≠ 0 :=
    hdetc.continuousAt.eventually_ne hE
  have hRc : ContinuousAt R E := by
    have h1 : ContinuousAt (Inv.inv : Matrix (α) (α) ℂ → _) (H_R - (E:ℂ) • 1) := by
      apply continuousAt_matrix_inv
      exact NormedRing.inverse_continuousAt (Units.mk0 _ hE)
    exact h1.comp (f := fun s : ℝ => H_R - (s:ℂ) • 1) (by fun_prop)
  have hlim : Tendsto (fun s => -(Cᴴ * (R s * R E) * C)) (𝓝[≠] E)
      (𝓝 (-(Cᴴ * (R E * R E) * C))) := by
    have : ContinuousAt (fun s => -(Cᴴ * (R s * R E) * C)) E := by
      have hc : Continuous fun M : Matrix (α) (α) ℂ => -(Cᴴ * (M * R E) * C) := by
        fun_prop
      exact hc.continuousAt.comp hRc
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hT : (physicalCoareaT H_R C E)ᴴ * physicalCoareaT H_R C E = Cᴴ * (R E * R E) * C := by
    have hRh : (R E)ᴴ = R E := by
      simp only [R, physicalCoareaResolvent, conjTranspose_nonsing_inv]
      congr 1
      rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
      simp
    change (R E * C)ᴴ * (R E * C) = _
    rw [conjTranspose_mul, hRh]
    simp only [Matrix.mul_assoc]
  rw [hT]
  let _ : NormedAddCommGroup (Matrix (β) (β) ℂ) :=
    Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix (β) (β) ℂ) :=
    Matrix.normedSpace
  refine hasDerivAt_iff_tendsto_slope.mpr ?_
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with s hs hdet
  have hsE : (s : ℂ) - E ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hs
  rw [slope_def_module]
  simp only [physicalCoareaF]
  have hsub : R s - R E = ((s : ℂ) - E) • (R s * R E) :=
    physicalCoareaResolvent_sub H_R s E hdet hE
  have : V - Cᴴ * R s * C - (V - Cᴴ * R E * C) = -(Cᴴ * (R s - R E) * C) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [this, hsub]
  ext i j
  simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- The moving Schur pencil is `F(E)+G-EI`, with `G` fixed. -/
def physicalCoareaA {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (H_R : Matrix α α ℂ) (C : Matrix α β ℂ)
    (V G : Matrix β β ℂ) (E : ℝ) : Matrix β β ℂ :=
  physicalCoareaF H_R C V E + G - (E : ℂ) • 1

/-- The full moving Schur pencil derivative is exactly the negative clock.
This is the finite matrix derivative behind the physical crossing speed. -/
theorem hasDerivAt_physicalCoareaA
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (H_R : Matrix α α ℂ) (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    (V G : Matrix β β ℂ) (E : ℝ)
    (hE : (H_R - (E : ℂ) • 1).det ≠ 0) :
    HasDerivAt (physicalCoareaA H_R C V G) (-physicalCoareaD H_R C E) E := by
  let _ : NormedAddCommGroup (Matrix β β ℂ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix β β ℂ) := Matrix.normedSpace
  have hId : HasDerivAt (fun e : ℝ => (e : ℂ) • (1 : Matrix β β ℂ))
      (1 : Matrix β β ℂ) E := by
    convert (hasDerivAt_id E).smul_const (1 : Matrix β β ℂ) using 1 <;>
      first | rfl | simp
  have h := ((hasDerivAt_physicalCoareaF H_R hH C V E hE).add_const G).sub hId
  have hD : -physicalCoareaD H_R C E =
      -((physicalCoareaT H_R C E)ᴴ * physicalCoareaT H_R C E) - 1 := by
    unfold physicalCoareaD schurClock
    abel
  rw [hD]
  convert h using 1 <;> rfl

end BlockBand.Coarea
