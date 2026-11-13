module

public import BlockBand.SourceProcess.ContractingWords.SlotCovPre

/-!
# Algebra of the slot covariances

* `int_center_mul`: `E[(a+f)(a'+f')] - aa' = E[ff']` for centered `f, f'`;
* `int_four`: `E[(X+Y)(X'+Y')] = E[XX'] + E[XY'] + E[YX'] + E[YY']`;
* `matrixExpect_projGamma`: `E projGamma = P(ENN*)P - E NPN*`;
* `centered_proj`: `u*(NPN*)⁰v = (Pu)*(NN*)⁰(Pv) - u*(projGamma)⁰v` (exact);
* `bilinear_sub_mat`: `u*(M - M')v = u*Mv - u*M'v`.

The real arithmetic of `slot_cov` is `cov_arith`, proved in a sibling module.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open scoped ENNReal Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem int_center_mul [IsProbabilityMeasure μ] {f f' : Ω → ℂ} (hf : Integrable f μ)
    (hf' : Integrable f' μ) (hff : Integrable (fun ω => f ω * f' ω) μ) (h0 : ∫ ω, f ω ∂μ = 0)
    (h0' : ∫ ω, f' ω ∂μ = 0) (a a' : ℂ) :
    ∫ ω, (a + f ω) * (a' + f' ω) ∂μ - a * a' = ∫ ω, f ω * f' ω ∂μ := by
  have e : ∀ ω, (a + f ω) * (a' + f' ω) = a * a' + a * f' ω + a' * f ω + f ω * f' ω :=
    fun ω => by ring
  simp only [e]
  have i1 : Integrable (fun ω => a * a' + a * f' ω) μ := (integrable_const _).add (hf'.const_mul a)
  have i2 : Integrable (fun ω => a * a' + a * f' ω + a' * f ω) μ := i1.add (hf.const_mul a')
  rw [integral_add i2 hff, integral_add i1 (hf.const_mul a'),
    integral_add (integrable_const _) (hf'.const_mul a)]
  simp [integral_const_mul, h0, h0']

theorem int_four {X Y X' Y' : Ω → ℂ} (h1 : Integrable (fun ω => X ω * X' ω) μ)
    (h2 : Integrable (fun ω => X ω * Y' ω) μ) (h3 : Integrable (fun ω => Y ω * X' ω) μ)
    (h4 : Integrable (fun ω => Y ω * Y' ω) μ) :
    ∫ ω, (X ω + Y ω) * (X' ω + Y' ω) ∂μ = ∫ ω, X ω * X' ω ∂μ + ∫ ω, X ω * Y' ω ∂μ +
      ∫ ω, Y ω * X' ω ∂μ + ∫ ω, Y ω * Y' ω ∂μ := by
  have e : ∀ ω, (X ω + Y ω) * (X' ω + Y' ω) =
      X ω * X' ω + X ω * Y' ω + Y ω * X' ω + Y ω * Y' ω := fun ω => by ring
  simp only [e]
  have i1 : Integrable (fun ω => X ω * X' ω + X ω * Y' ω) μ := h1.add h2
  have i2 : Integrable (fun ω => X ω * X' ω + X ω * Y' ω + Y ω * X' ω) μ := i1.add h3
  rw [integral_add i2 h4, integral_add i1 h3, integral_add h1 h2]

variable {W : ℕ}

theorem bilinear_sub_mat {n : Type*} [Fintype n] (u : n → ℂ) (M M' : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (M - M') v = bilinear u M v - bilinear u M' v := by
  simp [bilinear, Matrix.sub_mulVec, dotProduct_sub]

theorem matrixExpect_projGamma {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hI : ∀ i j, Integrable (fun y => transportedSep b E XX .id y i j) (freshLaw W b))
    (hP : ∀ i j, Integrable (fun y => transportedSep b E XX .proj y i j) (freshLaw W b)) :
    matrixExpect (freshLaw W b) (projGamma b E XX) =
      nearProjection W * matrixExpect (freshLaw W b) (transportedSep b E XX .id) *
        nearProjection W - matrixExpect (freshLaw W b) (transportedSep b E XX .proj) := by
  have h := FullSource.matrixExpect_sandwich (μ := freshLaw W b) (nearProjection W)
    (nearProjection W) 0 (transportedSep b E XX .id) hI
  simp only [sub_zero] at h
  have hint : ∀ i j, Integrable (fun y => (nearProjection W * transportedSep b E XX .id y *
      nearProjection W) i j) (freshLaw W b) := fun i j => by
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ =>
      (integrable_finsetSum _ fun l _ => (hI l k).const_mul _).mul_const _
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [matrixExpect, Matrix.of_apply] at hij
  simp only [matrixExpect, projGamma, Matrix.of_apply, Matrix.sub_apply]
  rw [integral_sub (hint i j) (hP i j), hij]

theorem centered_proj {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hG : matrixExpect (freshLaw W b) (projGamma b E XX) =
      nearProjection W * matrixExpect (freshLaw W b) (transportedSep b E XX .id) *
        nearProjection W - matrixExpect (freshLaw W b) (transportedSep b E XX .proj))
    (u v : Fin 2 × Fin W → ℂ) (y : LayerSample W .oneBlockOnePort) :
    bilinear u (transportedSep b E XX .proj y -
        matrixExpect (freshLaw W b) (transportedSep b E XX .proj)) v =
      bilinear (nearProjection W *ᵥ u) (transportedSep b E XX .id y -
        matrixExpect (freshLaw W b) (transportedSep b E XX .id)) (nearProjection W *ᵥ v) +
      -bilinear u (projGamma b E XX y - matrixExpect (freshLaw W b) (projGamma b E XX)) v := by
  have hP : (nearProjection W)ᴴ = nearProjection W :=
    BlockBand.Transmission.Bridge.nearProjection_conjTranspose
  have hb := bilinear_sandwich u (nearProjection W) (transportedSep b E XX .id y -
    matrixExpect (freshLaw W b) (transportedSep b E XX .id)) (nearProjection W) v
  rw [hP] at hb
  rw [← hb, ← sub_eq_add_neg, ← bilinear_sub_mat]
  congr 1
  rw [hG]
  simp only [projGamma, Matrix.mul_sub, Matrix.sub_mul]
  abel

end BlockBand.SourceProcess.ContractingWords
