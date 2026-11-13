module

public import BlockBand.Density.Stieltjes
public import BlockBand.QUE.Invariance.CyclicLaw

/-!
# Resolvent comparison for an embedded block segment

* `couplingDefect ι A B u v = A_{ι u, v} - Σ_{v'} 1{ι v' = v} B_{u v'}` (the coupling difference
  `V` read on the rows of the embedded segment);
* `norm_resolvent_sub_le_defect`: for Hermitian `A, B`, `z = e + iη`, `η > 0`, injective `ι`,
  `‖(A - z)⁻¹_{ι x, ι x} - (B - z)⁻¹_{x x}‖ ≤ η⁻¹ Σ_u ‖(B - z)⁻¹_{x u}‖ Σ_v ‖couplingDefect u v‖`
  (proof: `P (A - z) = (B - z) P + V` with the embedding matrix `P`, so
  `G^B P = P G^A + G^B V G^A`); this is the crude `Σ |V_uv|` form of the bound in the paper.
* `integral_resolvent_diag_block`: under every physical law the mean diagonal resolvent entry
  `E G_xx(z)` depends only on the internal coordinate `x.2` (cyclic invariance
  `GaussianRingModel.map_cyclicMatrix`), so the site can be placed in any block.
No contract or input.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Matrix
open scoped ComplexOrder

section Deterministic

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `A - z` is invertible for Hermitian `A` and `z = e + iη`, `η > 0`. -/
theorem isUnit_det_resolvent {A : Matrix α α ℂ} (hA : A.IsHermitian) (e : ℝ) {η : ℝ}
    (hη : 0 < η) :
    IsUnit (A - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix α α ℂ)).det := by
  set B : Matrix α α ℂ := (e : ℂ) • (1 : Matrix α α ℂ) - A
  have h1 : ((e : ℂ) • (1 : Matrix α α ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hB : B.IsHermitian := h1.sub hA
  set N' := Wegner.absorbedPencil B 0 η 0
  have hN' : Wegner.HasImMargin η N' :=
    Wegner.hasImMargin_absorbedPencil hB Matrix.PosSemidef.zero η (by simp)
  have hrel : A - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix α α ℂ) = -N' := by
    simp only [N', Wegner.absorbedPencil, B, zero_smul, add_zero, add_smul]
    abel
  rw [hrel]
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    ((Matrix.isUnit_iff_isUnit_det N').mpr (hN'.isUnit_det hη)).neg

/-- The coupling difference on the rows of the embedded segment. -/
def couplingDefect (ι : β → α) (A : Matrix α α ℂ) (B : Matrix β β ℂ) : Matrix β α ℂ :=
  fun u v => A (ι u) v - ∑ v', if ι v' = v then B u v' else 0

/-- The embedding matrix `P_{u x} = 1{ι u = x}`. -/
def embeddingMatrix (ι : β → α) : Matrix β α ℂ := fun u x => if ι u = x then 1 else 0

theorem embeddingMatrix_mul_sub (ι : β → α) (A : Matrix α α ℂ)
    (B : Matrix β β ℂ) (z : ℂ) :
    embeddingMatrix ι * (A - z • (1 : Matrix α α ℂ)) =
      (B - z • (1 : Matrix β β ℂ)) * embeddingMatrix ι + couplingDefect ι A B := by
  ext u v
  simp only [Matrix.mul_apply, embeddingMatrix, Matrix.add_apply, couplingDefect, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_ite, mul_one, mul_zero]
  have hj : ∀ j, (if ι j = v then B u j - (if u = j then z else 0) else 0) =
      (if ι j = v then B u j else 0) - (if u = j then (if ι j = v then z else 0) else 0) := by
    intro j
    split_ifs <;> simp
  simp only [hj, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **Resolvent comparison** (crude `Σ|V|` form): for Hermitian `A` on `α`,
Hermitian `B` on `β`, injective `ι : β → α`, `z = e + iη`, `η > 0`, and every `x ∈ β`,
`‖G^A_{ιx,ιx} - G^B_{xx}‖ ≤ η⁻¹ Σ_u ‖G^B_{xu}‖ Σ_v ‖V_{uv}‖`, `V = couplingDefect ι A B`. -/
theorem norm_resolvent_sub_le_defect {ι : β → α} (hι : Function.Injective ι)
    {A : Matrix α α ℂ} (hA : A.IsHermitian) {B : Matrix β β ℂ} (hB : B.IsHermitian)
    (e : ℝ) {η : ℝ} (hη : 0 < η) (x : β) :
    ‖(A - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix α α ℂ))⁻¹ (ι x) (ι x) -
        (B - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix β β ℂ))⁻¹ x x‖ ≤
      η⁻¹ * ∑ u, ‖(B - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix β β ℂ))⁻¹ x u‖ *
        ∑ v, ‖couplingDefect ι A B u v‖ := by
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I
  set F := (A - z • (1 : Matrix α α ℂ))⁻¹
  set G := (B - z • (1 : Matrix β β ℂ))⁻¹
  set P := embeddingMatrix ι
  set V := couplingDefect ι A B
  have hF : (A - z • (1 : Matrix α α ℂ)) * F = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_det_resolvent hA e hη)
  have hG : G * (B - z • (1 : Matrix β β ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_resolvent hB e hη)
  have hid : G * P = P * F + G * V * F := by
    calc G * P = G * P * ((A - z • (1 : Matrix α α ℂ)) * F) := by rw [hF, Matrix.mul_one]
      _ = G * (P * (A - z • (1 : Matrix α α ℂ))) * F := by
          simp only [Matrix.mul_assoc]
      _ = G * ((B - z • (1 : Matrix β β ℂ)) * P + V) * F := by
          rw [embeddingMatrix_mul_sub ι A B z]
      _ = P * F + G * V * F := by
          rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hG, Matrix.one_mul]
  have hent := congrFun (congrFun hid x) (ι x)
  have hGP : (G * P) x (ι x) = G x x := by
    simp only [Matrix.mul_apply, P, embeddingMatrix, hι.eq_iff, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hPF : (P * F) x (ι x) = F (ι x) (ι x) := by
    simp only [Matrix.mul_apply, P, embeddingMatrix, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Matrix.add_apply, hGP, hPF] at hent
  have hdiff : F (ι x) (ι x) - G x x = -(G * V * F) x (ι x) := by
    rw [hent]; ring
  rw [hdiff, norm_neg]
  have hFb : ∀ a b, ‖F a b‖ ≤ η⁻¹ := fun a b => norm_resolvent_apply_le hA e hη a b
  calc ‖(G * V * F) x (ι x)‖
      = ‖∑ v, (∑ u, G x u * V u v) * F v (ι x)‖ := by
        simp only [Matrix.mul_apply]
    _ ≤ ∑ v, ‖(∑ u, G x u * V u v) * F v (ι x)‖ := norm_sum_le _ _
    _ ≤ ∑ v, (∑ u, ‖G x u‖ * ‖V u v‖) * η⁻¹ := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [norm_mul]
        refine mul_le_mul ((norm_sum_le _ _).trans (le_of_eq ?_)) (hFb _ _) (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ => by positivity)
        simp only [norm_mul]
    _ = η⁻¹ * ∑ u, ‖G x u‖ * ∑ v, ‖V u v‖ := by
        rw [← Finset.sum_mul, Finset.sum_comm, mul_comm]
        simp only [Finset.mul_sum]

end Deterministic

/-- **Rotation**: under every physical law the mean diagonal resolvent entry at `x` equals the
one at `(k, x.2)` for every block `k` (cyclic invariance `map_cyclicMatrix`); any `z`. -/
theorem integral_resolvent_diag_block (p : Parameters) (model : p.GaussianRingModel) (z : ℂ)
    (x : p.Site) (k : ZMod p.n) :
    ∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix) =
      ∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ (k, x.2) (k, x.2) ∂(model.law : Measure p.SiteMatrix) := by
  set e := p.cyclicSiteEquiv (x.1 - k)
  have hex : e (k, x.2) = x := by
    simp [e, Parameters.cyclicSiteEquiv]
  have hpt : ∀ H : p.SiteMatrix,
      (p.siteReindexMatrix e H - z • (1 : p.SiteMatrix))⁻¹ (k, x.2) (k, x.2) =
        (H - z • (1 : p.SiteMatrix))⁻¹ x x := by
    intro H
    have hsub : p.siteReindexMatrix e H - z • (1 : p.SiteMatrix) =
        (H - z • (1 : p.SiteMatrix)).submatrix e e := by
      ext a b
      simp [Parameters.siteReindexMatrix, Matrix.one_apply, e.injective.eq_iff]
    rw [hsub, Matrix.inv_submatrix_equiv]
    simp [hex]
  calc ∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix)
      = ∫ H, (p.siteReindexMatrix e H - z • (1 : p.SiteMatrix))⁻¹ (k, x.2) (k, x.2)
          ∂(model.law : Measure p.SiteMatrix) := by simp_rw [hpt]
    _ = ∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ (k, x.2) (k, x.2)
          ∂(Measure.map (p.siteReindexMatrix e) (model.law : Measure p.SiteMatrix)) :=
        (integral_map (p.measurable_siteReindexMatrix e).aemeasurable
          (measurable_resolvent_apply z _ _).aestronglyMeasurable).symm
    _ = _ := by rw [model.map_cyclicMatrix]

end BlockBand.Density
