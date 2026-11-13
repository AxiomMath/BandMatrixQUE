module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Complex.Basic

/-!
# The Schur step of the interior pencil (pure block algebra)

Old path: interior pencil `P = H_O - E - z⁻¹CC*`, `C = n·ι* + f` (near column `n`, far coupling
`f`, near selector `ι*` with `ι*ι = 1`, `ι*f* = 0`), interior inverse `G`, boundary map `U`,
`V = 𝕊U*`. Fresh layer: `(A'' - X)𝒢 = 1` (`A'' = A - E - z⁻¹BB*`), `K = z - X`, `RK = 1`.
`old_facts` turns the old path into `P_OG = 1 + z⁻¹n(n*G)`, `n*G = -z ι*V`, `P_O(Uι) = -nR`,
`n*(Uι) = 1 - zR` (`P_O = H_O - E - z⁻¹ff*`); `grown_interior_mul` shows that
`[[𝒢, 𝒢Kι*V],[UιK𝒢, G + UιΔι*V]]`, `Δ = K𝒢K - K`, is a right inverse of the grown interior
pencil `[[A'', n*],[n, P_O]]` (newest block first).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open Matrix
open scoped Matrix

variable {O P : Type*} [Fintype O] [Fintype P] [DecidableEq O] {W : ℕ}

/-- **The old-path facts.** -/
theorem old_facts (z : ℂ) (hz : z ≠ 0) (HO : Matrix O O ℂ) (nc : Matrix O (Fin W) ℂ)
    (f : Matrix O P ℂ) (ns : Matrix (Fin W) P ℂ) (hnsf : ns * fᴴ = 0) (hns : ns * nsᴴ = 1)
    (G : Matrix O O ℂ) (U : Matrix O P ℂ) (V : Matrix P O ℂ) (R : Matrix (Fin W) (Fin W) ℂ)
    (hG : (HO - z⁻¹ • ((nc * ns + f) * (nc * ns + f)ᴴ)) * G = 1)
    (hV : (nc * ns + f)ᴴ * G = -(z • V))
    (hU : (HO - z⁻¹ • ((nc * ns + f) * (nc * ns + f)ᴴ)) * U = -(z⁻¹ • (nc * ns + f)))
    (hd : ncᴴ * (U * nsᴴ) = 1 - z • R) :
    (HO - z⁻¹ • (f * fᴴ)) * G = 1 + z⁻¹ • (nc * (ncᴴ * G)) ∧
      ncᴴ * G = -(z • (ns * V)) ∧ (HO - z⁻¹ • (f * fᴴ)) * (U * nsᴴ) = -(nc * R) := by
  have hfn : f * nsᴴ = 0 := by
    have := congrArg conjTranspose hnsf
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have hns' : ∀ M : Matrix (Fin W) O ℂ, ns * (nsᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hns, Matrix.one_mul]
  have hfn' : ∀ M : Matrix (Fin W) O ℂ, f * (nsᴴ * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hfn, Matrix.zero_mul]
  have hCC : (nc * ns + f) * (nc * ns + f)ᴴ = nc * ncᴴ + f * fᴴ := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hns', hnsf, hfn', Matrix.mul_zero, add_zero, zero_add]
  have hnsC : ns * (nc * ns + f)ᴴ = ncᴴ := by
    rw [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, ← Matrix.mul_assoc, hns,
      Matrix.one_mul, hnsf, add_zero]
  have hCns : (nc * ns + f) * nsᴴ = nc := by
    rw [Matrix.add_mul, Matrix.mul_assoc, hns, Matrix.mul_one, hfn, add_zero]
  have hP : HO - z⁻¹ • ((nc * ns + f) * (nc * ns + f)ᴴ) =
      (HO - z⁻¹ • (f * fᴴ)) - z⁻¹ • (nc * ncᴴ) := by
    rw [hCC, smul_add]; abel
  rw [hP] at hG hU
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.sub_mul, sub_eq_iff_eq_add] at hG
    rw [hG, Matrix.smul_mul, Matrix.mul_assoc, add_comm]
  · rw [← hnsC, Matrix.mul_assoc, hV, Matrix.mul_neg, Matrix.mul_smul]
  · have h := congrArg (fun M => M * nsᴴ) hU
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc] at h
    rw [hCns, hd] at h
    have h' := sub_eq_iff_eq_add.mp h
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [h', Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, smul_sub, smul_smul,
      inv_mul_cancel₀ hz, one_smul]
    abel

/-- **The grown interior right inverse.** -/
theorem grown_interior_mul (z : ℂ) (PO : Matrix O O ℂ) (nc : Matrix O (Fin W) ℂ)
    (G : Matrix O O ℂ) (U' : Matrix O (Fin W) ℂ) (V' : Matrix (Fin W) O ℂ)
    (X R A'' 𝒢 : Matrix (Fin W) (Fin W) ℂ)
    (hF1 : PO * G = 1 + z⁻¹ • (nc * (ncᴴ * G))) (hF2 : ncᴴ * G = -(z • V'))
    (hF3 : PO * U' = -(nc * R)) (hF4 : ncᴴ * U' = 1 - z • R)
    (hF5 : A'' * 𝒢 = 1 + X * 𝒢) (hRK : R * (z • 1 - X) = 1) (hz : z ≠ 0) :
    fromBlocks A'' ncᴴ nc PO *
      fromBlocks 𝒢 (𝒢 * (z • 1 - X) * V') (U' * ((z • 1 - X) * 𝒢))
        (G + U' * ((z • 1 - X) * 𝒢 * (z • 1 - X) - (z • 1 - X)) * V') = 1 := by
  have hRX : ∀ M : Matrix (Fin W) (Fin W) ℂ, R * (X * M) = z • (R * M) - M := by
    intro M
    have h := congrArg (· * M) hRK
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul] at h
    have h1 := sub_eq_iff_eq_add.mp h
    rw [← Matrix.mul_assoc]
    exact eq_sub_iff_add_eq.mpr (by rw [h1, add_comm])
  have hRXO : ∀ M : Matrix (Fin W) O ℂ, R * (X * M) = z • (R * M) - M := by
    intro M
    have h := congrArg (· * M) hRK
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul] at h
    have h1 := sub_eq_iff_eq_add.mp h
    rw [← Matrix.mul_assoc]
    exact eq_sub_iff_add_eq.mpr (by rw [h1, add_comm])
  have hF1b : PO * G = 1 - nc * V' := by
    rw [hF1, hF2, Matrix.mul_neg, Matrix.mul_smul, smul_neg, smul_smul, inv_mul_cancel₀ hz,
      one_smul, ← sub_eq_add_neg]
  have hF3W : ∀ M : Matrix (Fin W) (Fin W) ℂ, PO * (U' * M) = -(nc * (R * M)) := by
    intro M; rw [← Matrix.mul_assoc, hF3, Matrix.neg_mul, Matrix.mul_assoc]
  have hF3O : ∀ M : Matrix (Fin W) O ℂ, PO * (U' * M) = -(nc * (R * M)) := by
    intro M; rw [← Matrix.mul_assoc, hF3, Matrix.neg_mul, Matrix.mul_assoc]
  have hF4W : ∀ M : Matrix (Fin W) (Fin W) ℂ, ncᴴ * (U' * M) = M - z • (R * M) := by
    intro M; rw [← Matrix.mul_assoc, hF4, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have hF4O : ∀ M : Matrix (Fin W) O ℂ, ncᴴ * (U' * M) = M - z • (R * M) := by
    intro M; rw [← Matrix.mul_assoc, hF4, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have hF5O : ∀ M : Matrix (Fin W) O ℂ, A'' * (𝒢 * M) = M + X * (𝒢 * M) := by
    intro M; rw [← Matrix.mul_assoc, hF5, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, hF5, hF4W, hRX,
      smul_sub]
    module
  · simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, hF5O, hF4O,
      hRXO, smul_sub, hF2]
    module
  · simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, hF3W, hRX]
    module
  · simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, hF3O, hRXO,
      smul_sub, hF1b]
    module

end BlockBand.SourceProcess.RawTag
