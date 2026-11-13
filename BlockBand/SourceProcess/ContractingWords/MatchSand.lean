module

public import BlockBand.SourceProcess.ContractingWords.SlotCovPre
public import BlockBand.SourceProcess.ContractingWords.LayerCombi

/-!
# Contracting sandwiches of the same-sign tensors

`B = sepOf 𝕏` (an ordinary separator table, `ordTable_sepOf`), `P = B P`, `𝕊 = twoPortScattering`.
* `sandwich_contr`: for ordinary `s, s'` and the same-sign tensors `G ∈ {P𝕊, 𝕊*P}` (`fscG 2, 3`),
  `B_s G B_{s'}` is a contracting separator `B_σ`, `σ ∈ contrSeps`;
* `exists_contr_pair`: `Tr(B_{s'}·segProd S·G) = Tr(setLastSep S σ)` for some `σ ∈ contrSeps`
  (the cycles of `contrTwo`);
* `exists_contr_cross`: `Tr(B_s·segProd S·G·B_{s'}·segProd S'·H) = Tr(setLastSep S σ ++
  setLastSep S' σ')` (the cycles of `contrCov`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.FullSourceGenerator BlockBand.Transmission.Bridge

variable {W nT nI : ℕ}

theorem coreProd_one (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI) :
    coreProd A T [w] = wval A T w := by
  simp [coreProd, matWord, letWord, wval, segProd, List.map_map, Function.comp_def]

theorem coreProd_two (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (u v : TraceWord nT nI) :
    coreProd A T [u, v] = wval A T u * wval A T v := by
  simp [coreProd, matWord, letWord, wval, segProd, List.map_map, Function.comp_def]

theorem ordTable_sepOf (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    OrdTable (sepOf b E XX) :=
  ⟨rfl, BlockBand.Transmission.Bridge.nearProjection_mul_self⟩

theorem fscH_eq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {k : Fin 4}
    (hk : k = 2 ∨ k = 3) : fscH b E XX k = fscG b E XX k := by
  rcases hk with rfl | rfl <;> rfl

/-- **The same-sign tensors sandwiched by ordinary separators are contracting.** -/
theorem sandwich_contr (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {s s' : Separator} (hs : s = .id ∨ s = .proj) (hs' : s' = .id ∨ s' = .proj) {k : Fin 4}
    (hk : k = 2 ∨ k = 3) :
    ∃ σ ∈ contrSeps, sepOf b E XX s * fscG b E XX k * sepOf b E XX s' = sepOf b E XX σ := by
  have hPP := BlockBand.Transmission.Bridge.nearProjection_mul_self (W := W)
  rcases hk with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;>
    simp only [sepOf, fscG, Matrix.cons_val, Matrix.one_mul, Matrix.mul_one]
  · exact ⟨.projS, by simp [contrSeps], rfl⟩
  · exact ⟨.projSProj, by simp [contrSeps], rfl⟩
  · exact ⟨.projS, by simp [contrSeps], by simp only [← Matrix.mul_assoc, hPP]⟩
  · exact ⟨.projSProj, by simp [contrSeps], by simp only [← Matrix.mul_assoc, hPP]⟩
  · exact ⟨.sStarProj, by simp [contrSeps], rfl⟩
  · exact ⟨.sStarProj, by simp [contrSeps], by simp only [Matrix.mul_assoc, hPP]⟩
  · exact ⟨.projSStarProj, by simp [contrSeps], by simp only [Matrix.mul_assoc]⟩
  · exact ⟨.projSStarProj, by simp [contrSeps], by
      simp only [Matrix.mul_assoc, hPP]⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Tr(B_{s'}·segProd(u ++ [z])·G) = Tr(segProd u·A_z·B_σ)` when `B_{z₂} G B_{s'} = B_σ`. -/
theorem trace_setLast (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (Bs G : Matrix ι ι ℂ) (u : TraceWord nT nI) (z : TraceLetter nT nI × Separator)
    (σ : Separator) (h : B z.2 * G * Bs = B σ) :
    (Bs * segProd A B (u ++ [z]) * G).trace = wval A B (setLastSep (u ++ [z]) σ) := by
  rw [setLastSep_concat, wval, segProd_append, segProd_append, segProd_singleton,
    segProd_singleton, ← h]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The cross version: two cycles closed into one. -/
theorem trace_cross_setLast (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (Bs Bs' G H : Matrix ι ι ℂ) (u u' : TraceWord nT nI) (z z' : TraceLetter nT nI × Separator)
    (σ σ' : Separator) (h1 : B z.2 * G * Bs' = B σ) (h2 : B z'.2 * H * Bs = B σ') :
    (Bs * segProd A B (u ++ [z]) * G * (Bs' * segProd A B (u' ++ [z'])) * H).trace =
      wval A B (setLastSep (u ++ [z]) σ ++ setLastSep (u' ++ [z']) σ') := by
  rw [setLastSep_concat, setLastSep_concat, wval]
  simp only [segProd_append, segProd_singleton, ← h1, ← h2]
  rw [show Bs * (segProd A B u * (A z.1 * B z.2)) * G * (Bs' * (segProd A B u' *
      (A z'.1 * B z'.2))) * H = Bs * (segProd A B u * (A z.1 * B z.2) * G * (Bs' * (segProd A B u' *
      (A z'.1 * B z'.2))) * H) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem exists_concat_ord {S : TraceWord nT nI} (hS : S ≠ [])
    (hSo : ∀ x ∈ S, x.2 = .id ∨ x.2 = .proj) :
    ∃ (u : TraceWord nT nI) (z : TraceLetter nT nI × Separator), S = u ++ [z] ∧
      (z.2 = .id ∨ z.2 = .proj) := by
  obtain ⟨u, z, rfl⟩ := (List.eq_nil_or_concat S).resolve_left hS
  exact ⟨u, z, List.concat_eq_append .., hSo z (by simp)⟩

/-- **A cycle of a within-word pair, closed by a same-sign tensor, is a contracting word.** -/
theorem exists_contr_pair (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {S : TraceWord nT nI}
    (hS : S ≠ []) (hSo : ∀ x ∈ S, x.2 = .id ∨ x.2 = .proj) {s' : Separator}
    (hs' : s' = .id ∨ s' = .proj) {k : Fin 4} (hk : k = 2 ∨ k = 3) :
    ∃ σ ∈ contrSeps, (sepOf b E XX s' * segProd A (sepOf b E XX) S * fscG b E XX k).trace =
      wval A (sepOf b E XX) (setLastSep S σ) := by
  obtain ⟨u, z, rfl, hz⟩ := exists_concat_ord hS hSo
  obtain ⟨σ, hσ, h⟩ := sandwich_contr b E XX hz hs' hk
  exact ⟨σ, hσ, trace_setLast A _ _ _ u z σ h⟩

/-- **A cross pair closed by same-sign tensors is one contracting word.** -/
theorem exists_contr_cross (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {S S' : TraceWord nT nI}
    (hS : S ≠ []) (hSo : ∀ x ∈ S, x.2 = .id ∨ x.2 = .proj) (hS' : S' ≠ [])
    (hSo' : ∀ x ∈ S', x.2 = .id ∨ x.2 = .proj) {s s' : Separator} (hs : s = .id ∨ s = .proj)
    (hs' : s' = .id ∨ s' = .proj) {k : Fin 4} (hk : k = 2 ∨ k = 3) :
    ∃ σ ∈ contrSeps, ∃ σ' ∈ contrSeps,
      (sepOf b E XX s * segProd A (sepOf b E XX) S * fscG b E XX k *
          (sepOf b E XX s' * segProd A (sepOf b E XX) S') * fscH b E XX k).trace =
        wval A (sepOf b E XX) (setLastSep S σ ++ setLastSep S' σ') := by
  obtain ⟨u, z, rfl, hz⟩ := exists_concat_ord hS hSo
  obtain ⟨u', z', rfl, hz'⟩ := exists_concat_ord hS' hSo'
  obtain ⟨σ, hσ, h1⟩ := sandwich_contr b E XX hz hs' hk
  obtain ⟨σ', hσ', h2⟩ := sandwich_contr b E XX hz' hs hk
  rw [fscH_eq b E XX hk]
  exact ⟨σ, hσ, σ', hσ', trace_cross_setLast A _ _ _ _ _ u u' z z' σ σ' h1 h2⟩

end BlockBand.SourceProcess.ContractingWords
